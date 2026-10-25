import asyncio
import base64
from urllib.parse import urlsplit
import logging
import configparser
import hashlib
import hmac
import json
import os
import random
import re
import signal
import sys
import time
from xml.sax.saxutils import escape, quoteattr

COMPACT = {"v": "via", "f": "from", "t": "to", "i": "call-id", "m": "contact"}
REPLY_HEADERS = ("via", "from", "to", "call-id", "cseq")
ALLOW = "INVITE, ACK, CANCEL, BYE, OPTIONS, REGISTER, MESSAGE"
REQUIRED = (
    "bind", "host", "port", "realm", "users_file", "min_expires",
    "max_expires", "http_port",
)


def parse_headers(data):
    head, _, body = data.partition(b"\r\n\r\n")
    lines = head.decode("utf-8", "replace").split("\r\n")
    headers = []
    for line in lines[1:]:
        name, sep, value = line.partition(":")
        if sep:
            name = name.strip()
            headers.append([
                COMPACT.get(name.lower(), name.lower()),
                name,
                value.strip(),
            ])
    return lines[0], headers, body


def get_header(headers, key):
    key = key.lower()
    for h in headers:
        if h[0] == key:
            return h[2]
    return None


def render(start, headers, body=b""):
    lines = [start] + [f"{name}: {value}" for _, name, value in headers]
    if not any(k == "content-length" for k, _, _ in headers):
        lines.append(f"Content-Length: {len(body)}")
    return "\r\n".join(lines).encode() + b"\r\n\r\n" + body


def user_of(text):
    m = re.search(r"sips?:([^@>;\s]+)@", text, re.I)
    return m.group(1) if m else None


def uri_from_contact(contact):
    if not contact:
        return None
    contact = contact.strip()
    if contact == "*":
        return None
    m = re.search(r"<\s*(sips?:[^>\s]+)\s*>", contact, re.I)
    if m:
        return m.group(1)
    m = re.match(r"(sips?:[^\s;]+)", contact, re.I)
    return m.group(1) if m else None


def md5(text):
    return hashlib.md5(text.encode()).hexdigest()


def parse_auth(value):
    return {
        k.lower(): a or b
        for k, a, b in re.findall(
            r'(\w+)=(?:"([^"]*)"|([^,\s]+))', value or ""
        )
    }


def load_users(path):
    users = {}
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#") and ":" in line:
                name, _, password = line.partition(":")
                users[name.strip()] = password.strip()
    return users


def cseq_number(msg):
    value = get_header(msg[1], "cseq") or ""
    parts = value.split()
    return parts[0] if parts else ""


def top_via(headers):
    return next((h for h in headers if h[0] == "via"), None)


def via_branch(value):
    m = re.search(r"(?:^|;)\s*branch=([^;\s,]+)", value or "", re.I)
    return m.group(1) if m else ""


class SipServer(asyncio.DatagramProtocol):
    def __init__(self, conf):
        self.host = conf["host"]
        self.port = conf.getint("port")
        self.realm = conf["realm"]
        self.users_file = conf["users_file"]
        self.min_expires = conf.getint("min_expires")
        self.max_expires = conf.getint("max_expires")
        self.secret = os.urandom(32)
        self.users = {}
        self.regs = {}
        self.transactions = {}
        self.transport = None
        self.reload_users()

    def connection_made(self, transport):
        self.transport = transport

    def reload_users(self):
        if not self.users_file:
            return
        try:
            self.users = load_users(self.users_file)
            print(f"loaded {len(self.users)} users", file=sys.stderr)
        except OSError as exc:
            print(f"users file: {exc}", file=sys.stderr)

    def make_nonce(self):
        ts = f"{int(time.time()):x}"
        sig = hmac.new(self.secret, ts.encode(), "sha256").hexdigest()[:32]
        return ts + sig

    def valid_nonce(self, nonce):
        if len(nonce) < 33:
            return False
        ts, sig = nonce[:-32], nonce[-32:]
        try:
            age = time.time() - int(ts, 16)
        except ValueError:
            return False
        expected = hmac.new(
            self.secret, ts.encode(), "sha256"
        ).hexdigest()[:32]
        return hmac.compare_digest(sig, expected) and 0 <= age < 300

    def authorized(self, msg, user):
        value = get_header(msg[1], "authorization")
        if not value:
            return False
        a = parse_auth(value)
        if any(k not in a for k in (
            "username", "realm", "nonce", "uri", "response"
        )):
            return False
        password = self.users.get(user)
        if password is None:
            return False
        if a["username"] != user or a["realm"] != self.realm:
            return False
        if not self.valid_nonce(a["nonce"]):
            return False

        ha1 = md5(f"{user}:{self.realm}:{password}")
        method = msg[0].split()[0].upper()
        ha2 = md5(f"{method}:{a['uri']}")

        if a.get("qop", "").lower() == "auth":
            expected = md5(
                f"{ha1}:{a['nonce']}:{a.get('nc', '')}:"
                f"{a.get('cnonce', '')}:auth:{ha2}"
            )
        else:
            expected = md5(f"{ha1}:{a['nonce']}:{ha2}")

        return hmac.compare_digest(expected, a["response"].lower())

    def datagram_received(self, data, addr):
        if len(data) < 10:
            return
        try:
            msg = parse_headers(data)
        except Exception as exc:
            print(f"parse error: {exc}", file=sys.stderr)
            return

        print(
            f"rx {len(data)} bytes from {addr[0]}:{addr[1]} {msg[0]}",
            file=sys.stderr,
        )
        if msg[0].startswith("SIP/2.0 "):
            self.on_response(msg, addr)
        else:
            self.on_request(msg, addr)

    def send(self, data, addr):
        try:
            self.transport.sendto(data, addr)
        except (ValueError, OSError) as exc:
            print(f"send failed to {addr}: {exc}", file=sys.stderr)

    def reply(self, addr, msg, code, reason, extra=()):
        headers = []
        for h in msg[1]:
            if h[0] in REPLY_HEADERS:
                value = h[2]
                if (
                    code != 100
                    and h[0] == "to"
                    and not re.search(r";\s*tag=", value)
                ):
                    value += f";tag={random.getrandbits(32):08x}"
                headers.append([h[0], h[1], value])

        headers.extend([[k.lower(), k, v] for k, v in extra])
        headers.append(["server", "Server", "o1"])
        headers.append(["content-length", "Content-Length", "0"])
        self.send(render(f"SIP/2.0 {code} {reason}", headers), addr)

    def lookup(self, user):
        entry = self.regs.get(user)
        if entry and entry["expires"] > time.time():
            return entry
        self.regs.pop(user, None)
        return None

    def register(self, msg, addr):
        user = user_of(get_header(msg[1], "to") or "")
        if not user:
            self.reply(addr, msg, 400, "Bad Request")
            return

        if self.users_file and not self.authorized(msg, user):
            challenge = (
                f'Digest realm="{self.realm}", nonce="{self.make_nonce()}", '
                'algorithm=MD5, qop="auth"'
            )
            self.reply(
                addr, msg, 401, "Unauthorized",
                [("WWW-Authenticate", challenge)],
            )
            return

        contact = get_header(msg[1], "contact")
        if contact is None:
            self.reply(addr, msg, 200, "OK")
            return

        expires_value = get_header(msg[1], "expires")
        ttl = self.max_expires
        if expires_value and expires_value.isdigit():
            ttl = int(expires_value)

        match = re.search(r"(?:^|;)\s*expires=(\d+)", contact, re.I)
        if match:
            ttl = int(match.group(1))

        if contact.strip() == "*":
            ttl = 0

        if ttl > 0:
            ttl = max(self.min_expires, min(ttl, self.max_expires))
            self.regs[user] = {
                "addr": addr,
                "expires": time.time() + ttl,
                "contact": contact,
                "uri": uri_from_contact(contact),
            }
        else:
            self.regs.pop(user, None)

        print(
            f"register {user} ttl={ttl} source={addr} contact={contact}",
            file=sys.stderr,
        )
        self.reply(
            addr, msg, 200, "OK",
            [("Contact", contact), ("Expires", str(ttl))],
        )

    def transaction_branch(self, msg, addr):
        via = top_via(msg[1])
        if via is None:
            return None

        original_branch = via_branch(via[2])
        callid = get_header(msg[1], "call-id") or ""
        cseq = cseq_number(msg)
        parts = (get_header(msg[1], "cseq") or "").split()
        method = parts[1].upper() if len(parts) > 1 else ""

        if not original_branch or not callid or not cseq or not method:
            return None

        # CANCEL uses the same proxy branch as the INVITE it cancels.
        seed = f"{addr[0]}:{addr[1]}|{original_branch}|{callid}|{cseq}"
        branch = "z9hG4bK" + hashlib.sha256(seed.encode()).hexdigest()[:24]
        key = (branch, method)

        now = time.time()
        for old_key in list(self.transactions):
            if self.transactions[old_key]["expires"] <= now:
                del self.transactions[old_key]

        existing = self.transactions.get(key)
        if existing and existing["expires"] > now:
            return branch

        self.transactions[key] = {
            "addr": addr,
            "expires": now + 180,
            "method": method,
            "forwarded": False,
            "response": None,
            "target": None,
        }
        return branch

    def on_request(self, msg, addr):
        parts = msg[0].split()
        if len(parts) != 3 or parts[2] != "SIP/2.0":
            return

        method, uri = parts[0].upper(), parts[1]
        print(f"{method} {uri}", file=sys.stderr)

        if method == "REGISTER":
            self.register(msg, addr)
            return

        if method == "OPTIONS" and not user_of(uri):
            self.reply(addr, msg, 200, "OK", [("Allow", ALLOW)])
            return

        if method not in (
            "INVITE", "ACK", "CANCEL", "BYE", "OPTIONS", "MESSAGE"
        ):
            self.reply(addr, msg, 405, "Method Not Allowed")
            return

        forwards = get_header(msg[1], "max-forwards")
        if forwards is not None and forwards.isdigit() and int(forwards) <= 0:
            if method != "ACK":
                self.reply(addr, msg, 483, "Too Many Hops")
            return

        user = user_of(uri)
        if not user:
            if method != "ACK":
                self.reply(addr, msg, 400, "Bad Request")
            return

        branch = self.transaction_branch(msg, addr)
        if branch is None:
            if method != "ACK":
                self.reply(addr, msg, 400, "Missing Via branch, Call-ID or CSeq")
            return

        cseq_parts = (get_header(msg[1], "cseq") or "").split()
        cseq_method = cseq_parts[1].upper() if len(cseq_parts) > 1 else method
        key = (branch, cseq_method)
        transaction = self.transactions.get(key)

        if method == "CANCEL":
            invite_tx = self.transactions.get((branch, "INVITE"))
            if invite_tx is None:
                self.reply(addr, msg, 481, "Call/Transaction Does Not Exist")
                return
            self.reply(addr, msg, 200, "OK")

        if method == "INVITE":
            if transaction and transaction["forwarded"]:
                cached = transaction.get("response")
                if cached:
                    self.send(cached, addr)
                else:
                    self.reply(addr, msg, 100, "Trying")
                print("duplicate INVITE handled locally", file=sys.stderr)
                return
            self.reply(addr, msg, 100, "Trying")

        entry = self.lookup(user)
        if entry is None:
            if method not in ("ACK", "CANCEL"):
                self.reply(addr, msg, 404, "Not Found")
            return

        headers = msg[1]
        if top_via(headers) is None:
            if method != "ACK":
                self.reply(addr, msg, 400, "Missing Via")
            return

        proxy_via = [
            "via", "Via",
            f"SIP/2.0/UDP {self.host}:{self.port};branch={branch};rport",
        ]

        new_headers = [proxy_via] + [h[:] for h in headers]
        for h in new_headers:
            if h[0] == "max-forwards" and h[2].isdigit():
                h[2] = str(max(0, int(h[2]) - 1))

        target_uri = entry["uri"]
        start = msg[0]
        if target_uri:
            start = re.sub(
                r"^(\S+)\s+\S+",
                lambda m: f"{m.group(1)} {target_uri}",
                start,
                count=1,
            )

        data = render(start, new_headers, msg[2])
        dst = entry["addr"]

        if transaction is not None:
            transaction["target"] = dst
            transaction["forwarded"] = True

        print(
            f"forward {method} uri={start.split()[1]} "
            f"to={dst[0]}:{dst[1]} branch={branch}",
            file=sys.stderr,
        )
        self.send(data, dst)

    def on_response(self, msg, addr):
        via = top_via(msg[1])
        if via is None:
            print("response dropped: missing Via", file=sys.stderr)
            return

        branch = via_branch(via[2])
        cseq_parts = (get_header(msg[1], "cseq") or "").split()
        method = cseq_parts[1].upper() if len(cseq_parts) > 1 else ""
        transaction = self.transactions.get((branch, method))

        if not transaction or transaction["expires"] <= time.time():
            print(
                f"response dropped: unknown transaction branch={branch} "
                f"method={method}",
                file=sys.stderr,
            )
            return

        if not via[2].startswith("SIP/2.0/UDP "):
            print("response dropped: unexpected proxy Via", file=sys.stderr)
            return

        # Remove only this proxy's Via. The caller's Via must remain.
        msg[1].remove(via)
        outgoing = render(msg[0], msg[1], msg[2])
        transaction["response"] = outgoing
        dst = transaction["addr"]

        print(f"{msg[0]} -> {dst[0]}:{dst[1]}", file=sys.stderr)
        self.send(outgoing, dst)


async def respond(writer, code, reason, body=b"", ctype="text/plain",
                  extra=(), length=None):
    size = len(body) if length is None else length
    headers = [
        f"HTTP/1.1 {code} {reason}",
        f"Content-Type: {ctype}",
        f"Content-Length: {size}",
        "Connection: close",
    ]
    headers.extend(f"{k}: {v}" for k, v in extra)
    writer.write("\r\n".join(headers).encode() + b"\r\n\r\n" + body)
    await writer.drain()


def parse_upload(content_type, body):
    m = re.search(r'boundary="?([^";]+)"?', content_type)
    if not m:
        return None

    delim = b"--" + m.group(1).encode()
    for part in body.split(delim):
        head, sep, data = part.partition(b"\r\n\r\n")
        if not sep or not re.search(rb'[;\s]name="File"', head, re.I):
            continue
        if data.endswith(b"\r\n"):
            data = data[:-2]

        found = re.search(rb'filename="([^"]*)"', head, re.I)
        name = found.group(1).decode("utf-8", "replace") if found else "file"
        name = os.path.basename(name.replace("\\", "/")) or "file"

        found = re.search(rb"content-type:\s*([^\r\n]+)", head, re.I)
        ctype = found.group(1).decode("latin-1").strip() if found else ""
        if not re.fullmatch(r"[\w.+-]+/[\w.+-]+", ctype):
            ctype = "application/octet-stream"

        return name, ctype, data
    return None


class MediaServer:
    def __init__(self, conf):
        self.dir = conf["media_dir"]
        self.host = conf["host"]
        self.port = conf.getint("http_port")
        self.max_size = conf.getint("max_media_mb") * 1024 * 1024
        self.ttl = conf.getint("media_ttl_days") * 86400
        self.salt = conf["media_salt"].encode()
        self.users = load_users(conf["users_file"]) if conf["users_file"] else {}
        os.makedirs(self.dir, mode=0o700, exist_ok=True)

    def new_token(self, data):
        material = hashlib.sha256(data).digest() + os.urandom(16)
        return hmac.new(self.salt, material, "sha256").hexdigest()[:40]

    def store(self, name, ctype, data):
        token = self.new_token(data)
        path = os.path.join(self.dir, token)
        with open(path, "xb") as f:
            f.write(data)
        with open(path + ".meta", "w") as f:
            json.dump({"name": name, "type": ctype, "size": len(data)}, f)
        return token

    def load(self, token):
        path = os.path.join(self.dir, token)
        if time.time() - os.path.getmtime(path) > self.ttl:
            raise FileNotFoundError(path)
        with open(path, "rb") as f:
            return f.read()

    def purge(self):
        cutoff = time.time() - self.ttl
        for entry in os.scandir(self.dir):
            if entry.is_file() and entry.stat().st_mtime < cutoff:
                os.remove(entry.path)

    async def purge_loop(self):
        while True:
            await asyncio.to_thread(self.purge)
            await asyncio.sleep(3600)

    async def handle(self, reader, writer):
        try:
            await self.serve(reader, writer)
        except (
            asyncio.TimeoutError, asyncio.IncompleteReadError,
            ConnectionError, ValueError,
        ) as exc:
            print(f"http error: {exc}", file=sys.stderr)
        finally:
            writer.close()
            try:
                await writer.wait_closed()
            except ConnectionError:
                pass

    async def serve(self, reader, writer):
        line = await asyncio.wait_for(reader.readline(), 10)
        if not line:
            return
        parts = line.decode("latin-1").split()
        if len(parts) != 3:
            await respond(writer, 400, "Bad Request")
            return

        method, path, _ = parts
        headers = {}
        for _ in range(100):
            raw = await asyncio.wait_for(reader.readline(), 10)
            if raw in (b"\r\n", b"\n", b""):
                break
            key, _, value = raw.decode("latin-1").partition(":")
            headers[key.strip().lower()] = value.strip()

        if method == "POST":
            await self.upload(headers, reader, writer)
        elif method in ("GET", "HEAD"):
            await self.download(method, path, headers, writer)
        else:
            await respond(writer, 405, "Method Not Allowed")

    async def upload(self, headers, reader, writer):
        length = headers.get("content-length", "")
        if not length.isdigit():
            await respond(writer, 411, "Length Required")
            return

        size = int(length)
        if size > self.max_size:
            await respond(writer, 413, "Payload Too Large")
            return

        if headers.get("expect", "").lower() == "100-continue":
            writer.write(b"HTTP/1.1 100 Continue\r\n\r\n")
            await writer.drain()

        body = await asyncio.wait_for(reader.readexactly(size), 120)
        part = parse_upload(headers.get("content-type", ""), body)
        if part is None:
            await respond(writer, 400, "Bad Request")
            return

        name, ctype, data = part
        token = await asyncio.to_thread(self.store, name, ctype, data)
        until = time.strftime(
            "%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() + self.ttl)
        )
        url = f"http://{self.host}:{self.port}/{token}"
        xml = (
            '<?xml version="1.0" encoding="UTF-8"?>\r\n'
            '<file xmlns="urn:gsma:params:xml:ns:rcs:rcs:fthttp">\r\n'
            '<file-info type="file">\r\n'
            f"<file-size>{len(data)}</file-size>\r\n"
            f"<file-name>{escape(name)}</file-name>\r\n"
            f"<content-type>{escape(ctype)}</content-type>\r\n"
            f"<data url={quoteattr(url)} until={quoteattr(until)}/>\r\n"
            "</file-info>\r\n</file>\r\n"
        )
        await respond(writer, 200, "OK", xml.encode(), "application/xml")

    async def download(self, method, path, headers, writer):
        m = re.fullmatch(r"/([0-9a-f]{40})", path.split("?")[0])
        if not m:
            await respond(writer, 404, "Not Found")
            return

        try:
            data = await asyncio.to_thread(self.load, m.group(1))
        except OSError:
            await respond(writer, 404, "Not Found")
            return

        total = len(data)
        extra = [
            ("Content-Disposition", "attachment"),
            ("X-Content-Type-Options", "nosniff"),
            ("Accept-Ranges", "bytes"),
        ]
        code, reason = 200, "OK"
        span = re.fullmatch(r"bytes=(\d*)-(\d*)", headers.get("range", ""))

        if span and (span.group(1) or span.group(2)):
            if span.group(1):
                first = int(span.group(1))
                last = int(span.group(2)) if span.group(2) else total - 1
            else:
                suffix = int(span.group(2))
                first = max(total - suffix, 0)
                last = total - 1

            last = min(last, total - 1)
            if first >= total or first > last:
                await respond(
                    writer, 416, "Range Not Satisfiable",
                    extra=[("Content-Range", f"bytes */{total}")],
                )
                return

            data = data[first:last + 1]
            code, reason = 206, "Partial Content"
            extra.append(("Content-Range", f"bytes {first}-{last}/{total}"))

        body = b"" if method == "HEAD" else data
        await respond(
            writer, code, reason, body,
            "application/octet-stream", extra, length=len(data),
        )


def read_conf(path):
    parser = configparser.ConfigParser(interpolation=None)
    if not parser.read(path) or not parser.has_section("sipd"):
        sys.exit(f"cannot read a [sipd] section from {path}")

    conf = parser["sipd"]
    missing = [key for key in REQUIRED if key not in conf]
    if missing:
        sys.exit(f"missing in {path}: {', '.join(missing)}")

    base = os.path.dirname(os.path.abspath(path))
    for key in ("users_file",):
        if conf[key]:
            conf[key] = os.path.join(base, conf[key])
    return conf


async def main():
    if len(sys.argv) != 2:
        sys.exit("usage: o1.py <o1.conf>")

    conf = read_conf(sys.argv[1])

    log_path = conf.get("log_file", "").strip()
    if log_path:
        log_path = os.path.expanduser(log_path)
        log_path = os.path.abspath(
            os.path.join(os.path.dirname(os.path.abspath(sys.argv[1])), log_path)
            if not os.path.isabs(log_path) else log_path
        )
        os.makedirs(os.path.dirname(log_path), exist_ok=True)
        log_handler = logging.FileHandler(log_path)
        log_handler.setFormatter(
            logging.Formatter("%(asctime)s %(levelname)s %(message)s")
        )
        logging.basicConfig(level=logging.INFO, handlers=[log_handler])
        sys.stdout = open(log_path, "a", buffering=1)
        sys.stderr = sys.stdout
        print(f"Logging to {log_path}")
    else:
        logging.basicConfig(level=logging.INFO)

    loop = asyncio.get_running_loop()

    _, server = await loop.create_datagram_endpoint(
        lambda: SipServer(conf),
        local_addr=(conf["bind"], conf.getint("port")),
    )

    loop.add_signal_handler(signal.SIGHUP, server.reload_users)

    if conf.get("media_dir", "").strip():
        media = MediaServer(conf)
        await asyncio.start_server(
            media.handle, conf["bind"], conf.getint("http_port")
        )
        asyncio.create_task(media.purge_loop())
        print(
            f"media server on {conf['bind']}:{conf['http_port']}",
            file=sys.stderr,
        )

    mode = "digest auth" if conf["users_file"] else "open"
    print(
        f"o1 listening on {conf['bind']}:{conf['port']} "
        f"as {conf['host']} ({mode})",
        file=sys.stderr,
    )

    await asyncio.Event().wait()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass

