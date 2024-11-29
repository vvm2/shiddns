from re import Pattern
import re
import struct

RX_DNAME: Pattern = re.compile(r"^(|([0-9a-zA-Z-]+\.)*[0-9a-zA-Z-]+)$")

TYPE_A = 1
TYPE_NS = 2
TYPE_MD = 3
TYPE_MF = 4
TYPE_CNAME = 5
TYPE_SOA = 6
TYPE_MB = 7
TYPE_MG = 8
TYPE_MR = 9
TYPE_NULL = 10
TYPE_WKS = 11
TYPE_PTR = 12
TYPE_HINFO = 13
TYPE_MINFO = 14
TYPE_MX = 15
TYPE_TXT = 16

QTYPE_AXFR = 252
QTYPE_MAILB = 253
QTYPE_MAILA = 254
QTYPE_ALL = 255

CLASS_IN = 1
CLASS_CS = 2
CLASS_CH = 3
CLASS_HS = 5
QCLASS_ALL = 255


def bin_dump(data: bytes) -> str:
    """Debug method to dump bytes to a string representation"""
    s: str = str(data)
    s += "\n\n"
    dlen: int = len(data)

    k: int = 0
    while k < (dlen // 16):
        i = 0
        while i < 16:
            s += "%02x " % data[k * 16 + i]
            i += 1
        s += " " * 8
        i = 0
        while i < 16:
            s += chr(data[k * 16 + i]) if data[k * 16 + i] >= 32 else "."
            i += 1
        k += 1
        s += "\n"

    i = k * 16
    while i < dlen:
        s += "%02x " % data[i]
        i += 1

    s += " " * ((k + 1) * 16 - i + 8)
    i = k * 16
    while i < dlen:
        s += chr(data[i]) if data[i] >= 32 else "."
        i += 1
    s += "\n"

    return s


class MessageParser:
    def __init__(self):
        self.lmap: dict[str, int] = {}

    def _parse_labels(
        self, data: bytes, offset: int, stack: list[int]
    ) -> tuple[int, list[str]]:
        """parse labels (a sequence of labels is the domain name) from a byte stream,
        the format is either:
        1. a pointer (bits 7 and 6 are high, the remainder a pointer into data)
        2. a sequence of labels ending in a pointer
        3. a sequence of labels ending in ONE zero byte

        Parameters
        ----------
        data (bytes): the byte buffer to parse the labels from
        offset (int): pointer into data where to start parsing
        stack (list[int]): offset call stack to prevent reference loops with
        pointers in case of malformed packets

        Returns
        -------
        (tuple[int,list[str]]): (offset after parsing, list or parsed labels)
        """
        dlen: int = len(data)
        if offset >= dlen:
            raise ParseException("message too short")

        k: int = 1
        p: int = 0  # p ointer to current position into data buffer
        label: str = ""
        result: list[str] = []

        while k > 0:
            if dlen <= offset + p:
                raise ParseException("data too short to parse labels")

            # read length byte - format is pascal string eg. [5][h][e][l][l][o]
            k = data[offset + p]
            p += 1

            # is this a pointer? (bits 6,7 are set)
            if k & 0xC0 == 0xC0:
                # pointer is 2-bytes 11XXXXXX YYYYYYYY
                # 1. clear the high bits (& 00111111(=0x3f))
                # 2. move over 8 bits 00XXXXXX 00000000 (<< 8)
                # 3. set the bits of the lower bty (| YYYYYYYY (data[offset+p])) -> 00XXXXXX YYYYYYYY
                k = (k & 0x3F) << 8 | data[offset + p]
                # a pointer is 2 bytes (for alignment i guess)
                p += 1
                # do we have a pointer loop?
                if k in stack:
                    raise ParseException("bad looping is bad!")

                stack.append(k)
                r: tuple[int, list[str]] = self._parse_labels(data, k, stack)
                stack.pop()

                # add to result and return! the pointer is the end
                # of the story or a 0 byte
                result.extend(r[1])
                return (offset + p, result)
            elif k > 0:
                if dlen < offset + p + k:
                    raise ParseException("data too short to parse labels")

                label: str = data[offset + p : offset + p + k].decode()
                result.append(label)
                p += k

        return (offset + p, result)

    def parse(self, data: bytes, offset: int) -> int:
        return 0


class MessageBuilder:
    def _build_labels(self, domain: str) -> bytearray:
        if domain is None or RX_DNAME.match(domain) is None:
            raise ParseException(f"invalid domain name: {domain}")

        labels: list[str] = domain.split(".")
        k: int = 0

        for next in labels:
            k += len(next) + 1

        # +1 for the null label
        qs = bytearray(k + 1)
        k = 0
        for i in range(len(labels)):
            s: bytes = labels[i].encode()
            struct.pack_into("%dp" % min(len(s) + 1, 255), qs, k, labels[i].encode())
            k += len(labels[i]) + 1

        # make sure 0 byte is set
        qs[-1] = 0

        return qs

    def build(self) -> bytes:
        return bytes(0)


class Question(MessageParser, MessageBuilder):
    def __str__(self) -> str:
        return f"qname: {self.qname} qtype: {self.qtype} qclass: {self.qclass}\n"

    def __init__(self):
        self.qname: str = ""
        self.qtype: int = 0
        self.qclass: int = 0

    def build(self) -> bytes:
        qs: bytearray = self._build_labels(self.qname)
        k: int = len(qs)

        # 4 bytes for qtype + qclass
        qs.extend(b"\x00\x00\x00\x00")
        struct.pack_into("!H", qs, k, self.qtype)
        struct.pack_into("!H", qs, k + 2, self.qclass)
        return bytes(qs)

    def parse(self, data: bytes, offset: int) -> int:
        dlen: int = len(data)
        offs: int = offset
        np, lb = self._parse_labels(data, offs, [])
        offs = np

        self.qname = ".".join(lb)
        if dlen < offs + 4:
            raise ParseException("data too short to parse question")

        self.qtype = struct.unpack("!H", data[offs : offs + 2])[0]
        offs += 2
        self.qclass = struct.unpack("!H", data[offs : offs + 2])[0]
        offs += 2

        return offs


class ResourceRecord(MessageParser, MessageBuilder):
    def __str__(self) -> str:
        s: str = f"name: {self.name} type: {self.type} class: {self.clazz} ttl: {self.ttl} rdlength: {self.rdlength}\nrdata:\n"
        s += bin_dump(self.rdata)
        return s

    def __init__(self):
        self.name: str = ""
        self.type: int = 0
        self.clazz: int = 0
        self.ttl: int = 0
        self.rdlength: int = 0
        self.rdata: bytes = b""

    def build(self) -> bytes:
        if self.name is None or RX_DNAME.match(self.name) is None:
            raise ParseException(f"invalid domain name: {self.name}")

        qs: bytearray = self._build_labels(self.name)
        k: int = len(qs)

        # +10 for type, class, ttl, rdlength
        qs.extend(b"\x00" * 10)
        struct.pack_into("!H", qs, k, self.type)
        struct.pack_into("!H", qs, k + 2, self.clazz)
        struct.pack_into("!L", qs, k + 4, self.ttl)
        struct.pack_into("!H", qs, k + 8, self.rdlength)
        qs.extend(self.rdata)
        return bytes(qs)

    def parse(self, data: bytes, offset: int) -> int:
        dlen: int = len(data)
        offs: int = offset

        np, lb = self._parse_labels(data, offs, [])
        offs = np
        self.name = ".".join(lb)

        if dlen < offs + 2:
            raise ParseException("data too short")
        self.type = struct.unpack("!H", data[offs : offs + 2])[0]
        offs += 2

        if dlen < offs + 2:
            raise ParseException("data too short")
        self.clazz = struct.unpack("!H", data[offs : offs + 2])[0]
        offs += 2

        if dlen < offs + 4:
            raise ParseException("data too short")
        self.ttl = struct.unpack("!I", data[offs : offs + 4])[0]
        offs += 4

        if dlen < offs + 2:
            raise ParseException("data too short")
        self.rdlength = struct.unpack("!H", data[offs : offs + 2])[0]

        offs += 2
        if dlen < offs + self.rdlength:
            raise ParseException("data too short")

        self.rdata = data[offs : offs + self.rdlength]
        offs += self.rdlength

        return offs

    def fill_a_record(self, name: str, ttl: int, ip: str) -> None:
        if ip is None:
            raise ParseException("A record: ip cannot be none")

        tmp: list[str] = ip.split(".")
        if len(tmp) != 4:
            raise ParseException("A record: needs IPv4 address format")

        bip: bytearray = bytearray(4)
        k: int = 0
        while k < 4:
            try:
                i: int = int(tmp[k])
                if i < 0 or i > 255:
                    raise ParseException("A record: needs IPv4 address format")
                struct.pack_into("!B", bip, k, i)

            except ValueError:
                raise ParseException("A record needs: IPv4 address format")

            k += 1
        self.name = name
        self.ttl = ttl
        self.clazz = CLASS_IN
        self.type = TYPE_A
        self.rdlength = 4
        self.rdata = bytes(bip)

    def fill_ptr_record(self, name: str, ttl: int, domain: str) -> None:
        self.name = name
        self.ttl = ttl
        self.clazz = CLASS_IN
        self.type = TYPE_PTR
        self.rdata = bytes(self._build_labels(domain))
        self.rdlength = len(self.rdata)


class Message(MessageParser, MessageBuilder):
    def __str__(self) -> str:
        head: str = (
            f"id: {self.id}\nqr: {self.qr}\nopcode: {self.opcode}\naa: {self.aa}\ntc: {self.tc}\nrd: {self.rd}\n"
            f"ra: {self.ra}\nrcode: {self.rcode}\nz: {self.z}\nad: {self.ad}\ncd: {self.cd}\n"
        )
        head += "questions:\n"
        for next in self.question:
            head += str(next)

        head += "anwers:\n"
        for next in self.answer:
            head += str(next)

        head += "authority:\n"
        for next in self.authority:
            head += str(next)

        head += "additional:\n"
        for next in self.additional:
            head += str(next)

        return head

    def __init__(self):
        self.orig_pkg: bytearray | None = None

        self.id: int = 0
        self.qr = 0
        self.opcode = 0
        self.aa = 0
        self.tc = 0
        self.rd = 0
        self.ra = 0
        self.rcode = 0
        self.z = 0
        self.ad = 0
        self.cd = 0

        self.question: list[Question] = []
        self.answer: list[ResourceRecord] = []
        self.authority: list[ResourceRecord] = []
        self.additional: list[ResourceRecord] = []

    def __build_header(self, dns_pkg: bytearray) -> None:
        struct.pack_into("!H", dns_pkg, 0, self.id)
        tmp = self.qr << 4
        tmp = (tmp | self.opcode) << 1
        tmp = (tmp | self.aa) << 1
        tmp = (tmp | self.tc) << 1
        tmp = (tmp | self.rd) << 1
        tmp = (tmp | self.ra) << 1
        tmp = (tmp | self.z) << 1
        tmp = (tmp | self.ad) << 1
        tmp = (tmp | self.cd) << 4
        tmp = tmp | self.rcode
        struct.pack_into("!H", dns_pkg, 2, tmp)

    def build_from_orig_with_header(self) -> bytes | None:
        """if this message was parsed, then the original packages
        as bytes is safed. this method can be used to return the
        original bytes parsed with an adjusted header. this is usefull
        to return errors without having to rebuild the whole packet

        **NOTE**: garbage in - garbage out, so beware!

        Returns
        -------
        the original dns request bytes with adjusted header bytes!
        """
        if self.orig_pkg is not None:
            self.__build_header(self.orig_pkg)
            return bytes(self.orig_pkg)

        return None

    def build(self) -> bytes:
        hd: bytearray = bytearray(12)
        self.__build_header(hd)

        struct.pack_into("!H", hd, 4, len(self.question))
        struct.pack_into("!H", hd, 6, len(self.answer))
        struct.pack_into("!H", hd, 8, len(self.authority))
        struct.pack_into("!H", hd, 10, len(self.additional))

        for next in self.question:
            hd.extend(next.build())

        for next in self.answer:
            hd.extend(next.build())

        for next in self.authority:
            hd.extend(next.build())

        for next in self.additional:
            hd.extend(next.build())

        return bytes(hd)

    def parse(self, data: bytes, offset: int) -> int:
        self.orig_pkg = bytearray(data)

        offs: int = offset
        if len(data) < offs + 12:
            raise ParseException("data too short to parse header")

        self.id = struct.unpack("!H", data[offs : offs + 2])[0]
        tmp: int = struct.unpack("!H", data[offs + 2 : offs + 4])[0]
        self.rcode = tmp & 0xF
        tmp = tmp >> 4
        self.cd = tmp & 0x1
        tmp = tmp >> 1
        self.ad = tmp & 0x1
        tmp = tmp >> 1
        self.z = tmp & 0x1
        tmp = tmp >> 1
        self.ra = tmp & 0x1
        tmp = tmp >> 1
        self.rd = tmp & 0x1
        tmp = tmp >> 1
        self.tc = tmp & 0x1
        tmp = tmp >> 1
        self.aa = tmp & 0x1
        tmp = tmp >> 1
        self.opcode = tmp & 0xF
        tmp = tmp >> 4
        self.qr = tmp & 0x1

        qdcount: int = struct.unpack("!H", data[offs + 4 : offs + 6])[0]
        ancount: int = struct.unpack("!H", data[offs + 6 : offs + 8])[0]
        nscount: int = struct.unpack("!H", data[offs + 8 : offs + 10])[0]
        arcount: int = struct.unpack("!H", data[offs + 10 : offs + 12])[0]

        offs += 12

        while qdcount > 0:
            q: Question = Question()
            offs = q.parse(data, offs)
            self.question.append(q)
            qdcount -= 1

        while ancount > 0:
            ans: ResourceRecord = ResourceRecord()
            offs = ans.parse(data, offs)
            self.answer.append(ans)
            ancount -= 1

        while nscount > 0:
            auth: ResourceRecord = ResourceRecord()
            offs = auth.parse(data, offs)
            self.authority.append(auth)
            nscount -= 1

        while arcount > 0:
            add: ResourceRecord = ResourceRecord()
            offs = add.parse(data, offs)
            self.additional.append(add)
            arcount -= 1

        return offs


class ParseException(Exception):
    def __init__(self, message):
        super().__init__(message)
