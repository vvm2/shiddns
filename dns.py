import asyncio
import grp
import json
import logging
import os
import pwd
import re
import urllib
import urllib.request
from asyncio.events import AbstractEventLoop
from asyncio.transports import DatagramTransport
from re import Pattern, error
from threading import Lock
from typing import Any

from message import (
    CLASS_IN,
    TYPE_A,
    TYPE_CNAME,
    TYPE_PTR,
    Message,
    Question,
    ResourceRecord,
)


def is_private_address(ip: str) -> bool:
    if ip is None:
        return False

    tmp: list[str] = ip.split(".")
    if len(tmp) != 4:
        return False

    try:
        a = int(tmp[0])
        b = int(tmp[1])
        c = int(tmp[2])
        d = int(tmp[3])

        if a < 0 or b < 0 or c < 0 or d < 0 or a > 255 or b > 255 or c > 255 or d > 255:
            return False

        if a == 10 or (a == 172 and b == 16) or (a == 192 and b == 168):
            return True

    except ValueError:
        pass

    return False


class InvalidFormatException(Exception):
    def __init__(self, message):
        super().__init__(message)


class DomainTree:
    """class to store domain labels in a tree form for non-redundant storing
    and quick search for the purpose block and allow listing of domain queries
    """

    def __init__(self) -> None:
        self.children: list[DomainTree] = []
        self.label: str = ""
        self.is_leaf: bool = False
        self.allow: bool = False
        self.cache: list[ResourceRecord] | None = None

    def __lin_search_child(self, find: str) -> int:
        i: int = -1
        while (i + 1) < len(self.children) and self.children[i + 1].label < find:
            i += 1

        if (i + 1) < len(self.children) and self.children[i + 1].label == find:
            return i + 1

        return i

    def __bin_search_child(self, find: str) -> int:
        min: int = 0
        max: int = len(self.children) - 1

        while min <= max:
            k: int = min + (max - min) // 2
            if self.children[k].label == find:
                return k

            if self.children[k].label < find:
                min = k + 1
            else:
                max = k - 1

        return max

    def search_child(self, label: str) -> int:
        if len(self.children) < 15:
            return self.__lin_search_child(label)
        return self.__bin_search_child(label)

    def add_domain(self, domain: str) -> None:
        """split a domain in lables and insert the labels uniquely
        into the tree (self).

        Parameters
        ----------
        domain (str): the fqdn to add to the domain tree
        """
        current: DomainTree = self
        tmp: list[str] = domain.split(".")

        while len(tmp) > 0:
            label: str = tmp.pop()
            k: int = current.search_child(label)

            # did we find the child?
            if k >= 0 and current.children[k].label == label:
                current = current.children[k]
            else:
                new_node = DomainTree()
                new_node.label = label
                current.children.insert(k + 1, new_node)
                current = current.children[k + 1]

        # last inserted node is a leaf of a domain
        # think to insert: ads.socal.com and more.ads.social.com
        # the "ads" label is not a leaf in the sence of a tree leaf but in
        # the sense of a domain leaf, yes
        current.is_leaf = True

    def has_match(self, domain: str) -> bool:
        labels: list[str] = domain.split(".")
        in_game: list[DomainTree] = [self]
        while len(in_game) > 0 and len(labels) > 0:
            # pop() to go from TLD to subdomain (reverse order of string)
            cur_label: str = labels.pop()
            new_game: list[DomainTree] = []

            while len(in_game) > 0:
                next: DomainTree = in_game.pop()
                # if we are sitting on a wildcard, include it in
                # the next round.
                if next.label == "*":
                    new_game.append(next)

                if len(next.children) > 0:
                    k: int = next.search_child(cur_label)
                    # if we found the actual label in one of the child nodes,
                    # then include the child in the next round.
                    if k >= 0 and next.children[k].label == cur_label:
                        # print(
                        #    f"found: {next.children[k]} -- {next.children[k].label}//{next.children[k].is_leaf}"
                        # )
                        new_game.append(next.children[k])

                    # lucky for us, the * symbol is in sorting order
                    # the first character of all valid domain label chars
                    if next.children[0].label == "*":
                        # print(
                        #    f"found: {next.children[0]} -- {next.children[0].label}//{next.children[0].is_leaf}"
                        # )
                        new_game.append(next.children[0])

            # new round - new luck
            in_game = new_game

        while len(in_game) > 0:
            next: DomainTree = in_game.pop()
            if next.is_leaf:
                return True

        return False

    def print_tree(self, level: int):
        prefix: str = "  " * level
        print(f"{prefix}{self.label}")
        for next in self.children:
            next.print_tree(level + 1)

    def as_string(self) -> str:
        res: str = "*" + self.label if self.is_leaf else self.label
        if len(self.children) == 0:
            return res

        res += "("
        children: list[str] = []
        for child in self.children:
            children.append(child.as_string())
        return res + ",".join(children) + ")"

    def from_string(self, string: str, pos: int) -> int:
        k: int = pos
        if string[k] == "*":
            self.is_leaf = True
            pos += 1
            k += 1
        # (com(cache(*image),*reddit(*old)),net(*x))
        while (
            k < len(string)
            and string[k] != "("
            and string[k] != ","
            and string[k] != ")"
        ):
            k += 1

        self.label = string[pos:k]
        if string[k] == ")":
            return k

        if string[k] == "(":
            while k < len(string) and string[k] != ")":
                new_child: DomainTree = DomainTree()
                k = new_child.from_string(string, k + 1)
                self.children.append(new_child)

        return k + 1


class DNSFilter:
    """DNS filter logic implementing loading of filter configuration,
    filtering dns names and regular exceptions
    """

    content_cache: dict = {}
    """static cache to avoid downloading and parsing resources multiple
    times from the internet during the initialization of the different filters
    """

    def __init__(self, name: str, storage_path: str) -> None:
        self.name = name
        """the filter name is used for storing downloaded lists
        """

        self.default_allow = True
        """defines the default action if no rule applies, if set to true,
        queries are by default resolved.
        """

        self.storage_path = storage_path
        """the path to store the block and allow lists once downloaded
        """

        self.block_src: list[str] = []
        """list of URLs to download DNS names and regular expressions that
        should be blocked. format is <type>:<url> - e.g. hosts:http://github.com/repo/master/bla/blub/block
        or rx:file:///tmp/rxblocks.txt
        """

        self.allow_src: list[str] = []
        """see block_src, only for the allow lists
        """

        self.block: DomainTree | None = None
        """tree implementation for fast lookup of blocked
        domains read from various hosts files
        """

        self.block_rx: list[Pattern] | None = None
        """list of regex patterns that filter blocked dns names
        """

        self.allow: DomainTree | None = None
        """see block - only for allow lists
        """

        self.allow_rx: list[Pattern] | None = None
        """see block_rx - only for allow lists
        """

    def __get_content(self, url: str) -> str:
        """read allow/block list via http or local file for
        further processing
        """

        txt: str = ""
        if url not in DNSFilter.content_cache:
            req = urllib.request.urlopen(url)
            content: bytes = req.read()
            txt = content.decode()
        else:
            txt = DNSFilter.content_cache[url]

        return txt

    def __gen_local_storage_path(self, suffix: str) -> str:
        base_path: str = self.storage_path
        if not base_path.endswith("/"):
            base_path += "/"

        # replace all . and / and \ with _ to avoid nasty path things
        # if people do stupid stuff with filter names and suffixes
        forbidden: Pattern = re.compile(r"(\.|/|\\)")
        name: str = forbidden.sub("_", self.name)
        suffix = forbidden.sub("_", suffix)

        return base_path + name + "_" + suffix

    def __download_hosts_list(self, dt: DomainTree, location: str, suffix: str):
        rx: Pattern = re.compile(r"[ ]*#.*$")
        txt: str = self.__get_content(location)
        for line in txt.split("\n"):
            # remove everything after and including the hash (comment)
            s: str = rx.sub("", line)
            s = s.strip()

            # skip comments and empty lines
            if len(s) > 0:
                # format example: 0.0.0.0 some.blocked.dns.name
                blk: list[str] = s.split(" ")
                if len(blk) != 2:
                    # warn but don't stop (believing)
                    logging.warn(f"invalid hosts entry in {location}: {s}")
                else:
                    dt.add_domain(blk[1])

        if self.storage_path is not None:
            f = open(self.__gen_local_storage_path(suffix), "w")  # overwrite!
            f.write(dt.as_string())
            f.close()

    def __download_regex_list(self, rl: list[str], location: str, suffix: str):
        txt: str = self.__get_content(location)
        for line in txt.split("\n"):
            s: str = line.strip()
            # skip comments and empty lines
            if len(s) > 0 and s[0] != "#":
                try:
                    # test if the regex compiles correctly!
                    re.compile(s)
                    rl.append(s)
                except error:
                    # warn but dont stop
                    logging.warn(f"invalid regular expression '{s}' in {location}.")

        if self.storage_path is not None:
            f = open(self.__gen_local_storage_path(suffix), "w")  # overwrite!
            f.write("\n".join(rl))
            f.write("\n")
            f.close()

    def download_lists(self, src_list: list[str], suffix: str) -> None:
        hosts: DomainTree | None = None
        rx: list[str] = []

        for next in src_list:
            tmp: list[str] = next.split(":", 1)
            if len(tmp) != 2:
                raise InvalidFormatException(
                    f"invalid block src reference in config.json: {next}"
                )

            if tmp[0] == "hosts":
                if hosts is None:
                    hosts = DomainTree()
                self.__download_hosts_list(hosts, tmp[1], suffix)

            elif tmp[0] == "rx":
                self.__download_regex_list(rx, tmp[1], suffix + "_rx")
            else:
                raise InvalidFormatException(
                    f"invalid block src type identifyer in config.json: '{tmp[0]}'"
                )

    def update(self) -> None:
        """download or load all block and allow lists from the
        source repositories and build the local_storage files that are
        loaded with the load() method
        """
        if self.block_src is not None:
            self.download_lists(self.block_src, "block")

        if self.allow_src is not None:
            self.download_lists(self.allow_src, "allow")

    def __load_domain_tree(self, suffix: str) -> DomainTree | None:
        path: str = self.__gen_local_storage_path(suffix)
        if os.path.exists(path):
            f = open(path, "r")
            tmp: str = f.read()
            f.close()

            if len(tmp) > 0:
                dt = DomainTree()
                dt.from_string(tmp, 0)
                return dt

        return None

    def __load_rx_list(self, suffix: str) -> list[Pattern] | None:
        path: str = self.__gen_local_storage_path(suffix)
        if os.path.exists(path):
            f = open(path, "r")
            tmp: list[str] = f.readlines()
            f.close()

            if len(tmp) > 0:
                rx_list: list[Pattern] = []
                for next in tmp:
                    # use ^ and $ - we will strip leading and trainling whitespace
                    next = next.strip()
                    try:
                        rx_list.append(re.compile(next))
                    except error:
                        # here we raise an exception, the local
                        # storage files should not be edited!
                        raise InvalidFormatException(
                            f"invalid regex {next} in {self.name} -> {suffix}"
                        )
                return rx_list
        return None

    def load(self) -> None:
        """load the locally stored block and allow lists. it is important that
        at time of the service (__init__) startup, no internet DNS queries are done,
        because the name resolution is not yet available. python also relies
        on the servers DNS configuration. if the configuration points to this service,
        the dog would bite it's own tail here.
        """

        self.block = self.__load_domain_tree("block")
        self.block_rx = self.__load_rx_list("block_rx")
        self.allow = self.__load_domain_tree("allow")
        self.allow_rx = self.__load_rx_list("allow_rx")

    def is_allowed(self, domain: str) -> bool:
        """check if the filter allows a certain domain to be resolved. the logic is
        1. set default_allow as starting permission
        2. if default allows, then check block lists
        3. if still allowed, then check allow lists

        so if a block list blocks a certain site and then the allow list opens it up
        again, the final result will be that the domain is allowed.

        Parameters
        ----------
            domain (str): the domain name that should be checked (should be fqdn to function)

        Returns
        -------
           (bool): True if the domain is allowed to be resolved, else False
        """
        allow: bool = self.default_allow

        if allow and self.block is not None:
            allow = not self.block.has_match(domain)

        if allow and self.block_rx is not None:
            k: int = 0
            while allow and k < len(self.block_rx):
                allow = self.block_rx[k].match(domain) is None
                k += 1

        if not allow and self.allow is not None:
            allow = self.allow.has_match(domain)

        if not allow and self.allow_rx is not None:
            k: int = 0
            while not allow and k < len(self.allow_rx):
                allow = self.allow_rx[k].match(domain) is not None
                k += 1

        return allow


class DNS:
    """main DNS resolver class, this class is implementing the high-level logic
    such as configuration loading and parsing, and orchestrating the DNS resolution
    and filtering
    """

    def __load_config(self) -> dict[str, Any]:
        f = open(self.config_path, "r")
        config: dict = json.load(f)
        f.close()

        # TODO: do plausibility/format checks
        return config

    def __init__(self, config_path: str) -> None:
        """loads the filter configuration (as json) provided in the
        config_path parameter

        Parameters
        ----------
        config_path (str): absolute path to the json filter config file

        """
        self.running = True
        self.config_path = config_path
        self.lock: Lock = Lock()

        # load config and do plausibility / format checking,
        # this will raise an InvalidFormatException if needed
        config: dict[str, Any] = self.__load_config()

        # set service user and group if service is started as root (necessary for
        # running on port UDP 53)
        self.daemon_user: str = config["service"]["user"]
        self.daemon_group: str = config["service"]["group"]

        # local file to communicate with this service (mid-term replace with socket!)
        self.control_file: str = config["service"]["control"]
        self.log_dir: str = config["storage"]["log"]

        # key = ip (str), value = (dnsname (str), filter_id (str))
        # used for reverse lookups of local network
        self.known_ips: dict[str, tuple[str, str]] = {}

        # key = dnsname (str), value = (ip (str), filter_id (str))
        # used for forward lookups of local network
        self.known_names: dict[str, tuple[str, str]] = {}

        self.host: str = config["network"]["host"]
        self.port: int = config["network"]["port"]
        self.upstream_host: str = config["network"]["upstream_host"]
        self.upstream_port: int = config["network"]["upstream_port"]

        self.local_domain = config["localdns"]["domain"]
        dns_entries: list[dict] = config["localdns"]["entries"]
        for entry in dns_entries:
            filter: str = entry["filter"] if "filter" in entry else "default"
            # can happen if json is assinged with null
            if filter is None:
                filter = "default"
            self.known_ips[entry["ip"]] = (entry["name"], filter)
            self.known_names[entry["name"]] = (entry["ip"], filter)

        self.filters: dict[str, DNSFilter] = {}
        dff: DNSFilter = DNSFilter("default", config["storage"]["filter"])
        dff.default_allow = config["filters"]["default"]["default_allow"]
        dff.allow_src = config["filters"]["default"]["allow_src"]
        dff.block_src = config["filters"]["default"]["block_src"]
        self.filters[dff.name] = dff

        # ensure all filters are configured
        for k in config["filters"]:
            # ignore the default filter
            if k != "default":
                dnsf = DNSFilter(k, config["storage"]["filter"])
                if "default_allow" in config["filters"][k]:
                    dnsf.default_allow = config["filters"][k]["default_allow"]
                else:
                    dnsf.default_allow = dff.default_allow

                if "allow_src" in config["filters"][k]:
                    dnsf.allow_src = config["filters"][k]["allow_src"]
                else:
                    dnsf.allow_src = dff.allow_src.copy()

                if "block_src" in config["filters"][k]:
                    dnsf.block_src = config["filters"][k]["block_src"]
                else:
                    dnsf.block_src = dff.block_src.copy()

                self.filters[k] = dnsf

        # load local filter rules
        for k in config["filters"]:
            self.filters[k].load()

    def __msg_flag_return(self, message, rcode):
        """set all the right flags to return the given
        message as error, providing
        """
        message.qr = 1
        message.ra = 1
        message.rcode = rcode

    def __resolve_local_fw(self, dns_request: Message) -> Message | None:
        """resolve the given query locally (authoratative) if possible

        **IMPORTANT**: this method assumes that the dns_request has already be
        checked and the query contains exactly 1 question! (not 2 or 5, not 6 or 9 - no 1 shall it be)

        Parameters
        ----------
        dns_request (Message): the message with the request.

        Returns
        -------
        (Message|None)
        None: if the query is not a forward query (opcode=0) requesting a local ip or dns name
        else
        Message: the dns response with the respective error/success codes and/or resource records
        """

        # fw lookups require standard query operation (0)
        if dns_request.opcode != 0:
            return None

        dns_response: Message = dns_request

        # at this point we already know the request has
        # exactly 1!!! question
        q: Question = dns_request.question[0]
        domain: str | None = q.qname

        # check if the domain is our own
        ld = "." + self.local_domain
        if not domain.endswith(ld):
            return None

        # check for query class and type
        if q.qclass != CLASS_IN or q.qtype not in (TYPE_A, TYPE_CNAME, TYPE_PTR):
            self.__msg_flag_return(dns_response, 4)  # not implemented
            return dns_response

        lup = self.local_fw_lookup(domain)
        if lup is not None:
            self.__msg_flag_return(dns_response, 0)
            dns_response.aa = 1

            rr: ResourceRecord = ResourceRecord()
            rr.fill_a_record(q.qname, 0, lup[0])
            dns_response.answer.append(rr)
            dns_response.additional.clear()

        else:
            self.__msg_flag_return(dns_response, 3)  # NXDOMAIN

        return dns_response

    def __resolve_local_rv(self, dns_request: Message) -> Message | None:
        """reverse resolve the given query locally (authoratative) if possible

        **IMPORTANT**: this method assumes that the dns_request has already be
        checked and the query contains exactly 1 question! (not 2 or 5, not 6 or 9 - no 1 shall it be)

        Parameters
        ----------
        dns_request (Message): the message with the request.

        Returns
        -------
        (Message|None)
        None: if the query is not a reverse query (opcode=1) requesting a local ip or dns name
        else
        Message: the dns response with the respective error/success codes and/or resource records
        """
        # fw lookups require reverse (inverse) query operation (1)
        if dns_request.opcode != 0:
            return None

        dns_response: Message = dns_request

        # at this point we already know the request has
        # exactly 1!!! question
        q: Question = dns_request.question[0]
        domain: str | None = q.qname

        # check if local resolution is possible
        if not domain.endswith(".in-addr.arpa"):
            return None

        # remove .in-addr.arpa ending
        domain = domain[: -len(".in-addr.arpa")]

        # for the love of god why? 1.2.3.4 is 4.3.2.1.in-addr.arpa
        # extra processing for fun and profit?
        labels: list[str] = domain.split(".")
        labels.reverse()
        domain = ".".join(labels)

        # we can only resolve local addresses
        if not is_private_address(domain):
            return None

        # check for query class and type
        if q.qclass != CLASS_IN or q.qtype != TYPE_PTR:
            self.__msg_flag_return(dns_response, 1)  # format error
            return dns_response

        # at this point we know we can resolve
        lup = self.local_rv_lookup(domain)
        if lup is not None:
            self.__msg_flag_return(dns_response, 0)  # all good in bollywood
            self.aa = 1

            rr: ResourceRecord = ResourceRecord()
            rr.fill_ptr_record(q.qname, 0, lup[0])
            dns_response.answer.append(rr)
            dns_response.additional.clear()

        # is private but cannot be resolved!
        else:
            self.__msg_flag_return(dns_response, 3)  # NXDOMAIN

        return dns_response

    async def __resolve_remote(
        self,
        data: bytes,
        client_transport: DatagramTransport,
        client_address: tuple[str, int],
    ) -> None:
        upstream_server: tuple[str, int] = (
            self.upstream_host,
            self.upstream_port,
        )
        on_con_lost: asyncio.Future = loop.create_future()
        trans, proto = await asyncio.get_event_loop().create_datagram_endpoint(
            lambda: UpstreamCallback(
                client_transport, client_address, data, on_con_lost
            ),
            remote_addr=upstream_server,
        )
        try:
            await asyncio.wait_for(on_con_lost, timeout=10)
        finally:
            trans.close()

    def filter(self, dns_req_msg: Message, client_ip: str) -> bool:
        """Check if the dns message should be filtered out, this will work
        through the loaded filter logic:
        1. apply default action
        2. check domain against block list
        3. check domain against allow list

        this means that an explicit allowing will always override blocks!
        IMPORTANT, the message MUST be sanity checked (sanity_check) and parsed before calling the filter
        method. Otherwise bad things may happen... assumptions assumptions assumptions

        Parameters
        ----------
        dns_req_msg (Message): the parsed! message
        client_ip (str): the ip of the sender, this is important to select the
        right filter, as filters can be configured per ip

        Returns
        -------
        (bool): True, if the message is filtered and MUST NOT be resolved. The default
        action is to resolve to NXDOMAIN
        """
        fconf: tuple[str, str] | None = self.local_rv_lookup(client_ip)
        fltr: DNSFilter | None = None

        if (
            fconf is None
            or fconf[1] is None
            or fconf[1] == "default"
            or fconf[1] not in self.filters
        ):
            fltr = self.filters["default"]
        else:
            fltr = self.filters[fconf[1]]

        # this works only like this, because sanity_check made sure that there is
        # exactly ONE question
        domain: str = dns_req_msg.question[0].qname
        allow: bool = fltr.is_allowed(domain)

        if not allow:
            self.__msg_flag_return(dns_req_msg, 3)  # NXDOMAIN!

        return not allow

    async def filter_update(self):
        while not self.lock.acquire(blocking=False):
            await asyncio.sleep(0.5)

        try:
            logging.info("downloading all filter sources")
            for next in self.filters:
                self.filters[next].update()
            logging.info("download complete")
            DNSFilter.content_cache.clear()
        finally:
            self.lock.release()

    def build_hosts_file(self, orig: str) -> str:
        """build a new hosts file content by merging
        the local dns configuration with the existing hosts file
        content (orig). it works by replacing all entries ending
        with the "local_domain".

        Parameters
        ----------
        orig (str): the contents of the current hosts file

        Returns
        -------
        (str): a new hosts file content
        """
        hosts: str = ""

        lines: list[str] = orig.split("\n")
        for next_line in lines:
            tmp: str = next_line.strip()
            # empty line?
            if len(tmp) == 0:
                hosts += "\n"
            # comment line?
            elif tmp.startswith("#"):
                hosts += next_line + "\n"
            # everything else----
            else:
                entry: list[str] = next_line.split()  # split by whitespace
                k: int = 1  # skip the inet address

                # build the next line starting with the inet addr
                newline: list[str] = []
                newline.append(entry[0])

                while k < len(entry):
                    # filter out all lines that contain a localdomani
                    if not entry[k].endswith(self.local_domain):
                        newline.append(entry[k])
                    k += 1

                if len(newline) > 1:
                    hosts += f"{' '.join(newline)}\n"

        for next in self.known_names:
            ip, filter = self.known_names[next]
            hosts += f"{ip} {next}\n"

        return hosts

    async def filter_reload(self):
        while not self.lock.acquire(blocking=False):
            await asyncio.sleep(0.5)

        try:
            logging.info("reloading all filters")
            for next in self.filters:
                self.filters[next].load()
            logging.info("reloading done")
        finally:
            self.lock.release()

    def local_fw_lookup(self, domain: str) -> tuple[str, str] | None:
        """lookup a local domain name and retrieve the ip and filter name
        the filter name is
        Parameters
        ----------
        domain (str): the domain name to resolve

        Returns
        -------
        (None | tuple[str,str]):
        - None: if the domain was not found
        - (ip, filter_name): if the domain was found.
        """
        if domain in self.known_names:
            return self.known_names[domain]

        return None

    def local_rv_lookup(self, ip: str) -> tuple[str, str] | None:
        """lookup a local ip address and retrieve the domain and filter name

        Parameters
        ----------
        ip (str): the ip address to lookup

        Returns
        -------
        (None | tuple[str,str]):
        - None: if the ip was not found
        - (domain, filter_name): if the ip was found.
        """
        if ip in self.known_ips:
            return self.known_ips[ip]

        return None

    def sanity_check(self, dns_req_msg: Message) -> bool:
        """perform sanity checks on the request message. the following checks are
        done:
        1. has the message exact 1 question (multiple or none are not supported)
        2. check if opcode is inverse query (not supported - not sure if the rfc authors were sniffing glue)
        2. currently no further checks!

        Parameters
        ----------
        dns_req_msg (Message): the dns request to be checked

        Returns
        -------
        (bool): False if the sanity check fails!
        """
        # we currently support exactly 1 question, the RFC is not
        # very specific on how to handle multiple questions at once - especially
        # if we mix domains (think about two questions, one resolves to NXDOMAIN, the other
        # resolves to something useful). thus, simply don't resolve that!
        if len(dns_req_msg.question) > 1:
            self.__msg_flag_return(dns_req_msg, 4)  # not implemented
            # that should never be None, because the orig was parsed
            return False

        # sending a "no question" to delphi? whaddup braaaa?
        if len(dns_req_msg.question) == 0:
            self.__msg_flag_return(dns_req_msg, 1)  # format error
            # again - should never be None, orig was parsed
            return False

        # only standard queries
        if dns_req_msg.opcode != 0:
            self.__msg_flag_return(dns_req_msg, 4)  # not implemented

        return True

    def resolve(
        self,
        dns_req_pkg: bytes,
        dns_req_msg: Message,
        client_transport: DatagramTransport,
        client_addr: tuple[str, int],
    ) -> bytes | None:
        """Trigger resolution of the given request, this will be tried in the following
        order and the first success is returned!:
        1. resolve locally (forward)
        2. resolve locally (reverse/inverse)
        3. resolve remote

        Parameters
        ----------
        dns_req_pkg (bytes): the original request as bytes
        dns_req_msg (Message): the parsed and sanity_checked (!!!) dns request message. the sainity
        check is important, because the resolution assumes the message contains only 1 question
        client_transport (DatagramTransport): the socket transport of the connected client. this must be used for
        sending back the reply from the upstream resolver (if remote resolution is triggered)
        client_addr (tuple[str,int]): ip4 address and port as (ip,port)

        Returns
        -------
        (bytes): if the message could be locally resolved
        (None): if the message has been submitted to be remote resolved, this will happen asynchronous (task)
        """

        # reuse the request as response
        dns_response: Message | None = dns_req_msg

        # try local (authoratative) resolution
        dns_response = self.__resolve_local_fw(dns_req_msg)
        if dns_response is not None:
            return dns_response.build()

        dns_response = self.__resolve_local_rv(dns_req_msg)
        if dns_response is not None:
            return dns_response.build()

        asyncio.get_event_loop().create_task(
            self.__resolve_remote(dns_req_pkg, client_transport, client_addr)
        )
        return None


class ServerCallback(asyncio.DatagramProtocol):
    def __init__(self, dns: DNS) -> None:
        """create a callback for client connections to the DNS service

        Parmeters
        ---------
        dns (DNS): DNS class containing config data, filtering + local resolution functions
        """
        super().__init__()
        self.dns = dns

    def connection_made(self, transport: DatagramTransport) -> None:
        """called when a client connect to the DNS service via UDP"""
        self.client_transport = transport

    def connection_lost(self, exc: Exception | None) -> None:
        pass

    def datagram_received(self, data: bytes, addr: tuple[str | Any, int]) -> None:
        logging.debug(f"con: ip={addr[0]}, port={addr[1]}")

        # resolve the requester (if possible)
        tmp: tuple[str, str] | None = self.dns.local_rv_lookup(addr[0])
        client_name: str = addr[0]
        filter_name: str = "default"

        if tmp is not None:
            client_name = tmp[0]
            filter_name = tmp[1]

        # FLOW:
        #  1. RECEIVE REQUEST
        #  2. PARSE DNS REQUEST INTO MESSAGE
        #  3. SANITY CHECKING
        #  3. FILTER DOMAIN
        #  4. RESOLVE REQUEST
        #  5. SEND REPLY
        #

        # create new DNS message object and parse incoming packet
        dns_req_msg: Message = Message()
        dns_req_msg.parse(data, 0)

        # if sanity check fails, or the message should be filtered,
        # them orig request header will be modified, we can send that back
        sane: bool = self.dns.sanity_check(dns_req_msg)
        if not sane:
            logging.info(
                f"[{client_name}][{filter_name}][invalid query] {dns_req_msg.question[0].qname}"
            )

        filter: bool = True if not sane else self.dns.filter(dns_req_msg, addr[0])
        if filter:
            logging.info(
                f"[{client_name}][{filter_name}][block] {dns_req_msg.question[0].qname}"
            )

        if not sane or filter:
            # sice the req was just parsed, this should never be None!
            self.client_transport.sendto(
                dns_req_msg.build_from_orig_with_header(), addr
            )
        else:
            logging.info(
                f"[{client_name}][{filter_name}][query] {dns_req_msg.question[0].qname}"
            )
            dns_resp_bytes: bytes | None = self.dns.resolve(
                data, dns_req_msg, self.client_transport, addr
            )
            if dns_resp_bytes is not None:
                self.client_transport.sendto(dns_resp_bytes, addr)

    # not implemented
    def error_received(self, exc: Exception) -> None:
        pass


class UpstreamCallback(asyncio.DatagramProtocol):
    """Simple callback to send DNS requests that cannot be
    resolved locally to an upstream DNS server (e.g. Cloudflare 1.1.1.1)
    """

    def __init__(
        self,
        requester_transport: DatagramTransport,
        requester_addr: tuple[str | Any, int],
        orig_request: bytes,
        on_con_lost: asyncio.Future,
    ) -> None:
        """constructor for the upstream connection callback. these callbacks are fired
        for the upstream server connection

        Parameters
        ----------
        orig_request (bytes): the original DNS query (request) that was send by a local client and could
        not be resolved locally

        requester_transport (DatagramTransport): socket/connection to the local client to send back the
        upstream response

        requester_address (Tuple[str,int]): address of the local client to send the upstream response to
        """

        self.orig_request = orig_request
        self.requester_transport = requester_transport
        self.requester_address = requester_addr
        self.on_connection_lost = on_con_lost

    def connection_made(self, transport: DatagramTransport) -> None:
        """this event is called when the UDP socket for connecting
        to the upstream server is ready. we simply call sendto, to forward
        the original request to the upstream server.
        """
        self.upstream_transport = transport
        self.upstream_transport.sendto(self.orig_request)

    def connection_lost(self, exc: Exception | None) -> None:
        self.on_connection_lost.set_result(True)

    def datagram_received(self, data: bytes, addr: tuple[str | Any, int]) -> None:
        """this event is called when the upstream dns sends a response back,
        this response needs to be forwarded to the original requester (connecton to
        local DNS service)
        """

        m = Message()
        m.parse(data, 0)

        self.requester_transport.sendto(data, self.requester_address)
        self.upstream_transport.close()


def init_logging():
    """initialize the logger"""
    fmtstr: str = "[%(asctime)s][%(levelname)s] %(message)s"
    datefmt: str = "%Y-%m-%d %H:%M:%S %Z"
    logging.basicConfig(level=logging.INFO, format=fmtstr, datefmt=datefmt)


def update_hosts(dns: DNS):
    hosts_path: str = "/etc/hosts"
    logging.info(f"updating hosts file: {hosts_path}")
    f = open(hosts_path, "r")
    orig: str = f.read()
    f.close()

    new_hosts: str = dns.build_hosts_file(orig)
    f = open(hosts_path, "w")
    f.write(new_hosts)
    f.close()


def read_commands(dns: DNS):
    """very quick and dirty (and certainly not thread/process proof)
    IPC to control the service behaviour. this can be used to trigger
    reloads of the filter lists etc.
    """
    if os.path.exists(dns.control_file):
        f = open(dns.control_file, "r+")
        cmd: str = f.readline()
        f.truncate(0)
        f.close()
        if len(cmd) > 0:
            cmd = cmd.strip()
            logging.info(f"received command: {cmd}")
            if cmd == "update":
                asyncio.run(dns.filter_update())
            elif cmd == "reload":
                asyncio.run(dns.filter_reload())
            elif cmd == "stop":
                dns.running = False
            elif cmd == "fstat":
                for name in dns.filters:
                    next: DNSFilter = dns.filters[name]
                    logging.info(f"{name} --> rx")
                    if dns.filters[name].block_rx is not None:
                        for p in dns.filters[name].block_rx:
                            logging.info(p)
            else:
                logging.info(f"unknown command: {cmd}")
    else:
        # if the control file does not exist - touch()
        f = open(dns.control_file, "w")
        f.close()


async def main():
    # the config file!
    config: str = "config.json"

    # start logging
    init_logging()
    logging.info("loading configuration")

    # load and parse config, initialize dns+filters
    logging.info(f"file: {config}")
    dns: DNS = DNS(config)

    # for privileged ports, this service needs to be started as root!
    # start network listener
    logging.info("starting network listener")
    loop: AbstractEventLoop = asyncio.get_event_loop()
    trans, proto = await loop.create_datagram_endpoint(
        lambda: ServerCallback(dns), local_addr=(dns.host, dns.port)
    )
    logging.info("ready and listening!")

    # if started as root, make sure to drop privileges!
    if os.getuid() == 0:
        update_hosts(dns)

        svc_uid = pwd.getpwnam(dns.daemon_user).pw_uid
        svc_gid = grp.getgrnam(dns.daemon_group).gr_gid
        os.setgroups([])
        os.setgid(svc_gid)
        os.setuid(svc_uid)
        os.umask(0o077)

    while dns.running:
        await asyncio.sleep(1)
        # thats just a fancy way to call this in an outside thread to
        # avoid blocking the resolution
        loop.run_in_executor(None, lambda: read_commands(dns))

    logging.info("stopping dns service")
    loop.stop()


if __name__ == "__main__":
    loop = asyncio.new_event_loop()
    loop.create_task(main())
    try:
        loop.run_forever()
    finally:
        loop.stop()
