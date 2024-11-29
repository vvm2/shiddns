# SHIDDNS - Overview
shiddns is a simple implementation of a DNS resolver with half-baked
local DNS capabilities (thus the name). i implemented this as an
educational project and experimented with it to resolve names in my
home network - only single A RECORDS. the service is not fully conform
to RFC 1034 / RFC 1035, does not support the various extensions like
DNSSEC. while testing it, it worked quite a while resolving names on
my local network without creating any notable issues.

so again: this project is implemented for educational purpose to play
around with DNS and understand "how things work" a bit more in depth.

i don't intend to actively maintain this project. however, i want to
share it with you so you can copy/learn or simply play around.

> [!CAUTION]
> THIS IS NOT PRODUCTION READY SOFTWARE
>
> if you are thinking about it, please simply don't! i did not write a
> single test case nor did i put much effort into preventing nasty
> things in terms of input validation, thread/process safety.
>
> if you decide to ignore this warning, you may suffer damage

> [!CAUTION]
> PRIVACY ISSUES: this dns logs (to stdout) all dns queries
> together with ip addresses of the client. i am not a lawyer but this may
> be even illegal in some countries - especially if you are running this on your wlan
> and provide access to guests.

## how does the program work?
very easy. follow the `main()` method in `dns.py`

**step 1**
the program starts by loading the configuration. unless you change the
code in `dns.py` (`main()`), the program expects a file named `config.json` to be present
in the same directory as the source code.

**step 2**
we create a udp socket listening for incoming datagrams (udp packets)
with a callback to be called whenever a new packet arrives.

**step 3**
if the program was called as root, drop all privileges to the service user/group in `config.json`

**step 4**
loop forever while periodically reading the `control` file to trigger actions like reloading
the blocking lists etc...

**upon arrival of a datagram**
1. PARSE DNS REQUEST INTO MESSAGE: raw udp datagram is parsed
2. SANITY CHECKING: check for unsupported stuff (e.g. more than one question in the dns request)
3. FILTER DOMAIN: compare the requested dns name against the filter lists -> prevent name resoultion if filtered (NXDOMAIN)
4. RESOLVE REQUEST: first try to resolve the request locally, if not possilbe simply forward the original request to the upstream host
5. SEND REPLY: send the reply back

thats it.

## what's missing
there are a couple of things that i did not implement but might do out of curiosity:
1. caching (currently queries are not cached which is not optimal)
2. compression (local replies are not compressed)
3. truncation (i currently do not truncate packets if they become too large - as local queries are usually not that big)
4. logging (i will probably not do this, but currently only logging to stdout is performed)

## running the software
i have not tested the code on windows and unfortunately will not be able to,
as i dont own a copy of it. the code will likely run fine on most Linux
and BSD (i tested OpenBSD) flavors.

once you downloaded the code you need to adjust your config.json. i will refer
to the different json config elements in forms of a path - so /service/user
would refer to:
```json
  "service": {
    "user": "_shiddns",
    ...
  }
```

| setting        | value description |
| -------------- | ----------------- |
| /service/user  | user name to run the service with, in case you start the program as root (uid 0). the user must exist. |
| /service/group | same as user only with group name. |
| /service/control | file name (can be a path) to use for IPC with the service. WARNING this is absolutely not thread/process safe. this can be used to start or stop the service or trigger a reload of the rules. |
| /network/host | ip address to run the service on |
| /network/port | the udp port (no tcp implemented) to start the service on (if you use a lower/privileged port, you need to start the service as root!) |
| /network/upstream_host | the ip address of the upstream dns to resolve non-local queries |
| /network/upstream_port | the udp port of the upstream dns to resolve non-local queries |
| /storage/filter | path to directory that will be used to save the consolidated blocking lists (temp storage) |
| /storage/logs | not implemented |
| /localdns/domain | domain name that is considered local, all requests ending with this domain are attempted to be resolved locally. if you put "com" here, you will try to resolve any .com domain locally |
| /localdns/entries/ip | the ip of a local system to be resolved by this service |
| /localdns/entries/name | the fqdn (must end in domain) of the system |
| /localdns/entries/filter | name of the filter to apply for this host |
| /filters/&lt;filtername&gt;/default_allow | true if queries should by default not be blocked, this is the starting point before evaluating all the block and allow lists |
| /filters/&lt;filtername&gt;/block_src | remote locations of hosts like blocking files (hosts: prefix) or regular expression files (rx: prefix) |
| /filters/&lt;filtername&gt;/allow_src | remote locations of hosts like allow files (hosts: prefix) or regular expression files (rx: prefix) |

*Note:* if you name a filter xyz, the following files may be created in the directory denoted in the
`/storage/filter` configuration:
1. block_xyz
2. allow_xyz
3. block_xyz_rx
4. allow_xyz_rx

These files will be auto generated and *OVERWRITTEN*.

## Example
Edit the `config.json` to look like this:
```json
{
  "service": {
    "user": "www",
    "group": "www",
    "control": "/tmp/control",
  },
  "network": {
    "host": "127.0.0.1",
    "port": 53535,
    "upstream_host": "1.1.1.1",
    "upstream_port": 53
  },
  "storage": {
    "filter": "/tmp",
    "logs": "/tmp"
  },
  "localdns": {
    "domain": "mein.zuhause",
    "entries": [
      {
        "ip": "10.0.0.1",
        "name": "router.mein.zuhause",
        "filter": "services"
      },
      {
        "ip": "10.0.0.200",
        "name": "pc-kids.mein.zuhause",
        "filter": "kids"
      }
    ]
  },
  "filters": {
    "default": {
      "default_allow": "true",
      "block_src": [
        "hosts:https://raw.githubusercontent.com/StevenBlack/hosts/master/hosts",
        "rx:file:///tmp/orig_blocks"
      ],
      "allow_src": []
    },
    "services": {
      "default_allow": "false",
      "block_src": [],
      "allow_src": []
    },
    "kids": {
      "default_allow": "true",
      "block_src": ["hosts:https://raw.githubusercontent.com/StevenBlack/hosts/master/alternates/fakenews-gambling-porn-social/hosts"],
      "allow_src": []
    }
  }
}
```
Then start the service as non-root! (i assume the source code lies under ~/shiddns)
```bash
me$ cd ~/shiddns
me$ python3 dns.py
[2024-12-31 10:00:25 CET][    INFO] loading configuration
[2024-12-31 10:00:25 CET][   DEBUG] file: config.json
[2024-12-31 10:00:26 CET][    INFO] starting network listener
[2024-12-31 10:00:26 CET][    INFO] ready and listening!
```

now open another terminal - and lets do some testing.
```bash
me$ dig @127.0.0.1 -p 53535 ccc.de

'; <<>> DiG 9.20.3 <<>> @127.0.0.1 -p 53535 ccc.de
; (1 server found)
;; global options: +cmd
;; Got answer:
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 35990
;; flags: qr rd ra; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 1

;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 1232
;; QUESTION SECTION:
;ccc.de.				IN	A

;; ANSWER SECTION:
ccc.de.			5225	IN	A	195.54.164.39

;; Query time: 43 msec
;; SERVER: 127.0.0.1#53535(127.0.0.1) (UDP)
;; WHEN: Tue Dec 31 10:01:10 CET 2024
;; MSG SIZE  rcvd: 51'

me$ dig @127.0.0.1 -p 53535 router.mein.zuhause

'; <<>> DiG 9.20.3 <<>> @127.0.0.1 -p 53535 router.mein.zuhause
; (1 server found)
;; global options: +cmd
;; Got answer:
;; ->>HEADER<<- opcode: QUERY, status: NOERROR, id: 50172
;; flags: qr aa rd ra ad; QUERY: 1, ANSWER: 1, AUTHORITY: 0, ADDITIONAL: 0

;; QUESTION SECTION:
;router.mein.zuhause.		IN	A

;; ANSWER SECTION:
router.mein.zuhause.	0	IN	A	10.0.0.1

;; Query time: 0 msec
;; SERVER: 127.0.0.1#53535(127.0.0.1) (UDP)
;; Tue Dec 31 10:01:12 CET 2024
;; MSG SIZE  rcvd: 72'
```

so resolution works. now lets make sure we download our blocking lists.

```bash
me$ echo "refresh" >> /tmp/control
```

after a couple of seconds, the server should respond with a
`received command: refresh`

now the running service needs to reload the new lists
```bash
me$ echo "reload" >> /tmp/control
```
the command should be acquitted with:
```
received command: reload
reloading all filters
reloading done
```

now try to resolve one of the blacklisted domains - e.g.
```bash
me$ dig @127.0.0.1 -p 53535 www.2no.co

' <<>> DiG 9.20.3 <<>> @127.0.0.1 -p 53535 www.2no.co
; (1 server found)
;; global options: +cmd
;; Got answer:
;; ->>HEADER<<- opcode: QUERY, status: NXDOMAIN, id: 46098
;; flags: qr rd ra ad; QUERY: 1, ANSWER: 0, AUTHORITY: 0, ADDITIONAL: 1

;; OPT PSEUDOSECTION:
; EDNS: version: 0, flags:; udp: 1232
; COOKIE: 33520598d276e204 (echoed)
;; QUESTION SECTION:
;www.2no.co.			IN	A
...'
```

observe the line `;; ->>HEADER<<- opcode: QUERY, status: NXDOMAIN, id: 46098`. the
status NXDOMAIN indicates that the domain was not found/resolved.

that's about it, have fun!

## troubleshooting

i developed the software with python 3.12.7. from 3.13 regular exceptions
raise a "PatternError" if compilation fails. there is still an alias named "error",
but who knows for how long. if you see errors in that direction, you need
to change the import in dns.py from:
```python
...
from re import Pattern, error
...
```
to
```python
from re import Pattern, PatternError
```
