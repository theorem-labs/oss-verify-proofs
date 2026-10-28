"""URLs as a browser reads them, and the links a reader can follow in a file.

`parse` follows the WHATWG URL standard (https://url.spec.whatwg.org/) as far as a link check needs: it resolves a
reference against a base, resolves dot segments (also %2e) as a browser does before it sends the path, and folds the
host as a browser does (percent-decoding, UTS #46 IDNA mapping by the idna package, the IPv4 forms a browser accepts,
IPv6 literals).  The path it gives a check is that path percent-decoded, with dot segments removed again (RFC 3986,
section 5.2.4) and repeated slashes collapsed: what a server that decodes %2F opens.  It returns None where a browser
opens nothing, and raises Unreadable where it cannot be sure what a browser opens, so that a caller can refuse what it
cannot judge.

`links` finds what a reader can follow: in any text, an absolute URL; in Markdown, also what GitHub renders as a link:
a bare URL to the end GitHub links it, a www. link, a link destination or reference definition, a <scheme:...>
autolink and an HTML href, src, srcset, cite or longdesc, with character references and backslash escapes decoded as
GitHub decodes them, and a URL in a line's text as GitHub shows it (unescape_markdown).
"""
import bisect
import functools
import html
import ipaddress
import re
import urllib.parse
from typing import NamedTuple

SPECIAL = {"http": 80, "https": 443, "ws": 80, "wss": 443, "ftp": 21, "file": None}
# The file names GitHub renders as Markdown, in any case (github/markup's Markdown pattern), and this repository's
# Markdown templates.
MARKDOWN = re.compile(r"(?i)\.(?:md|mkdn?|mdwn|mdown|markdown|mdx|litcoffee|md\.tmpl)\Z")
_FORBIDDEN_HOST = re.compile(r"[\x00-\x20#%/:<>?@\[\\\]^|\x7f]")
_C0_AND_SPACE = "".join(map(chr, range(0x21)))
# a character reference, as html.unescape finds one
CHARREF = re.compile(r"&(#[0-9]+;?|#[xX][0-9a-fA-F]+;?|[^\t\n\f <&#;]{1,32};?)")


def reference_digits(ref):
    """(the digits of a numeric reference, ref a CHARREF match's group 1, without their leading zeros, and their base),
    or None for a named one.  More than 7 digits is more than any code point."""
    if ref[0] != "#":
        return None
    hexa = ref[1] in "xX"
    return ref[2 if hexa else 1:].rstrip(";").lstrip("0") or "0", 16 if hexa else 10


def _reference(match):
    numeric = reference_digits(match.group(1))
    if numeric is None:
        return html.unescape(match.group())
    digits, base = numeric
    if len(digits) > 7:
        return match.group()
    # html.unescape reads every digit with int(), leading zeros too, and int() refuses a run of over 4,300
    return html.unescape("&#%s%s;" % ("x" if base == 16 else "", digits))


def unescape(text):
    """html.unescape(text), but a numeric reference is read without its leading zeros, and one too long for any code
    point (reference_digits) stays as it is, so no text makes it raise."""
    return CHARREF.sub(_reference, text) if "&" in text else text


class Unreadable(ValueError):
    """A URL whose host this parser cannot fold for sure the way a browser does."""


class Url(NamedTuple):
    scheme: str
    host: str          # a special scheme's: lower case and ASCII, no trailing dot; an IPv4 address dotted, an IPv6
                       # one in brackets.  Another scheme's: percent-decoded, as written
    port: int | None   # None for the scheme's default port
    path: str          # sent, percent-decoded, dot segments removed, repeated slashes collapsed; no query or fragment
    sent: str          # the path a browser sends: dot segments resolved, still percent-encoded

    def __str__(self):
        return "%s://%s%s%s" % (self.scheme, self.host, "" if self.port is None else ":%d" % self.port, self.path)


@functools.lru_cache(maxsize=1 << 16)
def parse(ref, base=None):
    """The Url a browser opens for ref, resolved against base (a Url); None if it opens nothing."""
    s = re.sub(r"[\t\n\r]", "", ref.strip(_C0_AND_SPACE))
    m = re.match(r"[A-Za-z][A-Za-z0-9+.-]*:", s)
    if m:
        scheme, rest = m.group()[:-1].lower(), s[m.end():]
        if scheme == "file":
            return Url("file", "", None, *_path(re.sub(r"^[/\\]{2}[^/\\?#]*", "", rest), True))
        if scheme not in SPECIAL:
            return _authority(scheme, rest[2:], False) if rest.startswith("//") else None
        if base is not None and base.scheme == scheme and not re.match(r"[/\\]{2}", rest):
            return _relative(rest, base)
        return _authority(scheme, rest.lstrip("/\\"), True)
    return None if base is None else _relative(s, base)


def _relative(s, base):
    special = base.scheme in SPECIAL
    slashes = "/\\" if special else "/"
    if len(s) > 1 and s[0] in slashes and s[1] in slashes:
        return _authority(base.scheme, s.lstrip(slashes), special)
    if s[:1] in ("", "?", "#"):
        return base
    sent = s if s[0] in slashes else base.sent[:base.sent.rfind("/") + 1] + s
    path, sent = _path(sent, special)
    return base._replace(path=path, sent=sent)


def _authority(scheme, rest, special):
    auth = re.match(r"[^/\\?#]*" if special else r"[^/?#]*", rest).group()
    hp = re.fullmatch(r"(\[[^\]]*\]|[^:\[\]]*)(?::([0-9]*))?", auth.rpartition("@")[2])
    if hp is None:
        return None
    host = _host(hp.group(1), special)
    port = int(hp.group(2)) if hp.group(2) else None
    if host is None or (special and not host) or (port is not None and port > 65535):
        return None
    return Url(scheme, host, None if port == SPECIAL.get(scheme) else port, *_path(rest[len(auth):], special))


def _host(raw, special):
    if raw.startswith("["):
        if not raw.endswith("]") or "%" in raw:
            return None
        try:
            return "[%s]" % ipaddress.IPv6Address(raw[1:-1]).compressed
        except ValueError:
            return None
    if not special:
        return urllib.parse.unquote(raw)
    try:
        decoded = urllib.parse.unquote(raw, errors="strict")
    except UnicodeDecodeError:
        return None
    domain = _domain_to_ascii(decoded)
    if domain is None:
        return None
    if _ends_in_a_number(domain):
        return _ipv4(domain)
    return domain.rstrip(".") or None


def _domain_to_ascii(domain):
    """UTS #46 ToASCII, as a browser applies it to a host: the domain mapped (lower case, compatibility forms, the
    code points IDNA ignores dropped; ß and the other deviations kept), a Punycode (xn--) label checked, and a
    non-ASCII label encoded.  None if the mapped domain holds a code point no host may (a browser opens nothing);
    Unreadable for a label IDNA refuses.  The idna package's label checks are IDNA 2008's, stricter than a browser's
    in places, so a host refused here may be one a browser opens: it is reported, never guessed."""
    # Imported here: `oft check` in the pinned runner image, whose Python has PyYAML alone, imports lint but maps no
    # host.
    import idna
    try:
        mapped = idna.uts46_remap(domain, std3_rules=False)
        if _FORBIDDEN_HOST.search(mapped):
            return None
        out = []
        for label in mapped.split("."):
            if not label.isascii():
                label = idna.alabel(label).decode("ascii")
            elif label.startswith("xn--"):
                idna.ulabel(label)
            out.append(label)
    except UnicodeError as e:   # idna.IDNAError is a UnicodeError
        raise Unreadable("a host IDNA does not map for sure: %r (%s)" % (domain, e)) from None
    return ".".join(out)


def _ends_in_a_number(domain):
    parts = domain.split(".")
    if parts[-1] == "":
        if len(parts) == 1:
            return False
        parts.pop()
    return bool(re.fullmatch(r"[0-9]+|0[xX][0-9A-Fa-f]*", parts[-1]))


def _ipv4(domain):
    """WHATWG's IPv4 parser: up to four parts, each decimal, octal (a leading 0) or hexadecimal (0x), the last one
    filling the remaining bytes."""
    parts = domain.split(".")
    if parts[-1] == "" and len(parts) > 1:
        parts.pop()
    if len(parts) > 4:
        return None
    numbers = []
    for part in parts:
        if part[:2] in ("0x", "0X"):
            digits, base, pattern = part[2:], 16, r"[0-9A-Fa-f]*"
        elif len(part) > 1 and part[0] == "0":
            digits, base, pattern = part[1:], 8, r"[0-7]+"
        else:
            digits, base, pattern = part, 10, r"[0-9]+"
        if not re.fullmatch(pattern, digits):
            return None
        numbers.append(int(digits, base) if digits else 0)
    if any(n > 255 for n in numbers[:-1]) or numbers[-1] >= 256 ** (5 - len(numbers)):
        return None
    return str(ipaddress.IPv4Address(numbers[-1] + sum(n << 8 * (3 - i) for i, n in enumerate(numbers[:-1]))))


def _path(raw, special):
    """(path, sent) for a path as written."""
    raw = re.split(r"[?#]", raw, maxsplit=1)[0]
    if special:
        raw = raw.replace("\\", "/")
    sent = _resolve_dot_segments(raw if raw.startswith("/") else "/" + raw)
    return re.sub(r"/{2,}", "/", _remove_dot_segments(urllib.parse.unquote(sent))), sent


def _resolve_dot_segments(raw):
    """WHATWG's path parser on a path that starts with /: a . or .. segment, also written with %2e, is resolved; the
    rest stay percent-encoded."""
    out = []
    segments = raw[1:].split("/")
    for i, seg in enumerate(segments):
        last = i == len(segments) - 1
        dots = seg.lower().replace("%2e", ".")
        if dots == "..":
            if out:
                out.pop()
            if last:
                out.append("")
        elif dots == ".":
            if last:
                out.append("")
        else:
            out.append(seg)
    return "/" + "/".join(out)


def _remove_dot_segments(path):
    """RFC 3986, section 5.2.4."""
    out = ""
    while path:
        if path.startswith(("../", "./")):
            path = path[path.index("/") + 1:]
        elif path.startswith("/./") or path == "/.":
            path = "/" + path[3:]
        elif path.startswith("/../") or path == "/..":
            path = "/" + path[4:]
            out = out[:out.rfind("/")] if "/" in out else ""
        elif path in (".", ".."):
            path = ""
        else:
            seg = re.match(r"/?[^/]*", path).group()
            out, path = out + seg, path[len(seg):]
    return out


# ------------------------------------------------------------------- links

class Link(NamedTuple):
    line: int
    text: str     # as written
    ref: str      # what a browser parses
    kind: str     # "url": an absolute URL in the text; "link": a Markdown or HTML link, resolved against the page that
                  # shows it; "reading": another reading of the same text (GitHub's extent of a bare URL, or the text
                  # with character references decoded, or as GitHub shows it: unescape_markdown)


# an absolute URL, to the first character that usually ends one in text or code; a host or path after the scheme's
# // (punctuation that ends a sentence does not count), and the scheme starting after anything but an ASCII letter
# (GitHub links a URL right after a digit, a _ or a non-ASCII letter such as ſ, which (?i) alone would read as an s).
# A scheme has at most 32 characters (CommonMark's limit), keeping searches over untrusted lines linear.
URL = re.compile(r"(?i)(?a:(?<![a-z])[a-z][a-z0-9+.-]{0,31})://(?:[^\s<>()\[\]\"'`|/@]*@)?"
                 r"(?:\[[^\]\s/]*\]|[.,;:!?]*[^\s<>()\[\]\"'`|.,;:!?])[^\s<>()\[\]\"'`|]*")
# what GitHub links in Markdown text: a URL from the ASCII letters before :// (a domain character after it) to the
# next white space or <, or a www. link
_GFM = re.compile(r"(?i)(?a:(?<![a-z])[a-z]+)://[\w.-][^\s<]*|(?:^|(?<=[\s*_~(]))www\.[^\s<]*")
_ANGLE = re.compile(r"<([A-Za-z][A-Za-z0-9+.-]{1,31}:[^\s<>]*)>")
# a reference definition, also inside a block quote or a list item
_REFERENCE = re.compile(r"(?m)^(?:[ \t]*(?:>|[-+*][ \t]|[0-9]{1,9}[.)][ \t]))*[ \t]*\[(?:[^\\\[\]]|\\.)+\]:")
# an HTML tag, whose quoted attribute values may hold < and >; an attribute after white space or a / (GitHub's HTML
# reads <a/href=...> as a link inside an HTML block)
_TAG = re.compile(r"<[A-Za-z](?:[^<>\"']|\"[^\"]*\"|'[^']*')*>")
_ATTRIBUTE = re.compile(r"(?i)\"[^\"]*\"|'[^']*'|[\s/](href|src|srcset|cite|longdesc)\s*=\s*"
                        r"(?:\"([^\"]*)\"|'([^']*)'|([^\s\"'=<>`]+))")
_BACKSLASH_ESCAPE = re.compile(r"\\([!-/:-@\[-`{-~])")
_HTML_COMMENT = re.compile(r"<!--.*?-->")
_LINE_GAP = re.compile(r"[ \t]*(?:\r?\n[ \t]*)?")
_HTML_WHITESPACE = " \t\n\f\r"
MAX_LINK_DESTINATION_PARENS = 32


def _srcset(value):
    """Every URL candidate in a decoded srcset attribute (HTML's parse a srcset attribute algorithm)."""
    i, n = 0, len(value)
    while i < n:
        while i < n and value[i] in _HTML_WHITESPACE + ",":
            i += 1
        start = i
        while i < n and value[i] not in _HTML_WHITESPACE:
            i += 1
        url = value[start:i]
        if not url:
            continue
        if url.endswith(","):
            url = url.rstrip(",")
            if url:
                yield url
            continue
        yield url
        parens = 0
        while i < n:
            c = value[i]
            if c == "(":
                parens += 1
            elif c == ")" and parens:
                parens -= 1
            elif c == "," and not parens:
                i += 1
                break
            i += 1


def unescape_markdown(line):
    """A line of Markdown as GitHub shows its text: backslash escapes and the HTML comments that end on the line
    removed, so that `a\\-b` and `a<!-- -->-b` read as `a-b`."""
    return _BACKSLASH_ESCAPE.sub(r"\1", _HTML_COMMENT.sub("", line))


def links(text, markdown):
    """Every Link in text; in Markdown (markdown=True), also what GitHub renders as one."""
    for no, line in enumerate(text.split("\n"), 1):
        for m in URL.finditer(line):
            yield Link(no, m.group(), m.group().rstrip(".,;:)]}'\""), "url")
        if not markdown:
            continue
        decoded = unescape(line)
        shown = unescape_markdown(line)
        for variant in dict.fromkeys((decoded, shown)):
            if variant != line:
                for m in URL.finditer(variant):
                    yield Link(no, m.group(), m.group().rstrip(".,;:)]}'\""), "reading")
        for variant in dict.fromkeys((line, decoded, shown)):
            for m in _GFM.finditer(variant):
                url = _gfm_trim(m.group())
                yield Link(no, m.group(), "http://" + url if url[:4].lower() == "www." else url, "reading")
    if not markdown:
        return
    starts = [0] + [m.end() for m in re.finditer("\n", text)]
    line_of = lambda pos: bisect.bisect_right(starts, pos)
    for m in [*re.finditer(r"\]\(", text), *_REFERENCE.finditer(text)]:
        dest = _destination(text, m.end())
        if dest is not None:
            yield Link(line_of(dest[1]), dest[0], unescape(_BACKSLASH_ESCAPE.sub(r"\1", dest[0])), "link")
    for m in _ANGLE.finditer(text):
        yield Link(line_of(m.start(1)), m.group(1), m.group(1), "link")
    for tag in _TAG.finditer(text):
        for m in _ATTRIBUTE.finditer(tag.group()):
            attribute, *values = m.groups()
            if attribute is None:
                continue
            value = next(v for v in values if v is not None)
            if attribute.lower() == "srcset":
                for ref in _srcset(unescape(value)):
                    yield Link(line_of(tag.start() + m.start(1)), ref, ref, "link")
            else:
                yield Link(line_of(tag.start() + m.start(1)), value, unescape(value), "link")


def _gfm_trim(url):
    """A URL without trailing punctuation, quotes or unbalanced closing parentheses and brackets."""
    opens_paren, closes_paren = url.count("("), url.count(")")
    opens_bracket, closes_bracket = url.count("["), url.count("]")
    end = len(url)
    while end:
        c = url[end - 1]
        if c in "?!.,:;*_~'\"":
            end -= 1
        elif c == ")" and closes_paren > opens_paren:
            closes_paren -= 1
            end -= 1
        elif c == "]" and closes_bracket > opens_bracket:
            closes_bracket -= 1
            end -= 1
        else:
            break
    return url[:end]


def _destination(text, i):
    """The link destination after text[:i] (CommonMark): <...>, or a run with balanced parentheses; and its start."""
    j = _LINE_GAP.match(text, i).end()
    if text.startswith("<", j):
        k = j + 1
        while k < len(text) and text[k] not in "<>\n":
            k += 2 if text[k] == "\\" else 1
        return (text[j + 1:k], j + 1) if k < len(text) and text[k] == ">" else None
    k, depth = j, 0
    while k < len(text):
        c = text[k]
        if c == "\\" and k + 1 < len(text):
            k += 2
            continue
        if c <= " " or c == "\x7f" or (c == ")" and depth == 0):
            break
        if c == "(":
            depth += 1
            if depth > MAX_LINK_DESTINATION_PARENS:
                return None
        elif c == ")":
            depth -= 1
        k += 1
    return (text[j:k], j) if k > j else None
