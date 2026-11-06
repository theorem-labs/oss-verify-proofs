#!/usr/bin/env python3
"""resolve_keys.py: carry the `sym` keys of a program tree to one image, and name what each lands on.

Input: a key-map file (.v) that defines an exact list `Definition E : list (Z * Z) := [KV k v; ...].`
or `... := (k, v) :: E0.`, and an interval list `Definition I : list (Z * Z * Z) := [KV3 lo hi (d); ...].`;
the names of the two lists; the image's unstripped twin (ELF with .symtab) and the image itself; the
function's key; and NAME=KEY for each other parameter. A key goes to its address as IInst.v's tsym
does: the first exact row with that key, else k + d for the first interval row with lo <= k < hi,
else k itself.

Output (stdout): one row per key: parameter, key, address, the twin's symbol holding the address
(name+offset, size), and for an address in .got the 8-byte value it holds and that value's symbol.
Then whether the function's bytes (address, symbol size) are equal in the twin and in the image, and
the --start/--end/--target arguments of ptree_emit.py. Exit 2 on a malformed input or a key whose
address no symbol holds. Dependencies: Python 3 standard library and pyelftools.
"""
import argparse
import re
import sys

from elftools.elf.elffile import ELFFile

NUM = r"(-?(?:0x[0-9a-fA-F]+|[0-9]+))"


def strip_comments(t):
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and t.startswith("*)", i):
            depth, i = depth - 1, i + 2
        else:
            if not depth:
                out.append(t[i])
            i += 1
    return "".join(out)


def definition(text, name):
    m = re.search(r"Definition\s+" + re.escape(name) + r"\s*:[^:]*?:=(.*?)\.\s*(?:\n|$)", text, re.S)
    if not m:
        sys.exit(f"resolve_keys: no Definition {name}")
    return m.group(1)


def exact_rows(text, name):
    body = definition(text, name).strip()
    m = re.fullmatch(r"\(\s*" + NUM + r"\s*,\s*" + NUM + r"\s*\)\s*::\s*(\w+)", body)
    if m:
        return [(int(m.group(1), 0), int(m.group(2), 0))] + exact_rows(text, m.group(3))
    return [(int(a, 0), int(b, 0)) for a, b in re.findall(r"KV\s+" + NUM + r"\s+" + NUM + r"\s*[;\]]", body)]


def iv_rows(text, name):
    body = definition(text, name)
    return [(int(a, 0), int(b, 0), int(c, 0))
            for a, b, c in re.findall(r"KV3\s+" + NUM + r"\s+" + NUM + r"\s+\(\s*" + NUM + r"\s*\)", body)]


def tsym(ex, iv, k):
    for a, v in ex:
        if a == k:
            return v
    for lo, hi, d in iv:
        if lo <= k < hi:
            return k + d
    return k


def load(path):
    f = open(path, "rb")
    return f, ELFFile(f)


def vread(f, elf, addr, n):
    for seg in elf.iter_segments():
        h = seg.header
        if h["p_type"] == "PT_LOAD" and h["p_vaddr"] <= addr and addr + n <= h["p_vaddr"] + h["p_filesz"]:
            f.seek(h["p_offset"] + addr - h["p_vaddr"])
            return f.read(n)
    return None


def symbols(elf):
    st = elf.get_section_by_name(".symtab")
    if st is None:
        sys.exit("resolve_keys: the twin has no .symtab")
    out = []
    for s in st.iter_symbols():
        if s.name and s["st_info"]["type"] in ("STT_FUNC", "STT_OBJECT") and s["st_shndx"] != "SHN_UNDEF":
            out.append((s["st_value"], s["st_size"], s.name, s["st_info"]["bind"]))
    # a global name first, then a weak one, then a local one, for one address
    rank = {"STB_GLOBAL": 0, "STB_WEAK": 1, "STB_LOCAL": 2}
    out.sort(key=lambda r: (r[0], rank.get(r[3], 3), r[2]))
    return out


def holder(syms, addr):
    """(start, size, 'name1/name2...') of the symbols holding addr that start where the first does."""
    hits = [(v, n, name) for v, n, name, _b in syms if v <= addr < v + max(n, 1)]
    if not hits:
        return None
    v0, n0 = hits[0][0], hits[0][1]
    return v0, n0, "/".join(name for v, n, name in hits if v == v0 and n == n0)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--map", required=True)
    ap.add_argument("--exact", required=True)
    ap.add_argument("--iv", required=True)
    ap.add_argument("--twin", required=True)
    ap.add_argument("--pin", required=True)
    ap.add_argument("--fn", required=True, metavar="KEY")
    ap.add_argument("--key", action="append", default=[], metavar="NAME=KEY")
    a = ap.parse_args(argv)
    text = strip_comments(open(a.map, encoding="utf-8").read())
    ex, iv = exact_rows(text, a.exact), iv_rows(text, a.iv)
    tf, twin = load(a.twin)
    pf, pin = load(a.pin)
    syms = symbols(twin)
    got = twin.get_section_by_name(".got")
    got_lo, got_hi = (got["sh_addr"], got["sh_addr"] + got["sh_size"]) if got else (0, 0)

    fkey = int(a.fn, 0)
    fa = tsym(ex, iv, fkey)
    h = holder(syms, fa)
    if h is None or h[0] != fa:
        print(f"resolve_keys: function key {fkey:#x} -> {fa:#x}: no symbol starts there", file=sys.stderr)
        return 2
    print(f"function\t{fkey:#x}\t{fa:#x}\t{h[2]}+0x0\tsize {h[1]}")
    args = [f"--start {fa:#x}", f"--end {fa + h[1]:#x}"]
    for kv in a.key:
        name, _, k = kv.partition("=")
        k = int(k, 0)
        addr = tsym(ex, iv, k)
        if got_lo <= addr < got_hi:
            val = int.from_bytes(vread(tf, twin, addr, 8), "little")
            vh = holder(syms, val)
            row = (f"{name}\t{k:#x}\t{addr:#x}\t.got+{addr - got_lo:#x}\tslot holds {val:#x} = "
                   + (f"{vh[2]}+{val - vh[0]:#x}" if vh else "no symbol"))
        else:
            hh = holder(syms, addr)
            if hh is None:
                print(f"resolve_keys: {name} key {k:#x} -> {addr:#x}: no symbol holds it", file=sys.stderr)
                return 2
            row = f"{name}\t{k:#x}\t{addr:#x}\t{hh[2]}+{addr - hh[0]:#x}\tsize {hh[1]}"
        print(row)
        args.append(f"--target {name}={addr:#x}")
    tb, pb = vread(tf, twin, fa, h[1]), vread(pf, pin, fa, h[1])
    print(f"bytes\t{fa:#x}+{h[1]}\t" + ("equal in twin and image" if tb is not None and tb == pb else "DIFFER"))
    print("args\t" + " ".join(args))
    return 0 if tb == pb else 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
