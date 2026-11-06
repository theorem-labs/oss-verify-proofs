#!/usr/bin/env python3
"""musl's __vm_wait in an unstripped image: its symbol, the symbols at the same address, its bytes, and every symbol
whose name holds "vmlock". Usage: measure-vmlock.py IMAGE... (needs pyelftools)."""
import sys

from elftools.elf.elffile import ELFFile


def main():
    for path in sys.argv[1:]:
        with open(path, "rb") as fh:
            elf = ELFFile(fh)
            syms = [s for s in elf.get_section_by_name(".symtab").iter_symbols() if s.name]
            print(f"# {path.rsplit('/', 1)[-1]}")
            for v in [s for s in syms if s.name == "__vm_wait"]:
                at = sorted({(s.name, s["st_info"]["type"], s["st_size"]) for s in syms if s["st_value"] == v["st_value"]})
                print(f"__vm_wait value 0x{v['st_value']:x} size {v['st_size']} type {v['st_info']['type']}")
                print("symbols at that address: " + ", ".join(f"{n} ({t}, size {z})" for n, t, z in at))
                for seg in elf.iter_segments():
                    if seg["p_type"] == "PT_LOAD" and seg["p_vaddr"] <= v["st_value"] < seg["p_vaddr"] + seg["p_filesz"]:
                        off = seg["p_offset"] + v["st_value"] - seg["p_vaddr"]
                        fh.seek(off)
                        b = fh.read(max(v["st_size"], 4))
                        print("bytes: " + " ".join(f"{x:02x}" for x in b) +
                              (" (jalr zero,0(ra): a bare return)" if b[:4] == bytes([0x67, 0x80, 0x00, 0x00]) else ""))
            vm = sorted(s.name for s in syms if "vmlock" in s.name.lower())
            print("symbols whose name holds 'vmlock': " + (", ".join(vm) if vm else "none"))


if __name__ == "__main__":
    main()
