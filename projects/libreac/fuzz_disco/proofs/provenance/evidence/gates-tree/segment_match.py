#!/usr/bin/env python3
"""Check each build that harness.yaml pins against the ELF file and against the memory image made from it.

Usage: segment_match.py HARNESS_YAML PIN_DIR SNAPSHOT_TOOL WORK_DIR [--hex-override BUILD:SEG:OFFSET]

For every build under `builds:` in HARNESS_YAML:
  1. PIN: the file PIN_DIR/<file> has the `bytes` and `sha256` that harness.yaml gives.
  2. SNAPSHOT: SNAPSHOT_TOOL (the elf-snapshot tool of the semantics commit that release.yaml names) is run on that file,
     with the arguments of the unit's images/dune rule, into WORK_DIR/<build>/. It must write one .hex file per segment,
     with the chunk counts of the `segments` list.
  3. SEGMENTS: this script reads the PT_LOAD program headers of the ELF itself and, for each mapped PT_LOAD, compares
     the segment's hex bytes with the ELF: the file bytes [p_offset, p_offset + p_filesz) must appear at offset
     p_vaddr mod 4096 of the page-rounded segment, the head slack must be the file bytes before p_offset, and every
     byte past p_vaddr + p_filesz of a segment with p_memsz > p_filesz must be zero.

--hex-override flips one byte of one segment's hex text after the snapshot is written (the planted control: the run
must then report that one segment as a mismatch).

Prints one line per build and segment and a SUMMARY line. Exit 0 = all pins and segments match; 1 = a mismatch;
2 = an input refused (missing file, unreadable harness, the tool failed).
"""
import hashlib
import os
import struct
import subprocess
import sys

PAGE = 4096
PT_LOAD = 1
PREFIX = {"plain": "Plain", "ubsan": "Ubsan", "asan": "Asan", "asan-ubsan": "AsanUbsan"}


def refuse(msg):
    print("REFUSE: " + msg)
    sys.exit(2)


def read_builds(path):
    """The `builds:` block of harness.yaml: {build: {file, bytes, sha256, segments}}. A small reader for this one
    block shape (two-space keys, four-space fields, `- n` list items), so the script needs no YAML library."""
    builds, cur, field, inside = {}, None, None, False
    for raw in open(path, encoding="utf-8"):
        line = raw.rstrip("\n")
        if not line.strip():
            continue
        if not line.startswith(" "):
            inside = line.startswith("builds:")
            continue
        if not inside:
            continue
        if line.startswith("  ") and not line.startswith("   "):
            cur = line.strip().rstrip(":")
            builds[cur] = {"segments": []}
            field = None
        elif line.startswith("    - "):
            if field != "segments":
                refuse("list item outside `segments` in build %s" % cur)
            builds[cur]["segments"].append(int(line.strip()[2:]))
        elif line.startswith("    "):
            key, _, val = line.strip().partition(":")
            field = key
            if val.strip():
                builds[cur][key] = val.strip()
    for b, d in builds.items():
        for k in ("file", "bytes", "sha256"):
            if k not in d:
                refuse("build %s has no `%s`" % (b, k))
    return builds


def loads(data):
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        refuse("not a little-endian ELF64 file")
    phoff = struct.unpack_from("<Q", data, 0x20)[0]
    phentsize, phnum = struct.unpack_from("<HH", data, 0x36)
    out = []
    for i in range(phnum):
        off = phoff + i * phentsize
        p_type = struct.unpack_from("<I", data, off)[0]
        if p_type != PT_LOAD:
            continue
        p_offset, p_vaddr = struct.unpack_from("<QQ", data, off + 8)
        p_filesz, p_memsz = struct.unpack_from("<QQ", data, off + 32)
        if p_memsz:
            out.append((p_offset, p_vaddr, p_filesz, p_memsz))
    return out


def main():
    args = sys.argv[1:]
    override = None
    if "--hex-override" in args:
        i = args.index("--hex-override")
        b, s, o = args[i + 1].split(":")
        override = (b, int(s), int(o, 0))
        del args[i : i + 2]
    if len(args) != 4:
        refuse("usage: segment_match.py HARNESS_YAML PIN_DIR SNAPSHOT_TOOL WORK_DIR [--hex-override BUILD:SEG:OFFSET]")
    harness, pin_dir, tool, work = args
    for p in (harness, tool):
        if not os.path.isfile(p):
            refuse("no file: " + p)
    print("TOOL snapshot sha256=" + hashlib.sha256(open(tool, "rb").read()).hexdigest())
    print("HARNESS sha256=" + hashlib.sha256(open(harness, "rb").read()).hexdigest())
    builds = read_builds(harness)
    pins_ok = segs_ok = segs_n = 0
    bad = 0
    for build, d in builds.items():
        if build not in PREFIX:
            refuse("unknown build name " + build)
        elf = os.path.join(pin_dir, d["file"])
        if not os.path.isfile(elf):
            refuse("no pinned file for build %s: %s" % (build, d["file"]))
        data = open(elf, "rb").read()
        sha = hashlib.sha256(data).hexdigest()
        ok = sha == d["sha256"] and len(data) == int(d["bytes"])
        print("PIN %s %s bytes=%d sha256=%s %s" % (build, d["file"], len(data), sha, "MATCH" if ok else "DIFFERS"))
        pins_ok += ok
        bad += not ok
        out = os.path.join(work, build)
        os.makedirs(out, exist_ok=True)
        pre = PREFIX[build]
        r = subprocess.run(
            [sys.executable, tool, elf, os.path.join(out, pre + ".v"), "--prefix", pre, "--module-name", "M",
             "--namespace", "OssFuzzTheorems.libreac.fuzz_disco.images"],
            capture_output=True, text=True)
        if r.returncode != 0:
            refuse("snapshot tool failed on %s (rc %d): %s" % (build, r.returncode, r.stderr.strip()[-300:]))
        segs = loads(data)
        if len(segs) != len(d["segments"]):
            print("SEGCOUNT %s ELF=%d harness=%d DIFFERS" % (build, len(segs), len(d["segments"])))
            bad += 1
        for k, (p_offset, p_vaddr, p_filesz, p_memsz) in enumerate(segs):
            segs_n += 1
            chunks = d["segments"][k] if k < len(d["segments"]) else 0
            names = (["%s_seg_%03d.hex" % (pre, k)] if chunks == 1 else
                     ["%s_seg_%03d_chunk_%03d.hex" % (pre, k, c) for c in range(chunks)])
            missing = [n for n in names if not os.path.isfile(os.path.join(out, n))]
            if missing:
                print("SEG %s %d MISSING %s" % (build, k, " ".join(missing)))
                bad += 1
                continue
            if override and override[0] == build and override[1] == k:
                p = os.path.join(out, names[0])
                t = bytearray(open(p).read().strip(), "ascii")
                j = 2 * override[2]
                t[j : j + 2] = b"%02x" % (int(t[j : j + 2], 16) ^ 0x01)
                open(p, "w").write(t.decode())
            img = bytes.fromhex("".join(open(os.path.join(out, n)).read().strip() for n in names))
            lo = p_vaddr - p_vaddr % PAGE
            hi = (p_vaddr + p_memsz + PAGE - 1) // PAGE * PAGE
            delta = p_vaddr - lo
            want_file = data[p_offset : p_offset + p_filesz]
            file_span = (delta + p_filesz + PAGE - 1) // PAGE * PAGE
            tail = data[p_offset + p_filesz : p_offset - delta + file_span]
            tail += b"\x00" * (file_span - delta - p_filesz - len(tail))
            checks = [
                ("size", len(img) == hi - lo),
                ("file bytes", img[delta : delta + p_filesz] == want_file),
                ("head slack", p_filesz == 0 or img[:delta] == data[p_offset - delta : p_offset]),
                ("tail slack", p_filesz == 0 or p_memsz > p_filesz
                 or img[delta + p_filesz : file_span] == tail),
                ("bss zero", p_memsz <= p_filesz or not any(img[delta + p_filesz :])),
                ("past file pages zero", p_filesz == 0 or not any(img[file_span:])),
            ]
            failed = [n for n, c in checks if not c]
            print("SEG %s %d vaddr=0x%x filesz=0x%x memsz=0x%x span=0x%x-0x%x sha256(file bytes)=%s %s" % (
                build, k, p_vaddr, p_filesz, p_memsz, lo, hi, hashlib.sha256(want_file).hexdigest()[:16],
                "MATCH" if not failed else "DIFFERS (" + ", ".join(failed) + ")"))
            segs_ok += not failed
            bad += bool(failed)
    print("SUMMARY: pins %d/%d match, segments %d/%d match, mismatches %d" % (
        pins_ok, len(builds), segs_ok, segs_n, bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
