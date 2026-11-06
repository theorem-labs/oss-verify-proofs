#!/usr/bin/env python3
"""The GXA memcpy / memset build table lib/<IMAGE>/RT_gxa_mem_Tbl.v of proofs/libreac/fuzz_disco (image A =
fuzz_disco.asan, image B = fuzz_disco.asan-ubsan). One script for both images: the new version of the two scripts of
record (one per image, which differed only in the image inputs, the lib directory read and two lines of the output
header). Changed from them: every input is an argument, the lib files are read from git, the nm lines are read from
an extract (its `#` lines skipped), the JSON log is optional. Same measurement, same output bytes.

  gen_tbl.py IMAGE HUB LIB_REF DONOR_REF REPLY_PIN REPLY_NM DISCO_PIN DISCO_NM OUT [LOG]

IMAGE      A or B.
HUB        a git repository holding LIB_REF and DONOR_REF.
LIB_REF    the commit whose proofs/libreac/fuzz_disco/lib/<IMAGE>/ files (the 18 paths of FILES) are counted; for B
           the text `fuzz_disco.lib.B` is read as `fuzz_disco.lib.A` before the token comparison.
DONOR_REF  the commit holding the donor files proofs/plugin-hostd/fuzz_reply/lib/A/... (the same 18 paths).
REPLY_PIN  the stripped fuzz_reply asan image; DISCO_PIN the stripped image IMAGE. Their sha256 are checked against
           SHA / IMAGES below and written into the table.
REPLY_NM, DISCO_NM  the nm lines of the two images (the extracts nm_extract.py writes; lines starting with # are skipped).
OUT        the table written. LOG (optional): a JSON log of every value measured, with the counts and frames on stdout.

What it measures, from the image bytes: 15 functions held by both images are paired by name (same size, same
instruction count; an instruction that differs differs only in its pc-relative operand, whose target in both images
is the same symbol + offset, the same C string, a slot holding the same symbol + offset, or 32 equal bytes); the GOT
and data cells the copy / set paths read; the stack frames of the copy and set paths; the trampoline jumps; the address
numerals of the 18 files moved from the donor (code / data) or kept. The table states them as Coq facts the kernel
checks (fetch_word of the image segments, the frame sums against the GXA depth constants).
"""
import hashlib, json, re, struct, subprocess, sys
from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC

IMAGES = {"A": dict(sha="5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46",
                    sha_name="FUZZ_DISCO_ASAN_SHA256"),
          "B": dict(sha="cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146",
                    sha_name="FUZZ_DISCO_ASAN_UBSAN_SHA256")}
if len(sys.argv) not in (10, 11) or sys.argv[1] not in IMAGES:
    sys.exit(__doc__)
IMG = sys.argv[1]
HUB, LIB_REF, DONOR_REF = sys.argv[2:5]
DONOR_LIB = "proofs/plugin-hostd/fuzz_reply/lib"
LIB = "proofs/libreac/fuzz_disco/lib"
ELF = {"R": sys.argv[5], "D": sys.argv[7]}
NM = {"R": sys.argv[6], "D": sys.argv[8]}
SHA = {"R": "42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a",
       "D": IMAGES[IMG]["sha"]}
OUT = sys.argv[9]
LOG = sys.argv[10] if len(sys.argv) == 11 else None


def git_show(ref, path):
    return subprocess.run(["git", "-C", HUB, "show", f"{ref}:{path}"], check=True, capture_output=True,
                          text=True).stdout


log = {}
raw = {}
for k, p in ELF.items():
    raw[k] = open(p, "rb").read()
    h = hashlib.sha256(raw[k]).hexdigest()
    assert h == SHA[k], (k, h)
    log["sha256_" + k] = h


def segs(d):
    phoff = struct.unpack_from("<Q", d, 0x20)[0]
    phentsize = struct.unpack_from("<H", d, 0x36)[0]
    phnum = struct.unpack_from("<H", d, 0x38)[0]
    out = []
    for i in range(phnum):
        o = phoff + i * phentsize
        p_type, p_flags = struct.unpack_from("<II", d, o)
        p_offset, p_vaddr, _, p_filesz, p_memsz = struct.unpack_from("<QQQQQ", d, o + 8)
        if p_type == 1:
            out.append((p_vaddr, p_filesz, p_offset, p_memsz, p_flags))
    return out


SEGS = {k: segs(raw[k]) for k in raw}


def rd(k, a, n):
    for va, sz, off, _, _ in SEGS[k]:
        if va <= a and a + n <= va + sz:
            return raw[k][off + (a - va):off + (a - va) + n]
    raise KeyError(hex(a))


def is_exec(k, a):
    for va, _, _, msz, fl in SEGS[k]:
        if va <= a < va + msz:
            return bool(fl & 1)
    return None


def nmrows(k):
    rows = []
    for l in open(NM[k]):
        if l.startswith("#"):
            continue
        q = l.split()
        if len(q) >= 4:
            rows.append((q[0], q[1], q[2], q[-1]))
    return rows


NMR = {k: nmrows(k) for k in NM}


def nm1(k, name, idx=None):
    hits = sorted([r for r in NMR[k] if r[3] == name], key=lambda r: int(r[0], 16))
    if idx is None:
        assert len(hits) == 1, (k, name, hits)
        r = hits[0]
    else:
        r = hits[idx]
    return int(r[0], 16), int(r[1], 16), r


md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)


def dis(k, a, n):
    return list(md.disasm(rd(k, a, n), a))


def targets(insns):
    base = {}
    out = {}
    for i, x in enumerate(insns):
        m = x.mnemonic
        o = x.op_str
        if m == "auipc":
            r, imm = [t.strip() for t in o.split(",")]
            v = int(imm, 0)
            base[r] = x.address + ((v - (1 << 20) if v >= (1 << 19) else v) << 12)
        elif m in ("jal", "j"):
            out[i] = x.address + int(o.split(",")[-1].strip(), 0)
        else:
            mm = re.search(r"(-?0x[0-9a-f]+|-?\d+)\(([a-z0-9]+)\)$", o)
            if mm and mm.group(2) in base:
                out[i] = base.pop(mm.group(2)) + int(mm.group(1), 0)
            else:
                mm2 = re.match(r"^([a-z0-9]+),\s*([a-z0-9]+),\s*(-?0x[0-9a-f]+|-?\d+)$", o)
                if mm2 and m == "addi" and mm2.group(2) in base:
                    out[i] = base.pop(mm2.group(2)) + int(mm2.group(3), 0)
    return out


FUNCS = [
    ("tramp_memset", "__interceptor_trampoline_memset", None),
    ("tramp_memcpy", "__interceptor_trampoline_memcpy", None),
    ("asan_memcpy", "__asan_memcpy", None),
    ("asan_memset", "__asan_memset", None),
    ("icpt_memset", "___interceptor_memset", None),
    ("icpt_memcpy", "___interceptor_memcpy", None),
    ("mem_to_shadow_3", "_ZN6__asanL11MemToShadowEm", 2),
    ("mem_to_shadow_4", "_ZN6__asanL11MemToShadowEm", 3),
    ("mem_to_shadow_5", "_ZN6__asanL11MemToShadowEm", 4),
    ("region_is_poisoned", "__asan_region_is_poisoned", None),
    ("asan_inited_fn", "_ZN6__asan10AsanInitedEv", None),
    ("try_asan_init_from_rtl", "_ZN6__asan18TryAsanInitFromRtlEv", None),
    ("mem_is_zero", "_ZN11__sanitizer11mem_is_zeroEPKcm", None),
    ("musl_memcpy", "memcpy", None),
    ("musl_memset", "memset", None),
]

SYMS = {k: sorted([(int(r[0], 16), int(r[1], 16), r[3]) for r in NMR[k] if int(r[1], 16) > 0]) for k in NMR}


def sym_of(k, a):
    best = None
    for s, n, name in SYMS[k]:
        if s <= a < s + n:
            if best is None or n < best[1]:
                best = (s, n, name)
    return None if best is None else (best[2], a - best[0])


def q8(k, a):
    try:
        return struct.unpack("<Q", rd(k, a, 8))[0]
    except KeyError:
        return None


unnamed = set()
def cstr(k, a):
    try:
        b = rd(k, a, 64)
    except KeyError:
        return None
    z = b.find(b"\0")
    if z <= 0 or not all(32 <= c < 127 for c in b[:z]):
        return None
    return b[:z].decode()


pairs = []
tmaps = []
for tag, name, idx in FUNCS:
    ra, rs, rrow = nm1("R", name, idx)
    da, ds, drow = nm1("D", name, idx)
    assert rs == ds, (tag, rs, ds)
    A = dis("R", ra, rs)
    B = dis("D", da, ds)
    assert len(A) == len(B), tag
    assert sum(x.size for x in A) == rs and sum(x.size for x in B) == ds, tag
    ta = targets(A)
    tb = targets(B)
    diff = 0
    for i, (x, y) in enumerate(zip(A, B)):
        assert x.size == y.size, (tag, hex(x.address))
        if x.bytes == y.bytes:
            continue
        diff += 1
        assert x.mnemonic == y.mnemonic, (tag, hex(x.address))
        ox = [t.strip() for t in x.op_str.split(",")]
        oy = [t.strip() for t in y.op_str.split(",")]
        assert len(ox) == len(oy) and ox[:-1] == oy[:-1], (tag, hex(x.address))
        if i in ta and i in tb:
            tmaps.append((ta[i], tb[i], tag))
            sr, sd = sym_of("R", ta[i]), sym_of("D", tb[i])
            if sr is None or sd is None:
                assert sr is None and sd is None, (tag, hex(x.address))
                s_r, s_d = cstr("R", ta[i]), cstr("D", tb[i])
                if s_r is not None and s_r == s_d:
                    unnamed.add((ta[i], tb[i], ("string", s_r)))
                else:
                    vr, vd = q8("R", ta[i]), q8("D", tb[i])
                    assert vr is not None and vd is not None, (tag, hex(x.address))
                    svr, svd = sym_of("R", vr), sym_of("D", vd)
                    if svr is not None and svr == svd:
                        unnamed.add((ta[i], tb[i], ("slot", svr)))
                    else:
                        assert rd("R", ta[i], 32) == rd("D", tb[i], 32), (tag, hex(x.address), hex(vr), hex(vd))
                        unnamed.add((ta[i], tb[i], ("const", rd("D", tb[i], 32).hex())))
            else:
                assert sr == sd, (tag, hex(x.address), hex(ta[i]), hex(tb[i]), sr, sd)
        else:
            assert x.mnemonic == "auipc", (tag, hex(x.address), x.mnemonic, x.op_str, y.op_str)
    pairs.append(dict(tag=tag, name=name, r=ra, d=da, size=rs, insns=len(A), differing=diff,
                      nm_r=" ".join(rrow), nm_d=" ".join(drow)))
log["unnamed_targets"] = sorted((hex(a), hex(b), str(c)) for a, b, c in unnamed)
log["code_pairs"] = [{k: (hex(v) if isinstance(v, int) and k in ("r", "d", "size") else v) for k, v in p.items()}
                     for p in pairs]


def q8(k, a):
    try:
        return struct.unpack("<Q", rd(k, a, 8))[0]
    except KeyError:
        return None


cells = []
for tag, sym in [("got_shadow_cell", "__asan_shadow_memory_dynamic_address"),
                 ("got_replace_intrin_flag", "_ZN6__asan21replace_intrin_cachedE")]:
    sr = nm1("R", sym)[0]
    sd = nm1("D", sym)[0]
    found = sorted({(r, d) for r, d, _ in tmaps if q8("R", r) == sr and q8("D", d) == sd})
    assert len(found) == 1, (tag, found)
    r, d = found[0]
    via = sorted({t for rr, dd, t in tmaps if (rr, dd) == (r, d)})
    cells.append(dict(tag=tag, r=r, d=d, vr=sr, vd=sd, via=via))
for tag, sym, val in [("real_memcpy", "_ZN14__interception11real_memcpyE", "memcpy"),
                      ("real_memset", "_ZN14__interception11real_memsetE", "memset")]:
    r = nm1("R", sym)[0]
    d = nm1("D", sym)[0]
    vr = nm1("R", val)[0]
    vd = nm1("D", val)[0]
    assert q8("R", r) == vr and q8("D", d) == vd, tag
    cells.append(dict(tag=tag, r=r, d=d, vr=vr, vd=vd, via=[]))
for tag, sym in [("asan_inited", "_ZN6__asanL11asan_initedE"), ("k_high_mem_end", "_ZN6__asan11kHighMemEndE"),
                 ("k_mid_mem_beg", "_ZN6__asan10kMidMemBegE"), ("k_mid_mem_end", "_ZN6__asan10kMidMemEndE")]:
    r = nm1("R", sym)[0]
    d = nm1("D", sym)[0]
    cells.append(dict(tag=tag, r=r, d=d, vr=None, vd=None, via=[]))
log["data_pairs"] = [{k: (hex(v) if isinstance(v, int) else v) for k, v in c.items()} for c in cells]


def frames(k, a, n, leaf=False):
    ins = dis(k, a, n)
    out = []
    for x in (ins if leaf else ins[:24]):
        s = x.op_str.replace(" ", "")
        if x.mnemonic in ("addi", "c.addi", "c.addi16sp") and s.startswith("sp,sp,-"):
            out.append((x.address, -int(s.split(",")[-1], 0), struct.unpack("<I", rd(k, x.address, 4))[0]))
        assert not (x.mnemonic == "sub" and s.startswith("sp,sp")), (hex(a), "variable frame")
    return out


P = {p["tag"]: p for p in pairs}
FR = {}
for tag in ("icpt_memcpy", "icpt_memset", "region_is_poisoned", "mem_is_zero", "musl_memcpy", "musl_memset"):
    fd = frames("D", P[tag]["d"], P[tag]["size"], leaf=tag.startswith("musl"))
    fr = frames("R", P[tag]["r"], P[tag]["size"], leaf=tag.startswith("musl"))
    assert [b for _, b, _ in fd] == [b for _, b, _ in fr], tag
    FR[tag] = fd
log["frames_D"] = {t: [(hex(a), hex(b), (hex(w) if w is not None else None)) for a, b, w in v] for t, v in FR.items()}
assert FR["musl_memcpy"] == [] and FR["musl_memset"] == []


def w32(k, a):
    return struct.unpack("<I", rd(k, a, 4))[0]


MAIN = nm1("D", "main")[0]
FUZZ = nm1("D", "LLVMFuzzerTestOneInput")[0]
MC_TRAMP, MC_ICPT = P["tramp_memcpy"]["d"], P["icpt_memcpy"]["d"]
MS_TRAMP, MS_ICPT = P["tramp_memset"]["d"], P["icpt_memset"]["d"]
for t, i in ((MC_TRAMP, MC_ICPT), (MS_TRAMP, MS_ICPT)):
    x = dis("D", t, 4)
    assert len(x) == 1 and x[0].mnemonic == "j" and t + int(x[0].op_str, 0) == i, (hex(t), x[0].op_str)


def jal_off(w):
    i = ((w >> 31) & 1) * (1 << 20) + ((w >> 21) & 0x3ff) * 2 + ((w >> 20) & 1) * (1 << 11) + ((w >> 12) & 0xff) * (1 << 12)
    return i - (1 << 21) if i >= (1 << 20) else i


assert (w32("D", MC_TRAMP) & 0xfff) == 0x6f and MC_TRAMP + jal_off(w32("D", MC_TRAMP)) == MC_ICPT
assert (w32("D", MS_TRAMP) & 0xfff) == 0x6f and MS_TRAMP + jal_off(w32("D", MS_TRAMP)) == MS_ICPT

FILES = ["A/Bz/A/I_memcpyw.v", "A/Bz/A/I_memcpyw2.v", "A/Bz/A/I_amemcpyw.v", "A/Bz/A/I_amemcpyw2.v",
         "A/Bz/A/I_amemcpy.v", "A/Bz/A/I_memcpy.v", "A/Bz/A/I_memsetw.v", "A/Bz/A/F_memset.v",
         "A/Bz/A/I_imemset.v", "A/Prog/memcpy_c.v", "A/Prog/memcpy.v", "A/Prog/memcpy_same_c.v",
         "A/Prog/memcpy_same.v", "A/Prog/memset_c.v", "A/Prog/memset.v", "A/R_memset.v",
         "A/Strw/STRW_tac.v", "A/Strw/STRWaj3.v"]


def strip_comments(s):
    o = []
    d = 0
    i = 0
    while i < len(s):
        if s.startswith("(*", i):
            d += 1
            i += 2
            continue
        if d and s.startswith("*)", i):
            d -= 1
            i += 2
            continue
        if d == 0:
            o.append(s[i])
        i += 1
    return "".join(o)


TOK = re.compile(r"0x[0-9a-fA-F]+|\d+|[A-Za-z_][A-Za-z_0-9'.]*|\S")


def toks(s):
    s = strip_comments(s).replace("plugin_hostd.fuzz_reply", "libreac.fuzz_disco")
    return TOK.findall(s)


def num(t):
    return int(t, 16) if t.lower().startswith("0x") else (int(t) if t.isdigit() else None)


moved_code = moved_data = kept = 0
per_file = {}
for f in FILES:
    a = toks(git_show(DONOR_REF, f"{DONOR_LIB}/{f}"))
    if IMG == "A":
        b = toks(git_show(LIB_REF, f"{LIB}/{f}"))
    else:
        b = toks(git_show(LIB_REF, f"{LIB}/B/{f[2:]}").replace("fuzz_disco.lib.B", "fuzz_disco.lib.A"))
    assert len(a) == len(b), (f, len(a), len(b))
    mc = mdt = kp = 0
    for x, y in zip(a, b):
        nx, ny = num(x), num(y)
        if nx is None or ny is None:
            assert x == y, (f, x, y)
            continue
        if nx != ny:
            if is_exec("D", ny):
                mc += 1
            else:
                mdt += 1
        elif nx >= 0x10000:
            kp += 1
    per_file[f] = (mc, mdt, kp)
    moved_code += mc
    moved_data += mdt
    kept += kp
log["counts_per_file"] = per_file
log["counts"] = dict(moved_code=moved_code, moved_data=moved_data, kept=kept)


def h(x):
    return "0x%x" % x


def hw(x):
    return "0x%08x" % x


L = []
L.append("From Stdlib Require Import ZArith List.")
L.append("From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.")
L.append(f"From OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.{IMG}.Bz.Lib Require Import ImageA.")
L.append("Require OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.CopyCall.")
L.append("Require OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.SetCall.")
L.append("Import ListNotations.")
L.append("Open Scope Z_scope.")
L.append("")
L.append("Module GXC := OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.CopyCall.")
L.append("Module GXM := OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.SetCall.")
L.append("")
L.append(f"Definition MC_TRAMP : Z := {h(MC_TRAMP)}.")
L.append(f"Definition MC_ICPT : Z := {h(MC_ICPT)}.")
L.append(f"Definition MS_TRAMP : Z := {h(MS_TRAMP)}.")
L.append(f"Definition MS_ICPT : Z := {h(MS_ICPT)}.")
L.append("")
L.append(f"Definition DONOR_FUZZ_REPLY_ASAN_SHA256 : Z := 0x{SHA['R']}.")
L.append(f"Definition {IMAGES[IMG]['sha_name']} : Z := 0x{SHA['D']}.")
L.append("")
L.append("Record code_pair : Type := { cp_donor : Z; cp_disco : Z; cp_size : Z; cp_insns : Z; cp_differing : Z }.")
L.append("")
for p in pairs:
    L.append(f"Definition CP_{p['tag']} : code_pair :=")
    L.append(f"  {{| cp_donor := {h(p['r'])}; cp_disco := {h(p['d'])}; cp_size := {h(p['size'])}; "
             f"cp_insns := {p['insns']}; cp_differing := {p['differing']} |}}.")
L.append("")
L.append("Definition code_pairs : list code_pair :=")
L.append("  [" + ";\n   ".join("CP_" + p["tag"] for p in pairs) + "].")
L.append("")
L.append("Record data_pair : Type := { dp_donor : Z; dp_disco : Z; dp_donor_value : option Z; dp_disco_value : option Z }.")
L.append("")
for c in cells:
    vr = f"Some {h(c['vr'])}" if c["vr"] is not None else "None"
    vd = f"Some {h(c['vd'])}" if c["vd"] is not None else "None"
    L.append(f"Definition DP_{c['tag']} : data_pair :=")
    L.append(f"  {{| dp_donor := {h(c['r'])}; dp_disco := {h(c['d'])}; dp_donor_value := {vr}; dp_disco_value := {vd} |}}.")
L.append("")
L.append("Definition data_pairs : list data_pair :=")
L.append("  [" + ";\n   ".join("DP_" + c["tag"] for c in cells) + "].")
L.append("")
L.append("Record frame_site : Type := { fs_pc : Z; fs_bytes : Z; fs_word : Z }.")
L.append("")
for t in ("icpt_memcpy", "icpt_memset", "region_is_poisoned", "mem_is_zero", "musl_memcpy", "musl_memset"):
    items = ";\n   ".join(f"{{| fs_pc := {h(a)}; fs_bytes := {h(b)}; fs_word := {hw(w)} |}}" for a, b, w in FR[t])
    if items:
        items = "\n  [" + items + "]"
    else:
        items = " []"
    L.append(f"Definition FR_{t} : list frame_site :={items}.")
L.append("")
L.append("Definition frame_bytes (l : list frame_site) : Z := fold_right (fun f s => fs_bytes f + s) 0 l.")
L.append("")
L.append("Lemma copy_depth_measured :")
L.append("  frame_bytes (FR_icpt_memcpy ++ FR_region_is_poisoned ++ FR_mem_is_zero ++ FR_musl_memcpy) = GXC.COPY_DEPTH.")
L.append("Proof. reflexivity. Qed.")
L.append("")
L.append("Lemma set_depth_measured :")
L.append("  frame_bytes (FR_icpt_memset ++ FR_region_is_poisoned ++ FR_mem_is_zero ++ FR_musl_memset) = GXM.SET_DEPTH.")
L.append("Proof. reflexivity. Qed.")
L.append("")
L.append("Lemma entries_paired :")
L.append("  cp_disco CP_tramp_memcpy = MC_TRAMP /\\ cp_disco CP_icpt_memcpy = MC_ICPT /\\")
L.append("  cp_disco CP_tramp_memset = MS_TRAMP /\\ cp_disco CP_icpt_memset = MS_ICPT /\\")
L.append("  option_map fs_pc (hd_error FR_icpt_memcpy) = Some MC_ICPT /\\")
L.append("  option_map fs_pc (hd_error FR_icpt_memset) = Some MS_ICPT /\\")
L.append("  dp_disco_value DP_real_memcpy = Some (cp_disco CP_musl_memcpy) /\\")
L.append("  dp_disco_value DP_real_memset = Some (cp_disco CP_musl_memset).")
L.append("Proof. repeat split; reflexivity. Qed.")
L.append("")
L.append(f"Definition MC_TRAMP_WORD : Z := {hw(w32('D', MC_TRAMP))}.")
L.append(f"Definition MS_TRAMP_WORD : Z := {hw(w32('D', MS_TRAMP))}.")
L.append("")
L.append("Definition jal_offset (w : Z) : Z :=")
L.append("  let i := Z.land (Z.shiftr w 31) 1 * 2 ^ 20 + Z.land (Z.shiftr w 21) 0x3ff * 2")
L.append("           + Z.land (Z.shiftr w 20) 1 * 2 ^ 11 + Z.land (Z.shiftr w 12) 0xff * 2 ^ 12 in")
L.append("  if 2 ^ 20 <=? i then i - 2 ^ 21 else i.")
L.append("")
L.append("Lemma tramps_jump :")
L.append("  Z.land MC_TRAMP_WORD 0xfff = 0x6f /\\ MC_TRAMP + jal_offset MC_TRAMP_WORD = MC_ICPT /\\")
L.append("  Z.land MS_TRAMP_WORD 0xfff = 0x6f /\\ MS_TRAMP + jal_offset MS_TRAMP_WORD = MS_ICPT.")
L.append("Proof. vm_compute. repeat split. Qed.")
L.append("")
L.append(f"Definition MOVED_CODE_NUMERALS : Z := {moved_code}.")
L.append(f"Definition MOVED_DATA_NUMERALS : Z := {moved_data}.")
L.append(f"Definition KEPT_ADDRESS_SIZED_NUMERALS : Z := {kept}.")
L.append("")
ident = [(MAIN, w32("D", MAIN)), (FUZZ, w32("D", FUZZ))]
L.append("Lemma rt_gxa_mem_build_identity :")
rows = [f"fetch_word asegs (Z_to_bv 64 {h(a)}) = Some (Z_to_bv 32 {hw(w)})" for a, w in ident]
rows.append("fetch_word asegs (Z_to_bv 64 MC_TRAMP) = Some (Z_to_bv 32 MC_TRAMP_WORD)")
rows.append("fetch_word asegs (Z_to_bv 64 MS_TRAMP) = Some (Z_to_bv 32 MS_TRAMP_WORD)")
for t in ("icpt_memcpy", "icpt_memset", "region_is_poisoned", "mem_is_zero"):
    for a, b, w in FR[t]:
        rows.append(f"fetch_word asegs (Z_to_bv 64 {h(a)}) = Some (Z_to_bv 32 {hw(w)})")
for t in ("musl_memcpy", "musl_memset"):
    a = P[t]["d"]
    rows.append(f"fetch_word asegs (Z_to_bv 64 {h(a)}) = Some (Z_to_bv 32 {hw(w32('D', a))})")
for i, r in enumerate(rows):
    L.append("  " + r + (" /\\" if i + 1 < len(rows) else "."))
L.append("Proof. repeat split; vm_compute; reflexivity. Qed.")

open(OUT, "w").write("\n".join(L) + "\n")
log["identity_words"] = [(hex(a), hex(w)) for a, w in ident]
log["tramp_words"] = (hex(w32("D", MC_TRAMP)), hex(w32("D", MS_TRAMP)))
if LOG:
    json.dump(log, open(LOG, "w"), indent=1, default=str)
    print(json.dumps(log["counts"]), json.dumps(log["frames_D"]))
