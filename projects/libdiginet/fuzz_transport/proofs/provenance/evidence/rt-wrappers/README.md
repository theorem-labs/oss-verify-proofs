# fuzz_transport image A: the strcmp and strlen wrapper texts (relocation record)

Proves no function (kind: measurement). This directory is the record of the relocation that writes
lib/A/Rt/{StrcmpTbl,StrcmpLoop,StrcmpChkX,StrcmpChkY,Strcmp,WrapRoM,Strlen}.v and lib/A/FM{sl0,strlen_chk1,strlen_chk2,
strlen_musl,strlen}.v, and of the two texts the image-A closing lib/A/TransportClose.v takes as Section hypotheses:

| hypothesis | proved by | statement (TransportClose.v's text, word for word) |
|---|---|---|
| H_RT_STRCMP | lib/A/Rt/RtStrcmpCg.v transport_strcmp_realizes | `forall (rc : YM05.RunCeil) (fx : YK11.FPState), @PPF.astrcmp_realizes fx rc segs B (transport_sigma TS___interceptor_trampoline_strcmp)` |
| H_RT_STRLEN | lib/A/Rt/RtStrlenCg.v transport_strlen_realizes | `forall (rc : YM05.RunCeil) (fx : YK11.FPState), @astrlen_realizes fx rc segs B (transport_sigma TS___interceptor_trampoline_strlen)` |

with `segs := tfibsegs`, `B := TransportB` (Local Notations, as in TransportClose.v), PPF =
lib/A/Prog/diginet_personality_from_name_cg.v, astrlen_realizes = lib/A/Prog/TransportRtCg.v.

## Donor

libreac/fuzz_identity, released (release history commit c3777b3715d0), projects/libreac/fuzz_identity/proofs/lib:
A/Rt/StrcmpTbl.v, StrcmpLoop.v, StrcmpChkX.v, StrcmpChkY.v, Strcmp.v (strcmp_icpt_contract), A/FMsl0.v,
FMstrlen_chk1.v, FMstrlen_chk2.v, FMstrlen_musl.v, FMstrlen.v (strlen_icpt_srr), A/Rt/WrapRoM.v (mconsts_of_aro),
A/Rt/Strlen.v (strlen_icpt_contract). Their binder file is A/Rt/WrapBinders.v (astrcmp_binder_A, astrlen_binder_A),
whose sigma-to-entry step the two Cg files repeat. Not relocated: the donor's A/Rt/StrcmpDef.v, Reusable/AStrcmpDef.v,
A/Rt/StrlenDef.v and A/Rt/WrapRo.v: this unit states the same definitions (verbatim, compared after whitespace
normalisation) in lib/A/Prog/diginet_personality_from_name_cg.v (strcmp_res, str_meet, astrcmp_realizes) and
lib/A/Prog/TransportRtCg.v (aro_unowned, astrlen_realizes), and the relocated files use those.
Every other module the donor files Require is this unit's applied core (lib/A/AB1v, AB1w, AE20, AE2y, AE34, AE39,
AE3a, AF0l, AF0m, AF0x, AD2l and 130 lib/Reusable files of the same names); the record class is TransportSyms (the
same fields as the donor's TfibSyms).

## Images

Donor fuzz_identity.asan pin c954b804786c, unstripped twin 5b0cbe573036; target fuzz_transport.asan pin
e89be137db17, unstripped twin 86efc3a80314. Each twin proved by the kit's `drvcmp.py twins` (twins.txt: same PT_LOAD
layout, no differing loaded byte outside the ELF header and the build-id note).

## Byte compare (cmpkit 86da41d3ef68, strictcmp3 65688e94214a, by address)

`tools/byaddr3.py KIT I=<donor twin> T=<target twin> ROW...` calls the kit's own strictcmp3 tcmp / verdict per row
(address in each image, size); output byaddr3-IT.tsv. Every walked function, both texts:

| function | donor | target | size | verdict | words that differ (all pc-relative: an auipc, or the ld / addi that consumes it) |
|---|---|---|---|---|---|
| __interceptor_trampoline_strcmp | 0x42194 | 0x42cec | 4 | EQUAL | none |
| __sanitizer_weak_hook_strcmp | 0x42744 | 0x4329c | 4 | EQUAL | none |
| ___interceptor_strcmp | 0x42748 | 0x432a0 | 1328 | EQUAL-mod-pcrel | 14: +0x7c/+0x80 (the common_flags .got load), +0xb0/+0xb4, +0x100/+0x104, +0x19c/+0x1a0, +0x350/+0x354 and +0x430/+0x434 (the "strcmp" name string, C-string acceptance), +0x4bc and +0x500 (the ld of the 8-byte .rodata word at 0x103d8 / 0x103e0, full-bytes acceptance) |
| __asan_region_is_poisoned | 0x543d4 | 0x54f2c | 836 | EQUAL-mod-pcrel | 26: +0x2c/+0x30, +0x4c/+0x50, +0x54/+0x58, +0x70/+0x74, +0x94/+0x98, +0x9c/+0xa0, +0xb8/+0xbc, +0x1a4/+0x1a8, +0x1f4/+0x1f8, +0x304..+0x310, +0x324..+0x330 (4 C-string acceptances: the CHECK file and condition strings) |
| __asan::TryAsanInitFromRtl | 0x59868 | 0x5a3c0 | 160 | EQUAL-mod-pcrel | 2: +0xc/+0x10 (asan_inited, 0xa5c98 / 0xad6d8) |
| __interceptor_trampoline_strlen | 0x4218c | 0x42ce4 | 4 | EQUAL | none |
| ___interceptor_strlen | 0x4221c | 0x42d74 | 660 | EQUAL-mod-pcrel | 9: +0x3c/+0x40 (real_strlen, 0x9e0b0 / 0xa5d90), +0x54/+0x58 (the common_flags .got slot), +0x80/+0x84 (the shadow-base .got slot), +0x1e0 (the "strlen" string), +0x25c/+0x260 (the .rodata word 0x103d8 / 0x103e0) |
| strlen (musl) | 0x94c64 | 0x9d860 | 144 | EQUAL-mod-pcrel | 4: +0x3c/+0x40 (two auipc), +0x44 (ld ONES 0x10368 / 0x10370), +0x48 (ld HIGHS 0x10350 / 0x10358) |
| __sanitizer::mem_is_zero | 0x64114 | 0x64c6c | 180 | EQUAL-mod-pcrel | 2: +0xa4/+0xa8 (the CHECK strings) |

0 real differences, 0 unmeasured, 0 differing targets in every row. Every runtime function above sits 0xb58 above the
donor's; musl strlen 0x8bfc above.

Rule 8 (the kit's known fail-open for a lui value whose uses are logical ops forming a load / store base):
`luiscan.py` (luiscan-IT.txt) finds 9 lui words in both images, `luiconst` 0, `insec` 0, `memfed` 0, exposure 0, so no
row is in the fail-open class. By hand: ___interceptor_strcmp +0x220, +0x268, +0x37c, +0x3a0, +0x3d4, +0x4a8, +0x4cc
are `lui rX,0x1` followed by `sub rX,s0,rX`: 4096 subtracted from the frame pointer s0 (a stack address, then the
base of a frame-slot load / store), not an image address; __asan::TryAsanInitFromRtl +0x38 `lui a1,0xff0` and +0x40
`lui a2,0x10` are the byte-lane mask 0xff0000 and the value 0x10000 of the lr.w / sc.w loop on the word holding
asan_inited_mutex, used as AMO data, not as an address. The same words in both images.

## The relocation (rtreloc.py)

rtreloc.py (sha256 b39a0f9f3525; internal record) is not in this slice: its code holds a branch name of the donor's
history (in a comment it rewrites, and in the list of words it refuses). It is cited by its file sha256,
b39a0f9f352545e62c86e0bccc339b3635f24f7a7874e670cfdb6af367f11859; tools/img.py is the ELF reader it imports.

`rtreloc.py HUB WT <donor twin> <target twin> numerals.tsv` reads each donor file at c3777b3715d0 and writes it to
this unit. Every numeral of the code and of the kept comments of 0x10000 or more is in numerals.tsv (file, line,
donor value, target value, reason): 387 moved, 592 kept (979 in all). The table:

- code addresses: function + offset in the nine functions above (same name, same size on both sides), and the first
  byte past ___interceptor_strcmp (___interceptor_index) and past ___interceptor_strlen (___interceptor_strnlen), the
  same next symbol on both sides;
- data: __sanitizer::common_flags_dont_use + 0, + 0xf0, + 0xf5, + 0xf8, + 0xfa, + 0xfb (0x136ae8 .. -> 0x13e528 ..),
  __interception::real_strlen (0x9e0b0 -> 0xa5d90); the .got slot that ___interceptor_strcmp + 0x7c / + 0x80 and
  ___interceptor_strlen + 0x54 / + 0x58 read (0x9c3a0 -> 0xa4080), computed from the paired auipc / ld in each image,
  holding common_flags_dont_use in both;
- kept: instruction words (each the same word at the same function offset in the target), and the model constants
  of KEEP (the shadow offset 0x7fff8000 + k, kHighMemEnd 0x7fffffffffff, the range-check fact bounds, the two flag
  words of common_flags + 0xf0 / + 0xf8 and musl's word constants).

The 8-byte flag words are the values of this unit's AF0m Tfib_const rows `z8 (ANum 0x13e618) 0x101000100000000` and
`z8 (ANum 0x13e620) 0x101010101010101` (the same as the donor's); the .got slot row is `z8 (ANum 0xa4080) 0x13e528`,
real_strlen's `z8 (ANum 0xa5d90) 0x9d860`; StrcmpTbl.sc_rodata_chk and FMstrlen.slA_rodata_chk check them by
vm_compute. The shadow cells (0xac9f8 __asan_shadow_memory_dynamic_address, 0xad6e0 kHighMemEnd, 0xad6d8 asan_inited)
are .bss: their values are the core's (AE2y.v icpt_rodata), not file bytes.

Comments: the donor's licence, notice and Modified-by blocks are not copied; each file has its own provenance header;
the donor's description blocks are kept with their numerals moved by the same table, and the comments that named the
donor's images or porting history are reworded (rtreloc.py CONF). FMstrlen_musl.v keeps the donor's third-party
object-code notice line (it restates musl's instruction words), as this unit's listing files carry it.

Code edits beyond numerals (rtreloc.py CONF): module paths; TfibSyms -> TransportSyms; Strcmp.v uses PPF.strcmp_res /
PPF.astrcmp_realizes and states strcmp_icpt_contract at STRCMP_TRAMP (the donor's StrcmpDef bridge lemma is
dropped); Strlen.v states strlen_icpt_contract at FMstrlen.SL_ENTRY over TransportRtCg's text; WrapRoM.v takes
TransportRtCg's aro_unowned. No proof step changed.

## Build and assumptions

`VM=<build VM> cb build <clone> lib/A/Rt/RtStrcmpCg.vo lib/A/Rt/RtStrlenCg.vo` (cb's defaults, dune): rc=0,
2 targets and 12 dependencies compiled, 0 failed, vo check 0 failed, 4 PINNED (facts f6acfcb0c1b8). Own times:
StrcmpChkY 67 s, StrcmpChkX 63 s, FMstrlen_chk2 44 s, every other file under 11 s.
PrintAssumptionsRt12.v (outside lib/, compiled in the checker image against the build's workspace): both theorems
print 13 Prim* primitives and FunctionalExtensionality.functional_extensionality_dep (pa-*.out), no other axiom.

## Re-run of the three measurements (2026-10-31)

From a scratch directory that holds img/ (trans.pin.asan e89be137db17, trans.twin.asan 86efc3a80314, ident.pin.asan
c954b804786c, ident.twin.asan 5b0cbe573036), kit/ (the kit, `sha256sum -c SHA256SUMS` OK, SHA256SUMS sha256
86da41d3ef68), tools/ (byaddr3.py, img.py) and an empty sub/, with PYTHONDONTWRITEBYTECODE=1:

```
python3 tools/byaddr3.py kit I=img/ident.twin.asan T=img/trans.twin.asan tramp_strcmp:0x42194:0x42cec:4 weak_hook_strcmp:0x42744:0x4329c:4 ___interceptor_strcmp:0x42748:0x432a0:1328 __asan_region_is_poisoned:0x543d4:0x54f2c:836 TryAsanInitFromRtl:0x59868:0x5a3c0:160 tramp_strlen:0x4218c:0x42ce4:4 ___interceptor_strlen:0x4221c:0x42d74:660 strlen:0x94c64:0x9d860:144 mem_is_zero:0x64114:0x64c6c:180 > byaddr3-IT.tsv
(cd sub && python3 ../kit/luiscan.py --fns __interceptor_trampoline_strcmp,__sanitizer_weak_hook_strcmp,___interceptor_strcmp,__asan_region_is_poisoned,_ZN6__asan18TryAsanInitFromRtlEv,__interceptor_trampoline_strlen,___interceptor_strlen,strlen,_ZN11__sanitizer11mem_is_zeroEPKcm ../img/ident.twin.asan ../img/trans.twin.asan > luiscan-IT.txt)
(cd img && python3 ../kit/drvcmp.py twins trans.pin.asan trans.twin.asan ident.pin.asan ident.twin.asan > ../twins.txt)
```

Each command exited with status 0, and each output is byte for byte the file of the same name here. numerals.tsv
(rtreloc.py writes it into a clone of the unit) and pa-*.out (a Rocq build) were not re-run.
