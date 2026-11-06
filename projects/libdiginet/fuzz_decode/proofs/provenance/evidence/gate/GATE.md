# fuzz_decode kit relocation: gate record

Tool: port_addr_check.py, sha256 efa19b81e92ba289e7c185d481faadf045ce7d52d092cc10642fec69924aba03. Donor: proofs/libreac/fuzz_decode/lib at
bf7779f81ed764787b77895d2f5c0db2627f33f3 (the relocation's donor ref). Ported tree: this unit's lib at 70a4ac10b1cb1dadd5428b5899fbbe8debd8bd34.
Images (pins, sha256): decode plain 556b61e63c44907b003aff8b1e8b926863db277b4f2897fdc58967a7beddc9cc, decode ubsan
ff70f30e22dcdcea42fe294ed23995ec278b6c66ace0ecade26d2a917657c1b9; libdiginet fuzz_decode plain d570b4c96d9e764af0482c34642d2e58e6eef3af84e768d2a076a56eaeb045a7,
fuzz_decode ubsan cfe3a2ee2a54a9693cae0c77632e069b3e7dd8ae01a8a8c25258faa955a31f71. Each image is read with its unstripped twin (decode plain 18a5c8eae19b,
decode ubsan a49dc45927bb, fuzz_decode plain 8c3eda27bf35, fuzz_decode ubsan bb338c34b158); each twin's four PT_LOADs equal its pin's (flags,
vaddr, filesz, memsz and bytes, with only e_shoff / e_shnum / e_shstrndx and the build-id note masked).

Command (arguments in angle brackets are local paths):

    port_addr_check.py --git <hub clone> --src bf7779f81ed7:proofs/libreac/fuzz_decode/lib --dst <this unit's lib>
      --src-image P=<decode plain pin>:<twin> --src-image U=<decode ubsan pin>:<twin>
      --dst-image P=<fuzz_decode plain pin>:<twin> --dst-image U=<fuzz_decode ubsan pin>:<twin>
      --assign 'U/**=U' --assign '**=P' --paired-only --fail-on-flags --summary --include <each file the relocation wrote>

The images are keyed by their build letters (P plain, U ubsan), so the named-symbol rule is measured: `count named-symbol
cells UNMEASURED: 0`. The included files are the 1100 .v files the relocation script (k2/README.md) writes for this
unit: the files of the plain / UBSan kit (25e3d17bdb50's file list) that k2-values.tsv does not list as not copied or
dropped, without Theorems.v (the script does not write it). The unit's own files (lib/Spec, the walks and harness files of
lib/Prog and lib/U/Prog, Theorems.v: 99 files) are not relocations; the tool reports them as UNPAIRED-FILE-UNMEASURED
(99 rows, on its own UNMEASURED line: neither a finding nor a pass).

## Control (run first)

One relocated file, Prog/memcpy_c.v, with two planted pointers, run alone with the same command:

- `Definition memcpy_entry` (:19) put back to decode's memcpy, 0x1b634 (a donor code pointer left unmoved);
- the contract's `F (Z_to_bv 64 ..)` (:43) set to 0x1c0a4, the unit's memset (a wrong function of the unit's own image).

Planted: exit 4, `FLAGGED 2 rows in 1 classes: STALE-DONOR-CODE-POINTER=2`; the rows name each plant (`the port value is
__divtf3+0x2e8; ... expected 0x1bca0` and `the port value is memset+0x0; ... expected 0x1bca0`). The same file unplanted:
exit 0, SAME-SYMBOL 2, `FLAGGED 0 rows`. Both plants are caught.

## Result

Exit 4. `FLAG-CLASSES 575d398c6022`. `FLAGGED 609 rows in 3 classes: KIND-CHANGED=1 NON-ADDRESS-CHANGED=28 UNPAIRED-SOURCE=580`.
1100 files paired, 227436 numerals: NON-ADDRESS-SAME 218184, SAME-GEOMETRY 3409, INSN-SAME 2068, SAME-SYMBOL 1825,
IDENT-NAME 882, IMAGE-EXTENT-SAME 246, ROUND-CONSTANT-SAME 114. GENERATOR-FILL rows: 0; DIFFERENT-SYMBOL,
STALE-DONOR-CODE-POINTER, STALE-DONOR-DATA-POINTER, GEOMETRY-CHANGED and UNRESOLVED rows: 0. The 609 rows are in
gate/gate-flagged.tsv.

Each flagged row, with its measured reason (lines are the unit's; plain and U alike unless one image is named):

| rows | class | file:line | reason |
|---|---|---|---|
| 288 + 288 | UNPAIRED-SOURCE | Reusable/YH03.v, U/Reusable/YH03.v | The script regenerates YH03 with only the definitions the unit's files use: donor 331 definitions, kept 43, dropped 288. Each row is one dropped definition (288 distinct), no row is on a kept one, and no other .v file of the unit (all 1199 under lib/) names a dropped definition. |
| 2 + 2 | UNPAIRED-SOURCE | FrameAPI.v:34, :63 | `ms_calloc B = (Some 0x1454c)` (U: 0x14b7c) became `None` (k2-values.tsv `no calloc linked x2`): the unit's symtab has no `calloc` (decode's was called by its harness, check_round_trip+108). The unit links musl's `__libc_calloc` (0x14cf4 / 0x14eec), called only by atexit+96, as decode does; that is not the program's calloc. |
| 1 + 1 | NON-ADDRESS-CHANGED | FrameAPI.v:15 `frame_RELRO` (0xb8 -> 0xd0) | RELRO list length: the list is [(.init_array start, the GOT slot of __stack_chk_guard minus that start); (that slot + 8, 16)]. Decode: 0x1d0c8 - 0x1d010 = 184 (U 0x1d6f8 - 0x1d640); fuzz_decode: 0x1d750 - 0x1d680 = 208 (U 0x1d948 - 0x1d878), from the section headers (fuzz_decode's .data.rel.ro is 0x40 bytes, decode's 0x10). The slot holds the unit's __stack_chk_guard (0x4ed40 / 0x4ef30). k2-values.tsv row `RELRO from .init_array / .got / GOT[__stack_chk_guard]`. |
| 1 + 1 | NON-ADDRESS-CHANGED | Reusable/YL0k.v:184 `src0_R` (0xb8 -> 0xd0) | The same RELRO list length. |
| 2 + 2 | NON-ADDRESS-CHANGED | Reusable/YN3f.v:284, :344 | jal immediates of the decode facts D_17b98 / D_17c20 (`decode_any ... = Some (Jal 1 imm)`, checked in the kernel) of the instruction words at __stdio_write+140 and +276 (plain 0x17100 / 0x17188, U 0x172f8 / 0x17380), read from the unit's image: 0xbadfd0ef and 0xb25fd0ef, both `jal __syscall_ret` (0x14cac / 0x14ea4). The call distance shrank by 0x138: 0x1fda74 -> 0x1fdbac, 0x1fd9ec -> 0x1fdb24. k2-values.tsv `fetch_word at .. read from the image`. |
| 2 + 2 | NON-ADDRESS-CHANGED | Reusable/YL0v.v:393, :396 | Decimal addresses inside driver strings, moved with the string (the script's rule (g)): 66365 -> 66383 is "cli: cannot open %s\n" + 19 (string at 0x1032a in decode, 0x1033c here); 66388 -> 66406 is "cli: read error on %s\n" + 21 (0x1033f, 0x10351). Each string occurs once in each image's .rodata; the tool gives both sides the same `str:` content label. |
| 4 + 4, 4 + 4 | NON-ADDRESS-CHANGED | Reusable/YL0w.v:159, :160; YL0w_cfw.v:154, :155 (two numerals each) | The same 66365 -> 66383 ("cli: cannot open %s\n" + 19) in src0_open_failed and src0_open_failed_cf (k2-values.tsv `x4`). |
| 1 (plain only) | KIND-CHANGED | AllocRoom.v:34 `CAP30 : Z := 86016` | Unchanged from the donor. A slot-count bound (`sb_cap b <= CAP30`, room_slots_giant, AllocRoom.v:69), never an address. 86016 = 0x15000 is the start of get_meta in fuzz_decode.plain, so the tool reads the ported side as an address; in the UBSan image get_meta is at 0x151f8 and there is no row. |

0 rows unexplained.

Reusable/YH03.v (plain and U alike): of the 43 kept definitions per image the tool gives 42 SAME-SYMBOL and 2 IDENT-NAME
(the hex inside the names src0_D_const_HIGHS_0x8080808080808080 / src0_D_const_ONES_0x0101010101010100), and 0
DIFFERENT-SYMBOL; the 43rd, `src0_vmlock : option Z := None`, has no numeral. The 4 hex values the address tool also
classes NON-ADDRESS (k2/k2-conflicts.tsv) are the thread pointer of YN06 / YN06_cf, moved by the builtin_tls + 0xc8 rule;
this tool gives every such numeral SAME-SYMBOL (builtin_tls+0xc8 and +0x24, 44 per image). ZImage.v's .text instruction
count (9831 -> 10213, U 10201 -> 10329) is SAME-GEOMETRY.

## yh03check

yh03check.py sha256 5e92f52b8caa0fcfb55a13ab18beee046fac4447e5c053bdf4215479fc6cf643 with yh03regen.py
4e9a57e74cac7e8f807ddeb49972900d357141c9dbaba4933e5ad2b2966db2a8, the newest registered version (its README lists the units
it covers; libdiginet/fuzz_decode is not one of them, so these rows are its rules applied here, not a covered result).
Run with --pinned and the pins of projects/libdiginet/fuzz_decode/harness.yaml, --other-side and --proofs:

    yh03check.py --pinned <pin> --pins <harness.yaml> --other-side <the other build's YH03.v> --proofs <this unit>
      <the build's unstripped twin> <lib/Reusable/YH03.v | lib/U/Reusable/YH03.v>

Both files, exit 0; self-test 133 known answers OK; unit identity: the twin's 4 PT_LOADs equal the pin (plain d570b4c96d9e,
ubsan cfe3a2ee2a54); COPIED 0 of 0.

| row class | plain | ubsan |
|---|---|---|
| A rows (no E cells in the kept set) | 27 OK (A-ONLY), 0 BAD, 0 ABSENT | 27 OK (A-ONLY), 0 BAD, 0 ABSENT |
| D cells by data symbol | 9 OK, 0 BAD | 9 OK, 0 BAD |
| D cells by the code of a function (OK-BY-LOAD / UNMEASURED) | 0 / 0 | 0 / 0 |
| NOSYM (not checked by the tool) | 6 | 6 |
| string cells | 0 | 0 |
| section-bound cells | none kept | none kept |

The 6 NOSYM cells per image, checked by value against each image: src0_D_const_HIGHS_0x8080808080808080 (0x10668) holds
80 80 80 80 80 80 80 80 and src0_D_const_ONES_0x0101010101010100 (0x10678) holds 00 01 01 01 01 01 01 01 (memchr+0x64 / +0x5c
load them), src0_D_debruijn32 (0x10460) holds the same 32 bytes as decode's table, src0_D_size_classes (0x10480) is
__malloc_size_classes, src0_D_got_stack_chk_guard (0x1d750, U 0x1d948) is the GOT slot that holds __stack_chk_guard
(0x4ed40, U 0x4ef30), src0_D_*_aligned_copy_empty (0x2e9e0, U 0x2ebd0) is oft_aligned_copy.empty (k2/k2-cells.tsv).

## Settings count

global_settings.py sha256 439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242 (r2), over every .v of
proofs/libdiginet/fuzz_decode (1200 files): exit 0; ESCAPES 480, PLAIN 1738, UNMEASURED 1, KERNEL 0. The 1100 relocated
files give ESCAPES 476, PLAIN 1717, UNMEASURED 1 (Lib/Exec.v:137, `Arguments`), and so do their donor counterparts at
bf7779f81ed7, file by file (0 files differ). The unit's own files add ESCAPES 4, all tactic-level `Ltac ... ::=`
redefinitions: Prog/diginet_decoder_next_lib.v:190, Prog/diginet_msg_next.v:117, U/Prog/diginet_msg_next.v:120 and :128
(the two msg_next walks carry them from libdiginet/fuzz_frame's texts), and PLAIN 21.
