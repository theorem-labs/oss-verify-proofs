# fuzz_uci kit relocation: gate record

Tool: port_addr_check.py, sha256 efa19b81e92ba289e7c185d481faadf045ce7d52d092cc10642fec69924aba03. Donor: proofs/libreac/fuzz_decode/lib at
25e3d17bdb5059606131377a3722d585415ab5d6. Images (pins, sha256): decode plain 556b61e63c44907b003aff8b1e8b926863db277b4f2897fdc58967a7beddc9cc,
decode ubsan ff70f30e22dcdcea42fe294ed23995ec278b6c66ace0ecade26d2a917657c1b9; fuzz_uci plain a6119aa7f1f281cacb63a767e0b5e6976b8f220542f6109c4fd2cecaf98ae5ac, fuzz_uci ubsan fa87ac3037db248a9ae80eb487b18990df08b26707cb501947d2831f6ccee58c.

Command (arguments in angle brackets are local paths):

    port_addr_check.py --git <hub clone> --src 25e3d17bdb50:proofs/libreac/fuzz_decode/lib --dst <this unit's lib>
      --src-image A=<decode plain pin>:<twin> --src-image U=<decode ubsan pin>:<twin>
      --dst-image A=<fuzz_uci plain pin>:<twin> --dst-image U=<fuzz_uci ubsan pin>:<twin>
      --assign 'U/**=U' --assign '**=A' --paired-only --fail-on-flags --summary --include <each file the relocation wrote>

The included files are the 1084 .v files the relocation script (k2/k2_relocate.py) writes for fuzz_uci; the unit's own
files (lib/Spec, the walks and harness files of lib/Prog and lib/U/Prog) are not relocations and are not paired.

Result: exit 4. `FLAG-CLASSES 575d398c6022`. `FLAGGED 768 rows in 4 classes: DIFFERENT-SYMBOL=2 KIND-CHANGED=2
NON-ADDRESS-CHANGED=10 UNPAIRED-SOURCE=754`. GENERATOR-FILL rows: 0; STALE-DONOR-CODE-POINTER rows: 0. UNMEASURED 71 rows
(UNPAIRED-FILE-UNMEASURED: unit-only files with no donor twin, not relocations). 1084 files paired. The flagged rows are in
gate/gate-flagged.tsv.

Each flagged row, with its measured reason (plain and U alike):

| rows | class | file:line | reason |
|---|---|---|---|
| 338 + 338 | UNPAIRED-SOURCE | Reusable/YH03.v, U/Reusable/YH03.v | The script regenerates YH03 with only the definitions the unit's files use: donor 387 definitions, kept 50, dropped 337; no other .v file of the unit names a dropped definition. |
| 37 + 37 | UNPAIRED-SOURCE | R_memchr.v, U/R_memchr.v, donor lines 21-171 | Module R_memcmp removed: fuzz_uci links no memcmp. |
| 2 + 2 | UNPAIRED-SOURCE | FrameAPI.v:33, :62 | `ms_calloc B = (Some 0x1454c)` became `None`: fuzz_uci links no calloc. |
| 1 + 1, 1 + 1 | NON-ADDRESS-CHANGED | FrameAPI.v:14/15, Reusable/YL0k.v:183 (0xb8 -> 0xa0) | RELRO list length: 184 on decode, 160 on fuzz_uci, from the .init_array / .got section headers. |
| 2 + 2, 1 + 1 | NON-ADDRESS-CHANGED | Reusable/YN3f.v:283, :343; YN3i.v:302 | jal immediates of instruction words read from fuzz_uci's image (callee moved): 0x1fda74 -> 0x1fdbac, 0x1fd9ec -> 0x1fdb24, 0x24 -> 0x1ffa18; each is checked in the kernel by its `decode_any ... = Some (Jal 1 imm)` fact. |
| 1 + 1, 1 + 1 | DIFFERENT-SYMBOL, KIND-CHANGED | Reusable/YH03.v:87 src0_A_stdio_seek (0x16b6c -> 0x16224; U 0x1719c -> 0x16348), :85 src0_A_stdio_read (0x168c4 -> 0x0; U 0x16ef4 -> 0x0) | The donor's own two values were wrong (decode's 0x16b6c = __stdio_write+0x164, and decode links no __stdio_read); the relocation script sets src0_A_stdio_seek by name to __stdio_seek, which equals the image __stdout_FILE's seek slot, and src0_A_stdio_read to the measured read slot 0 of the image's FILE objects (no __stdio_read, no fopen). The tool's 'expected' value is the donor's wrong value moved by offset. Both cells are unused (no sink FILE is ever open). |

0 rows unexplained. Against e165063a0081 (FLAGGED 764) the only new rows are the two YH03 code cells above. Against cb0e067e3bae (FLAGGED 768) the only change is R_memchr.v's: the 5 + 5
rows that tool mis-paired after the removed module now pair (NON-ADDRESS-SAME), and 3 + 3 rows of the removed module's own
sentences (donor lines 89, 103) are UNPAIRED-SOURCE as the rest of that module.

Reusable/YH03.v (plain and U alike), the per-image definitions: of the 50 kept definitions per image the tool gives 47
SAME-SYMBOL, 3 SAME-CONTENT and 2 IDENT-NAME, and 0 DIFFERENT-SYMBOL; every kept `src0_D_<sym>` whose name is a symbol of
fuzz_uci's symtab (small_cnt_tab, med_cnt_tab, read_stage, ...) equals that symbol's value. fuzz_uci's files use no
src0_D_stderr, so that cell is not kept. The values were moved by k2_relocate.py (symbol + offset from the unit's symtab,
section bounds from its section headers); no alreloc version took part.

The 4 hex values the tool also classes NON-ADDRESS (k2/k2-conflicts.tsv) are the thread pointer of YN06 / YN06_cf, moved by
the builtin_tls + 0xc8 rule (k2/k2-values.tsv rows with `decimal table: builtin_tls+0xc8`).
