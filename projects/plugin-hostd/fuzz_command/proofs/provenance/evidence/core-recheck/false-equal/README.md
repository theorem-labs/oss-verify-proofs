# False-equal re-check of the port_addr_check rows of fuzz_command's relocated core

## What was checked

The value gate port_addr_check 3d2eee813cce gave an OK verdict to rows of three classes that the registry names as
FALSE-EQUAL classes:

1. SAME-CONTENT: a string value is accepted because the bytes agree, maybe in another string cut at a NUL.
2. INSN-SAME: a word is compared modulo its relocation fields (a jal by opcode and rd only), so a wrong jal target
   passes.
3. ROUND-CONSTANT-SAME: a page-multiple value is accepted because it is the same number on both sides.

Each of these rows of the three gate runs was checked again in another way:

| run | donor files | ported files | images |
|---|---|---|---|
| RA | cgif lib/A/A*.v | lib/A/A*.v | asan |
| RB | cgif lib/Y*.v | lib/B/Y*.v | asan-ubsan |
| RU | cgif lib/Y*.v | lib/Reusable/Y*.v | the image each file names (see below) |

Inputs: ported tree plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (proofs/plugin-hostd/fuzz_command/lib), donor tree c8557374ad2e
(proofs/cgif/cgif_file_fuzzer/lib), the gate's full.tsv of each run, and these images. The bytes come from the pin
and the symbol names come from the twin, which is the same link:

| role | pin sha256 | twin sha256 |
|---|---|---|
| fuzz_command.asan | c0661b96b5bd | 68db792d5fa7 |
| fuzz_command.asan-ubsan | bbe55d24d096 | 658cefbe806b |
| fuzz_command.plain | a20873dc7f0e | fbe3a48ad296 |
| cgif_file_fuzzer.asan | 7093581aab04 | 488e39500746 |
| cgif_file_fuzzer.asan-ubsan | 1c29845fe605 | ce511d541cda |
| cgif_file_fuzzer.plain | 19dedd1bc682 | 6ab540c43108 |

The plain pins are the pins in each unit's harness.yaml (fuzz_command plain a20873dc7f0e; cgif plain 19dedd1bc682).
The plain twins are the same link with symbols kept.

## Method

The check does not import or call the gate. It reads ELF bytes and symbols with pyelftools, decodes RV64 words
itself, and reads the proof files' own text.

* **SAME-CONTENT** (`feq_check.content_row`): for the donor value in the donor image and the ported value in ours,
  the check names the twin symbol that holds the value, if one exists. It also names the whole NUL-terminated string
  that holds the value, read back to the previous NUL, and the value's offset in that string. The row is OK when the
  symbol and offset are the same, or the whole string and offset are the same. The check also reads every memory
  cell that the line states (`zN (ANum A) V`, `litN A V`, `mkChunk A (CVal N (SLit V))`, `val_mem .. A N V`) in the
  image. A cell in .bss is written at run time, so the check names it but does not compare it. The check also lists
  where the image refers to the value: 8-aligned data words, and lui/auipc pairs that form it.
* **INSN-SAME** (`feq_check.insn_row`): the check decodes every word and finds the pc that the files give the word at,
  on each side. It tries these sources in order:
  1. a fetch fact on the line;
  2. the fetch of the word definition in the file;
  3. a fetch or concrete `code_at` table in a file that Requires this one;
  4. the file's own run of `W_<hex>` definitions, found once by its bytes in each image;
  5. a `clookup` / `*tbl_ok` / `step_*` lemma on the line;
  6. the fetch fact of the enclosing statement;
  7. the sibling fetch of a decode lemma (D_x → F_x).

  The fetch's segments name the image: `Asan.M` is asan; `AsanUbsan.M` is asan-ubsan; `src0segs` and `zsegs` are
  `Plain.M`, which is plain. At each pc, the check reads our image's 4 bytes and names the pc by symbol+offset on
  both sides. For a jal or branch, the check computes the target (pc + immediate). For an auipc, the target is pc +
  the high part + the low part of the next word that uses its rd. The check compares the donor target with ours by
  symbol+offset. A word that is fetched only over abstract segments (`segs` variables, smoke tests), or that is not
  an RV64G instruction (bv 32 constants 0 and 31), has no image pc. Such a word is OK only when it is bit-equal to
  the donor word and is not pc-relative. A `j .` (jal x0, 0) is also OK.
* **ROUND-CONSTANT-SAME** (`feq_roles.round_row`): the role of each value was read from its line by hand. Each role
  is one rule, and the rule measures the value in our image. A row that no rule covers is NOT-CHECKABLE.

## Results

| run | class | rows | checked | OK | FINDING | not checkable |
|---|---|---|---|---|---|---|
| RA | SAME-CONTENT | 14 | 14 | 14 | 0 | 0 |
| RA | INSN-SAME | 1296 | 1296 | 1296 | 0 | 0 |
| RA | ROUND-CONSTANT-SAME | 54 | 54 | 54 | 0 | 0 |
| RB | SAME-CONTENT | 14 | 14 | 14 | 0 | 0 |
| RB | INSN-SAME | 1296 | 1296 | 1296 | 0 | 0 |
| RB | ROUND-CONSTANT-SAME | 53 | 53 | 53 | 0 | 0 |
| RU | SAME-CONTENT | 0 | 0 | 0 | 0 | 0 |
| RU | INSN-SAME | 1124 | 1124 | 1124 | 0 | 0 |
| RU | ROUND-CONSTANT-SAME | 16 | 16 | 16 | 0 | 0 |

**FINDINGs: none.**

### SAME-CONTENT details (RA 14, RB 14)

* Every value is in .rodata of a merged string section. No twin symbol covers it.
* Each value is the same whole string at the same offset on both sides: "SizeClassAllocator"+0,
  "LargeMmapAllocator"+0, ".str"+0, and "memory at address %p"+8, +16 and +20.
* Every cell that the lines state outside .bss reads, in our image, the value that the line states.
* The .bss cells of lib/A/AF0m.v:126,132 (B: YF0m) are `__asan::instance`+0x10 and +0x60 on both sides. Their values
  are the ones that our image keeps in `__sanitizer::PrimaryAllocatorName` and `SecondaryAllocatorName`.

### INSN-SAME details

* **RA and RB**: all 1296 rows have an image pc: 1291 from fetch facts, 4 from `clookup tbl_icpt`, and 1 from
  `tfibmusl_tbl_ok`.
  * Our image word at the pc is the stated word in 1296 of 1296 rows.
  * The donor pc is at the same symbol+offset in every row.
  * The check decoded 187 jal / j / branch targets (164 branch, 19 j, 4 jal). All 187 have the same symbol+offset as
    the donor target.
  * The 4 jal words that differ from the donor's are lib/A/AE3e.v:282,284,342,344 (B: YE3e.v:283,285,343,345). All
    four reach `__syscall_ret`+0x0, which is also the donor's target.
* **RU**: 1015 of the 1124 rows have an image pc.
  * The sources are: 827 fetch facts (811 over the plain image (src0segs), and 16 PW0..PW7 words that lib/A/AFk3.v,
    AB1i.v and their B twins fetch in both asan images); 100 `code_at` tables of lib/A/AB14, AB15, AB16 and AE20 and
    their B twins; 87 rows by locating the file's own word run; and 1 `step_lbu` lemma. For words that the asan
    files and the asan-ubsan files both use, the check measured both images.
  * Our image word at the pc is the stated word in every row. The pc is at the donor's symbol+offset in every row.
  * The check decoded 52 jal / branch targets, and all 52 are equal by symbol+offset. This includes
    lib/Reusable/YN3i.v:302: the ported word 0xce8ff0ef differs from the donor 0x024000ef, and both reach
    `memchr`+0x0 in their plain images.
  * 109 rows have no image pc:
    * 80 are words fetched only over abstract segments (lib/Reusable/YK1a.v smoke tests, YK11, YK1e, YK1f, YFk4,
      YK0a over `segs`).
    * 17 are bv 32 constants that are not instructions: 0 and 31 used as masks and zeros.
    * 10 are `ret` (0x00008067) in lemmas with a variable pc.
    * 2 are `j .` (0x6f).

    Each of these is bit-equal to the donor word.

### ROUND-CONSTANT-SAME roles and measurements

| value | lines | role | measured in our image |
|---|---|---|---|
| 0x7fffa000 | lib/A/AB01.v (generated), AB03.v (generated), AD1f.v, AFjy.v; B twins | shadow of the image's lowest load address | lowest PT_LOAD 0x10000. Shadow offset 0x7fff8000 (`__asan::FindDynamicShadowStart`+0xc: lui x10, 0x7fff8). (0x10000>>3)+0x7fff8000 = 0x7fffa000. In 70 of the 74 rows, the line also states the span 0xbec00 or the end 0x800b8c00, and both are our own (top 0x606000). No line states the donor span 0xbd600. |
| 0x200000 | lib/A/AE30.v:1393, AE6k.v:1387, lib/B/YE30.v:1394 | loose bound on addr+len of the icpt_rodata entries | the largest entry end is 0xb1db8 (A) / 0xb1938 (B), at `__asan::kHighMemEnd`. Both are below 0x200000. |
| 0x100000 | lib/A/AF0m.v:136, AFgi.v:108, AFgm.v:96, AFgn.v:71; B twins | a size in a run-time field | the cell is `__asan::instance`+0x328 in .bss on both sides; the field beside it holds 0x10000000. Read as an address, the value would point to different places in the two images, so it is not an address. |
| 0x100000 | lib/A/AFem.v:194, lib/B/YFem.v:195 (`bkt < 1048576`) | bound of a hash-bucket index | the twin symtab names `StackDepotBase<StackDepotNode, 1, 20>`, so the table size is 2^20 |
| 0x100000 | lib/Reusable/YG0f.v:33 (kNodesBlockSize) | StackDepot node block size | `TwoLevelMap<StackDepotNode,32768,65536>::Create`+0x80: lui x11, 0x100, at the same offset in both images |
| 0x40000 | lib/A/AFk8.v, AFk9.v, AFkn.v; B twins | the register value that the R3_* pins put in x19/x18 | `SizeClassAllocator64::PopulateFreeArray`+0xb0: lui x19, 0x40, and `EnsureFreeArraySpace`+0x28: lui x13, 0x40. These are at the same offsets in the donor. Where a line has a runto pc (0x39630, 0x372c0; B 0x3967c, 0x3730c), that pc is in these functions. |
| 0x32000 | lib/Reusable/YI5c.v:38, YN0c.v:61,65, YN0d.v:99 | size of the plain image's read-write region | fuzz_command.plain: last PT_LOAD [0x23a80, 0x54cb8), page range [0x23000, 0x55000), size 0x32000 |
| 0x60000 | lib/Reusable/YL0k.v:151,154,163 | loose bound above the plain image | the highest PT_LOAD end is 0x54cb8, which is below 0x60000 |
| 0x20000 | lib/Reusable/YK1a.v:901,907,911,917 | a register value in smoke tests over abstract segments | no image quantity |
| 0x142000, 0x52f000 | lib/Reusable/YK09.v:2751,2762 | rw_lo / rw_len of the atables ASAN / BOTH (img_hi 0x671000) | not a table of any image of this unit (tops 0x606000 / 0x606000 / 0x55000). A by-use grep over the unit found no use of ASAN, BOTH, asan_init or both_init outside YK09.v, so no proof reads the value. |

## Observations (not FINDINGs)

1. **RU used the asan-ubsan image for rows of the plain image.** In RU, 827 INSN rows are fetches over `src0segs`.
   `src0segs` is `zsegs` (lib/Reusable/YH00.v:6), and `zsegs` is `Plain.M.loaded_segments` (lib/ZImage.v). The
   RU gate run read these rows against asan-ubsan. This check measured them in the plain pins (ours a20873dc7f0e,
   donor 19dedd1bc682), and all of them agree.
2. **lib/Reusable/YK09.v:2749-2770 holds an unused foreign table.** The atables ASAN and BOTH, and asan_init and
   both_init, describe an image with img_hi 0x671000. That image is none of this unit's, and no other file uses
   these definitions. The donor carries the same text. No claim depends on them.
3. **87 word definitions in lib/Reusable/YB1o.v are used by no file.** These are W_c96ec..W_c9844. The check found
   their bytes once in each asan image, at `__sanitizer::Sort<ioctl_desc, ...>`+0, the same function as in the
   donor.

## Controls (controls.txt)

`feq_controls.py` plants one line in an in-memory copy of a ported file. The files on disk are not changed. It
also runs the unplanted rows first.

* **N1, N2, N3** (unplanted: lib/A/AE3e.v:282, lib/A/AB1u.v:154, lib/A/AFih.v:67): OK.
* **P1**: lib/A/AE3e.v:282, jal x1 0xdbdfa0ef → 0x290040ef. The opcode and rd are the same, so the gate's coarse
  compare of a jal sees the same word. The target is memcpy+0x0. Result: FINDING. Our image word at 0x9a8ac is not
  the stated word, and the target differs: donor `__syscall_ret`+0x0, ours memcpy+0x0.
* **P2**: lib/A/AB1u.v:154, word definition j 0x3500006f → 0x3940006f. The target is memset+0x0. Result: FINDING.
  The image word differs, and the target differs: donor memcpy+0x3c0, ours memset+0x0.
* **P3**: lib/A/AFih.v:67. The NUL of "memory at address %p" (+20, 0x1cf36) is replaced by 0x15515, the NUL of
  another string. The bytes from the value to its NUL are equal (both empty), and the 1-byte cell that the line
  states reads 0 at both addresses. Result: flagged (the holder differs): ' %p %p'+6 against
  'memory at address %p'+20.

## Files

* `feq_lib.py`: image, symbol, string and RV64 decoder helpers, and the proof-text parser.
* `feq_check.py`: the three class checks and the driver, which writes rows.tsv.
* `feq_roles.py`: the ROUND-CONSTANT role rules and their measurements.
* `feq_controls.py`: the planted controls.
* `run.sh BASE`: a cold re-run. BASE is the copy root with tree/, img/, runs/ and out/false-equal/img/.
* `img/`: the plain pins and twins used here (shas above).
* `rows.tsv`: one row per gate row. The columns are run, verdict, src, dst, sentence, src_value, dst_value, measured,
  status, finding_kind, new_value and read_by. finding_kind, new_value and read_by are `-` in every row because
  there is no FINDING.
* `controls.txt`: the controls, as listed above.

## Reproduction

`run.sh BASE` was run from a cold start on a build machine with the same input copies. It exited 0 and wrote
`counts.txt`. Its outputs are byte-equal to the files here: rows.tsv sha256 e2cb4bd0e8e5 and controls.txt
49b47595e922. The script sha256s are feq_lib.py e90c3dedaa5d, feq_check.py 2d71eea15538, feq_roles.py
37b42a1a9052 and feq_controls.py e60b4da335fa. The shipped feq_check.py (f23a0fd2e6e3) differs from the copy that ran
only in its work directory's name, written in 4 lines (519, 530, 531, 539: a docstring, the two plain-image paths and
the --base help text) as this part's directory name, false-equal; the other three are the copies that ran.
