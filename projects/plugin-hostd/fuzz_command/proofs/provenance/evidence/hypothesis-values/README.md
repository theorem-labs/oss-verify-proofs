# Hypothesis-position values of plugin-hostd/fuzz_command that differ from their donor

This slice records, for plugin-hostd/fuzz_command at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record), every hypothesis-position numeric value of a
relocated file that differs from its paired donor line or has no donor line, with the bound derived from this unit's
own definitions and from its pinned images. A green build does not check a value in a hypothesis position: a value that
is too narrow compiles and states a false fact. So each value below is derived, not taken from the build.

## Scope and pairing

- Tree: `proofs/plugin-hostd/fuzz_command/lib/{A,B,Reusable,U}/**/*.v` at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (4212 files).
- Hypothesis positions: every `mkAF lo hi al` term (atom ranges, also inside proofs), and every `Hypothesis`,
  `Hypotheses`, `Variable`, `Variables` and `Context` sentence that contains a numeral (comments removed). 15107 items.
- Each file is paired through the relocating runs' own stage map, not by path name: the core-recheck slice's
  `d9e0/files.tsv` (port_core runs A1 and A2 over cgif_file_fuzzer lib/A) and `inventory.tsv` (the route of every file
  of lib/A, lib/B, lib/Reusable, lib/A/Rt and lib/B/Rt), at the same bytes as the shipped core-recheck/d9e0/files.tsv (sha256 497cbf8baf06) and core-recheck/inventory.tsv (sha256 f0de038c6c2a).
  - A core: a lib/A file of run A1 or A2 pairs with `proofs/cgif/cgif_file_fuzzer/lib/A/` of the same name at
    c8557374ad2e; a lib/Reusable file whose route is a port_core run-1 copy or a copied donor model file pairs with the
    cgif file of the same name at the cgif lib root.
  - B core: a lib/B file (made from our lib/A file by the A->B relay, or the B start-up set) pairs with cgif's own B
    twin `lib/Yxx.v` and with our `lib/A/Axx.v`. A value is donor-identical only when it equals the cgif B twin's;
    equality with our A twin alone does not clear it. The values of both are in the donor value column.
  - Runtime relocations: a lib/A/Rt or lib/B/Rt file whose route is "runtime relocation from a donor file" pairs with
    the donor file its header names. The B twins of lib/A/Rt files pair with that lib/A/Rt file.
  - Files in neither map pair with the released cgif_file_fuzzer tree by base name; else they are the unit's own and
    are counted, not derived.
- Missing mapping files: the donor named for lib/{A,B}/Rt/RtStrcmp*.v (proofs/libreac/fuzz_grant/lib/A/Rt/Strcmp*.v,
  10 files) and for lib/B/Rt/RtSMxA.v (proofs/omx-clap-core/fuzz_preset/lib/A/FCxA.v) are at neither c8557374ad2e nor
  781f46bc05cd; the best available copies (proofs/libreac/fuzz_ctrl/lib/{A,B}/Rt/, proofs/omx-clap-core/fuzz_state/lib/B/)
  are used. files.tsv lists lib/A/AF0r.v and lib/A/AF0s.v, which are not in the tree at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record).
- An item is donor-identical when the same normalized text (module paths ignored) is in the paired donor file. Every
  donor-identical item that holds an address (234 address uses) was checked on the pins: each address is the same
  symbol plus the same offset in our pin as in the donor image (the 24 uses in files paired with libreac/fuzz_ctrl are
  the ASan shadow-layout constants).

## Counts

| map | files listed | files paired | items | identical | differing | derived |
|---|---|---|---|---|---|---|
| A core: lib/A (port_core runs A1, A2) | 391 | 389 | 3435 | 3086 | 349 | 349 |
| A core: lib/Reusable (run-1 copies, donor model files) | 401 | 401 | 1022 | 1005 | 17 | 17 |
| B core: lib/B (cgif B twin + our A twin) | 390 | 390 | 3437 | 3087 | 350 | 350 |
| runtime relocations (donor named in header) | 37 | 36 | 429 | 345 | 84 | 84 |
| runtime B twins of lib/A/Rt files | 22 (+1, see below) | 23 | 129 | 129 | 0 | 0 |
| neither map, paired to the cgif tree by base name | - | 264 | 841 | 824 | 17 | 17 |
| neither map, the unit's own (counted, not derived) | - | 2709 | 5814 | - | - | - |

lib/B/Rt/MemchrChk.v is listed as a runtime relocation; its header names our lib/A/Rt/MemchrChk.v, so it is counted
with the B twins. 2973 files are in neither map: 373 inventoried (2 lib/A files that no port_core run wrote, 160
lib/Reusable files with no donor file of that name, 211 runtime proofs written for this unit) and 2600 not inventoried
(lib/U, lib/*/Prog, lib/*/Bz, Spec, Strw, Ox and the like).

The 817 derived rows by kind: Hypothesis 424, Hypotheses 104, Variables 220, mkAF 69. By change: numerals
changed 342, no donor line 238, same numerals with a changed identifier or structure 237.

| class | rows |
|---|---|
| TRUE-EXACT | 577 |
| TRUE-WIDER | 240 |
| FALSE-NARROW | 0 |
| UNDERIVABLE | 0 |

## Method

Each row of `values.tsv` gives the file and line at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record), the sentence or `(atom, mkAF ...)` text, the kind,
the paired donor file:line with the donor numerals that changed (and, for lib/B, our A twin's numerals), our numerals,
the derived bound, the derivation with the map the file was paired through and the file:line of every definition it
uses (paths relative to `proofs/plugin-hostd/fuzz_command/`), and the class: TRUE-EXACT (the value equals the derived
bound or fact), TRUE-WIDER (true but weaker than the derived bound), FALSE-NARROW (narrower than the derived bound: a
false fact), UNDERIVABLE (the derivation needs a fact that is not available).

- Addresses are derived from the pinned images, read with pyelftools: fuzz_command asan sha256 c0661b96... (lib/A),
  asan-ubsan bbe55d24... (lib/B), plain a20873dc... (lib/Reusable, whose `src0segs` is the Plain image) and ubsan
  941fc716... (lib/U, the Ubsan image). Symbols come from the pins' debug files. A relocated address is TRUE-EXACT
  when it is the same symbol plus the same offset as the donor value in the donor image (cgif_file_fuzzer asan
  7093581a..., asan-ubsan 1c29845f..., plain 19dedd1b...; symbols from their unstripped twins, whose code and data
  segments are byte-identical), and the object has the same size. For code addresses the function was also compared
  instruction by instruction: every differing instruction is an auipc/jal or an instruction that completes an auipc
  address pair. Return addresses were checked to follow a `jal ra` to the same callee.
- Format-string addresses were checked by reading the string from the pin's .rodata; GOT addresses by reading the
  8-byte GOT word from the pin; image extents from the pins' PT_LOAD segments; the musl constant window from the
  pin's disassembly.
- Bounds (depot ids and frames, compact pointer, stack windows, trace length, string-function lengths) are derived from
  the definitions and program call sites cited in each row. The aTOT row follows the derivation already recorded for
  lib/A/AFek.v:34 and lib/B/YFek.v:35, and adds the tighter bound that the depot invariant gives.
- Section premises that select one control-flow case of a wrapper walk (a register equal to 0 or 1) are classified
  against the case that the file's header names.
