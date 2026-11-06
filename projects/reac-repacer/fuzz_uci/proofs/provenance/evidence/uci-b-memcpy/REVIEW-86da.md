CONFIRM: the UCI-B-MEMCPY donor compare, re-run on cmpkit 86da41d3ef68, is settled. The by-name closure is 785 members = 170 EQUAL + 515 EQUAL-mod-pcrel + 100 DIFFERENT-target; the 100 split into 74 `lui-in-section` rows (luiuse: 46 NUMBER + 28 NUMBER+HAND, 0 ADDRESS) and 76 other open words (settle.out: 67 CSTRANY + 6 BYTE64 + 3 REL4, all EQUAL); basecalc on the lui values that reach a base gives 22 IMAGE EQUAL + 182 RUNTIME, 0 ABS / JOIN / NOT-MEASURED; the 35 lui-const acceptances are settled the same way. A reviewer that made none of the settlements re-derived every one of these from the two images and agrees. The defects found are latent tool gaps and three imprecise hand reasons; none changes a row.

# Fresh review: the UCI-B-MEMCPY donor compare on cmpkit 86da41d3ef68

All measurements were taken from the two images with the reviewer's own tools; the kit's files and outputs were reproduced and used only as the list of claims. Read-only, no proof work. Every reproduction ran without writing byte-code into the kit.

## Images (role, sha256)
- X: uci image B, unstripped twin `8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16`.
- Y: fuzz_grant image B, unstripped twin `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417`.
Both are unstripped RV64GC static binaries (musl + compiler-rt asan/ubsan). The kit (nine members) verifies `sha256sum -c SHA256SUMS`.

## Reproduced byte-for-byte
closure-memcpy.out, jtcheck-others.out, settle.out, luiuse.out, luiuse_control.out, basecalc.out, basecalc_control.out, control-notable.out, luiconst-rows.txt, luiuse-luiconst.out, basecalc-luiconst.out and handcheck.out were each re-run and match the record. control-notable.out = settle.py with table matching switched off: the three REL4 targets go OPEN, exit 1.

## Method
Own ELF reader (file bytes of a PT_LOAD only) and capstone; own RV64 decoder and path walk; a reaching-definition pass over the kit's own control-flow successors; and the authors' `cstr_use` and `walk` loaded and re-run unchanged. hand.tsv reasons were checked against the bytes and against Linux, compiler-rt and musl sources.

## 1. Closure, coverage, ambiscan
- The closure header is 785 = EQUAL 170 + EQUAL-mod-pcrel 515 + other 100. The 100 DIFFERENT-target members are exactly others.txt, and jtcheck was run on exactly those.
- jtcheck leaves 150 words open (76 DIFF, 74 UNMEASURED). The per-function header counts equal the listed lines, and the header addresses equal the symbol table. The 74 `lui-in-section` DIFF words are exactly luiuse's rows; the other 76 are exactly settle.out's rows — nothing open is missing, nothing extra.
- ambiscan reports 0 ambiguous by-name hits. The twin-vs-pin check (drvcmp) is unchanged from the superseded kit; the twin SHAs match the record.

## 2. settle.py and the three REL4 rows
settle.py now bounds a 4-byte jump/word table with a dataflow (`bound_const`: on every path from the entry the last writer of the bound register is `addi rK, zero, K`, one K) and accepts `slli rI, rJ, 2` with a separate index register. For each REL4 row, on both images: the bound register has exactly one definition on every path (`addi rK,zero,K`); the index is not rewritten between the bound and the shift/add; the indirect jump is not reachable from the entry without the bound branch; and every table entry resolves to an in-function, 4-aligned offset, equal on X and Y.

| row | bound | entries | X==Y |
|---|---|---|---|
| VSNPrintf +0x1c0 | `addi s0,zero,0x20` (32) | 33 | yes |
| parseFDEInstructions +0x140 | `addi s1,zero,0x2f` (47) | 48 | yes |
| parseCIE +0x23c | `addi s5,zero,0x2e` (46) | 47 | yes |

jtcheck refuses parseFDEInstructions by its table-shape heuristic ("the bound is reloaded from the stack"); in these two images the bound is a single constant, which the dataflow settles, so settle.py's REL4 is correct here.

## 3. settle.out's 76 rows
On both images: every forming word resolves to the row's address; the 67 CSTRANY rows pass the use gate and an independent trace (identical results) and are byte-equal through the first NUL (all the empty string); the 6 BYTE64 and 3 REL4 rows are refused by the gate exactly where the trace finds the first non-string use, and are settled by BYTE64 / REL4. The two functions new since the superseded kit pass the empty string to string helpers (`internal_strncmp` / `internal_strcmp`; `internal_strncpy`). Accepting the empty string is sound because every consumer reads a NUL-terminated string.

## 4. luiuse: the lui values as numbers
luiuse gives 46 NUMBER + 28 NUMBER+HAND, 0 ADDRESS, X==Y on every row. Re-running the author's walk gives identical results. At each point a value becomes MIXED (lui value combined with a non-constant), the reaching definitions of the other operand show it is either a run-time pointer (`this` / a parameter / a pc-relative global / a loaded pointer) with the lui value as a field offset, or a number added to a number; the lui value is never a base by itself. The MIXED rule does not prove this on its own — the base-use question is what basecalc answers.

## 5. basecalc: the lui values that reach a base
basecalc reports 204 base sites: 22 IMAGE EQUAL + 182 RUNTIME, 0 ABS / JOIN / NOT-MEASURED / DIFFER; its four planted controls pass.

- **The 22 IMAGE sites**, recomputed independently (pc-relative base + the lui value + the access immediate), land in the same symbol+offset on both images, inside the object: `internal_alloc_placeholder` (size 0x81040) at +0x40040 / +0x40048 / +0x40dc0 / +0x40dc8 / +0x81008 / +0x81010, and `theDepot` (size 0x440010) at +0x400008 / +0x400010.
- **The 182 RUNTIME sites** (95 distinct function/word/access): an independent reaching-definition analysis of every base register shows it is a run-time value — a parameter / `this`, a load from a run-time pointer, an atomic result, or a masked pointer — never a pc-relative image address and never a constant-pointer-cell load. So the lui value is a field offset on a genuine run-time pointer, identical bytes and identical code on both images.
- **Soundness of the value algebra and pre_state.** Planted probes show the walk fails closed: the no-return judgement is conservative; an image address reached by more than one non-lui arithmetic step, or through a `.data` pointer cell, or through a non-stack store-and-reload, is reported RUNTIME (or not followed) rather than IMAGE — never the other way. basecalc does not itself prove that a RUNTIME base is a run-time pointer (only that its non-lui part is not an image constant it recognises); that property was established here by checking all 182 bases.

## 6. hand reasons
The hand file has 49 reasons; handcheck reports 0 failures over luiuse's and the lui-const traces (115 uses). All 47 original reasons were checked against the bytes and the kernel / compiler-rt / musl sources: 44 are exactly right, 3 have imprecise wording whose conclusion still holds, none hides an address use, and no chain lands a tracked register on a `%s` conversion. The two reasons for the lui-const rows (gettid, futex: the extra argument register is not read by the syscall) are correct. The three imprecise reasons: two Printf/Report rows name the dead store at +0x28 instead of the real va_list hand-off at +0x30/+0x34 (the tracked slots still feed only numeric conversions); one AsanDeactivate row gives a wrong clause about a 4-byte store, whose real point (the value is two u16 redzone fields written as data, not a base) holds.

## 7. lui-const rows
The 35 `lui-const` acceptances of the closure (33 functions) are all turned into rows (complete). luiuse gives 17 NUMBER + 18 NUMBER+HAND, 0 ADDRESS; basecalc gives 4 base sites, all RUNTIME (a locale pointer). Both tools follow the logical operations the kit's rule-8 scan leaves as "constant" (`and` / `or` / `xor` / `andi` / `ori` / `xori`): luiuse propagates the value's tag through them, basecalc keeps following the value (as a run-time value) through them. The acceptance values are 26 of 0xfffff and 9 other constants, each identical on X and Y.

## Defects (latent; none changes a row or a verdict)
- **D1 (basecalc).** An image address reached by more than one non-lui arithmetic step, or through a `.data` pointer cell, or stored to a non-stack field and reloaded, is classed RUNTIME (or not followed) rather than IMAGE; the RUNTIME verdict then rests on "a run-time pointer + the offset", which the tool asserts but does not prove. It holds on these rows only because every RUNTIME base was checked independently. Fix: settle a RUNTIME base whose non-lui part can be an image address by hand, or prove that part is a run-time pointer.
- **D2 (luiuse).** The MIXED rule does not prove the lui value is an offset and not a base; basecalc answers that for the base-use question, so the two together settle the rows.
- **Wording.** Three hand reasons (section 6) name a dead store or a wrong clause; the conclusions hold. The lui-const values are not all the same constant, contrary to one note.
