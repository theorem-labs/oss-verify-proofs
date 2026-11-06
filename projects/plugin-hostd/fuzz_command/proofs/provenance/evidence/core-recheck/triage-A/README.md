# Measured triage of gate run RA's open rows (image A, relocated files)

Unit plugin-hostd/fuzz_command. Gate: port_addr_check 3d2eee813cce, run RA (cgif_file_fuzzer lib/A -> fuzz_command
lib/A, key A). Input: the 807 rows that the first mechanical pass left OPEN in relocated (not generated) files
(`RA.open.tsv`, sha256 da9b0a1af52e): 639 UNPAIRED-PORTED, 152 NON-ADDRESS-CHANGED, 6 DIFFERENT-SYMBOL,
6 KIND-CHANGED, 3 UNRESOLVED, 1 GEOMETRY-CHANGED.

Images (pin = bytes and headers, twin = symbol table and DWARF; one link):

| role | sha256 |
|---|---|
| fuzz_command.asan (pin) | c0661b96b5bd |
| fuzz_command.asan twin | 68db792d5fa7 |
| cgif_file_fuzzer.asan (pin) | 7093581aab04 |
| cgif_file_fuzzer.asan twin | 488e39500746 |

Trees: ours = the series head plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record); donor = cgif_file_fuzzer at c8557374ad2e.

## Result

807 rows, 0 without a reason: 805 OK, 2 FINDING (code), 0 comment findings.

| reason | rows | what the rule measures |
|---|---|---|
| TRACE-OBJ | 268 | the caller's trace object: 1 <= length <= 30, 8-aligned, buffer at p + 16, 8-byte frames, extent 256 = 16 + 8 * 30. Measured against lib/A/Rt/RtDDefs.v:82-86 astrace_at and :105-113 premises, lib/Reusable/YG00.v:37 kUnwindMax |
| REG-SP | 127 | register / atom 2 = sp (RISC-V psABI; lib/Reusable/YI04.v:81 + YP01.v:42 make atom r the entry value of register r) |
| XREG-WIDTH | 106 | bvmap 5 / bv 5: 32 integer registers (ELF header: ELFCLASS64, EM_RISCV) |
| REG-A1 | 59 | register / atom 11 = a1 = the trace object pointer: twin symtab has PC_asan_malloc 0x34528 = asan_malloc(unsigned long, BufferedStackTrace*), 2nd argument; RtDDefs.v:105 |
| WIDTH | 33 | 2 ^ 64, Z_to_bv 64, byte range 256, 8 / 4-byte reads, 8-byte words, shadow granule 8 and 7 |
| GEN-AVIS | 22 | AVIS14's (epg v, len) pairs are visible zones (a_vis) of the generated start-up certificate lib/A/AB01.v |
| TRACE-REGION | 21 | AFhy.v R_bst and the region checks at atom 11: base atom 11, [0, 16) header, chunks at 0 / 8, extent 256 |
| DEPOT-BOUND | 18 | depot ids <= DEPOT_CAP + 1 = 20481 (+1 = 20482), TOT <= 31 * (DEPOT_CAP + 2) + 32 = 634974 (lib/Reusable/YG01.v:151; the donor's 127070 is the same formula with 4096) |
| GI-IVS | 16 | GI_IVS = lib/A/Prog/CmdGlob.v GI_cmdA runs, each checked against the twin's DWARF field extents (recorder.ncalls, answer..nreplies, reply..reply_size; rec_call fn+nargs; g_quitting int); gi_byte_range = [.bss start, image top); not_inFPC = [g_rec, g_quitting + 4) |
| OWNED-EXTENT | 14 | C object 256, D object 4096 (lib/Reusable/YG0f.v:301-302), offset lower bound 0, minimum cell width 1 (same text as donor lib/A/AD1g.v:1248) |
| REGION-HEAD | 14 | skipn 3 REG0* = the 3 stack regions at the head of REG0 / REG0K (AFhy.v:94, AFi1.v); firstn 43 = donor 41 + 2 (donor head had 1 region) |
| FCSR-FRM | 12 | frm = fcsr bits 5..7, mask 7, RNE = 0 |
| GEN-MAPIDX | 9 | head 4 maps, 16 fixed maps, eSB / eNB at indices 2 / 3: the generated certificate's 50 states all have 4 head + 0..2 musl + 12 tail maps |
| GEN-HEAD | 7 | TFIB_HEAD4, eDM = epg 1639, dDM length = the certificate's first four maps |
| ITAB-RANGES | 7 | startup_plan_tfib_ranges counts: IT0 = mk_itab_ranges is sound for any range (AB1m.v:27-29, Qed); the range must lie in .text (BOUND) |
| ZSHADOW-RUN | 7 | zero-shadow run ends from the image's 180 asan_globals descriptors (lowest .rodata global 0x210a0; largest p + n with its 8-aligned shadow hull inside = 0x21080; last .bss redzone end 0x5e3c80; first .bss global's redzone start 0x5e3b00); AD1o.v:86 p lower bound in [0x5e3c80, STDOUT_BUFA 0x604ca8] (BOUND) |
| FREE-ARRAY | 5 | kFreeArrayOffset 3758096384 (lib/Reusable/YG00.v:14); CPv < kFreeArrayOffset / 16 <= 2 ^ 28 |
| STACK-MALLOC-KEY | 5 | pc_stack_malloc keys = N of the __asan_stack_malloc_N symbol at each arm's address (twin symtab) |
| CMDB-CELL | 4 | __asan_shadow_memory_dynamic_address, __asan_option_detect_stack_use_after_return (symtab); as_junk = donor's __asan::instance + 0x2b0, 40 bytes, at the same offset of ours (same object size) |
| GOT-WORD | 4 | the .got words that hold those two symbols (GOT word contents read from the pin); the program GOT run [0xa7068, 0xa7088) = g_rec .. g_quitting words |
| DRV-IVS | 4 | driver statics end = oft_aligned_copy.empty end = g_rec start; errno cell = TFIB_TP + imm of __errno_location (addi a0, tp, 0; addi a0, a0, -164) = 0x5e44f4 |
| MU-CELL | 4 | DtorExit's cell = __asan::mu_for_globals 0xae970 (symtab), an 8-byte zero cell `z8` in lib/A/AF0m.v Tfib_const |
| SINK-UNREAD | 4 | A_RWA / A_WB / A_TRAILER / A_PATH := 0: the donor strings are not in our .rodata, and a by-use grep over lib/A finds no reader of ak_path / ak_mode / ak_rwa / ak_trailer (the chain uses aclosed_stdio_env) |
| STARTUP-STACK | 4 | R_hdr true = [sp, sp + 24), atom 0 = the stack base (lib/Reusable/YP08.v:267-270, lib/A/AD1y.v:41-44) |
| TOPF | 10 | page 4096 (PT_LOAD p_align), 4095, TOPF_range 3935 = 4095 - 160; TOPF's own slack 160 and TOPF_eq's 3920 are BOUND slots (any slack in [0, 4095]; TOPF_eq needs <= 3935) |
| FREG-FA0 | 4 | bv 5 float register index (arch has F and D), fa0 = f10 |
| IMG-SHADOW | 3 | kn_vis (ELit 0) 0x7fffa000 0xbec00 = shadow of the image [0x10000, 0x606000) |
| GEN-KRANGE | 3 | KRange (EVar 1639) 1 34359736319 is a kentry of the certificate |
| ASAN-MALLOC-RET | 2 | 0x34564 = the first `ret` word (0x00008067) of asan_malloc |
| EV-BUDGET | 2 | EV_LIB 2900 in [measured worst case 2372 (lib/A/ACfn.v:27-28), EV_MAX 11776] (BOUND; a model budget, not an image count) |
| JAL-DECODE | 2 | Jal offsets = J-immediate of the image word at the F_ fact's pc (0x9a8ac, 0x9a934), target __syscall_ret |
| SMV-LOWER-BOUND | 2 | FINDING, see below |
| AMAP-PREFIX | 1 | 6144 = the aMAP region extent of the same file (AFjo.v:637; user block at map + 6144, AFjz.v:828) |
| GEN-EAGER | 1 | a_eager bound = max a_eager over the certificate's 50 states (16519168; the donor certificate's max 16515072) |
| PHDR | 1 | ph_addr_z = PT_PHDR p_vaddr 0x10040 |
| RUNTO-SENTINEL | 1 | runto 0x7ffffff0 = the unit's run-to-the-end sentinel (AFi0.v:48), in no PT_LOAD; MK_NR has no user in lib/A |
| TEXT-WORDS | 1 | TFIB_TEXT_N = .text size / 4 = 115951 |

By gate verdict: UNPAIRED-PORTED 639 (all OK); NON-ADDRESS-CHANGED 152 (all OK); DIFFERENT-SYMBOL 6 (ZSHADOW-RUN, OK);
KIND-CHANGED 6 (SINK-UNREAD 4, RUNTO-SENTINEL 1, ZSHADOW-RUN 1, OK); UNRESOLVED 3 (PHDR OK, SMV-LOWER-BOUND 2 FINDING);
GEOMETRY-CHANGED 1 (DEPOT-BOUND, OK; the gate read 634974 as a donor segment size).

Every UNPAIRED-PORTED row also carries the stale-donor test: no row's value is the donor image's address of a symbol
that our image has elsewhere.

## FINDINGs (code; listed in code-findings.tsv)

| file:line | old | new | read | measurement |
|---|---|---|---|---|
| lib/A/AFjm.v:428 (map_zoneN) | 2148223601 | 2148236288 | proofs only (Local Abbreviation in 21 walk files, first lib/A/AFjh.v:152) | map_zoneN restates map_zone (AFjm.v:419) kLowShadowBeg + TFIB_IMG_END / 8 <= SMv: 0x7fff7000 (Reusable/YG0f.v:21) + 0x606000 / 8 = 0x800b7c00. The old value is the donor's 0x800b33b0 + 0xb608 / 8: a bound moved as a shadow address (class B). |
| lib/A/AFk1.v:696 (sm_bounds) | 2148223601 | 2148236288 | proofs only (first lib/A/AFk0.v:566) | restates map_zoneN; same measurement |

Both are harmless: the old number is a true weaker bound and both lemmas are closed by Qed, so no claim or release
check changes. Reported to the slice owner under the stop rule (proofs read the value).

## Known-answer controls (controls.tsv)

Each OK row is judged again by its own rule with value + 4 and with the donor's value; a BOUND slot also 4 beyond its
measured bound; each FINDING row with its measured new value.

- value + 4: refused on 793 of the 805 OK rows; accepted on the 12 BOUND slots (EV-BUDGET 2, ITAB-RANGES 7, TOPF 2,
  ZSHADOW-RUN 1), by design, since it lies inside the measured interval; 4 beyond the bound is refused on all 12.
- Donor value: refused on 180 rows; accepted on 7 (the ITAB-RANGES counts: any count inside .text is sound); equal to
  ours on 6 (not a perturbation: e.g. PT_PHDR 0x10040, the 8-byte zero cell, the min cell width 1); no donor value on
  612 rows (model constants in sentences the port wrote, where the donor has no such slot).
- FINDING rows: the measured new value 2148236288 is accepted on both.
- Stale-donor test: the donor's address of the symbol a row's value names (planted) is called STALE on all 5 rows
  where that symbol exists in both images; the donor values of the 4 address slots that are exact donor symbol
  starts are called STALE; the 5 donor values that are not symbol starts (GOT words, an image extent, an object
  interior) are not called stale by this symbol test, and the row's own rule refuses each of them.

## What was run

```
python3 triage.py --open RA.open.tsv --ours <fuzz_command unit>/lib --donor <cgif_file_fuzzer unit>/lib \
    --img <images dir: cmd.A.pin cmd.A.twin cgif.A.pin cgif.A.twin> --outdir .
```

Scripts (sha256 first 12 of this run): triage.py 20162c83d335 (engine: numeral location by the gate's own
sentence ordinal `idx` for paired rows and by row order for UNPAIRED-PORTED rows, the stale-donor test, by-use
grep, controls), rules.py 3e07931b23be (the rules and their measurements), facts.py 566050a36791 (ISA / ABI /
image / unit-model facts), imgtools.py 799de36cd2a8 (pyelftools image access; the run used 0837a25c00a3, which
differs only in a default argument of load() that triage.py always passes). pyelftools 0.33; no other tool.

Outputs: triage-rows.tsv (the 16 input columns + reason, measurement, result, finding_kind, new_value, read_by),
controls.tsv, code-findings.tsv.

## Limits

- Rows that restate a unit model definition (RtDDefs.v astrace_at, YG00.v kUnwindMax / kFreeArrayOffset,
  YG01.v DEPOT_CAP, YG0f.v SHADOW_OFF / kLowShadowBeg / owned_extents, YP08.v R_hdr) are judged against that
  definition; the definitions themselves are not re-derived from the image here.
- Start-up numerals are judged against the generated certificate lib/A/AB01.v; its own fidelity to the image is
  not checked here.
- Observed, not a numeral row: the fuzz_command header line of lib/A/AFhy.v and of the walk files lib/A/AFip.v ..
  AFk2.v does not mention the rewritten trace-object start these files carry (R_bst / R_nofr at the head of REG0;
  Hch / RIo / RI2 / regsI, the premises of lib/A/Rt/RtDDefs.v amalloc_inner_realizes); e.g. lib/A/AFip.v's header
  names only module paths, TfibSyms -> CmdBSyms and moved addresses. A provenance-text gap, no value is wrong.
