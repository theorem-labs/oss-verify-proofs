# reac-pw/fuzz_segconf image A: the interceptor interface (the interceptor lane <-> the image-A owner)

proves no function (kind: statement text; this file names contracts, it proves nothing)

Version: v1, 2026-10-30, the interceptor lane. Status: ACCEPTED by the image-A owner at
15:45Z (Agreement section) with rule 3 reworded and DECISIONS 1-3 answered; v1 proposal was e45889d6935a.
Inputs: the image-A owner's Option B decision (15:25Z: fuzz_command's A/Prog shape, runtime entries as Section hypotheses, one
`<x>_realizes` per interceptor, image numbers as Section variables) and the image-A owner's kit decision (15:28Z: fuzz_command's
Reusable lineage; frame from fuzz_command's lib/A; listing layer `Seg*` by the listing lane, commit d7b80bda74fb).
Donor ref: origin/ossv/recipes 501c0d516c69. Entry addresses: the .symtab of the unstripped twin (sha256 4362701197e4...) of the pin (sha256 48c5355bdacb...).

## Rules of this interface

1. A row's contract is a RELEASED Definition, carried VERBATIM in a segconf file with the SAME module path tail as in its
   donor (lib/A/Rt/<File>.v), so a walk writes exactly what fuzz_command's walks write, e.g.
   `Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @RtString.astrspn_realizes fx0 rc SEGS B pc_strspn gotw guard.`
   Every image number is one of the Definition's own parameters (pc, gotw, guard, cid, ...): the text is
   image-independent and image B uses it unchanged.
2. A row marked NEW has no released text. The interceptor lane writes it in the family of the template named in the row, as a
   new Definition in lib/A/Rt/RtSeg.v, and offers it to the image-A owner BEFORE any walk relies on it.
3. The interceptor lane AUTHORS the text of every row and owns every file of its closing; the image-A owner is the owner of record of
   the row texts: a new row or a changed text goes to the image-A owner first, with the exact text, and no walk relies on it
   until the image-A owner accepts it. (Reworded by the image-A owner, 15:45Z: VERIFY's 15:11Z condition makes it the one owner of
   every shared contract.)
4. The interceptor lane delivers, per row, `seg_<x>_closed` in lib/A/Rt/SegRtClosed.v (the role of fuzz_command's
   lib/A/Rt/RtClosed.v): the contract at segconf A's numbers, under the kit's facts on B only (AR_laws and the
   unit's B-symbols record), no other Section hypothesis left. the image-A owner's close consumes it.

## Rows (the interceptor lane owns)

| # | entry (A `__wrap_` trampoline) | contract a walk takes | carrier file | text source (501c0d516c69) | closing the interceptor lane delivers |
|---|---|---|---|---|---|
| 1 | strncmp 0x43a18 | `RtString.astrncmp_realizes (pc)` | lib/A/Rt/RtString.v | fuzz_command lib/A/Rt/RtString.v:121 | port fuzz_command RtClosed.v:81 cmd_strncmp_closed (Bz walk + bridge) |
| 2 | strspn 0x43a30 | `RtString.astrspn_realizes (pc gotw guard)` | lib/A/Rt/RtString.v | RtString.v:139 | port RtClosed.v:83 / RtLStrspn.v:111 |
| 3 | strtol 0x43ab8 | NEW `RtSeg.astrtol0_realizes (pc gotw guard)` | lib/A/Rt/RtSeg.v | template RtNumber.v:81 astrtol_realizes, which needs `0 < e` (:85); segconf's one site (reac_declared_vlan_split 0x89c68) passes a1 = 0 (internal record commit f252a3dc75cb, path records/interceptors/measurements/callsites.asan.tsv, sha256 704ffff206b5) | port RtLStrtol.v + the NULL-endptr arm of StrtolFixAndCheck |
| 4 | snprintf 0x43a64 | `RtPFSeg.seg_asnprintf_realizes segs B img_lo img_hi cr pc gotw guard` = released RtPFCmd.cmd_asnprintf_realizes (RtFormat.asnprintf_realizes' text, rt_rom_view) at the family `FR_seg img_lo gotw` over the segconf grammar seg_piece (PRel p | Pu | Pzu | P24s; seg_pk total, so FR_cmd is a special case and one closing also gives RtFormat.asnprintf_realizes via seg_all_rtformat); accepted-by the image-A owner 2026-10-30T17:50Z 755e9278f8ff | lib/A/Rt/RtPFSeg.v (sha256 5fcabfce1726) | RtPFCmd.v:310; review (internal record commit 72eb1296d954, path records/interceptors/reviews/pfreview.md, sha256 ef57763bee05) | port the released route (RtFSnprintf.v cmd_snprintf; printf_common pcom_genx_spec; GXA printf model) + the piece agreement for %u / %zu / %.24s (internal record commit f252a3dc75cb, path records/interceptors/measurements/pfdesign.md, sha256 1eae8f5667f8, section 8) |
| 5 | vsnprintf 0x43a5c (refuse 0x88fa4, caller's va_list) | `RtPFSeg.seg_avsnprintf_realizes segs B img_lo img_hi cr pc gotw guard` = released sh_avsnprintf_icpt_realizesUa (RtPFSx.v:166, the only form svsni_ok proves) at U = [] with consts_view over cr replaced by RtDefs.rt_rom_view (four Ua premises the caller gives: spZ <= ap, destination off the argument slots, ap + 8|ws| <= 2^47, amem_range d (w+8)); accepted-by the image-A owner 2026-10-30T17:50Z 755e9278f8ff | lib/A/Rt/RtPFSeg.v | RtPFSx.v:166 (RtPFShared.v:226 has no released proof) | port FMsnprintfSvsni.v:981 svsni_ok + bridge seg_avsnprintf_of_Ua (ecall_preU at [], AR from ARU at [], rt_rom_view -> consts_view over cr) |
| 6 | strchr 0x43a28 | NEW `RtSeg.astrchr_realizes (pc)`, RtString form (PRE / RD / STR / POST), post of FMH_Rt.v:115 | lib/A/Rt/RtSeg.v | fuzz_manifest lib/A/FMH_Rt.v:115 (fm form only) | port fm FMstrchr.v:85 astrchr_holds + bridge to RtString form (as RtClosed.v:81 does for strncmp) |
| 7 | strncasecmp 0x43a20 | NEW `RtSeg.astrncasecmp_realizes (pc)`, RtString form, post of FMH_Rt.v:133 | lib/A/Rt/RtSeg.v | FMH_Rt.v:133 | port FMstrncasecmp.v (fm_astrncasecmp_realizes) + bridge |
| 8 | strstr 0x43a24 | NEW `RtSeg.astrstr_realizes (pc gotw guard)`, RtString form, `aguard_ok segs W mem gotw guard` first (RtString.v:139 form: musl twoway_strstr reads the GOT word 0xa36d8 and __stack_chk_guard 0x5ff078, 0x9b238 / 0x9b23c, canary store 0x9b250; the image-A owner's finding 16:08Z), post of FMH_Rt.v:160 | lib/A/Rt/RtSeg.v | FMH_Rt.v:160 | port FMstrstr.v + bridge |
| 9 | isalnum 0x901a0 (musl, direct call) | NEW `RtSeg.aisalnum_realizes (pc)`, RtString form, post of FMH_Rt.v:170 | lib/A/Rt/RtSeg.v | FMH_Rt.v:170 | PORT, not a new walk: fm FMctype.v aisalnum_holds (FMAsm.v:99-100) + bridge |
| 10 | strcasecmp 0x43a1c | NEW `RtSeg.astrcasecmp_realizes (pc)`, RtString form | lib/A/Rt/RtSeg.v | template FMH_Rt.v:133 without n (post: v = 0 <-> map lc (l1 ++ [0]) = map lc (l2 ++ [0])) | new walk from fm Bz/A/I_scase.v |
| 11 | strrchr 0x43a2c | NEW `RtSeg.astrrchr_realizes (pc)`, RtString form | lib/A/Rt/RtSeg.v | template FMH_Rt.v:115, post = last occurrence; both sites pass c = 0x2e | new walk on Bz/A/I_strchrw.v + musl strrchr / __memrchr |
| 12 | strncpy 0x43ab4 | NEW `RtSeg.astrncpy_realizes (pc)` | lib/A/Rt/RtSeg.v | template RtString.v:214 astrcpy_realizes, plus n and the NUL padding | new walk |
| 13 | calloc 0x56c38 (PC_calloc, lib/A/Rt/SegRtPC.v) | `RtSegCalloc.aseg_calloc04_rule (pc_calloc cstk)` (renamed from acalloc04_rule to avoid the kit's YGCalloc.acalloc04_rule): the kit's YC5d.amalloc04_rule form (YC5d.v:58-75) at size m*n, a0 = m, a1 = n, m*n <= YGCalloc.PRIM_MAX (64512; asan_calloc zero-fills only primary blocks, 0x33af8-0x33b08), NO trace premise, post adds (res, m*n) to ablocks with all m*n bytes reading 0, ONE allocator event (k + 1), meter mo_malloc MT (m*n), 4096 <= res (no NULL arm); walkers write `forall fx0, @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT pc_calloc cstk`, cstk = ASTACK + 2192 = 18576 (Allocate's ly_bot bound via astk_ok); accepted-by the image-A owner 2026-10-30T17:28Z 4d194b3b4e98, CHANGE (PRIM_MAX cap) accepted-by the image-A owner 2026-10-30T17:45Z 09a999c99c8a | lib/A/Rt/RtSegCalloc.v (sha256 53722c5175e3) | consumer shape: the harness lane's calloc call shape for its harness walk, carried verbatim as the Definition in lib/A/Rt/RtSegCalloc.v at 4d194b3b4e98 (one rename), + the PRIM_MAX cap at 09a999c99c8a; ruled by the image-A owner 16:17Z (replaces YGCalloc.acalloc_realizes_cgif) | fuzz_decode's thin calloc walk over omx-clap-core/fuzz_state's closed Allocate (AGtopcgifC.v:57) + journal bridge from fuzz_command's malloc closing (internal record commit f252a3dc75cb, path records/interceptors/measurements/callocplan.md, sha256 7a3106749b34) |
| 14 | `__asan_stack_malloc_5` 0x3ea2c | `astack_malloc_realizes 5` (kit YG0d) | kit | YG0d.v:285 | port RtSM5 / RtSM5T (RtClosed.v:53) |
| 15 | `__asan_stack_free_5` 0x3ec38 | `RtStack.astack_free_cls_realizes (pc 5)` | lib/A/Rt/RtStack.v (the image-A owner's frame file by DECISION 1) | RtStack.v:77 (fuzz_command's walks take it at class 5: CmdProgClosed.v:193-195) | port RtSF5 (RtClosed.v:60) |
| 16 | strlen 0x43a0c | `RtString.astrlen_realizes (pc)` | lib/A/Rt/RtString.v | RtString.v:80 | port RtClosed.v:70 cmd_strlen_closed chain |
| 17 | strcmp 0x43a14 | `RtString.astrcmp_realizes (pc)` | lib/A/Rt/RtString.v | RtString.v:108 | port RtClosed.v:72 cmd_strcmp_closed chain |
| 18 | (RETIRED, accepted-by the image-A owner 2026-10-30T17:16Z) memchr 0x43a3c | was `RtString.amemchr0_nf_realizes (pc)`: it states only the not-found case, and the c = 0 site 0x850d8 searches libFuzzer's (data, size), which may hold a 0 byte (internal record commit f252a3dc75cb, path records/interceptors/measurements/sites.md, sha256 ae7d3353ce4c, lines 149-151, 214-217); all three memchr sites take ROW 20 | - | - | - |
| 19 | bcmp 0x43a38 | `abcmp_realizes (pc)` (kit text, YG0d; the image-A owner's kit file) | kit | fuzz_command Reusable/YG0d.v (abcmp_realizes) | OWNER the image-A owner (kit text + core closing): fuzz_command's AE2s family (AE2s AE2z AE3b AE6z AE70; AE2s.v:711 bcmp_icpt_contract : abcmp_realizes tfibsegs B 0x45154), relocated by the image-A owner's core with its pc regenerated for segconf A; the interceptor lane only re-exports it in SegRtClosed.v. accepted-by the image-A owner 2026-10-30T17:12Z |
| 20 | memchr 0x43a3c, ALL THREE sites: 0x850d8 (LLVMFuzzerTestOneInput, c = 0), 0x862d4 (m_file, c = 0x5d), 0x86344 (m_file, c = 0x3d) | `MemchrDef.amemchr_realizesM (lo hi pc)`: consts_view segs lo hi W mem over musl memchr's .rodata word-constant window (any 0 <= c < 256, n < 2^32; post first_byte ... c k /\ a0 = if k <? n then x + k else 0); walks write `@MemchrDef.amemchr_realizesM fx0 rc SEGS B memchr_lo memchr_hi pc_memchr` (memchr_lo / memchr_hi in the image-A owner's SegInstA; the listing lane reads 0x10350..0x10370 in A, to be checked against the bytes in the closing). CHANGED 17:14Z from `amemchr_realizes (pc)`, whose `rom_view` (YG0d.v:390, every in_rom byte) no program walk can give: found by the m_file lane, accepted by the image-A owner 17:14Z | lib/Rt/MemchrDef.v (on commit 8998d9038b25) | fuzz_command lib/Rt/MemchrDef.v (amemchr_realizesM) | port fuzz_command lib/A/Rt/Memchr.v:587 memchr_icpt_realizesM tfibsegs B 0x10358 0x10378 0x45158. Row added by the image-A owner 15:58Z, found by the m_file lane; site 0x850d8 added 17:16Z |

Not in this layer: malloc, free (allocator), `__asan_memcpy` / `__asan_memset`, set_shadow, classes 0 / 1 / 3, the kit laws
(stack_malloc_progressP, astack_free_law, frame_flag_lawP): the image-A owner's frame. identity's lib/A/Rt files are not carried at all
(DECISION 2).

## DECISIONS (answered by the image-A owner 15:45Z: 1 = the rule as proposed, 2 = (b), 3 = (a))

1. fuzz_command's 139 lib/A/Rt files: which are frame (the image-A owner) and which are this layer (the interceptor lane)? RECOMMENDED rule:
   a file is the image-A owner's if the frame's own closure (AsanTop / close, minus the interceptor closings) Requires it - e.g.
   RtDefs, RtAPI, RtStack, RtShadow*, RtSRegion*, RtSM0/1/3 (+T), RtSMx*, RtD* (malloc), RtLAsanMemcpy / Memset,
   RtDtor*; every other Rt file a closing of a row above needs is the interceptor lane's (RtString, RtNumber, RtFormat, RtF*,
   RtPF*, RtBz*, RtL{Strncmp,StrncmpR,Strspn,Strtol}, RtNMusl, RtSM5 / RtSM5T, RtSF5, Strnlen*, RtSStrnlen*, and the
   strlen / strcmp / memchr files if DECISION 2 is (b)); files no closing needs are not carried (strdup / strndup,
   atoi, strcat, strcpy, strcspn, strtok, sprintf, classes 4 and 7). A file both need stays the image-A owner's; I consume it.
2. strlen 0x43a0c, strcmp 0x43a14, memchr 0x43a3c, bcmp 0x43a38. The image-A owner's first premise map put identity's lib/A/Rt (identity form:
   its `astrlen_realizes` has first_byte / src_ok premises, a DIFFERENT text with the SAME name as
   RtString.astrlen_realizes) in your core. Under Option B fuzz_command's walks take RtString.astrlen_realizes,
   RtString.astrcmp_realizes and RtString.amemchr0_nf_realizes, closed in its RtClosed.v (:70, :72, :76), and the
   kit's abcmp_realizes (closed outside RtClosed.v; where, I have not yet read). (a) your frame carries them, or (b)
   the interceptor lane carries them as rows 16-19. RECOMMENDED (b): one
   owner of interceptor text. Note for either owner: segconf's three memchr sites must be checked against
   amemchr0_nf_realizes (c = 0, not-found form); a site that searches another byte needs a new contract.
3. strchr, strncasecmp, strstr, isalnum have released text in fuzz_manifest's form only (FMH_Rt.v: ecall_pre_k /
   cstr_ok / rom_viewN / rom_viewO, over fuzz_command's own copy of that vocabulary in RtBzHBase.v). (a) NEW RtSeg
   Definitions in RtString form (PRE / RD / STR / POST) with FMH_Rt's posts, proved from fm's walks by the bridge
   fuzz_command already uses for strncmp (fm-form Bz walk -> RtString.astrncmp_realizes, RtClosed.v:81); or (b) carry
   FMH_Rt's text verbatim in lib/A/Rt/RtBzHStr.v beside fuzz_command's strncmp. RECOMMENDED (a): the walks see one
   premise form. Rows 10 and 11 follow the same choice.

## Names still open (I take them from their owners, I do not choose them)

- SEGS, the B-symbols record and the trampoline symbol names (`SIG CS___interceptor_trampoline_<x>` in fuzz_command):
  from the listing layer (commit d7b80bda74fb, prefix `Seg`).
- gotw / guard (fuzz_command: A_SSP_GOT / A_SSP_GUARD): segconf A's stack-protector GOT cell and guard, from the same
  listing layer or the image-A owner's base file.

## Agreement

- offered-by: the interceptor lane 2026-10-30 (proposal e45889d6935a)
- accepted-by: the image-A owner 2026-10-30T15:45Z (Decisions 1 = rule as proposed, 2 = (b), 3 = (a); rule 3 as reworded)
  (the image-A owner's message 1f44d2cf, 15:31Z; it also asks that segconf's three memchr sites be measured against row 18,
  and that the core lane tell the interceptor lane before it stages an Rt file whose owner by DECISION 1 differs from
  port_core's closure.)
- accepted-by: the image-A owner 2026-10-30T17:27Z 80d098bd1905 (rows 3, 6-12: lib/A/Rt/RtSeg.v sha256 ce2e38d10fc0, after the fresh
  review (internal record: commit 72eb1296d954, path records/interceptors/reviews/ctrreview.md, sha256 57e482a595bd), 8 / 8 ACCEPT against all 18 caller sites). Bridges interceptor post -> SegModel are
  the interceptor lane's (next to the rows); the list Z / list byte string glue goes to the image-A owner's SegABase.v.
- Names settled since: SegBSyms (B record), RtAPI.v keeps fuzz_command's PC_* / A_SSP_* names (the image-A owner's), the PC_ constants only
  this layer uses are in lib/A/Rt/SegRtPC.v (f1877f008159).
