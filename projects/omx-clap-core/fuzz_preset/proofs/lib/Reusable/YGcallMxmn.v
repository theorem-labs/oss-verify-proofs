(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): Section allocm takes
   YGcallx's new QMm (the call's conjuncts on the state and the call memory) and QMQ (QMm S mem -> QM S); its eight
   _m rules take `QMm Sc <call memory>` instead of `QM Sc`, and pass QMm / QMQ to YGcallx's rules. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the free _m rules are proved once over the journal's
   world relation R and the callee's call post APOST (aj_free_x_ct_mR / aj_free_at_x_ct_mR; the old _m names are the
   instances at wle and acall_post_x; aj_free_x_mR / aj_free_at_x_mR likewise); every other call rule here with a
   journal takes it at any R, the old names being their wle instances: aj_intrin_at_xmR, aj_poison_at_x_mR and
   aj_poison_x_mR take R alone; aj_intrin_at_xm_frR, aj_bcmp_at_xmR, aj_strcmp_at_xroR, aj_strlen_at_xroR,
   aj_strcmp_at_xromR, aj_strlen_at_xromR, aj_strlen_at_xmR, aj_stack_malloc_at_xmR, aj_set_shadow_at_xmR,
   aj_unpoison_at_x_mR and aj_unpoison_x_mR take R reflexive and transitive, binders first (the stack-malloc form uses
   both to compose the call's own journal into the caller's); the malloc _m rules aj_malloc_x_mR, aj_malloc_x_ct_mR,
   aj_malloc_at_x_mR and aj_malloc_at_x_ct_mR also take wle inside R (YGcallx's malloc R forms); section 12 states the cf
   free forms under the re-hide (aj_free_x_ct_m_rh / aj_free_at_x_ct_m_rh: SRr' segs RZ_cf, the journal at wle' segs
   RZ_cf). *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: memnorm out of every call text): YGcallx.v's leaves
   malloc_leaf_x / free_leaf_x / free_leaf_xA lost their memnorm keep, the conjunct family 4's keep was read from. So
   the eight _m malloc / free rules of section 10, their R forms (_mR) and section 12's two cf free forms (_m_rh) drop
   the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) from their conclusion: each _m / _mR rule is now its
   YGcallx.v original VERBATIM (the _mR forms are proved by it), under its own name for the walks that apply it. *)
(* Theorem Labs, 2026-10: fuzz_preset, the ENGINE HALF OF THE MEMNORM PER-CALL KEEPS (c-omx-alloc's MemnormKeeps
   measurement, the internal file MEMNORM-KEEPS.md; decisions a Theorem Labs lane 10:42Z / 10:50Z / 11:00Z, a Theorem Labs lane 10:41Z).
   rule 24: no function proved. rule 24: proves no function (kind: engine lemmas).
   MN.memnorm is YAkMemnorm.memnorm (YAkMemnorm.v:41): the body of YAjMemnorm.memnorm (= Lib.Mem.mem_inv segs m /\
   MemNorm.task_mem segs m, YCbqGmn's MN.memnorm) written over LPS only. The two convert into each other
   (YAkMemnormJ.memnorm_kit_j, `exact H`); a consumer that needs the YAjMemnorm form converts in its own leaf.
   No call rule can derive memnorm segs mem' from a text's post: every post states mem' through views only (aview,
   apresent, ARx), so the keep (MN.memnorm segs mem -> MN.memnorm segs mem') must be a conjunct of the text's own post.

   FAMILY 1, runtime rows (consumers: the row owners of po_asan_memcpy_cf = YG0d2cf.aintrin_realizes_cf and po_bcmp_cf
   = YG0d2cf.abcmp_realizes_cf, who pay the conjunct from their own runs; and every walk that crosses __asan_memcpy or
   bcmp, e.g. FuzzStrdup.v through the ARcfx lift):
   - aintrin_realizes_xm / abcmp_realizes_xm: YGcallMx.v's aintrin_realizes_x / abcmp_realizes_x with the keep as the
     last post conjunct; the _forget lemmas give the plain texts back;
   - aj_intrin_at_xm, aj_intrin_at_xm_fr, aj_bcmp_at_xm: YGcallMx.v's aj_intrin_at_x, aj_intrin_at_x_fr, aj_bcmp_at_x
     with the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) as the last conclusion conjunct (memcpy goes
     through aintrin). EVERY call rule here states the keep as an implication in its conclusion, with no
     MN.memnorm premise (h-hpreset-7 11:30Z, measured by h-rw-pre-5's BPjGet): a walk carries the invariant
     R m := (P mem -> P m) (the srr_inv_laws_imp form), so at a call it holds the implication, not P memT;
   - aintrin_realizes_xm_conj / abcmp_realizes_xm_conj: the ARx -> ARx /\ P lifts (YGcallMx.v Section cj).
   FAMILY 1b, the strcmp / strlen twins in the read-only-premise form (c-libc-stdio 11:46Z rom_view decision; section 8
   below). Consumers (at origin/cold/h-rw-pre-7-b-ex_value 96eea692f6cd and origin/cold/h-pre-b3-exword-b
   2038bfaedb4e): B/Prog/ExvB_Stmt.v:317 / :321 (EXV_HYP's strcmp and strlen fields, the _xro texts),
   B/Prog/ExvB_Disp_str.v:537 and B/Prog/ExvB_Loop_A2_call.v:494 (aj_strcmp_at_xro), B/Prog/ExwB.v:435 (Hypothesis
   STRLEN, astrlen_realizes_xro) and :674 (aj_strlen_at_xro). Each passes (SK) segs B PST ARx rlo rhi LAWS segs_low in
   the order this file's twins take them.
   - astrcmp_realizes_xro / astrlen_realizes_xro: the consumers' texts, copied VERBATIM from h-rw-pre-7's
     B/Prog/ExvB_StrcmpRo.v (blob af14c24f474d) and h-pre-b3's B/Prog/ExwB_StrlenRo.v (blob d38c23bec721).
     Checked by a diff: each is YGcallMx.v's astrcmp_realizes_x / astrlen_realizes_x with the one premise
     `rom_view segs W mem` replaced by `arodata_okP segs rlo rhi B (aview segs (w_H W) mem)` (byte-identical after that
     substitution), and so are the consumers' rules aj_strcmp_at_xro / aj_strlen_at_xro (statements and proofs).
     Same Variable order (segs B ARx rlo rhi), so each copy converts to the consumer's definition;
   - astrcmp_realizes_xrom / astrlen_realizes_xrom: those texts with the keep as the last post conjunct; the _forget
     lemmas give the _xro texts back; the _conj lifts take them to ARx /\ P;
   - aj_strcmp_at_xro / aj_strlen_at_xro: the consumers' rules, MOVED here (h-hpreset-7 12:41Z) from
     ExvB_StrcmpRo.v:74 / ExwB_StrlenRo.v:72, statement and proof verbatim but for the text's arguments
     (`astrcmp_realizes_xro pc` there, `astrcmp_realizes_xro segs B ARx rlo rhi pc` here, the text being this file's
     global). NO memnorm keep: for a walk that needs only the rodata swap and must not be given an unread memnorm
     obligation (h-hpreset-7's `same` walk);
   - aj_strcmp_at_xrom / aj_strlen_at_xrom: aj_strcmp_at_xro / aj_strlen_at_xro (= YGcallMx.v's aj_strcmp_at_x /
     aj_strlen_at_x with the premise renamed) with the keep an implication in the conclusion. The proofs pass
     arodata_okP to the text unread; no proof reads rom_view.
   - in_roP / arodata_okP: NOT defined here. They are the leaf lib/Spec/PresetRodata.v (blob 4eb7e95e7e93, by path
     from commit 1bba49fd7ac5), Required, so every arodata_okP below is
     PresetRodata.arodata_okP: one home. The leaf is LiaTwx2-free but NOT override-free (a Theorem Labs lane's measured probe,
     2026-10-29: `Print Ltac lia` after Requiring the leaf alone prints the YM05 / YM03 body, "Redefined by: YM05
     YM03"), and this file already carries that override, so the leaf buys one home only, not a stock lia.
   - astrlen_realizes_xm / aj_strlen_at_xm (section 9; h-verbs-1 12:36Z: literal's walks carry rom_view, not
     arodata_okP, on both images): YGcallMx.v's astrlen_realizes_x / aj_strlen_at_x in the rom_view form, with the
     keep (text: last post conjunct; rule: implication in the conclusion) and nothing else; astrlen_realizes_xm_forget
     gives astrlen_realizes_x back, astrlen_realizes_xm_conj lifts it to ARx /\ P.

   FAMILY 2, fake frames (consumers: h-hpreset-7's frame-class lane, which pays stack_malloc0_contract_xm /
   stack_malloc1_contract_xm from the image walks FCm0s.v:49 / FCm1s.v:51 in its own per-image leaves (lib/A/FCm01xm.v
   and the AU twin) through memnorm_frame_of; the parse_value walk across __asan_stack_malloc_1, image A pc 0x85efc,
   through aj_stack_malloc_at_xm; and the walks that retire a fake frame through __asan_set_shadow_f5, e.g. image A'
   pc 0x82bec, through aj_set_shadow_at_xm). The contracts are not here (h-hpreset-7 11:00Z): they need the image
   walks, and those stay in the per-image leaves.
   - astack_malloc_realizes_xm: FCiface.v's astack_malloc_realizes_x with the keep as the last post conjunct;
   - aj_stack_malloc_at_xm: YGcallSx.v's aj_stack_malloc_at_x for it (Section hypotheses as YGcallSx.v Section x),
     the keep an implication in its conclusion as for family 1;
   - astack_malloc_realizes_xm_conj: the ARcfx lift, YGcallScf.v's astack_malloc_realizes_x_conj for it;
   - memnorm_frame_of: memnorm survives one symbolic-runner phase. The phase lemmas (FCm0r.v:67-88 fs_phase /
     fs_phase_to, from SRr_run_gen, YA0o.v) end in frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1), and the walk holds
     the phase's start st_ok (FCm0s.v :167, :303, :348, :385). Evidence (s1b blobs YP09.v 2538c5959920, YP0l.v
     12ec6262ab0c, the same as origin/cold/h-hpreset-7-frameclass 386c6872566): st_ok (YP0l.v:102) contains
     mem_ok segs E (ms_mem ms) (ss_mem ss), which is Forall region_ok (YP09.v:158); region_ok (YP09.v:138) gives
     writable_at m (base + o) for every o in [r_wlo, r_whi); writable_at m a := wview segs m (Z_to_bv 64 a) <> None
     (YP09.v:136); in_wrange (YP09.v:861) is the union of those windows. So every byte that frame_of (YP09.v:863)
     lets change is writable_at (mrestrict H (ms_mem ms)), and wview_not_ro + wview_absent_seg close it (here as
     ak_wview_not_ro / ak_wview_absent_seg, below). The statement is h-hpreset-7's frame-step hypothesis at
     P := memnorm segs, generic in segs.
   - aset_shadow_realizes_xm: FCiface.v's aset_shadow_realizes_x with the keep as the last post conjunct;
     aset_shadow_realizes_xm_forget gives aset_shadow_realizes_x back;
   - aj_set_shadow_at_xm: YGcallSx.v's aj_set_shadow_at_x for it (Section x's hypotheses, so the same arguments),
     the keep an implication in its conclusion as for family 1; its proof is the original's, with the text's keep
     read off the post (the text's mem' is the call's mem2);
   - aset_shadow_realizes_xm_conj: the ARx -> ARx /\ P lift (ARcfx: P := xs_placed_cf). The text keeps S (no
     set_fs), so, unlike astack_malloc_realizes_xm_conj, it needs no law on P.
   KEEP VERDICT FOR set_shadow (measured as the internal file MEMNORM-KEEPS.md sec. 6 did for stack_malloc): B. Not A: the text's
   post states mem' only through ARx, aview (Some v on [q, q + n), equal elsewhere) and apresent, so the two gaps of
   the internal file MEMNORM-KEEPS.md sec. 2.2 stay open: a byte equal to its ROM value at a read-only image address where mem holds
   none leaves every view equal (mem_inv fails), and a byte at a hidden address at or above TASK_SIZE leaves every
   view and every apresent fact equal (task_mem fails); so aj_set_shadow_at_x cannot derive the keep. Not C: the walk
   behind FCapi.v:41 preset_set_shadow_f5_x, FCf5.v:83 set_shadow_gen_x, makes no kernel step (its post has
   same_but_materialized md md') and changes memory only by machine stores: the stub phase f5_phase (FCf5.v:62)
   leaves the overlay equal (MEQ1, FCf5.v:115), and musl memset (AE3d.v:1049 tfib_memset, under store_ok,
   FCf5.v:137) is one msteps run. PAYMENT ROUTE, for the per-image leaf as for stack_malloc's contracts (compiled in a
   scratch leaf over FCf5.v, not committed; the commit message that added this paragraph has the result):
   set_shadow_f5_contract_xm is set_shadow_gen_x's proof plus one assert before SRr_ret and the keep as the last
   split. From MN.memnorm mem: memnorm_sub with MEQ1 gives MN.memnorm mem1; memnorm_mrestrict, then memnorm_msteps
   (whose store case is memnorm_write) on tfib_memset's run Hms (FCf5.v:140-142), give MN.memnorm m2r;
   memnorm_munrestrict gives MN.memnorm mem2 (mem2 := munrestrict H mem1 m2r, FCf5.v:146). memnorm_frame_of is not
   needed: the stub phase writes nothing.

   FAMILY 3, helpers (consumers: rows proved by the MemNorm cj-kit composition, e.g. c-libc-stdio's strcmp row through
   MemNorm.evt_normalize_cj (memnorm_same_cj); rows whose new bytes are all wview-defined at the call
   (memnorm_new_wview); c-omx-alloc's fuzz_malloc walk at its kernel grant nodes (region_free_reserved_off_segs)):
   - memnorm_same_cj, memnorm_new_wview (the internal file MEMNORM-KEEPS.md sec. 4.5). memnorm_same_cj is stated over cj_same_ak, the
     body of MemNorm.cj_same (MemNorm.v:541, through cj_drop :527) over YAkMemnorm.ro_addr; MemNorm.cj_same segs m m'
     converts to cj_same_ak segs m m';
   - region_free_reserved_off_segs: a grant range that region_free clears of segments_reserved segs (Run.v:216, the
     page-rounded LOAD segments) holds no byte of any segment. It needs one bound the report did not state: every
     nonempty segment ends at least page_size below 2 ^ 64. Without it the lemma is false: a segment with base 0 and
     size 2 ^ 64 - 1 has the reservation (0, 2 ^ 64), whose length wraps to 0, so region_free clears every range
     while find_segment still finds that segment. region_free_reserved_off_segs_low takes the engine's segs_low
     (forall a, in_img segs a -> 0 <= a < kLowMemEnd) instead, so no consumer carries the bare bound: the last byte of
     a nonempty segment is in_img, so it ends below kLowMemEnd = 0x7fff8000 (YG0f.v:18). segs_low at each instance:
     the ARcf walks take it from the PAImg class field pa_segs_low (YC4aP.v:43), filled by A_prog_segs_low
     (A/PAImg_prog.v:142, image A), B_prog_segs_low (B/PAImg_prog.v:142, image B) and img_segs_low (A/PAImg_S1.v:144,
     B/PAImg_S1B.v:144, the S1 images); the frame-class image tfibsegs (cgif's AR through FCiface.AR_nohp, and ARcf
     through fs_iface) has tfib_segs_low (A/AE7f.v:64, over A/AB1v.v's Asan tfibsegs; Reusable/YE7f.v:65 is the
     twin over Reusable/YB1v.v's AsanUbsan tfibsegs). region_free_app_l gives
     the reserved prefix of a fresh grant's guard (Mmap.v:1566-1570, region_free (vm_reserved h ++ vm_maps h) a n).

   FAMILY 4, the malloc / free call rules (section 10). They exported the leaf's memnorm keep; since field round 3
   part 3c YGcallx.v's malloc_leaf_x / free_leaf_x end with errno kept and the raw frame, with no keep, so these rules
   state none:
   - aj_free_x_m, aj_malloc_x_m, aj_free_x_ct_m, aj_malloc_x_ct_m, aj_free_at_x_m, aj_malloc_at_x_m,
     aj_free_at_x_ct_m, aj_malloc_at_x_ct_m: each is its YGcallx.v rule (the name without _m) VERBATIM, with the same
     arguments and the same _x text premise (afree_realizes_x / amalloc_realizes_x); each R form (suffix _mR) is
     YGcallx.v's R form (suffix R) VERBATIM and is proved by it. They keep their names for the walks that apply them;
   - fs_frame_bytes_ok (for 0 <= cid, fs_frame_bytes cid is at least 64 and a multiple of 64) now lives in YCbqG.v,
     where frame_bytes_x reads it.

   FAMILY 5, the poison / unpoison call rules that EXPORT the text's keep (consumers: S1's walks, which cross
   __asan_poison_memory_region (own B) and __asan_unpoison_memory_region (fuzz_free A / B); h-rw-cmd-3's fuzz_realloc
   walk (AL3, three poison / unpoison calls); section 11). YGcallPx.v's texts apoison_realizes_x / aunpoison_realizes_x
   end with (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem') since s1b 459129c18903, so no text twin is
   needed, and YGcallPx.v's rules drop it (`& _`):
   - aj_poison_at_x_m, aj_unpoison_at_x_m, aj_poison_x_m, aj_unpoison_x_m: each is its YGcallPx.v rule (the name
     without _m) with the same arguments, in YGcallPx.v's Section order (px: segs B PST ARx hd; l: LAWS segs_low), plus
     the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) as the last conclusion conjunct (the symbolic-state forms
     at (ms_mem ms)). The _at_x_m proofs are YGcallPx.v's, keeping the text's last conjunct; the _x_m proofs reduce
     to them as YGcallPx.v's do. These four are all the poison / unpoison call rules of YGcallPx.v; it has no _ct
     form. A script checked that each statement differs from its original only in the name, the added conjunct and
     the text's spelling (YGcallPx.apoison_realizes_x segs B ARx hd pc here, apoison_realizes_x pc inside YGcallPx.v's
     Section px); the commit message of the commit that merged section 11 into cold/c-omx-alloc-mxmn has its output.

   WHICH RULE TO USE. A rule with the keep has the conjunct (MN.memnorm segs memT -> MN.memnorm segs mem2) last in its
   conclusion, and its text has (MN.memnorm segs mem -> MN.memnorm segs mem') last in its post; no rule has a memnorm
   premise. Only the two _xro rules and the eight malloc / free rules (family 4) have no keep.
   | call         | rule                  | text                       | read-only   | keep | use it when the walk carries ...
   | memcpy/set   | aj_intrin_at_xm       | aintrin_realizes_xm        | none        | yes  | dest bytes awr_byte admits
   | memcpy/set   | aj_intrin_at_xm_fr    | aintrin_realizes_xm        | none        | yes  | dest bytes awr_byte admits or
   |              |                       |                            |             |      | caller-frame bytes FP names
   | bcmp         | aj_bcmp_at_xm         | abcmp_realizes_xm          | none        | yes  | (no read-only fact needed)
   | stack_malloc | aj_stack_malloc_at_xm | astack_malloc_realizes_xm  | none        | yes  | SMX (model's frame malloc)
   | set_shadow   | aj_set_shadow_at_xm   | aset_shadow_realizes_xm    | none        | yes  | the frame (cid, pos) in own,
   |              |                       |                            |             |      | [q, q + n) in its shadow
   | strcmp       | aj_strcmp_at_xro      | astrcmp_realizes_xro       | arodata_okP | no   | arodata_okP, no memnorm
   | strcmp       | aj_strcmp_at_xrom     | astrcmp_realizes_xrom      | arodata_okP | yes  | arodata_okP and memnorm
   | strlen       | aj_strlen_at_xm       | astrlen_realizes_xm        | rom_view    | yes  | rom_view (literal, A and B)
   | strlen       | aj_strlen_at_xro      | astrlen_realizes_xro       | arodata_okP | no   | arodata_okP, no memnorm
   | strlen       | aj_strlen_at_xrom     | astrlen_realizes_xrom      | arodata_okP | yes  | arodata_okP and memnorm
   | free         | aj_free_x_m           | afree_realizes_x           | none        | no   | a symbolic state at the free wrapper
   | free         | aj_free_x_ct_m        | afree_realizes_x           | none        | no   | that, the trace on call_trace (tail call)
   | free         | aj_free_at_x_m        | afree_realizes_x           | none        | no   | a concrete state at the free wrapper
   | free         | aj_free_at_x_ct_m     | afree_realizes_x           | none        | no   | that, the trace on call_trace (tail call)
   | malloc       | aj_malloc_x_m         | amalloc_realizes_x         | none        | no   | a symbolic state at the malloc wrapper
   | malloc       | aj_malloc_x_ct_m      | amalloc_realizes_x         | none        | no   | that, the trace on call_trace
   | malloc       | aj_malloc_at_x_m      | amalloc_realizes_x         | none        | no   | a concrete state at the malloc wrapper
   | malloc       | aj_malloc_at_x_ct_m   | amalloc_realizes_x         | none        | no   | that, the trace on call_trace
   | poison       | aj_poison_at_x_m      | apoison_realizes_x         | none        | yes  | a concrete state at the poison call
   | poison       | aj_poison_x_m         | apoison_realizes_x         | none        | yes  | a symbolic state at the callee entry
   | unpoison     | aj_unpoison_at_x_m    | aunpoison_realizes_x       | none        | yes  | a concrete state at the unpoison
   |              |                       |                            |             |      | call, b in the ghost set Hpc
   | unpoison     | aj_unpoison_x_m       | aunpoison_realizes_x       | none        | yes  | a symbolic state at the callee
   |              |                       |                            |             |      | entry, b in the ghost set Hpc
   Design note (h-hpreset-7 12:37Z): a call rule exists in the form the walk can supply; nobody proves a general
   rom_view -> arodata_okP bridge (it is false in general: h-hpreset-7's s911_rob_unsat_A). A script checked, for
   strcmp and strlen, that _xro differs from YGcallMx.v's _x only in the one read-only premise, that _xrom differs from
   _xro only in the keep, and that aj_strlen_at_xm / aj_strlen_at_xrom (and their texts) differ only in the one
   premise; the commit message of the commit that added section 9 has its output.

   WHY A SEPARATE FILE AND NOT YGcallMx.v, AND WHY YAkMemnorm: YAjMemnorm.v Requires lib/Lib/Mem.v, Mem.v Requires
   PropExec, and PropExec Exports LiaTwx2, whose `Ltac lia ::=` (LiaTwx2.v:187) changes lia for every proof after the
   Require. So the keeps are kept out of YGcallMx.v (whose proofs, like the image walks FCm0s / FCm1s, run on the
   stock lia) and are stated over YAkMemnorm.memnorm. This file Requires neither YAjMemnorm, nor MemNorm.v, nor
   lib/Lib/Mem.v (nor lib/A/PRH_Base.v), so lib/Lib/LiaTwx2.v is not in its Require closure; lib/Spec/PresetRodata.v
   Requires only Stdlib, BvBase / MemImageType and YK11 / YG0f / YG0n, all already Required here. The lia redefinitions
   that are in it are the engine's own (YM03.v:182, YM05.v:63, YM04.v:36), all already in YGcallMx.v's / YGcallSx.v's
   closure. The facts it needs from those files are copied below, each named at its source: ak_wview_absent_seg
   (YAjMemnorm.v:45), ak_wview_not_ro (Lib/Mem.v:298), cj_drop_ak / cj_same_ak (MemNorm.v:527 / :541). No YAkMemnormJ
   bridge is in this file: it would Require YAjMemnorm.

   Numerals: 1, 3, 4, 10, 11, 12 are RISC-V register numbers (WORD); 16 (stack alignment), 2 (the factor of the
   2 * ESTACK window), 256 (byte modulus), 0 and 10 (frame classes), 8 (shadow granule), 2 ^ 32, 2 ^ 63, 2 ^ 64 are
   LENGTH / DERIVED constants of the texts copied from YGcallMx.v / YGcallSx.v / ExvB_StrcmpRo.v / ExwB_StrlenRo.v;
   4096 (= ESTACK, = LPS page_size) and 16384 (= ASTACK, in the copied YGcallSx.v proofs) are DERIVED. In section 10
   (YGcallx.v's statements verbatim): 1, 2, 3, 4, 10 are register numbers and 12 (ENOMEM) / 1 (the out-of-memory
   byte) are stored values (WORD); 0, 16 (stack alignment) and 4096 (cgif's lowest block address) are LENGTH; 64
   (fs_frame_bytes' base, fs_frame_bytes_ok) is LENGTH. In section 11 (YGcallPx.v's statements and proofs): 1, 2, 3,
   4, 10, 11 are register numbers (WORD); 0 is WORD (an addressable granule's shadow value) and LENGTH (the frame offset
   bound); 8 (shadow granule) and 2 ^ 64 are LENGTH; 16 (stack and block alignment), 2 (16 / 8) and 4096 (= ESTACK)
   are DERIVED.
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0s YG0q YG0t YF0v FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YP0a YP0d YP0c YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
(* the step relation over a world relation (SRrG) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.

(* ---------------------------------------------------------------------------- *)
(* 1. The texts with the keep (families 1 and 2).                                *)
Section texts. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* YGcallMx.v:81 aintrin_realizes_x, plus the keep *)
Definition aintrin_realizes_xm (op : memop) (pc : Z) : Prop :=
forall ly S Hp W regs mem md d x n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

(* YGcallMx.v:125 abcmp_realizes_x, plus the keep *)
Definition abcmp_realizes_xm (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> src_ok segs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

(* FCiface.v:51 astack_malloc_realizes_x, plus the keep *)
Definition astack_malloc_realizes_xm (cid : Z) : Prop :=
forall ly S Hp W regs mem md pos S',
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
count_cid cid (frames S) < fs_frames cid ->
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
SRr segs W (cfg_at segs (pc_stack_malloc (as_code B) cid) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S' Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly cid pos) /\
zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) /\
(forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

(* FCiface.v:69 aset_shadow_realizes_x, plus the keep *)
Definition aset_shadow_realizes_xm (pc v : Z) : Prop :=
forall ly S Hp W regs mem md cid pos q n,
ecall_pre_x segs B ARx ly S Hp W regs mem md -> In (cid, pos) (frames S) ->
getr regs 10 = w64 q -> getr regs 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr ly cid pos) <= q -> q + n <= shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

(* forgetting the keep gives the plain texts (a row that proves the _xm text fills the plain instance field) *)
Lemma aintrin_realizes_xm_forget : forall op pc, aintrin_realizes_xm op pc -> aintrin_realizes_x segs B ARx op pc.
Proof.
intros op pc AI ly S Hp W regs mem md d x n HPRE. intros.
eapply SRr_mono; [apply (AI ly S Hp W regs mem md d x n HPRE); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & K1 & K2 & K3 & K4 & K5 & K6 & K7 & _).
split; [reflexivity|]. exists regs', mem', md'.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7))))))).
Qed.

Lemma abcmp_realizes_xm_forget : forall pc, abcmp_realizes_xm pc -> abcmp_realizes_x segs B ARx pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n HPRE. intros.
eapply SRr_mono; [apply (AM ly S Hp W regs mem md x y n HPRE); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & K1 & K2 & K3 & K4 & K5 & K6 & K7 & _).
split; [reflexivity|]. exists regs', mem', md', v.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7))))))).
Qed.

Lemma astack_malloc_realizes_xm_forget : forall cid,
astack_malloc_realizes_xm cid -> astack_malloc_realizes_x segs B ARx cid.
Proof.
intros cid ASM ly S Hp W regs mem md pos S' HPRE Hcnt Hpath.
eapply SRr_mono; [exact (ASM ly S Hp W regs mem md pos S' HPRE Hcnt Hpath)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & _).
split; [reflexivity|]. exists regs', mem', md'.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 (conj K7 (conj K8 K9))))))))).
Qed.

Lemma aset_shadow_realizes_xm_forget : forall pc v,
aset_shadow_realizes_xm pc v -> aset_shadow_realizes_x segs B ARx pc v.
Proof.
intros pc v ASS ly S Hp W regs mem md cid pos q n HPRE Hin G10 G11 Hn Hq1 Hq2.
eapply SRr_mono; [exact (ASS ly S Hp W regs mem md cid pos q n HPRE Hin G10 G11 Hn Hq1 Hq2)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & K1 & K2 & K3 & K4 & K5 & K6 & K7 & _).
split; [reflexivity|]. exists regs', mem', md'.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7))))))).
Qed.
End texts.

(* ---------------------------------------------------------------------------- *)
(* 2. The call-site keeps of family 1 (YGcallMx.v Section mx / Section l).       *)
Section rules. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* aj_intrin_at_xm over a journal at any world relation R: the call keeps the world (W2 = W), so the journal's world
   conjunct passes through unchanged; aj_intrin_at_xm is its case R := wle *)
Lemma aj_intrin_at_xmR : forall (R : world segs -> world segs -> Prop) op pc, aintrin_realizes_xm segs B ARx op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R op pc AI W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
destruct (awr_byte_present_xR (SK := SK) segs B PST ARx LAWS R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a
  HJ Hw) as [Hpa Hno]. rewrite Hsp'.
split; [apply apresent_writable; exact Hpa | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc Hpc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W
memT mdc k mem2 md2 (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

(* YGcallMx.v:213 aj_intrin_at_x, plus the keep: the text's mem' is the call's mem2 *)
Lemma aj_intrin_at_xm : forall op pc, aintrin_realizes_xm segs B ARx op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. intros op pc. exact (aj_intrin_at_xmR (@wle segs) op pc). Qed.

(* aj_intrin_at_xm_fr over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_intrin_at_xm_fr is its case R := wle *)
Lemma aj_intrin_at_xm_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall op pc, aintrin_realizes_xm segs B ARx op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n ->
   (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) /\
   ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans op pc AI W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HFR : forall a, wr_fp_frame FP S lyc a -> apresent (w_H W) memT a /\ ~ aowned B lyc Sc a).
{ intros a (_ & cid & pos & Hin & Hr).
  assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (alx_frames segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos HAR Hin') as (_ & _ & Hb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (Hb a Hr). }
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns]. rewrite Hsp'.
destruct Hw as [Hw | Hw].
- destruct (awr_byte_present_xR (SK := SK) segs B PST ARx LAWS R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a HJ Hw)
    as [Hpa Hno].
  split; [apply apresent_writable; exact Hpa | auto].
- destruct (HFR a Hw) as [Hpa Hno]. split; [apply apresent_writable; exact Hpa | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc Hpc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [| split; [exact HP|]; split; [exact Hres|]; split; [exact Heff|]; split; [exact Hfr|];
  split; [exact Hpres2 | exact Hmn]].
set (memi := fun xw : word => if wr_fp_frame_dec FP S lyc (bv_unsigned xw) then memT xw else mem2 xw).
assert (Hnh : forall xw : word, wr_fp_frame FP S lyc (bv_unsigned xw) -> w_H W xw = false).
{ intros xw Hw. destruct (HFR _ Hw) as [[Hh _] _]. rewrite Z_to_bv_bv_unsigned in Hh. exact Hh. }
assert (Ewd : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. exact Ha. }
assert (Ei_fr : forall a, 0 <= a < 2 ^ 64 -> wr_fp_frame FP S lyc a -> aview segs (w_H W) memi a = aview segs (w_H W) memT a).
{ intros a Ha Hw. apply aview_eq_of. unfold mrestrict, memi.
  destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [_|Hn']; [reflexivity|].
  rewrite (Ewd a Ha) in Hn'. contradiction. }
assert (Ei_nf : forall a, 0 <= a < 2 ^ 64 -> ~ wr_fp_frame FP S lyc a -> aview segs (w_H W) memi a = aview segs (w_H W) mem2 a).
{ intros a Ha Hw. apply aview_eq_of. unfold mrestrict, memi.
  destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [Hy|_]; [|reflexivity].
  rewrite (Ewd a Ha) in Hy. contradiction. }
assert (HARi : ARx lyc Sc Hpc W memi md2).
{ apply (alx_frame segs B ARx LAWS lyc Sc Hpc W mem2 md2 memi md2 HAR2).
  - intros a Ha Ho. apply Ei_nf; [exact Ha|]. intros Hw. exact (proj2 (HFR a Hw) Ho).
  - intros a Hv. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [Hw|Hw].
    + assert (E1 : aview segs (w_H W) memi a = aview segs (w_H W) memT a).
      { apply aview_eq_of. unfold mrestrict, memi.
        destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [_|Hn']; [reflexivity | contradiction]. }
      rewrite E1. pose proof (aview_some_of_apresent segs (w_H W) memT _ (proj1 (HFR _ Hw))) as Hs.
      unfold aview, mbyte in Hs |- *. rewrite Z_to_bv_bv_unsigned in Hs. exact Hs.
    + assert (E1 : aview segs (w_H W) memi a = aview segs (w_H W) mem2 a).
      { apply aview_eq_of. unfold mrestrict, memi.
        destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [Hy|_]; [contradiction | reflexivity]. }
      rewrite E1. exact Hv.
  - reflexivity. - reflexivity. - reflexivity.
  - intros a _ Hh. unfold memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (w64 a))) as [Hw|Hw]; [|reflexivity].
    rewrite (Hnh _ Hw) in Hh. discriminate. }
assert (HJi : ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memi md2 k).
{ apply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k
    memi md2 (fun a => (d <= a < d + n /\ ~ wr_fp_frame FP S lyc a) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc Hpc own HJ).
  - intros a Ha Hna. destruct (wr_fp_frame_dec FP S lyc a) as [Hw|Hw].
    + exact (Ei_fr a Ha Hw).
    + rewrite (Ei_nf a Ha Hw). apply (Hfr a Ha); intros H'; apply Hna; [left; split; [exact H' | exact Hw] | right; exact H'].
  - intros a Hpa. pose proof (Hpres2 a Hpa) as (Hh2 & Hb2). destruct Hpa as (Hh & Hb). split; [exact Hh|].
    unfold memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))); [exact Hb | exact Hb2].
  - exact Hsame.
  - intros a [[Ha Hw] | Ha]; left.
    + destruct (proj1 (Hdest a Ha)) as [H'|H']; [exact H' | contradiction].
    + left. zlia.
  - exact HARi.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
apply (ajournal_x_frame_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memi md2 k
  mem2 md2 HJi).
- intros xw Hxw. unfold mrestrict, memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned xw)) as [Hy|_]; [contradiction | reflexivity].
- intros xw. unfold mrestrict, memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned xw)) as [Hy|_]; [|exact (fun H => H)].
  rewrite (Hnh xw Hy). intros Hm. destruct (memT xw) as [b|] eqn:Eb; [|exfalso; apply Hm; first [exact Eb | reflexivity]].
  assert (Hpa : apresent (w_H W) memT (bv_unsigned xw)).
  { rewrite <- (Z_to_bv_bv_unsigned 64 xw) in Eb. split; [rewrite Z_to_bv_bv_unsigned; exact (Hnh xw Hy) | exists b; exact Eb]. }
  destruct (Hpres2 _ Hpa) as [_ (b' & Hb')]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
- intros xw Hh. unfold memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned xw)) as [Hy|_]; [|reflexivity].
  rewrite (Hnh xw Hy) in Hh. discriminate.
- apply same_but_materialized_refl.
Qed.

(* YGcallMx.v:272 aj_intrin_at_x_fr, plus the keep: mem2 is the text's mem' (memi below is the journal's only) *)
Lemma aj_intrin_at_xm_fr : forall op pc, aintrin_realizes_xm segs B ARx op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n ->
   (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) /\
   ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_intrin_at_xm_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_bcmp_at_xm over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_bcmp_at_xm is its case R := wle *)
Lemma aj_bcmp_at_xmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, abcmp_realizes_xm segs B ARx pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans pc AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc Hpc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

(* YGcallMx.v:448 aj_bcmp_at_x, plus the keep *)
Lemma aj_bcmp_at_xm : forall pc, abcmp_realizes_xm segs B ARx pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_bcmp_at_xmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End rules.

(* ---------------------------------------------------------------------------- *)
(* 3. The call-site keeps of family 2 (YGcallSx.v Section x).                    *)
Section srule. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Local Abbreviation code := (as_code B).
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
(* YGcallSx.v:68 SMX *)
Hypothesis SMX : forall ly S Hp W mem md cid, ARx ly S Hp W mem md -> 0 <= cid <= 10 ->
  count_cid cid (frames S) < fs_frames cid ->
  exists pos S', apath (stack_malloc cid S) [] (PFake cid pos, S') /\ (exists f, S' = set_fs f S) /\
    frames S' = (cid, pos) :: frames S /\ ~ In (cid, pos) (frames S).

(* aj_stack_malloc_at_xm over a journal at any reflexive and transitive world relation R: the call keeps the world
   (W2 = W), its own journal (W to W) is at R by reflexivity and composes into the caller's by transitivity; the
   call's own journal in the post stays at wle. aj_stack_malloc_at_xm is its case R := wle. *)
Lemma aj_stack_malloc_at_xmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall cid, astack_malloc_realizes_xm segs B ARx cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own) lyc S2 Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept_x segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
ajournal_x segs B [] ARx ESTACK (sp0 + o) [] lyc Sc Hpc W memT mdc [(cid, pos)] lyc S2 Hpc W mem2 md2 0 /\
(exists f, S2 = set_fs f Sc) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans cid ASM Hcid W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_pres HJ) as Hpres.
pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
destruct (SMX lyc Sc Hpc W memT mdc cid HAR Hcid Hcnt) as (pos & S2 & Hpath & (f & ES2) & Hfrs2 & Hfresh).
eapply SRr_mono; [exact (ASM lyc Sc Hpc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2 & Hmn).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal_x segs B [] ARx ESTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [(cid, pos)] lyc S2 Hpc W mem2 md2 0).
{ eapply (call_effect_journal_x segs B ARx LAWS segs_low errno_low OWNLOW ESTACK lyc Sc Hpc W regsT memT mdc lyc S2 Hpc W
    mem2 md2 (fun _ => False) [] [(cid, pos)] 0 []);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR
  | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | | ].
  - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p n i Hp0 Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp0.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
  - rewrite ES2. apply wild_part_same. }
(* the call's own journal at R: the world is W at both ends *)
assert (HJ1R : ajournal_xR (SK := SK) segs B [] ARx R ESTACK (spZ regsT) [] lyc Sc Hpc W memT mdc [(cid, pos)] lyc S2 Hpc W
  mem2 md2 0).
{ exact (ajxR_intro (ajx_ar HJ1) (ajx_ly HJ1) (ajx_secs HJ1) (R_refl W) (ajx_io HJ1) (ajx_frs HJ1) (ajx_nev HJ1)
    (ajx_k HJ1) (ajx_hi HJ1) (ajx_blk HJ1) (ajx_img HJ1) (ajx_frm HJ1) (ajx_gone HJ1) (ajx_pres HJ1) (ajx_stk HJ1)
    (ajx_extra HJ1) (ajx_qt HJ1) (ajx_wild HJ1)). }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1R. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
  eapply (ajournal_x_subR segs B PST ARx LAWS segs_low R R_trans);
  [exact HJ | exact (ajournal_xwR_nil_pst segs B ARx R PST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1R) | zlia | zlia
  | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
rewrite Hsp' in HJ1. split; [| split; [exact HJ1 | split; [exists f; exact ES2 | exact Hmn]]].
eapply (acall_kept_of_journal_x segs B ARx segs_low); [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
intros b m i Hb Hi _. rewrite Eab2. exact Hb.
Qed.

(* YGcallSx.v:73 aj_stack_malloc_at_x, plus the keep *)
Lemma aj_stack_malloc_at_xm : forall cid, astack_malloc_realizes_xm segs B ARx cid -> 0 <= cid <= 10 ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid cid (frames Sc) < fs_frames cid ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_stack_malloc code cid)) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own) lyc S2 Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc cid pos) /\
ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
zero_shadow (aview segs (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
rdword (aview segs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) /\
(forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> apresent (w_H W) mem2 a) /\
acall_kept_x segs B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
ajournal_x segs B [] ARx ESTACK (sp0 + o) [] lyc Sc Hpc W memT mdc [(cid, pos)] lyc S2 Hpc W mem2 md2 0 /\
(exists f, S2 = set_fs f Sc) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_stack_malloc_at_xmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_set_shadow_at_xm over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_set_shadow_at_xm is its case R := wle *)
Lemma aj_set_shadow_at_xmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc v, aset_shadow_realizes_xm segs B ARx pc v ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k cid pos q n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R _ _ pc v ASS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc Hpc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2 & Hpmono & Hmn).
destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W
memT mdc k mem2 md2 (fun a => q <= a < q + n) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha Hna).
- exact Hpmono.
- exact Hsame.
- intros a Ha. left. unfold awr_byte, in_frames. right. right. right. exists cid, pos.
split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. zlia.
- exact HAR2.
- reflexivity.
- reflexivity.
- zlia.
- exact Hfrs.
- exact HQT.
- reflexivity. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr | exact Hmn].
Qed.

(* YGcallSx.v:146 aj_set_shadow_at_x, plus the keep: the text's mem' is the call's mem2 *)
Lemma aj_set_shadow_at_xm : forall pc v, aset_shadow_realizes_xm segs B ARx pc v ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k cid pos q n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_set_shadow_at_xmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End srule.

(* ---------------------------------------------------------------------------- *)
(* 4. The lifts ARx -> ARx /\ P (YGcallMx.v Section cj; YGcallScf.v:119): ARcfx := ARcf /\ xs_placed_cf.            *)
Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable P : alayout -> astate -> Prop.
Local Abbreviation ARP := (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S).

Lemma aintrin_realizes_xm_conj : forall op pc, aintrin_realizes_xm segs B ARx op pc -> aintrin_realizes_xm segs B ARP op pc.
Proof.
intros op pc AI ly S Hp W regs mem md d x n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AI ly S Hp W regs mem md d x n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

Lemma abcmp_realizes_xm_conj : forall pc, abcmp_realizes_xm segs B ARx pc -> abcmp_realizes_xm segs B ARP pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AM ly S Hp W regs mem md x y n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md', v. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

(* the set_shadow text keeps S (no set_fs), so its lift needs no law on P, as aintrin_realizes_xm_conj *)
Lemma aset_shadow_realizes_xm_conj : forall pc v,
aset_shadow_realizes_xm segs B ARx pc v -> aset_shadow_realizes_xm segs B ARP pc v.
Proof.
intros pc v ASS ly S Hp W regs mem md cid pos q n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (ASS ly S Hp W regs mem md cid pos q n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.
End cj.

Section cjs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* YGcallScf.v:119 astack_malloc_realizes_x_conj, for the text with the keep *)
Lemma astack_malloc_realizes_xm_conj : forall segs B
(ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
(P : alayout -> astate -> Prop) cid,
(forall ly S f, P ly S -> P ly (set_fs f S)) ->
astack_malloc_realizes_xm segs B ARx cid ->
astack_malloc_realizes_xm segs B (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S) cid.
Proof.
intros segs B ARx P cid HPk ASM ly S Hp W regs mem md pos S' ((HAR & HP) & R) Hcnt Hpath.
destruct (YGcallScf.stack_malloc_apath_set_fs S cid pos S' Hpath) as (f & ES').
assert (HP' : P ly S') by (rewrite ES'; exact (HPk ly S f HP)).
eapply SRr_mono; [exact (ASM ly S Hp W regs mem md pos S' (conj HAR R) Hcnt Hpath)|].
cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & Hc & HAR' & Rest).
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [exact (conj HAR' HP') | exact Rest].
Qed.
End cjs.

(* ---------------------------------------------------------------------------- *)
(* 5. Copied facts (this file Requires neither YAjMemnorm nor lib/Lib/Mem.v nor MemNorm.v; header).              *)

(* copied from YAjMemnorm.v:45 wview_absent_seg: an overlay byte made where wview is defined lies in a segment *)
Lemma ak_wview_absent_seg : forall segs m a, wview segs m a <> None -> m a = None ->
  find_segment segs (bv_unsigned a) 1 <> None.
Proof.
  intros segs m a W E. unfold wview in W. rewrite E in W.
  destruct (find_segment segs (bv_unsigned a) 1); [discriminate|]. exfalso. apply W. reflexivity.
Qed.

(* copied from lib/Lib/Mem.v:298 wview_not_ro, over YAkMemnorm.ro_addr *)
Lemma ak_wview_not_ro : forall segs m a, wview segs m a <> None -> m a = None -> MN.ro_addr segs a = false.
Proof.
  intros segs m a H Hm. unfold wview, MN.ro_addr in *. rewrite Hm in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|reflexivity].
  destruct (seg_writable seg); [reflexivity|]. exfalso; apply H; reflexivity.
Qed.

(* MemNorm.v:527 cj_drop and :541 cj_same, body for body over YAkMemnorm.ro_addr; MemNorm.cj_same segs m m' converts
   to cj_same_ak segs m m' *)
Definition cj_drop_ak (segs : list Segment) (a : word) : bool :=
  orb (MN.ro_addr segs a)
      (match find_segment segs (bv_unsigned a) 1 with
       | Some _ => false
       | None => Z.leb TASK_SIZE (bv_unsigned a)
       end).

Definition cj_same_ak (segs : list Segment) (m m' : word -> option byte) : Prop :=
  forall a, cj_drop_ak segs a = true -> m' a = m a.

(* ---------------------------------------------------------------------------- *)
(* 6. memnorm across one symbolic-runner phase (family 2; evidence in the header). *)
Lemma in_wrange_dec : forall E rs a, {in_wrange E rs a} + {~ in_wrange E rs a}.
Proof.
intros E rs a.
destruct (Exists_dec (fun r => YP09.base_val E (YP09.r_base r) + YP09.r_wlo r <= a < YP09.base_val E (YP09.r_base r) + YP09.r_whi r) rs)
  as [Hx|Hx].
- intros r. destruct (Z_le_dec (YP09.base_val E (YP09.r_base r) + YP09.r_wlo r) a);
  [destruct (Z_lt_dec a (YP09.base_val E (YP09.r_base r) + YP09.r_whi r))|]; [left; lia | right; lia | right; lia].
- left. apply Exists_exists in Hx. exact Hx.
- right. intros Hf. apply Hx. apply Exists_exists. exact Hf.
Qed.

Section fr. Context {fx : YK11.FPState}.
Lemma memnorm_frame_of : forall (segs : list Segment) (H : word -> bool) E ss (ms : machine_state) (m' : word -> option byte), MN.memnorm segs (ms_mem ms) -> st_ok segs E ss (restrict H ms) -> frame_of E (ss_mem ss) (ms_mem ms) m' -> MN.memnorm segs m'.
Proof.
intros segs H E ss ms m' (Hi & Ht) HS HF.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & ROK & _) & _).
(* every byte frame_of lets change is writable_at the restricted overlay *)
assert (HW : forall a : word, in_wrange E (ss_mem ss) (bv_unsigned a) -> wview segs (mrestrict H (ms_mem ms)) a <> None).
{ intros a (r & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) ROK r Hin) as Hok. unfold region_ok in Hok.
  destruct Hok as (_ & _ & Hw & _).
  specialize (Hw (bv_unsigned a - YP09.base_val E (YP09.r_base r)) ltac:(lia)).
  unfold writable_at in Hw.
  replace (YP09.base_val E (YP09.r_base r) + (bv_unsigned a - YP09.base_val E (YP09.r_base r))) with (bv_unsigned a) in Hw by lia.
  rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
assert (HN : forall a : word, ms_mem ms a = None -> mrestrict H (ms_mem ms) a = None).
{ intros a Ea. unfold mrestrict. destruct (H a); [reflexivity | exact Ea]. }
split.
- intros a b Ea. destruct (ms_mem ms a) as [b0|] eqn:E0; [exact (Hi a b0 E0)|].
  destruct (in_wrange_dec E (ss_mem ss) (bv_unsigned a)) as [Hin|Hout].
  + exact (ak_wview_not_ro segs (mrestrict H (ms_mem ms)) a (HW a Hin) (HN a E0)).
  + rewrite (HF a Hout), E0 in Ea. discriminate.
- intros a b Ea. destruct (ms_mem ms a) as [b0|] eqn:E0; [exact (Ht a b0 E0)|].
  destruct (in_wrange_dec E (ss_mem ss) (bv_unsigned a)) as [Hin|Hout].
  + left. exact (ak_wview_absent_seg segs (mrestrict H (ms_mem ms)) a (HW a Hin) (HN a E0)).
  + rewrite (HF a Hout), E0 in Ea. discriminate.
Qed.
End fr.

(* ---------------------------------------------------------------------------- *)
(* 7. Family 3: helpers.                                                          *)

(* a run that leaves every cj_drop address unchanged keeps memnorm (the MemNorm cj-kit row route; the task_mem half
   is MemNorm.v:950 task_mem_same_cj's proof) *)
Lemma memnorm_same_cj : forall segs m m',
  MN.memnorm segs m -> cj_same_ak segs m m' -> MN.memnorm segs m'.
Proof.
intros segs m m' (Hi & Ht) Hs. split.
- intros a b Ea. destruct (cj_drop_ak segs a) eqn:D.
  + rewrite (Hs a D) in Ea. exact (Hi a b Ea).
  + unfold cj_drop_ak in D. apply orb_false_iff in D as [D1 _]. exact D1.
- intros a b Ea. destruct (cj_drop_ak segs a) eqn:D.
  + rewrite (Hs a D) in Ea. exact (Ht a b Ea).
  + unfold cj_drop_ak in D. apply orb_false_iff in D as [_ D2]. revert D2.
    destruct (find_segment segs (bv_unsigned a) 1) as [sg|]; intros D2; [left; discriminate|].
    right. apply Z.leb_gt in D2. exact D2.
Qed.

(* a post whose new bytes are all wview-defined at the call keeps memnorm (enough for memcpy / strcmp / bcmp, NOT for
   malloc: an mmap grant is not wview-defined beforehand) *)
Lemma memnorm_new_wview : forall segs (m m' : word -> option byte),
  MN.memnorm segs m ->
  (forall (a : word) b, m' a = Some b -> m a = None -> wview segs m a <> None) ->
  MN.memnorm segs m'.
Proof.
intros segs m m' (Hi & Ht) HW. split.
- intros a b Ea. destruct (m a) as [b0|] eqn:E0; [exact (Hi a b0 E0)|].
  exact (ak_wview_not_ro segs m a (HW a b Ea E0) E0).
- intros a b Ea. destruct (m a) as [b0|] eqn:E0; [exact (Ht a b0 E0)|].
  left. exact (ak_wview_absent_seg segs m a (HW a b Ea E0) E0).
Qed.

(* LPS (State.v:4346 region_free, :4341 iv_overlap): a range region_free clears does not overlap a listed extent *)
Lemma region_free_iv_overlap : forall (l : list (word * word)) (lo n : word) p,
  region_free l lo n = true -> In p l -> iv_overlap lo n (fst p) (snd p) = false.
Proof.
induction l as [|[a0 s0] l IH]; intros lo n p Hf Hin; [destruct Hin|].
cbn [region_free] in Hf. apply andb_prop in Hf as [H1 H2]. destruct Hin as [Ep|Hin].
- subst p. cbn [fst snd]. apply negb_true_iff in H1. exact H1.
- exact (IH lo n p H2 Hin).
Qed.

(* the guard of a fresh grant clears its first list (Mmap.v:1566-1570: vm_reserved h ++ vm_maps h) *)
Lemma region_free_app_l : forall (l1 l2 : list (word * word)) (lo n : word),
  region_free (l1 ++ l2) lo n = true -> region_free l1 lo n = true.
Proof.
induction l1 as [|[a0 s0] l1 IH]; intros l2 lo n Hf; [reflexivity|].
cbn [region_free app] in Hf |- *. apply andb_prop in Hf as [H1 H2]. rewrite H1. exact (IH l2 lo n H2).
Qed.

(* the grant range of a region_free check against segments_reserved segs (Run.v:211-217) holds no segment byte *)
Lemma region_free_reserved_off_segs : forall (segs : list Segment) (a n x : word),
  (forall s, In s segs -> 0 < Z.of_N (seg_size s) -> Z.of_N (seg_base s) + Z.of_N (seg_size s) + page_size <= 2 ^ 64) ->
  region_free (segments_reserved segs) a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  find_segment segs (bv_unsigned x) 1 = None.
Proof.
intros segs a n x Hsz Hf Hx.
destruct (find_segment segs (bv_unsigned x) 1) as [s|] eqn:Ef; [exfalso | reflexivity].
destruct (find_segment_some_spec segs (bv_unsigned x) 1 s Ef) as (Hin & Hb & Ht).
pose proof (bv_unsigned_in_range _ x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
pose proof (N2Z.is_nonneg (seg_base s)) as Hb0. pose proof (N2Z.is_nonneg (seg_size s)) as Hs0.
specialize (Hsz s Hin ltac:(lia)). unfold page_size in Hsz.
pose proof (region_free_iv_overlap _ a n _ Hf (in_map segment_reservation segs s Hin)) as Hov.
unfold segment_reservation, page_round_down_Z, page_round_up_Z, page_size in Hov. cbn [fst snd] in Hov.
set (t := Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4096 - 1) in Hov.
pose proof (Z.div_mod (Z.of_N (seg_base s)) 4096 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (Z.of_N (seg_base s)) 4096 ltac:(lia)) as M1.
pose proof (Z.div_mod t 4096 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound t 4096 ltac:(lia)) as M2.
assert (Et : t = Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4096 - 1) by reflexivity. clearbody t.
unfold iv_overlap in Hov. rewrite !Z_to_bv_unsigned in Hov. unfold bv_wrap in Hov. change (bv_modulus 64) with (2 ^ 64) in Hov.
rewrite (Z.mod_small (Z.of_N (seg_base s) / 4096 * 4096)) in Hov by lia.
rewrite (Z.mod_small (t / 4096 * 4096 - Z.of_N (seg_base s) / 4096 * 4096)) in Hov by lia.
apply andb_false_iff in Hov as [Hv|Hv]; apply Z.ltb_ge in Hv; lia.
Qed.

(* the same at the engine's segs_low (the Section hypothesis of YCbqG.v / YGcallMx.v / YGcallSx.v): the last byte of a
   nonempty segment is in_img, hence below kLowMemEnd, far below 2 ^ 64 - page_size *)
Lemma region_free_reserved_off_segs_low : forall (segs : list Segment),
  (forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
  forall (a n x : word),
  region_free (segments_reserved segs) a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
  find_segment segs (bv_unsigned x) 1 = None.
Proof.
intros segs Hlow a n x Hf Hx. apply (region_free_reserved_off_segs segs a n x); [|exact Hf | exact Hx].
intros s Hin Hsz.
assert (Hz : in_img segs (Z.of_N (seg_base s) + Z.of_N (seg_size s) - 1)) by (exists s; split; [exact Hin | lia]).
pose proof (Hlow _ Hz) as Hb. unfold page_size, kLowMemEnd in *. lia.
Qed.


(* ---------------------------------------------------------------------------- *)
(* 8. Family 1b: strcmp / strlen in the read-only-premise form (header).         *)

Section strtexts. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.

(* VERBATIM ExvB_StrcmpRo.v:43-67 (blob af14c24f474d): YGcallMx.v:149 astrcmp_realizes_x with rom_view -> arodata_okP *)
Definition astrcmp_realizes_xro (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y kx ky,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
first_byte segs W mem x (kx + 1) 0 kx -> first_byte segs W mem y (ky + 1) 0 ky ->
src_ok segs W regs mem x (kx + 1) -> src_ok segs W regs mem y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a <= y + ky -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (kx + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* VERBATIM ExwB_StrlenRo.v:45-64 (blob d38c23bec721): YGcallMx.v:103 astrlen_realizes_x with rom_view -> arodata_okP *)
Definition astrlen_realizes_xro (pc : Z) : Prop :=
forall ly S Hp W regs mem md x k,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* astrcmp_realizes_xro, plus the keep *)
Definition astrcmp_realizes_xrom (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y kx ky,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
first_byte segs W mem x (kx + 1) 0 kx -> first_byte segs W mem y (ky + 1) 0 ky ->
src_ok segs W regs mem x (kx + 1) -> src_ok segs W regs mem y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a <= y + ky -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (kx + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

(* astrlen_realizes_xro, plus the keep *)
Definition astrlen_realizes_xrom (pc : Z) : Prop :=
forall ly S Hp W regs mem md x k,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

Lemma astrcmp_realizes_xrom_forget : forall pc, astrcmp_realizes_xrom pc -> astrcmp_realizes_xro pc.
Proof.
intros pc AC ly S Hp W regs mem md x y kx ky HPRE. intros.
eapply SRr_mono; [apply (AC ly S Hp W regs mem md x y kx ky HPRE); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & K1 & K2 & K3 & K4 & K5 & K6 & K7 & _).
split; [reflexivity|]. exists regs', mem', md', v.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7))))))).
Qed.

Lemma astrlen_realizes_xrom_forget : forall pc, astrlen_realizes_xrom pc -> astrlen_realizes_xro pc.
Proof.
intros pc AS ly S Hp W regs mem md x k HPRE. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md x k HPRE); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & K1 & K2 & K3 & K4 & K5 & K6 & _).
split; [reflexivity|]. exists regs', mem', md'.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 K6)))))).
Qed.
End strtexts.

(* the lifts ARx -> ARx /\ P (YGcallMx.v:589 / :605), for the texts with the keep *)
Section strcj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.
Variable P : alayout -> astate -> Prop.
Local Abbreviation ARP := (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S).

Lemma astrcmp_realizes_xrom_conj : forall pc,
  astrcmp_realizes_xrom segs B ARx rlo rhi pc -> astrcmp_realizes_xrom segs B ARP rlo rhi pc.
Proof.
intros pc AC ly S Hp W regs mem md x y kx ky [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AC ly S Hp W regs mem md x y kx ky (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md', v. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

Lemma astrlen_realizes_xrom_conj : forall pc,
  astrlen_realizes_xrom segs B ARx rlo rhi pc -> astrlen_realizes_xrom segs B ARP rlo rhi pc.
Proof.
intros pc AS ly S Hp W regs mem md x k [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md x k (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.
End strcj.

(* the call-site keeps: the consumers' aj_strcmp_at_xro (ExvB_StrcmpRo.v:74) / aj_strlen_at_xro (ExwB_StrlenRo.v:72),
   statement and proof, with the keep an implication in the conclusion *)
Section strrules. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.


(* aj_strcmp_at_xro over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strcmp_at_xro is its case R := wle *)
Lemma aj_strcmp_at_xroR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrcmp_realizes_xro segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (kx + 1) 0 kx -> first_byte segs W memT y (ky + 1) 0 ky ->
src_ok segs W regsT memT x (kx + 1) -> src_ok segs W regsT memT y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + ky -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kx + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky o raw
HJ Ha0 Ha1 Hx0 Hy0 Hkx0 Hkx32 Hxk Hky0 Hky32 Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw
Hfx Hfy Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy Htx Hty Hrom.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AC lyc Sc Hpc W regsT memT mdc x y kx ky HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hkx0 Hkx32 Hxk Hky0 Hky32 Hyk
Hfx Hfy Hsx Hsy ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy Htx Hty Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.

(* MOVED here from B/Prog/ExvB_StrcmpRo.v:74 (blob af14c24f474d), statement and proof verbatim but for the text's
   arguments (the text is this file's global astrcmp_realizes_xro): no memnorm keep, for a walk that needs only the
   rodata swap (h-hpreset-7 12:41Z) *)
Lemma aj_strcmp_at_xro : forall pc, astrcmp_realizes_xro segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (kx + 1) 0 kx -> first_byte segs W memT y (ky + 1) 0 ky ->
src_ok segs W regsT memT x (kx + 1) -> src_ok segs W regsT memT y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + ky -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kx + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_strcmp_at_xroR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_strlen_at_xro over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strlen_at_xro is its case R := wle *)
Lemma aj_strlen_at_xroR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrlen_realizes_xro segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw
HJ Ha0 Hx0 Hl0 Hl32 Hxl Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hrom.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AS lyc Sc Hpc W regsT memT mdc x len HPRE Hlo2 Hpres2E Ha0 Hx0 Hl0 Hl32 Hxl Hfb Hsx
ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* MOVED here from B/Prog/ExwB_StrlenRo.v:72 (blob d38c23bec721), the same way *)
Lemma aj_strlen_at_xro : forall pc, astrlen_realizes_xro segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_strlen_at_xroR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_strcmp_at_xrom over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strcmp_at_xrom is its case R := wle *)
Lemma aj_strcmp_at_xromR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrcmp_realizes_xrom segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (kx + 1) 0 kx -> first_byte segs W memT y (ky + 1) 0 ky ->
src_ok segs W regsT memT x (kx + 1) -> src_ok segs W regsT memT y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + ky -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kx + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans pc AC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky o raw
HJ Ha0 Ha1 Hx0 Hy0 Hkx0 Hkx32 Hxk Hky0 Hky32 Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw
Hfx Hfy Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy Htx Hty Hrom.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AC lyc Sc Hpc W regsT memT mdc x y kx ky HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hkx0 Hkx32 Hxk Hky0 Hky32 Hyk
Hfx Hfy Hsx Hsy ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy Htx Hty Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

Lemma aj_strcmp_at_xrom : forall pc, astrcmp_realizes_xrom segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (kx + 1) 0 kx -> first_byte segs W memT y (ky + 1) 0 ky ->
src_ok segs W regsT memT x (kx + 1) -> src_ok segs W regsT memT y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + ky -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kx + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_strcmp_at_xromR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_strlen_at_xrom over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strlen_at_xrom is its case R := wle *)
Lemma aj_strlen_at_xromR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrlen_realizes_xrom segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R _ _ pc AS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw
HJ Ha0 Hx0 Hl0 Hl32 Hxl Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hrom.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfrs.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AS lyc Sc Hpc W regsT memT mdc x len HPRE Hlo2 Hpres2E Ha0 Hx0 Hl0 Hl32 Hxl Hfb Hsx
ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W
memT mdc k mem2 md2 (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

Lemma aj_strlen_at_xrom : forall pc, astrlen_realizes_xrom segs B ARx rlo rhi pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_strlen_at_xromR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End strrules.


(* ---------------------------------------------------------------------------- *)
(* 9. strlen in the rom_view form (h-verbs-1 12:36Z: literal's walks carry rom_view, not arodata_okP, on both
   images). YGcallMx.v's astrlen_realizes_x / aj_strlen_at_x with the keep, nothing else (checked by a script; see
   the commit message). *)
Section strx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).

(* YGcallMx.v:103 astrlen_realizes_x, plus the keep *)
Definition astrlen_realizes_xm (pc : Z) : Prop :=
forall ly S Hp W regs mem md x k,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* aj_strlen_at_xm over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strlen_at_xm is its case R := wle *)
Lemma aj_strlen_at_xmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrlen_realizes_xm pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
rom_view segs W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans pc AS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw
HJ Ha0 Hx0 Hl0 Hl32 Hxl Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hrom.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AS lyc Sc Hpc W regsT memT mdc x len HPRE Hlo2 Hpres2E Ha0 Hx0 Hl0 Hl32 Hxl Hfb Hsx
ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

(* YGcallMx.v:391 aj_strlen_at_x, plus the keep (an implication in the conclusion) *)
Lemma aj_strlen_at_xm : forall pc, astrlen_realizes_xm pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
rom_view segs W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_strlen_at_xmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End strx.

Section strxcj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable P : alayout -> astate -> Prop.
Local Abbreviation ARP := (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S).

Lemma astrlen_realizes_xm_forget : forall pc, astrlen_realizes_xm segs B ARx pc -> astrlen_realizes_x segs B ARx pc.
Proof.
intros pc AS ly S Hp W regs mem md x k HPRE. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md x k HPRE); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & K1 & K2 & K3 & K4 & K5 & K6 & _).
split; [reflexivity|]. exists regs', mem', md'.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 K6)))))).
Qed.

(* YGcallMx.v:589 astrlen_realizes_x_conj, for the text with the keep *)
Lemma astrlen_realizes_xm_conj : forall pc, astrlen_realizes_xm segs B ARx pc -> astrlen_realizes_xm segs B ARP pc.
Proof.
intros pc AS ly S Hp W regs mem md x k [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md x k (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.
End strxcj.

(* ---------------------------------------------------------------------------- *)
(* 10. Family 4: the malloc / free call rules with the keep (YGcallx.v Section r). *)
(* Section variables and hypotheses in YGcallx.v's order (Section gx, then Section r), so each _m rule takes exactly the
   arguments of its YGcallx.v original; the abbreviations below are YGcallx.v's section-local names, so each statement
   is the original's text. *)

Section allocm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable QM : astate -> Prop.
(* the call's trailing conjuncts on the state and the call memory (YGcallx.QMm, round 6g); non-cf: fun S _ => QM S *)
Variable QMm : astate -> (word -> option byte) -> Prop.
Variable mt : Z -> list Z -> YG00.M sptr.
Variable nmax : Z.
Variable ft : sptr -> list Z -> YG00.M unit.
Variable WFx : astate -> Prop.
Variable XS : alayout -> astate -> list (Z * Z).
Local Abbreviation code := (as_code B).
Local Abbreviation acall_pre_x := (YGcallx.acall_pre_x segs B ARx QMm).
Local Abbreviation malloc_leaf_x := (YGcallx.malloc_leaf_x (fx := fx) segs B ARx XS).
Local Abbreviation free_leaf_x := (YGcallx.free_leaf_x (fx := fx) segs B ARx).
Local Abbreviation amalloc_realizes_x := (YGcallx.amalloc_realizes_x (fx := fx) segs B ARx QMm mt nmax XS).
Local Abbreviation afree_realizes_x := (YGcallx.afree_realizes_x (fx := fx) segs B ARx QMm ft).
Local Abbreviation acall_kept_x := (YGcallx.acall_kept_x (rc := rc) segs B).
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law (rc := rc) segs B ARx.
Hypothesis WFL : ARx_wf_law segs ARx WFx.
Hypothesis AMX : alloc_model_laws_x B QM mt nmax ft WFx.
(* the call's memory-aware conjuncts give the model laws' state predicate (YGcallx.QMQ; non-cf: the identity) *)
Hypothesis QMQ : forall S mem, QMm S mem -> QM S.
Hypothesis XSL : ARx_xs_law (rc := rc) segs B ARx XS.

(* aj_malloc_x_m over a journal at a reflexive and transitive world relation R that contains wle (YGcallx.aj_malloc_xR);
   aj_malloc_x_m is its case R := wle *)
Lemma aj_malloc_x_mR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact (YGcallx.aj_malloc_xR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx XS LAWS segs_low errno_low OWNLOW WFL AMX QMQ XSL
  R R_refl R_trans R_wle AMALLOC W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr).
Qed.

(* YGcallx.v's aj_malloc_x VERBATIM *)
Lemma aj_malloc_x_m : amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_x_mR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* ---------------------------------------------------------------------------- *)
(* The free _m rules over the journal's world relation R and the callee's call post APOST (YGcallx Section rR):  *)
(* aj_free_x_ct_mR / aj_free_at_x_ct_mR; aj_free_x_ct_m / aj_free_at_x_ct_m below are their instances at wle and *)
(* acall_post_x. Each is its YGcallx.v R form VERBATIM, proved by it.                                            *)
Section allocmR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Variable APOST : Z -> alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
  (Z -> Prop) -> alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Hypothesis POST_AR : apost_ar_law segs ARx APOST.
Hypothesis POST_J : apost_j_law (rc := rc) (SK := SK) segs B ARx R APOST.
Local Abbreviation afree_realizes_xR := (YGcallx.afree_realizes_xR (fx := fx) segs B ARx QMm ft R APOST).
Local Abbreviation free_leaf_xA := (YGcallx.free_leaf_xA (fx := fx) segs B APOST).

Lemma aj_free_x_ct_mR : afree_realizes_xR ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
exact (YGcallx.aj_free_x_ctR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx LAWS segs_low errno_low
  WFL AMX QMQ R R_trans APOST POST_AR POST_J
  AFREE W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2
  Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP).
Qed.

Lemma aj_free_at_x_ct_mR : afree_realizes_xR ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
exact (YGcallx.aj_free_at_x_ctR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx LAWS segs_low
  errno_low WFL AMX QMQ R R_trans APOST POST_AR POST_J
  AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp
  Htp Hra Hraw HQM Hch Htr HFP).
Qed.
(* aj_free_x_m over R and APOST (YGcallx.aj_free_xR); aj_free_x_m is its case R := wle, APOST := acall_post_x *)
Lemma aj_free_x_mR : afree_realizes_xR ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch
HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
exact (YGcallx.aj_free_xR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx LAWS segs_low errno_low WFL AMX QMQ
  R R_trans APOST POST_AR POST_J AFREE W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o spw raw ch HS Hpcs Hrv HJ Hin Hnhp Ha0 Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP).
Qed.

(* aj_free_at_x_m over R and APOST (YGcallx.aj_free_at_xR); aj_free_at_x_m is its case R := wle, APOST := acall_post_x *)
Lemma aj_free_at_x_mR : afree_realizes_xR ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRrG segs R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch
HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP.
exact (YGcallx.aj_free_at_xR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx LAWS segs_low errno_low WFL AMX QMQ
  R R_trans APOST POST_AR POST_J AFREE W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n o raw ch HJ Hin Hnhp Ha0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr HFP).
Qed.

End allocmR.

(* YGcallx.v's aj_free_x VERBATIM *)
Lemma aj_free_x_m : afree_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_x_mR (@wle segs) (wle_trans segs) (YGcallx.acall_post_x segs B ARx) (POST_AR_x segs B ARx)
  (POST_J_x (rc := rc) (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW)
  (YGcallx.afree_realizes_x_R (fx := fx) segs B ARx QMm ft AFREE)).
Qed.

(* YGcallx.v's aj_free_x_ct VERBATIM *)
Lemma aj_free_x_ct_m : afree_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_x_ct_mR (@wle segs) (wle_trans segs) (YGcallx.acall_post_x segs B ARx) (POST_AR_x segs B ARx)
  (POST_J_x (rc := rc) (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW)
  (YGcallx.afree_realizes_x_R (fx := fx) segs B ARx QMm ft AFREE)).
Qed.

(* aj_malloc_x_ct_m over a journal at a reflexive and transitive world relation R that contains wle (YGcallx.aj_malloc_x_ctR);
   aj_malloc_x_ct_m is its case R := wle *)
Lemma aj_malloc_x_ct_mR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch
HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact (YGcallx.aj_malloc_x_ctR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx XS LAWS segs_low errno_low OWNLOW WFL AMX QMQ XSL
  R R_refl R_trans R_wle AMALLOC W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o spw raw ch HS Hpcs Hrv HJ Ha0 Hn Hlb Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr).
Qed.

(* YGcallx.v's aj_malloc_x_ct VERBATIM *)
Lemma aj_malloc_x_ct_m : amalloc_realizes_x ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_malloc code -> ss_resv ss = None ->
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
getr (ms_regs ms) 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) (ms_regs ms) ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_x_ct_mR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* YGcallx.v's aj_free_at_x VERBATIM *)
Lemma aj_free_at_x_m : afree_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_at_x_mR (@wle segs) (wle_trans segs) (YGcallx.acall_post_x segs B ARx) (POST_AR_x segs B ARx)
  (POST_J_x (rc := rc) (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW)
  (YGcallx.afree_realizes_x_R (fx := fx) segs B ARx QMm ft AFREE)).
Qed.

(* aj_malloc_at_x_m over a journal at a reflexive and transitive world relation R that contains wle (YGcallx.aj_malloc_at_xR);
   aj_malloc_at_x_m is its case R := wle *)
Lemma aj_malloc_at_x_mR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact (YGcallx.aj_malloc_at_xR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx XS LAWS segs_low errno_low OWNLOW WFL AMX QMQ XSL
  R R_refl R_trans R_wle AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr).
Qed.

(* YGcallx.v's aj_malloc_at_x VERBATIM *)
Lemma aj_malloc_at_x_m : amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace0 (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_at_x_mR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.

(* YGcallx.v's aj_free_at_x_ct VERBATIM *)
Lemma aj_free_at_x_ct_m : afree_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (ft q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_x lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AFREE WS.
exact (aj_free_at_x_ct_mR (@wle segs) (wle_trans segs) (YGcallx.acall_post_x segs B ARx) (POST_AR_x segs B ARx)
  (POST_J_x (rc := rc) (SK := SK) segs B ARx LAWS segs_low errno_low OWNLOW)
  (YGcallx.afree_realizes_x_R (fx := fx) segs B ARx QMm ft AFREE)).
Qed.

(* aj_malloc_at_x_ct_m over a journal at a reflexive and transitive world relation R that contains wle (YGcallx.aj_malloc_at_x_ctR);
   aj_malloc_at_x_ct_m is its case R := wle *)
Lemma aj_malloc_at_x_ct_mR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof.
intros R R_refl R_trans R_wle AMALLOC WS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch
HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr.
exact (YGcallx.aj_malloc_at_x_ctR (fx := fx) (rc := rc) (SK := SK) segs B PST ARx QM QMm mt nmax ft WFx XS LAWS segs_low errno_low OWNLOW WFL AMX QMQ XSL
  R R_refl R_trans R_wle AMALLOC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n o raw ch HJ Ha0 Hn Hlive Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HQM Hch Htr).
Qed.

(* YGcallx.v's aj_malloc_at_x_ct VERBATIM *)
Lemma aj_malloc_at_x_ct_m : amalloc_realizes_x ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k n (o : Z) raw ch,
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
getr regsT 10 = w64 n -> 0 <= n < nmax -> blocks_bytes Sc + n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2 (k + (st_nev S2 - st_nev Sc))
  (WS ++ [call_trace lyc (pc_malloc_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
acall_pre_x lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc /\
(exists p trc, apath (mt n (call_trace lyc (pc_malloc_ra0 code) regsT ch) Sc) trc (p, S2) /\ gflag trc = true /\
malloc_leaf_x lyc Sc Hpc W regsT memT mdc n (p, S2) W2 c2 /\
(p = PNull <-> res = 0) /\ (p <> PNull -> res = sptr_addr B ly2 p)) /\
((res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun _ => False) /\
rd32 (aview segs (w_H W2) mem2) (as_errno B) 12 /\ aview segs (w_H W2) mem2 (as_oom_byte B) = Some 1)
\/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\
acall_kept_x lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => res <= a < res + req_size n)))).
Proof. exact (aj_malloc_at_x_ct_mR (@wle segs) (wle_refl segs) (wle_trans segs) (fun _ _ H => H)). Qed.
End allocm.

(* ---------------------------------------------------------------------------- *)
(* 11. Family 5: the poison / unpoison call rules with the keep (YGcallPx.v Section px / l). *)
Section poisonm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable hd : Z.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* aj_poison_at_x_m over a journal at any world relation R: the call keeps the world (W2 = W); aj_poison_at_x_m is
   its case R := wle *)
Lemma aj_poison_at_x_mR : forall (R : world segs -> world segs -> Prop) pc, YGcallPx.apoison_realizes_x segs B ARx hd pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R pc AP W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o raw
HJ Ha0 Ha1 H8 Hin Hhd Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (ajxR_ar HJ) as HAR.
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc b n HAR Hin) as (Hb16 & _).
assert (Hb8 : b mod 8 = 0) by (apply Z.mod_divide in Hb16 as [x Hx]; [|lia]; rewrite Hx;
replace (x * 16) with ((x * 2) * 8) by lia; apply Z.mod_mul; lia).
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ eapply (YGcallPx.ecall_pre_at_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k
  regsT o); try eassumption.
rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AP lyc Sc Hpc W regsT memT mdc b n HPRE Ha0 Ha1 H8 Hin Hhd). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hsh & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (YGcallPx.ajournal_x_shd_writeR (SK := SK) segs B PST ARx hd LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc
    Sc Hpc W memT mdc k mem2 md2 (b :: Hpc)
    b n (sp0 + o - ESTACK) (sp0 + o) HJ Hin ltac:(lia)); [zlia | zlia | exact Hfr | exact Hpres2 | exact Hsame | exact HAR2]. }
split; [exact HP|]. split; [|split; [exact Hfr | split; [exact Hpres2 | exact Hmn]]].
intros g Hg. destruct (YGcallPx.shd_idx_g hd b g Hb8 H8 Hg) as [Eg Hi]. rewrite Eg. exact (Hsh _ Hi).
Qed.

(* aj_poison_x_m over a journal at any world relation R; aj_poison_x_m is its case R := wle *)
Lemma aj_poison_x_mR : forall (R : world segs -> world segs -> Prop) pc, YGcallPx.apoison_realizes_x segs B ARx hd pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof.
intros R pc AP W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o spw raw
HS Hpc' Hrv HJ Ha0 Ha1 H8 Hin Hhd Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (ajxR_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply YP0m.zcanon_small. zlia. }
rewrite (YA0o.st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpc'.
eapply (aj_poison_at_x_mR R); eassumption.
Qed.

(* YGcallPx.v:239 aj_poison_at_x, plus the keep (the text's last post conjunct) *)
Lemma aj_poison_at_x_m : forall pc, YGcallPx.apoison_realizes_x segs B ARx hd pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. intros pc. exact (aj_poison_at_x_mR (@wle segs) pc). Qed.

(* aj_unpoison_at_x_m over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_unpoison_at_x_m is its case R := wle *)
Lemma aj_unpoison_at_x_mR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, YGcallPx.aunpoison_realizes_x segs B ARx hd pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans pc AU W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o raw
HJ Ha0 Ha1 H8 Hhp Hin Hhd Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & _).
destruct (alx_blocks segs B ARx LAWS lyc Sc Hpc W memT mdc b n HAR Hin) as (Hb16 & _).
assert (Hb8 : b mod 8 = 0) by (apply Z.mod_divide in Hb16 as [x Hx]; [|lia]; rewrite Hx;
replace (x * 16) with ((x * 2) * 8) by lia; apply Z.mod_mul; lia).
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ eapply (YGcallPx.ecall_pre_at_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k regsT o);
  try eassumption.
rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AU lyc Sc Hpc W regsT memT mdc b n HPRE Ha0 Ha1 H8 Hhp Hin Hhd). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hsh & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr, Hpres2.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (YGcallPx.ajournal_x_shd_writeR (SK := SK) segs B PST ARx hd LAWS segs_low R
    STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2 (remove Z.eq_dec b Hpc)
    b n (sp0 + o - ESTACK) (sp0 + o) HJ Hin ltac:(lia)); [zlia | zlia | exact Hfr | exact Hpres2 | exact Hsame | exact HAR2]. }
split; [exact HP|]. split; [|split; [exact Hfr | split; [exact Hpres2 | exact Hmn]]].
intros g Hg. destruct (YGcallPx.shd_idx_g hd b g Hb8 H8 Hg) as [Eg Hi]. rewrite Eg. exact (Hsh _ Hi).
Qed.

(* YGcallPx.v:279 aj_unpoison_at_x, plus the keep (the text's last post conjunct) *)
Lemma aj_unpoison_at_x_m : forall pc, YGcallPx.aunpoison_realizes_x segs B ARx hd pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) raw,
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 b -> getr regsT 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_unpoison_at_x_mR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* YGcallPx.v:319 aj_poison_x, plus the keep at the call's memory *)
Lemma aj_poison_x_m : forall pc, YGcallPx.apoison_realizes_x segs B ARx hd pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (b :: Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some YGcfNames.shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof. intros pc. exact (aj_poison_x_mR (@wle segs) pc). Qed.

(* aj_unpoison_x_m over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_unpoison_x_m is its case R := wle *)
Lemma aj_unpoison_x_mR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, YGcallPx.aunpoison_realizes_x segs B ARx hd pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans pc AU W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n o spw raw
HS Hpc' Hrv HJ Ha0 Ha1 H8 Hhp Hin Hhd Hsp HE2 Hspw Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (ajxR_stk HJ) as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _). assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hsp' : spZ (ms_regs ms) = sp0 + o).
{ unfold spZ. rewrite Hsp. rewrite denot_SOff, HE2, Hspw. apply YP0m.zcanon_small. zlia. }
rewrite (YA0o.st_ok_restrict_mkst segs (w_H W) E ss ms HS Hrv), Hpc'.
eapply (aj_unpoison_at_x_mR R R_refl R_trans); eassumption.
Qed.

(* YGcallPx.v:349 aj_unpoison_x, plus the keep at the call's memory *)
Lemma aj_unpoison_x_m : forall pc, YGcallPx.aunpoison_realizes_x segs B ARx hd pc ->
forall W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k b n (o : Z) spw raw,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
getr (ms_regs ms) 10 = w64 b -> getr (ms_regs ms) 11 = w64 hd -> hd mod 8 = 0 -> In b Hpc ->
In (b, n) (ablocks B lyc Sc) -> hd <= req_size n ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg ms mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc (remove Z.eq_dec b Hpc) W mem2 md2 k /\
aregs_preserved (ms_regs ms) regs2 /\
(forall g, b <= g < b + hd -> aview segs (w_H W) mem2 (shadow_addr g) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> ~ (shadow_addr b <= a < shadow_addr b + hd / 8) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) (ms_mem ms) a) /\
(forall a, sp0 + o - ESTACK <= a < sp0 + o -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs (ms_mem ms) -> MN.memnorm segs mem2)).
Proof. exact (aj_unpoison_x_mR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End poisonm.

(* ---------------------------------------------------------------------------- *)
(* 12. The cf free call-site forms under the re-hide: aj_free_x_ct_mR / aj_free_at_x_ct_mR at the primed cf row       *)
(*     (YG0dcfR.afree_realizes_cf_rh, through YGcallcf.afree_realizes_x_cf_rh), R := wle' segs RZ_cf, APOST := APOST_cf *)
(*     with its laws POST_AR_cf / POST_J_cf (YGcallcf.v), ARx := ARcf /\ xs_placed_cf. A run that crosses such a free   *)
(*     ends in SRr' segs RZ_cf, with the journal's world conjunct at wle' segs RZ_cf. These imports serve this section *)
(*     only.                                                                                                          *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRehidePost YG0dcfR YGcallcf.

Section allocrh. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Local Abbreviation ARxs := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
Local Abbreviation code := (as_code B).
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARxs HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law (rc := rc) segs B ARxs.
Hypothesis WFL : ARx_wf_law segs ARxs (Wf_cf (as_universe B)).
Hypothesis AMX : alloc_model_laws_x B QM_cf malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).

Lemma aj_free_x_ct_m_rh : afree_realizes_cf_rh segs B ->
forall {WS : list (list Z)} W E ss ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) spw raw ch,
st_ok segs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_free code -> ss_resv ss = None ->
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr (ms_regs ms) 10 = w64 pa ->
getr (ms_regs ms) 2 = sv_denot E (SOff 2 o) -> ew E 2 = spw -> bv_unsigned spw = sp0 ->
o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc (ms_mem ms) ->
chain_pre lyc (aview segs (w_H W) (ms_mem ms)) (ms_regs ms) ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr' segs RZ_cf W (mkCfg ms mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
  (k + (st_nev S2 - st_nev Sc)) (WS ++ [call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch]) /\
aregs_preserved (ms_regs ms) regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (free_cf q (call_trace lyc (pc_free_ra0 code) (ms_regs ms) ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA segs B (APOST_cf segs B) lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc q n (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W (ms_mem ms) W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AF WS.
exact (aj_free_x_ct_mR (fx := fx) (rc := rc) (SK := SK) segs B PST ARxs QM_cf (QMm_cf segs B) malloc_cf cf_malloc_max
  free_cf (Wf_cf (as_universe B)) LAWS segs_low errno_low WFL AMX (QMQ_cf segs B) (wle' segs RZ_cf) (wle'_trans segs RZ_cf)
  (APOST_cf segs B) (POST_AR_cf segs B) (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
  (afree_realizes_x_cf_rh segs B AF)).
Qed.

Lemma aj_free_at_x_ct_m_rh : afree_realizes_cf_rh segs B ->
forall {WS : list (list Z)} W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa n (o : Z) raw ch,
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k WS ->
In (pa, n) (ablocks B lyc Sc) -> ~ In pa Hpc ->
getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
QMm_cf segs B Sc memT ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc ->
(In (pa, n) (ablocks B ly S) -> forall i, 0 <= i < req_size n -> inFP FP (pa + i)) ->
SRr' segs RZ_cf W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free code)) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xwR segs B PST ARxs (wle' segs RZ_cf) STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hpc W2 mem2 md2
  (k + (st_nev S2 - st_nev Sc)) (WS ++ [call_trace lyc (pc_free_ra0 code) regsT ch]) /\
aregs_preserved regsT regs2 /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
frames S2 = frames Sc /\
acall_pre_x segs B ARxs (QMm_cf segs B) lyc Sc Hpc W regsT memT mdc ch /\
admits (as_universe B) (call_trace lyc (pc_free_ra0 code) regsT ch) Sc /\
(exists q trc, sptr_addr B lyc q = pa /\ In (q, n) (blocks Sc) /\
apath (free_cf q (call_trace lyc (pc_free_ra0 code) regsT ch) Sc) trc (tt, S2) /\ gflag trc = true /\
free_leaf_xA segs B (APOST_cf segs B) lyc Sc Hpc W regsT memT mdc q n (tt, S2) W2 c2) /\
acall_kept_x segs B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size n)).
Proof.
intros AF WS.
exact (aj_free_at_x_ct_mR (fx := fx) (rc := rc) (SK := SK) segs B PST ARxs QM_cf (QMm_cf segs B) malloc_cf cf_malloc_max
  free_cf (Wf_cf (as_universe B)) LAWS segs_low errno_low WFL AMX (QMQ_cf segs B) (wle' segs RZ_cf) (wle'_trans segs RZ_cf)
  (APOST_cf segs B) (POST_AR_cf segs B) (POST_J_cf (SK := SK) segs B LAWS segs_low errno_low OWNLOW)
  (afree_realizes_x_cf_rh segs B AF)).
Qed.
End allocrh.
