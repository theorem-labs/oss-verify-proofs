(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Disp_word.v, with its module paths and module names changed; 116 of its 154 lines of code are new or changed and 465 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_Kit.v, with its module names changed; 989 of its 1073 lines of code are new or changed and 70 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Caw102B_WB2.v; 55 of its 120 lines of code are new or changed and 1008 lines of the source are left out. *)
(* fuzz_preset, image B' (asan-ubsan, harness fix #102: pin sha256 d663f82d7f488d30, twin c90d4fa54d43160b): WB_Top,
   the composition of check_as_written's segment walk (Caw102B.v and its segment files) into the text
   tcheck_as_written_specX as this tree states it (lib/A/PRH_FnCheck.v:1313-1402: c40cf3fdcd2a :832-902 @ the kit's cut
   7cdbb61b5fa0 plus hull_budget and HPOS, SRr' for SRr), with the memnorm invariant instantiated ONCE: P := fun m =>
   memnorm SEGS mem -> memnorm SEGS m (YSRrMemnorm srr_inv_laws_imp at srr_inv_laws_memnorm_k, srr_inv_call_imp,
   srr_inv_mn_imp). Lane CawA102R; the A' twin is Caw102A_Top.v's caw_A_top.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma; the composition of the segments).
   BASE OF RECORD: the kit's cut, this row's lib/B/Prog/Caw102B.v (its
   statements). WHAT CHANGED against the f97c top (Caw102B.v, text 9ecd8eb167c6), and why:
   - the run-word list DW is GONE from the text (its binder and prh_univ_closure's argument) and from the base's record
     (mkCawB lost its last field c_DW): caw_B_top quantifies over CTX0 only;
   - the ROOM COUNTS are entry premises of the text (:862-863), caw_pre's 23rd / 24th conjuncts: with the hull budget and HPOS the text now has 27
     premises, intros H1 .. H24 HHULL HHPOS H25, and Hpre is their conjunction in the text's order. The named argument CAW_CNT is GONE:
     the segments that take caw_cnt C (WB1 / WB2 / WB3) get the base's caw_pre_cnt C Hpre (by conversion);
   - the text's NEW post conjunct THE OUTCOME (:879-888) is in caw_post (the base's caw_Q), which WB6 builds from
     cut_end (caw_dead on the r = 1 arm, caw_prog C (caw_evs C) on the r = 0 arm): no new step here;
   - caw_pre is read BY NAME (caw_pre_mn), never positionally.
   THE CHAIN: caw_WB0 (entry -> 0x81fbc) -> caw_WB1 (the malloc and its two arms) -> {caw_WB2 (-> {caw_WB3 ->
   {caw_WB4a, caw_WB4}, caw_WB4a}), caw_WB6 (the NULL arm)}; caw_WB4 -> {caw_WB6 (refuted arm), caw_WB5 -> caw_WB6}.
   THE CONCLUSION IS THE TEXT ITSELF: caw_B_top states `tcheck_as_written_specX (fx := fx) B ARcfx SK CTX0`, binder
   for binder, premise for premise, its post in full (the Batch-2 ledger at most own', THE OUTCOME under the run
   hypothesis, the post-implication position keyed on the scratch's own grant).
   SECTION HYPOTHESES: the callee texts TEXV (ex_value, at DOC_D), TEXWS (ex_ws), TRO (fuzz_alloc_ran_out), AFREE /
   AMALLOC (the free / malloc rows, their keep twins of YGcfMallocComposeKeep.v, the free under the re-hide), each at
   every float state; the image facts, each spelled as in its segment file: Hent, PAL, Hpst, Hpst_img, Hpst_rw,
   Hret_free, Hfree2, PAB (at IMG_LO_B), Hown_obj, Hpst_wr, Hmal, Hown_hi, and the cf layer's relro rows Hrelro_seg,
   Herrno_relro, Hrelro_top, Hrelro_eq, Hro_reads_nw; their instance witness at PI_prog_B is Caw102B_Img.v
   (caw_B_top_inst; PAL by PALibB.v 5baa19c890f7).
   THE TEXT'S CONCLUSION IS SRr' segs RZ_cf (the re-hide's relation RW, past the scratch's free): the segments past the
   free compose at RW (their R forms), WB0 / WB1 by Caw102B.v's lifts of their wle statements.
   No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YG0lawscf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfHeadSh YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require H2CawPure S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Caw102B Caw102B_WB0 Caw102B_WB1 Caw102B_WB2
  Caw102B_WB3 Caw102B_WB4 Caw102B_WB5 Caw102B_WB6.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

Section f.
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the callee texts *)
Hypothesis TEXV : forall fz : YK11.FPState, tex_value_specX (fx := fz) B ARcfx SK DOC_D.
Hypothesis TEXWS : forall fz, tex_ws_specX (fx := fz) B ARcfx SK.
Hypothesis TRO : forall fz, tfuzz_alloc_ran_out_specX (fx := fz) B ARcfx SK.
(* the free / malloc rows: the keep twins (YGcfMallocComposeKeep.v; the free under the re-hide), at every float
   state *)
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) SEGS B.
Hypothesis AMALLOC : forall fz, YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fz) SEGS B.
(* the image facts (their instance witness at PI_prog_B is a separate pins102 file) *)
Hypothesis Hent : SIGMA AS_check_as_written = BASE + AF_cawB.
Hypothesis PAL : PALib B.
Hypothesis Hpst : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis Hpst_img : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis Hpst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
Hypothesis Hret_free : In (BASE + (AF_cawB + 116)) (pi_ret_sites F_check_as_written RT_free).
Hypothesis Hfree2 : BASE + (AF_cawB + 160) = pi_ret_caw_free2.
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO_B.
Hypothesis Hown_obj : VAL (A_OBJ 13) = pi_g_own_ran_out.
Hypothesis Hpst_wr : forall (m : word -> option byte) a, Exists (in_zr a) prh_pst -> writable_at SEGS m a.
Hypothesis Hmal : BASE + (AF_cawB + CAWB_RET) = pi_ret_caw_malloc.
Hypothesis Hown_hi : VAL (A_HI 10) + (-624) = VAL (A_OBJ 13).
(* the cf layer's relro rows at the image, each spelled as in Caw102B_WB2.v / Caw102B_WB3.v (the allocator calls'
   arodata_ok_cf); their instance witness at PI_prog_B is Caw102B_Img.v (lib/AU/CfAroPresetB.v, the range equation by
   computation) *)
Hypothesis Hrelro_seg : YG0ncf.relro_seg_t SEGS.
Hypothesis Herrno_relro : YG0ncf.errno_relro_t B.
Hypothesis Hrelro_top : cf_relro_hi <= 2 ^ 64.
Hypothesis Hrelro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA.
Hypothesis Hro_reads_nw : YGcfAroBridge.ro_reads_nw_t SEGS.
(* the world relation past the scratch's free (the re-hide's zone): the text's own SRr' relation *)
#[local] Abbreviation RW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* WB_Top: the tcheck_as_written_specX, as written (its conclusion SRr' segs RZ_cf, the re-hide's relation RW). THE
   CHAIN AT RW: the segments past the free state their R forms (caw_WB6R, caw_WB5R, caw_WB4R, caw_WB4aR, caw_WB3,
   caw_WB2); WB1 and WB0, whose own cuts are before any free, keep their wle statements and are lifted by Caw102B.v's
   caw_K_mal_lift_ev_end / caw_K_mal_lift *)
Theorem caw_B_top : forall (CTX0 : list (list Z)), tcheck_as_written_specX (fx := fx) B ARcfx SK CTX0.
Proof.
intros CTX0 ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most
  size H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 HHULL HHPOS H25.
set (C := mkCawB ly S Hp W regs mem md ch data x rc0 doc t D Lam peak cnt fail ran most CTX0).
(* the text's 27 premises, in its order, ARE caw_pre C (HHULL / HHPOS its hull budget and entry run position) *)
assert (Hpre : caw_pre (fx := fx) B C).
{ exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
    (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23
    (conj H24 (conj HHULL (conj HHPOS H25)))))))))))))))))))))))))). }
(* the room counts, by conversion (formerly the named argument CAW_CNT) *)
pose proof (caw_pre_cnt (fx := fx) B C Hpre) as Hcnt.
(* the memnorm invariant, ONCE *)
pose (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as PLAW.
pose proof (srr_inv_call_imp SEGS mem) as PCALL.
pose proof (srr_inv_mn_imp SEGS mem (caw_pre_mn (fx := fx) B C Hpre)) as PMN.
fold P in PLAW, PCALL, PMN.
pose (Q := caw_post (fx := fx) B C).
pose proof (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) as RWle.
pose proof (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) as RWtr.
(* the continuations at RW, from the End back to the malloc *)
assert (Kend : caw_K_endR (fx := fx) B RW C P Q) by (eapply caw_WB6R; eassumption).
assert (Kck : caw_K_ckR (fx := fx) B RW C P Q) by (eapply caw_WB5R; eassumption).
assert (KoB : caw_K_oBR (fx := fx) B RW C P Q) by (eapply caw_WB4R; eassumption).
assert (KoA : caw_K_oAR (fx := fx) B RW C P Q) by (eapply caw_WB4aR; eassumption).
assert (Kws : caw_K_wsR (fx := fx) B RW C P Q) by (eapply caw_WB3; eassumption).
assert (Kev : caw_K_evR (fx := fx) B RW C P Q) by (eapply caw_WB2; eassumption).
(* the malloc cut: WB1's wle statement at every final post, lifted *)
assert (HWB1 : forall Q0, caw_K_ev (fx := fx) B C P Q0 -> caw_K_end (fx := fx) B C P Q0 -> caw_K_mal (fx := fx) B C P Q0)
  by (intros Q0; eapply caw_WB1; eassumption).
pose proof (caw_K_mal_lift_ev_end (fx := fx) B RW RWle RWtr C P HWB1 Q Kev Kend) as Kmal.
(* the entry: WB0's wle statement at every final post, lifted; then the text's post from caw_post and the invariant *)
assert (HWB0 : forall Q0, caw_K_mal (fx := fx) B C P Q0 ->
  SRr SEGS (c_W C) (cfg_at SEGS (SIGMA AS_check_as_written) (c_regs C) (c_mem C) (c_md C))
    (fun W' c' => Q0 W' c' /\ P (ms_mem (cfg_ms c'))))
  by (intros Q0 KM; exact (caw_WB0 B Hent C P Q0 PLAW Hpre KM (fun h => h))).
unfold YA0nH.SRr'.
eapply (YA0nH.SRrG_mono SEGS RW); [exact (caw_K_mal_lift (fx := fx) B RW RWle RWtr C P _ _ HWB0 Q Kmal)|].
intros W' c' _ [Hpost HPM'].
unfold Q, caw_post, fpostF, apost_base_xFR in Hpost.
destruct Hpost as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hfz & Hfk & HJ & Har & HQ).
unfold fpostFm, fpostF, apost_base_xFR, fQmn.
exists fx', ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ|]. split; [exact Har|].
split; [exact HQ|].
rewrite Hc in HPM'. exact HPM'.
Qed.

End f.
End d.

Check caw_B_top.
Print Assumptions caw_B_top.
