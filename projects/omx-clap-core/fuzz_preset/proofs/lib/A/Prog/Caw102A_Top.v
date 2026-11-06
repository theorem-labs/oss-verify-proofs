(* fuzz_preset lib/A, the #102 re-walk of check_as_written on image A' (asan, pin sha256 1be0f53d96cb9d6c, unstripped
   twin bff8519bbe3ea0e4; entry 0x81fb8 = slot A_prog_slot AS_check_as_written): WA_Top, the composition of the segment
   walk WA0 .. WA6 into the kit's text tcheck_as_written_specX THROUGH the base's caw_text_of_walkR, with the memnorm
   invariant instantiated ONCE: P := caw_mn D (fun m => memnorm segs (cw_mem D) -> memnorm segs m), its laws by the
   base's caw_mn_laws / caw_mn_call / caw_mn_mn. Part of the #102 re-walk. The B'
   twin is caw_B_top (lib/B/Prog/Caw102B_Top.v); this file mirrors its shape.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma; the composition of WA0..WA6).
   On the kit's cut of the #102 batch, preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record): the re-fit to the RE-STATED base, prepared on the batch kit.
   BASE OF RECORD: this row's lib/A/Prog/Caw102A_Base.v (statements of blob 6fb51f0a23b0, as at preset-tree-at-2026-10-30T02-52-53Z.tsv (sha256 5a024403b9d9; internal record))
   (Kit 3d241a90402d); the kit's cut (the batch-102 kit) preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (lib/A/PRH_FnCheck.v
   c40cf3fdcd2a, tcheck_as_written_specX :832-902; PRH_Base.v ef7c8ca98529; PRH_Refute.v 23f7a37f01c9, Required by WA0).
   THE CONCLUSION is the text itself as this tree states it (PRH_FnCheck.v:1313-1402: the batch kit's c40cf3fdcd2a plus
   hull_budget :1349 and HPOS :1359-1362, SRr' :1373 for SRr), every premise and every post conjunct (caw_text_of_walkR's binder-for-binder check), at ARcfx B, P instantiated once.
   WHAT CHANGED ON THIS BASE, AND WHY (the batch text's changes):
   (1) the run-word list DW is gone from the text (its binder and prh_univ_closure's argument): the Section variable
       DW is removed, every base and segment name is cited without it, and caw_A_top is stated at
       `tcheck_as_written_specX .. CTX0`.
   (2) the room counts are the text's own entry premises (:1343-1344, after room_live_cf): the named argument CAW_CNT
       and its paragraph are removed; caw_text_of_walkR takes no count argument, and WA0's caw_cnt D is the base's
       caw_pre_cnt of the entry premises (a projection, by conversion).
   (3) THE OUTCOME, the text's new post conjunct (:1379-1388), is built in caw_top_QbR: on the r = 1 arm from the cut's
       caw_dead (the refused malloc is impossible at a consumer position: exfalso), on the r = 0 arm r = 0 and the
       cut's caw_prog D (caw_evs D) (the text's list literal and its length are caw_evs D by conversion).
   (4) caw_at_END grew (caw_dead on its r = 1 arm), so it and its R form caw_at_ENDR are read BY NAME
       (caw_top_end_carry / _arm / _ab / _ledger and their R twins below), never by a positional pattern.
   THE CHAIN (the base's cuts and continuations):
     WA0 (+0 -> caw_k_X +68 / caw_k_null +112)
     WA1 (caw_at_null +112 -> caw_k_END +300: the malloc's NULL arm, `sb 1, g_own_ran_out`, r = 1)
     WA2 (caw_at_X +68 -> caw_k_R +128 / caw_k_OOM +252)      WA3 (caw_at_R +128 -> caw_k_OOM +252)
     WA4 (caw_at_OOM +252 -> caw_k_END +300 / caw_k_CHK +276) WA5 (caw_at_CHK +276 -> caw_k_END +300)
     WA6 (caw_at_END +300 -> the return: fpostF at the body Qb := fQmn (cw_mem D) (caw_Qb B D), i.e. caw_text_post).
   THE RELATION: the walk runs at RW := YA0nH.wle' segs RZ_cf (the re-hide's relation past the scratch's free). Every
   continuation is its R form at RW (caw_k_XR / _nullR / _RR / _OOMR / _CHKR / _ENDR); WA0 / WA1 are their wle
   statements lifted by the base's caw_seg_WA0_lift / caw_seg_WA1_lift; WA2 / WA3 are stated at RW; WA4 / WA5 / WA6
   are their R forms caw_wa4_holdsR / caw_wa5_holdsR / caw_wa6_holdsR. The walk's SRrG at RW is the base's
   caw_text_of_walkR premise (YA0nH.SRr' segs RZ_cf) once SRrG_mono drops P.
   THE BODY AT THE RETURN (caw_top_QbR; its wle twin caw_top_Qb stays beside it): the carry gives the room and Hp; the
   cut's ablocks clause the blocks; the ledger with own' := ownv is the cut's caw_ledger; the text's bytes by WA2's
   wa2_src_rd_JR at RW; r, own', THE OUTCOME and the post-implication position per arm (r = 1: caw_prog D [] and
   caw_dead D, r = 0: caw_prog D (caw_evs D), the text's forms by conversion, caw_Qb_prog) from the cut's arm fact; the
   reader's tree (rc = 0) by WA2's wa2_tree_JR at RW; the memnorm keep of fQmn from P at the cut.
   INPUTS (BY PATH): the base of record above; the segment files WA0 .. WA6 re-fitted on it by the #102 re-walk
   (one branch per segment, WA0 / WA1 / WA2 / WA3 / WA4-6).
   SECTION HYPOTHESES (the segments' own, each in its segment's spelling; owners in brackets):
     CWI : caw_img (PA := PA) B [a Theorem Labs lane / Caw102A_Img.v caw_img_A at PI_prog_A];
     PAL : PALib B [PALibA.v palib_A at the instance];
     AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (WA0's malloc row, the memnorm keep at the leaf) and
       AFREE : forall fz, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (WA2 / WA3's free row under the re-hide)
       [YGcfMallocComposeKeep.v];
     HEXV : forall fz, tex_value_specX B (ARcfx B) SK DOC_D [a Theorem Labs lane's text, the ex_value walk];
     HRANOUT : forall fz, tfuzz_alloc_ran_out_specX B (ARcfx B) SK [a Theorem Labs lane's text, the fuzz_alloc_ran_out walk].
   cp := CfParamsPreset.CfParams_preset (WA0 / WA2 / WA3 bind it; the base's text is stated at it).
   No numeral but register 10 (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnEx PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Caw102A_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Caw102A_WA0 Caw102A_WA1 Caw102A_WA2 Caw102A_WA3
  Caw102A_WA4 Caw102A_WA5 Caw102A_WA6.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {PA : PAImg A_prog_listing}.
#[local] Existing Instances CW_PrhImg CW_PAListing CW_RL.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
(* the relation past the scratch's free (the re-hide's zone) *)
#[local] Abbreviation RW := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).

(* ---- the segments' Section hypotheses, each in its segment's spelling ---- *)
Hypothesis CWI : caw_img (PA := PA) B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep segs B.
Hypothesis AFREE : forall fz : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fz) segs B.
Hypothesis HEXV : forall fz : YK11.FPState, tex_value_specX (fx := fz) B (ARcfx B) SK DOC_D.
Hypothesis HRANOUT : forall fz : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fz) B (ARcfx B) SK.

(* ---- caw_at_END BY NAME (the cut grew: caw_dead on its r = 1 arm); each projection states its conjunct, so a change
   of the cut fails here, never mis-binds ---- *)
Lemma caw_top_end_carry : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  caw_carry (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (H & _). exact H. Qed.
Lemma caw_top_end_arm : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  (r = 1 /\ ownv = 1 /\ caw_prog D [] S3 /\ caw_dead D) \/ (r = 0 /\ ownv = 0 /\ caw_prog D (caw_evs D) S3).
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (_ & _ & H & _). exact H. Qed.
Lemma caw_top_end_ab : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D).
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (_ & _ & _ & H & _). exact H. Qed.
Lemma caw_top_end_ledger : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  caw_ledger B D ly3 S3 Hp3 W3 mem3 ownv.
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (_ & _ & _ & _ & H). exact H. Qed.

(* ---- the text's body at the End cut, for any a0 = r and any preserved callee-saved registers (WA6's premise): the
   ledger at the cut's own byte (caw_ledger, own' := ownv), THE OUTCOME (r = 1: the cut's caw_dead refutes the
   consumer position; r = 0: r = 0 and the cut's caw_prog D (caw_evs D)) and the post-implication position of the
   arm ---- *)
Lemma caw_top_Qb : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_END (fx := fx) B SK CTX0 D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv -> caw_mn D mem3 ->
  forall regs' md', getr regs' 10 = w64 r -> aregs_preserved (cw_regs D) regs' ->
  fQmn (cw_mem D) (caw_Qb B D) ly3 S3 Hp3 W3 regs' mem3 md'.
Proof.
intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT HPM regs' md' R10 HAR.
pose proof (caw_top_end_carry D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as HC.
pose proof (caw_top_end_arm D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as Hr.
pose proof (caw_top_end_ab D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as Eab.
pose proof (caw_top_end_ledger D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as HLG.
clear HAT.
destruct HC as (Hpre & Hcnt & HFL & HJ & HKR & HSP & HSV & EHp & HRL & HROD).
unfold caw_ledger in HLG.
assert (Hinc : incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly3 S3)) by (rewrite Eab; apply incl_refl).
pose proof (Caw102A_WA2.wa2_src_rd_J (fx := fx) B SK CTX0 D ly3 S3 Hp3 W3 mem3 md3 k _ _ _ _ _ _ _
  Hpre HJ Hinc EHp HLG) as HSRC.
split; [|exact HPM].
unfold caw_Qb. cbv beta.
split; [exact HRL|]. split; [exact EHp|]. split; [exact Eab|].
exists ownv. split; [exact HLG|]. split; [exact (proj1 HSRC)|].
exists r. split; [exact R10|].
destruct Hr as [(-> & -> & Hprog & Hdead) | (-> & -> & Hprog)].
- split.
  + intros sm x0 os i H0 hist Hp Hrun Hcons. exfalso. exact (Hdead sm x0 os i H0 hist Hp Hrun Hcons).
  + left. split; [reflexivity|]. split; [reflexivity|]. exact Hprog.
- split.
  + intros sm x0 os i H0 hist Hp Hrun Hcons. split; [reflexivity | exact (Hprog sm x0 os i H0 hist Hp Hrun)].
  + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hprog|]. intros Hrc.
    exact (proj1 (Caw102A_WA2.wa2_tree_J (fx := fx) B SK CTX0 D ly3 S3 Hp3 W3 regs' mem3 md3 k
      Hpre HJ Hinc Hrc)).
Qed.

(* ---- caw_at_ENDR at RW BY NAME, the R twins of the four projections above ---- *)
Lemma caw_top_end_carryR : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_ENDR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  caw_carryR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k.
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (H & _). exact H. Qed.
Lemma caw_top_end_armR : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_ENDR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  (r = 1 /\ ownv = 1 /\ caw_prog D [] S3 /\ caw_dead D) \/ (r = 0 /\ ownv = 0 /\ caw_prog D (caw_evs D) S3).
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (_ & _ & H & _). exact H. Qed.
Lemma caw_top_end_abR : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_ENDR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  ablocks B ly3 S3 = ablocks B (cw_ly D) (cw_S D).
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (_ & _ & _ & H & _). exact H. Qed.
Lemma caw_top_end_ledgerR : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_ENDR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv ->
  caw_ledger B D ly3 S3 Hp3 W3 mem3 ownv.
Proof. intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT. destruct HAT as (_ & _ & _ & _ & H). exact H. Qed.

(* ---- caw_top_Qb at the End cut's R form at RW: the same body, the text's bytes and tree by WA2's R readers ---- *)
Lemma caw_top_QbR : forall D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv,
  caw_at_ENDR (fx := fx) B SK CTX0 RW D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv -> caw_mn D mem3 ->
  forall regs' md', getr regs' 10 = w64 r -> aregs_preserved (cw_regs D) regs' ->
  fQmn (cw_mem D) (caw_Qb B D) ly3 S3 Hp3 W3 regs' mem3 md'.
Proof.
intros D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT HPM regs' md' R10 HAR.
pose proof (caw_top_end_carryR D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as HC.
pose proof (caw_top_end_armR D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as Hr.
pose proof (caw_top_end_abR D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as Eab.
pose proof (caw_top_end_ledgerR D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT) as HLG.
clear HAT.
destruct HC as (Hpre & Hcnt & HFL & HJ & HKR & HSP & HSV & EHp & HRL & HROD).
unfold caw_ledger in HLG.
assert (Hinc : incl (ablocks B (cw_ly D) (cw_S D)) (ablocks B ly3 S3)) by (rewrite Eab; apply incl_refl).
pose proof (Caw102A_WA2.wa2_src_rd_JR (fx := fx) B SK CTX0 RW D ly3 S3 Hp3 W3 mem3 md3 k _ _ _ _ _ _ _
  Hpre HJ Hinc EHp HLG) as HSRC.
split; [|exact HPM].
unfold caw_Qb. cbv beta.
split; [exact HRL|]. split; [exact EHp|]. split; [exact Eab|].
exists ownv. split; [exact HLG|]. split; [exact (proj1 HSRC)|].
exists r. split; [exact R10|].
destruct Hr as [(-> & -> & Hprog & Hdead) | (-> & -> & Hprog)].
- split.
  + intros sm x0 os i H0 hist Hp Hrun Hcons. exfalso. exact (Hdead sm x0 os i H0 hist Hp Hrun Hcons).
  + left. split; [reflexivity|]. split; [reflexivity|]. exact Hprog.
- split.
  + intros sm x0 os i H0 hist Hp Hrun Hcons. split; [reflexivity | exact (Hprog sm x0 os i H0 hist Hp Hrun)].
  + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hprog|]. intros Hrc.
    exact (proj1 (Caw102A_WA2.wa2_tree_JR (fx := fx) B SK CTX0 RW D ly3 S3 Hp3 W3 regs' mem3 md3 k
      Hpre HJ Hinc Hrc)).
Qed.

(* WA_Top: tcheck_as_written_specX as this tree states it (PRH_FnCheck.v:1313-1402: c40cf3fdcd2a :832-902 at the kit's cut
   7cdbb61b5fa0 plus hull_budget and HPOS, SRr' for SRr) at ARcfx B, through caw_text_of_walkR (the walk at RW); the room counts are the text's entry premises (caw_pre_cnt) *)
Theorem caw_A_top : @tcheck_as_written_specX fx rc ci CfParams_preset CW_PrhImg (@CW_RL CfParams_preset)
  A_prog_listing PA B (ARcfx B) SK CTX0.
Proof.
apply caw_text_of_walkR. intros D Hpre _.
(* the memnorm invariant, ONCE *)
pose (P := caw_mn D).
pose proof (caw_mn_laws D) as PLAW. pose proof (caw_mn_call D) as PCALL.
pose proof (caw_mn_mn B CTX0 D Hpre) as PMN.
fold P in PLAW, PCALL, PMN.
pose (Q := caw_text_post B SK D).
(* the seven segments at P and RW: WA0 / WA1 lifted from their wle statements *)
assert (H0 : caw_seg_WA0R (fx := fx) B SK CTX0 P RW)
  by exact (caw_seg_WA0_lift B SK CTX0 RW (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf) P (Caw102A_WA0.caw_wa0_holds B SK CTX0 CWI PAL AMALLOC P PLAW PCALL)).
assert (H1 : caw_seg_WA1R (fx := fx) B SK CTX0 P RW)
  by exact (caw_seg_WA1_lift B SK CTX0 RW (YA0nH.wle_wle' segs YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans segs YGcfRehidePost.RZ_cf) P (Caw102A_WA1.caw_wa1_holds B SK CTX0 CWI P PLAW)).
assert (H2 : caw_seg_WA2R (fx := fx) B SK CTX0 P RW)
  by exact (Caw102A_WA2.caw_wa2_holds B SK CTX0 PAL AFREE HEXV CWI P PLAW PCALL PMN).
assert (H3 : caw_seg_WA3R (fx := fx) B SK CTX0 P RW)
  by exact (Caw102A_WA3.caw_wa3_holds B SK CTX0 PAL AFREE CWI P PLAW PCALL).
assert (H4 : caw_seg_WA4R (fx := fx) B SK CTX0 P RW)
  by exact (Caw102A_WA4.caw_wa4_holdsR B SK CTX0 CWI HRANOUT P PLAW PCALL).
assert (H5 : caw_seg_WA5R (fx := fx) B SK CTX0 P RW) by exact (Caw102A_WA5.caw_wa5_holdsR B SK CTX0 P PLAW).
assert (H6 : caw_seg_WA6R (fx := fx) B SK CTX0 P RW) by exact (Caw102A_WA6.caw_wa6_holdsR B SK CTX0 P PLAW).
(* the continuations at RW, from the End back to the entry *)
assert (KEND : caw_k_ENDR (fx := fx) B SK CTX0 P RW Q D).
{ intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT HPM.
  exact (H6 (fQmn (cw_mem D) (caw_Qb B D)) D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT
    (caw_top_QbR D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k r ownv HAT HPM) HPM). }
assert (KCHK : caw_k_CHKR (fx := fx) B SK CTX0 P RW Q D).
{ intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv HAT HPM.
  exact (H5 Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want ownv HAT KEND HPM). }
assert (KOOM : caw_k_OOMR (fx := fx) B SK CTX0 P RW Q D).
{ intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want HAT HPM.
  exact (H4 Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k want HAT KEND KCHK HPM). }
assert (KR : caw_k_RR (fx := fx) B SK CTX0 P RW Q D).
{ intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl HAT HPM.
  exact (H3 Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr u rest dl HAT KOOM HPM). }
assert (KX : caw_k_XR (fx := fx) B SK CTX0 P RW Q D).
{ intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr HAT HPM.
  exact (H2 Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k scr HAT KR KOOM HPM). }
assert (KNULL : caw_k_nullR (fx := fx) B SK CTX0 P RW Q D).
{ intros fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT HPM.
  exact (H1 Q D fy ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT KEND HPM). }
(* the entry: P holds at the entry memory (memnorm mem -> memnorm mem), the room counts by caw_pre_cnt (the text's
   own premises), then the post without P (SRr' is SRrG at RW) *)
unfold YA0nH.SRr'.
eapply (YA0nH.SRrG_mono segs RW); [exact (H0 Q D Hpre (caw_pre_cnt B CTX0 D Hpre) KX KNULL (fun h => h))|].
intros W' c' _ [HQ _]. exact HQ.
Qed.

End top.

Check caw_A_top.
Print Assumptions caw_A_top.
