(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim APrimSpec2 APrimLem APrimPop APrimPopLens APrimRefill APrimQ APrimDealloc APrimCover ASec ASecD AQuar AQuarM
                        AHeap F_quar_E AQuarR AQuarP F_quar_As F_quar_R F_quar_DR F_quar_D F_quar_P ALedger ALinkPg ALinkVm ALink ALinkPrim ALinkFree ALinkFreeIn.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import PEnv AHeap2 AHeapB AFreeL8 AMallocP.
Import ListNotations.
Open Scope Z_scope.

Section PI.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

Definition pure_inv (s : astB) : Prop :=
  pinv AL (bs_X s) (allheld s) (flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s))
  /\ pwf_all (bs_prim s) /\ budget_ok s
  /\ Forall qbatch_wf (bs_gl s) /\ qbytes (bs_gl s) <= A0_QB /\ Forall ch_cls_ok (flat_map qb_chunks (bs_gl s)).

#[using="Type"] Lemma pure_inv_of_rheap : forall s LB (m : mem), RHEAP_B AL E s LB m -> pure_inv s.
Proof.
  intros s LB m HR. pose proof (rheap_pinv AL E s LB m HR) as PI. pose proof (rheap_wf AL E s LB m HR) as WF. destruct (rheap_qbytes AL E s LB m HR) as [FWG QB].
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FCQ & _ & BUD & _).
  split; [exact PI|]. split; [exact WF|]. split; [exact BUD|]. split; [exact FWG|]. split; [exact QB| exact FCQ].
Qed.

#[using="Type"] Lemma pure_refill_budget : forall s, pure_inv s -> forall c, 1 <= c <= 31 -> refill_budget c (get_cls (bs_prim s) c).
Proof.
  intros s (_ & WF & (BMU & _) & _) c Hc. apply refill_budget_of_mu; [exact Hc| exact (WF c Hc)|]. pose proof (PM_fits c Hc) as [_ PF]. specialize (BMU c Hc). lia.
Qed.

#[using="Type"] Lemma pure_refill_mu : forall s, pure_inv s -> forall c, 1 <= c <= 31 -> p_cnt (get_cls (bs_prim s) c) = 0 ->
  p_mu (refill (get_cls (bs_prim s) c) c) <= PM c.
Proof.
  intros s ((_ & _ & COV & _) & WF0 & (BMU & BLV & _) & FWG & QB & FCQ) c Hc C0. cbn [bs_X fst] in COV. pose proof (WF0 c Hc) as WF.
  pose proof WF as (_ & _ & _ & _ & _ & _ & AU & _ & _ & AUS & _).
  pose proof (cover_count (bs_prim s) (allheld s) c COV Hc ltac:(lia) AUS) as CC.
  pose proof (held_count_le (bs_gl s) (live_chunks s) c Hc FWG QB FCQ (BLV c Hc)) as HM.
  exact (refill_mu_le c (get_cls (bs_prim s) c) _ Hc WF C0 CC HM (BMU c Hc)).
Qed.

#[using="Type"] Theorem free_link_inputs_pure : forall s ch n l1 l2 v,
  pure_inv s -> bs_live s = l1 ++ (ch, n) :: l2 -> linked v (bs_X s) ->
  let P := bs_prim s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let X1 := (fst (enq_prim P loc), bs_sec s) in let todo := put_todo P glob loc ch in
  let X' := dorecycle X1 todo in
  let v1 := va_enq v P loc in let v' := va_dorecycle v1 X1 todo in
  (enq_refills P loc = true -> pclass_wf K_BCLASS (get_cls P K_BCLASS) /\ refill_budget K_BCLASS (get_cls P K_BCLASS))
  /\ sok_dorecycle v1 X1 todo
  /\ 8 * R_dorecycle X1 todo <= 9 * (31 * K_FA_SIZE - sum_mfa (fst X1))
  /\ linked v' X' /\ va_base v' (fst X') = va_base v P /\ va_nsec v' = va_nsec v /\ va_aux v' = va_aux v.
Proof.
  intros s ch n l1 l2 v PIV EL LK. cbv zeta.
  set (P := bs_prim s). set (glob := q_glob (bs_quar s)). set (loc := q_loc (bs_quar s)).
  set (hrest := flat_map prim_of (map fst (l1 ++ l2))). set (secsR := flat_map sec_of (map fst (l1 ++ l2))).
  pose proof (pure_refill_budget s PIV K_BCLASS ltac:(lia)) as RB24. fold P in RB24.
  destruct PIV as (PI0 & WF0 & _). fold P in WF0.
  destruct (allheld_split s ch n l1 l2 EL) as [PH PS].
  pose proof (pinv_perm AL _ _ _ _ _ PH PS PI0) as PIa. clear PI0 PH PS.
  change (bs_gl s) with (glob ++ loc) in PIa. change (bs_X s) with (P, bs_sec s) in PIa. fold hrest secsR in PIa.
  pose proof (pinv_put_mid AL P (bs_sec s) glob loc ch hrest secsR PIa (WF0 K_BCLASS ltac:(lia)) (fun _ => RB24)) as PIm.
  pose proof PIa as (LEN & _). cbn [fst] in LEN.
  pose proof (pwf_enq P loc LEN WF0 (fun _ => RB24)) as WF1.
  assert (LK1 : linked (va_enq v P loc) (fst (enq_prim P loc), bs_sec s)) by exact LK.
  destruct (step_dorecycle AL _ _ _ _ _ PIm WF1 LK1) as [SOK FR].
  pose proof (R_dorecycle_bound AL _ _ _ _ _ PIm WF1 LK1) as RB.
  pose proof (dorecycle_same_mu AL _ _ _ _ PIm) as [MU1 _]. cbn [fst] in MU1.
  destruct FR as (_ & LK' & EP & EN & EA & _). cbv zeta in EP. cbn [fst] in EP.
  split; [intros _; split; [exact (WF0 K_BCLASS ltac:(lia))| exact RB24]|]. split; [exact SOK|]. split; [exact RB|]. split; [exact LK'|].
  split; [| split; [exact EN| exact EA]].
  unfold va_base. rewrite EP. unfold va_enq at 1. cbn [va_prim]. rewrite (D_enq_eq P loc LEN), (sum_mu_ext _ _ MU1). lia.
Qed.

#[using="Type"] Lemma pure_inv_malloc_prim : forall s LB (m : mem) c (ch : qchunk) (cn : Z) H' hs' total',
  RHEAP_B AL E s LB m -> 1 <= c <= 31 ->
  qc_kind ch = QPrim c (snd (cache_alloc (bs_prim s) c)) ->
  (lbcZ LB c + 1) * a0_csz c <= A0_CAP c ->
  pure_inv (mkASB H' (bs_pages s) (fst (cache_alloc (bs_prim s) c)) (bs_sec s) (bs_quar s) hs' total' (bs_nsec s) ((ch, cn) :: bs_live s) (bs_depot0 s)).
Proof.
  intros s LB m c ch cn H' hs' total' HR Hc EK CAP.
  destruct (malloc_prim_budget AL E s LB m c ch cn H' hs' total' HR Hc EK CAP) as [PI BUD]. cbv zeta in PI, BUD.
  destruct (pure_inv_of_rheap s LB m HR) as ((LEN & _) & WF0 & _ & FWG & QB & FCQ). cbn [bs_X fst] in LEN.
  pose proof (rheap_refill_budget AL E s LB m HR c Hc) as RB.
  split; [exact PI|]. split; [exact (pwf_cache_alloc (bs_prim s) c Hc LEN WF0 (fun _ => RB))|]. split; [exact BUD|].
  split; [exact FWG|]. split; [exact QB| exact FCQ].
Qed.

#[using="Type"] Lemma pure_inv_malloc_sec : forall s LB (m : mem) a size (ch : qchunk) (cn : Z) H' hs' total',
  RHEAP_B AL E s LB m -> sec_wf AL (sec_alloc (bs_sec s) a size) ->
  qc_kind ch = QSec (mkSC a (sec_msize size) size) ->
  sec_live_cnt s + 1 <= A0_SEC_CNT -> sec_live_bytes s + cn <= A0_SEC_BYTES -> bs_nsec s + 1 <= A0_NSEC_MAX ->
  pure_inv (mkASB H' (bs_pages s) (bs_prim s) (sec_alloc (bs_sec s) a size) (bs_quar s) hs' total' (bs_nsec s + 1) ((ch, cn) :: bs_live s) (bs_depot0 s)).
Proof.
  intros s LB m a size ch cn H' hs' total' HR SWF EK BC BB BN.
  destruct (malloc_sec_budget AL E s LB m a size ch cn H' hs' total' HR SWF EK BC BB BN) as [PI BUD]. cbv zeta in PI, BUD.
  destruct (pure_inv_of_rheap s LB m HR) as (_ & WF0 & _ & FWG & QB & FCQ).
  split; [exact PI|]. split; [exact WF0|]. split; [exact BUD|]. split; [exact FWG|]. split; [exact QB| exact FCQ].
Qed.

End PI.
