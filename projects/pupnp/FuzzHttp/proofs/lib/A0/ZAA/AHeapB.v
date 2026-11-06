(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim PEnv APrimSpec2 APrimLem APrimPop APrimRefill APrimQ APrimDealloc APrimCover ASec ASecD AQuar AQuarM
                        AHeap F_quar_E AQuarR AQuarS AQuarP F_quar_As F_quar_R F_quar_DR F_quar_D F_quar_P ALedger AHeap2.
Import ListNotations.
Open Scope Z_scope.

Section HB.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).

#[using="Type"] Lemma sum_cs_nonneg : forall P hs, Forall (held1 P) hs -> 0 <= sum_cs hs.
Proof.
  intros P hs FH. induction FH as [|[c v] l (Hc & _) _ IH]; [cbn; lia|]. rewrite sum_cs_cons. cbn [fst] in *.
  pose proof (class_size_pos c Hc). lia.
Qed.

#[using="Type"] Lemma rheap_held : forall s LB (m : mem), RHEAP_B AL E s LB m -> held_ok (bs_prim s) (allheld s).
Proof.
  intros s LB m (_ & _ & _ & INVB & _). destruct INVB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOK & _).
  unfold allheld, tc_of. rewrite <- app_assoc. exact HOK.
Qed.

#[using="Type"] Lemma rheap_pinv : forall s LB (m : mem), RHEAP_B AL E s LB m ->
  pinv AL (bs_X s) (allheld s) (flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s)).
Proof.
  intros s LB m HR. pose proof (rheap_held s LB m HR) as HO.
  destruct HR as (_ & _ & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PSEC & COV & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & CAL & _) & _).
  destruct INVB as (RP & _ & RS & _). destruct RP as (LEN & _). destruct RS as (SWF & _). destruct SWF as (_ & _ & _ & _ & _ & COK & CSEP).
  unfold pinv, bs_X. cbn [fst snd]. tauto.
Qed.

#[using="Type"] Lemma rheap_wf : forall s LB (m : mem), RHEAP_B AL E s LB m -> forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (bs_prim s) c).
Proof. intros s LB m (_ & _ & _ & INVB & _) c Hc. destruct INVB as (RP & _). destruct RP as (_ & _ & CLS & _). exact (proj1 (CLS c Hc)). Qed.

#[using="Type"] Lemma rheap_stats : forall s LB (m : mem), RHEAP_B AL E s LB m ->
  0 <= pr_calloc (bs_prim s) /\ 0 <= pr_cmapped (bs_prim s) /\ pr_cmapped (bs_prim s) + K_REGION < 2^63.
Proof.
  intros s LB m HR. pose proof (rheap_held s LB m HR) as [_ FH]. pose proof (rheap_wf s LB m HR) as WF0.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & CAL & CMP & _) & _).
  rewrite CAL, CMP. split; [exact (sum_cs_nonneg _ _ FH)|].
  pose proof (sum_mu_bound (bs_prim s) FA_OFF ltac:(lia)) as SB.
  assert (BD : forall c, 1 <= c <= 31 -> 0 <= p_mu (get_cls (bs_prim s) c) <= FA_OFF).
  { intros c Hc. pose proof (WF0 c Hc) as (_ & _ & _ & _ & _ & _ & AU & MUF & _). lia. }
  specialize (SB BD). lia.
Qed.

#[using="Type"] Lemma rheap_refill_budget : forall s LB (m : mem), RHEAP_B AL E s LB m -> forall c, 1 <= c <= 31 -> refill_budget c (get_cls (bs_prim s) c).
Proof.
  intros s LB m HR c Hc. pose proof (rheap_wf s LB m HR c Hc) as WF.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (BMU & _) & _).
  apply refill_budget_of_mu; [exact Hc| exact WF|]. pose proof (PM_fits c Hc) as [_ PF]. specialize (BMU c Hc). lia.
Qed.

#[using="Type"] Lemma rheap_qbytes : forall s LB (m : mem), RHEAP_B AL E s LB m -> Forall qbatch_wf (bs_gl s) /\ qbytes (bs_gl s) <= A0_QB.
Proof.
  intros s LB m (_ & _ & _ & _ & _ & _ & _ & _ & _ & (FWF & QBL & QBG) & _). unfold bs_gl. split.
  - eapply Permutation_Forall; [apply Permutation_app_comm| exact FWF].
  - rewrite qbytes_app. unfold A0_QB. lia.
Qed.

#[using="Type"] Lemma rheap_refill_mu : forall s LB (m : mem), RHEAP_B AL E s LB m -> forall c, 1 <= c <= 31 -> p_cnt (get_cls (bs_prim s) c) = 0 ->
  p_mu (refill (get_cls (bs_prim s) c) c) <= PM c.
Proof.
  intros s LB m HR c Hc C0. pose proof (rheap_wf s LB m HR c Hc) as WF. destruct (rheap_qbytes s LB m HR) as [FWG QB].
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & COV & _ & _ & _ & _ & _ & _ & FCQ & _ & (BMU & BLV & _) & _).
  pose proof WF as (_ & _ & _ & _ & _ & _ & AU & _ & _ & AUS & _).
  pose proof (cover_count (bs_prim s) (allheld s) c COV Hc ltac:(lia) AUS) as CC.
  pose proof (held_count_le (bs_gl s) (live_chunks s) c Hc FWG QB FCQ (BLV c Hc)) as HM.
  exact (refill_mu_le c (get_cls (bs_prim s) c) _ Hc WF C0 CC HM (BMU c Hc)).
Qed.

End HB.
