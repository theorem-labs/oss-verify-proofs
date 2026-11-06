From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantSlotPlan.
Import ListNotations.
Open Scope Z_scope.

Lemma kept_trans : forall x W ms ms1 ms2, kept x W ms ms1 -> kept x W ms1 ms2 -> kept x W ms ms2.
Proof.
  intros x W ms ms1 ms2 [M1 W1] [M2 W2]. split.
  - exact (munch_trans _ _ _ _ M1 M2).
  - exact (wmono_trans rsegs _ _ _ W1 W2).
Qed.

Lemma kept_nil : forall x W ms ms', kept x [] ms ms' -> kept x W ms ms'.
Proof.
  intros x W ms ms' [M Wm]. split; [| exact Wm].
  eapply munch_weaken; [| exact M]. intros a Ha. cbn in Ha |- *. tauto.
Qed.

Lemma kept_refl : forall x W ms, kept x W ms ms.
Proof. intros x W ms. split; [apply munch_refl | apply wmono_refl]. Qed.

Lemma evt_kept_step : forall x W (P Q : machine_state -> Prop) ms,
  evt rsegs (fun ms1 => kept x W ms ms1 /\ P ms1) ms ->
  (forall ms1, P ms1 -> evt rsegs (fun ms2 => kept x W ms1 ms2 /\ Q ms2) ms1) ->
  evt rsegs (fun ms2 => kept x W ms ms2 /\ Q ms2) ms.
Proof.
  intros x W P Q ms H1 H2. eapply evt_cut; [exact H1|]. intros ms1 [K1 HP].
  eapply evt_mono; [exact (H2 ms1 HP)|]. intros ms2 [K2 HQ]. split; [exact (kept_trans _ _ _ _ _ K1 K2) | exact HQ].
Qed.

Lemma set_loop : seg_set_turn -> forall x t k i ms,
  (i + k)%nat = Z.to_nat (nset (x_pl x)) -> At_set x t i ms ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\ At_unset0 x t ms') ms.
Proof.
  intros TURN x t k. induction k as [|k IH]; intros i ms Hk H.
  - exfalso. destruct H as (_ & _ & Hi & _). lia.
  - eapply evt_cut; [exact (TURN x t i ms H)|]. intros ms1 [K1 [[Hi1 H1] | [Hi1 H1]]].
    + eapply evt_mono; [exact (IH (S i) ms1 ltac:(lia) H1)|].
      intros ms2 [K2 H2]. split; [exact (kept_trans _ _ _ _ _ K1 K2) | exact H2].
    + apply evt_done. split; [exact K1 | exact H1].
Qed.

Lemma unset_loop : seg_unset_turn -> forall x t k c ms,
  c + Z.of_nat k = 48 -> At_unset x t c ms ->
  evt rsegs (fun ms' => kept x [] ms ms' /\ At_admit x t ms') ms.
Proof.
  intros TURN x t k. induction k as [|k IH]; intros c ms Hk H.
  - exfalso. destruct H as (_ & _ & Hc & _). lia.
  - eapply evt_cut; [exact (TURN x t c ms H)|]. intros ms1 [K1 [[Hc1 H1] | [Hc1 H1]]].
    + eapply evt_mono; [exact (IH (c + 1) ms1 ltac:(lia) H1)|].
      intros ms2 [K2 H2]. split; [exact (kept_trans _ _ _ _ _ K1 K2) | exact H2].
    + apply evt_done. split; [exact K1 | exact H1].
Qed.

Lemma sched_loop : seg_sched_turn -> forall x t k i ms,
  (i + k)%nat = Z.to_nat (frames (x_pl x)) -> At_sched x t i ms ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\ At_freeT x t ms') ms.
Proof.
  intros TURN x t k. induction k as [|k IH]; intros i ms Hk H.
  - exfalso. destruct H as (_ & _ & Hi & _). lia.
  - eapply evt_cut; [exact (TURN x t i ms H)|]. intros ms1 [K1 [[Hi1 H1] | [Hi1 H1]]].
    + eapply evt_mono; [exact (IH (S i) ms1 ltac:(lia) H1)|].
      intros ms2 [K2 H2]. split; [exact (kept_trans _ _ _ _ _ K1 K2) | exact H2].
    + apply evt_done. split; [exact K1 | exact H1].
Qed.

(* Phase E1: from the return of malloc(460) to the first allocator call after admission. *)
Lemma phase_E1 : seg_init -> seg_nset -> seg_set_turn -> seg_unset_enter -> seg_unset_turn -> seg_admit ->
  forall x t ms, At_mallocT_ret x t ms ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\
    ((ok (x_pl x) = true /\ At_mallocSW1 x t ms') \/ (ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK ms'))) ms.
Proof.
  intros INIT NSET TURN UENT UTURN ADMIT x t ms H.
  assert (A1 : evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\ At_admit x t ms') ms).
  { eapply evt_kept_step; [exact (INIT x t ms H)|]. intros ms1 H1.
    eapply evt_cut; [exact (NSET x t ms1 H1)|]. intros ms2 [K2 [[Hn H2] | [Hn H2]]].
    - eapply evt_cut; [exact (UENT x t ms2 H2)|]. intros ms3 [K3 H3].
      eapply evt_mono; [exact (unset_loop UTURN x t 48 0 ms3 ltac:(lia) H3)|].
      intros ms4 [K4 H4]. split; [| exact H4].
      pose proof (kept_nil x [(t, t + 460)] _ _ K2) as K2'. pose proof (kept_nil x [(t, t + 460)] _ _ K3) as K3'.
      pose proof (kept_nil x [(t, t + 460)] _ _ K4) as K4'.
      exact (kept_trans _ _ _ _ _ (kept_trans _ _ _ _ _ K2' K3') K4').
    - eapply evt_cut; [exact (set_loop TURN x t (Z.to_nat (nset (x_pl x))) 0 ms2 ltac:(lia) H2)|].
      intros ms3 [K3 H3].
      eapply evt_cut; [exact (UENT x t ms3 H3)|]. intros ms4 [K4 H4].
      eapply evt_mono; [exact (unset_loop UTURN x t 48 0 ms4 ltac:(lia) H4)|].
      intros ms5 [K5 H5]. split; [| exact H5].
      pose proof (kept_nil x [(t, t + 460)] _ _ K2) as K2'. pose proof (kept_nil x [(t, t + 460)] _ _ K4) as K4'.
      pose proof (kept_nil x [(t, t + 460)] _ _ K5) as K5'.
      exact (kept_trans _ _ _ _ _ (kept_trans _ _ _ _ _ (kept_trans _ _ _ _ _ K2' K3) K4') K5'). }
  eapply evt_cut; [exact A1|]. intros ms1 [K1 H1].
  eapply evt_mono; [exact (ADMIT x t ms1 H1)|]. intros ms2 [K2 H2].
  split; [exact (kept_trans _ _ _ _ _ K1 (kept_nil x [(t, t + 460)] _ _ K2)) | exact H2].
Qed.

(* Phase E5: from the return of the second free to the free of the table. *)
Lemma phase_E5 : seg_sched_setup -> seg_sched_turn ->
  forall x t ms, At_freeSW2_ret x t ms ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms ms' /\ At_freeT x t ms') ms.
Proof.
  intros SETUP TURN x t ms H.
  eapply evt_cut; [exact (SETUP x t ms H)|]. intros ms1 [K1 [[Hf H1] | [Hf H1]]].
  - apply evt_done. split; [exact K1 | exact H1].
  - eapply evt_mono; [exact (sched_loop TURN x t (Z.to_nat (frames (x_pl x))) 0 ms1 ltac:(lia) H1)|].
    intros ms2 [K2 H2]. split; [exact (kept_trans _ _ _ _ _ K1 K2) | exact H2].
Qed.
