(* Modified by Theorem Labs, 2026-10: new file, operations 5 (wake), 6 (close) and 7 (fail-next) of the fuzz_transport harness keep the simulation invariant, in the form the loop takes (a Theorem Labs lane). *)
(* From agree I ops at the loop head and the input cursor in range: the operation returns Some, agree I (ops + 1)
   holds after, and the cursor stays in range. The proofs: WakeOp5.v, WakeOp5T.v, WakeOp6.v, WakeOk.v (op 7). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TImg TNeed TSess0 TCb TSess TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Import Agree Links SendOk SimLib SettleOk WakeOk WakeBase
  WakeOp5 WakeOp5T WakeOp6.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Open Scope Z_scope.

(* the wake succeeds (FT:231-232; DS:139-144) *)
Lemma op5_ok_send : forall (HL : links) I ops W0 c1 k, agree I ops W0 -> opz W0 -> M_desk_known W0 = 1 ->
  M_foreign W0 = 0 -> g_fail_next W0 = 0 -> 0 <= ops < OPS_MAX ->
  exists W5, op5_body I W0 c1 k = Some (W5, (c1, k)) /\ agree I (ops + 1) W5.
Proof.
  intros HL I ops W0 c1 k HA Hz Dk Fo Fn Ho.
  destruct (Z.eq_dec (M_state W0) S_WAKING) as [Sw|Sw].
  - exact (op5_same HL I ops W0 c1 k HA Hz Dk Fo Fn Sw Ho).
  - exact (op5_trans HL I ops W0 c1 k HA Hz Dk Fo Fn Sw Ho).
Qed.

(* operation 5 (FT:1193-1199) *)
Theorem op5_step : forall (HL : links) (I : timg) (ops : Z) (B : list byte) (A : nat -> Z) (D : list byte)
    (c : fuzz_in) (k : nat),
  agree I ops B -> 0 <= ops < OPS_MAX -> snd (fuzz_u8_m D c) mod 9 = 5 ->
  exists B', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (fst (fuzz_u8_m D c), k)) /\
             agree I (ops + 1) B'.
Proof.
  intros HL I ops B A D c k HA Ho Hop.
  rewrite (op5_unfold I B A D c k Hop).
  destruct (op_begin_facts I ops B HA) as (W0 & Eb & HA0 & Hz).
  rewrite Eb. cbv beta iota.
  pose proof (ac_st _ _ _ (ag_core _ _ _ HA0)) as Hst.
  pose proof (ac_misc _ _ _ (ag_core _ _ _ HA0)) as Hmi.
  destruct (b2_desk_known01 _ Hst) as [Dk|Dk].
  - destruct (op5_unknown I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz Dk Ho) as [E H]. exists W0. split; assumption.
  - destruct (b3_foreign01 _ Hst) as [Fo|Fo].
    + destruct (e1_fail_next _ _ Hmi) as [Fn|Fn].
      * exact (op5_ok_send HL I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz Dk Fo Fn Ho).
      * exact (op5_fail HL I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz Dk Fo Fn Ho).
    + destruct (op5_foreign I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz ltac:(rewrite Dk; discriminate)
                  ltac:(rewrite Fo; discriminate) Ho) as [E H].
      eexists. split; [exact E | exact H].
Qed.

(* operation 6 (FT:1200-1205) *)
Theorem op6_step : forall (HL : links) (I : timg) (ops : Z) (B : list byte) (A : nat -> Z) (D : list byte)
    (c : fuzz_in) (k : nat),
  agree I ops B -> 0 <= ops < OPS_MAX -> snd (fuzz_u8_m D c) mod 9 = 6 ->
  exists B', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (fst (fuzz_u8_m D c), k)) /\
             agree I (ops + 1) B'.
Proof.
  intros HL I ops B A D c k HA Ho Hop.
  rewrite (op6_unfold I B A D c k Hop).
  destruct (op_begin_facts I ops B HA) as (W0 & Eb & HA0 & Hz).
  rewrite Eb. cbv beta iota.
  pose proof (ac_st _ _ _ (ag_core _ _ _ HA0)) as Hst.
  destruct (b2_desk_known01 _ Hst) as [Dk|Dk].
  - exact (op6_nosend I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz (or_introl Dk) Ho).
  - destruct (b3_foreign01 _ Hst) as [Fo|Fo].
    + destruct (Z.eqb_spec (M_state W0) S_CLOSED) as [Sc|Sc].
      * exact (op6_nosend I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz (or_intror (or_intror Sc)) Ho).
      * exact (op6_send HL I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz Dk Fo Sc Ho).
    + assert (Fo' : M_foreign W0 <> 0) by (rewrite Fo; discriminate).
      exact (op6_nosend I ops W0 (fst (fuzz_u8_m D c)) k HA0 Hz (or_intror (or_introl Fo')) Ho).
Qed.

(* the two operations with the input cursor (QueueFacts.fuzz_in_ok), as the loop takes them *)
Theorem op5_ok : forall (HL : links) (I : timg) (ops : Z) (B : list byte) (A : nat -> Z) (D : list byte)
    (c : fuzz_in) (k : nat),
  agree I ops B -> 0 <= ops < OPS_MAX -> QueueFacts.fuzz_in_ok D c -> snd (fuzz_u8_m D c) mod 9 = 5 ->
  exists B' c', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k)) /\ agree I (ops + 1) B' /\
                QueueFacts.fuzz_in_ok D c'.
Proof.
  intros HL I ops B A D c k HA Ho Hc Hop.
  destruct (op5_step HL I ops B A D c k HA Ho Hop) as (B' & E & H).
  destruct (QueueFacts.fuzz_u8_ok D c Hc) as (c' & v & Ec & Hc' & _).
  exists B', (fst (fuzz_u8_m D c)). split; [exact E|]. split; [exact H|]. rewrite Ec. exact Hc'.
Qed.

Theorem op6_ok : forall (HL : links) (I : timg) (ops : Z) (B : list byte) (A : nat -> Z) (D : list byte)
    (c : fuzz_in) (k : nat),
  agree I ops B -> 0 <= ops < OPS_MAX -> QueueFacts.fuzz_in_ok D c -> snd (fuzz_u8_m D c) mod 9 = 6 ->
  exists B' c', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k)) /\ agree I (ops + 1) B' /\
                QueueFacts.fuzz_in_ok D c'.
Proof.
  intros HL I ops B A D c k HA Ho Hc Hop.
  destruct (op6_step HL I ops B A D c k HA Ho Hop) as (B' & E & H).
  destruct (QueueFacts.fuzz_u8_ok D c Hc) as (c' & v & Ec & Hc' & _).
  exists B', (fst (fuzz_u8_m D c)). split; [exact E|]. split; [exact H|]. rewrite Ec. exact Hc'.
Qed.

Theorem op7_ok : forall (I : timg) (ops : Z) (B : list byte) (A : nat -> Z) (D : list byte) (c : fuzz_in) (k : nat),
  agree I ops B -> 0 <= ops < OPS_MAX -> QueueFacts.fuzz_in_ok D c -> snd (fuzz_u8_m D c) mod 9 = 7 ->
  exists B' c', LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B', (c', k)) /\ agree I (ops + 1) B' /\
                QueueFacts.fuzz_in_ok D c'.
Proof.
  intros I ops B A D c k HA Ho Hc Hop.
  destruct (op7_step I ops B A D c k HA Ho Hop) as [E H].
  destruct (QueueFacts.fuzz_u8_ok D c Hc) as (c' & v & Ec & Hc' & _).
  exists (set_g_fail_next B 1), (fst (fuzz_u8_m D c)). split; [exact E|]. split; [exact H|]. rewrite Ec. exact Hc'.
Qed.
