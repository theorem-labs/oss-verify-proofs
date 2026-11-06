(* The address stream of the harness model (TOps.v): LLVMFuzzerTestOneInput_op_m reads A only at its receive index
   k, and returns k or S k; so LLVMFuzzerTestOneInput_loop_m from index k reads A only at indices >= k. The machine
   walk of LLVMFuzzerTestOneInput uses this to fix A k to the address the k-th receive's malloc returned while
   keeping its loop invariant `forall A, ... -> loop_m ... A ... k = Some _` (lib/Prog/T/LLVMFuzzerTestOneInput*.v,
   lib/U/Prog/T/LLVMFuzzerTestOneInput*.v). Build-independent. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TNeed TSess0 TCb TSess TOps.
Import ListNotations.
Open Scope Z_scope.

(* A with index k set to a. *)
Definition aupd (A : nat -> Z) (k : nat) (a : Z) : nat -> Z := fun i => if Nat.eqb i k then a else A i.

Lemma aupd_at : forall A k a, aupd A k a k = a.
Proof. intros A k a. unfold aupd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma aupd_other : forall A k a i, i <> k -> aupd A k a i = A i.
Proof. intros A k a i H. unfold aupd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma op_m_A_ext : forall I B A A' D c k, A k = A' k ->
  LLVMFuzzerTestOneInput_op_m I B A D c k = LLVMFuzzerTestOneInput_op_m I B A' D c k.
Proof. intros I B A A' D c k H. unfold LLVMFuzzerTestOneInput_op_m. rewrite H. reflexivity. Qed.

(* The op returns the receive index unchanged or advanced by one. *)
Lemma op_m_k : forall I B A D c k B1 c1 k1,
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B1, (c1, k1)) -> k1 = k \/ k1 = S k.
Proof.
  intros I B A D c k B1 c1 k1 H. unfold LLVMFuzzerTestOneInput_op_m in H.
  repeat match type of H with
  | Some (_, (_, _)) = Some (_, (_, _)) => injection H as _ _ <-; first [left; reflexivity | right; reflexivity]
  | None = Some _ => discriminate H
  | (if ?b then _ else _) = _ => destruct b
  | (match ?x with _ => _ end) = _ => destruct x
  end.
Qed.

Lemma loop_m_A_ext : forall fuel I B A A' D c k, (forall i, (k <= i)%nat -> A i = A' i) ->
  LLVMFuzzerTestOneInput_loop_m fuel I B A D c k = LLVMFuzzerTestOneInput_loop_m fuel I B A' D c k.
Proof.
  induction fuel as [|f IH]; intros I B A A' D c k H; [reflexivity|].
  cbn [LLVMFuzzerTestOneInput_loop_m].
  destruct (fi_n c =? 0); [reflexivity|].
  rewrite (op_m_A_ext I B A A' D c k (H k (le_n k))).
  destruct (LLVMFuzzerTestOneInput_op_m I B A' D c k) as [[B1 [c1 k1]]|] eqn:E; [|reflexivity].
  apply IH. intros i Hi. apply H.
  destruct (op_m_k I B A' D c k B1 c1 k1 E) as [-> | ->]; lia.
Qed.

(* Whether the op at index k reads A k: the receiving ops (0, 1, 2, 8) do and return S k; the others neither read
   it nor advance k. *)
Lemma op_m_keep_ext : forall I B A A' D c k B1 c1,
  LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B1, (c1, k)) ->
  LLVMFuzzerTestOneInput_op_m I B A' D c k = Some (B1, (c1, k)).
Proof.
  intros I B A A' D c k B1 c1 H. unfold LLVMFuzzerTestOneInput_op_m in *.
  destruct (fuzz_u8_m D c) as [c0 opb].
  destruct (opb mod 9 =? 0).
  { destruct (fuzz_record_m D c0) as [[c2 off] n].
    destruct (receive_m I B (A k) (sub D off (Z.to_nat n)) 0 0) as [[B2 []]|]; [|discriminate H].
    injection H as _ _ E. exfalso. lia. }
  destruct (opb mod 9 =? 1).
  { destruct (op_frame_m I B D (A k) c0) as [[B2 c2]|]; [|discriminate H].
    injection H as _ _ E. exfalso. lia. }
  destruct (opb mod 9 =? 2).
  { destruct (op_announce_m I B D (A k) c0) as [[B2 c2]|]; [|discriminate H].
    injection H as _ _ E. exfalso. lia. }
  destruct (opb mod 9 =? 3); [exact H|].
  destruct (opb mod 9 =? 4); [exact H|].
  destruct (opb mod 9 =? 5); [exact H|].
  destruct (opb mod 9 =? 6); [exact H|].
  destruct (opb mod 9 =? 7); [exact H|].
  destruct (fuzz_u8_m D c0) as [c2 pf].
  destruct (fuzz_record_m D c2) as [[c3 off] n].
  destruct (receive_m I B (A k) (sub D off (Z.to_nat n)) 1 pf) as [[B2 []]|]; [|discriminate H].
  injection H as _ _ E. exfalso. lia.
Qed.

(* The step the walk takes at an op: the invariant at index k for every stream of a class P, the op's result at a
   stream with A k = a (for a receiving op, the address its malloc returned; for any other op, any a), and the class
   closed under setting index k to a; then the invariant at the op's result for every stream of P. *)
Lemma loop_m_step_at : forall (P : (nat -> Z) -> Prop) f I B D c k a B1 c1 k1,
  (forall A, P A -> P (aupd A k a)) ->
  (forall A, P A -> exists B', LLVMFuzzerTestOneInput_loop_m (S f) I B A D c k = Some (B', tt)) ->
  fi_n c <> 0 ->
  (forall A, P A -> LLVMFuzzerTestOneInput_op_m I B (aupd A k a) D c k = Some (B1, (c1, k1))) ->
  forall A, P A -> exists B', LLVMFuzzerTestOneInput_loop_m f I B1 A D c1 k1 = Some (B', tt).
Proof.
  intros P f I B D c k a B1 c1 k1 HP HI Hn HOP A HA.
  pose proof (HOP A HA) as HO.
  destruct (op_m_k I B (aupd A k a) D c k B1 c1 k1 HO) as [-> | ->].
  - (* the op kept k: it did not read A k, so it gives the same result at A itself *)
    pose proof (op_m_keep_ext I B (aupd A k a) A D c k B1 c1 HO) as HO'.
    destruct (HI A HA) as [B' HL]. cbn [LLVMFuzzerTestOneInput_loop_m] in HL.
    destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
    rewrite HO' in HL. exists B'. exact HL.
  - destruct (HI (aupd A k a) (HP A HA)) as [B' HL]. cbn [LLVMFuzzerTestOneInput_loop_m] in HL.
    destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
    rewrite HO in HL. exists B'. rewrite <- HL. apply loop_m_A_ext.
    intros i Hi. symmetry. apply aupd_other. lia.
Qed.

(* The model premise at an op that receives: for every address a of the class, the op at A k = a is not None.
   This is what receive_args / bar_args ask of the receive (`forall a, h_addr_ok a -> receive_m ... a ... <> None`),
   read off the invariant at a stream with A k = a. *)
Lemma loop_m_op_some : forall (P : (nat -> Z) -> Prop) f I B D c k a,
  (forall A, P A -> exists B', LLVMFuzzerTestOneInput_loop_m (S f) I B A D c k = Some (B', tt)) ->
  fi_n c <> 0 ->
  forall A, P A -> A k = a ->
  exists B1 c1 k1, LLVMFuzzerTestOneInput_op_m I B A D c k = Some (B1, (c1, k1)).
Proof.
  intros P f I B D c k a HI Hn A HA Ha.
  destruct (HI A HA) as [B' HL]. cbn [LLVMFuzzerTestOneInput_loop_m] in HL.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
  destruct (LLVMFuzzerTestOneInput_op_m I B A D c k) as [[B1 [c1 k1]]|]; [|discriminate HL].
  exists B1, c1, k1. reflexivity.
Qed.
