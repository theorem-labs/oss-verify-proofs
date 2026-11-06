(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Acc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module SpecFrame.

Definition store_acc (i : instr) (c : core) (a : word) (n : nat) : Prop :=
  match i with
  | Load _ _ _ _ _ | FLoad _ _ _ _ | Lr _ _ _ _ _ => False
  | _ => Acc.mem_acc i c a n
  end.

Fixpoint eff_stores_in (P : word -> nat -> Prop) (t : eff) : Prop :=
  match t with
  | ELoad n a k => forall v, eff_stores_in P (k v)
  | EStore n a v k => P a (width_bytes n) /\ eff_stores_in P k
  | _ => True
  end.

Lemma accs_stores : forall P t, Acc.eff_accs_in P t -> eff_stores_in P t.
Proof.
  intros P t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; cbn; intros H; try exact I.
  - destruct H as [_ H]. intros v. exact (IH v (H v)).
  - destruct H as [Pa H]. split; [exact Pa| exact (IH H)].
Qed.

Lemma exec_stores : forall sz i c, eff_stores_in (store_acc i c) (exec sz i c).
Proof.
  intros sz i c.
  destruct i; try (apply accs_stores; exact (Acc.exec_accs sz _ c));
    cbn [exec store_acc];
    repeat match goal with
           | |- context [match ?x with _ => _ end] => destruct x
           | |- context [if ?x then _ else _] => destruct x
           end; cbn; intros; auto.
  all: unfold load_val; repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; cbn; intros; auto.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_inv : forall (P : word -> nat -> Prop) (Inv : (word -> option byte) -> Prop) t m report,
  eff_stores_in P t -> interp_eff_accesses segs t m = MachineOk report ->
  (forall m1 a bs, Inv m1 -> P a (length bs) -> store_ok segs m1 a (length bs) = true -> Inv (write_to_mem m1 a bs)) ->
  Inv m -> Inv (snd (@access_value _ report)).
Proof.
  intros P Inv t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m report HP H HW HI; cbn in H; try discriminate.
  - injection H as <-. exact HI.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m r (HP _) Hr HW HI).
  - destruct HP as [Pa Pk].
    destruct (store_ok segs m a (width_bytes n)) eqn:SO; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. apply (IH _ r Pk Hr HW).
    apply HW; [exact HI| |]; rewrite length_Z_to_le_bytes; assumption.
Qed.

Lemma step_inv : forall (Inv : (word -> option byte) -> Prop) ms w i report,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  step_accesses segs ms = MachineOk report ->
  (forall m1 a bs, Inv m1 ->
     store_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) a (length bs) ->
     store_ok segs m1 a (length bs) = true -> Inv (write_to_mem m1 a bs)) ->
  Inv (ms_mem ms) -> Inv (ms_mem (@access_value _ report)).
Proof.
  intros Inv ms w i report Hf He Hd H HW HI.
  unfold step_accesses in H. unfold ms_pc in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Hr; try discriminate.
  pose proof (interp_inv _ Inv _ _ _ (exec_stores _ i _) Hr HW HI) as X.
  destruct r as [[c' m'] acc]. cbn in H. injection H as <-. cbn in X |- *. exact X.
Qed.

End WithSegs.
End SpecFrame.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Acc.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module SpecFrame.

Definition store_acc (i : instr) (c : core) (a : word) (n : nat) : Prop :=
  match i with
  | Load _ _ _ _ _ | FLoad _ _ _ _ | Lr _ _ _ _ _ => False
  | _ => Acc.mem_acc i c a n
  end.

Fixpoint eff_stores_in (P : word -> nat -> Prop) (t : eff) : Prop :=
  match t with
  | ELoad n a k => forall v, eff_stores_in P (k v)
  | EStore n a v k => P a (width_bytes n) /\ eff_stores_in P k
  | _ => True
  end.

Lemma accs_stores : forall P t, Acc.eff_accs_in P t -> eff_stores_in P t.
Proof.
  intros P t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; cbn; intros H; try exact I.
  - destruct H as [_ H]. intros v. exact (IH v (H v)).
  - destruct H as [Pa H]. split; [exact Pa| exact (IH H)].
Qed.

Lemma exec_stores : forall sz i c, eff_stores_in (store_acc i c) (exec sz i c).
Proof.
  intros sz i c.
  destruct i; try (apply accs_stores; exact (Acc.exec_accs sz _ c));
    cbn [exec store_acc];
    repeat match goal with
           | |- context [match ?x with _ => _ end] => destruct x
           | |- context [if ?x then _ else _] => destruct x
           end; cbn; intros; auto.
  all: unfold load_val; repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; cbn; intros; auto.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_inv : forall (P : word -> nat -> Prop) (Inv : (word -> option byte) -> Prop) t m report,
  eff_stores_in P t -> interp_eff_accesses segs t m = MachineOk report ->
  (forall m1 a bs, Inv m1 -> P a (length bs) -> store_ok segs m1 a (length bs) = true -> Inv (write_to_mem m1 a bs)) ->
  Inv m -> Inv (snd (@access_value _ report)).
Proof.
  intros P Inv t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m report HP H HW HI; cbn in H; try discriminate.
  - injection H as <-. exact HI.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m r (HP _) Hr HW HI).
  - destruct HP as [Pa Pk].
    destruct (store_ok segs m a (width_bytes n)) eqn:SO; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. apply (IH _ r Pk Hr HW).
    apply HW; [exact HI| |]; rewrite length_Z_to_le_bytes; assumption.
Qed.

Lemma step_inv : forall (Inv : (word -> option byte) -> Prop) ms w i report,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  step_accesses segs ms = MachineOk report ->
  (forall m1 a bs, Inv m1 ->
     store_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) a (length bs) ->
     store_ok segs m1 a (length bs) = true -> Inv (write_to_mem m1 a bs)) ->
  Inv (ms_mem ms) -> Inv (ms_mem (@access_value _ report)).
Proof.
  intros Inv ms w i report Hf He Hd H HW HI.
  unfold step_accesses in H. unfold ms_pc in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Hr; try discriminate.
  pose proof (interp_inv _ Inv _ _ _ (exec_stores _ i _) Hr HW HI) as X.
  destruct r as [[c' m'] acc]. cbn in H. injection H as <-. cbn in X |- *. exact X.
Qed.

End WithSegs.
End SpecFrame.
End TwinB.
