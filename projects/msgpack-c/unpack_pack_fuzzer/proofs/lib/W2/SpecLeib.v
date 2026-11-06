(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Frame.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module SpecLeib.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Definition rg (R : bvmap 5 word) (k : Z) : word := reg_get R (Z_to_bv 5 k).
Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  AF.mkR (rg R 1) (rg R 2) (rg R 3) (rg R 4) (rg R 5) (rg R 6) (rg R 7) (rg R 8) (rg R 9) (rg R 10) (rg R 11) (rg R 12) (rg R 13) (rg R 14) (rg R 15)
         (rg R 16) (rg R 17) (rg R 18) (rg R 19) (rg R 20) (rg R 21) (rg R 22) (rg R 23) (rg R 24) (rg R 25) (rg R 26) (rg R 27) (rg R 28) (rg R 29)
         (rg R 30) (rg R 31).
Definition shape (R : bvmap 5 word) : Prop := R = mkR_of R.

Lemma shape_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  shape (AF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. reflexivity. Qed.

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Lemma shape_set : forall R (r : reg) v, shape R -> is_x0 r = false -> shape (bvmap_set r v R).
Proof.
  intros R r v H NZ. unfold shape in H. rewrite H. unfold mkR_of.
  generalize (rg R 1) (rg R 2) (rg R 3) (rg R 4) (rg R 5) (rg R 6) (rg R 7) (rg R 8) (rg R 9) (rg R 10) (rg R 11) (rg R 12) (rg R 13) (rg R 14) (rg R 15)
         (rg R 16) (rg R 17) (rg R 18) (rg R 19) (rg R 20) (rg R 21) (rg R 22) (rg R 23) (rg R 24) (rg R 25) (rg R 26) (rg R 27) (rg R 28) (rg R 29)
         (rg R 30) (rg R 31).
  clear H. intros.
  destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [discriminate NZ|].
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Fixpoint eff_leaves (P : core -> Prop) (t : eff) : Prop :=
  match t with
  | EDone c => P c
  | ELoad n a k => forall v, eff_leaves P (k v)
  | EStore n a v k => eff_leaves P k
  | _ => True
  end.

Definition keep (c c' : core) : Prop :=
  c_fregs c' = c_fregs c /\ c_fcsr c' = c_fcsr c /\ (shape (c_regs c) -> shape (c_regs c')).

Lemma keep_refl : forall c, keep c c. Proof. intros c. split; [reflexivity|]. split; [reflexivity| auto]. Qed.
Lemma keep_trans : forall a b c, keep a b -> keep b c -> keep a c.
Proof. intros a b c (A1 & A2 & A3) (B1 & B2 & B3). split; [congruence|]. split; [congruence| auto]. Qed.
Lemma keep_with_pc : forall v c, keep c (with_pc v c). Proof. intros v c. split; [reflexivity|]. split; [reflexivity| auto]. Qed.
Lemma keep_rset : forall r v c, keep c (rset r v c).
Proof.
  intros r v c. unfold rset. destruct (is_x0 r) eqn:Z; [apply keep_refl|].
  split; [reflexivity|]. split; [reflexivity|]. cbn [with_regs c_regs]. intros S. apply shape_set; assumption.
Qed.
Lemma keep_inval_resv : forall a c, keep c (inval_resv a c).
Proof.
  intros a c. unfold inval_resv. destruct (c_resv c); [| apply keep_refl].
  destruct (Z.eqb _ _); [| apply keep_refl]. split; [reflexivity|]. split; [reflexivity| auto].
Qed.

Definition int_instr (i : instr) : bool :=
  match i with
  | Lui _ _ | Auipc _ _ | Jal _ _ | Jalr _ _ _ | Branch _ _ _ _ | Load _ _ _ _ _ | Store _ _ _ _ | OpImm _ _ _ _ | ShiftImm _ _ _ _
  | Op _ _ _ _ | OpImm32 _ _ _ | ShiftImm32 _ _ _ _ | Op32 _ _ _ _ | Fence _ _ _ _ _ | FenceI _ _ _ | Mul _ _ _ _ | Mul32 _ _ _ _ => true
  | _ => false
  end.

Lemma exec_keep : forall sz i c, int_instr i = true -> eff_leaves (keep c) (exec sz i c).
Proof.
  intros sz i c H. destruct i; try discriminate H; cbn [exec eff_leaves];
    try (eapply keep_trans; [apply keep_with_pc| apply keep_rset]);
    try apply keep_with_pc.
  -   destruct sz0; cbn [load_val eff_leaves]; intros v; (eapply keep_trans; [apply keep_with_pc| apply keep_rset]).
  -   destruct sz0; cbn [store_val eff_leaves]; (eapply keep_trans; [apply keep_with_pc| apply keep_inval_resv]).
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_leaves : forall (P : core -> Prop) t m report,
  eff_leaves P t -> interp_eff_accesses segs t m = MachineOk report -> P (fst (@access_value _ report)).
Proof.
  intros P t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m report HP H; cbn in H; try discriminate.
  - injection H as <-. exact HP.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m r (HP _) Hr).
  - destruct (store_ok segs m a (width_bytes n)) eqn:SO; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ r HP Hr).
Qed.

Definition mkeep (ms ms' : machine_state) : Prop :=
  ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ (shape (ms_regs ms) -> shape (ms_regs ms')).
Lemma mkeep_refl : forall ms, mkeep ms ms. Proof. intros ms. split; [reflexivity|]. split; [reflexivity| auto]. Qed.
Lemma mkeep_trans : forall a b c, mkeep a b -> mkeep b c -> mkeep a c.
Proof. intros a b c (A1 & A2 & A3) (B1 & B2 & B3). split; [congruence|]. split; [congruence| auto]. Qed.

Lemma step_keep : forall ms w i isz report,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, isz) ->
  step_accesses segs ms = MachineOk report -> int_instr i = true ->
  mkeep ms (@access_value _ report).
Proof.
  intros ms w i isz report Hf He Hd H HI.
  unfold step_accesses in H. unfold ms_pc in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Hr; try discriminate.
  pose proof (interp_leaves _ _ _ _ (exec_keep _ i _ HI) Hr) as X.
  destruct r as [[c' m'] acc]. cbn in H. injection H as <-. cbn in X |- *. exact X.
Qed.
End WithSegs.
End SpecLeib.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module SpecLeib.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Definition rg (R : bvmap 5 word) (k : Z) : word := reg_get R (Z_to_bv 5 k).
Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  AF.mkR (rg R 1) (rg R 2) (rg R 3) (rg R 4) (rg R 5) (rg R 6) (rg R 7) (rg R 8) (rg R 9) (rg R 10) (rg R 11) (rg R 12) (rg R 13) (rg R 14) (rg R 15)
         (rg R 16) (rg R 17) (rg R 18) (rg R 19) (rg R 20) (rg R 21) (rg R 22) (rg R 23) (rg R 24) (rg R 25) (rg R 26) (rg R 27) (rg R 28) (rg R 29)
         (rg R 30) (rg R 31).
Definition shape (R : bvmap 5 word) : Prop := R = mkR_of R.

Lemma shape_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  shape (AF.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. reflexivity. Qed.

Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Lemma shape_set : forall R (r : reg) v, shape R -> is_x0 r = false -> shape (bvmap_set r v R).
Proof.
  intros R r v H NZ. unfold shape in H. rewrite H. unfold mkR_of.
  generalize (rg R 1) (rg R 2) (rg R 3) (rg R 4) (rg R 5) (rg R 6) (rg R 7) (rg R 8) (rg R 9) (rg R 10) (rg R 11) (rg R 12) (rg R 13) (rg R 14) (rg R 15)
         (rg R 16) (rg R 17) (rg R 18) (rg R 19) (rg R 20) (rg R 21) (rg R 22) (rg R 23) (rg R 24) (rg R 25) (rg R 26) (rg R 27) (rg R 28) (rg R 29)
         (rg R 30) (rg R 31).
  clear H. intros.
  destruct (reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [discriminate NZ|].
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Fixpoint eff_leaves (P : core -> Prop) (t : eff) : Prop :=
  match t with
  | EDone c => P c
  | ELoad n a k => forall v, eff_leaves P (k v)
  | EStore n a v k => eff_leaves P k
  | _ => True
  end.

Definition keep (c c' : core) : Prop :=
  c_fregs c' = c_fregs c /\ c_fcsr c' = c_fcsr c /\ (shape (c_regs c) -> shape (c_regs c')).

Lemma keep_refl : forall c, keep c c. Proof. intros c. split; [reflexivity|]. split; [reflexivity| auto]. Qed.
Lemma keep_trans : forall a b c, keep a b -> keep b c -> keep a c.
Proof. intros a b c (A1 & A2 & A3) (B1 & B2 & B3). split; [congruence|]. split; [congruence| auto]. Qed.
Lemma keep_with_pc : forall v c, keep c (with_pc v c). Proof. intros v c. split; [reflexivity|]. split; [reflexivity| auto]. Qed.
Lemma keep_rset : forall r v c, keep c (rset r v c).
Proof.
  intros r v c. unfold rset. destruct (is_x0 r) eqn:Z; [apply keep_refl|].
  split; [reflexivity|]. split; [reflexivity|]. cbn [with_regs c_regs]. intros S. apply shape_set; assumption.
Qed.
Lemma keep_inval_resv : forall a c, keep c (inval_resv a c).
Proof.
  intros a c. unfold inval_resv. destruct (c_resv c); [| apply keep_refl].
  destruct (Z.eqb _ _); [| apply keep_refl]. split; [reflexivity|]. split; [reflexivity| auto].
Qed.

Definition int_instr (i : instr) : bool :=
  match i with
  | Lui _ _ | Auipc _ _ | Jal _ _ | Jalr _ _ _ | Branch _ _ _ _ | Load _ _ _ _ _ | Store _ _ _ _ | OpImm _ _ _ _ | ShiftImm _ _ _ _
  | Op _ _ _ _ | OpImm32 _ _ _ | ShiftImm32 _ _ _ _ | Op32 _ _ _ _ | Fence _ _ _ _ _ | FenceI _ _ _ | Mul _ _ _ _ | Mul32 _ _ _ _ => true
  | _ => false
  end.

Lemma exec_keep : forall sz i c, int_instr i = true -> eff_leaves (keep c) (exec sz i c).
Proof.
  intros sz i c H. destruct i; try discriminate H; cbn [exec eff_leaves];
    try (eapply keep_trans; [apply keep_with_pc| apply keep_rset]);
    try apply keep_with_pc.
  -   destruct sz0; cbn [load_val eff_leaves]; intros v; (eapply keep_trans; [apply keep_with_pc| apply keep_rset]).
  -   destruct sz0; cbn [store_val eff_leaves]; (eapply keep_trans; [apply keep_with_pc| apply keep_inval_resv]).
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_leaves : forall (P : core -> Prop) t m report,
  eff_leaves P t -> interp_eff_accesses segs t m = MachineOk report -> P (fst (@access_value _ report)).
Proof.
  intros P t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m report HP H; cbn in H; try discriminate.
  - injection H as <-. exact HP.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ m r (HP _) Hr).
  - destruct (store_ok segs m a (width_bytes n)) eqn:SO; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn [access_value]. exact (IH _ r HP Hr).
Qed.

Definition mkeep (ms ms' : machine_state) : Prop :=
  ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ (shape (ms_regs ms) -> shape (ms_regs ms')).
Lemma mkeep_refl : forall ms, mkeep ms ms. Proof. intros ms. split; [reflexivity|]. split; [reflexivity| auto]. Qed.
Lemma mkeep_trans : forall a b c, mkeep a b -> mkeep b c -> mkeep a c.
Proof. intros a b c (A1 & A2 & A3) (B1 & B2 & B3). split; [congruence|]. split; [congruence| auto]. Qed.

Lemma step_keep : forall ms w i isz report,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, isz) ->
  step_accesses segs ms = MachineOk report -> int_instr i = true ->
  mkeep ms (@access_value _ report).
Proof.
  intros ms w i isz report Hf He Hd H HI.
  unfold step_accesses in H. unfold ms_pc in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Hr; try discriminate.
  pose proof (interp_leaves _ _ _ _ (exec_keep _ i _ HI) Hr) as X.
  destruct r as [[c' m'] acc]. cbn in H. injection H as <-. cbn in X |- *. exact X.
Qed.
End WithSegs.
End SpecLeib.
End TwinB.
