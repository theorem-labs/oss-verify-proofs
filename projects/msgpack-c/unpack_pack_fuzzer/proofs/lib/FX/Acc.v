(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Module Acc.

Definition msz_nat (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%nat.
Definition aw_nat (wd : awidth) : nat := match wd with AW => 4 | AD => 8 end%nat.
Definition fmt_nat (f : ffmt) : nat := match f with FMT_S => 4 | FMT_D => 8 end%nat.

Definition mem_acc (i : instr) (c : core) (a : word) (n : nat) : Prop :=
  match i with
  | Load msz _ _ rs1 imm => a = (rget c rs1 + sext 64 imm)%bv /\ n = msz_nat msz
  | Store msz rs1 _ imm => a = (rget c rs1 + sext 64 imm)%bv /\ n = msz_nat msz
  | Lr wd _ _ _ rs1 => a = rget c rs1 /\ n = aw_nat wd
  | Sc wd _ _ _ rs1 _ => a = rget c rs1 /\ n = aw_nat wd
  | Amo _ wd _ _ _ rs1 _ => a = rget c rs1 /\ n = aw_nat wd
  | FLoad fmt _ rs1 imm => a = (rget c rs1 + sext 64 imm)%bv /\ n = fmt_nat fmt
  | FStore fmt rs1 _ imm => a = (rget c rs1 + sext 64 imm)%bv /\ n = fmt_nat fmt
  | _ => False
  end.

Fixpoint eff_accs_in (P : word -> nat -> Prop) (t : eff) : Prop :=
  match t with
  | ELoad n a k => P a (width_bytes n) /\ forall v, eff_accs_in P (k v)
  | EStore n a v k => P a (width_bytes n) /\ eff_accs_in P k
  | _ => True
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_accs_in : forall P t m report,
  eff_accs_in P t -> interp_eff_accesses segs t m = MachineOk report ->
  Forall (fun an => P (fst an) (snd an)) (@accessed_ranges _ report).
Proof.
  intros P t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m report HP H; cbn in H;
    try discriminate.
  - injection H as <-. constructor.
  - destruct HP as [Pa Pk].
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn. constructor; [exact Pa|]. exact (IH _ m r (Pk _) Hr).
  - destruct HP as [Pa Pk].
    destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn. constructor; [exact Pa|]. exact (IH _ r Pk Hr).
Qed.

Lemma exec_csr_accs : forall P op rd operand writes csr c, eff_accs_in P (exec_csr op rd operand writes csr c).
Proof.
  intros. unfold exec_csr.
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x
         | |- context [if ?x then _ else _] => destruct x
         end; cbn; auto.
Qed.

Lemma exec_accs : forall sz i c, eff_accs_in (mem_acc i c) (exec sz i c).
Proof.
  intros sz i c. destruct i; cbn [exec mem_acc];
    try exact I;
    try (apply exec_csr_accs).
  all: repeat match goal with
         | |- eff_accs_in _ (exec_csr _ _ _ _ _ _) => apply exec_csr_accs
         | |- context [match ?x with _ => _ end] => destruct x
         | |- context [if ?x then _ else _] => destruct x
         end; cbn; auto.
  all: try (split; [split; reflexivity|]; intros; cbn; auto).
  - destruct sz0; cbn; (split; [split; reflexivity| intros; exact I]).
  - destruct sz0; cbn; (split; [split; reflexivity| exact I]).
Qed.

Lemma step_accesses_accs : forall ms w i report,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  step_accesses segs ms = MachineOk report ->
  Forall (fun an => mem_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) (fst an) (snd an))
         (@accessed_ranges _ report).
Proof.
  intros ms w i report Hf He Hd H.
  unfold step_accesses in H. unfold ms_pc in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Hr; try discriminate.
  destruct r as [[c' m'] acc]. cbn in H. injection H as <-. cbn.
  exact (interp_accs_in _ _ _ _ (exec_accs _ i _) Hr).
Qed.

Lemma materialize_nil : forall mo, materialize_model_accesses mo [] = Some mo.
Proof. intros [fd [maps lz mat] io fs proc lim]. reflexivity. Qed.

Lemma account_step_noacc : forall ms w i ms' mo,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  (forall c a n, ~ mem_acc i c a n) ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  mi_account_step segs ms mo = MachineOk (ms', mo).
Proof.
  intros ms w i ms' mo Hf He Hd NM Hstep.
  unfold mi_account_step. unfold RiscvSemantics.step in Hstep.
  destruct (step_accesses segs ms) as [report| |] eqn:SA; cbn [drop_access_report] in Hstep; try discriminate.
  injection Hstep as Hv.
  pose proof (step_accesses_accs ms w i report Hf He Hd SA) as FA.
  destruct report as [v acc]. cbn [access_value accessed_ranges] in *. subst v.
  destruct acc as [|[a n] rest]; [rewrite materialize_nil; reflexivity|].
  exfalso. apply Forall_inv in FA. exact (NM _ _ _ FA).
Qed.

Lemma account_step_ecall : forall ms w ms' mo,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  mi_account_step segs ms mo = MachineOk (ms', mo).
Proof.
  intros ms w ms' mo Hf He Hstep.
  unfold mi_account_step. unfold RiscvSemantics.step in Hstep. unfold step_accesses in *. unfold ms_pc in *. rewrite Hf in *.
  unfold decode_exec_accesses in *. rewrite He in *. cbn [drop_access_report access_value] in Hstep. injection Hstep as <-.
  cbn [accessed_ranges access_value]. rewrite materialize_nil. reflexivity.
Qed.

End WithSegs.
End Acc.
