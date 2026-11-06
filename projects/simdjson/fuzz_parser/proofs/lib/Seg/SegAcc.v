(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module SAC.

(* [comment removed for export] *)
Definition eff_nomem (t : eff) : Prop := match t with ELoad _ _ _ | EStore _ _ _ _ => False | _ => True end.

(* [comment removed for export] *)
Definition eff_simple (t : eff) : Prop :=
  match t with
  | ELoad _ _ k => forall v, eff_nomem (k v)
  | EStore _ _ _ k => eff_nomem k
  | _ => True
  end.

Definition eff_accs (t : eff) : list (word * nat) :=
  match t with
  | ELoad n a _ => [(a, width_bytes n)]
  | EStore n a _ _ => [(a, width_bytes n)]
  | _ => []
  end.

Definition is_atomic (i : instr) : bool := match i with Lr _ _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition mem_kind (i : instr) : bool :=
  match i with Load _ _ _ _ _ | Store _ _ _ _ | FLoad _ _ _ _ | FStore _ _ _ _ => true | _ => false end.

Definition msz_nb (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.
Definition fmt_nb (fmt : ffmt) : nat := match fmt with FMT_S => 4 | FMT_D => 8 end.

Lemma eff_accs_nonmem : forall sz i c, mem_kind i = false -> is_atomic i = false -> eff_accs (exec sz i c) = [].
Proof.
  intros sz i c H1 H2. destruct i; try discriminate H1; try discriminate H2; cbn [exec];
    repeat (cbn; match goal with |- context [match ?x with _ => _ end] => destruct x end); try reflexivity;
    unfold exec_csr; repeat (cbn; match goal with |- context [match ?x with _ => _ end] => destruct x end); reflexivity.
Qed.

Lemma eff_accs_load : forall sz msz sgn rd rs1 imm c,
  eff_accs (exec sz (Load msz sgn rd rs1 imm) c) = [(rget c rs1 + sext 64 imm, msz_nb msz)].
Proof. intros. cbn [exec]. unfold load_val. destruct msz; reflexivity. Qed.

Lemma eff_accs_store : forall sz msz rs1 rs2 imm c,
  eff_accs (exec sz (Store msz rs1 rs2 imm) c) = [(rget c rs1 + sext 64 imm, msz_nb msz)].
Proof. intros. cbn [exec]. unfold store_val. destruct msz; reflexivity. Qed.

Lemma eff_accs_fload : forall sz fmt rd rs1 imm c,
  eff_accs (exec sz (FLoad fmt rd rs1 imm) c) = [(rget c rs1 + sext 64 imm, fmt_nb fmt)].
Proof. intros. cbn [exec]. destruct fmt; reflexivity. Qed.

Lemma eff_accs_fstore : forall sz fmt rs1 rs2 imm c,
  eff_accs (exec sz (FStore fmt rs1 rs2 imm) c) = [(rget c rs1 + sext 64 imm, fmt_nb fmt)].
Proof. intros. cbn [exec]. destruct fmt; reflexivity. Qed.

Section Steps.
Variable segs : list Segment.

Lemma nomem_accs : forall t m r, eff_nomem t -> interp_eff_accesses segs t m = MachineOk r -> @accessed_ranges _ r = [].
Proof. intros t m r H E. destruct t; try contradiction; cbn in E; try discriminate. injection E as <-. reflexivity. Qed.

Lemma simple_accs : forall t m r, eff_simple t -> interp_eff_accesses segs t m = MachineOk r -> @accessed_ranges _ r = eff_accs t.
Proof.
  intros t m r H E. destruct t as [c|c|c|c|c|c|n a k|n a v k]; cbn [eff_simple eff_accs] in *; cbn [interp_eff_accesses] in E; try discriminate.
  - injection E as <-. reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r'| |] eqn:E'; try discriminate.
    injection E as <-. cbn. rewrite (nomem_accs _ _ _ (H _) E'). reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r'| |] eqn:E'; try discriminate.
    injection E as <-. cbn. rewrite (nomem_accs _ _ _ H E'). reflexivity.
Qed.

Ltac nomem_cases :=
  repeat (cbn; match goal with
  | |- forall v, _ => intros ?
  | |- context [match ?x with _ => _ end] => destruct x
  end); cbn; try exact I.

Lemma exec_simple : forall sz i c, is_atomic i = false -> eff_simple (exec sz i c).
Proof.
  intros sz i c H. destruct i; try discriminate H; cbn [exec];
    try solve [ exact I
              | unfold load_val; nomem_cases
              | unfold store_val; nomem_cases
              | unfold exec_csr; nomem_cases
              | nomem_cases ].
Qed.

(* [comment removed for export] *)
Lemma step_accesses_simple : forall ms ms' w i sz,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) -> is_atomic i = false ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  RiscvSemantics.step_accesses segs ms =
    MachineOk (@mkAccessReport machine_state ms' (eff_accs (exec (Z_to_bv 64 sz) i
                 {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}))).
Proof.
  intros ms ms' w i sz Hf He Hd Ha Hs.
  unfold RiscvSemantics.step in Hs. unfold RiscvSemantics.step_accesses in Hs |- *. rewrite Hf in Hs |- *.
  unfold RiscvSemantics.decode_exec_accesses in Hs |- *. rewrite He, Hd in Hs |- *.
  pose proof (exec_simple (Z_to_bv 64 sz) i
                {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |} Ha) as HS.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:E; cbn in Hs; try discriminate.
  destruct r as [[c m'] accs]. cbn in Hs |- *. injection Hs as <-.
  pose proof (simple_accs _ _ _ HS E) as A. cbn in A. rewrite A. reflexivity.
Qed.

End Steps.
End SAC.
