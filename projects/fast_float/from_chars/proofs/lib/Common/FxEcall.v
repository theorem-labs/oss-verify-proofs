(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition ecall_ok (t : tree xi) : Prop :=
  forall pc, tlookup t pc = XEcall -> exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = true.

Definition tecall_ok (t : tree xi) : Prop :=
  forall p, tget p t = Some XEcall -> exists w, fetch_word segs (Z_to_bv 64 (Zpos p)) = Some w /\ is_ecall w = true.

#[using="Type"] Lemma tecall_ok_ecall_ok : forall t, tecall_ok t -> ecall_ok t.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t Ht pc Hx. unfold tlookup in Hx. destruct pc as [|p|p]; try discriminate.
  destruct (tget p t) as [x|] eqn:E; [|discriminate]. subst x. exact (Ht p E).
Qed.

#[using="Type"] Lemma xentry_ecall : forall pc, xentry segs pc = XEcall -> exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc H. unfold xentry in H. destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:He; [exists w; split; [reflexivity | exact He]|].
  destruct (decode_any w) as [[i sz]|]; [|discriminate]. destruct (Z.eqb sz 4); [|discriminate].
  exfalso. revert H. unfold xlate, fcvt_x. destruct i; try discriminate;
    repeat match goal with |- (match ?x with _ => _ end) = _ -> _ => destruct x; try discriminate end.
Qed.

#[using="Type"] Lemma mk_tbl_acc_ecall : forall n pc t, tecall_ok t -> tecall_ok (mk_tbl_acc segs n pc t).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros pc t Ht; cbn [mk_tbl_acc]; [exact Ht|].
  apply IH. destruct pc as [|p|p]; try exact Ht.
  intros q Hq. destruct (Pos.eq_dec q p) as [->|Hne].
  - rewrite tget_tset_same in Hq. injection Hq as Hq. exact (xentry_ecall _ Hq).
  - rewrite tget_tset_other in Hq by congruence. exact (Ht q Hq).
Qed.

#[using="Type"] Lemma mk_tbl_ranges_ecall : forall rs, ecall_ok (mk_tbl_ranges segs rs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rs. apply tecall_ok_ecall_ok. unfold mk_tbl_ranges.
  assert (H0 : tecall_ok TEmpty) by (intros p H; rewrite tget_empty in H; discriminate).
  revert H0. generalize (@TEmpty xi) as t. induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_tbl_ranges_acc]; [exact Ht|].
  apply IH. apply mk_tbl_acc_ecall. exact Ht.
Qed.

(* [comment removed for export] *)
Definition svc_set (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

#[using="Type"] Lemma ecall_step : forall ms w, fetch_word segs (ms_pc ms) = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs ms = MachineOk (svc_set ms).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms w Hf He. unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

#[using="Type"] Lemma fx_ecall_step : forall t E L ms, ecall_ok t -> tlookup t (s_pc L) = XEcall -> sden segs E L ms ->
  RiscvSemantics.step segs ms = MachineOk (svc_set ms) /\ ms_svc_pending ms = None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t E L ms Ht Hx Hd. destruct (Ht _ Hx) as (w & Hf & He).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & _).
  split; [|exact Hsvc]. apply (ecall_step ms w); [|exact He].
  unfold ms_pc. rewrite Hpc. exact Hf.
Qed.
End WithSegs.
