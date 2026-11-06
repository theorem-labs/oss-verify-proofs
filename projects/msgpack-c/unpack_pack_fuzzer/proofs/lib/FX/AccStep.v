(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Acc.
Import ListNotations.
Import W64 Val Mem FI St Step.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AccStep.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Lemma account_step_gen : forall ms w i ms' mo (Q : Model -> Prop),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  (forall acc, Forall (fun an => Acc.mem_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) (fst an) (snd an)) acc ->
     exists mo', materialize_model_accesses mo acc = Some mo' /\ Q mo') ->
  exists mo', mi_account_step segs ms mo = MachineOk (ms', mo') /\ Q mo'.
Proof.
  intros ms w i ms' mo Q Hf He Hd Hstep HM.
  unfold mi_account_step. unfold RiscvSemantics.step in Hstep.
  destruct (step_accesses segs ms) as [report| |] eqn:SA; cbn [drop_access_report] in Hstep; try discriminate.
  injection Hstep as Hv.
  pose proof (Acc.step_accesses_accs segs ms w i report Hf He Hd SA) as FA.
  destruct report as [v acc]. cbn [access_value accessed_ranges] in *. subst v.
  destruct (HM acc FA) as (mo' & M & HQ). exists mo'. rewrite M. split; [reflexivity| exact HQ].
Qed.

Section Law.
Variable CH : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAW : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CH os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.

Theorem st_ok_account : forall E st' ms ms' model w i,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  st_ok segs OPS E st' ms' model ->
  (forall a n j, Acc.mem_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) a n -> 0 <= j < Z.of_nat n ->
     CH (insts E (s_ops st')) (ms_mem ms') model (bv_unsigned a + j)) ->
  exists mo', mi_account_step segs ms model = MachineOk (ms', mo') /\ st_ok segs OPS E st' ms' mo'.
Proof.
  intros E st' ms ms' model w i Hf He Hd Hstep HS' HCH.
  apply (account_step_gen ms w i ms' model (fun mo' => st_ok segs OPS E st' ms' mo') Hf He Hd Hstep).
  intros acc FA.
  pose proof (so_ops _ _ _ _ _ _ HS') as HO. apply (proj1 (ops_hold_insts OPS E _ _ _)) in HO.
  destruct (LAW (insts E (s_ops st')) (ms_mem ms') model acc (so_mf _ _ _ _ _ _ HS') HO) as (mo' & M & HMI & HO').
  { intros a n j Hin Hj. apply (HCH a n j); [| exact Hj].
    exact (proj1 (Forall_forall _ _) FA (a, n) Hin). }
  exists mo'. split; [exact M|].
  destruct HS' as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19].
  constructor; try assumption.
  apply (proj2 (ops_hold_insts OPS E _ _ _)). exact HO'.
Qed.

Theorem st_ok_account_mp : forall (MP : Model -> Prop),
  (forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo') ->
  forall E st' ms ms' model w i,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  st_ok segs OPS E st' ms' model -> MP model ->
  (forall a n j, Acc.mem_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) a n -> 0 <= j < Z.of_nat n ->
     CH (insts E (s_ops st')) (ms_mem ms') model (bv_unsigned a + j)) ->
  exists mo', mi_account_step segs ms model = MachineOk (ms', mo') /\ st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros MP HMPA E st' ms ms' model w i Hf He Hd Hstep HS' HMP HCH.
  apply (account_step_gen ms w i ms' model (fun mo' => st_ok segs OPS E st' ms' mo' /\ MP mo') Hf He Hd Hstep).
  intros acc FA.
  pose proof (so_ops _ _ _ _ _ _ HS') as HO. apply (proj1 (ops_hold_insts OPS E _ _ _)) in HO.
  destruct (LAW (insts E (s_ops st')) (ms_mem ms') model acc (so_mf _ _ _ _ _ _ HS') HO) as (mo' & M & HMI & HO').
  { intros a n j Hin Hj. apply (HCH a n j); [| exact Hj].
    exact (proj1 (Forall_forall _ _) FA (a, n) Hin). }
  exists mo'. split; [exact M|]. split; [| exact (HMPA model acc mo' HMP M)].
  destruct HS' as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19].
  constructor; try assumption.
  apply (proj2 (ops_hold_insts OPS E _ _ _)). exact HO'.
Qed.

Corollary rz_account : forall E st' ms ms' model w i K,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  RiscvSemantics.step segs ms = MachineOk ms' -> ms_svc_pending ms = None -> m_halted model = None ->
  st_ok segs OPS E st' ms' model ->
  (forall a n j, Acc.mem_acc i (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) a n -> 0 <= j < Z.of_nat n ->
     CH (insts E (s_ops st')) (ms_mem ms') model (bv_unsigned a + j)) ->
  (forall mo', st_ok segs OPS E st' ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros E st' ms ms' model w i K Hf He Hd Hstep Hsvc Hh HS' HCH HK.
  destruct (st_ok_account E st' ms ms' model w i Hf He Hd Hstep HS' HCH) as (mo' & AS & HS2).
  exact (rz_astep segs ms model ms' mo' K Hh Hsvc AS (HK mo' HS2)).
Qed.
End Law.

Definition CH_cov (os : list oinst) (_ : word -> option byte) (_ : Model) (z : Z) : Prop := op_cov OPS os z.
Lemma LAW_cov : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CH_cov os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.
Proof. intros os m mo acc MI HO HC. exact (op_acc OPS os m mo acc MI HO HC). Qed.

End WithSegs.
End AccStep.
