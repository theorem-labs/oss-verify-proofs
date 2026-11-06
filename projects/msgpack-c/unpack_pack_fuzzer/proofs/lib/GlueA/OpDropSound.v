(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps OpDropC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan ValP StepB StepS PlanS CtrLib OpDropC.
Open Scope Z_scope.
Unset Lia Cache.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.

Lemma drop_In : forall id os o, In o (drop_ops id os) -> In o os.
Proof. intros id os o H. unfold drop_ops in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma ms_with_mem_id : forall ms, ms_svc_pending ms = None -> ms_with_mem ms (ms_mem ms) = ms.
Proof. intros ms H. destruct ms. cbn in H. subst. reflexivity. Qed.

Theorem op_drop_sound : forall id pc, contract_sound segs OPS MP PB (op_drop_c id pc).
Proof.
  intros id pc st sts Hpc HAP K E ms mo HS HMP HPB HK. cbn [op_drop_c c_apply] in HAP. unfold op_drop_apply in HAP.
  destruct (find_op id (s_ops st)) as [args0|]; [|discriminate HAP].
  destruct (PrimInt63.eqb id HEAP_ID) eqn:Q; [discriminate HAP|]. injection HAP as <-.
  apply Uint63.eqb_false_spec in Q.
  assert (HS' : st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) ([] ++ s_facts st) (drop_ops id (s_ops st)) (s_priv st) (s_next st))
                      (ms_with_mem ms (ms_mem ms)) mo).
  { apply (st_ok_memops segs OPS E st ms mo mo [] (drop_ops id (s_ops st)) (s_next st) (ms_mem ms) HS (Forall_nil _) (so_mf _ _ _ _ _ _ HS)).
    - pose proof (so_ops _ _ _ _ _ _ HS) as H. unfold ops_hold in *. apply Forall_forall. intros o Ho.
      exact (proj1 (Forall_forall _ _) H o (drop_In id _ o Ho)).
    - pose proof (so_apart _ _ _ _ _ _ HS) as H. unfold ops_apart in *. apply Forall_forall. intros o Ho.
      exact (proj1 (Forall_forall _ _) H o (drop_In id _ o Ho)).
    - intros a Ha. destruct (so_cover _ _ _ _ _ _ HS a Ha) as [C|C]; [left; exact C| right].
      apply Exists_exists in C as (oi & Hoi & C1). apply Exists_exists. exists oi. split; [| exact C1].
      unfold insts in *. apply in_map_iff in Hoi as (o & <- & Ho). apply (in_map (fun o0 => (op_id o0, map (den E) (op_args o0)))). unfold drop_ops. apply filter_In. split; [exact Ho|].
      cbn [fst] in C1. pose proof (OPS_cov1_heap _ _ _ C1) as EH.
      apply negb_true_iff. apply Uint63.eqb_false_spec. rewrite EH. intros X. apply Q. symmetry. exact X.
    - intros; reflexivity.
    - intros a b Hb Hn. rewrite Hn in Hb. discriminate Hb. }
  cbn [app] in HS'. rewrite (ms_with_mem_id ms (so_svc _ _ _ _ _ _ HS)) in HS'.
  exact (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ _) HMP HS').
Qed.
End Sound.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import MemOps.TwinB OpDropC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan ValP StepB StepS PlanS CtrLib OpDropC.TwinB.OpDropC.
Open Scope Z_scope.
Unset Lia Cache.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis OPS_cov1_heap : forall id args z, op_cov1 OPS id args z -> id = HEAP_ID.

Lemma drop_In : forall id os o, In o (drop_ops id os) -> In o os.
Proof. intros id os o H. unfold drop_ops in H. apply filter_In in H. exact (proj1 H). Qed.

Lemma ms_with_mem_id : forall ms, ms_svc_pending ms = None -> ms_with_mem ms (ms_mem ms) = ms.
Proof. intros ms H. destruct ms. cbn in H. subst. reflexivity. Qed.

Theorem op_drop_sound : forall id pc, contract_sound segs OPS MP PB (op_drop_c id pc).
Proof.
  intros id pc st sts Hpc HAP K E ms mo HS HMP HPB HK. cbn [op_drop_c c_apply] in HAP. unfold op_drop_apply in HAP.
  destruct (find_op id (s_ops st)) as [args0|]; [|discriminate HAP].
  destruct (PrimInt63.eqb id HEAP_ID) eqn:Q; [discriminate HAP|]. injection HAP as <-.
  apply Uint63.eqb_false_spec in Q.
  assert (HS' : st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) ([] ++ s_facts st) (drop_ops id (s_ops st)) (s_priv st) (s_next st))
                      (ms_with_mem ms (ms_mem ms)) mo).
  { apply (st_ok_memops segs OPS E st ms mo mo [] (drop_ops id (s_ops st)) (s_next st) (ms_mem ms) HS (Forall_nil _) (so_mf _ _ _ _ _ _ HS)).
    - pose proof (so_ops _ _ _ _ _ _ HS) as H. unfold ops_hold in *. apply Forall_forall. intros o Ho.
      exact (proj1 (Forall_forall _ _) H o (drop_In id _ o Ho)).
    - pose proof (so_apart _ _ _ _ _ _ HS) as H. unfold ops_apart in *. apply Forall_forall. intros o Ho.
      exact (proj1 (Forall_forall _ _) H o (drop_In id _ o Ho)).
    - intros a Ha. destruct (so_cover _ _ _ _ _ _ HS a Ha) as [C|C]; [left; exact C| right].
      apply Exists_exists in C as (oi & Hoi & C1). apply Exists_exists. exists oi. split; [| exact C1].
      unfold insts in *. apply in_map_iff in Hoi as (o & <- & Ho). apply (in_map (fun o0 => (op_id o0, map (den E) (op_args o0)))). unfold drop_ops. apply filter_In. split; [exact Ho|].
      cbn [fst] in C1. pose proof (OPS_cov1_heap _ _ _ C1) as EH.
      apply negb_true_iff. apply Uint63.eqb_false_spec. rewrite EH. intros X. apply Q. symmetry. exact X.
    - intros; reflexivity.
    - intros a b Hb Hn. rewrite Hn in Hb. discriminate Hb. }
  cbn [app] in HS'. rewrite (ms_with_mem_id ms (so_svc _ _ _ _ _ _ HS)) in HS'.
  exact (HK _ (or_introl eq_refl) E ms mo (env_ext_refl _ _) HMP HS').
Qed.
End Sound.
End TwinB.
