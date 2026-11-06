(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase StepSound PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan ValP StepB StepS PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Definition ms_with_mem (ms : machine_state) (m' : word -> option byte) : machine_state := ms_upd ms (core_of ms) m'.

Lemma st_ok_memops : forall E T ms model model' fs' os' n' (m' : word -> option byte),
  st_ok segs OPS E T ms model ->
  Forall (fact_holds E) fs' ->
  op_minv OPS model' ->
  ops_hold OPS E os' m' model' ->
  ops_apart segs OPS E os' (s_regs T) (s_priv T) ->
  (forall a, fx_acc segs E (s_regs T) a -> op_cov OPS (insts E os') a) ->
  (forall a, 0 <= a < two64 -> (find_segment segs a 1 = None \/ ~ in_priv (s_priv T) a) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a b, m' a = Some b -> ms_mem ms a = None -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true) ->
  st_ok segs OPS E (SS (s_pc T) (s_rf T) (s_ff T) (s_resv T) (s_regs T) (fs' ++ s_facts T) os' (s_priv T) n')
        (ms_with_mem ms m') model'.
Proof.
  intros E T ms model model' fs' os' n' m' HS Hfs Hmf Hops Hapart Hcov Hmem Hnew.
  destruct HS as [Hpc' Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops' Hapart' Hmf0 Hcov0 Hminv].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv ms_with_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending
              ms_resv ms_fcsr ms_mem ms_rom] in *; try assumption.
  all: try reflexivity.
  - intros k r Hk. apply (MemP.region_ok_frame segs (s_priv T) E (ms_mem ms) m' k r Hz (Hreg k r Hk)).
    intros a Ha Hbased Habs. apply Hmem; [exact Ha|].
    destruct (PrimInt63.eqb k 0%uint63) eqn:Hk0.
    + right. exact (proj2 (Habs eq_refl)).
    + left. exact (proj2 (proj2 (ro_valid _ _ _ _ _ _ (Hreg k r Hk) Hk0 a (Hbased eq_refl)))).
  - unfold facts_hold. apply Forall_app. split; assumption.
  - intros a b Hb seg Hseg. destruct (ms_mem ms a) as [b0|] eqn:Hm.
    + exact (Hminv a b0 Hm seg Hseg).
    + exact (Hnew a b Hb Hm seg Hseg).
Qed.
End WithSegs.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan ValP StepB StepS PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Definition ms_with_mem (ms : machine_state) (m' : word -> option byte) : machine_state := ms_upd ms (core_of ms) m'.

Lemma st_ok_memops : forall E T ms model model' fs' os' n' (m' : word -> option byte),
  st_ok segs OPS E T ms model ->
  Forall (fact_holds E) fs' ->
  op_minv OPS model' ->
  ops_hold OPS E os' m' model' ->
  ops_apart segs OPS E os' (s_regs T) (s_priv T) ->
  (forall a, fx_acc segs E (s_regs T) a -> op_cov OPS (insts E os') a) ->
  (forall a, 0 <= a < two64 -> (find_segment segs a 1 = None \/ ~ in_priv (s_priv T) a) ->
     m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a b, m' a = Some b -> ms_mem ms a = None -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true) ->
  st_ok segs OPS E (SS (s_pc T) (s_rf T) (s_ff T) (s_resv T) (s_regs T) (fs' ++ s_facts T) os' (s_priv T) n')
        (ms_with_mem ms m') model'.
Proof.
  intros E T ms model model' fs' os' n' m' HS Hfs Hmf Hops Hapart Hcov Hmem Hnew.
  destruct HS as [Hpc' Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops' Hapart' Hmf0 Hcov0 Hminv].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv ms_with_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending
              ms_resv ms_fcsr ms_mem ms_rom] in *; try assumption.
  all: try reflexivity.
  - intros k r Hk. apply (MemP.region_ok_frame segs (s_priv T) E (ms_mem ms) m' k r Hz (Hreg k r Hk)).
    intros a Ha Hbased Habs. apply Hmem; [exact Ha|].
    destruct (PrimInt63.eqb k 0%uint63) eqn:Hk0.
    + right. exact (proj2 (Habs eq_refl)).
    + left. exact (proj2 (proj2 (ro_valid _ _ _ _ _ _ (Hreg k r Hk) Hk0 a (Hbased eq_refl)))).
  - unfold facts_hold. apply Forall_app. split; assumption.
  - intros a b Hb seg Hseg. destruct (ms_mem ms a) as [b0|] eqn:Hm.
    + exact (Hminv a b0 Hm seg Hseg).
    + exact (Hnew a b Hb Hm seg Hseg).
Qed.
End WithSegs.
End TwinB.
