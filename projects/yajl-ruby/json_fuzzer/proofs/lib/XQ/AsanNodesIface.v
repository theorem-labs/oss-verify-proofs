(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable SC : SpuriousCfg.     (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmapG : Prop := mm1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 (node_mmapG A nx0 LIMIT).
Definition OBL_mmapin : Prop := mm1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT).
Definition OBL_mprotect : Prop := mm1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 (node_mprotect A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS SC A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS SC A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS SC A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmapG /\ OBL_mmapin /\ OBL_mprotect /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmapG_unfold :
  OBL_mmapG <->
  forall cs csb E R FULL model TB,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmapG A nx0 LIMIT cs = Some csb ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        realizes_cfg SC SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    realizes_cfg SC SEGS (cfg_of SEGS R (pc cs) FULL model) TB.
Proof. unfold OBL_mmapG, mm1_stmt. tauto. Qed.
End Iface.
