(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BShapeAlg BpinAlg BAgentLib BothAcct BothAcctShape BxSymExec3 BxSymExec3Sound BxSymRun3 BothPlanCore BothPlan BothPlanSound Bcfg.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Context {SC : StepCfg}.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

Definition OBL_mmap1 : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (APS.node_mmap1 A nx0 LIMIT).
Definition OBL_mmapin1 : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapin1 A LIMIT).
Definition OBL_mprotect1 : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mprotect A LIMIT).

Definition OBL_mmapgaps : Prop := nodeL_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapgaps A nx0 LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT SINV argH FS0.

Definition OBL_all : Prop := OBL_mmap1 /\ OBL_mmapin1 /\ OBL_mprotect1 /\ OBL_mmapgaps /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

End Iface.
