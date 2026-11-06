(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound Scfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Context {SC : StepCfg}.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OBL_mmap1 : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (APS.node_mmap1 A nx0 LIMIT).
Definition OBL_mmapin1 : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapin1 A LIMIT).
Definition OBL_mprotect1 : Prop := node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mprotect A LIMIT).
(* [comment removed for export] *)
Definition OBL_mmapgaps : Prop := nodeL_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapgaps A nx0 LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap1 /\ OBL_mmapin1 /\ OBL_mprotect1 /\ OBL_mmapgaps /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

End Iface.
