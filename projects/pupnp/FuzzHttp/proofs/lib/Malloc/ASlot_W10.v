(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import MallocKit_A3 ASlot_W1.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ag_frame (sc : Z) (j : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (Z_to_bv 64 (sc * 2)); CB 40 j; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section AG1.
Context {HCEIL : HasCeiling}.
Variables (sc lo : Z).
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
End AG1.

Section EPI.
Context {HCEIL : HasCeiling}.
Variables (lo : Z).
Hypothesis CLO : alloc_ceiling <= lo.
End EPI.