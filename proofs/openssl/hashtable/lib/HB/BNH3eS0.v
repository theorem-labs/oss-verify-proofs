(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch CxTmpl CxTmpl2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam HBParity BVG3T3Se.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition NH3e_N0 : nat := 1140.
Definition NH3e_base_ (_ : unit) : acs := vg3t3se.
Abbreviation NH3e_base := (NH3e_base_ tt).
Definition NH3e_cs_ (_ : unit) : acs := Eval vm_compute in add_kn (bump NH3e_base (NH3e_N0 - nxt NH3e_base)) [].
Abbreviation NH3e_cs := (NH3e_cs_ tt).
Eval vm_compute in ("S0"%string, nxt NH3e_cs, length (kn NH3e_cs), csmaxv NH3e_cs).
