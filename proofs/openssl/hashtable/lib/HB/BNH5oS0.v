(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch CxTmpl CxTmpl2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam HBParity BVG5T3So.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition NH5o_N0 : nat := 1140.
Definition NH5o_base_ (_ : unit) : acs := vg5t3so.
Abbreviation NH5o_base := (NH5o_base_ tt).
Definition NH5o_cs_ (_ : unit) : acs := Eval vm_compute in add_kn (bump NH5o_base (NH5o_N0 - nxt NH5o_base)) [].
Abbreviation NH5o_cs := (NH5o_cs_ tt).
Eval vm_compute in ("S0"%string, nxt NH5o_cs, length (kn NH5o_cs), csmaxv NH5o_cs).
