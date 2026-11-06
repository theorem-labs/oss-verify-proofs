(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch CxTmpl CxTmpl2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import HAPlanImage HAAtable HAArg HACheckG HAChain HAHop HABatch HAFam HAParity VG9T3So.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Definition NH9o_N0 : nat := 1140.
Definition NH9o_base_ (_ : unit) : acs := vg9t3so.
Abbreviation NH9o_base := (NH9o_base_ tt).
Definition NH9o_cs_ (_ : unit) : acs := Eval vm_compute in add_kn (bump NH9o_base (NH9o_N0 - nxt NH9o_base)) [].
Abbreviation NH9o_cs := (NH9o_cs_ tt).
Eval vm_compute in ("S0"%string, nxt NH9o_cs, length (kn NH9o_cs), csmaxv NH9o_cs).
