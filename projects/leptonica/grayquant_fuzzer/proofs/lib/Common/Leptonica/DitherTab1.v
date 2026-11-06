(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib DitherLib DitherTab.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.
(* [comment removed for export] *)
Definition tab_rdn (n : nat) (sx : bool) (P : Z -> Prop) (cells : list (Z * Z)) (m : word -> option byte) (tab : Z) : Prop :=
  forall (m' : word -> option byte) (k : Z), mframe cells m m' -> 0 <= k <= 255 ->
    exists bs, rdn segs m' (Z_to_bv 64 (tab + 4 * k)) n = Some bs /\ P (rdv sx n bs).
End WithSegs.
