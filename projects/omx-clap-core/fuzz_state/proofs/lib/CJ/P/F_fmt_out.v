(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import Prelim SoftFloat FmtFp StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Exit_tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.Exit_tac.STRW_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.
Lemma sext32_small : forall z, (-2147483648 <= z < 2147483648)%Z -> bv_swrap 32 z = z.
Proof.
  intros. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32 `div` 2)%Z with 2147483648%Z. lia.
Qed.