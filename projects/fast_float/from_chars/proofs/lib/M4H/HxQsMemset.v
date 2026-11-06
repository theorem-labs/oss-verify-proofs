(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQSites AsanQcsNode AsanQSSites.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSSites.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QS_MEMSET : qsite := QS 0x606b0 (rr 13) (rr 15) (rr 10) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x607f0 - 0x606dc)) false.
Lemma QS_MEMSET_ok : qsite_ok ASEGSQ QS_MEMSET. Proof. qsite_tac. Qed.
Definition QSS_MEMSET : qssite := QSS QS_MEMSET 0x607f0 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x606e0 - 0x60820)).
Lemma QSS_MEMSET_ok : qssite_ok ASEGSQ QSS_MEMSET. Proof. qssite_tac QS_MEMSET_ok. Qed.
