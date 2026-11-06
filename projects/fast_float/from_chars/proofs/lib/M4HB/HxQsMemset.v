(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQSites AsanQcsNode AsanQSSites.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSSites.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QS_MEMSET : qsite := QS 0x606a4 (rr 13) (rr 15) (rr 10) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x607e4 - 0x606d0)) false.
Lemma QS_MEMSET_ok : qsite_ok ASEGSQ QS_MEMSET. Proof. qsite_tac. Qed.
Definition QSS_MEMSET : qssite := QSS QS_MEMSET 0x607e4 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x606d4 - 0x60814)).
Lemma QSS_MEMSET_ok : qssite_ok ASEGSQ QSS_MEMSET. Proof. qssite_tac QS_MEMSET_ok. Qed.
(* [comment removed for export] *)
