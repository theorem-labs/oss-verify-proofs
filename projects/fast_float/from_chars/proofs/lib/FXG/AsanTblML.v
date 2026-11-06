(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxImg FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require Import AsanImgScan AsanImg AsanTblM AsanTblMd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma TBLM_eq : TBLM = TBLMd.
Proof. reflexivity. Qed.       (* [comment removed for export] *)
Lemma TBLM_ok : tbl_ok ASEGS TBLM. Proof. rewrite TBLM_eq. exact TBLMd_ok. Qed.
Lemma TBLM_ecall : ecall_ok ASEGS TBLM. Proof. rewrite TBLM_eq. exact TBLMd_ecall. Qed.
