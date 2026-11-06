(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxImg.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanTblM AsanTblAll.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanTblH2 AsanBodyE.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.HarnTblX.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation ASEGSL := AsanUbsan.M.loaded_segments.
Definition IMGHX_d : tree Z := mk_img_runsH (HX_WR ++ S0M_WR) TEmpty.
Definition TBLHXL : tree xi := AsanTblAll.TBLA.      (* [comment removed for export] *)
Definition IMGHXL : tree Z := Eval vm_compute in IMGHX_d.
Lemma IMGHXL_eq : IMGHXL = IMGHX_d. Proof. vm_cast_no_check (eq_refl IMGHXL). Qed.
(* [comment removed for export] *)
