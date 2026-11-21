(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Export InffastFrame InffastFastOk InffastClPinv InffastGfastOb InffastFfOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require InflA_LenF InflA_Cl1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma FFOK : InflA_LenF.ffok_stmt.
Proof. exact InffastFfOk.ffok. Qed.
Lemma FASTOK : InflA_LenF.fastok_stmt.
Proof. exact InffastFastOk.fastok. Qed.
Lemma GFOB : InflA_LenF.gfast_ob_stmt.
Proof. exact InffastGfastOb.gfast_ob. Qed.
Lemma FFRAME : InflA_LenF.fframe_stmt.
Proof. exact InffastFrame.fframe. Qed.
Lemma CLPINV : InflA_Cl1.InflA_Codelens5.cl_pinv_stmt.
Proof. exact InffastClPinv.cl_pinv. Qed.
