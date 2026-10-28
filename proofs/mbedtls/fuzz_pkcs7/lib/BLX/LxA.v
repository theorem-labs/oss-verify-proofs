(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxPost LxDex LxTac.

Definition lxA_img (AL0 : asan_layout) (IMG : asan_img_ok AL0) : LxImg asegs AL0 :=
  {| li_lo := 0x10000%Z; li_hi := 0x65f000%Z; li_got := 0x0f5e50%Z; li_gsb := 0x1099f8%Z;
     li_ok := match IMG with conj G (conj LO (conj HI GSB)) => conj (eq_sym LO) (conj (eq_sym HI) (conj (eq_sym G) (eq_sym GSB))) end |}.
