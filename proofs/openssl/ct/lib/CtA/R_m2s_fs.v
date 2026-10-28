(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_m2s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Lemma m2s_3d1d8_spec : m2s_stmt 0x1a8648.
Proof.
  unfold m2s_stmt. intros until p. intros -> HP [GOT [SH HM]] MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  unfold SHB, kHighMemEnd in *. unfold addr_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HP.
  do 8 zstep.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
  - (* [comment removed for export] *)
    assert (HH : (17594333495295 < p <= 140737488355327)%Z).
    { assert (E : (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879 = 2147450879)%Z)
        by reflexivity.
      rewrite E in K. destruct HP as [HP|HP]; [lia|exact HP]. }
    clear HP K.
    do 8 zstep.
    assert (C1 : negb (bv_ltu (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) = true).
    { unfold bv_ltu. rewrite (unsigned_lit_wrap (-1)), (unsigned_lit p) by lia.
      change ((-1) mod 2^64)%Z with 18446744073709551615%Z. apply negb_true_iff, Z.ltb_ge. lia. }
    rewrite C1; cbv iota.
    do 6 zstep.
    assert (C2 : bv_ltu (Z_to_bv 64 140737488355327) (Z_to_bv 64 p) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. }
    rewrite C2; cbv iota.
    do 1 zstep.
    assert (C3 : negb (bv_ltu (Z_to_bv 64 17594333495295) (Z_to_bv 64 p)) = false).
    { unfold bv_ltu. rewrite !unsigned_lit by lia. apply negb_false_iff, Z.ltb_lt. lia. }
    rewrite C3; cbv iota.
    do 3 zstep.
    replace (Z_to_bv 64 (2147450880 + p ≫ 3)) with (Z_to_bv 64 (shad p))
      by (f_equal; unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z; lia).
    finish.
Qed.
