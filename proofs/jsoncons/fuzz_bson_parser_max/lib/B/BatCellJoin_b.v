(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim SeqExec StoreOk ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatUnwind_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).

Lemma art_cell_join : forall (M : word -> option byte) a (n1 n2 : nat) lo hi, 0 <= a -> a + Z.of_nat (n1 + n2) < 2 ^ 64 -> (n1 + n2 <= 8)%nat ->
  0 <= lo < 2 ^ (8 * Z.of_nat n1) -> 0 <= hi < 2 ^ (8 * Z.of_nat n2) ->
  cellA M a n1 lo -> cellA M (a + Z.of_nat n1) n2 hi -> cellA M a (n1 + n2) (lo + hi * 2 ^ (8 * Z.of_nat n1)).
Proof.
  intros M a n1 n2 lo hi Ha Ha' Hn Hlo Hhi C1 C2. unfold cell in *.
  assert (P1 : 0 < 2 ^ (8 * Z.of_nat n1)) by (apply Z.pow_pos_nonneg; lia).
  assert (B1 : 2 ^ (8 * Z.of_nat n1) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  assert (B2 : 2 ^ (8 * Z.of_nat n2) * 2 ^ (8 * Z.of_nat n1) <= 2 ^ 64).
  { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
  assert (Hv : 0 <= lo + hi * 2 ^ (8 * Z.of_nat n1) < 2 ^ 64) by nia.
  erewrite rdn_app; [|exact C1|].
  2: { replace (Z_to_bv 64 a + nat_to_word n1)%bv with (Z_to_bv 64 (a + Z.of_nat n1) : word); [exact C2|].
       apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
       rewrite (Z.mod_small (Z.of_nat n1)) by lia. rewrite (Z.mod_small a) by lia. rewrite Z.mod_small by lia. reflexivity. }
  f_equal. unfold word_to_le_bytes. rewrite !art_u_lit by lia. rewrite (Z_to_le_bytes_add n1 n2). f_equal.
  - rewrite <- (Z_to_le_bytes_wrap n1 (N.of_nat (8 * n1)) (lo + hi * 2 ^ (8 * Z.of_nat n1))) by lia.
    rewrite <- (Z_to_le_bytes_wrap n1 (N.of_nat (8 * n1)) lo) by lia. f_equal.
    unfold bv_wrap, bv_modulus. replace (Z.of_N (N.of_nat (8 * n1))) with (8 * Z.of_nat n1) by lia. rewrite Z.mod_add by lia. reflexivity.
  - f_equal. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma art_hdr_word : forall (M : word -> option byte) h st b1, 0 <= h -> h + 4 < 2 ^ 64 -> 0 <= st < 256 -> 0 <= b1 < 256 ->
  cellA M h 1 st -> cellA M (h + 1) 1 b1 -> cellA M (h + 2) 2 0 -> cellA M h 4 (st + 256 * b1).
Proof.
  intros M h st b1 Hh Hh' Hst Hb1 C0 C1 C2.
  assert (C12 : cellA M (h + 1) 3 (b1 + 0 * 2 ^ (8 * Z.of_nat 1))).
  { apply (art_cell_join M (h + 1) 1 2 b1 0); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C1|]. replace (h + 1 + Z.of_nat 1) with (h + 2) by lia. exact C2. }
  replace (b1 + 0 * 2 ^ (8 * Z.of_nat 1)) with b1 in C12 by lia.
  replace (st + 256 * b1) with (st + b1 * 2 ^ (8 * Z.of_nat 1)) by (cbn; lia).
  apply (art_cell_join M h 1 3 st b1); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C0|]. replace (h + Z.of_nat 1) with (h + 1) by lia. exact C12.
Qed.
