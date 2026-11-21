(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkXt CkMultmodp CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkA Require Import CrcAGlue CrcAMirror.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition dY1B (y : Z) : Z := Z.lxor (sxz (ctab (Z.land y 255))) ((y mod 4294967296) ≫ 8).
Definition dYnB (y x w : Z) : Z :=
  Z.lxor (Z.lxor (Z.lxor ((y mod 4294967296) ≫ 8) x) (sxz w)) (sxz (ctab (Z.land y 255))).
Definition dYfB (y : Z) : Z := Z.lxor (ctab (Z.land y 255)) ((y mod 4294967296) ≫ 8).

Lemma dY1B_unfold : forall y, dY1B y = Z.lxor (sxz (ctab (Z.land y 255))) ((y mod 4294967296) ≫ 8). Proof. reflexivity. Qed.
Lemma dYnB_unfold : forall y x w, dYnB y x w =
  Z.lxor (Z.lxor (Z.lxor ((y mod 4294967296) ≫ 8) x) (sxz w)) (sxz (ctab (Z.land y 255))).
Proof. reflexivity. Qed.
Lemma dYfB_unfold : forall y, dYfB y = Z.lxor (ctab (Z.land y 255)) ((y mod 4294967296) ≫ 8). Proof. reflexivity. Qed.

Lemma dY1B_eq : forall y, dY1B y = dY1 y.
Proof. intros y. unfold dY1B, dY1. apply Z.lxor_comm. Qed.
Lemma dYnB_eq : forall y x w, dYnB y x w = dYn y x w.
Proof. intros y x w. unfold dYnB, dYn. lxor_ac. Qed.
Lemma dYfB_eq : forall y, dYfB y = dYf y.
Proof. intros y. unfold dYfB, dYf. apply Z.lxor_comm. Qed.

Lemma dY1B_range : forall y, 0 <= dY1B y < 2^64.
Proof. intros y. rewrite dY1B_eq. apply dY1_range. Qed.
Lemma dY1B_mod32 : forall y, dY1B y mod 2^32 = crc_word1 (y mod 2^32).
Proof. intros y. rewrite dY1B_eq. apply dY1_mod32. Qed.
Lemma dYnB_range : forall y x w, 0 <= x < 2^64 -> 0 <= dYnB y x w < 2^64.
Proof. intros y x w H. rewrite dYnB_eq. apply dYn_range. exact H. Qed.
Lemma dYnB_mod32 : forall y x w, 0 <= w < 2^32 ->
  dYnB y x w mod 2^32 = Z.lxor (Z.lxor (x mod 2^32) w) (crc_word1 (y mod 2^32)).
Proof. intros y x w H. rewrite dYnB_eq. apply dYn_mod32. exact H. Qed.
Lemma dYfB_eq1 : forall y, dYfB y = crc_word1 (y mod 2^32).
Proof. intros y. rewrite dYfB_eq. apply dYf_eq. Qed.
