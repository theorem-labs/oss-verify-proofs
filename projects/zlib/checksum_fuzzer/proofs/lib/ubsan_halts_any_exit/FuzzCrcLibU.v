(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import FuzzZ FuzzCk FuzzCrcLib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition mw1u (y : Z) : Z := Z.lxor (sx32 (ctab (Z.land y 255))) (Z.shiftr (y mod two32) 8).
Definition mw3u (y : Z) : Z := mw1u (mw1u (mw1u y)).
Definition mw4u (z x w : Z) : Z :=
  Z.lxor (Z.lxor (Z.lxor (Z.shiftr (z mod two32) 8) x) (sx32 w)) (sx32 (ctab (Z.land z 255))).
Definition mwfu (z : Z) : Z := Z.lxor (ctab (Z.land z 255)) (Z.shiftr (z mod two32) 8).

Definition mlastu (x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 : Z) : Z :=
  let y0 := Z.lxor (sx32 w0) x0 in
  let y1 := mw4u (mw3u y0) x1 w1 in
  let y2 := mw4u (mw3u y1) x2 w2 in
  let y3 := mw4u (mw3u y2) x3 w3 in
  let y4 := mw4u (mw3u y3) x4 w4 in
  mwfu (mw3u y4).

Lemma mw1u_eq : forall y, mw1u y = mw1 y.
Proof. intros. unfold mw1u, mw1. apply Z.lxor_comm. Qed.

Lemma mw3u_eq : forall y, mw3u y = mw3 y.
Proof. intros. unfold mw3u, mw3. rewrite !mw1u_eq. reflexivity. Qed.

Lemma mw4u_eq : forall z x w, mw4u z x w = mw4 z (Z.lxor x (sx32 w)).
Proof.
  intros. unfold mw4u, mw4.
  rewrite (Z.lxor_comm _ (sx32 (ctab _))). f_equal.
  rewrite Z.lxor_assoc. apply Z.lxor_comm.
Qed.

Lemma mwfu_eq : forall z, mwfu z = mwf z.
Proof. intros. unfold mwfu, mwf. apply Z.lxor_comm. Qed.

Lemma mlastu_eq : forall x0 x1 x2 x3 x4 w0 w1 w2 w3 w4,
  mlastu x0 x1 x2 x3 x4 w0 w1 w2 w3 w4 = mlast x0 x1 x2 x3 x4 w0 w1 w2 w3 w4.
Proof.
  intros. unfold mlastu, mlast. cbv zeta. rewrite !mw4u_eq, !mw3u_eq, mwfu_eq. reflexivity.
Qed.

Definition mlastxu (BA : Z -> Z) (x : lanes) (a : Z) : Z :=
  let '(x0, x1, x2, x3, x4) := x in
  mlastu x0 x1 x2 x3 x4 (Wd BA a) (Wd BA (a + 4)) (Wd BA (a + 8)) (Wd BA (a + 12)) (Wd BA (a + 16)).

Lemma mlastxu_eq : forall BA x a, mlastxu BA x a = mlastx BA x a.
Proof. intros BA [[[[x0 x1] x2] x3] x4] a. unfold mlastxu, mlastx. apply mlastu_eq. Qed.
