(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition ms_u32 (c : Z) : Z := ((c mod 2 ^ 8) * 2 ^ 8 + c mod 2 ^ 8) * 2 ^ 16 + ((c mod 2 ^ 8) * 2 ^ 8 + c mod 2 ^ 8).
Definition ms_c32 (c : Z) : Z := szwrap 32 (ms_u32 c).
Definition ms_c64 (c : Z) : Z := ms_c32 c * 2 ^ 32 + ms_u32 c.

Fixpoint allb (n : nat) (f : Z -> bool) : bool :=
  match n with O => true | S n' => f (Z.of_nat n') && allb n' f end.

Definition cst_ok (lo hi : Z) (p : Z * nat) : Prop :=
  0 <= fst p /\ fst p + Z.of_nat (snd p) <= 2 ^ 64 /\ lo <= fst p /\ fst p + Z.of_nat (snd p) <= hi.

Ltac prove_In := cbn [In]; repeat (first [ left; reflexivity | right ]).

Lemma land_neg_pow2 : forall x n, 0 <= n -> Z.land x (- 2 ^ n) = x - x mod 2 ^ n.
Proof.
  intros x n Hn.
  replace (- 2 ^ n) with (Z.lnot (Z.ones n)) by (unfold Z.ones; rewrite Z.shiftl_1_l; unfold Z.lnot; lia).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2 ^ n) ltac:(lia)). lia.
Qed.

Definition iv (a : Z) (k : nat) : Z * Z := (a, a + Z.of_nat k).


