(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool Btauto.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.cks Require Import CkTables CkModel CkXt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).




Ltac xor_ac :=
  cbn [xorb andb orb negb];
  rewrite ?Z.lxor_0_l, ?Z.lxor_0_r, ?Z.lxor_nilpotent;
  first [ reflexivity
        | apply Z.bits_inj'; intros ?n ?Hn; rewrite ?Z.lxor_spec, ?Z.bits_0;
          repeat match goal with |- context [Z.testbit ?x ?m] => generalize (Z.testbit x m); intro end;
          btauto ].


Lemma pow2_split : forall a n, 0 <= n -> 0 <= a < 2 ^ (n + 1) -> 2 ^ n <= a ->
  a = Z.lxor (a - 2 ^ n) (2 ^ n).
Proof.
  intros a n Hn Ha Hge.
  rewrite <- Z.add_nocarry_lxor.
  - lia.
  - replace (2 ^ n) with (Z.shiftl 1 n) at 2 by (rewrite Z.shiftl_1_l; reflexivity).
    apply land_shiftl_disj; [| lia | lia]. rewrite Z.pow_add_r in Ha by lia. change (2 ^ 1) with 2 in Ha. lia.
Qed.







Definition xp (e : nat) : Z := xtn e X0.


















Fixpoint msum (i : nat) (a b : Z) : Z :=
  Z.lxor (if Z.testbit a (Z.of_nat i) then b else 0)
         (match i with O => 0 | S i' => msum i' a (xt b) end).







































