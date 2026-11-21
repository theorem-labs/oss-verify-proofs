(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateFast InffastModel InffastCtx InffastSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma cpn_shape : forall x n f,
  f_in (cpn x n f) = f_in f /\ f_hold (cpn x n f) = f_hold f /\ f_bits (cpn x n f) = f_bits f
  /\ f_len (cpn x n f) = f_len f /\ f_dist (cpn x n f) = f_dist f /\ f_op (cpn x n f) = f_op f
  /\ f_out (cpn x n f) = f_out f + Z.of_nat n /\ f_from (cpn x n f) = fr_add (f_from f) n
  /\ f_ob (cpn x n f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) n.
Proof.
  intros x n f. destruct (cpn_keep x n f) as (A & B & C & D & E & F). destruct (cpn_cblit x n f) as (G & H & I).
  repeat split; assumption.
Qed.

Lemma copy_op_shape : forall x f, 1 <= f_op f < 2 ^ 32 ->
  f_in (copy_op x f) = f_in f /\ f_hold (copy_op x f) = f_hold f /\ f_bits (copy_op x f) = f_bits f
  /\ f_len (copy_op x f) = f_len f /\ f_dist (copy_op x f) = f_dist f /\ f_op (copy_op x f) = 0
  /\ f_out (copy_op x f) = f_out f + f_op f /\ f_from (copy_op x f) = fr_add (f_from f) (Z.to_nat (f_op f))
  /\ f_ob (copy_op x f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) (Z.to_nat (f_op f)).
Proof.
  intros x f Hop. rewrite copy_op_cpn by exact Hop.
  destruct (cpn_shape x (Z.to_nat (f_op f)) f) as (A & B & C & D & E & F & G & H & I).
  cbn [f_in f_hold f_bits f_len f_dist f_op f_out f_from f_ob fset_op]. rewrite A, B, C, D, E, G, H, I.
  repeat split; try reflexivity. lia.
Qed.

Lemma copy_op_len : forall x f, 1 <= f_op f < 2 ^ 32 -> f_len (copy_op x f) = f_len f.
Proof. intros x f H. destruct (copy_op_shape x f H) as (_ & _ & _ & D & _). exact D. Qed.

Lemma w3_shape : forall x f, 0 <= f_len f < 2 ^ 32 ->
  let g := copy_tail x (copy_while3 x f) in
  f_in g = f_in f /\ f_hold g = f_hold f /\ f_bits g = f_bits f
  /\ f_out g = f_out f + f_len f
  /\ f_ob g = cblit (x_window x) (f_from f) (f_ob f) (f_out f) (Z.to_nat (f_len f)).
Proof.
  intros x f Hl. cbv zeta. rewrite copy_while3_cpn by exact Hl.
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as Hm. pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as Hdm.
  rewrite copy_tail_cpn by (cbn [f_len fset_len]; lia). cbn [f_len fset_len].
  rewrite cpn_fset_len. cbn [f_in f_hold f_bits f_out f_ob fset_len].
  rewrite <- cpn_add.
  destruct (cpn_shape x (Z.to_nat (3 * (f_len f / 3)) + Z.to_nat (f_len f mod 3)) f) as (A & B & C & D & E & F & G & H & I).
  rewrite A, B, C, G, I.
  replace (Z.to_nat (3 * (f_len f / 3)) + Z.to_nat (f_len f mod 3))%nat with (Z.to_nat (f_len f)) by lia.
  repeat split; try reflexivity. lia.
Qed.

Lemma do3_shape : forall x f, 3 <= f_len f < 2 ^ 32 ->
  let g := copy_tail x (copy_do3 x f) in
  f_in g = f_in f /\ f_hold g = f_hold f /\ f_bits g = f_bits f
  /\ f_out g = f_out f + f_len f
  /\ f_ob g = cblit (x_window x) (f_from f) (f_ob f) (f_out f) (Z.to_nat (f_len f)).
Proof.
  intros x f Hl. cbv zeta. rewrite copy_do3_cpn by exact Hl.
  pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as Hm. pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as Hdm.
  rewrite copy_tail_cpn by (cbn [f_len fset_len]; lia). cbn [f_len fset_len].
  rewrite cpn_fset_len. cbn [f_in f_hold f_bits f_out f_ob fset_len].
  rewrite <- cpn_add.
  destruct (cpn_shape x (Z.to_nat (3 * (f_len f / 3)) + Z.to_nat (f_len f mod 3)) f) as (A & B & C & D & E & F & G & H & I).
  rewrite A, B, C, G, I.
  replace (Z.to_nat (3 * (f_len f / 3)) + Z.to_nat (f_len f mod 3))%nat with (Z.to_nat (f_len f)) by lia.
  repeat split; try reflexivity. lia.
Qed.

Lemma cblit_len2 : forall win fr ob i n, arr_len (cblit win fr ob i n) = arr_len ob.
Proof. intros. apply cblit_len. Qed.
