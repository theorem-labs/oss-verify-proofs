(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lxor3_decomp : forall X, 0 <= X -> Z.lxor X 3 = 4 * (X / 4) + (3 - X mod 4).
Proof.
  intros X HX.
  assert (E : X = 4 * (X / 4) + X mod 4) by (apply Z.div_mod; lia).
  set (q := X / 4) in *. set (r := X mod 4) in *.
  assert (Hr : 0 <= r < 4) by (unfold r; apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (L1 : Z.land (4 * q) r = 0).
  { replace r with (Z.land (Z.ones 2) r) by (rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite Z.land_assoc. rewrite (Z.land_ones (4 * q) 2) by lia.
    assert (M : (4 * q) mod 2 ^ 2 = 0) by (change (2 ^ 2) with 4; rewrite Z.mul_comm; apply Z.mod_mul; lia). rewrite M. apply Z.land_0_l. }
  assert (L2 : Z.land (4 * q) (Z.lxor r 3) = 0).
  { assert (R3 : 0 <= Z.lxor r 3 < 4) by (destruct (Z.eq_dec r 0) as [->|]; [cbn; lia|];
                                           destruct (Z.eq_dec r 1) as [->|]; [cbn; lia|];
                                           destruct (Z.eq_dec r 2) as [->|]; [cbn; lia|];
                                           assert (r = 3) as -> by lia; cbn; lia).
    replace (Z.lxor r 3) with (Z.land (Z.ones 2) (Z.lxor r 3)) by (rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
    rewrite Z.land_assoc. rewrite (Z.land_ones (4 * q) 2) by lia.
    assert (M : (4 * q) mod 2 ^ 2 = 0) by (change (2 ^ 2) with 4; rewrite Z.mul_comm; apply Z.mod_mul; lia). rewrite M. apply Z.land_0_l. }
  rewrite E. rewrite (Z.add_nocarry_lxor (4 * q) r L1). rewrite Z.lxor_assoc.
  rewrite <- (Z.add_nocarry_lxor (4 * q) (Z.lxor r 3) L2). f_equal.
  destruct (Z.eq_dec r 0) as [->|]; [reflexivity|]. destruct (Z.eq_dec r 1) as [->|]; [reflexivity|].
  destruct (Z.eq_dec r 2) as [->|]; [reflexivity|]. assert (r = 3) as -> by lia. reflexivity.
Qed.
