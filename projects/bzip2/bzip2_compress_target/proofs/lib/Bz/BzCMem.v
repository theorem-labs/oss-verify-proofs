(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition rd8 (a : zarr) (o : Z) : Z := zget a o.
Definition wr8 (a : zarr) (o v : Z) : zarr := zset a o (v mod 256).

(* [comment removed for export] *)
Definition rd16 (a : zarr) (o : Z) : Z := zget a o + 256 * zget a (o + 1).
Definition wr16 (a : zarr) (o v : Z) : zarr :=
  zset (zset a o (v mod 256)) (o + 1) ((v / 256) mod 256).

(* [comment removed for export] *)
Definition rd32 (a : zarr) (i : Z) : Z :=
  zget a (4 * i) + 256 * zget a (4 * i + 1) + 65536 * zget a (4 * i + 2) + 16777216 * zget a (4 * i + 3).
Definition wr32 (a : zarr) (i v : Z) : zarr :=
  zset (zset (zset (zset a (4 * i) (v mod 256)) (4 * i + 1) ((v / 256) mod 256))
             (4 * i + 2) ((v / 65536) mod 256)) (4 * i + 3) ((v / 16777216) mod 256).

Lemma bytes4_recompose : forall v, 0 <= v < 4294967296 ->
  v mod 256 + 256 * ((v / 256) mod 256) + 65536 * ((v / 65536) mod 256) + 16777216 * ((v / 16777216) mod 256) = v.
Proof.
  intros v Hv.
  assert (E1 : v / 65536 = (v / 256) / 256) by (rewrite Z.div_div by lia; reflexivity).
  assert (E2 : v / 16777216 = (v / 65536) / 256) by (rewrite Z.div_div by lia; reflexivity).
  assert (R3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (v / 16777216) 256) by exact R3.
  pose proof (Z.div_mod v 256 ltac:(lia)) as D0.
  pose proof (Z.div_mod (v / 256) 256 ltac:(lia)) as D1.
  pose proof (Z.div_mod (v / 65536) 256 ltac:(lia)) as D2.
  rewrite <- E1 in D1. rewrite <- E2 in D2. lia.
Qed.

Lemma rd32_wr32_same : forall a i v, 0 <= v < 4294967296 -> rd32 (wr32 a i v) i = v.
Proof.
  intros a i v Hv. unfold rd32, wr32.
  rewrite !zget_zset. rewrite !Z.eqb_refl.
  repeat match goal with |- context [?x =? ?y] =>
    replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) end.
  apply bytes4_recompose. exact Hv.
Qed.

Lemma rd32_wr32_other : forall a i v j, j <> i -> rd32 (wr32 a i v) j = rd32 a j.
Proof.
  intros a i v j H. unfold rd32, wr32.
  rewrite !zget_zset.
  repeat match goal with |- context [?x =? ?y] =>
    replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) end.
  reflexivity.
Qed.

(* [comment removed for export] *)

Lemma rd16_wr16_same : forall a o v, 0 <= v < 65536 -> rd16 (wr16 a o v) o = v.
Proof.
  intros a o v Hv. unfold rd16, wr16. rewrite !zget_zset. rewrite !Z.eqb_refl.
  replace (o =? o + 1) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small (v / 256) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod v 256 ltac:(lia)). lia.
Qed.

Lemma rd16_wr16_other : forall a o v o', (o' + 1 < o \/ o + 1 < o') -> rd16 (wr16 a o v) o' = rd16 a o'.
Proof.
  intros a o v o' H. unfold rd16, wr16. rewrite !zget_zset.
  repeat match goal with |- context [?x =? ?y] =>
    replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) end.
  reflexivity.
Qed.
