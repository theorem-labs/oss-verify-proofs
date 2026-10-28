(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import seqH_kit.
Open Scope Z_scope.

Lemma lit_lxor_pos : forall a b, 0 <= a -> 0 <= b -> (0 <? Z.lxor a b) = (0 <? Z.abs (a - b)).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent, Z.sub_diag. reflexivity.
  - assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; tauto).
    assert (Z.lxor a b <> 0) by (intro X; apply Z.lxor_eq in X; contradiction).
    transitivity true; [apply Z.ltb_lt; lia | symmetry; apply Z.ltb_lt; lia].
Qed.

Lemma lit_lxor_lt1 : forall a b, 0 <= a -> 0 <= b -> (Z.lxor a b <? 1) = (a =? b).
Proof.
  intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; tauto).
    assert (Z.lxor a b <> 0) by (intro X; apply Z.lxor_eq in X; contradiction). lia.
Qed.

Ltac b2z_decide :=
  repeat match goal with
  | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by lia
  | |- context [Z.shiftr ?x ?k] => rewrite (Z.shiftr_div_pow2 x k) by lia
  | |- context [0 <? Z.lxor ?a ?b] => rewrite (lit_lxor_pos a b) by lia
  | |- context [Z.lxor ?a ?b <? 1] => rewrite (lit_lxor_lt1 a b) by lia
  end; zb_fix.

Ltac uckb := b2z_decide; uck.
