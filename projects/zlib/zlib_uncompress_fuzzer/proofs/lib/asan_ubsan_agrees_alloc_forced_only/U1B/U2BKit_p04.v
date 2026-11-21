(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma lxor_pos : forall a b, 0 <= a -> 0 <= b -> a <> b -> 1 <= Z.lxor a b.
Proof.
  intros a b Ha Hb Hab.
  assert (L0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  assert (L1 : Z.lxor a b <> 0) by (intros E; apply Z.lxor_eq in E; lia).
  lia.
Qed.
Ltac ub_b2z :=
  repeat match goal with
  | |- context [Z.b2z (Z.lxor ?a ?b <? 1)] =>
      replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; apply lxor_pos; lia); cbn [Z.b2z]
  | |- context [Z.b2z (?x <? ?y)] =>
      first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
            | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]; cbn [Z.b2z]
  end;
  change (Z.lxor 1 0) with 1; change (Z.lxor 0 1) with 1; change (Z.lxor 0 0) with 0; change (Z.lxor 1 1) with 0.

Ltac ub_dec :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ rewrite ?Shadow.land7_mod; pc_dec | ub_b2z; first [pc_lit | pc_dec] ]
  end.
Ltac zrung STOPS := repeat (first [ at_free_pc STOPS; zs | pc_dec | ub_dec ]).
