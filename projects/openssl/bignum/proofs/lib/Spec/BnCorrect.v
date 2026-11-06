(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnInv BnSpecs
  BnSpecs2 BnDivSpec BnMulSpec BnAddSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Correct.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition ls_inv (ls : LS) (X : blocks) : Prop := st_ok ls /\ own ls X /\ ctx_rest (ls_ctx ls).

Definition sgn (b : bool) : Z := if b then -1 else 1.

End Correct.
