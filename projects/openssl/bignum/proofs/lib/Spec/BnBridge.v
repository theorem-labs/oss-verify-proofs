(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prog LB_Inv LibProg LibSafe LibOps.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint embed {A} (t : btree bptr A) : lprog A :=
  match t with
  | TRet a => LRet a
  | TUnr => LUnr
  | TMalloc n k => LMalloc n (fun r => embed (k r))
  | TFree p k => LFree p (embed k)
  end.

Definition BN_NBLK : Z := 11.
Definition BN_BSZ : Z := 524288.

Definition bn_lib_one (ls : lstate bptr) (d : list Z) : lprog (lstate bptr * Z) := embed (bn_one ls d).
Definition bn_linv (ls : lstate bptr) (X : list (bptr * Z)) : Prop := ls_inv ls X.

