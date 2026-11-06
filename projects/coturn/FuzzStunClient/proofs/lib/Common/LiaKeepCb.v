(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac LKcb := repeat match goal with x := _ |- _ => clearbody x end.

Module LiaKeepCbSelfTest.
  Local Open Scope Z_scope.
  Goal forall (x y : Z), let b := Z.of_nat (Z.to_nat (x + 1)) in x < y -> y < b -> x < b.
  Proof. intros x y b Hxy Hyb. ltac2:(LK.k [@Hxy; @Hyb]); LKcb; lia. Qed.
End LiaKeepCbSelfTest.
