(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy7F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy7F. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5.
Local Set Keyed Unification.

Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

Definition rejects {R} (t : M R) : Prop :=
match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek (e : ev) : bool := match e with EPeek _ _ _ => true | _ => false end.
Definition is_undef (e : ev) : bool := match e with EUndef _ => true | _ => false end.

Fixpoint ftree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
match t with
| SRet r => Post L r
| SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> ftree L (k v) Post
| SVis (EUndef _) _ => False
| SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)
end.

Fixpoint ptree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
match t with
| SRet r => Post L r
| SVis (EPeek _ _ _) k => False
| SVis (EUndef _) _ => False
| SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ptree (event_post L e a) (k a) Post else rejects (k a)
end.

Ltac case_ans :=
match goal with
| |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
| H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
end.

Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

End PRUN.

