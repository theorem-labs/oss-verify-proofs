(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac StoreFast.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Lemma sep_use : forall b1 a2 b2 a1 e1 a e2 A : Z,
  id (b1 <= a2 \/ b2 <= a1) ->
  (a1 <= A /\ e1 <= b1 /\ a2 <= a /\ e2 <= b2 /\ A <= e1 /\ a <= e2) ->
  (e1 <= a \/ e2 <= A).
Proof. unfold id. intros. lia. Qed.

Lemma sep_use' : forall b1 a2 b2 a1 e1 a e2 A : Z,
  id (b1 <= a2 \/ b2 <= a1) ->
  (a2 <= A /\ e1 <= b2 /\ a1 <= a /\ e2 <= b1 /\ A <= e1 /\ a <= e2) ->
  (e1 <= a \/ e2 <= A).
Proof. unfold id. intros. lia. Qed.
End ACeilS1.


Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.

(* [comment removed for export] *)
Ltac sep_base e :=
  lazymatch e with
  | Z.add ?x _ => sep_base x
  | Z.sub ?x _ => sep_base x
  | _ => e
  end.
Ltac sep_is_lit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac sep_same x y := first [ constr_eq x y | sep_is_lit x; sep_is_lit y ].

Ltac tlia1 := Zify.zify; xlia zchecker.
Ltac tlia2 := sf_unhide; unhide_disj;
              first [ zify_prune_neg; Zify.zify; xlia zchecker
                    | zify_prune_plain; Zify.zify; xlia zchecker
                    | Zify.zify; xlia zchecker ].

Ltac sep_tac :=
  lazymatch goal with |- (?e1 <= ?a \/ ?e2 <= ?A) =>
    let bA := sep_base A in let ba := sep_base a in
    match goal with
    | H : id (?b1 <= ?a2 \/ ?b2 <= ?a1) |- _ =>
        let c1 := sep_base a1 in let c2 := sep_base a2 in
        first [ sep_same c1 bA; sep_same c2 ba; apply (sep_use b1 a2 b2 a1 e1 a e2 A H); tlia1
              | sep_same c2 bA; sep_same c1 ba; apply (sep_use' b1 a2 b2 a1 e1 a e2 A H); tlia1 ]
    end
  end.

(* [comment removed for export] *)
Ltac tslia_sep := first [ exact I | tlia1 | sep_tac | tlia2 | split; [ first [ tlia1 | sep_tac | tlia2 ] | exact I ] ].
