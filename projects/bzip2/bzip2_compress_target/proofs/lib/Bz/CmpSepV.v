(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast LiaTuning SepLin SepLinT.
From Ltac2 Require Ltac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma sep_use_v : forall b1 a2 b2 a1 e1 a e2 A : Z,
  (b1 <= a2 \/ b2 <= a1) -> a1 <= A -> e1 <= b1 -> a2 <= a -> e2 <= b2 -> (e1 <= a \/ e2 <= A).
Proof. intros. lia. Qed.
Lemma sep_use_v' : forall b1 a2 b2 a1 e1 a e2 A : Z,
  (b1 <= a2 \/ b2 <= a1) -> a2 <= A -> e1 <= b2 -> a1 <= a -> e2 <= b1 -> (e1 <= a \/ e2 <= A).
Proof. intros. lia. Qed.

Ltac sv_base e := lazymatch e with Z.add ?x _ => sv_base x | Z.sub ?x _ => sv_base x | _ => e end.
Ltac sv_is_lit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac sv_same x y := first [ constr_eq x y | sv_is_lit x; sv_is_lit y ].
(* [comment removed for export] *)
Module SVC.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 clear_local_props () : unit :=
    let m := LiaTuning.zt_memo () in
    let ids := List.map_filter (fun (id, body, ty) =>
                 match body with
                 | Some _ => None
                 | None => if LiaTuning.zt_is_prop_m m ty then (if LiaTuning.zt_is_local id then Some id else None) else None
                 end) (Control.hyps ()) in
    match ids with [] => () | _ :: _ => Std.clear ids end.
End SVC.
Ltac sv_clear_local := ltac2:(Control.enter SVC.clear_local_props).
Ltac sv_lia :=
  first [ solve [ sv_clear_local; Zify.zify; xlia zchecker ]   (* [comment removed for export] *)
        | solve [ sv_clear_local; lia ]
        | repeat match goal with
                 | H : _ \/ _ |- _ => clear H
                 | H : StoreFast.sf_hide _ |- _ => clear H
                 end; lia ].
Ltac sv_use H b1 a2 b2 a1 :=
  lazymatch goal with |- (?e1 <= ?a \/ ?e2 <= ?A) =>
    let bA := sv_base A in let ba := sv_base a in
    let c1 := sv_base a1 in let c2 := sv_base a2 in
    first [ sv_same c1 bA; sv_same c2 ba; apply (sep_use_v b1 a2 b2 a1 e1 a e2 A H); sv_lia
          | sv_same c2 bA; sv_same c1 ba; apply (sep_use_v' b1 a2 b2 a1 e1 a e2 A H); sv_lia ]
  end.
Ltac sep_vis :=
  match goal with
  | H : (?b1 <= ?a2 \/ ?b2 <= ?a1) |- _ => sv_use H b1 a2 b2 a1
  | H : id (?b1 <= ?a2 \/ ?b2 <= ?a1) |- _ => sv_use H b1 a2 b2 a1
  | H : StoreFast.sf_hide (?b1 <= ?a2 \/ ?b2 <= ?a1) |- _ => sv_use H b1 a2 b2 a1
  end.
(* [comment removed for export] *)
Ltac sv_old_same :=
  first [ solve [ sv_clear_local; Zify.zify; xlia zchecker ] | left; solve [ sv_clear_local; lia ] | right; solve [ sv_clear_local; lia ] ].
Ltac sv_conj_with fallback :=
  first [ SepLin.sl_conj ltac:(idtac; sv_old_same) ltac:(idtac; sv_lia) ltac:(idtac; sep_vis)
        | SepLin.sl_not_conj;
          first [ lazymatch goal with |- (?e1 <= ?a \/ ?e2 <= ?A) =>
                    (* [comment removed for export] *)
                    let bA := sv_base A in let ba := sv_base a in sv_same bA ba; sv_old_same end
                | sep_vis ]
        | fallback ].
(* [comment removed for export] *)
Ltac slia_orig := first [ exact I | lia | split; [lia|exact I] ].
Ltac tslia_orig := first [ exact I | StoreFast.tlia | split; [ StoreFast.tlia | exact I ] ].
Ltac slia_v :=
  lazymatch goal with
  | |- True => exact I
  | |- (_ <= _ \/ _ <= _) /\ _ => first [ split; [ sv_conj_with ltac:(lia) | slia_v ] | slia_orig ]
  | |- (_ <= _ \/ _ <= _) => first [ sv_conj_with ltac:(lia) | slia_orig ]
  | |- ~ _ /\ _ => first [ SepLinT.sl_outside | slia_orig ]   (* [comment removed for export] *)
  | |- _ => slia_orig
  end.
Ltac tslia_v :=
  lazymatch goal with
  | |- True => exact I
  | |- (_ <= _ \/ _ <= _) /\ _ => first [ split; [ sv_conj_with ltac:(StoreFast.tlia) | tslia_v ] | tslia_orig ]
  | |- (_ <= _ \/ _ <= _) => first [ sv_conj_with ltac:(StoreFast.tlia) | tslia_orig ]
  | |- ~ _ /\ _ => first [ SepLinT.sl_outside | tslia_orig ]   (* [comment removed for export] *)
  | |- _ => tslia_orig
  end.
