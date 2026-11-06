(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Ltac2 Require Import Ltac2.
From Ltac2 Require String Ident Control List Std Ltac1.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Inductive lin_box (P : Prop) : Prop := LinBox : P -> lin_box P.
Lemma lin_box_elim : forall P : Prop, lin_box P -> P. Proof. intros P [p]; exact p. Qed.

Inductive pack45 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41 P42 P43 P44 P45 : Prop) : Prop :=
  Pack45 : P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> P8 -> P9 -> P10 -> P11 -> P12 -> P13 -> P14 -> P15 -> P16 -> P17 -> P18 -> P19 -> P20 -> P21 -> P22 -> P23 -> P24 -> P25 -> P26 -> P27 -> P28 -> P29 -> P30 -> P31 -> P32 -> P33 -> P34 -> P35 -> P36 -> P37 -> P38 -> P39 -> P40 -> P41 -> P42 -> P43 -> P44 -> P45 -> pack45 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41 P42 P43 P44 P45.

Lemma and_pack45 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41 P42 P43 P44 P45 : Prop,
  P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7 /\ P8 /\ P9 /\ P10 /\ P11 /\ P12 /\ P13 /\ P14 /\ P15 /\ P16 /\ P17 /\ P18 /\ P19 /\ P20 /\ P21 /\ P22 /\ P23 /\ P24 /\ P25 /\ P26 /\ P27 /\ P28 /\ P29 /\ P30 /\ P31 /\ P32 /\ P33 /\ P34 /\ P35 /\ P36 /\ P37 /\ P38 /\ P39 /\ P40 /\ P41 /\ P42 /\ P43 /\ P44 /\ P45 -> pack45 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41 P42 P43 P44 P45.
Proof. intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41 P42 P43 P44 P45 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H35 & H36 & H37 & H38 & H39 & H40 & H41 & H42 & H43 & H44 & H45). constructor; assumption. Qed.

Inductive pack15 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 : Prop) : Prop :=
  Pack15 : P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> P8 -> P9 -> P10 -> P11 -> P12 -> P13 -> P14 -> P15 -> pack15 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15.
Lemma and_pack15 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 : Prop,
  P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7 /\ P8 /\ P9 /\ P10 /\ P11 /\ P12 /\ P13 /\ P14 /\ P15 -> pack15 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15.
Proof. (intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15; cps_intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15)). constructor; assumption. Qed.

(* [comment removed for export] *)
Ltac2 lin_is_atom (id : ident) : bool :=
  let s := Ident.to_string id in
  if Int.lt (String.length s) 4 then false else String.equal (String.sub s 0 4) "LINa".
Ltac2 lin_clear_atoms () : unit :=
  let ids := List.map_filter (fun h => let (id, _, _) := h in if lin_is_atom id then Some id else None) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac lin_clear_atoms := ltac2:(Control.enter lin_clear_atoms).

(* [comment removed for export] *)
Lemma len_natZ_lit : forall (A : Type) (l : list A) (n : nat) (z : Z), Z.of_nat n = z -> length l = n -> Z.of_nat (length l) = z.
Proof. intros A l n z <- ->. reflexivity. Qed.
Ltac lin_natZ_core H :=
  lazymatch type of H with
  | @eq nat (@length ?A ?l) ?n =>
      let z := eval cbv in (Z.of_nat n) in
      lazymatch z with Z0 => idtac | Zpos _ => idtac end;
      apply (len_natZ_lit A l n z eq_refl) in H
  | _ => idtac
  end.
Tactic Notation "lin_natZ" ident(H) := first [ lin_natZ_core H | idtac ].
Ltac2 lin_natZ_atoms () : unit :=
  List.iter (fun h => let (id, _, ty) := h in
     if lin_is_atom id then
       lazy_match! ty with
       | @eq nat (@length _ _) _ => let c := Control.hyp id in ltac1:(c |- first [ lin_natZ_core c | idtac ]) (Ltac1.of_constr c)
       | _ => ()
       end
     else ()) (Control.hyps ()).
Ltac lin_natZ_atoms := ltac2:(Control.enter lin_natZ_atoms).

(* [comment removed for export] *)
Fixpoint conjs (l : list Prop) : Prop :=
  match l with
  | nil => True
  | cons a nil => a
  | cons a r => a /\ conjs r
  end.
Fixpoint curried (l : list Prop) (P : Prop) : Prop :=
  match l with
  | nil => P
  | cons a r => a -> curried r P
  end.
Lemma conjs_elim : forall (l : list Prop) (P : Prop), conjs l -> curried l P -> P.
Proof.
  induction l as [|a r IH]; intros P H K; [exact K|].
  destruct r as [|b r']; [exact (K H)|].
  destruct H as [Ha Hr]. exact (IH P Hr (K Ha)).
Qed.
Ltac lin_conj_list T :=
  lazymatch T with
  | ?A /\ ?B => let r := lin_conj_list B in constr:(@cons Prop A r)
  | _ => constr:(@cons Prop T (@nil Prop))
  end.
Ltac lin_intros_n l :=
  lazymatch l with
  | @nil _ => idtac
  | @cons _ _ ?r => let a := fresh "LINa" in intro a; lin_intros_n r
  end.
(* [comment removed for export] *)
Ltac lin_split_cps C :=
  lazymatch type of C with ?T =>
    let l := lin_conj_list T in
    lazymatch goal with |- ?G => apply (conjs_elim l G C); clear C; lin_intros_n l; change G end
  end.

Ltac lin_split_generic C :=
  lazymatch type of C with
  | _ /\ _ => let a := fresh "LINa" in let b := fresh "LINa" in destruct C as [a b]; lin_split_generic b
  | _ => idtac
  end.

Ltac lin_split_core LIN :=
  lazymatch type of LIN with
  | lin_box _ => idtac
  | ?T =>
      try lin_clear_atoms;
      let C := fresh "LINp" in
      first [ pose proof (and_pack45 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LIN) as C;
              destruct C as [?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa]
            | pose proof LIN as C; first [ lin_split_cps C | lin_split_generic C ] ];
      lin_natZ_atoms;
      apply LinBox in LIN
  end.
(* [comment removed for export] *)
Tactic Notation "lin_split" ident(LIN) := lin_split_core LIN.
Tactic Notation "lin_unbox" ident(LIN) := first [ apply lin_box_elim in LIN | idtac ].
(* [comment removed for export] *)
Tactic Notation "lin_atoms" ident(H) := lin_split_generic H.
(* [comment removed for export] *)
Ltac lin_pose15 t :=
  let C := fresh "LINp" in
  pose proof (and_pack15 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t) as C;
  destruct C as [?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa ?LINa].
