(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Using "Type".

Inductive ctree : Type :=
| CLeaf (P : Prop)
| CNode (l r : ctree).

Fixpoint cdenote (t : ctree) : Prop :=
  match t with CLeaf P => P | CNode l r => cdenote l /\ cdenote r end.

Fixpoint ccurry (t : ctree) (G : Prop) : Prop :=
  match t with CLeaf P => P -> G | CNode l r => ccurry l (ccurry r G) end.

Lemma elim_tree : forall (t : ctree) (G : Prop), cdenote t -> ccurry t G -> G.
Proof.
  induction t as [P | l IHl r IHr]; intros G H K; cbn in *.
  - exact (K H).
  - destruct H as [Hl Hr]. exact (IHr G Hr (IHl _ Hl K)).
Qed.

Ltac dand_chain T n :=
  lazymatch n with
  | S O => constr:(CLeaf T)
  | S ?n' =>
      lazymatch T with
      | ?a /\ ?b => let r := dand_chain b n' in constr:(CNode (CLeaf a) r)
      | _ => let T' := eval hnf in T in
             lazymatch T' with
             | ?a /\ ?b => let r := dand_chain b n' in constr:(CNode (CLeaf a) r)
             end
      end
  end.

Ltac dand_full T :=
  lazymatch T with
  | ?a /\ ?b => let ta := dand_full a in let tb := dand_full b in constr:(CNode ta tb)
  | _ => constr:(CLeaf T)
  end.

Ltac dand_prod t G :=
  lazymatch t with
  | CLeaf ?P => constr:(P -> G)
  | CNode ?l ?r => let Gr := dand_prod r G in dand_prod l Gr
  end.

Ltac dand_apply t c :=
  lazymatch goal with
  | |- ?G => let P := dand_prod t G in refine (elim_tree t G c _); change_no_check P
  end.

Ltac dand_core c n :=
  let T := type of c in
  let t := dand_chain T n in
  dand_apply t c;
  tryif is_var c then clear c else idtac.

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) ")" :=
  first [ dand_core c (S (S O)); intros p1 p2 | destruct c as [p1 p2] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) ")" :=
  first [ dand_core c (S (S (S O))); intros p1 p2 p3 | destruct c as [p1 [p2 p3]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) ")" :=
  first [ dand_core c (S (S (S (S O)))); intros p1 p2 p3 p4 | destruct c as [p1 [p2 [p3 p4]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) ")" :=
  first [ dand_core c (S (S (S (S (S O))))); intros p1 p2 p3 p4 p5 | destruct c as [p1 [p2 [p3 [p4 p5]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) ")" :=
  first [ dand_core c (S (S (S (S (S (S O)))))); intros p1 p2 p3 p4 p5 p6 | destruct c as [p1 [p2 [p3 [p4 [p5 p6]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S O))))))); intros p1 p2 p3 p4 p5 p6 p7 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 p7]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S O)))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 p8]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S O))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 p9]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S O)))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 p10]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S O))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 p11]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 p12]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 p13]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 p14]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 p15]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 p16]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 p17]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 p18]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 p19]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 p20]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 p21]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 p22]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 p23]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 p24]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 p25]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 p26]]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) "&" simple_intropattern(p27) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 [p26 p27]]]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) "&" simple_intropattern(p27) "&" simple_intropattern(p28) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 [p26 [p27 p28]]]]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) "&" simple_intropattern(p27) "&" simple_intropattern(p28) "&" simple_intropattern(p29) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 [p26 [p27 [p28 p29]]]]]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) "&" simple_intropattern(p27) "&" simple_intropattern(p28) "&" simple_intropattern(p29) "&" simple_intropattern(p30) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 [p26 [p27 [p28 [p29 p30]]]]]]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) "&" simple_intropattern(p27) "&" simple_intropattern(p28) "&" simple_intropattern(p29) "&" simple_intropattern(p30) "&" simple_intropattern(p31) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 [p26 [p27 [p28 [p29 [p30 p31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]] ].

Tactic Notation "dand" constr(c) "as" "(" simple_intropattern(p1) "&" simple_intropattern(p2) "&" simple_intropattern(p3) "&" simple_intropattern(p4) "&" simple_intropattern(p5) "&" simple_intropattern(p6) "&" simple_intropattern(p7) "&" simple_intropattern(p8) "&" simple_intropattern(p9) "&" simple_intropattern(p10) "&" simple_intropattern(p11) "&" simple_intropattern(p12) "&" simple_intropattern(p13) "&" simple_intropattern(p14) "&" simple_intropattern(p15) "&" simple_intropattern(p16) "&" simple_intropattern(p17) "&" simple_intropattern(p18) "&" simple_intropattern(p19) "&" simple_intropattern(p20) "&" simple_intropattern(p21) "&" simple_intropattern(p22) "&" simple_intropattern(p23) "&" simple_intropattern(p24) "&" simple_intropattern(p25) "&" simple_intropattern(p26) "&" simple_intropattern(p27) "&" simple_intropattern(p28) "&" simple_intropattern(p29) "&" simple_intropattern(p30) "&" simple_intropattern(p31) "&" simple_intropattern(p32) ")" :=
  first [ dand_core c (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))); intros p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 | destruct c as [p1 [p2 [p3 [p4 [p5 [p6 [p7 [p8 [p9 [p10 [p11 [p12 [p13 [p14 [p15 [p16 [p17 [p18 [p19 [p20 [p21 [p22 [p23 [p24 [p25 [p26 [p27 [p28 [p29 [p30 [p31 p32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]] ].


Ltac dand_names t cur :=
  lazymatch t with
  | CNode ?l ?r => let n := fresh "F" in pose proof I as n; dand_names l n; dand_names r cur
  | CLeaf _ => clear cur; intro cur
  end.

Ltac destr_conj_lin H :=
  lazymatch type of H with
  | _ /\ _ =>
      let T := type of H in
      let t := dand_full T in
      dand_apply t H; dand_names t H
  | _ => idtac
  end.
