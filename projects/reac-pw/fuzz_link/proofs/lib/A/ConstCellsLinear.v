(* Linear proofs over a unit's const-cell list (YG0f.acell). A unit with many instrumented globals has many const cells
   (reac-pw/fuzz_link's generated A/AF0m.v: 9915, of them 9151 shadow bytes of its 43 globals' redzones), and a case split
   or a Forall_cons chain over the list costs time quadratic in its length (measured on reac-pw/fuzz_link:
   2000 cells already take 55 s). These lemmas replace such proofs by one boolean check of the whole list, run by
   vm_compute in linear time:
   - const_at_zero: a cell at a given address and width in the list holds 0, if every cell of the list at that address
     and width holds 0;
   - cells_lt_of_noasec: every cell of the list satisfies AFib.cell_lt for every section count, if no cell names a
     section address ASec. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AFib.
Import ListNotations.

Fixpoint aexp_eqb (a b : aexp) : bool :=
  match a, b with
  | ANum x, ANum y | ASp x, ASp y | AQ x, AQ y | AT x, AT y | AC x, AC y | AF x, AF y | ANB x, ANB y | ASB x, ASB y
  | ATop x, ATop y | ATsd x, ATsd y | AStk x, AStk y | AInst x, AInst y | ADepot x, ADepot y | AStore x, AStore y
  | ATp x, ATp y | AIal x, AIal y | AD x, AD y => Z.eqb x y
  | ASec r x, ASec s y => Nat.eqb r s && Z.eqb x y
  | ASh e, ASh f => aexp_eqb e f
  | _, _ => false
  end.

Lemma aexp_eqb_refl : forall a, aexp_eqb a a = true.
Proof. induction a; cbn; rewrite ?Z.eqb_refl, ?Nat.eqb_refl; auto. Qed.

(* the value 0 *)
Definition aval_is_zero (v : aval) : bool := match v with AV (ANum 0) => true | _ => false end.

Lemma const_at_zero : forall (L : list acell) (a : aexp) (w : nat) (v : aval),
  In (ACell a w v) L ->
  forallb (fun c => negb (aexp_eqb (c_at c) a && Nat.eqb (c_w c) w) || aval_is_zero (c_val c)) L = true ->
  v = AV (ANum 0).
Proof.
  intros L a w v Hin Hall.
  pose proof (proj1 (forallb_forall _ _) Hall _ Hin) as H. cbn [c_at c_w c_val] in H.
  rewrite aexp_eqb_refl, Nat.eqb_refl in H. cbn in H.
  destruct v as [e|m z]; [|discriminate H]. destruct e; try discriminate H. destruct z; try discriminate H. reflexivity.
Qed.

(* no section address anywhere in an address expression *)
Fixpoint aexp_noasec (e : aexp) : bool :=
  match e with ASec _ _ => false | ASh e' => aexp_noasec e' | _ => true end.

Lemma asec_lt_of_noasec : forall e n, aexp_noasec e = true -> asec_lt n e.
Proof. induction e; cbn; intros n H; try exact I; try discriminate H. exact (IHe n H). Qed.

Definition cell_noasec (c : acell) : bool :=
  aexp_noasec (c_at c) && match c_val c with AV e => aexp_noasec e | AVmask _ _ => true end.

Lemma cells_lt_of_noasec : forall (L : list acell), forallb cell_noasec L = true -> forall nn, Forall (AFib.cell_lt nn) L.
Proof.
  intros L H nn. apply Forall_forall. intros c Hc.
  pose proof (proj1 (forallb_forall _ _) H c Hc) as Hc'. unfold cell_noasec in Hc'.
  apply andb_prop in Hc' as [H1 H2]. unfold AFib.cell_lt. split; [exact (asec_lt_of_noasec _ nn H1)|].
  revert H2. destruct (c_val c) as [e|m z]; intros H2; [exact (asec_lt_of_noasec e nn H2) | exact I].
Qed.
