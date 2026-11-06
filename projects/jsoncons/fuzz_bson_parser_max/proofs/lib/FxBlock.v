(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.

Module BLKF.
Import AX2. Import AX2B. Import APC.

(* [comment removed for export] *)
Fixpoint eqb4 (n m : nat) {struct n} : bool :=
  match n, m with
  | S (S (S (S n'))), S (S (S (S m'))) => eqb4 n' m'
  | _, _ => Nat.eqb n m
  end.
Lemma eqb4_eq : forall n m, eqb4 n m = Nat.eqb n m.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros m.
  destruct n as [|[|[|[|n']]]]; try reflexivity.
  destruct m as [|[|[|[|m']]]]; try reflexivity.
  cbn [eqb4 Nat.eqb]. apply IH. repeat constructor.
Qed.
Fixpoint expr_eqbF (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => eqb4 a b
  | EAlu o a b, EAlu o' a' b' => if aluop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EAluw o a b, EAluw o' a' b' => if aluop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EMd o a b, EMd o' a' b' => if mulop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EMdw o a b, EMdw o' a' b' => if mulop_eqb o o' then if expr_eqbF a a' then expr_eqbF b b' else false else false
  | EExt s l n a, EExt s' l' n' a' => if Bool.eqb s s' then if Nat.eqb l l' then if Nat.eqb n n' then expr_eqbF a a' else false else false else false
  | EBlob s k i n, EBlob s' k' i' n' => if Bool.eqb s s' then if Nat.eqb k k' then if Z.eqb i i' then Nat.eqb n n' else false else false else false
  | _, _ => false
  end.
Lemma expr_eqbF_eq : forall x y, expr_eqbF x y = expr_eqb x y.
Proof.
  induction x; destruct y; cbn [expr_eqbF expr_eqb]; try reflexivity;
    rewrite ?eqb4_eq, ?IHx1, ?IHx2, ?IHx;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bm_get (l : list bool) (n : nat) : bool :=
  match l with [] => false | b :: r => match n with O => b | S m => bm_get r m end end.
Fixpoint bm_set (l : list bool) (n : nat) : list bool :=
  match n with
  | O => match l with [] => [true] | _ :: r => true :: r end
  | S m => match l with [] => false :: bm_set [] m | b :: r => b :: bm_set r m end
  end.
Fixpoint bm_clr (l : list bool) (n : nat) : list bool :=
  match l with [] => [] | b :: r => match n with O => false :: r | S m => b :: bm_clr r m end end.
Fixpoint bm_cnt (l : list bool) : nat := match l with [] => O | b :: r => if b then S (bm_cnt r) else bm_cnt r end.

Lemma bm_get_nil : forall n, bm_get [] n = false. Proof. intros [|n]; reflexivity. Qed.
Lemma bm_get_set : forall l n v, bm_get (bm_set l n) v = (Nat.eqb v n || bm_get l v)%bool.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l v.
  - destruct l as [|b r]; destruct v as [|v]; cbn [bm_set bm_get Nat.eqb orb]; rewrite ?bm_get_nil; reflexivity.
  - destruct l as [|b r]; destruct v as [|v]; cbn [bm_set bm_get Nat.eqb orb]; rewrite ?IH, ?bm_get_nil; reflexivity.
Qed.
Lemma bm_get_clr : forall l n v, bm_get (bm_clr l n) v = (bm_get l v && negb (Nat.eqb v n))%bool.
Proof.
  induction l as [|b r IH]; intros n v; [reflexivity|].
  destruct n as [|n]; destruct v as [|v]; cbn [bm_clr bm_get Nat.eqb negb]; rewrite ?IH, ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
Qed.
Lemma bm_cnt_clr : forall l n, bm_get l n = true -> bm_cnt (bm_clr l n) = Nat.pred (bm_cnt l).
Proof.
  induction l as [|b r IH]; intros n H; [discriminate|].
  destruct n as [|n]; cbn [bm_get] in H.
  - subst b. reflexivity.
  - cbn [bm_clr bm_cnt]. rewrite (IH n H). destruct b; [|reflexivity].
    destruct (bm_cnt r) eqn:E; [|reflexivity]. exfalso. clear IH. revert n H E. induction r as [|c q IHq]; intros n H E; [destruct n; discriminate|].
    destruct n as [|n]; cbn [bm_get bm_cnt] in *; [subst c; discriminate|]. destruct c; [discriminate|]. exact (IHq n H E).
Qed.
Lemma bm_cnt_0 : forall l, bm_cnt l = O -> forall n, bm_get l n = false.
Proof.
  induction l as [|b r IH]; intros H n; [apply bm_get_nil|]. cbn [bm_cnt] in H. destruct b; [discriminate|].
  destruct n as [|n]; [reflexivity|]. exact (IH H n).
Qed.

(* [comment removed for export] *)
Fixpoint expr_cand (nx0 : nat) (e : expr) (C : list bool) : list bool :=
  match e with
  | ELit _ => C
  | EVar n => if Nat.ltb n nx0 then C else if bm_get C n then C else bm_set C n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_cand nx0 x (expr_cand nx0 y C)
  | EExt _ _ _ x => expr_cand nx0 x C
  | EBlob _ _ _ _ => C
  end.
Fixpoint kn_cand (nx0 : nat) (kn : list kentry) (C : list bool) : list bool :=
  match kn with
  | [] => C
  | K :: r =>
      kn_cand nx0 r (match K with
                     | KRange e _ _ | KAlign e _ => expr_cand nx0 e C
                     | KDisj a1 n1 a2 n2 => expr_cand nx0 (a_base a1) (expr_cand nx0 n1 (expr_cand nx0 (a_base a2) (expr_cand nx0 n2 C)))
                     | _ => C
                     end)
  end.
(* [comment removed for export] *)
Fixpoint expr_has (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar n => Nat.eqb v n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_has v x then true else expr_has v y
  | EExt _ _ _ x => expr_has v x
  | EBlob _ _ _ _ => false
  end.
(* [comment removed for export] *)
Fixpoint expr_clr (e : expr) (st : list bool * nat) : list bool * nat :=
  match e with
  | ELit _ => st
  | EVar n => if bm_get (fst st) n then (bm_clr (fst st) n, Nat.pred (snd st)) else st
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_clr x (expr_clr y st)
  | EExt _ _ _ x => expr_clr x st
  | EBlob _ _ _ _ => st
  end.
Definition CINV (st : list bool * nat) : Prop := snd st = bm_cnt (fst st).
Lemma expr_clr_ok : forall e st, CINV st ->
  CINV (expr_clr e st) /\ forall v, bm_get (fst (expr_clr e st)) v = (bm_get (fst st) v && negb (expr_has v e))%bool.
Proof.
  induction e; intros st H; cbn [expr_clr expr_has];
    try (split; [exact H|intros v; rewrite Bool.andb_true_r; reflexivity]).
  - destruct (bm_get (fst st) n) eqn:E.
    + split; [unfold CINV in *; cbn [fst snd]; rewrite (bm_cnt_clr _ _ E), H; reflexivity|].
      intros v. cbn [fst]. apply bm_get_clr.
    + split; [exact H|]. intros v. destruct (Nat.eqb_spec v n) as [->|NE]; [rewrite E; reflexivity|rewrite Bool.andb_true_r; reflexivity].
  - destruct (IHe2 st H) as [H2 G2]. destruct (IHe1 _ H2) as [H1 G1]. split; [exact H1|].
    intros v. rewrite G1, G2. destruct (expr_has v e1), (expr_has v e2), (bm_get (fst st) v); reflexivity.
  - destruct (IHe2 st H) as [H2 G2]. destruct (IHe1 _ H2) as [H1 G1]. split; [exact H1|].
    intros v. rewrite G1, G2. destruct (expr_has v e1), (expr_has v e2), (bm_get (fst st) v); reflexivity.
  - destruct (IHe2 st H) as [H2 G2]. destruct (IHe1 _ H2) as [H1 G1]. split; [exact H1|].
    intros v. rewrite G1, G2. destruct (expr_has v e1), (expr_has v e2), (bm_get (fst st) v); reflexivity.
  - destruct (IHe2 st H) as [H2 G2]. destruct (IHe1 _ H2) as [H1 G1]. split; [exact H1|].
    intros v. rewrite G1, G2. destruct (expr_has v e1), (expr_has v e2), (bm_get (fst st) v); reflexivity.
  - exact (IHe st H).
Qed.

(* [comment removed for export] *)
Section Walk.
Variable T : Type.
Variable f : T -> list bool * nat -> list bool * nat.
Variable has : nat -> T -> bool.
Hypothesis f_ok : forall x st, CINV st ->
  CINV (f x st) /\ forall v, bm_get (fst (f x st)) v = (bm_get (fst st) v && negb (has v x))%bool.
Fixpoint walk (l : list T) (st : list bool * nat) : list bool * nat :=
  match l with
  | [] => st
  | x :: r => match snd st with O => st | S _ => walk r (f x st) end
  end.
Lemma walk_ok : forall l st, CINV st ->
  CINV (walk l st) /\ forall v, bm_get (fst (walk l st)) v = (bm_get (fst st) v && negb (existsb (has v) l))%bool.
Proof.
  induction l as [|x r IH]; intros st H; cbn [walk existsb].
  - split; [exact H|]. intros v. rewrite Bool.andb_true_r. reflexivity.
  - destruct (snd st) eqn:E.
    + split; [exact H|]. intros v. unfold CINV in H. rewrite E in H. rewrite (bm_cnt_0 _ (eq_sym H) v). reflexivity.
    + destruct (f_ok x st H) as [H1 G1]. destruct (IH _ H1) as [H2 G2]. split; [exact H2|].
      intros v. rewrite G2, G1. destruct (bm_get (fst st) v), (has v x), (existsb (has v) r); reflexivity.
Qed.
End Walk.

Definition kentry_clr (K : kentry) (st : list bool * nat) : list bool * nat :=
  match K with
  | KWord a _ v => expr_clr (a_base a) (expr_clr v st)
  | KZero a n | KWr a n | KUnk a n => expr_clr (a_base a) (expr_clr n st)
  | KBlob a n _ | KFill a n _ => expr_clr (a_base a) (expr_clr n st)
  | _ => st
  end.
Definition kentry_has (v : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ x => if expr_has v (a_base a) then true else expr_has v x
  | KZero a n | KWr a n | KUnk a n => if expr_has v (a_base a) then true else expr_has v n
  | KBlob a n _ | KFill a n _ => if expr_has v (a_base a) then true else expr_has v n
  | _ => false
  end.
Definition pair_clr (p : expr * expr) (st : list bool * nat) := expr_clr (fst p) (expr_clr (snd p) st).
Definition pair_has (v : nat) (p : expr * expr) : bool := if expr_has v (fst p) then true else expr_has v (snd p).
Definition amap_clr (m : amap) (st : list bool * nat) := expr_clr (am_base m) (expr_clr (am_len m) st).
Definition amap_has (v : nat) (m : amap) : bool := if expr_has v (am_base m) then true else expr_has v (am_len m).
Definition fd_clr (f : afd) (st : list bool * nat) := match f with FdFile _ l o => expr_clr l (expr_clr o st) | _ => st end.
Definition fd_has (v : nat) (f : afd) : bool := match f with FdFile _ l o => if expr_has v l then true else expr_has v o | _ => false end.
Lemma two_clr_ok : forall e1 e2 st, CINV st ->
  CINV (expr_clr e1 (expr_clr e2 st)) /\
  forall v, bm_get (fst (expr_clr e1 (expr_clr e2 st))) v = (bm_get (fst st) v && negb (if expr_has v e1 then true else expr_has v e2))%bool.
Proof.
  intros e1 e2 st H. destruct (expr_clr_ok e2 st H) as [H2 G2]. destruct (expr_clr_ok e1 _ H2) as [H1 G1]. split; [exact H1|].
  intros v. rewrite G1, G2. destruct (expr_has v e1), (expr_has v e2), (bm_get (fst st) v); reflexivity.
Qed.
Lemma kentry_clr_ok : forall K st, CINV st ->
  CINV (kentry_clr K st) /\ forall v, bm_get (fst (kentry_clr K st)) v = (bm_get (fst st) v && negb (kentry_has v K))%bool.
Proof.
  intros K st H. destruct K; cbn [kentry_clr kentry_has]; try apply two_clr_ok; try exact H;
    (split; [exact H|intros v; rewrite Bool.andb_true_r; reflexivity]).
Qed.
(* [comment removed for export] *)
Definition occ (v : nat) (cs : acs) : bool :=
  (expr_has v (a_brk cs) || (fd_has v (a_fd cs) || (existsb (pair_has v) (a_ghost cs) || (existsb (pair_has v) (a_vis cs)
   || (existsb (amap_has v) (a_maps cs) || (existsb (kentry_has v) (kn cs) || existsb (expr_has v) (s_regs (a_ss cs))))))))%bool.
Definition unmarked (cs : acs) (C : list bool) : list bool :=
  match bm_cnt C with
  | O => C
  | S _ as c =>
      let st := walk expr expr_clr (s_regs (a_ss cs)) (C, c) in
      let st := walk kentry kentry_clr (kn cs) st in
      let st := walk amap amap_clr (a_maps cs) st in
      let st := walk (expr * expr) pair_clr (a_vis cs) st in
      let st := walk (expr * expr) pair_clr (a_ghost cs) st in
      fst (expr_clr (a_brk cs) (fd_clr (a_fd cs) st))
  end.
Lemma unmarked_ok : forall cs C v, bm_get (unmarked cs C) v = (bm_get C v && negb (occ v cs))%bool.
Proof.
  intros cs C v. unfold unmarked. destruct (bm_cnt C) as [|c] eqn:EC.
  - rewrite (bm_cnt_0 _ EC v). reflexivity.
  - assert (H0 : CINV (C, S c)) by (unfold CINV; cbn [fst snd]; symmetry; exact EC).
    destruct (walk_ok expr expr_clr expr_has expr_clr_ok (s_regs (a_ss cs)) _ H0) as [H1 G1].
    destruct (walk_ok kentry kentry_clr kentry_has kentry_clr_ok (kn cs) _ H1) as [H2 G2].
    destruct (walk_ok amap amap_clr amap_has (fun m st => two_clr_ok (am_base m) (am_len m) st) (a_maps cs) _ H2) as [H3 G3].
    destruct (walk_ok (expr * expr) pair_clr pair_has (fun p st => two_clr_ok (fst p) (snd p) st) (a_vis cs) _ H3) as [H4 G4].
    destruct (walk_ok (expr * expr) pair_clr pair_has (fun p st => two_clr_ok (fst p) (snd p) st) (a_ghost cs) _ H4) as [H5 G5].
    set (st5 := walk (expr * expr) pair_clr (a_ghost cs) _) in *.
    assert (F : CINV (fd_clr (a_fd cs) st5) /\ forall v, bm_get (fst (fd_clr (a_fd cs) st5)) v = (bm_get (fst st5) v && negb (fd_has v (a_fd cs)))%bool).
    { unfold fd_clr, fd_has. destruct (a_fd cs); try (split; [exact H5|intros v0; rewrite Bool.andb_true_r; reflexivity]). apply two_clr_ok. exact H5. }
    destruct F as [H6 G6]. destruct (expr_clr_ok (a_brk cs) _ H6) as [_ G7].
    rewrite G7, G6, G5, G4, G3, G2, G1. cbn [fst]. unfold occ.
    destruct (bm_get C v), (expr_has v (a_brk cs)), (fd_has v (a_fd cs)), (existsb (pair_has v) (a_ghost cs)), (existsb (pair_has v) (a_vis cs)),
      (existsb (amap_has v) (a_maps cs)), (existsb (kentry_has v) (kn cs)), (existsb (expr_has v) (s_regs (a_ss cs))); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma in_live_expr : forall e t v, in_live_t (expr_vars_t e t) v = (expr_has v e || in_live_t t v)%bool.
Proof.
  induction e; intros t v; cbn [expr_vars_t expr_has]; try reflexivity.
  - unfold in_live_t. destruct (Nat.eqb_spec v n) as [->|NE].
    + rewrite pt_gss. reflexivity.
    + rewrite pt_gso by (intros HK; apply NE; apply vkey_inj; exact HK). reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - apply IHe.
Qed.
Lemma in_live_two : forall e1 e2 t v, in_live_t (expr_vars_t e1 (expr_vars_t e2 t)) v = ((if expr_has v e1 then true else expr_has v e2) || in_live_t t v)%bool.
Proof. intros. rewrite !in_live_expr. destruct (expr_has v e1); reflexivity. Qed.
Lemma in_live_fold : forall (T : Type) (g : T -> ptree unit -> ptree unit) (has : nat -> T -> bool),
  (forall x t v, in_live_t (g x t) v = (has v x || in_live_t t v)%bool) ->
  forall l t v, in_live_t (fold_right g t l) v = (existsb (has v) l || in_live_t t v)%bool.
Proof.
  intros T g has Hg l t v. induction l as [|x r IH]; [reflexivity|]. cbn [fold_right existsb]. rewrite Hg, IH.
  destruct (has v x); reflexivity.
Qed.
Lemma live_occ : forall cs v, in_live_t (live_vars_t cs) v = occ v cs.
Proof.
  intros cs v. unfold live_vars_t, occ. rewrite in_live_expr. f_equal.
  assert (FD : forall t, in_live_t (match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o t) | _ => t end) v = (fd_has v (a_fd cs) || in_live_t t v)%bool).
  { intros t. unfold fd_has. destruct (a_fd cs); try reflexivity. apply in_live_two. }
  rewrite FD. f_equal.
  rewrite (in_live_fold _ _ pair_has (fun p t v => in_live_two (fst p) (snd p) t v)). f_equal.
  rewrite (in_live_fold _ _ pair_has (fun p t v => in_live_two (fst p) (snd p) t v)). f_equal.
  rewrite (in_live_fold _ _ amap_has (fun m t v => in_live_two (am_base m) (am_len m) t v)). f_equal.
  rewrite (in_live_fold _ _ kentry_has).
  2:{ intros K t0 v0. destruct K; cbn [kentry_has]; try apply in_live_two; reflexivity. }
  f_equal. rewrite (in_live_fold _ _ expr_has in_live_expr). replace (in_live_t PTLeaf v) with false by (unfold in_live_t; rewrite pt_get_leaf; reflexivity). apply Bool.orb_false_r.
Qed.

(* [comment removed for export] *)
Lemma expr_cand_mono : forall nx0 e C v, bm_get C v = true -> bm_get (expr_cand nx0 e C) v = true.
Proof.
  intros nx0 e. induction e; intros C v H; cbn [expr_cand]; auto.
  destruct (Nat.ltb n nx0); [exact H|]. destruct (bm_get C n); [exact H|]. rewrite bm_get_set, H. apply Bool.orb_true_r.
Qed.
Lemma expr_cand_has : forall nx0 e C v, expr_has v e = true -> Nat.ltb v nx0 = false -> bm_get (expr_cand nx0 e C) v = true.
Proof.
  intros nx0 e. induction e; intros C v H L; cbn [expr_cand expr_has] in *; try discriminate.
  - apply Nat.eqb_eq in H. subst n. rewrite L. destruct (bm_get C v) eqn:E; [exact E|]. rewrite bm_get_set, Nat.eqb_refl. reflexivity.
  - destruct (expr_has v e1) eqn:E1; [apply IHe1; assumption|apply expr_cand_mono; apply IHe2; assumption].
  - destruct (expr_has v e1) eqn:E1; [apply IHe1; assumption|apply expr_cand_mono; apply IHe2; assumption].
  - destruct (expr_has v e1) eqn:E1; [apply IHe1; assumption|apply expr_cand_mono; apply IHe2; assumption].
  - destruct (expr_has v e1) eqn:E1; [apply IHe1; assumption|apply expr_cand_mono; apply IHe2; assumption].
  - apply IHe; assumption.
Qed.
Definition fact_has (v : nat) (K : kentry) : bool :=
  match K with
  | KRange e _ _ | KAlign e _ => expr_has v e
  | KDisj a1 n1 a2 n2 => if expr_has v (a_base a1) then true else if expr_has v n1 then true else if expr_has v (a_base a2) then true else expr_has v n2
  | _ => false
  end.
Lemma kn_cand_mono : forall nx0 kn C v, bm_get C v = true -> bm_get (kn_cand nx0 kn C) v = true.
Proof.
  intros nx0 kn. induction kn as [|K r IH]; intros C v H; [exact H|]. cbn [kn_cand]. apply IH.
  destruct K; try exact H; repeat apply expr_cand_mono; exact H.
Qed.
Lemma kn_cand_has : forall nx0 kn C K v, In K kn -> fact_has v K = true -> Nat.ltb v nx0 = false -> bm_get (kn_cand nx0 kn C) v = true.
Proof.
  intros nx0 kn. induction kn as [|K0 r IH]; intros C K v HI HF L; [destruct HI|]. cbn [kn_cand].
  destruct HI as [->|HI]; [|exact (IH _ K v HI HF L)].
  apply kn_cand_mono. destruct K; cbn [fact_has] in HF; try discriminate.
  - apply expr_cand_has; assumption.
  - apply expr_cand_has; assumption.
  - destruct (expr_has v (a_base a1)) eqn:E1; [apply expr_cand_has; assumption|apply expr_cand_mono].
    destruct (expr_has v n1) eqn:E2; [apply expr_cand_has; assumption|apply expr_cand_mono].
    destruct (expr_has v (a_base a2)) eqn:E3; [apply expr_cand_has; assumption|apply expr_cand_mono]. apply expr_cand_has; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint expr_all_live_u (nx0 : nat) (U : list bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else if bm_get U n then false else true
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_u nx0 U x then expr_all_live_u nx0 U y else false
  | EExt _ _ _ x => expr_all_live_u nx0 U x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_f (nx0 : nat) (spb : expr) (spk : Z) (U : list bool) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => if expr_eqbF b spb then (if Z.leb (k + Z.of_nat w) spk then false else true) else true
  | KZero (SA b k) (ELit n) | KBlob (SA b k) (ELit n) _ | KFill (SA b k) (ELit n) _ | KUnk (SA b k) (ELit n) =>
      if expr_eqbF b spb then (if Z.leb (k + n) spk then false else true) else true
  | KRange e _ _ | KAlign e _ => expr_all_live_u nx0 U e
  | KDisj a1 n1 a2 n2 =>
      if expr_all_live_u nx0 U (a_base a1) then if expr_all_live_u nx0 U n1 then if expr_all_live_u nx0 U (a_base a2) then expr_all_live_u nx0 U n2 else false else false else false
  | _ => true
  end.
Definition cs_gc_f (nx0 : nat) (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let U := unmarked cs (kn_cand nx0 (kn cs) []) in
  set_kn cs (List.filter (kn_gc_entry_f nx0 spb spk U) (kn cs)).

Lemma expr_all_live_u_eq : forall nx0 C U t e,
  (forall v, bm_get U v = (bm_get C v && negb (in_live_t t v))%bool) ->
  (forall v, expr_has v e = true -> Nat.ltb v nx0 = false -> bm_get C v = true) ->
  expr_all_live_u nx0 U e = expr_all_live_t nx0 t e.
Proof.
  intros nx0 C U t e HU. induction e; intros HC; cbn [expr_all_live_u expr_all_live_t]; try reflexivity.
  - destruct (Nat.ltb n nx0) eqn:L; [reflexivity|]. rewrite HU, (HC n); [|cbn [expr_has]; apply Nat.eqb_refl|exact L].
    destruct (in_live_t t n); reflexivity.
  - rewrite IHe1 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; reflexivity|exact L]).
    rewrite IHe2 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; destruct (expr_has v e1); reflexivity|exact L]). reflexivity.
  - rewrite IHe1 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; reflexivity|exact L]).
    rewrite IHe2 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; destruct (expr_has v e1); reflexivity|exact L]). reflexivity.
  - rewrite IHe1 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; reflexivity|exact L]).
    rewrite IHe2 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; destruct (expr_has v e1); reflexivity|exact L]). reflexivity.
  - rewrite IHe1 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; reflexivity|exact L]).
    rewrite IHe2 by (intros v H L; apply HC; [cbn [expr_has]; rewrite H; destruct (expr_has v e1); reflexivity|exact L]). reflexivity.
  - apply IHe. exact HC.
Qed.
Lemma filter_ext_in : forall (T : Type) (f g : T -> bool) l, (forall x, In x l -> f x = g x) -> List.filter f l = List.filter g l.
Proof.
  intros T f g l H. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter]. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.
Lemma cs_gc_f_eq : forall nx0 cs, cs_gc_f nx0 cs = cs_gc nx0 cs.
Proof.
  intros nx0 cs. unfold cs_gc_f, cs_gc. destruct (split_lit (reg cs 2)) as [spb spk]. f_equal.
  set (C := kn_cand nx0 (kn cs) []). set (U := unmarked cs C). set (t := live_vars_t cs).
  assert (HU : forall v, bm_get U v = (bm_get C v && negb (in_live_t t v))%bool) by (intros v; unfold U, t; rewrite unmarked_ok, live_occ; reflexivity).
  apply filter_ext_in. intros K HK.
  assert (HC : forall v, fact_has v K = true -> Nat.ltb v nx0 = false -> bm_get C v = true) by (intros v HF L; exact (kn_cand_has nx0 (kn cs) [] K v HK HF L)).
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2|[b kk] l c|[b kk] l]; cbn [kn_gc_entry_f kn_gc_entry_t]; try reflexivity.
  - rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + Z.of_nat w) spk); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
  - apply (expr_all_live_u_eq nx0 C U t e HU). exact HC.
  - apply (expr_all_live_u_eq nx0 C U t e HU). exact HC.
  - cbn [fact_has] in HC.
    rewrite (expr_all_live_u_eq nx0 C U t (a_base a1) HU) by (intros v H L; apply HC; [rewrite H; reflexivity|exact L]).
    rewrite (expr_all_live_u_eq nx0 C U t n1 HU) by (intros v H L; apply HC; [rewrite H; destruct (expr_has v (a_base a1)); reflexivity|exact L]).
    rewrite (expr_all_live_u_eq nx0 C U t (a_base a2) HU) by (intros v H L; apply HC; [rewrite H; destruct (expr_has v (a_base a1)), (expr_has v n1); reflexivity|exact L]).
    rewrite (expr_all_live_u_eq nx0 C U t n2 HU) by (intros v H L; apply HC; [rewrite H; destruct (expr_has v (a_base a1)), (expr_has v n1), (expr_has v (a_base a2)); reflexivity|exact L]).
    destruct (expr_all_live_t nx0 t (a_base a1)), (expr_all_live_t nx0 t n1), (expr_all_live_t nx0 t (a_base a2)), (expr_all_live_t nx0 t n2); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bm_get4 (l : list bool) (n : nat) {struct n} : bool :=
  match n with
  | S (S (S (S m))) => match l with _ :: _ :: _ :: _ :: r => bm_get4 r m | _ => false end
  | _ => bm_get l n
  end.
Lemma bm_get4_eq : forall n l, bm_get4 l n = bm_get l n.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros l.
  destruct n as [|[|[|[|m]]]]; try reflexivity.
  cbn [bm_get4]. destruct l as [|b0 [|b1 [|b2 [|b3 r]]]]; try reflexivity.
  cbn [bm_get]. apply IH. repeat constructor.
Qed.
Fixpoint expr_setv (e : expr) (L : list bool) : list bool :=
  match e with
  | ELit _ => L
  | EVar n => if bm_get4 L n then L else bm_set L n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_setv x (expr_setv y L)
  | EExt _ _ _ x => expr_setv x L
  | EBlob _ _ _ _ => L
  end.
Lemma expr_setv_ok : forall e L v, bm_get (expr_setv e L) v = (expr_has v e || bm_get L v)%bool.
Proof.
  induction e; intros L v; cbn [expr_setv expr_has]; try reflexivity.
  - rewrite bm_get4_eq. destruct (bm_get L n) eqn:E; [|apply bm_get_set].
    destruct (Nat.eqb_spec v n) as [->|NE]; [rewrite E; reflexivity|reflexivity].
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - rewrite IHe1, IHe2. destruct (expr_has v e1); reflexivity.
  - apply IHe.
Qed.
Lemma two_setv_ok : forall e1 e2 L v, bm_get (expr_setv e1 (expr_setv e2 L)) v = ((if expr_has v e1 then true else expr_has v e2) || bm_get L v)%bool.
Proof. intros. rewrite !expr_setv_ok. destruct (expr_has v e1); reflexivity. Qed.
Definition kentry_setv (L : list bool) (K : kentry) : list bool :=
  match K with
  | KWord a _ v => expr_setv (a_base a) (expr_setv v L)
  | KZero a n | KWr a n | KUnk a n => expr_setv (a_base a) (expr_setv n L)
  | KBlob a n _ | KFill a n _ => expr_setv (a_base a) (expr_setv n L)
  | _ => L
  end.
Lemma fold_setv : forall (T : Type) (g : list bool -> T -> list bool) (has : nat -> T -> bool),
  (forall x L v, bm_get (g L x) v = (has v x || bm_get L v)%bool) ->
  forall l L v, bm_get (fold_left g l L) v = (existsb (has v) l || bm_get L v)%bool.
Proof.
  intros T g has Hg l. induction l as [|x r IH]; intros L v; [reflexivity|]. cbn [fold_left existsb]. rewrite IH, Hg.
  destruct (has v x), (existsb (has v) r); reflexivity.
Qed.
Definition live_bm (cs : acs) : list bool :=
  let L := fold_left (fun L e => expr_setv e L) (s_regs (a_ss cs)) [] in
  let L := fold_left kentry_setv (kn cs) L in
  let L := fold_left (fun L m => expr_setv (am_base m) (expr_setv (am_len m) L)) (a_maps cs) L in
  let L := fold_left (fun L p => expr_setv (fst p) (expr_setv (snd p) L)) (a_vis cs) L in
  let L := fold_left (fun L p => expr_setv (fst p) (expr_setv (snd p) L)) (a_ghost cs) L in
  let L := match a_fd cs with FdFile _ l o => expr_setv l (expr_setv o L) | _ => L end in
  expr_setv (a_brk cs) L.
Lemma live_bm_ok : forall cs v, bm_get (live_bm cs) v = occ v cs.
Proof.
  intros cs v. unfold live_bm, occ. rewrite expr_setv_ok. f_equal.
  assert (FD : forall L, bm_get (match a_fd cs with FdFile _ l o => expr_setv l (expr_setv o L) | _ => L end) v = (fd_has v (a_fd cs) || bm_get L v)%bool).
  { intros L. unfold fd_has. destruct (a_fd cs); try reflexivity. apply two_setv_ok. }
  rewrite FD. f_equal.
  rewrite (fold_setv _ _ pair_has (fun p L v => two_setv_ok (fst p) (snd p) L v)). f_equal.
  rewrite (fold_setv _ _ pair_has (fun p L v => two_setv_ok (fst p) (snd p) L v)). f_equal.
  rewrite (fold_setv _ _ amap_has (fun m L v => two_setv_ok (am_base m) (am_len m) L v)). f_equal.
  rewrite (fold_setv _ _ kentry_has).
  2:{ intros K L0 v0. destruct K; cbn [kentry_setv kentry_has]; try apply two_setv_ok; reflexivity. }
  f_equal. rewrite (fold_setv _ _ expr_has (fun e L v => expr_setv_ok e L v)). rewrite bm_get_nil. apply Bool.orb_false_r.
Qed.
Fixpoint expr_all_live_b (nx0 : nat) (L : list bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else bm_get4 L n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_b nx0 L x then expr_all_live_b nx0 L y else false
  | EExt _ _ _ x => expr_all_live_b nx0 L x
  | EBlob _ _ _ _ => true
  end.
Lemma expr_all_live_b_eq : forall nx0 L t e, (forall v, bm_get L v = in_live_t t v) -> expr_all_live_b nx0 L e = expr_all_live_t nx0 t e.
Proof.
  intros nx0 L t e H. induction e; cbn [expr_all_live_b expr_all_live_t]; try reflexivity.
  - rewrite bm_get4_eq, H. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - exact IHe.
Qed.
Definition kn_gc_entry_b (nx0 : nat) (spb : expr) (spk : Z) (L : list bool) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => if expr_eqbF b spb then (if Z.leb (k + Z.of_nat w) spk then false else true) else true
  | KZero (SA b k) (ELit n) | KBlob (SA b k) (ELit n) _ | KFill (SA b k) (ELit n) _ | KUnk (SA b k) (ELit n) =>
      if expr_eqbF b spb then (if Z.leb (k + n) spk then false else true) else true
  | KRange e _ _ | KAlign e _ => expr_all_live_b nx0 L e
  | KDisj a1 n1 a2 n2 =>
      if expr_all_live_b nx0 L (a_base a1) then if expr_all_live_b nx0 L n1 then if expr_all_live_b nx0 L (a_base a2) then expr_all_live_b nx0 L n2 else false else false else false
  | _ => true
  end.
Definition cs_gc_b (nx0 : nat) (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let L := live_bm cs in
  set_kn cs (List.filter (kn_gc_entry_b nx0 spb spk L) (kn cs)).
Lemma cs_gc_b_eq : forall nx0 cs, cs_gc_b nx0 cs = cs_gc nx0 cs.
Proof.
  intros nx0 cs. unfold cs_gc_b, cs_gc. destruct (split_lit (reg cs 2)) as [spb spk]. f_equal.
  assert (HL : forall v, bm_get (live_bm cs) v = in_live_t (live_vars_t cs) v) by (intros v; rewrite live_bm_ok, live_occ; reflexivity).
  apply filter_ext_in. intros K _.
  destruct K as [[b kk] w v|[b kk] l|[b kk] l bk|lo hi|e m|e lo hi|[b kk] n|a1 n1 a2 n2|[b kk] l c|[b kk] l]; cbn [kn_gc_entry_b kn_gc_entry_t]; try reflexivity;
    rewrite ?(expr_all_live_b_eq nx0 _ _ _ HL).
  - rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + Z.of_nat w) spk); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (expr_all_live_t nx0 _ (a_base a1)), (expr_all_live_t nx0 _ n1), (expr_all_live_t nx0 _ (a_base a2)), (expr_all_live_t nx0 _ n2); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
  - destruct l; try reflexivity. rewrite expr_eqbF_eq. destruct (expr_eqb b spb), (Z.leb (kk + z) spk); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition granF (a : Z) : Z :=
  Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 (Z.div2 a))))))))))).
Lemma granF_eq : forall a, granF a = gran a.
Proof. intros a. reflexivity. Qed.
(* [comment removed for export] *)
Fixpoint pt_cons {A : Type} (k : positive) (x : A) (t : ptree (list A)) {struct k} : ptree (list A) :=
  match t with
  | PTLeaf => pt_set k [x] PTLeaf
  | PTNode l o r =>
      match k with
      | xH => PTNode l (Some (x :: match o with Some b => b | None => [] end)) r
      | xO k' => PTNode (pt_cons k' x l) o r
      | xI k' => PTNode l o (pt_cons k' x r)
      end
  end.
Lemma pt_cons_eq : forall (A : Type) (k : positive) (x : A) t,
  pt_cons k x t = pt_set k (x :: match pt_get t k with Some b => b | None => [] end) t.
Proof.
  intros A k. induction k as [k IH|k IH|]; intros x t; destruct t as [|l o r]; cbn [pt_cons pt_get pt_set]; try reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.
Definition kx_addF (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  pt_cons (kx_gkey g) x t.
Lemma kx_addF_eq : forall g x t, kx_addF g x t = kx_add g x t.
Proof. intros. unfold kx_addF, kx_add, kx_bucket. apply pt_cons_eq. Qed.
(* [comment removed for export] *)
Definition kx_ins (i : positive) (K : kentry) (g1 g2 : Z) (gr : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
  let gr1 := kx_addF g1 (i, K) gr in
  if Z.eqb g1 g2 then gr1 else kx_addF g2 (i, K) gr1.
Fixpoint kx_buildF (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
  match kn with
  | [] => ([], PTLeaf, [])
  | K :: rest =>
      let '(w0, gr, wf) := kx_buildF rest (Pos.succ i) in
      match K with
      | KWord (SA (ELit 0) kk) (S _ as w) _ =>
          let e1 := kk + Z.of_nat w - 1 in
          let g1 := granF kk in let g2 := granF e1 in
          if Z.leb (g2 - g1) 1 then (w0, kx_ins i K g1 g2 gr, wf) else ((i, K) :: w0, gr, wf)
      | _ =>
          let wf' := if kx_candf K then K :: wf else wf in
          match lit0_extent K with
          | Some (s, e) =>
              if Z.ltb s e then
                let g1 := granF s in let g2 := granF (e - 1) in
                if Z.leb (g2 - g1) 1 then (w0, kx_ins i K g1 g2 gr, wf') else ((i, K) :: w0, gr, wf')
              else ((i, K) :: w0, gr, wf')
          | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
          end
      end
  end.
Lemma kx_buildF_eq : forall l i, kx_buildF l i = kx_build l i.
Proof.
  intros l. induction l as [|K rest IH]; intros i; [reflexivity|]. cbn [kx_buildF kx_build]. rewrite IH.
  destruct (kx_build rest (Pos.succ i)) as [[w0 gr] wf].
  assert (GEN : (let wf' := if kx_candf K then K :: wf else wf in
                 match lit0_extent K with
                 | Some (s, e) =>
                     if Z.ltb s e then
                       let g1 := granF s in let g2 := granF (e - 1) in
                       if Z.leb (g2 - g1) 1 then (w0, kx_ins i K g1 g2 gr, wf') else ((i, K) :: w0, gr, wf')
                     else ((i, K) :: w0, gr, wf')
                 | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
                 end) =
                (let wf' := if kx_candf K then K :: wf else wf in
                 match lit0_extent K with
                 | Some (s, e) =>
                     if ext_fits s e then
                       let g1 := gran s in let g2 := gran (e - 1) in
                       let gr1 := kx_add g1 (i, K) gr in
                       (w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
                     else ((i, K) :: w0, gr, wf')
                 | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
                 end)).
  { cbv zeta. destruct (lit0_extent K) as [[s e]|]; [|reflexivity]. unfold ext_fits, kx_ins. change granF with gran. rewrite !kx_addF_eq.
    destruct (Z.ltb s e); [|reflexivity]. destruct (Z.leb (gran (e - 1) - gran s) 1); reflexivity. }
  destruct K as [[b kk] w v|a l|a l bk|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a l c|a l]; try exact GEN.
  destruct b as [z| | | | | | |]; try exact GEN. destruct z as [|p|p]; try exact GEN. destruct w as [|w']; [exact GEN|].
  clear GEN. cbn [kx_candf is_lit0 negb lit0_extent]. cbv zeta. unfold ext_fits, kx_ins. change granF with gran. rewrite !kx_addF_eq.
  assert (L : Z.ltb kk (kk + Z.of_nat (S w')) = true) by (apply Z.ltb_lt; lia). rewrite L.
  destruct (Z.leb (gran (kk + Z.of_nat (S w') - 1) - gran kk) 1); reflexivity.
Qed.
Definition mk_kix_f (kn : list kentry) : kix :=
  let r := kx_buildF kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
Lemma mk_kix_f_eq : forall l, mk_kix_f l = mk_kix l.
Proof. intros l. unfold mk_kix_f, mk_kix. rewrite kx_buildF_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkbc_f (fk : list kentry) : bctx :=
  let ffk := facts_of fk in
  let ri := mk_ri ffk in
  BC fk ffk (sum_factsB (BC fk ffk [] ri) fk) ri.
Lemma mkbc_f_eq : forall fk, mkbc_f fk = mkbc fk.
Proof. intros fk. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ltb4 (n b : nat) {struct b} : bool :=
  match b with
  | S (S (S (S b'))) => match n with S (S (S (S n'))) => ltb4 n' b' | _ => true end
  | _ => Nat.ltb n b
  end.
Lemma ltb4_eq : forall b n, ltb4 n b = Nat.ltb n b.
Proof.
  intros b. induction b as [b IH] using lt_wf_ind. intros n.
  destruct b as [|[|[|[|b']]]]; try reflexivity.
  destruct n as [|[|[|[|n']]]]; try reflexivity.
  cbn [ltb4]. rewrite IH by lia. reflexivity.
Qed.
Fixpoint expr_vars_ltF (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => ltb4 n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_vars_ltF b x then expr_vars_ltF b y else false
  | EExt _ _ _ x => expr_vars_ltF b x
  | EBlob _ _ _ _ => true
  end.
Lemma expr_vars_ltF_eq : forall b e, expr_vars_ltF b e = expr_vars_lt b e.
Proof.
  intros b e. induction e; cbn [expr_vars_ltF expr_vars_lt]; try reflexivity; try (rewrite IHe1, IHe2; destruct (expr_vars_lt b e1); reflexivity).
  - apply ltb4_eq.
  - exact IHe.
Qed.
Definition kentry_vars_ltF (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => if expr_vars_ltF b (a_base a) then expr_vars_ltF b v else false
  | KZero a n | KWr a n | KUnk a n => if expr_vars_ltF b (a_base a) then expr_vars_ltF b n else false
  | KBlob a n _ | KFill a n _ => if expr_vars_ltF b (a_base a) then expr_vars_ltF b n else false
  | KImg _ _ => true
  | KAlign e _ | KRange e _ _ => expr_vars_ltF b e
  | KDisj a1 n1 a2 n2 =>
      if expr_vars_ltF b (a_base a1) then if expr_vars_ltF b n1 then if expr_vars_ltF b (a_base a2) then expr_vars_ltF b n2 else false else false else false
  end.
Lemma kentry_vars_ltF_eq : forall b K, kentry_vars_ltF b K = kentry_vars_lt b K.
Proof.
  intros b K. destruct K; cbn [kentry_vars_ltF kentry_vars_lt]; unfold saddr_vars_lt; rewrite ?expr_vars_ltF_eq; try reflexivity;
    repeat match goal with |- context [expr_vars_lt b ?x] => destruct (expr_vars_lt b x); cbn [andb]; try reflexivity end.
Qed.
Fixpoint kn_vars_ltF (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => if kentry_vars_ltF b K then kn_vars_ltF b r else false end.
Lemma kn_vars_ltF_eq : forall b k, kn_vars_ltF b k = kn_vars_lt b k.
Proof. intros b k. induction k as [|K r IH]; [reflexivity|]. cbn [kn_vars_ltF kn_vars_lt]. rewrite kentry_vars_ltF_eq, IH. destruct (kentry_vars_lt b K); reflexivity. Qed.
Fixpoint sr_vars_ltF (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => if expr_vars_ltF b e then sr_vars_ltF b r else false end.
Lemma sr_vars_ltF_eq : forall b sr, sr_vars_ltF b sr = sr_vars_lt b sr.
Proof. intros b sr. induction sr as [|e r IH]; [reflexivity|]. cbn [sr_vars_ltF sr_vars_lt]. rewrite expr_vars_ltF_eq, IH. destruct (expr_vars_lt b e); reflexivity. Qed.
Definition fresh_ok_f (nx0 : nat) (cs : acs) : bool :=
  let v := nxt cs in
  if sr_vars_ltF v (s_regs (a_ss cs)) then
    if kn_vars_ltF v (kn cs) then
      (maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
       && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && Nat.leb nx0 v)%bool
    else false
  else false.
Lemma fresh_ok_f_eq : forall nx0 cs, fresh_ok_f nx0 cs = fresh_ok nx0 cs.
Proof.
  intros nx0 cs. unfold fresh_ok_f, fresh_ok. cbv zeta. rewrite sr_vars_ltF_eq, kn_vars_ltF_eq.
  destruct (sr_vars_lt (nxt cs) (s_regs (a_ss cs))); [|reflexivity]. destruct (kn_vars_lt (nxt cs) (kn cs)); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rmemo : Type := list (expr * option (Z * Z)).
Fixpoint rm_find (M : rmemo) (a : expr) : option (option (Z * Z)) :=
  match M with [] => None | (a', r) :: rest => if expr_eqbF a a' then Some r else rm_find rest a end.
Definition rm_get (bc : bctx) (M : rmemo) (a : expr) : option (Z * Z) * rmemo :=
  match rm_find M a with Some r => (r, M) | None => let r := erangeB bc a in (r, (a, r) :: M) end.
Definition MOK (bc : bctx) (M : rmemo) : Prop := forall a r, In (a, r) M -> r = erangeB bc a.
Lemma rm_get_ok : forall bc M a, MOK bc M -> fst (rm_get bc M a) = erangeB bc a /\ MOK bc (snd (rm_get bc M a)).
Proof.
  intros bc M a H. unfold rm_get.
  assert (F : forall r, rm_find M a = Some r -> r = erangeB bc a).
  { clear - H. induction M as [|[a' r'] rest IH]; intros r HF; [discriminate|]. cbn [rm_find] in HF.
    rewrite expr_eqbF_eq in HF. destruct (expr_eqb a a') eqn:E.
    - injection HF as <-. apply p_expr_eqb_eq in E. subst a'. apply H. left. reflexivity.
    - apply IH; [intros a0 r0 H0; apply H; right; exact H0|exact HF]. }
  destruct (rm_find M a) as [r|]; cbn [fst snd].
  - split; [exact (F r eq_refl)|exact H].
  - split; [reflexivity|]. intros a0 r0 [E0|H0]; [injection E0 as <- <-; reflexivity|exact (H a0 r0 H0)].
Qed.
Fixpoint lin_rangeM (bc : bctx) (M : rmemo) (c : Z) (ts : list (Z * expr)) : option (Z * Z) * rmemo :=
  match ts with
  | [] => (Some (c, c), M)
  | (k, a) :: rest =>
      let '(ra, M1) := rm_get bc M a in
      match ra with
      | Some (al, ah) =>
          let '(rr, M2) := lin_rangeM bc M1 c rest in
          (match rr with
           | Some (lo, hi) => if Z.leb 0 k then Some (lo + k * al, hi + k * ah) else Some (lo + k * ah, hi + k * al)
           | None => None
           end, M2)
      | None => (None, M1)
      end
  end.
Lemma lin_rangeM_ok : forall bc c ts M, MOK bc M ->
  fst (lin_rangeM bc M c ts) = lin_range (erangeB bc) c ts /\ MOK bc (snd (lin_rangeM bc M c ts)).
Proof.
  intros bc c ts. induction ts as [|[k a] rest IH]; intros M H; [split; [reflexivity|exact H]|].
  cbn [lin_rangeM lin_range]. destruct (rm_get_ok bc M a H) as [E1 H1]. destruct (rm_get bc M a) as [ra M1]. cbn [fst snd] in E1, H1.
  rewrite <- E1. destruct ra as [[al ah]|]; [|split; [reflexivity|exact H1]].
  destruct (IH M1 H1) as [E2 H2]. destruct (lin_rangeM bc M1 c rest) as [rr M2]. cbn [fst snd] in *. rewrite <- E2.
  split; [|exact H2]. destruct rr as [[lo hi]|]; reflexivity.
Qed.
(* [comment removed for export] *)
Definition amemo : Type := list (expr * Z).
Fixpoint am_find (A : amemo) (e : expr) : option Z :=
  match A with [] => None | (e', r) :: rest => if expr_eqbF e e' then Some r else am_find rest e end.
Definition am_get (bc : bctx) (A : amemo) (e : expr) : Z * amemo :=
  match am_find A e with Some r => (r, A) | None => let r := ealignB bc e in (r, (e, r) :: A) end.
Definition AOK (bc : bctx) (A : amemo) : Prop := forall e r, In (e, r) A -> r = ealignB bc e.
Lemma am_get_ok : forall bc A e, AOK bc A -> fst (am_get bc A e) = ealignB bc e /\ AOK bc (snd (am_get bc A e)).
Proof.
  intros bc A e H. unfold am_get.
  assert (F : forall r, am_find A e = Some r -> r = ealignB bc e).
  { clear - H. induction A as [|[e' r'] rest IH]; intros r HF; [discriminate|]. cbn [am_find] in HF.
    rewrite expr_eqbF_eq in HF. destruct (expr_eqb e e') eqn:E.
    - injection HF as <-. apply p_expr_eqb_eq in E. subst e'. apply H. left. reflexivity.
    - apply IH; [intros e0 r0 H0; apply H; right; exact H0|exact HF]. }
  destruct (am_find A e) as [r|]; cbn [fst snd].
  - split; [exact (F r eq_refl)|exact H].
  - split; [reflexivity|]. intros e0 r0 [E0|H0]; [injection E0 as <- <-; reflexivity|exact (H e0 r0 H0)].
Qed.
Definition smst : Type := (rmemo * amemo)%type.
Definition SOK (bc : bctx) (S : smst) : Prop := MOK bc (fst S) /\ AOK bc (snd S).
Definition lin_nowrapM (bc : bctx) (M : rmemo) (e : expr) : bool * rmemo :=
  let l := lin_of e in
  let '(r, M1) := lin_rangeM bc M (fst l) (snd l) in
  (match r with Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool | None => false end, M1).
Lemma lin_nowrapM_ok : forall bc e M, MOK bc M -> fst (lin_nowrapM bc M e) = lin_nowrapB bc e /\ MOK bc (snd (lin_nowrapM bc M e)).
Proof.
  intros bc e M H. unfold lin_nowrapM, lin_nowrapB. destruct (lin_rangeM_ok bc (fst (lin_of e)) (snd (lin_of e)) M H) as [E1 H1].
  destruct (lin_rangeM bc M (fst (lin_of e)) (snd (lin_of e))) as [r M1]. cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|exact H1].
Qed.
(* [comment removed for export] *)
Inductive skind := SKsrl (e : expr) (s : Z) | SKand (e : expr) (mk : Z) | SKnone.
Definition srl_kind (a : expr) : skind :=
  match a with
  | EAlu ALU_SRL e (ELit s) => SKsrl e s
  | EAlu ALU_AND e (ELit mk) => SKand e mk
  | _ => SKnone
  end.
Lemma srl_expandB_step : forall bc k a rest,
  srl_expandB bc ((k, a) :: rest) =
  let '(c, ts') := srl_expandB bc rest in
  let keep := (c, lins_e k a ts') in
  match srl_kind a with
  | SKsrl e s =>
      let m := (2 ^ ((s mod two64) mod 64))%Z in
      if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%bool then
        let q := (k / m)%Z in
        let le := lin_of e in
        if Z.leb ((s mod two64) mod 64) (ealignB bc e) then
          ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
        else
        ((c + q * fst le)%Z,
         lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
      else keep
  | SKand e mk =>
      match highmask_s mk with
      | Some s =>
          if lin_nowrapB bc e then
            let le := lin_of e in
            ((c + k * fst le)%Z,
             lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | None => keep
      end
  | SKnone => keep
  end.
Proof.
  intros bc k a rest. cbn [srl_expandB]. destruct (srl_expandB bc rest) as [c ts'].
  destruct a as [z|n|op x y|op x y|op x y|op x y|sg o w x|sg o w i]; try reflexivity.
  destruct op; try reflexivity; destruct y; reflexivity.
Qed.
Fixpoint srl_expandM (bc : bctx) (S : smst) (ts : list (Z * expr)) : (Z * list (Z * expr)) * smst :=
  match ts with
  | [] => ((0%Z, []), S)
  | (k, a) :: rest =>
      let '(r, S0) := srl_expandM bc S rest in
      let '(c, ts') := r in
      match srl_kind a with
      | SKsrl e s =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if Z.eqb (k mod m)%Z 0%Z then
            let '(nw, M1) := lin_nowrapM bc (fst S0) e in
            if nw then
              let '(al, A1) := am_get bc (snd S0) e in
              let q := (k / m)%Z in
              let le := lin_of e in
              if Z.leb ((s mod two64) mod 64) al then
                (((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)), (M1, A1))
              else
                (((c + q * fst le)%Z,
                  lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))), (M1, A1))
            else ((c, lins_e k a ts'), (M1, snd S0))
          else ((c, lins_e k a ts'), S0)
      | SKand e mk =>
          match highmask_s mk with
          | Some s =>
              let '(nw, M1) := lin_nowrapM bc (fst S0) e in
              if nw then
                let le := lin_of e in
                (((c + k * fst le)%Z,
                  lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le))), (M1, snd S0))
              else ((c, lins_e k a ts'), (M1, snd S0))
          | None => ((c, lins_e k a ts'), S0)
          end
      | SKnone => ((c, lins_e k a ts'), S0)
      end
  end.
Lemma srl_expandM_ok : forall bc ts S, SOK bc S -> fst (srl_expandM bc S ts) = srl_expandB bc ts /\ SOK bc (snd (srl_expandM bc S ts)).
Proof.
  intros bc ts. induction ts as [|[k a] rest IH]; intros S H; [split; [reflexivity|exact H]|].
  rewrite srl_expandB_step. cbn [srl_expandM]. destruct (IH S H) as [E0 H0]. destruct (srl_expandM bc S rest) as [r S0]. cbn [fst snd] in E0, H0.
  rewrite <- E0. destruct r as [c ts']. destruct H0 as [HM HA]. cbv zeta.
  destruct (srl_kind a) as [e s|e mk|]; [| |split; [reflexivity|split; assumption]].
  - destruct (Z.eqb (k mod 2 ^ ((s mod two64) mod 64)) 0); cbn [andb]; [|split; [reflexivity|split; assumption]].
    destruct (lin_nowrapM_ok bc e (fst S0) HM) as [E1 H1]. destruct (lin_nowrapM bc (fst S0) e) as [nw M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
    destruct nw; [|split; [reflexivity|split; assumption]].
    destruct (am_get_ok bc (snd S0) e HA) as [E2 H2]. destruct (am_get bc (snd S0) e) as [al A1]. cbn [fst snd] in E2, H2. rewrite <- E2.
    destruct (Z.leb ((s mod two64) mod 64) al); (split; [reflexivity|split; assumption]).
  - destruct (highmask_s mk) as [s|]; [|split; [reflexivity|split; assumption]].
    destruct (lin_nowrapM_ok bc e (fst S0) HM) as [E1 H1]. destruct (lin_nowrapM bc (fst S0) e) as [nw M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
    destruct nw; (split; [reflexivity|split; assumption]).
Qed.
Fixpoint sum_factsM (bc : bctx) (S : smst) (kn : list kentry) : list sfact * smst :=
  match kn with
  | [] => ([], S)
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsM bc S rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            let '(r, M1) := lin_rangeM bc (fst S) c ts in
            if (match r with Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool | None => false end) then
              let '(x, S2) := srl_expandM bc (M1, snd S) ts in
              let '(c2, ts2) := x in
              let '(tl, S3) := sum_factsM bc S2 rest in
              ((ts, ((lo - c)%Z, (hi - c)%Z)) ::
               (match ts2 with _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c - c2)%Z, (hi - c - c2)%Z))] | [] => [] end) ++ tl, S3)
            else sum_factsM bc (M1, snd S) rest
        | _ => sum_factsM bc S rest
        end
      end
  | _ :: rest => sum_factsM bc S rest
  end.

Lemma sum_factsM_ok : forall bc l S, SOK bc S -> fst (sum_factsM bc S l) = sum_factsB bc l /\ SOK bc (snd (sum_factsM bc S l)).
Proof.
  intros bc l. induction l as [|K rest IH]; intros S H; [split; [reflexivity|exact H]|].
  destruct K as [a w v|a n|a n bk|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [sum_factsM sum_factsB]; try exact (IH S H).
  assert (GEN : forall c ts, lin_of e = (c, ts) ->
     (let '(r, M1) := lin_rangeM bc (fst S) c ts in
      if (match r with Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool | None => false end) then
        let '(x, S2) := srl_expandM bc (M1, snd S) ts in
        let '(c2, ts2) := x in
        let '(tl, S3) := sum_factsM bc S2 rest in
        ((ts, ((lo - c)%Z, (hi - c)%Z)) ::
         (match ts2 with _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c - c2)%Z, (hi - c - c2)%Z))] | [] => [] end) ++ tl, S3)
      else sum_factsM bc (M1, snd S) rest) =
     (let '(r, M1) := lin_rangeM bc (fst S) c ts in
      if (match r with Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool | None => false end) then
        let '(x, S2) := srl_expandM bc (M1, snd S) ts in
        let '(c2, ts2) := x in
        let '(tl, S3) := sum_factsM bc S2 rest in
        ((ts, ((lo - c)%Z, (hi - c)%Z)) ::
         (match ts2 with _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c - c2)%Z, (hi - c - c2)%Z))] | [] => [] end) ++ tl, S3)
      else sum_factsM bc (M1, snd S) rest) ->
     fst (let '(r, M1) := lin_rangeM bc (fst S) c ts in
      if (match r with Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool | None => false end) then
        let '(x, S2) := srl_expandM bc (M1, snd S) ts in
        let '(c2, ts2) := x in
        let '(tl, S3) := sum_factsM bc S2 rest in
        ((ts, ((lo - c)%Z, (hi - c)%Z)) ::
         (match ts2 with _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c - c2)%Z, (hi - c - c2)%Z))] | [] => [] end) ++ tl, S3)
      else sum_factsM bc (M1, snd S) rest)
     = (if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest else sum_factsB bc rest)
     /\ SOK bc (snd (let '(r, M1) := lin_rangeM bc (fst S) c ts in
      if (match r with Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool | None => false end) then
        let '(x, S2) := srl_expandM bc (M1, snd S) ts in
        let '(c2, ts2) := x in
        let '(tl, S3) := sum_factsM bc S2 rest in
        ((ts, ((lo - c)%Z, (hi - c)%Z)) ::
         (match ts2 with _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c - c2)%Z, (hi - c - c2)%Z))] | [] => [] end) ++ tl, S3)
      else sum_factsM bc (M1, snd S) rest))).
  { intros c ts EL _. destruct H as [HM HA]. unfold fact_nowrapB. rewrite EL. cbn [fst snd].
    destruct (lin_rangeM_ok bc c ts (fst S) HM) as [E1 H1]. destruct (lin_rangeM bc (fst S) c ts) as [r M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
    destruct (match r with Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool | None => false end).
    - destruct (srl_expandM_ok bc ts (M1, snd S) (conj H1 HA)) as [E2 H2]. destruct (srl_expandM bc (M1, snd S) ts) as [x S2]. cbn [fst snd] in E2, H2.
      unfold sum_fact_xB. rewrite <- E2. destruct x as [c2 ts2].
      destruct (IH S2 H2) as [E3 H3]. destruct (sum_factsM bc S2 rest) as [tl S3]. cbn [fst snd] in *. rewrite <- E3.
      split; [|exact H3]. destruct ts2; [reflexivity|]. destruct (Z.eqb c2 0); reflexivity.
    - exact (IH (M1, snd S) (conj H1 HA)). }
  destruct e as [z|v|op x y|op x y|op x y|op x y|sg o w x|sg o w i]; try exact (IH S H);
    (destruct (lin_of _) as [c ts] eqn:EL; destruct ts as [|t1 [|t2 tr]]; try exact (IH S H); exact (GEN c _ eq_refl eq_refl)).
Qed.
(* [comment removed for export] *)
Fixpoint lset4 {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
  match n with
  | S (S (S (S m))) => match l with
                       | a :: b :: c :: d :: rest => a :: b :: c :: d :: lset4 rest m x
                       | _ => lset l n x
                       end
  | _ => lset l n x
  end.
Lemma lset4_eq : forall (A : Type) n (l : list (list A)) x, lset4 l n x = lset l n x.
Proof.
  intros A n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros l x.
  destruct n as [|[|[|[|m]]]]; try reflexivity.
  cbn [lset4]. destruct l as [|a [|b [|c [|d rest]]]]; try reflexivity.
  cbn [lset]. rewrite IH by (repeat constructor). reflexivity.
Qed.
Fixpoint mk_riF (fk : list kentry) : rindex :=
  match fk with
  | [] => RI [] []
  | K :: rest =>
      let t := mk_riF rest in
      match K with
      | KRange e' _ _ =>
          match vkey_of e' with
          | Some n => RI (lset4 (ri_vars t) n K) (ri_other t)
          | None => RI (ri_vars t) (K :: ri_other t)
          end
      | _ => t
      end
  end.
Lemma mk_riF_eq : forall fk, mk_riF fk = mk_ri fk.
Proof.
  induction fk as [|K rest IH]; [reflexivity|]. cbn [mk_riF mk_ri]. rewrite IH.
  destruct K; try reflexivity. destruct (vkey_of e); [rewrite lset4_eq|]; reflexivity.
Qed.
Definition mkbc_m (fk : list kentry) : bctx :=
  let ffk := facts_of fk in
  let ri := mk_riF ffk in
  BC fk ffk (fst (sum_factsM (BC fk ffk [] ri) ([], []) fk)) ri.
Lemma mkbc_m_eq : forall fk, mkbc_m fk = mkbc fk.
Proof.
  intros fk. unfold mkbc_m. cbv zeta. rewrite mk_riF_eq.
  assert (S0 : SOK (BC fk (facts_of fk) [] (mk_ri (facts_of fk))) ([], [])) by (split; [intros a r []|intros e r []]).
  rewrite (proj1 (sum_factsM_ok _ fk _ S0)). reflexivity.
Qed.
End BLKF.
