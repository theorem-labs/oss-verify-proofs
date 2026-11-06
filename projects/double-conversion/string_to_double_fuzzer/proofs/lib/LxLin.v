(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module LXL.

(* [comment removed for export] *)
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity) : bool_scope.
Notation "a &&& b" := (if a then b else false) (at level 40, left associativity) : bool_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sym := nat.
(* [comment removed for export] *)
Record lin := Lin { lc : Z; lt : list (sym * Z) }.

Definition valuation := sym -> Z.

Fixpoint evalt (rho : valuation) (ts : list (sym * Z)) : Z :=
  match ts with
  | [] => 0
  | (x, k) :: r => k * rho x + evalt rho r
  end.
Definition evl (rho : valuation) (l : lin) : Z := lc l + evalt rho (lt l).

Definition lconst (c : Z) : lin := Lin c [].
Definition lvar (x : sym) : lin := Lin 0 [(x, 1)].

Fixpoint tadd_go (x : sym) (k : Z) (a' : list (sym * Z)) (rec : list (sym * Z) -> list (sym * Z))
         (b : list (sym * Z)) : list (sym * Z) :=
  match b with
  | [] => (x, k) :: a'
  | (y, m) :: b' =>
      if Nat.ltb x y then (x, k) :: rec b
      else if Nat.eqb x y then
        (let s := k + m in if Z.eqb s 0 then rec b' else (x, s) :: rec b')
      else (y, m) :: tadd_go x k a' rec b'
  end.

Fixpoint tadd (a b : list (sym * Z)) {struct a} : list (sym * Z) :=
  match a with
  | [] => b
  | (x, k) :: a' => tadd_go x k a' (tadd a') b
  end.

Fixpoint tscale (k : Z) (a : list (sym * Z)) : list (sym * Z) :=
  match a with
  | [] => []
  | (x, m) :: a' => (x, k * m) :: tscale k a'
  end.

Definition ladd (a b : lin) : lin := Lin (lc a + lc b) (tadd (lt a) (lt b)).
Definition lscale (k : Z) (a : lin) : lin :=
  if Z.eqb k 0 then lconst 0 else Lin (k * lc a) (tscale k (lt a)).
Definition lneg (a : lin) : lin := lscale (-1) a.
Definition lsub (a b : lin) : lin := ladd a (lneg b).
Definition laddc (a : lin) (c : Z) : lin := Lin (lc a + c) (lt a).

Fixpoint teqb (a b : list (sym * Z)) : bool :=
  match a, b with
  | [], [] => true
  | (x, k) :: a', (y, m) :: b' => Nat.eqb x y &&& Z.eqb k m &&& teqb a' b'
  | _, _ => false
  end.
Definition leqb (a b : lin) : bool := Z.eqb (lc a) (lc b) &&& teqb (lt a) (lt b).

Definition is_const (a : lin) : option Z := match lt a with [] => Some (lc a) | _ => None end.
(* [comment removed for export] *)
Definition is_var (a : lin) : option sym :=
  match a with Lin c [(x, k)] => if Z.eqb c 0 &&& Z.eqb k 1 then Some x else None | _ => None end.

Fixpoint tsyms (a : list (sym * Z)) : list sym := match a with [] => [] | (x, _) :: r => x :: tsyms r end.
Definition lsyms (a : lin) : list sym := tsyms (lt a).

(* [comment removed for export] *)
Fixpoint tcoef (x : sym) (a : list (sym * Z)) : Z :=
  match a with [] => 0 | (y, k) :: r => if Nat.eqb x y then k else tcoef x r end.
Definition lcoef (x : sym) (a : lin) : Z := tcoef x (lt a).

(* [comment removed for export] *)
Fixpoint tsubst (f : sym -> option lin) (a : list (sym * Z)) : lin :=
  match a with
  | [] => lconst 0
  | (x, k) :: r => ladd (match f x with Some l => lscale k l | None => Lin 0 [(x, k)] end) (tsubst f r)
  end.
Definition lsubst (f : sym -> option lin) (a : lin) : lin := laddc (tsubst f (lt a)) (lc a).

(* [comment removed for export] *)
Lemma evalt_app_irrel : True. Proof. exact I. Qed.

Lemma tadd_go_sound : forall rho x k a' rec,
  (forall b, evalt rho (rec b) = evalt rho a' + evalt rho b) ->
  forall b, evalt rho (tadd_go x k a' rec b) = k * rho x + evalt rho a' + evalt rho b.
Proof.
  intros rho x k a' rec Hrec b. induction b as [|[y m] b' IHb]; cbn -[Z.add Z.mul Nat.ltb Nat.eqb Z.eqb].
  - lia.
  - destruct (Nat.ltb x y) eqn:E1.
    + cbn -[Z.add Z.mul Nat.ltb Nat.eqb Z.eqb]. rewrite Hrec. cbn -[Z.add Z.mul]. lia.
    + destruct (Nat.eqb x y) eqn:E2.
      * apply Nat.eqb_eq in E2; subst y. destruct (Z.eqb (k + m) 0) eqn:E3.
        -- apply Z.eqb_eq in E3. rewrite Hrec. nia.
        -- cbn -[Z.add Z.mul Nat.ltb Nat.eqb Z.eqb]. rewrite Hrec. nia.
      * cbn -[Z.add Z.mul Nat.ltb Nat.eqb Z.eqb]. rewrite IHb. lia.
Qed.

Lemma tadd_sound : forall rho a b, evalt rho (tadd a b) = evalt rho a + evalt rho b.
Proof.
  intros rho a. induction a as [|[x k] a' IH]; intros b; [reflexivity|].
  cbn -[Z.add Z.mul tadd_go]. rewrite (tadd_go_sound rho x k a' (tadd a') IH). cbn -[Z.add Z.mul]. lia.
Qed.

Lemma tscale_sound : forall rho k a, evalt rho (tscale k a) = k * evalt rho a.
Proof. intros rho k a; induction a as [|[x m] a' IH]; cbn -[Z.add Z.mul]; [lia|rewrite IH; lia]. Qed.

Lemma ladd_sound : forall rho a b, evl rho (ladd a b) = evl rho a + evl rho b.
Proof. intros; unfold evl, ladd; cbn -[Z.add Z.mul]. rewrite tadd_sound. lia. Qed.
Lemma lscale_sound : forall rho k a, evl rho (lscale k a) = k * evl rho a.
Proof.
  intros; unfold lscale. destruct (Z.eqb k 0) eqn:E; [apply Z.eqb_eq in E; subst; cbn; lia|].
  unfold evl; cbn -[Z.add Z.mul]. rewrite tscale_sound. lia.
Qed.
Lemma lneg_sound : forall rho a, evl rho (lneg a) = - evl rho a.
Proof. intros; unfold lneg; rewrite lscale_sound; lia. Qed.
Lemma lsub_sound : forall rho a b, evl rho (lsub a b) = evl rho a - evl rho b.
Proof. intros; unfold lsub; rewrite ladd_sound, lneg_sound; lia. Qed.
Lemma laddc_sound : forall rho a c, evl rho (laddc a c) = evl rho a + c.
Proof. intros; unfold laddc, evl; cbn -[Z.add Z.mul]; lia. Qed.
Lemma lconst_sound : forall rho c, evl rho (lconst c) = c.
Proof. intros; unfold evl, lconst; cbn -[Z.add Z.mul]. lia. Qed.
Lemma lvar_sound : forall rho x, evl rho (lvar x) = rho x.
Proof. intros; unfold evl, lvar; cbn -[Z.add Z.mul]. lia. Qed.

Lemma teqb_sound : forall a b, teqb a b = true -> a = b.
Proof.
  induction a as [|[x k] a' IH]; destruct b as [|[y m] b']; cbn; try discriminate; auto.
  intros H. apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
  apply Nat.eqb_eq in H1; apply Z.eqb_eq in H2; subst. f_equal. auto.
Qed.
Lemma leqb_sound : forall a b, leqb a b = true -> a = b.
Proof.
  intros [ca ta] [cb tb] H. unfold leqb in H; cbn in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply teqb_sound in H2. subst; reflexivity.
Qed.
Lemma leqb_eval : forall rho a b, leqb a b = true -> evl rho a = evl rho b.
Proof. intros rho a b H. apply leqb_sound in H. subst; reflexivity. Qed.

Lemma is_const_sound : forall rho a c, is_const a = Some c -> evl rho a = c.
Proof. intros rho [c0 [|t ts]] c H; cbn in H; [injection H; intros <-; unfold evl; cbn; lia|discriminate]. Qed.
Lemma is_var_sound : forall rho a x, is_var a = Some x -> evl rho a = rho x.
Proof.
  intros rho [c0 ts] x H. unfold is_var in H. destruct ts as [|[y k] [|]]; try discriminate.
  destruct (Z.eqb c0 0 &&& Z.eqb k 1) eqn:E; [|discriminate]. injection H; intros <-.
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1; apply Z.eqb_eq in E2. subst. unfold evl; cbn -[Z.add Z.mul]. lia.
Qed.

(* [comment removed for export] *)
Definition subst_ok (rho rho' : valuation) (f : sym -> option lin) : Prop :=
  forall x, match f x with Some l => rho x = evl rho' l | None => rho x = rho' x end.

Lemma tsubst_sound : forall rho rho' f a, subst_ok rho rho' f -> evl rho' (tsubst f a) = evalt rho a.
Proof.
  intros rho rho' f a Hs. induction a as [|[x k] r IH]; cbn -[Z.add Z.mul ladd lscale]; [reflexivity|].
  rewrite ladd_sound, IH. specialize (Hs x). destruct (f x) as [l|].
  - rewrite lscale_sound, <- Hs. reflexivity.
  - unfold evl at 1; cbn -[Z.add Z.mul]. rewrite Hs. lia.
Qed.
Lemma lsubst_sound : forall rho rho' f a, subst_ok rho rho' f -> evl rho' (lsubst f a) = evl rho a.
Proof. intros. unfold lsubst. rewrite laddc_sound, (tsubst_sound rho rho' f) by assumption. unfold evl. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record itv := Itv { ilo : option Z; ihi : option Z }.
Definition itop : itv := Itv None None.
Definition ipt (c : Z) : itv := Itv (Some c) (Some c).
Definition in_itv (z : Z) (i : itv) : Prop :=
  (match ilo i with Some lo => lo <= z | None => True end) /\
  (match ihi i with Some hi => z <= hi | None => True end).

Definition oadd (a b : option Z) : option Z :=
  match a, b with Some x, Some y => Some (x + y) | _, _ => None end.
Definition iadd (a b : itv) : itv := Itv (oadd (ilo a) (ilo b)) (oadd (ihi a) (ihi b)).
Definition iscale (k : Z) (a : itv) : itv :=
  if Z.ltb 0 k then Itv (option_map (Z.mul k) (ilo a)) (option_map (Z.mul k) (ihi a))
  else if Z.ltb k 0 then Itv (option_map (Z.mul k) (ihi a)) (option_map (Z.mul k) (ilo a))
  else ipt 0.
Definition imeet (a b : itv) : itv :=
  Itv (match ilo a, ilo b with Some x, Some y => Some (Z.max x y) | Some x, None => Some x | None, o => o end)
      (match ihi a, ihi b with Some x, Some y => Some (Z.min x y) | Some x, None => Some x | None, o => o end).
Definition ijoin (a b : itv) : itv :=
  Itv (match ilo a, ilo b with Some x, Some y => Some (Z.min x y) | _, _ => None end)
      (match ihi a, ihi b with Some x, Some y => Some (Z.max x y) | _, _ => None end).

Lemma iadd_sound : forall x y a b, in_itv x a -> in_itv y b -> in_itv (x + y) (iadd a b).
Proof.
  intros x y [al ah] [bl bh] [H1 H2] [H3 H4]; unfold in_itv, iadd; cbn in *.
  destruct al, bl, ah, bh; cbn; split; try exact I; lia.
Qed.
Lemma iscale_sound : forall k x a, in_itv x a -> in_itv (k * x) (iscale k a).
Proof.
  intros k x [al ah] [H1 H2]; unfold iscale, in_itv; cbn in *.
  destruct (Z.ltb 0 k) eqn:E1; [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1].
  - destruct al, ah; cbn; split; try exact I; nia.
  - destruct (Z.ltb k 0) eqn:E2; [apply Z.ltb_lt in E2|apply Z.ltb_ge in E2].
    + destruct al, ah; cbn; split; try exact I; nia.
    + assert (k = 0) by lia. subst. cbn. lia.
Qed.
Lemma imeet_sound : forall x a b, in_itv x a -> in_itv x b -> in_itv x (imeet a b).
Proof.
  intros x [al ah] [bl bh] [H1 H2] [H3 H4]; unfold in_itv, imeet; cbn in *.
  destruct al, bl, ah, bh; cbn; split; try exact I; lia.
Qed.
Definition itv_sub (a b : itv) : bool :=   (* [comment removed for export] *)
  (match ilo b with None => true | Some lb => match ilo a with Some la => Z.leb lb la | None => false end end
   &&& match ihi b with None => true | Some hb => match ihi a with Some ha => Z.leb ha hb | None => false end end)%bool.
Lemma itv_sub_sound : forall z a b, itv_sub a b = true -> in_itv z a -> in_itv z b.
Proof.
  intros z [alo ahi] [blo bhi] H [H1 H2]; unfold itv_sub in H; cbn in *.
  destruct blo as [lb|]; destruct alo as [la|]; destruct bhi as [hb|]; destruct ahi as [ha|]; cbn in *;
  repeat match goal with
  | H : (if ?c then _ else _) = true |- _ => destruct c eqn:?E; [|discriminate]
  end;
  repeat match goal with
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  end; split; cbn; try exact I; try lia; try discriminate.
Qed.
Lemma ijoin_l : forall x a b, in_itv x a -> in_itv x (ijoin a b).
Proof. intros x [al ah] [bl bh] [H1 H2]; unfold in_itv, ijoin; cbn in *; destruct al, bl, ah, bh; cbn; split; try exact I; lia. Qed.
Lemma ijoin_r : forall x a b, in_itv x b -> in_itv x (ijoin a b).
Proof. intros x [al ah] [bl bh] [H1 H2]; unfold in_itv, ijoin; cbn in *; destruct al, bl, ah, bh; cbn; split; try exact I; lia. Qed.
Lemma ipt_sound : forall c, in_itv c (ipt c).
Proof. intros; unfold in_itv, ipt; cbn; lia. Qed.
Lemma itop_sound : forall c, in_itv c itop.
Proof. intros; unfold in_itv, itop; cbn; tauto. Qed.

(* [comment removed for export] *)
Definition bmap := list (sym * itv).
Fixpoint bget (b : bmap) (x : sym) : itv :=
  match b with [] => itop | (y, i) :: r => if Nat.eqb x y then i else bget r x end.
Definition bmap_ok (rho : valuation) (b : bmap) : Prop := forall x, in_itv (rho x) (bget b x).

Fixpoint titv (b : bmap) (ts : list (sym * Z)) : itv :=
  match ts with
  | [] => ipt 0
  | (x, k) :: r => iadd (iscale k (bget b x)) (titv b r)
  end.
Definition litv (b : bmap) (l : lin) : itv := iadd (ipt (lc l)) (titv b (lt l)).

Lemma titv_sound : forall rho b ts, bmap_ok rho b -> in_itv (evalt rho ts) (titv b ts).
Proof.
  intros rho b ts Hb. induction ts as [|[x k] r IH]; cbn -[Z.add Z.mul].
  - apply ipt_sound.
  - apply iadd_sound; [apply iscale_sound; apply Hb | exact IH].
Qed.
Lemma litv_sound : forall rho b l, bmap_ok rho b -> in_itv (evl rho l) (litv b l).
Proof. intros. unfold litv, evl. apply iadd_sound; [apply ipt_sound | apply titv_sound; assumption]. Qed.

(* [comment removed for export] *)
Fixpoint vset (v : list itv) (x : nat) (i : itv) : list itv :=
  match x, v with
  | O, [] => [i]
  | O, _ :: r => i :: r
  | S x', [] => itop :: vset [] x' i
  | S x', j :: r => j :: vset r x' i
  end.
Definition vget (v : list itv) (x : sym) : itv := nth x v itop.
Definition bvec (b : bmap) : list itv := fold_right (fun p v => vset v (fst p) (snd p)) [] b.
Lemma vget_vset : forall x v y i, vget (vset v x i) y = if Nat.eqb y x then i else vget v y.
Proof.
  unfold vget. induction x as [|x IH]; intros v y i; destruct v as [|j r]; destruct y as [|y]; cbn [vset nth Nat.eqb]; try reflexivity.
  - destruct y; reflexivity.
  - rewrite IH. destruct (Nat.eqb y x); [reflexivity|]. destruct y; reflexivity.
  - apply IH.
Qed.
Lemma vget_bvec : forall b x, vget (bvec b) x = bget b x.
Proof.
  induction b as [|[y i] r IH]; intros x; [unfold vget; destruct x; reflexivity|].
  cbn [bvec fold_right fst snd bget]. fold (bvec r). rewrite vget_vset, IH. reflexivity.
Qed.
Fixpoint titvV (v : list itv) (ts : list (sym * Z)) : itv :=
  match ts with
  | [] => ipt 0
  | (x, k) :: r => iadd (iscale k (vget v x)) (titvV v r)
  end.
Definition litvV (v : list itv) (l : lin) : itv := iadd (ipt (lc l)) (titvV v (lt l)).
Lemma titvV_eq : forall b ts, titvV (bvec b) ts = titv b ts.
Proof. intros b ts. induction ts as [|[x k] r IH]; [reflexivity|]. cbn [titvV titv]. rewrite vget_bvec, IH. reflexivity. Qed.
Lemma litvV_eq : forall b l, litvV (bvec b) l = litv b l.
Proof. intros. unfold litvV, litv. rewrite titvV_eq. reflexivity. Qed.

Definition itv_nonneg (i : itv) : bool := match ilo i with Some lo => Z.leb 0 lo | None => false end.
Definition itv_neg (i : itv) : bool := match ihi i with Some hi => Z.ltb hi 0 | None => false end.
Lemma itv_nonneg_sound : forall z i, in_itv z i -> itv_nonneg i = true -> 0 <= z.
Proof. intros z [lo hi] [H1 H2] H; unfold itv_nonneg in H; cbn in *. destruct lo; [apply Z.leb_le in H; lia|discriminate]. Qed.
Lemma itv_neg_sound : forall z i, in_itv z i -> itv_neg i = true -> z < 0.
Proof. intros z [lo hi] [H1 H2] H; unfold itv_neg in H; cbn in *. destruct hi; [apply Z.ltb_lt in H; lia|discriminate]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ctx := Ctx { cfacts : list lin; cb : bmap }.
Definition ctx_ok (rho : valuation) (C : ctx) : Prop :=
  Forall (fun f => 0 <= evl rho f) (cfacts C) /\ bmap_ok rho (cb C).

Definition empty_ctx : ctx := Ctx [] [].
Lemma empty_ctx_ok : forall rho, ctx_ok rho empty_ctx.
Proof. intros; split; [constructor | intros x; apply itop_sound]. Qed.

(* [comment removed for export] *)
Definition ent_itv (C : ctx) (l : lin) : bool := itv_nonneg (litv (cb C) l).
(* [comment removed for export] *)
Fixpoint tmem (x : sym) (ts : list (sym * Z)) : bool :=
  match ts with [] => false | (y, _) :: r => (Nat.eqb x y ||| tmem x r) end.
Fixpoint tshare (a b : list (sym * Z)) : bool :=
  match a with [] => false | (x, _) :: r => (tmem x b ||| tshare r b) end.
Definition lshare (a b : lin) : bool := tshare (lt a) (lt b).
(* [comment removed for export] *)
Definition ent_fact1V (v : list itv) (fs : list lin) (l : lin) : bool :=
  existsb (fun f => lshare f l &&& (leqb f l ||| itv_nonneg (litvV v (lsub l f)))) fs.
Definition ent_fact1 (C : ctx) (l : lin) : bool := ent_fact1V (bvec (cb C)) (cfacts C) l.
(* [comment removed for export] *)
Definition ent_fact2V (v : list itv) (fs : list lin) (l : lin) : bool :=
  existsb (fun f => lshare f l &&&
     let lf := lsub l f in
     existsb (fun g => lshare g lf &&& itv_nonneg (litvV v (lsub lf g))) fs) fs.
Definition ent_fact2 (C : ctx) (l : lin) : bool := ent_fact2V (bvec (cb C)) (cfacts C) l.

(* [comment removed for export] *)
Record farkas := Farkas { fk_d : Z; fk_lams : list Z }.
Fixpoint lin_comb (lams : list Z) (fs : list lin) : lin :=
  match lams, fs with
  | k :: lr, f :: fr => if Z.leb k 0 then lin_comb lr fr else ladd (lscale k f) (lin_comb lr fr)
  | _, _ => lconst 0
  end.
Definition ent_farkas (C : ctx) (l : lin) (fk : farkas) : bool :=
  let d := fk_d fk in
  Z.ltb 0 d &&
  let rest := lsub (lscale d l) (lin_comb (fk_lams fk) (cfacts C)) in
  match ilo (litv (cb C) rest) with Some lo => Z.ltb (- d) lo | None => false end.

Definition entails (C : ctx) (l : lin) (cert : option farkas) : bool :=
  ent_itv C l ||| ent_fact1 C l ||| ent_fact2 C l |||
  match cert with Some fk => ent_farkas C l fk | None => false end.

Lemma lin_comb_nonneg : forall rho lams fs,
  Forall (fun f => 0 <= evl rho f) fs -> 0 <= evl rho (lin_comb lams fs).
Proof.
  intros rho lams. induction lams as [|k lr IH]; intros fs Hfs; cbn -[ladd lscale lconst].
  - rewrite lconst_sound; lia.
  - destruct fs as [|f fr]; [rewrite lconst_sound; lia|]. inversion Hfs; subst.
    destruct (Z.leb k 0) eqn:E; [apply IH; assumption|]. apply Z.leb_gt in E.
    rewrite ladd_sound, lscale_sound. specialize (IH fr H2). nia.
Qed.

Lemma existsb_exists' : forall (A : Type) (f : A -> bool) l, existsb f l = true -> exists x, In x l /\ f x = true.
Proof. intros. apply existsb_exists. assumption. Qed.

Lemma entails_sound : forall rho C l cert, ctx_ok rho C -> entails C l cert = true -> 0 <= evl rho l.
Proof.
  intros rho C l cert [HF HB] H. unfold entails in H.
  repeat (apply orb_prop in H; destruct H as [H|H]).
  - unfold ent_itv in H. eapply itv_nonneg_sound; [apply litv_sound; exact HB | exact H].
  - unfold ent_fact1, ent_fact1V in H. apply existsb_exists in H as (f & Hin & Hf).
    pose proof (proj1 (Forall_forall _ _) HF f Hin) as Hf0. cbv beta in Hf0.
    apply andb_prop in Hf as [_ Hf].
    apply orb_prop in Hf as [Hf|Hf].
    + apply leqb_sound in Hf; subst; lia.
    + rewrite litvV_eq in Hf. pose proof (itv_nonneg_sound _ _ (litv_sound rho _ (lsub l f) HB) Hf). rewrite lsub_sound in H. lia.
  - unfold ent_fact2, ent_fact2V in H. apply existsb_exists in H as (f & Hin & Hf). apply andb_prop in Hf as [_ Hf].
    apply existsb_exists in Hf as (g & Hing & Hg). apply andb_prop in Hg as [_ Hg]. rewrite litvV_eq in Hg.
    pose proof (proj1 (Forall_forall _ _) HF f Hin). pose proof (proj1 (Forall_forall _ _) HF g Hing). cbv beta in *.
    pose proof (itv_nonneg_sound _ _ (litv_sound rho _ _ HB) Hg). rewrite !lsub_sound in H1. lia.
  - destruct cert as [fk|]; [|discriminate]. unfold ent_farkas in H.
    apply andb_prop in H as [Hd H]. apply Z.ltb_lt in Hd.
    set (rest := lsub _ _) in H.
    pose proof (litv_sound rho (cb C) rest HB) as [Hlo _].
    destruct (ilo (litv (cb C) rest)) as [lo|]; [|discriminate]. apply Z.ltb_lt in H.
    subst rest. rewrite lsub_sound, lscale_sound in Hlo.
    pose proof (lin_comb_nonneg rho (fk_lams fk) (cfacts C) HF). nia.
Qed.

(* [comment removed for export] *)
Definition decide_ge0 (C : ctx) (l : lin) : option bool :=
  if entails C l None then Some true
  else if entails C (laddc (lneg l) (-1)) None then Some false
  else None.
Lemma decide_ge0_sound : forall rho C l b, ctx_ok rho C -> decide_ge0 C l = Some b ->
  (b = true -> 0 <= evl rho l) /\ (b = false -> evl rho l < 0).
Proof.
  intros rho C l b HC H. unfold decide_ge0 in H.
  destruct (entails C l None) eqn:E1.
  - injection H; intros <-. split; [intros _; eapply entails_sound; eauto | discriminate].
  - destruct (entails C (laddc (lneg l) (-1)) None) eqn:E2; [|discriminate]. injection H; intros <-.
    split; [discriminate | intros _]. pose proof (entails_sound rho C _ None HC E2). rewrite laddc_sound, lneg_sound in H0. lia.
Qed.

(* [comment removed for export] *)
Fixpoint bset (b : bmap) (x : sym) (i : itv) : bmap :=
  match b with
  | [] => [(x, i)]
  | (y, j) :: r => if Nat.eqb x y then (x, i) :: r else (y, j) :: bset r x i
  end.
Lemma bget_bset : forall b x i y, bget (bset b x i) y = if Nat.eqb y x then i else bget b y.
Proof.
  induction b as [|[z j] r IH]; intros; cbn.
  - destruct (Nat.eqb y x); reflexivity.
  - destruct (Nat.eqb x z) eqn:E.
    + apply Nat.eqb_eq in E; subst. cbn. destruct (Nat.eqb y z); reflexivity.
    + cbn. destruct (Nat.eqb y z) eqn:E2.
      * apply Nat.eqb_eq in E2; subst. rewrite Nat.eqb_sym, E. reflexivity.
      * apply IH.
Qed.

(* [comment removed for export] *)
Definition zceil_div (a b : Z) : Z := - ((- a) / b).   (* [comment removed for export] *)
Definition refine1 (b : bmap) (l : lin) : bmap :=
  match lt l with
  | [(x, k)] =>
      if Z.ltb 0 k then bset b x (imeet (bget b x) (Itv (Some (zceil_div (- lc l) k)) None))
      else if Z.ltb k 0 then bset b x (imeet (bget b x) (Itv None (Some (lc l / (- k)))))
      else b
  | _ => b
  end.
Lemma refine1_sound : forall rho b l, bmap_ok rho b -> 0 <= evl rho l -> bmap_ok rho (refine1 b l).
Proof.
  intros rho b [c ts] Hb Hl. unfold refine1; cbn.
  destruct ts as [|[x k] [|t r]]; try exact Hb.
  unfold evl in Hl; cbn -[Z.add Z.mul] in Hl.
  destruct (Z.ltb 0 k) eqn:E1; [apply Z.ltb_lt in E1|apply Z.ltb_ge in E1].
  - intros y. rewrite bget_bset. destruct (Nat.eqb y x) eqn:E; [|apply Hb]. apply Nat.eqb_eq in E; subst.
    apply imeet_sound; [apply Hb|]. unfold in_itv; cbn. split; [|exact I].
    unfold zceil_div. assert (k * rho x >= - c) by lia.
    enough ((- - c) / k >= - rho x) by lia.
    apply Z.le_ge. apply Z.div_le_lower_bound; [lia|]. nia.
  - destruct (Z.ltb k 0) eqn:E2; [apply Z.ltb_lt in E2|exact Hb].
    intros y. rewrite bget_bset. destruct (Nat.eqb y x) eqn:E; [|apply Hb]. apply Nat.eqb_eq in E; subst.
    apply imeet_sound; [apply Hb|]. unfold in_itv; cbn. split; [exact I|].
    apply Z.div_le_lower_bound; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Definition single_sym (l : lin) : bool :=
  match lt l with [(_, k)] => negb (Z.eqb k 0) | _ => false end.
Definition contra_witnessV (v : list itv) (fs : list lin) (l : lin) : option lin :=
  match find (fun g => itv_neg (litvV v (ladd l g))) fs with
  | Some g => Some (ladd l g)
  | None => None
  end.
Definition contra_witness (fs : list lin) (b : bmap) (l : lin) : option lin := contra_witnessV (bvec b) fs l.
(* [comment removed for export] *)
Fixpoint tgcd (ts : list (sym * Z)) : Z :=
  match ts with [] => 0 | (_, k) :: r => Z.gcd k (tgcd r) end.
Fixpoint tdivg (ts : list (sym * Z)) (g : Z) : list (sym * Z) :=
  match ts with [] => [] | (x, k) :: r => (x, k / g) :: tdivg r g end.
Definition lnormg (l : lin) : lin :=
  let g := tgcd (lt l) in if Z.ltb 1 g then Lin (lc l / g) (tdivg (lt l) g) else l.
Lemma tgcd_nonneg : forall ts, 0 <= tgcd ts.
Proof. induction ts as [|[x k] r IH]; cbn; [lia | apply Z.gcd_nonneg]. Qed.
Lemma tgcd_div : forall ts x k, In (x, k) ts -> (tgcd ts | k).
Proof.
  induction ts as [|[y m] r IH]; intros x k Hin; [destruct Hin|]. cbn. destruct Hin as [E|Hin].
  - injection E; intros -> ->. apply Z.gcd_divide_l.
  - eapply Z.divide_trans; [apply Z.gcd_divide_r | apply (IH x k Hin)].
Qed.
Lemma evalt_tdivg : forall rho ts g, g <> 0 -> (forall x k, In (x, k) ts -> (g | k)) -> evalt rho ts = g * evalt rho (tdivg ts g).
Proof.
  intros rho ts g Hg. induction ts as [|[x k] r IH]; intros Hd; cbn -[Z.mul Z.div Z.add]; [lia|].
  rewrite (IH ltac:(intros x' k' H'; apply (Hd x' k'); right; exact H')).
  pose proof (Hd x k ltac:(left; reflexivity)) as Dk. pose proof (Z.mod0_divide k g Dk) as M0.
  pose proof (Z.div_mod k g Hg) as DM. rewrite M0, Z.add_0_r in DM. rewrite DM at 1. ring.
Qed.
Lemma lnormg_sound : forall rho l, 0 <= evl rho l -> 0 <= evl rho (lnormg l).
Proof.
  intros rho [c ts] H. unfold lnormg; cbn. destruct (Z.ltb 1 (tgcd ts)) eqn:E; [|exact H]. apply Z.ltb_lt in E.
  unfold evl in H |- *; cbn -[Z.add Z.mul Z.div] in H |- *.
  set (g := tgcd ts) in *.
  rewrite (evalt_tdivg rho ts g ltac:(lia) ltac:(intros x k Hin; subst g; exact (tgcd_div ts x k Hin))) in H.
  set (S' := evalt rho (tdivg ts g)) in *.
  pose proof (Z.div_mod c g ltac:(lia)) as Hc. pose proof (Z.mod_pos_bound c g ltac:(lia)) as Hm. nia.
Qed.

(* [comment removed for export] *)
Definition kx_max (b : bmap) (x : sym) (k : Z) : option Z :=
  let i := bget b x in
  if Z.ltb 0 k then option_map (Z.mul k) (ihi i) else option_map (Z.mul k) (ilo i).
Definition derive2 (b : bmap) (g : lin) (x : sym) : option lin :=
  match lt g with
  | [(u, ku); (v, kv)] =>
      if Nat.eqb u x then match kx_max b u ku with Some M => Some (Lin (lc g + M) [(v, kv)]) | None => None end
      else if Nat.eqb v x then match kx_max b v kv with Some M => Some (Lin (lc g + M) [(u, ku)]) | None => None end
      else None
  | _ => None
  end.
(* [comment removed for export] *)
Fixpoint propagate2 (fs : list lin) (b : bmap) (x : sym) : bmap :=
  match fs with
  | [] => b
  | g :: r => propagate2 r (match derive2 b g x with Some l1 => refine1 b l1 | None => b end) x
  end.
(* [comment removed for export] *)
Definition refine2 (b : bmap) (l : lin) : bmap :=
  match lt l with
  | [(u, _); (v, _)] =>
      let b1 := match derive2 b l v with Some l1 => refine1 b l1 | None => b end in
      match derive2 b1 l u with Some l2 => refine1 b1 l2 | None => b1 end
  | _ => b
  end.
Definition the_sym (l : lin) : sym := match lt l with [(x, _)] => x | _ => O end.

Definition add_fact (C : ctx) (l0 : lin) : ctx :=
  let l := lnormg l0 in
  match is_const l with
  | Some c => if Z.ltb c 0 then Ctx (l :: cfacts C) (cb C) else C
  | None =>
      let b' := refine1 (cb C) l in
      if single_sym l then Ctx (cfacts C) (propagate2 (cfacts C) b' (the_sym l))
      else
        let b'' := refine2 b' l in
        match contra_witness (cfacts C) b'' l with
        | Some w => Ctx (w :: l :: cfacts C) b''
        | None => Ctx (l :: cfacts C) b''
        end
  end.
Lemma contra_witness_sound : forall rho fs b l w,
  Forall (fun f => 0 <= evl rho f) fs -> 0 <= evl rho l -> contra_witness fs b l = Some w -> 0 <= evl rho w.
Proof.
  intros rho fs b l w HF Hl H. unfold contra_witness, contra_witnessV in H.
  destruct (find _ fs) as [g|] eqn:E; [|discriminate]. injection H; intros <-.
  apply find_some in E as [Hin _]. pose proof (proj1 (Forall_forall _ _) HF g Hin) as Hg. cbv beta in Hg. rewrite ladd_sound. lia.
Qed.
Lemma kx_max_sound : forall rho b x k M, bmap_ok rho b -> kx_max b x k = Some M -> k * rho x <= M.
Proof.
  intros rho b x k M Hb H. unfold kx_max in H. pose proof (Hb x) as [H1 H2].
  destruct (Z.ltb 0 k) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - destruct (ihi (bget b x)) as [h|]; [|discriminate]. cbn in H. injection H; intros <-. nia.
  - destruct (ilo (bget b x)) as [lo|]; [|discriminate]. cbn in H. injection H; intros <-. nia.
Qed.
Lemma derive2_sound : forall rho b g x l1, bmap_ok rho b -> 0 <= evl rho g -> derive2 b g x = Some l1 -> 0 <= evl rho l1.
Proof.
  intros rho b [c ts] x l1 Hb Hg H. unfold derive2 in H; cbn in H.
  destruct ts as [|[u ku] [|[v kv] [|t r]]]; try discriminate.
  unfold evl in Hg; cbn -[Z.add Z.mul] in Hg.
  destruct (Nat.eqb u x) eqn:Eu.
  - destruct (kx_max b u ku) as [M|] eqn:EM; [|discriminate]. injection H; intros <-.
    pose proof (kx_max_sound rho b u ku M Hb EM). unfold evl; cbn -[Z.add Z.mul]. lia.
  - destruct (Nat.eqb v x) eqn:Ev; [|discriminate].
    destruct (kx_max b v kv) as [M|] eqn:EM; [|discriminate]. injection H; intros <-.
    pose proof (kx_max_sound rho b v kv M Hb EM). unfold evl; cbn -[Z.add Z.mul]. lia.
Qed.
Lemma propagate2_sound : forall rho fs b x,
  Forall (fun f => 0 <= evl rho f) fs -> bmap_ok rho b -> bmap_ok rho (propagate2 fs b x).
Proof.
  intros rho fs. induction fs as [|g r IH]; intros b x HF Hb; cbn; [exact Hb|].
  apply Forall_cons_iff in HF as [Hg Hr]. apply IH; [exact Hr|].
  destruct (derive2 b g x) as [l1|] eqn:E; [|exact Hb].
  apply refine1_sound; [exact Hb | eapply derive2_sound; eauto].
Qed.
Lemma refine2_sound : forall rho b l, bmap_ok rho b -> 0 <= evl rho l -> bmap_ok rho (refine2 b l).
Proof.
  intros rho b l Hb Hl. unfold refine2. destruct (lt l) as [|[u ku] [|[v kv] [|t r]]]; try exact Hb.
  set (b1 := match derive2 b l v with Some l1 => refine1 b l1 | None => b end).
  assert (Hb1 : bmap_ok rho b1).
  { subst b1. destruct (derive2 b l v) as [l1|] eqn:E; [|exact Hb]. apply refine1_sound; [exact Hb | eapply derive2_sound; eauto]. }
  destruct (derive2 b1 l u) as [l2|] eqn:E2; [|exact Hb1]. apply refine1_sound; [exact Hb1 | eapply derive2_sound; eauto].
Qed.
Lemma add_fact_sound : forall rho C l, ctx_ok rho C -> 0 <= evl rho l -> ctx_ok rho (add_fact C l).
Proof.
  intros rho C l0 [HF HB] Hl0. unfold add_fact. pose proof (lnormg_sound rho l0 Hl0) as Hl. set (l := lnormg l0) in *. clearbody l.
  destruct (is_const l).
  - destruct (Z.ltb _ 0); split; cbn; [constructor| | |]; assumption.
  - destruct (single_sym l).
    { split; cbn; [assumption | apply propagate2_sound; [assumption | apply refine1_sound; assumption]]. }
    assert (HB2 : bmap_ok rho (refine2 (refine1 (cb C) l) l)) by (apply refine2_sound; [apply refine1_sound; assumption | assumption]).
    destruct (contra_witness (cfacts C) (refine2 (refine1 (cb C) l) l) l) as [w|] eqn:E.
    + split; cbn; [|exact HB2].
      constructor; [eapply contra_witness_sound; eauto|]. constructor; assumption.
    + split; cbn; [constructor; assumption | exact HB2].
Qed.

(* [comment removed for export] *)
Definition norm_step (b : bmap) (f : lin) : bmap :=
  if single_sym f then refine1 b f else refine2 b f.
Fixpoint rebound (fs : list lin) (b : bmap) : bmap :=
  match fs with [] => b | f :: r => rebound r (norm_step b f) end.
Definition ctx_norm (C : ctx) : ctx := Ctx (cfacts C) (rebound (cfacts C) (rebound (cfacts C) (cb C))).
Lemma norm_step_sound : forall rho b f, bmap_ok rho b -> 0 <= evl rho f -> bmap_ok rho (norm_step b f).
Proof. intros rho b f Hb Hf. unfold norm_step. destruct (single_sym f); [apply refine1_sound | apply refine2_sound]; assumption. Qed.
Lemma rebound_sound : forall rho fs b, Forall (fun f => 0 <= evl rho f) fs -> bmap_ok rho b -> bmap_ok rho (rebound fs b).
Proof.
  intros rho fs. induction fs as [|f r IH]; intros b HF Hb; cbn; [exact Hb|].
  apply Forall_cons_iff in HF as [Hf Hr]. apply IH; [exact Hr | apply norm_step_sound; assumption].
Qed.
Lemma ctx_norm_sound : forall rho C, ctx_ok rho C -> ctx_ok rho (ctx_norm C).
Proof.
  intros rho C [HF HB]. split; cbn; [exact HF|]. apply rebound_sound; [exact HF|]. apply rebound_sound; assumption.
Qed.

(* [comment removed for export] *)
Definition set_bound (C : ctx) (x : sym) (i : itv) : ctx := Ctx (cfacts C) (bset (cb C) x i).
Lemma set_bound_sound : forall rho C x i, ctx_ok rho C -> in_itv (rho x) i -> ctx_ok rho (set_bound C x i).
Proof.
  intros rho C x i [HF HB] Hi. split; cbn; [exact HF|].
  intros y. rewrite bget_bset. destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst; exact Hi | apply HB].
Qed.

(* [comment removed for export] *)
Definition ctx_contraV (v : list itv) (fs : list lin) : bool := existsb (fun f => itv_neg (litvV v f)) fs.
Definition ctx_contra (C : ctx) (cert : option farkas) : bool :=
  ctx_contraV (bvec (cb C)) (cfacts C)
  ||| match cert with Some fk => ent_farkas C (lconst (-1)) fk | None => false end.
Lemma ctx_contra_sound : forall rho C cert, ctx_ok rho C -> ctx_contra C cert = true -> False.
Proof.
  intros rho C cert [HF HB] H. unfold ctx_contra in H. apply orb_prop in H as [H|H].
  - unfold ctx_contraV in H. apply existsb_exists in H as (f & Hin & Hf). rewrite litvV_eq in Hf.
    pose proof (proj1 (Forall_forall _ _) HF f Hin). cbv beta in *.
    pose proof (itv_neg_sound _ _ (litv_sound rho _ f HB) Hf). lia.
  - destruct cert as [fk|]; [|discriminate].
    assert (E : entails C (lconst (-1)) (Some fk) = true).
    { unfold entails. rewrite H. destruct (ent_itv C (lconst (-1))), (ent_fact1 C (lconst (-1))), (ent_fact2 C (lconst (-1))); reflexivity. }
    pose proof (entails_sound rho C (lconst (-1)) (Some fk) (conj HF HB) E). rewrite lconst_sound in H0. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scale_of (tl tf : list (sym * Z)) : option Z :=
  match tl, tf with
  | (x, a) :: _, (y, b) :: _ =>
      if (Nat.eqb x y &&& negb (Z.eqb b 0) &&& Z.eqb (a mod b) 0)%bool then
        let k := a / b in if (negb (Z.eqb k 0) &&& teqb (tscale k tf) tl)%bool then Some k else None
      else None
  | _, _ => None
  end.
Fixpoint frange (fs : list lin) (tl : list (sym * Z)) (c : Z) (acc : itv) : itv :=
  match fs with
  | [] => acc
  | f :: r =>
      let acc' := match scale_of tl (lt f) with
                  | Some k => if Z.ltb 0 k then imeet acc (Itv (Some (c - k * lc f)) None)
                              else imeet acc (Itv None (Some (c - k * lc f)))
                  | None => acc
                  end in
      frange r tl c acc'
  end.
Definition lrange (C : ctx) (l : lin) : itv :=
  match lt l with
  | [] => litv (cb C) l
  | tl => frange (cfacts C) tl (lc l) (litv (cb C) l)
  end.
Lemma scale_of_sound : forall rho tl tf k, scale_of tl tf = Some k -> evalt rho tl = k * evalt rho tf.
Proof.
  intros rho tl tf k H. unfold scale_of in H.
  destruct tl as [|[x a] tl']; [discriminate|]. destruct tf as [|[y b] tf']; [discriminate|].
  destruct (Nat.eqb x y &&& negb (Z.eqb b 0) &&& Z.eqb (a mod b) 0)%bool; [|discriminate].
  destruct (negb (Z.eqb (a / b) 0) &&& teqb (tscale (a / b) ((y, b) :: tf')) ((x, a) :: tl'))%bool eqn:E; [|discriminate].
  injection H; intros <-. apply andb_prop in E as [_ E]. apply teqb_sound in E. rewrite <- E, tscale_sound. reflexivity.
Qed.
Lemma frange_sound : forall rho fs tl c acc v,
  Forall (fun f => 0 <= evl rho f) fs -> v = c + evalt rho tl -> in_itv v acc -> in_itv v (frange fs tl c acc).
Proof.
  intros rho fs. induction fs as [|f r IH]; intros tl c acc v HF Hv Hacc; cbn; [exact Hacc|].
  apply Forall_cons_iff in HF as [Hf Hr]. apply (IH tl c _ v Hr Hv).
  unfold evl in Hf.
  destruct (scale_of tl (lt f)) as [k|] eqn:E; [|exact Hacc].
  pose proof (scale_of_sound rho tl (lt f) k E) as Hk.
  destruct (Z.ltb_spec 0 k).
  - apply imeet_sound; [exact Hacc|]. unfold in_itv; cbn. split; [nia | exact I].
  - apply imeet_sound; [exact Hacc|]. unfold in_itv; cbn. split; [exact I | nia].
Qed.
Lemma lrange_ok : forall rho C l, ctx_ok rho C -> in_itv (evl rho l) (lrange C l).
Proof.
  intros rho C l [HF HB]. unfold lrange. pose proof (litv_sound rho (cb C) l HB) as HL.
  destruct (lt l) as [|t r] eqn:El; [exact HL|].
  apply (frange_sound rho); [exact HF | unfold evl; rewrite El; reflexivity | exact HL].
Qed.
Definition two64 : Z := 18446744073709551616.
Definition two63 : Z := 9223372036854775808.
Definition two32 : Z := 4294967296.
Definition two31 : Z := 2147483648.
Definition itv_within (i : itv) (lo hi : Z) : bool :=   (* [comment removed for export] *)
  match ilo i, ihi i with Some a, Some b => Z.leb lo a &&& Z.ltb b hi | _, _ => false end.
Lemma itv_within_sound : forall z i lo hi, in_itv z i -> itv_within i lo hi = true -> lo <= z < hi.
Proof.
  intros z [a b] lo hi [H1 H2] H; unfold itv_within in H; cbn in *.
  destruct a, b; try discriminate. apply andb_prop in H as [Ha Hb]. apply Z.leb_le in Ha; apply Z.ltb_lt in Hb. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition entails12 (C : ctx) (l : lin) : bool := ent_itv C l ||| ent_fact1 C l.
Lemma entails12_sound : forall rho C l, ctx_ok rho C -> entails12 C l = true -> 0 <= evl rho l.
Proof.
  intros rho C l HC H. apply (entails_sound rho C l None HC). unfold entails, entails12 in *.
  destruct (ent_itv C l); [reflexivity|]. destruct (ent_fact1 C l); [reflexivity | discriminate].
Qed.
Definition in_range (C : ctx) (l : lin) (lo hi : Z) : bool :=   (* [comment removed for export] *)
  itv_within (lrange C l) lo hi
  ||| (entails12 C (laddc l (- lo)) &&& entails12 C (laddc (lneg l) (hi - 1))).
Lemma in_range_sound : forall rho C l lo hi, ctx_ok rho C -> in_range C l lo hi = true -> lo <= evl rho l < hi.
Proof.
  intros rho C l lo hi HC H. unfold in_range in H. apply orb_prop in H as [H|H].
  - eapply itv_within_sound; [apply lrange_ok; exact HC | exact H].
  - apply andb_prop in H as [H1 H2].
    pose proof (entails12_sound rho C _ HC H1). pose proof (entails12_sound rho C _ HC H2).
    rewrite laddc_sound in H. rewrite laddc_sound, lneg_sound in H0. lia.
Qed.
Definition uexact (C : ctx) (l : lin) : bool := in_range C l 0 two64.
Definition sexact (C : ctx) (l : lin) : bool := in_range C l (- two63) two63.
Definition sexact32 (C : ctx) (l : lin) : bool := in_range C l (- two31) two31.
Definition uexact32 (C : ctx) (l : lin) : bool := in_range C l 0 two32.

(* [comment removed for export] *)
Fixpoint tdivisible (ts : list (sym * Z)) (m : Z) : bool :=
  match ts with [] => true | (_, k) :: r => (Z.eqb (k mod m) 0 &&& tdivisible r m)%bool end.
Fixpoint tdiv (ts : list (sym * Z)) (m : Z) : list (sym * Z) :=
  match ts with [] => [] | (x, k) :: r => (x, k / m) :: tdiv r m end.
Definition ldivisible (l : lin) (m : Z) : bool := (Z.eqb (lc l mod m) 0 &&& tdivisible (lt l) m)%bool.
Definition ldiv (l : lin) (m : Z) : lin := Lin (lc l / m) (tdiv (lt l) m).

End LXL.
