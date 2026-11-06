(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Definition terms := list (nat * Z).
Definition lin : Type := (Z * terms)%type.

Definition valuation := nat -> Z.

Fixpoint teval (ρ : valuation) (ts : terms) : Z :=
  match ts with
  | [] => 0
  | (x, a) :: r => a * ρ x + teval ρ r
  end.

Definition leval (ρ : valuation) (f : lin) : Z := fst f + teval ρ (snd f).

Definition lconst (c : Z) : lin := (c, []).
Definition lvar (x : nat) : lin := (0, [(x, 1)]).

(* [comment removed for export] *)
Fixpoint tadd (a : terms) : terms -> terms :=
  match a with
  | [] => fun b => b
  | (x, p) :: ra =>
      fix tadd_b (b : terms) : terms :=
        match b with
        | [] => a
        | (y, q) :: rb =>
            if Nat.ltb x y then (x, p) :: tadd ra b
            else if Nat.ltb y x then (y, q) :: tadd_b rb
            else let s := p + q in if s =? 0 then tadd ra rb else (x, s) :: tadd ra rb
        end
  end.

Definition tscale (k : Z) (ts : terms) : terms := map (fun p => (fst p, k * snd p)) ts.

Definition ladd (f g : lin) : lin := (fst f + fst g, tadd (snd f) (snd g)).
Definition lscale (k : Z) (f : lin) : lin :=
  if k =? 0 then (0, []) else (k * fst f, tscale k (snd f)).
Definition laddc (f : lin) (c : Z) : lin := (fst f + c, snd f).
Definition lsub (f g : lin) : lin := ladd f (lscale (-1) g).

Lemma teval_tadd (ρ : valuation) : forall a b, teval ρ (tadd a b) = teval ρ a + teval ρ b.
Proof.
  induction a as [|[x p] ra IH]; intros b; [reflexivity|].
  induction b as [|[y q] rb IHb]; cbn [tadd teval] in *.
  - lia.
  - destruct (Nat.ltb_spec x y) as [Hxy|Hxy].
    + cbn [teval]. rewrite IH. cbn [teval]. lia.
    + destruct (Nat.ltb_spec y x) as [Hyx|Hyx].
      * cbn [teval]. rewrite IHb. cbn [teval]. lia.
      * assert (x = y) by lia. subst y.
        destruct (Z.eqb_spec (p + q) 0) as [E|E].
        -- rewrite IH. nia.
        -- cbn [teval]. rewrite IH. lia.
Qed.

Lemma teval_tscale (ρ : valuation) (k : Z) : forall ts, teval ρ (tscale k ts) = k * teval ρ ts.
Proof. induction ts as [|[x a] r IH]; cbn [tscale map teval fst snd] in *; [lia|]. unfold tscale in IH. rewrite IH. ring. Qed.

Lemma leval_ladd (ρ : valuation) (f g : lin) : leval ρ (ladd f g) = leval ρ f + leval ρ g.
Proof. unfold leval, ladd. cbn [fst snd]. rewrite teval_tadd. ring. Qed.

Lemma leval_lscale (ρ : valuation) (k : Z) (f : lin) : leval ρ (lscale k f) = k * leval ρ f.
Proof.
  unfold leval, lscale. destruct (Z.eqb_spec k 0) as [->|Hk]; cbn [fst snd teval]; [ring|].
  rewrite teval_tscale. ring.
Qed.

Lemma leval_laddc (ρ : valuation) (f : lin) (c : Z) : leval ρ (laddc f c) = leval ρ f + c.
Proof. unfold leval, laddc. cbn [fst snd]. ring. Qed.

Lemma leval_lsub (ρ : valuation) (f g : lin) : leval ρ (lsub f g) = leval ρ f - leval ρ g.
Proof. unfold lsub. rewrite leval_ladd, leval_lscale. ring. Qed.

Lemma leval_lconst (ρ : valuation) (c : Z) : leval ρ (lconst c) = c.
Proof. unfold leval, lconst. cbn [fst snd teval]. ring. Qed.

Lemma leval_lvar (ρ : valuation) (x : nat) : leval ρ (lvar x) = ρ x.
Proof. unfold leval, lvar. cbn [fst snd teval]. ring. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint teqb (a b : terms) : bool :=
  match a, b with
  | [], [] => true
  | (x, p) :: ra, (y, q) :: rb => Nat.eqb x y && (p =? q) && teqb ra rb
  | _, _ => false
  end.

Lemma teqb_eq (a b : terms) : teqb a b = true -> a = b.
Proof.
  revert b; induction a as [|[x p] ra IH]; intros [|[y q] rb] H; cbn [teqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3].
  apply Nat.eqb_eq in H1. apply Z.eqb_eq in H3. subst. f_equal. apply IH. exact H2.
Qed.

(* [comment removed for export] *)
Definition tmult (k : Z) (g f : terms) : bool := teqb g (tscale k f).

Lemma tmult_sound (ρ : valuation) (k : Z) (g f : terms) : tmult k g f = true -> teval ρ g = k * teval ρ f.
Proof. unfold tmult. intros H. apply teqb_eq in H. subst g. apply teval_tscale. Qed.

(* [comment removed for export] *)
Definition tratio (g f : terms) : option Z :=
  match g, f with
  | (x, p) :: _, (y, q) :: _ => if negb (Nat.eqb x y) then None else if (q =? 0) then None else if (p mod q =? 0) then
                                  (let k := p / q in if tmult k g f then Some k else None) else None
  | _, _ => None
  end.

Lemma tratio_sound (ρ : valuation) (g f : terms) (k : Z) : tratio g f = Some k -> teval ρ g = k * teval ρ f.
Proof.
  unfold tratio. destruct g as [|[x p] rg]; [discriminate|]. destruct f as [|[y q] rf]; [discriminate|].
  destruct (negb (Nat.eqb x y)); [discriminate|].
  destruct (q =? 0); [discriminate|]. destruct (p mod q =? 0); [|discriminate].
  destruct (tmult (p / q) ((x, p) :: rg) ((y, q) :: rf)) eqn:E; [|discriminate].
  intros H. injection H as <-. apply tmult_sound. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record fact : Type := Fact { fc_f : lin; fc_lo : Z; fc_hi : Z }.

Definition fact_sat (ρ : valuation) (x : fact) : Prop := fc_lo x <= leval ρ (fc_f x) <= fc_hi x.

Definition store := list fact.

Definition sat (ρ : valuation) (s : store) : Prop := Forall (fact_sat ρ) s.

Definition ivl : Type := (Z * Z)%type.

Definition imeet (a b : option ivl) : option ivl :=
  match a, b with
  | None, x => x
  | x, None => x
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  end.

(* [comment removed for export] *)
Fixpoint vbound (s : store) (x : nat) : option ivl :=
  match s with
  | [] => None
  | Fact (c, [(y, a)]) lo hi :: r =>
      if (a =? 1) && Nat.eqb x y then Some (lo - c, hi - c) else vbound r x
  | _ :: r => vbound r x
  end.

(* [comment removed for export] *)
Definition iscale (a : Z) (i : ivl) : ivl :=
  if 0 <=? a then (a * fst i, a * snd i) else (a * snd i, a * fst i).

Fixpoint tbox (s : store) (ts : terms) : option ivl :=
  match ts with
  | [] => Some (0, 0)
  | (x, a) :: r =>
      match vbound s x, tbox s r with
      | Some i, Some j => let k := iscale a i in Some (fst k + fst j, snd k + snd j)
      | _, _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint trel (s : store) (c : Z) (ts : terms) : option ivl :=
  match s with
  | [] => None
  | Fact f lo hi :: r =>
      let rest := trel r c ts in
      match tratio ts (snd f) with
      | Some k =>
          (* [comment removed for export] *)
          let i := iscale k (lo - fst f, hi - fst f) in imeet (Some (c + fst i, c + snd i)) rest
      | None => rest
      end
  end.

Definition lrange0 (s : store) (g : lin) : option ivl :=
  match snd g with
  | [] => Some (fst g, fst g)
  | ts => imeet (match tbox s ts with Some i => Some (fst g + fst i, fst g + snd i) | None => None end)
                (trel s (fst g) ts)
  end.

Lemma imeet_sound (z : Z) (a b : option ivl) :
  (forall i, a = Some i -> fst i <= z <= snd i) -> (forall i, b = Some i -> fst i <= z <= snd i) ->
  forall i, imeet a b = Some i -> fst i <= z <= snd i.
Proof.
  intros Ha Hb i H. destruct a as [[l1 h1]|], b as [[l2 h2]|]; cbn [imeet] in H.
  - injection H as <-. specialize (Ha _ eq_refl). specialize (Hb _ eq_refl). cbn in *. lia.
  - apply Ha. exact H.
  - apply Hb. exact H.
  - discriminate.
Qed.

Lemma vbound_sound (ρ : valuation) (s : store) (x : nat) :
  sat ρ s -> forall i, vbound s x = Some i -> fst i <= ρ x <= snd i.
Proof.
  induction s as [|[f lo hi] r IH]; intros Hs i H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. unfold fact_sat in Hf. cbn [fc_f fc_lo fc_hi] in Hf.
  destruct f as [c ts]. cbn [vbound] in H.
  destruct ts as [|[y a] [|t r']]; try (apply IH; assumption).
  destruct (Z.eqb_spec a 1) as [->|Ha]; cbn [andb] in H; [| apply IH; assumption].
  destruct (Nat.eqb_spec x y) as [->|Hxy]; [| apply IH; assumption].
  injection H as <-. unfold leval in Hf. cbn [fst snd teval] in *. lia.
Qed.

Lemma iscale_sound (a z : Z) (i : ivl) : fst i <= z <= snd i -> fst (iscale a i) <= a * z <= snd (iscale a i).
Proof.
  intros H. unfold iscale. destruct (Z.leb_spec 0 a); cbn [fst snd]; nia.
Qed.

Lemma tbox_sound (ρ : valuation) (s : store) (ts : terms) :
  sat ρ s -> forall i, tbox s ts = Some i -> fst i <= teval ρ ts <= snd i.
Proof.
  intros Hs. induction ts as [|[x a] r IH]; intros i H; cbn [tbox teval] in *.
  - injection H as <-. cbn. lia.
  - destruct (vbound s x) as [j|] eqn:Ev; [|discriminate]. destruct (tbox s r) as [k|] eqn:Et; [|discriminate].
    injection H as <-. pose proof (vbound_sound ρ s x Hs j Ev) as Hj. pose proof (iscale_sound a (ρ x) j Hj).
    specialize (IH k eq_refl). cbn [fst snd]. lia.
Qed.

Lemma trel_sound (ρ : valuation) (s : store) (c : Z) (ts : terms) :
  sat ρ s -> forall i, trel s c ts = Some i -> fst i <= c + teval ρ ts <= snd i.
Proof.
  induction s as [|[f lo hi] r IH]; intros Hs i H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. unfold fact_sat in Hf. cbn [fc_f fc_lo fc_hi] in Hf.
  cbn [trel] in H. destruct (tratio ts (snd f)) as [k|] eqn:Er; [| apply IH; assumption].
  revert H. apply imeet_sound; [| intros j Hj; apply IH; assumption].
  intros j Hj. injection Hj as <-. rewrite (tratio_sound ρ _ _ k Er).
  assert (Hi : fst (lo - fst f, hi - fst f) <= teval ρ (snd f) <= snd (lo - fst f, hi - fst f)).
  { unfold leval in Hf. cbn [fst snd]. lia. }
  pose proof (iscale_sound k _ _ Hi). cbn [fst snd] in *. lia.
Qed.

Lemma lrange0_sound (ρ : valuation) (s : store) (g : lin) :
  sat ρ s -> forall i, lrange0 s g = Some i -> fst i <= leval ρ g <= snd i.
Proof.
  intros Hs i H. unfold lrange0, leval in *. destruct g as [c ts]. cbn [fst snd] in *.
  destruct ts as [|t r].
  - injection H as <-. cbn. lia.
  - revert H. apply imeet_sound.
    + intros j Hj. destruct (tbox s (t :: r)) as [k|] eqn:Et; [|discriminate]. injection Hj as <-.
      pose proof (tbox_sound ρ s _ Hs k Et). cbn [fst snd]. lia.
    + intros j Hj. exact (trel_sound ρ s c (t :: r) Hs j Hj).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint tcoef (ts : terms) (x : nat) : Z :=
  match ts with
  | [] => 0
  | (y, a) :: r => if Nat.eqb x y then a else tcoef r x
  end.

Definition cdiv (a b : Z) : Z := - ((- a) / b).

(* [comment removed for export] *)
Definition elim1 (s : store) (g : lin) (fc : fact) : option ivl :=
  match snd g with
  | (x, gx) :: _ =>
      let fx := tcoef (snd (fc_f fc)) x in
      if fx =? 0 then None else
      let r := lsub (lscale fx g) (lscale gx (fc_f fc)) in
      match tbox s (snd r) with
      | Some (rl, rh) =>
          let i := iscale gx (fc_lo fc, fc_hi fc) in
          let lo' := fst i + fst r + rl in
          let hi' := snd i + fst r + rh in
          if 0 <? fx then Some (cdiv lo' fx, hi' / fx) else Some (cdiv (- hi') (- fx), (- lo') / (- fx))
      | None => None
      end
  | [] => None
  end.

(* [comment removed for export] *)
Definition relational (fc : fact) : bool := match snd (fc_f fc) with _ :: _ :: _ => true | _ => false end.

Fixpoint trel2 (s0 s : store) (g : lin) : option ivl :=
  match s with
  | [] => None
  | fc :: r => if relational fc then imeet (elim1 s0 g fc) (trel2 s0 r g) else trel2 s0 r g
  end.

Definition lrange (s : store) (g : lin) : option ivl :=
  match snd g with
  | [] => Some (fst g, fst g)
  | _ => imeet (lrange0 s g) (trel2 s s g)
  end.

Lemma cdiv_le (a b z : Z) : 0 < b -> a <= b * z -> cdiv a b <= z.
Proof.
  intros Hb H. unfold cdiv. assert (- z <= (- a) / b); [|lia].
  apply Z.div_le_lower_bound; lia.
Qed.

Lemma div_ge (a b z : Z) : 0 < b -> b * z <= a -> z <= a / b.
Proof. intros Hb H. apply Z.div_le_lower_bound; lia. Qed.

Lemma elim1_sound (ρ : valuation) (s : store) (g : lin) (fc : fact) :
  sat ρ s -> fact_sat ρ fc -> forall i, elim1 s g fc = Some i -> fst i <= leval ρ g <= snd i.
Proof.
  intros Hs Hf i H. unfold elim1 in H. unfold fact_sat in Hf.
  destruct (snd g) as [|[x gx] rest]; [discriminate|].
  set (fx := tcoef (snd (fc_f fc)) x) in *.
  destruct (Z.eqb_spec fx 0) as [E0|E0]; [discriminate|].
  set (r := lsub (lscale fx g) (lscale gx (fc_f fc))) in *.
  destruct (tbox s (snd r)) as [[rl rh]|] eqn:Et; [|discriminate].
  pose proof (tbox_sound ρ s (snd r) Hs _ Et) as Hr. cbn [fst snd] in Hr.
  assert (Hrv : leval ρ r = fx * leval ρ g - gx * leval ρ (fc_f fc)).
  { unfold r. rewrite leval_lsub, !leval_lscale. ring. }
  assert (Hr2 : fst r + rl <= leval ρ r <= fst r + rh) by (unfold leval in *; lia).
  pose proof (iscale_sound gx (leval ρ (fc_f fc)) (fc_lo fc, fc_hi fc) ltac:(cbn [fst snd]; lia)) as Hi.
  set (j := iscale gx (fc_lo fc, fc_hi fc)) in *.
  assert (Hb : fst j + fst r + rl <= fx * leval ρ g <= snd j + fst r + rh) by lia.
  destruct (Z.ltb_spec 0 fx) as [Hp|Hp].
  - assert (Hlo : cdiv (fst j + fst r + rl) fx <= leval ρ g) by (apply cdiv_le; lia).
    assert (Hhi : leval ρ g <= (snd j + fst r + rh) / fx) by (apply div_ge; lia).
    injection H as <-. exact (conj Hlo Hhi).
  - assert (Hlo : cdiv (- (snd j + fst r + rh)) (- fx) <= leval ρ g) by (apply cdiv_le; nia).
    assert (Hhi : leval ρ g <= (- (fst j + fst r + rl)) / (- fx)) by (apply div_ge; nia).
    injection H as <-. exact (conj Hlo Hhi).
Qed.

Lemma trel2_sound (ρ : valuation) (s0 : store) (g : lin) :
  sat ρ s0 -> forall s, sat ρ s -> forall i, trel2 s0 s g = Some i -> fst i <= leval ρ g <= snd i.
Proof.
  intros Hs0. induction s as [|fc r IH]; intros Hs i H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. cbn [trel2] in H. destruct (relational fc); [|exact (IH Hr i H)].
  revert H. apply imeet_sound.
  - exact (elim1_sound ρ s0 g fc Hs0 Hf).
  - intros j Hj. exact (IH Hr j Hj).
Qed.

Lemma lrange_sound (ρ : valuation) (s : store) (g : lin) :
  sat ρ s -> forall i, lrange s g = Some i -> fst i <= leval ρ g <= snd i.
Proof.
  intros Hs i H. unfold lrange in H. destruct g as [c ts]. cbn [fst snd] in *.
  destruct ts as [|t r].
  - injection H as <-. unfold leval. cbn. lia.
  - revert H. apply imeet_sound.
    + exact (lrange0_sound ρ s (c, t :: r) Hs).
    + exact (trel2_sound ρ s (c, t :: r) Hs s Hs).
Qed.

(* [comment removed for export] *)
Fixpoint sadd_m (s : store) (ts : terms) (lo hi : Z) : option store :=
  match s with
  | [] => None
  | Fact (c, ts') lo' hi' :: r =>
      if teqb ts ts' then Some (Fact (0, ts) (Z.max lo (lo' - c)) (Z.min hi (hi' - c)) :: r)
      else match sadd_m r ts lo hi with
           | Some r' => Some (Fact (c, ts') lo' hi' :: r')
           | None => None
           end
  end.

Definition sadd0 (s : store) (f : lin) (lo hi : Z) : store :=
  match snd f with
  | [] => s
  | _ => match sadd_m s (snd f) (lo - fst f) (hi - fst f) with
         | Some s' => s'
         | None => Fact f lo hi :: s
         end
  end.

Lemma sadd_m_sound (ρ : valuation) (ts : terms) (lo hi : Z) :
  lo <= teval ρ ts <= hi -> forall s s', sat ρ s -> sadd_m s ts lo hi = Some s' -> sat ρ s'.
Proof.
  intros Ht. induction s as [|[[c ts'] lo' hi'] r IH]; intros s' Hs H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. unfold fact_sat in Hf. cbn [fc_f fc_lo fc_hi] in Hf.
  cbn [sadd_m] in H. destruct (teqb ts ts') eqn:E.
  - apply teqb_eq in E. subst ts'. injection H as <-. constructor; [|exact Hr].
    unfold fact_sat, leval in *. cbn [fc_f fc_lo fc_hi fst snd] in *. lia.
  - destruct (sadd_m r ts lo hi) as [r'|] eqn:E2; [|discriminate]. injection H as <-.
    constructor; [exact Hf | exact (IH r' Hr eq_refl)].
Qed.

Lemma sat_sadd0 (ρ : valuation) (s : store) (f : lin) (lo hi : Z) :
  sat ρ s -> lo <= leval ρ f <= hi -> sat ρ (sadd0 s f lo hi).
Proof.
  intros Hs Hf. unfold sadd0. destruct (snd f) as [|t r] eqn:Ets; [exact Hs|].
  destruct (sadd_m s (t :: r) (lo - fst f) (hi - fst f)) as [s'|] eqn:E.
  - apply (sadd_m_sound ρ (t :: r) (lo - fst f) (hi - fst f)) with (s := s); [| exact Hs | exact E].
    unfold leval in Hf. rewrite Ets in Hf. lia.
  - constructor; [exact Hf | exact Hs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tremove (ts : terms) (x : nat) : terms := filter (fun p => negb (Nat.eqb (fst p) x)) ts.
Definition tcoefs (ts : terms) (x : nat) : Z := fold_right (fun p acc => if Nat.eqb (fst p) x then snd p + acc else acc) 0 ts.

Lemma teval_tremove (ρ : valuation) (ts : terms) (x : nat) : teval ρ ts = tcoefs ts x * ρ x + teval ρ (tremove ts x).
Proof.
  induction ts as [|[y a] r IH]; cbn [teval tremove tcoefs filter fold_right fst snd] in *; [lia|].
  unfold tremove, tcoefs in IH. destruct (Nat.eqb_spec y x) as [->|Hne]; cbn [negb teval].
  - rewrite IH. ring.
  - rewrite IH. ring.
Qed.

(* [comment removed for export] *)
Definition xbound (s : store) (f : lin) (lo hi : Z) (x : nat) : option ivl :=
  let a := tcoefs (snd f) x in
  match tbox s (tremove (snd f) x) with
  | Some (ol, oh) =>
      let l' := lo - fst f - oh in let h' := hi - fst f - ol in
      if 0 <? a then Some (cdiv l' a, h' / a)
      else if a <? 0 then Some (cdiv (- h') (- a), (- l') / (- a)) else None
  | None => None
  end.

Lemma xbound_sound (ρ : valuation) (s : store) (f : lin) (lo hi : Z) (x : nat) :
  sat ρ s -> lo <= leval ρ f <= hi -> forall i, xbound s f lo hi x = Some i -> fst i <= ρ x <= snd i.
Proof.
  intros Hs Hf i H. unfold xbound in H. set (a := tcoefs (snd f) x) in *.
  destruct (tbox s (tremove (snd f) x)) as [[ol oh]|] eqn:Et; [|discriminate].
  pose proof (tbox_sound ρ s _ Hs _ Et) as Hb. cbn [fst snd] in Hb.
  assert (He : leval ρ f = fst f + a * ρ x + teval ρ (tremove (snd f) x)) by (unfold leval; rewrite (teval_tremove ρ (snd f) x); unfold a; ring).
  destruct (Z.ltb_spec 0 a) as [Hp|Hp].
  - assert (Hlo : cdiv (lo - fst f - oh) a <= ρ x) by (apply cdiv_le; lia).
    assert (Hhi : ρ x <= (hi - fst f - ol) / a) by (apply div_ge; lia).
    injection H as <-. exact (conj Hlo Hhi).
  - destruct (Z.ltb_spec a 0) as [Hn|Hn]; [|discriminate].
    assert (Hlo : cdiv (- (hi - fst f - ol)) (- a) <= ρ x) by (apply cdiv_le; nia).
    assert (Hhi : ρ x <= (- (lo - fst f - oh)) / (- a)) by (apply div_ge; nia).
    injection H as <-. exact (conj Hlo Hhi).
Qed.

Fixpoint sprop (s : store) (f : lin) (lo hi : Z) (ts : terms) : store :=
  match ts with
  | [] => s
  | (x, _) :: r =>
      let s' := match xbound s f lo hi x with Some (xl, xh) => sadd0 s (lvar x) xl xh | None => s end in
      sprop s' f lo hi r
  end.

Lemma sprop_sound (ρ : valuation) (f : lin) (lo hi : Z) : lo <= leval ρ f <= hi ->
  forall ts s, sat ρ s -> sat ρ (sprop s f lo hi ts).
Proof.
  intros Hf. induction ts as [|[x a] r IH]; intros s Hs; cbn [sprop]; [exact Hs|].
  apply IH. destruct (xbound s f lo hi x) as [[xl xh]|] eqn:E; [|exact Hs].
  apply sat_sadd0; [exact Hs|]. rewrite leval_lvar. exact (xbound_sound ρ s f lo hi x Hs Hf _ E).
Qed.

(* [comment removed for export] *)
Definition sadd (s : store) (f : lin) (lo hi : Z) : store := sprop (sadd0 s f lo hi) f lo hi (snd f).

Lemma sat_sadd (ρ : valuation) (s : store) (f : lin) (lo hi : Z) :
  sat ρ s -> lo <= leval ρ f <= hi -> sat ρ (sadd s f lo hi).
Proof. intros Hs Hf. unfold sadd. apply sprop_sound; [exact Hf|]. apply sat_sadd0; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint pick1 (ts : terms) : option (nat * Z) :=
  match ts with
  | [] => None
  | (x, a) :: r => match pick1 r with Some p => Some p | None => if (a =? 1) || (a =? -1) then Some (x, a) else None end
  end.

Lemma pick1_spec (ts : terms) (x : nat) (a : Z) : pick1 ts = Some (x, a) -> a = 1 \/ a = -1.
Proof.
  induction ts as [|[y b] r IH]; cbn [pick1]; [discriminate|].
  destruct (pick1 r) as [p|] eqn:E; [intros H; injection H as Hp; subst p; exact (IH eq_refl)|].
  destruct ((b =? 1) || (b =? -1)) eqn:Eb; [|discriminate]. intros H. injection H as <- <-.
  apply orb_prop in Eb as [Eb|Eb]; apply Z.eqb_eq in Eb; [left | right]; exact Eb.
Qed.

(* [comment removed for export] *)
Definition subst1 (f : lin) (fc : fact) : lin :=
  if fc_lo fc =? fc_hi fc then
    match pick1 (snd (fc_f fc)) with
    | Some (x, a) =>
        let k := tcoefs (snd f) x in
        if k =? 0 then f else lsub f (lscale (k * a) (laddc (fc_f fc) (- fc_lo fc)))
    | None => f
    end
  else f.

Lemma subst1_sound (ρ : valuation) (f : lin) (fc : fact) : fact_sat ρ fc -> leval ρ (subst1 f fc) = leval ρ f.
Proof.
  intros Hf. unfold subst1, fact_sat in *. destruct (Z.eqb_spec (fc_lo fc) (fc_hi fc)) as [E|E]; [|reflexivity].
  destruct (pick1 (snd (fc_f fc))) as [[x a]|]; [|reflexivity].
  destruct (tcoefs (snd f) x =? 0); [reflexivity|].
  rewrite leval_lsub, leval_lscale, leval_laddc. assert (leval ρ (fc_f fc) = fc_lo fc) by lia. rewrite H. ring.
Qed.

Definition lnorm (s : store) (f : lin) : lin := fold_left subst1 s f.

Lemma lnorm_sound (ρ : valuation) (s : store) (f : lin) : sat ρ s -> leval ρ (lnorm s f) = leval ρ f.
Proof.
  unfold lnorm. revert f. induction s as [|fc r IH]; intros f Hs; cbn [fold_left]; [reflexivity|].
  inversion Hs as [|? ? Hfc Hr]; subst. rewrite (IH _ Hr). exact (subst1_sound ρ f fc Hfc).
Qed.
