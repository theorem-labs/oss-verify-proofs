(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Znumtheory.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition box := pmap itv.

Definition box_get (B : box) (s : sym) : itv :=
  match pm_get s B with Some i => i | None => itv_top end.

Definition in_box (v : val) (B : box) : Prop :=
  forall s i, pm_get s B = Some i -> in_itv (v s) i.

Lemma in_box_get v B s : in_box v B -> in_itv (v s) (box_get B s).
Proof.
  intros H. unfold box_get. destruct (pm_get s B) eqn:E.
  - exact (H _ _ E).
  - apply in_itv_top.
Qed.

Lemma in_box_empty v : in_box v pm_empty.
Proof. intros s i H. rewrite pm_get_empty in H. discriminate. Qed.

Lemma in_box_set v B s i :
  in_box v B -> in_itv (v s) i -> in_box v (pm_set s i B).
Proof.
  intros HB Hi s' i'. rewrite pm_get_set. destruct (Pos.eqb_spec s' s).
  - intros E; inversion E; subst; auto.
  - apply HB.
Qed.

Lemma in_box_remove v B s : in_box v B -> in_box v (pm_remove s B).
Proof.
  intros HB s' i'. rewrite pm_get_remove. destruct (Pos.eqb s' s); [discriminate|apply HB].
Qed.

(* [comment removed for export] *)
Fixpoint terms_range (B : box) (l : list term) (acc : itv) : itv :=
  match l with
  | [] => acc
  | (s, k) :: t => terms_range B t (itv_add acc (itv_scale k (box_get B s)))
  end.

Definition lin_range (B : box) (a : lin) : itv := terms_range B (lt a) (itv_const (lc a)).

Lemma terms_range_sound v B l : forall acc x,
  in_box v B -> in_itv x acc -> in_itv (x + eval_terms v l) (terms_range B l acc).
Proof.
  induction l as [|[s k] t IH]; intros acc x HB Hx; simpl.
  - replace (x + 0) with x by lia. exact Hx.
  - replace (x + (k * v s + eval_terms v t)) with ((x + k * v s) + eval_terms v t) by lia.
    apply IH; auto. apply in_itv_add; auto. apply in_itv_scale. now apply in_box_get.
Qed.

Lemma lin_range_sound v B a : in_box v B -> in_itv (eval v a) (lin_range B a).
Proof.
  intros HB. unfold lin_range, eval. apply terms_range_sound; auto. apply in_itv_const.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cong := pmap (Z * Z).

Definition in_cong (v : val) (C : cong) : Prop :=
  forall s m r, pm_get s C = Some (m, r) -> (m | v s - r).

Lemma in_cong_empty v : in_cong v pm_empty.
Proof. intros s m r H. rewrite pm_get_empty in H. discriminate. Qed.

Definition cong_get (C : cong) (s : sym) : Z * Z :=
  match pm_get s C with Some mr => mr | None => (1, 0) end.

Lemma in_cong_get v C s : in_cong v C -> (fst (cong_get C s) | v s - snd (cong_get C s)).
Proof.
  intros H. unfold cong_get. destruct (pm_get s C) as [[m r]|] eqn:E; simpl.
  - exact (H _ _ _ E).
  - exists (v s - 0). lia.
Qed.

Lemma in_cong_set v C s m r :
  in_cong v C -> (m | v s - r) -> in_cong v (pm_set s (m, r) C).
Proof.
  intros HC Hs s' m' r'. rewrite pm_get_set. destruct (Pos.eqb_spec s' s).
  - intros E; inversion E; subst; auto.
  - apply HC.
Qed.

Lemma in_cong_remove v C s : in_cong v C -> in_cong v (pm_remove s C).
Proof.
  intros HC s' m' r'. rewrite pm_get_remove. destruct (Pos.eqb s' s); [discriminate|apply HC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record store := mkStore { sbox : box ; scons : list lin ; scong : cong }.

Definition store_top : store := mkStore pm_empty [] pm_empty.

Definition sat (v : val) (S : store) : Prop :=
  in_box v (sbox S) /\ Forall (fun c => eval v c <= 0) (scons S) /\ in_cong v (scong S).

Lemma sat_top v : sat v store_top.
Proof. split; [|split]. apply in_box_empty. constructor. apply in_cong_empty. Qed.

Lemma sat_box v S : sat v S -> in_box v (sbox S).
Proof. intros [H _]; exact H. Qed.
Lemma sat_cons v S : sat v S -> Forall (fun c => eval v c <= 0) (scons S).
Proof. intros [_ [H _]]; exact H. Qed.
Lemma sat_cons_in v S c : sat v S -> In c (scons S) -> eval v c <= 0.
Proof. intros HS Hin. apply sat_cons in HS. rewrite Forall_forall in HS. auto. Qed.
Lemma sat_cong v S : sat v S -> in_cong v (scong S).
Proof. intros [_ [_ H]]; exact H. Qed.
Lemma sat_range v S a : sat v S -> in_itv (eval v a) (lin_range (sbox S) a).
Proof. intros HS. apply lin_range_sound. now apply sat_box. Qed.

Definition store_get_box (S : store) (s : sym) : itv := box_get (sbox S) s.

(* [comment removed for export] *)
Definition store_set_box (S : store) (s : sym) (i : itv) : store :=
  mkStore (pm_set s i (sbox S)) (scons S) (scong S).

Lemma sat_set_box v S s i : sat v S -> in_itv (v s) i -> sat v (store_set_box S s i).
Proof.
  intros [HB [HC HG]] Hi. (split; [|split]); simpl; auto. now apply in_box_set.
Qed.

(* [comment removed for export] *)
Definition store_meet_box (S : store) (s : sym) (i : itv) : option store :=
  let nb := itv_meet (store_get_box S s) i in
  if itv_empty nb then None else Some (store_set_box S s nb).

Lemma sat_meet_box v S s i :
  sat v S -> in_itv (v s) i ->
  exists S', store_meet_box S s i = Some S' /\ sat v S'.
Proof.
  intros HS Hi. unfold store_meet_box.
  assert (Hm : in_itv (v s) (itv_meet (store_get_box S s) i)).
  { apply in_itv_meet; auto. apply in_box_get. now apply sat_box. }
  destruct (itv_empty _) eqn:E.
  - exfalso. exact (itv_empty_sound _ _ E Hm).
  - eexists; split; [reflexivity|]. now apply sat_set_box.
Qed.

(* [comment removed for export] *)
Definition zmod2 (x m : Z) : Z :=
  let k := Z.log2 m in
  if Z.eqb (Z.shiftl 1 k) m then Z.land x (Z.pred (Z.shiftl 1 k)) else x mod m.

Lemma zmod2_eq x m : zmod2 x m = x mod m.
Proof.
  unfold zmod2. destruct (Z.eqb_spec (Z.shiftl 1 (Z.log2 m)) m) as [E|E]; [|reflexivity].
  pose proof (Z.log2_nonneg m) as Hk.
  rewrite Z.shiftl_1_l in * by exact Hk. rewrite <- Z.ones_equiv, Z.land_ones by exact Hk. rewrite E. reflexivity.
Qed.

Definition ceil_to_class (m r lo : Z) : Z := lo + zmod2 (r - lo) m.
Definition floor_to_class (m r hi : Z) : Z := hi - zmod2 (hi - r) m.

Definition itv_tighten_cong (m r : Z) (i : itv) : itv :=
  if Z.leb m 0 then i else
  (match fst i with Some lo => Some (ceil_to_class m r lo) | None => None end,
   match snd i with Some hi => Some (floor_to_class m r hi) | None => None end).

Lemma ceil_to_class_le m r lo x : 0 < m -> (m | x - r) -> lo <= x -> ceil_to_class m r lo <= x.
Proof.
  intros Hm [q Hq] Hlo. unfold ceil_to_class. rewrite zmod2_eq.
  assert (E : x = r + q * m) by lia. subst x.
  pose proof (Z.mod_pos_bound (r - lo) m Hm) as Hb.
  set (d := (r - lo) mod m) in *.
  assert (Hd : (m | (r - lo) - d)).
  { unfold d. exists ((r - lo) / m). pose proof (Z.div_mod (r - lo) m ltac:(lia)). lia. }
  destruct Hd as [q' Hq'].
  (* [comment removed for export] *)
  assert (lo + d = r - q' * m) by lia.
  destruct (Z_lt_le_dec (q + q') 0); [|nia].
  exfalso. assert (r + q * m <= r - q' * m - m) by nia. lia.
Qed.

Lemma floor_to_class_ge m r hi x : 0 < m -> (m | x - r) -> x <= hi -> x <= floor_to_class m r hi.
Proof.
  intros Hm [q Hq] Hhi. unfold floor_to_class. rewrite zmod2_eq.
  assert (E : x = r + q * m) by lia. subst x.
  pose proof (Z.mod_pos_bound (hi - r) m Hm) as Hb.
  set (d := (hi - r) mod m) in *.
  assert (Hd : (m | (hi - r) - d)).
  { unfold d. exists ((hi - r) / m). pose proof (Z.div_mod (hi - r) m ltac:(lia)). lia. }
  destruct Hd as [q' Hq'].
  assert (hi - d = r + q' * m) by lia.
  destruct (Z_lt_le_dec (q' - q) 0); [|nia].
  exfalso. assert (r + q * m >= r + q' * m + m) by nia. lia.
Qed.

Lemma in_itv_tighten_cong m r i x :
  (m | x - r) -> in_itv x i -> in_itv x (itv_tighten_cong m r i).
Proof.
  intros Hd Hi. unfold itv_tighten_cong. destruct (Z.leb_spec m 0); [exact Hi|].
  destruct i as [[lo|] [hi|]]; destruct Hi as [H1 H2]; simpl in *; split; simpl; auto.
  - apply ceil_to_class_le; auto.
  - apply floor_to_class_ge; auto.
  - apply ceil_to_class_le; auto.
  - apply floor_to_class_ge; auto.
Qed.

(* [comment removed for export] *)
Definition obz_eqb (a b : option Z) : bool :=
  match a, b with Some x, Some y => Z.eqb x y | None, None => true | _, _ => false end.
Definition itv_eqb (a b : itv) : bool := obz_eqb (fst a) (fst b) && obz_eqb (snd a) (snd b).

(* [comment removed for export] *)
Definition round_itv (S : store) (s : sym) (i : itv) : itv :=
  match pm_get s (scong S) with
  | Some (m, r) => itv_tighten_cong m r i
  | None => i
  end.

Lemma in_round_itv v S s i : sat v S -> in_itv (v s) i -> in_itv (v s) (round_itv S s i).
Proof.
  intros HS Hi. unfold round_itv. destruct (pm_get s (scong S)) as [[m r]|] eqn:E; [|exact Hi].
  apply in_itv_tighten_cong; [|exact Hi]. exact (sat_cong v S HS _ _ _ E).
Qed.

(* [comment removed for export] *)
Definition store_meet_box_r (always : bool) (S : store) (s : sym) (i : itv) : option store :=
  let old := store_get_box S s in
  let nb := itv_meet old i in
  if negb always && itv_eqb nb old then Some S
  else let nb' := round_itv S s nb in
       if itv_empty nb' then None else Some (store_set_box S s nb').

Lemma sat_meet_box_r v al S s i :
  sat v S -> in_itv (v s) i ->
  exists S', store_meet_box_r al S s i = Some S' /\ sat v S'.
Proof.
  intros HS Hi. unfold store_meet_box_r.
  assert (Hm : in_itv (v s) (itv_meet (store_get_box S s) i)).
  { apply in_itv_meet; auto. apply in_box_get. now apply sat_box. }
  destruct (negb al && itv_eqb _ _); [eauto|].
  pose proof (in_round_itv v S s _ HS Hm) as Hr.
  destruct (itv_empty _) eqn:E.
  - exfalso. exact (itv_empty_sound _ _ E Hr).
  - eexists; split; [reflexivity|]. now apply sat_set_box.
Qed.

Definition store_add_cong (S : store) (s : sym) (m r : Z) : option store :=
  if Z.leb m 1 then (if Z.eqb m 0 then
                       (* [comment removed for export] *)
                       match store_meet_box S s (itv_const r) with
                       | None => None
                       | Some S' => Some (mkStore (sbox S') (scons S') (pm_set s (0, r) (scong S')))
                       end
                     else Some S)
  else
    let r := r mod m in
    let '(om, orr) := cong_get (scong S) s in
    if Z.eqb om 0 then (if Z.eqb (orr mod m) r then Some S else None)
    else if Z.eqb (om mod m) 0 then
      (* [comment removed for export] *)
      (if Z.eqb (orr mod m) r then Some S else None)
    else if Z.ltb 0 om && Z.eqb (m mod om) 0 then
      (* [comment removed for export] *)
      (if Z.eqb (r mod om) (orr mod om) then
         let nb := itv_tighten_cong m r (store_get_box S s) in
         if itv_empty nb then None
         else Some (mkStore (pm_set s nb (sbox S)) (scons S) (pm_set s (m, r) (scong S)))
       else None)
    else Some S (* [comment removed for export] *).

Lemma divide_mod_eq m a b : 0 < m -> (m | a - b) -> a mod m = b mod m.
Proof.
  intros Hm [q Hq]. replace a with (b + q * m) by lia.
  rewrite Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod by lia. reflexivity.
Qed.

Lemma mod_eq_divide m a b : 0 < m -> a mod m = b mod m -> (m | a - b).
Proof.
  intros Hm E.
  pose proof (Z.div_mod a m ltac:(lia)). pose proof (Z.div_mod b m ltac:(lia)).
  exists (a / m - b / m). lia.
Qed.

Lemma divide_mod_0 m k x : 0 < k -> m mod k = 0 -> (m | x) -> (k | x).
Proof.
  intros Hk E Hd. apply Z.divide_trans with m; auto.
  apply Z.mod_divide; lia.
Qed.

Lemma sat_add_cong v S s m r :
  sat v S -> (m | v s - r) ->
  exists S', store_add_cong S s m r = Some S' /\ sat v S'.
Proof.
  intros HS Hd. unfold store_add_cong.
  destruct (Z.leb_spec m 1) as [Hm1|Hm1].
  - destruct (Z.eqb_spec m 0) as [Hm0|Hm0]; [|eauto].
    subst. destruct Hd as [q Hq]. assert (Evs : v s = r) by lia.
    destruct (sat_meet_box v S s (itv_const r) HS) as [S' [E HS']].
    { rewrite Evs. apply in_itv_const. }
    rewrite E. eexists; split; [reflexivity|].
    destruct HS' as [HB [HC HG]]. (split; [|split]); simpl; auto.
    apply in_cong_set; auto. exists 0; lia.
  - pose proof (sat_cong v S HS) as HG.
    pose proof (in_cong_get v (scong S) s HG) as Hold.
    destruct (cong_get (scong S) s) as [om orr]. simpl in Hold.
    assert (Hr : (v s) mod m = (r mod m) mod m).
    { rewrite Z.mod_mod by lia. apply divide_mod_eq; auto; lia. }
    assert (Hdm : (m | v s - r mod m)).
    { apply mod_eq_divide; [lia|]. exact Hr. }
    destruct (Z.eqb_spec om 0) as [Hom0|Hom0].
    + subst. destruct Hold as [q Hq]. assert (E0 : orr = v s) by lia.
      rewrite E0, Hr, Z.mod_mod, Z.eqb_refl by lia. eauto.
    + destruct (Z.eqb_spec (om mod m) 0) as [Homm|Homm].
      * assert (Hk : (m | v s - orr)).
        { apply divide_mod_0 with om; auto; lia. }
        apply divide_mod_eq in Hk; [|lia]. rewrite <- Hk, Hr, Z.mod_mod, Z.eqb_refl by lia. eauto.
      * destruct (Z.ltb_spec 0 om) as [Hom|Hom]; simpl; [|eauto].
        destruct (Z.eqb_spec (m mod om) 0) as [Hmom|Hmom]; simpl; [|eauto].
        assert (Hk : (om | v s - r mod m)).
        { apply divide_mod_0 with m; auto. }
        assert (E1 : (r mod m) mod om = orr mod om).
        { apply divide_mod_eq in Hk; auto. apply divide_mod_eq in Hold; auto. congruence. }
        rewrite E1, Z.eqb_refl.
        assert (Ht : in_itv (v s) (itv_tighten_cong m (r mod m) (store_get_box S s))).
        { apply in_itv_tighten_cong; auto. apply in_box_get. now apply sat_box. }
        destruct (itv_empty _) eqn:E.
        -- exfalso. exact (itv_empty_sound _ _ E Ht).
        -- eexists; split; [reflexivity|].
           destruct HS as [HB [HC HG']]. (split; [|split]); simpl; auto.
           ++ now apply in_box_set.
           ++ apply in_cong_set; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zdivf (a b : Z) : Z := match b with Zpos xH => a | _ => Z.div a b end.
Lemma zdivf_eq a b : zdivf a b = a / b.
Proof. destruct b as [|[p|p|]|p]; try reflexivity. symmetry; apply Z.div_1_r. Qed.
#[global] Arguments zdivf : simpl never.

Definition ceil_div (a b : Z) : Z := - (zdivf (- a) b).   (* [comment removed for export] *)

Lemma ceil_div_spec a b x : 0 < b -> b * x >= a -> x >= ceil_div a b.
Proof.
  intros Hb H. unfold ceil_div. rewrite zdivf_eq.
  assert ((-a) / b >= - x); [|lia].
  apply Z.le_ge. apply Z.div_le_lower_bound; lia.
Qed.

Lemma floor_div_spec a b x : 0 < b -> b * x <= a -> x <= a / b.
Proof.
  intros Hb H. apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
Definition assume_single (S : store) (s : sym) (k c : Z) : option store :=
  if Z.ltb 0 k then store_meet_box_r true S s (None, Some (zdivf (- c) k))
  else if Z.ltb k 0 then store_meet_box_r true S s (Some (ceil_div c (- k)), None)
  else (if Z.leb c 0 then Some S else None).

Lemma sat_assume_single v S s k c :
  sat v S -> k * v s + c <= 0 ->
  exists S', assume_single S s k c = Some S' /\ sat v S'.
Proof.
  intros HS H. unfold assume_single.
  destruct (Z.ltb_spec 0 k).
  - apply sat_meet_box_r; auto. split; simpl; [exact I|]. rewrite zdivf_eq. apply floor_div_spec; lia.
  - destruct (Z.ltb_spec k 0).
    + apply sat_meet_box_r; auto. split; simpl; [|exact I].
      apply Z.ge_le. apply ceil_div_spec; lia.
    + assert (k = 0) by lia. subst. destruct (Z.leb_spec c 0); [eauto|lia].
Qed.

(* [comment removed for export] *)
Fixpoint terms_gcd (l : list term) : Z :=
  match l with
  | [] => 0
  | (_, k) :: t => Z.gcd k (terms_gcd t)
  end.

Fixpoint terms_divq (g : Z) (l : list term) : list term :=
  match l with
  | [] => []
  | (s, k) :: t => (s, k / g) :: terms_divq g t
  end.

Lemma terms_gcd_nonneg l : 0 <= terms_gcd l.
Proof. destruct l as [|[s k] t]; simpl; [lia|apply Z.gcd_nonneg]. Qed.

Lemma terms_divq_eval v g l :
  g <> 0 -> (forall sk, In sk l -> (g | snd sk)) ->
  g * eval_terms v (terms_divq g l) = eval_terms v l.
Proof.
  intros Hg. induction l as [|[s k] t IH]; intros Hall; simpl; [lia|].
  rewrite Z.mul_add_distr_l.
  rewrite IH by (intros; apply Hall; simpl; auto).
  assert (Hk : (g | k)) by (apply (Hall (s, k)); simpl; auto).
  destruct Hk as [q Hq]. subst k. rewrite Z.div_mul by auto. lia.
Qed.

Lemma terms_gcd_divides l : forall sk, In sk l -> (terms_gcd l | snd sk).
Proof.
  induction l as [|[s k] t IH]; intros sk Hin; simpl in *; [tauto|].
  destruct Hin as [<-|Hin]; simpl.
  - apply Z.gcd_divide_l.
  - apply Z.divide_trans with (terms_gcd t); auto. apply Z.gcd_divide_r.
Qed.

(* [comment removed for export] *)
Definition lin_normc (a : lin) : lin :=
  let g := terms_gcd (lt a) in
  if Z.leb g 1 then a else mkLin (ceil_div (lc a) g) (terms_divq g (lt a)).

Lemma lin_normc_sound v a : eval v a <= 0 -> eval v (lin_normc a) <= 0.
Proof.
  intros H. unfold lin_normc. destruct (Z.leb_spec (terms_gcd (lt a)) 1); auto.
  unfold eval in *. cbn [lc lt].
  set (g := terms_gcd (lt a)) in *.
  pose proof (terms_divq_eval v g (lt a) ltac:(lia) (terms_gcd_divides (lt a))) as E.
  set (T := eval_terms v (terms_divq g (lt a))) in *.
  assert (HT : g * T <= - lc a) by lia.
  assert (T <= (- lc a) / g) by (apply floor_div_spec; lia).
  unfold ceil_div. rewrite zdivf_eq. lia.
Qed.

Lemma lin_normc_sound_inv v a : eval v (lin_normc a) <= 0 -> eval v a <= 0.
Proof.
  unfold lin_normc. destruct (Z.leb_spec (terms_gcd (lt a)) 1); auto.
  unfold eval in *. cbn [lc lt].
  set (g := terms_gcd (lt a)) in *.
  pose proof (terms_divq_eval v g (lt a) ltac:(lia) (terms_gcd_divides (lt a))) as E.
  set (T := eval_terms v (terms_divq g (lt a))) in *. intros HT.
  unfold ceil_div in HT. rewrite zdivf_eq in HT.
  assert (Hc : g * ((- lc a) / g) <= - lc a) by (apply Z.mul_div_le; lia).
  assert (Hm : g * T <= g * ((- lc a) / g)) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

(* [comment removed for export] *)
Fixpoint terms_remove (s : sym) (l : list term) : list term :=
  match l with
  | [] => []
  | (s', k) :: t => if Pos.eqb s s' then t else (s', k) :: terms_remove s t
  end.

Lemma eval_terms_remove v s l :
  NoDup (map fst l) ->
  eval_terms v (terms_remove s l) = eval_terms v l - terms_coef l s * v s.
Proof.
  induction l as [|[s' k] t IH]; intros Hnd; simpl; [lia|].
  inversion Hnd; subst.
  destruct (Pos.eqb_spec s s').
  - subst. lia.
  - simpl. rewrite IH; auto. lia.
Qed.

(* [comment removed for export] *)
Definition tighten_one (S : store) (a : lin) (s : sym) (k : Z) : option store :=
  let rest := laxpy a (- k) (lsym s) in          (* [comment removed for export] *)
  match itv_lo (lin_range (sbox S) rest) with
  | None => Some S
  | Some rlo =>
      (* [comment removed for export] *)
      if Z.ltb 0 k then store_meet_box_r false S s (None, Some (zdivf (- rlo) k))
      else if Z.ltb k 0 then store_meet_box_r false S s (Some (ceil_div rlo (- k)), None)
      else Some S
  end.

Lemma sat_tighten_one v S a s k :
  sat v S -> eval v a <= 0 ->
  exists S', tighten_one S a s k = Some S' /\ sat v S'.
Proof.
  intros HS Ha. unfold tighten_one.
  set (rest := laxpy a (- k) (lsym s)).
  assert (Er : eval v rest = eval v a - k * v s).
  { unfold rest. rewrite eval_laxpy, eval_lsym. lia. }
  pose proof (sat_range v S rest HS) as Hr.
  destruct (lin_range (sbox S) rest) as [[rlo|] rhi]; simpl; [|eauto].
  destruct Hr as [Hlo _]. simpl in Hlo.
  destruct (Z.ltb_spec 0 k).
  - apply sat_meet_box_r; auto. split; simpl; [exact I|]. rewrite zdivf_eq. apply floor_div_spec; lia.
  - destruct (Z.ltb_spec k 0); [|eauto].
    apply sat_meet_box_r; auto. split; simpl; [|exact I].
    apply Z.ge_le. apply ceil_div_spec; lia.
Qed.

Fixpoint tighten_all (S : store) (a : lin) (l : list term) : option store :=
  match l with
  | [] => Some S
  | (s, k) :: t =>
      match tighten_one S a s k with
      | None => None
      | Some S' => tighten_all S' a t
      end
  end.

Lemma sat_tighten_all v a l : forall S,
  sat v S -> eval v a <= 0 ->
  exists S', tighten_all S a l = Some S' /\ sat v S'.
Proof.
  induction l as [|[s k] t IH]; intros S HS Ha; simpl; [eauto|].
  destruct (sat_tighten_one v S a s k HS Ha) as [S1 [E HS1]]. rewrite E.
  apply IH; auto.
Qed.

Definition lin_mem (a : lin) (l : list lin) : bool := existsb (lin_eqb a) l.

Lemma lin_mem_sound a l : lin_mem a l = true -> In a l.
Proof.
  unfold lin_mem. rewrite existsb_exists. intros [x [Hin E]].
  apply lin_eqb_eq in E. now subst.
Qed.

(* [comment removed for export] *)
Definition assume_general (S : store) (a : lin) : option store :=
  let a' := lin_normc a in
  if lin_mem a' (scons S) then Some S
  else tighten_all (mkStore (sbox S) (a' :: scons S) (scong S)) a' (lt a').

Lemma sat_assume_general v S a :
  sat v S -> eval v a <= 0 ->
  exists S', assume_general S a = Some S' /\ sat v S'.
Proof.
  intros HS Ha. unfold assume_general.
  pose proof (lin_normc_sound v a Ha) as Ha'.
  destruct (lin_mem _ _); [eauto|].
  apply sat_tighten_all; auto.
  destruct HS as [HB [HC HG]]. (split; [|split]); simpl; auto.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_assume0 (S : store) (a : lin) : option store :=
  match lt a with
  | [] => if Z.leb (lc a) 0 then Some S else None
  | [(s, k)] => assume_single S s k (lc a)
  | _ =>
      let r := lin_range (sbox S) a in
      if itv_hi_le r 0 then Some S
      else if itv_lo_ge r 1 then None
      else assume_general S a
  end.

Lemma sat_assume0 v S a :
  sat v S -> eval v a <= 0 ->
  exists S', store_assume0 S a = Some S' /\ sat v S'.
Proof.
  intros HS Ha. unfold store_assume0.
  destruct (lt a) as [|[s k] [|t2 l2]] eqn:E.
  - rewrite (eval_is_const v a) in Ha by (unfold lin_is_const; now rewrite E).
    destruct (Z.leb_spec (lc a) 0); [eauto|lia].
  - apply sat_assume_single; auto.
    rewrite (eval_single v a s k) in Ha by (unfold lin_single; now rewrite E). lia.
  - pose proof (sat_range v S a HS) as Hr.
    destruct (itv_hi_le _ 0) eqn:E1; [eauto|].
    destruct (itv_lo_ge _ 1) eqn:E2.
    + exfalso. pose proof (itv_lo_ge_sound _ _ _ E2 Hr). lia.
    + apply sat_assume_general; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint terms_all_live (live : pmap unit) (l : list term) : bool :=
  match l with
  | [] => true
  | (s, _) :: t => pm_mem s live && terms_all_live live t
  end.

Fixpoint box_restrict (live : pmap unit) (B : box) (l : list (positive * itv)) : box :=
  match l with
  | [] => B
  | (s, i) :: t => box_restrict live (if pm_mem s live then B else pm_remove s B) t
  end.

Definition store_restrict (S : store) (live : pmap unit) : store :=
  mkStore (pm_of_list (filter (fun si => pm_mem (fst si) live) (pm_elements (sbox S))))
          (filter (fun c => terms_all_live live (lt c)) (scons S))
          (pm_of_list (filter (fun si => pm_mem (fst si) live) (pm_elements (scong S)))).

Lemma pm_of_list_get_in {A} (l : list (positive * A)) k (x : A) :
  pm_get k (pm_of_list l) = Some x -> In (k, x) l.
Proof.
  unfold pm_of_list.
  assert (H : forall m, pm_get k (fold_left (fun m kv => pm_set (fst kv) (snd kv) m) l m) = Some x ->
                        In (k, x) l \/ pm_get k m = Some x).
  { induction l as [|[k' x'] t IH]; intros m Hg; simpl in *; auto.
    destruct (IH _ Hg) as [H|H]; auto.
    rewrite pm_get_set in H. destruct (Pos.eqb_spec k k'); [|auto].
    inversion H; subst; auto. }
  intros Hg. destruct (H _ Hg) as [H'|H']; auto. rewrite pm_get_empty in H'. discriminate.
Qed.

Lemma sat_restrict v S live : sat v S -> sat v (store_restrict S live).
Proof.
  intros [HB [HC HG]]. (split; [|split]); simpl.
  - intros s i Hg. apply pm_of_list_get_in in Hg. apply filter_In in Hg as [Hin _].
    apply pm_elements_sound in Hin. exact (HB _ _ Hin).
  - rewrite Forall_forall in *. intros c Hin. apply filter_In in Hin as [Hin _]. auto.
  - intros s m r Hg. apply pm_of_list_get_in in Hg. apply filter_In in Hg as [Hin _].
    apply pm_elements_sound in Hin. exact (HG _ _ _ Hin).
Qed.

(* [comment removed for export] *)
Definition sym_in_store (S : store) (s : sym) : Prop :=
  (exists i, pm_get s (sbox S) = Some i) \/
  (exists c, In c (scons S) /\ In s (lsyms c)) \/
  (exists mr, pm_get s (scong S) = Some mr).

Lemma sat_ext v1 v2 S :
  (forall s, sym_in_store S s -> v1 s = v2 s) -> sat v1 S -> sat v2 S.
Proof.
  intros Hagree [HB [HC HG]]. (split; [|split]).
  - intros s i Hg. rewrite <- Hagree; [exact (HB _ _ Hg)|]. left; eauto.
  - rewrite Forall_forall in *. intros c Hin.
    rewrite (eval_ext v2 v1); [auto|].
    intros s Hs. symmetry. apply Hagree. right; left. eauto.
  - intros s m r Hg. rewrite <- Hagree; [exact (HG _ _ _ Hg)|]. right; right; eauto.
Qed.

(* [comment removed for export] *)
Fixpoint terms_below (b : positive) (l : list term) : bool :=
  match l with
  | [] => true
  | (s, _) :: t => Pos.ltb s b && terms_below b t
  end.

Definition store_below (S : store) (b : positive) : bool :=
  forallb (fun si => Pos.ltb (fst si) b) (pm_elements (sbox S))
  && forallb (fun c => terms_below b (lt c)) (scons S)
  && forallb (fun si => Pos.ltb (fst si) b) (pm_elements (scong S)).

Lemma terms_below_sound b l s : terms_below b l = true -> In s (map fst l) -> (s < b)%positive.
Proof.
  induction l as [|[s' k] t IH]; simpl; intros H Hin; [tauto|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; auto.
  now apply Pos.ltb_lt.
Qed.

Lemma store_below_sound S b s : store_below S b = true -> sym_in_store S s -> (s < b)%positive.
Proof.
  unfold store_below. intros H Hs.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite forallb_forall in *.
  destruct Hs as [[i Hg]|[[c [Hin Hsc]]|[mr Hg]]].
  - apply pm_elements_complete in Hg. specialize (H1 _ Hg). simpl in H1. now apply Pos.ltb_lt.
  - specialize (H2 _ Hin). eapply terms_below_sound; eauto.
  - apply pm_elements_complete in Hg. specialize (H3 _ Hg). simpl in H3. now apply Pos.ltb_lt.
Qed.

Definition vupd (v : val) (s : sym) (x : Z) : val :=
  fun s' => if Pos.eqb s' s then x else v s'.

Lemma vupd_same v s x : vupd v s x s = x.
Proof. unfold vupd. now rewrite Pos.eqb_refl. Qed.
Lemma vupd_other v s x s' : s' <> s -> vupd v s x s' = v s'.
Proof. intros. unfold vupd. destruct (Pos.eqb_spec s' s); congruence. Qed.

(* [comment removed for export] *)
Lemma sat_fresh v S b s i x :
  store_below S b = true -> (b <= s)%positive ->
  sat v S -> in_itv x i ->
  sat (vupd v s x) (store_set_box S s i).
Proof.
  intros Hb Hs HS Hi. apply sat_set_box.
  - apply sat_ext with v; auto. intros s' Hs'. rewrite vupd_other; auto.
    pose proof (store_below_sound S b s' Hb Hs'). lia.
  - rewrite vupd_same. exact Hi.
Qed.

Lemma sat_fresh_top v S b s x :
  store_below S b = true -> (b <= s)%positive -> sat v S -> sat (vupd v s x) S.
Proof.
  intros Hb Hs HS. apply sat_ext with v; auto. intros s' Hs'. rewrite vupd_other; auto.
  pose proof (store_below_sound S b s' Hb Hs'). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lin_below (a : lin) (b : positive) : bool := terms_below b (lt a).

Lemma terms_below_iff b l : terms_below b l = true <-> (forall s, In s (map fst l) -> (s < b)%positive).
Proof.
  induction l as [|[s k] t IH]; simpl.
  - split; [tauto|auto].
  - rewrite andb_true_iff, IH, Pos.ltb_lt. split.
    + intros [H1 H2] s' [<-|H]; auto.
    + intros H; split; auto.
Qed.

Lemma lin_below_iff a b : lin_below a b = true <-> (forall s, In s (lsyms a) -> (s < b)%positive).
Proof. apply terms_below_iff. Qed.

Lemma store_below_iff S b :
  store_below S b = true <-> (forall s, sym_in_store S s -> (s < b)%positive).
Proof.
  split; [intros; eapply store_below_sound; eauto|].
  intros H. unfold store_below. rewrite !andb_true_iff, !forallb_forall. split; [split|].
  - intros [s i] Hin. simpl. apply Pos.ltb_lt. apply H. left. exists i. now apply pm_elements_sound.
  - intros c Hin. apply terms_below_iff. intros s Hs. apply H. right; left. exists c; auto.
  - intros [s mr] Hin. simpl. apply Pos.ltb_lt. apply H. right; right. exists mr. now apply pm_elements_sound.
Qed.

Lemma store_below_mono S b b' : (b <= b')%positive -> store_below S b = true -> store_below S b' = true.
Proof.
  intros Hle H. apply (proj2 (store_below_iff _ _)). intros s Hs. pose proof (proj1 (store_below_iff _ _) H) as H'; clear H; rename H' into H. specialize (H s Hs). lia.
Qed.

Lemma sym_in_store_set_box S s i s' :
  sym_in_store (store_set_box S s i) s' -> s' = s \/ sym_in_store S s'.
Proof.
  unfold sym_in_store, store_set_box; simpl. intros [[i' Hg]|[H|H]]; auto.
  rewrite pm_get_set in Hg. destruct (Pos.eqb_spec s' s); auto. right. left. eauto.
Qed.

Lemma store_below_set_box S b s i :
  store_below S b = true -> (s < b)%positive -> store_below (store_set_box S s i) b = true.
Proof.
  intros H Hs. apply (proj2 (store_below_iff _ _)). intros s' Hs'. apply sym_in_store_set_box in Hs' as [->|Hs']; auto.
  pose proof (proj1 (store_below_iff _ _) H) as H'; clear H; rename H' into H. auto.
Qed.

Lemma store_below_meet_box S b s i S' :
  store_below S b = true -> (s < b)%positive -> store_meet_box S s i = Some S' -> store_below S' b = true.
Proof.
  unfold store_meet_box. intros H Hs E. destruct (itv_empty _); [discriminate|].
  inversion E; subst. now apply store_below_set_box.
Qed.

Lemma store_below_meet_box_r al S b s i S' :
  store_below S b = true -> (s < b)%positive -> store_meet_box_r al S s i = Some S' -> store_below S' b = true.
Proof.
  unfold store_meet_box_r. intros H Hs E. destruct (negb al && itv_eqb _ _); [inversion E; now subst|].
  destruct (itv_empty _); [discriminate|]. inversion E; subst. now apply store_below_set_box.
Qed.

Lemma store_below_add_cong S b s m r S' :
  store_below S b = true -> (s < b)%positive -> store_add_cong S s m r = Some S' -> store_below S' b = true.
Proof.
  intros H Hs. unfold store_add_cong.
  assert (Hgen : forall B C, store_below (mkStore B (scons S) C) b = true ->
            store_below (mkStore B (scons S) (pm_set s (m, r mod m) C)) b = true).
  { intros B C HB. apply (proj2 (store_below_iff _ _)). intros s' Hs'. pose proof (proj1 (store_below_iff _ _) HB) as HB'; clear HB; rename HB' into HB.
    destruct Hs' as [X|[X|[mr Hg]]]; [apply HB; left; exact X|apply HB; right; left; exact X|].
    simpl in Hg. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec s' s); [subst; auto|].
    apply HB. right; right. exists mr. exact Hg. }
  destruct (Z.leb m 1).
  - destruct (Z.eqb m 0); [|intros E; inversion E; now subst].
    destruct (store_meet_box S s (itv_const r)) as [S1|] eqn:E1; [|discriminate].
    intros E; inversion E; subst. pose proof (store_below_meet_box S b s _ S1 H Hs E1) as H1.
    apply (proj2 (store_below_iff _ _)). intros s' Hs'. pose proof (proj1 (store_below_iff _ _) H1) as H1'; clear H1; rename H1' into H1.
    destruct Hs' as [X|[X|[mr Hg]]]; [apply H1; left; exact X|apply H1; right; left; exact X|].
    simpl in Hg. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec s' s); [subst; auto|].
    apply H1. right; right. exists mr. exact Hg.
  - destruct (cong_get (scong S) s) as [om orr].
    destruct (Z.eqb om 0). { destruct (Z.eqb _ _); intros E; inversion E; now subst. }
    destruct (Z.eqb (om mod m) 0). { destruct (Z.eqb _ _); intros E; inversion E; now subst. }
    destruct (Z.ltb 0 om && Z.eqb (m mod om) 0); [|intros E; inversion E; now subst].
    destruct (Z.eqb _ _); [|discriminate].
    destruct (itv_empty _); [discriminate|].
    intros E; inversion E; subst.
    apply (Hgen (pm_set s (itv_tighten_cong m (r mod m) (store_get_box S s)) (sbox S)) (scong S)).
    pose proof (store_below_set_box S b s (itv_tighten_cong m (r mod m) (store_get_box S s)) H Hs) as X.
    unfold store_set_box in X. destruct S; simpl in *. exact X.
Qed.

Lemma store_below_assume_single S b s k c S' :
  store_below S b = true -> (s < b)%positive -> assume_single S s k c = Some S' -> store_below S' b = true.
Proof.
  unfold assume_single. intros H Hs.
  destruct (Z.ltb 0 k); [intros; eapply store_below_meet_box_r; eauto|].
  destruct (Z.ltb k 0); [intros; eapply store_below_meet_box_r; eauto|].
  destruct (Z.leb c 0); intros E; inversion E; now subst.
Qed.

Lemma store_below_tighten_one S b a s k S' :
  store_below S b = true -> (s < b)%positive -> tighten_one S a s k = Some S' -> store_below S' b = true.
Proof.
  unfold tighten_one. intros H Hs. destruct (itv_lo _); [|intros E; inversion E; now subst].
  destruct (Z.ltb 0 k); [intros; eapply store_below_meet_box_r; eauto|].
  destruct (Z.ltb k 0); [intros; eapply store_below_meet_box_r; eauto|].
  intros E; inversion E; now subst.
Qed.

Lemma store_below_tighten_all b a l : forall S S',
  store_below S b = true -> (forall s, In s (map fst l) -> (s < b)%positive) ->
  tighten_all S a l = Some S' -> store_below S' b = true.
Proof.
  induction l as [|[s k] t IH]; intros S S' H Hl E; simpl in E.
  - inversion E; now subst.
  - destruct (tighten_one S a s k) as [S1|] eqn:E1; [|discriminate].
    apply (IH S1 S'); auto.
    + eapply store_below_tighten_one; eauto. apply Hl. simpl; auto.
    + intros; apply Hl; simpl; auto.
Qed.

Lemma map_fst_terms_divq g l : map fst (terms_divq g l) = map fst l.
Proof. induction l as [|[s k] t IH]; simpl; auto. now rewrite IH. Qed.

Lemma lsyms_lin_normc a : lsyms (lin_normc a) = lsyms a.
Proof.
  unfold lin_normc, lsyms. destruct (Z.leb _ 1); auto. simpl. apply map_fst_terms_divq.
Qed.

Lemma store_below_assume_general S b a S' :
  store_below S b = true -> lin_below a b = true -> assume_general S a = Some S' -> store_below S' b = true.
Proof.
  unfold assume_general. intros H Ha. destruct (lin_mem _ _); [intros E; inversion E; now subst|].
  intros E. pose proof (proj1 (lin_below_iff _ _) Ha) as Ha'; clear Ha; rename Ha' into Ha.
  eapply store_below_tighten_all; [| |exact E].
  - apply (proj2 (store_below_iff _ _)). intros s Hs. pose proof (proj1 (store_below_iff _ _) H) as H'; clear H; rename H' into H.
    destruct Hs as [X|[[c [Hin Hsc]]|X]]; [apply H; left; exact X| |apply H; right; right; exact X].
    simpl in Hin. destruct Hin as [<-|Hin].
    + apply Ha. now rewrite <- lsyms_lin_normc.
    + apply H. right; left. eauto.
  - intros s Hs. apply Ha. rewrite <- lsyms_lin_normc. exact Hs.
Qed.

Lemma store_below_restrict S b live : store_below S b = true -> store_below (store_restrict S live) b = true.
Proof.
  intros H. apply (proj2 (store_below_iff _ _)). intros s Hs. pose proof (proj1 (store_below_iff _ _) H) as H'; clear H; rename H' into H. apply H.
  destruct Hs as [[i Hg]|[[c [Hin Hsc]]|[mr Hg]]]; simpl in *.
  - left. apply pm_of_list_get_in in Hg. apply filter_In in Hg as [Hg _]. apply pm_elements_sound in Hg. eauto.
  - right; left. apply filter_In in Hin as [Hin _]. eauto.
  - right; right. apply pm_of_list_get_in in Hg. apply filter_In in Hg as [Hg _]. apply pm_elements_sound in Hg. eauto.
Qed.
