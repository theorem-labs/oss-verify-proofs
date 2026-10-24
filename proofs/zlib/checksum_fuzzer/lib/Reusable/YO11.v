(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Ltac mbinds := repeat lazymatch goal with |- itok (bind _ _ _) _ => apply itok_bind end.
Definition LK (s : astate) (q : sptr) : option (option sptr * option sptr) :=
match MT s q with Some x => Some (links_of x) | None => None end.
Lemma links_with_links x pr nx : links_of (with_links x pr nx) = (pr, nx).
Proof. destruct x; reflexivity. Qed.
Lemma with_links_with_links x a b c d : with_links (with_links x a b) c d = with_links x c d.
Proof. destruct x; reflexivity. Qed.
Definition set_head_st (h : headloc) (v : option sptr) (s : astate) : astate :=
match h with
| HActive sc => set_active (lupd (st_active s) (Z.to_nat sc) v) s
| HFreeMeta => set_free_meta_head v s
end.
Lemma itok_set_head' h v s (Q : unit * astate -> Prop) : Q (tt, set_head_st h v s) -> itok (set_head h v s) Q.
Proof. intros H. apply itok_set_head. destruct h; exact H. Qed.
Definition head_of (h : headloc) (s : astate) : option sptr :=
match h with HActive sc => active_hd s sc | HFreeMeta => st_free_meta_head s end.
Lemma itok_get_head' h s (Q : option sptr * astate -> Prop) : Q (head_of h s, s) -> itok (get_head h s) Q.
Proof. intros H. apply itok_get_head. destruct h; exact H. Qed.
Definition head_idx_ok (h : headloc) (s : astate) : Prop :=
match h with HActive sc => (Z.to_nat sc < length (st_active s))%nat | HFreeMeta => True end.
Lemma st_metas_set_head h v s : st_metas (set_head_st h v s) = st_metas s.
Proof. destruct h; reflexivity. Qed.
Lemma MT_set_head h v s q : MT (set_head_st h v s) q = MT s q.
Proof. unfold MT. rewrite st_metas_set_head. reflexivity. Qed.
Lemma head_of_set_head h v s : head_idx_ok h s -> head_of h (set_head_st h v s) = v.
Proof.
destruct h as [sc|]; cbn; [|reflexivity]. intros Hi. unfold active_hd. cbn [st_active set_active].
rewrite nth_lupd, Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) (length (st_active s))) with true; [reflexivity|].
symmetry. apply Nat.ltb_lt. exact Hi.
Qed.
Lemma nth_active_set_head h v s k :
(forall sc, h = HActive sc -> k <> Z.to_nat sc) ->
nth k (st_active (set_head_st h v s)) None = nth k (st_active s) None.
Proof.
intros Hk. destruct h as [sc|]; cbn [st_active set_head_st set_active set_free_meta_head]; [|reflexivity].
rewrite nth_lupd. replace (Nat.eqb k (Z.to_nat sc)) with false; [reflexivity|].
symmetry. apply Nat.eqb_neq. apply Hk. reflexivity.
Qed.
Lemma fmh_set_head h v s : h <> HFreeMeta -> st_free_meta_head (set_head_st h v s) = st_free_meta_head s.
Proof. destruct h; [reflexivity | intros H; exfalso; apply H; reflexivity]. Qed.
Lemma length_active_set_head h v s : length (st_active (set_head_st h v s)) = length (st_active s).
Proof. destruct h; cbn; [apply length_lupd | reflexivity]. Qed.
Lemma head_idx_ok_set_head h h' v s : head_idx_ok h s -> head_idx_ok h (set_head_st h' v s).
Proof. unfold head_idx_ok. rewrite length_active_set_head. auto. Qed.
Lemma head_idx_ok_upd_meta h g x s : head_idx_ok h s -> head_idx_ok h (upd_meta g x s).
Proof. unfold head_idx_ok, upd_meta. cbn. auto. Qed.
Lemma head_of_upd_meta h g x s : head_of h (upd_meta g x s) = head_of h s.
Proof. destruct h; reflexivity. Qed.
Lemma itok_set_links' p pr nx s x (Q : unit * astate -> Prop) :
MT s p = Some x -> Q (tt, upd_meta p (with_links x pr nx) s) -> itok (set_links p pr nx s) Q.
Proof. intros. eapply itok_set_links; eauto. Qed.
Lemma itok_setm' p am s (Q : unit * astate -> Prop) : Q (tt, upd_meta p (MUsed am) s) -> itok (setm p am s) Q.
Proof. intros. apply itok_setm. assumption. Qed.
Lemma itok_setslot' p x s (Q : unit * astate -> Prop) : Q (tt, upd_meta p x s) -> itok (setslot p x s) Q.
Proof. intros. apply itok_setslot. assumption. Qed.
Lemma itok_set_next p nx s x (Q : unit * astate -> Prop) :
MT s p = Some x ->
Q (tt, upd_meta p (with_links x (fst (links_of x)) nx) s) ->
itok (set_next p nx s) Q.
Proof.
intros Hm H. unfold set_next. apply itok_bind. eapply itok_get_links; [exact Hm|]. msimp.
eapply itok_set_links; [exact Hm|]. exact H.
Qed.
Lemma itok_set_prev p pr s x (Q : unit * astate -> Prop) :
MT s p = Some x ->
Q (tt, upd_meta p (with_links x pr (snd (links_of x))) s) ->
itok (set_prev p pr s) Q.
Proof.
intros Hm H. unfold set_prev. apply itok_bind. eapply itok_get_links; [exact Hm|]. msimp.
eapply itok_set_links; [exact Hm|]. exact H.
Qed.
Definition same_but_metas_heads (s s' : astate) : Prop :=
st_init_done s' = st_init_done s /\ st_mmap_counter s' = st_mmap_counter s /\
st_avail_meta s' = st_avail_meta s /\ st_avail_meta_count s' = st_avail_meta_count s /\
st_avail_meta_area_count s' = st_avail_meta_area_count s /\ st_meta_alloc_shift s' = st_meta_alloc_shift s /\
st_area_head s' = st_area_head s /\ st_area_tail s' = st_area_tail s /\
st_avail_meta_areas s' = st_avail_meta_areas s /\ st_usage s' = st_usage s /\
st_unmap_seq s' = st_unmap_seq s /\ st_bounces s' = st_bounces s /\ st_seq s' = st_seq s /\
st_brk s' = st_brk s /\ st_regions s' = st_regions s /\ st_areas s' = st_areas s /\
keys s' = keys s.
Definition heads_same_except (h : headloc) (s s' : astate) : Prop :=
(forall k, (forall sc, h = HActive sc -> k <> Z.to_nat sc) -> nth k (st_active s') None = nth k (st_active s) None) /\
(h <> HFreeMeta -> st_free_meta_head s' = st_free_meta_head s) /\
length (st_active s') = length (st_active s).
Lemma sbmh_refl s : same_but_metas_heads s s.
Proof. repeat split; reflexivity. Qed.
Lemma sbmh_trans s1 s2 s3 : same_but_metas_heads s1 s2 -> same_but_metas_heads s2 s3 -> same_but_metas_heads s1 s3.
Proof. unfold same_but_metas_heads. intros A B. decompose [and] A. decompose [and] B. repeat split; congruence. Qed.
Lemma sbmh_upd_meta g x s : In g (keys s) -> same_but_metas_heads s (upd_meta g x s).
Proof. intros Hg. repeat split; try reflexivity. apply keys_upd_In. exact Hg. Qed.
Lemma sbmh_set_head h v s : same_but_metas_heads s (set_head_st h v s).
Proof. destruct h; repeat split; reflexivity. Qed.
Lemma hse_refl h s : heads_same_except h s s.
Proof. repeat split; reflexivity. Qed.
Lemma hse_trans h s1 s2 s3 : heads_same_except h s1 s2 -> heads_same_except h s2 s3 -> heads_same_except h s1 s3.
Proof.
intros (A1 & A2 & A3) (B1 & B2 & B3). split; [|split]; [intros k Hk; rewrite B1, A1; auto | intros H; rewrite B2, A2; auto | congruence].
Qed.
Lemma hse_upd_meta h g x s : heads_same_except h s (upd_meta g x s).
Proof. repeat split; reflexivity. Qed.
Lemma hse_set_head h v s : heads_same_except h s (set_head_st h v s).
Proof.
split; [|split].
- intros k Hk. apply nth_active_set_head. exact Hk.
- apply fmh_set_head.
- apply length_active_set_head.
Qed.
Lemma In_keys_of_MT s q x : MT s q = Some x -> In q (keys s).
Proof. apply MT_Some_In_keys. Qed.
Lemma dequeue_op h m s x rest (lk : sptr -> option (option sptr * option sptr)) (Q : unit * astate -> Prop) :
MT s m = Some x ->
cycle_ok lk (m :: rest) ->
(forall q l, In q (m :: rest) -> lk q = Some l -> LK s q = Some l) ->
head_idx_ok h s ->
(forall s',
same_but_metas_heads s s' ->
heads_same_except h s s' ->
head_of h s' = (match rest with
| [] => None
| y :: _ => if osptr_eqb (head_of h s) (Some m) then Some y else head_of h s
end) ->
MT s' m = Some (with_links x None None) ->
(forall q, ~ In q (m :: rest) -> MT s' q = MT s q) ->
(forall y xy, In y rest -> MT s y = Some xy ->
MT s' y = Some (with_links xy
(if sptr_eqb y (hd m rest) then Some (last rest m) else fst (links_of xy))
(if sptr_eqb y (last rest m) then Some (hd m rest) else snd (links_of xy)))) ->
Q (tt, s')) ->
itok (dequeue h m s) Q.
Proof.
intros Hm Hcyc Hlk Hh HQ.
destruct Hcyc as [Hnd Hch].
assert (Lm : lk m = Some (Some (last rest m), Some (hd m rest))).
{ cbn [chain] in Hch. rewrite last_cons in Hch. destruct Hch as [Hx _]. exact Hx. }
pose proof (Hlk m _ (or_introl eq_refl) Lm) as LKm. unfold LK in LKm. rewrite Hm in LKm.
injection LKm as Lx.
pose proof (In_keys_of_MT _ _ _ Hm) as Km.
unfold dequeue. mbinds. eapply itok_get_links; [exact Hm|]. msimp. rewrite Lx. cbn [fst snd].
inversion Hnd as [|m' rest0 Hmn Hndr]; subst.
destruct rest as [|y rest'].
-
cbn [hd]. replace (osptr_eqb (Some m) (Some m)) with true by (cbn; rewrite sptr_eqb_refl; reflexivity).
mbinds. apply itok_set_head'. msimp.
eapply itok_set_links; [rewrite MT_set_head; exact Hm|].
change (Q (tt, upd_meta m (with_links x None None) (set_head_st h None s))).
apply HQ.
+ eapply sbmh_trans; [apply sbmh_set_head | apply sbmh_upd_meta]. unfold keys. rewrite st_metas_set_head. exact Km.
+ eapply hse_trans; [apply hse_set_head | apply hse_upd_meta].
+ rewrite head_of_upd_meta. apply head_of_set_head. exact Hh.
+ rewrite MT_upd_same. reflexivity.
+ intros q Hq. rewrite MT_upd_other, MT_set_head; [reflexivity|]. intros ->. apply Hq. left. reflexivity.
+ intros z xz Hz. destruct Hz.
-
cbn [hd].
assert (Hym : y <> m) by (intros ->; apply Hmn; left; reflexivity).
replace (osptr_eqb (Some y) (Some m)) with false
by (symmetry; apply Bool.not_true_iff_false; rewrite osptr_eqb_eq; congruence).
remember (last (y :: rest') m) as t eqn:Et.
assert (Htin : In t (y :: rest')) by (rewrite Et; apply In_last; discriminate).
assert (Htm : t <> m) by (intros E; apply Hmn; rewrite <- E; exact Htin).
destruct Hch as [_ Hch].
destruct (chain_links _ _ _ _ t Hch Htin) as (tpr & tnx & Lt).
pose proof (Hlk t _ (or_intror Htin) Lt) as LKt. unfold LK in LKt.
destruct (MT s t) as [xt|] eqn:Mt; [|discriminate]. injection LKt as Lxt.
destruct (chain_links _ _ _ _ y Hch (or_introl eq_refl)) as (ypr & ynx & Ly).
pose proof (Hlk y _ (or_intror (or_introl eq_refl)) Ly) as LKy. unfold LK in LKy.
destruct (MT s y) as [xy|] eqn:My; [|discriminate]. injection LKy as Lxy.
mbinds. eapply itok_set_next; [exact Mt|]. msimp. rewrite Lxt. cbn [fst].
mbinds.
apply (itok_set_prev _ _ _ (if sptr_eqb y t then with_links xt (Some tpr) (Some y) else xy)).
{ rewrite MT_upd. destruct (sptr_eqb y t); [reflexivity | exact My]. }
msimp.
mbinds. apply itok_get_head'. msimp. rewrite !head_of_upd_meta.
match goal with |- itok ((if ?c then _ else _) ?st) _ => set (s2 := st) end.
assert (K2 : same_but_metas_heads s s2 /\ heads_same_except h s s2 /\ head_of h s2 = head_of h s /\
head_idx_ok h s2 /\
MT s2 m = Some x /\
(forall q, ~ In q (m :: y :: rest') -> MT s2 q = MT s q) /\
(forall z xz, In z (y :: rest') -> MT s z = Some xz ->
MT s2 z = Some (with_links xz
(if sptr_eqb z y then Some t else fst (links_of xz))
(if sptr_eqb z t then Some y else snd (links_of xz))))).
{ subst s2. split.
{ eapply sbmh_trans; [apply sbmh_upd_meta; eapply In_keys_of_MT; exact Mt|].
apply sbmh_upd_meta. rewrite keys_upd_In by (eapply In_keys_of_MT; exact Mt). eapply In_keys_of_MT; exact My. }
split; [eapply hse_trans; apply hse_upd_meta|].
split; [rewrite !head_of_upd_meta; reflexivity|].
split; [apply head_idx_ok_upd_meta, head_idx_ok_upd_meta; exact Hh|].
split.
{ rewrite MT_upd_other by (intros ->; exact (Hym eq_refl)).
rewrite MT_upd_other by (intros ->; exact (Htm eq_refl)). exact Hm. }
split.
{ intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; right; left; reflexivity).
rewrite MT_upd_other by (intros ->; apply Hq; right; exact Htin). reflexivity. }
intros z xz Hz Mz. rewrite MT_upd. destruct (sptr_eqb z y) eqn:Ezy.
- apply sptr_eqb_eq in Ezy. subst z. rewrite My in Mz. injection Mz as <-.
destruct (sptr_eqb y t) eqn:Eyt.
+ apply sptr_eqb_eq in Eyt. rewrite <- Eyt in *. rewrite Mt in My. injection My as <-.
rewrite with_links_with_links, links_with_links. cbn [snd]. reflexivity.
+ rewrite Lxy. cbn [snd]. reflexivity.
- rewrite MT_upd. destruct (sptr_eqb z t) eqn:Ezt.
+ apply sptr_eqb_eq in Ezt. subst z. rewrite Mt in Mz. injection Mz as <-. rewrite Lxt. reflexivity.
+ rewrite Mz. f_equal.
destruct (chain_links _ _ _ _ z Hch Hz) as (zp & zn & Lz).
pose proof (Hlk z _ (or_intror Hz) Lz) as LKz. unfold LK in LKz. rewrite Mz in LKz.
injection LKz as Lxz.
destruct xz as [p1 n1| |am]; cbn in Lxz |- *; [injection Lxz as -> ->; reflexivity | discriminate |].
destruct am; cbn in Lxz |- *. injection Lxz as -> ->. reflexivity. }
clearbody s2. destruct K2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
assert (FIN : forall s3, same_but_metas_heads s s3 -> heads_same_except h s s3 ->
head_of h s3 = (if osptr_eqb (head_of h s) (Some m) then Some y else head_of h s) ->
(forall q, MT s3 q = MT s2 q) -> head_idx_ok h s3 ->
itok (set_links m None None s3) Q).
{ intros s3 T1 T2 T3 T4 T5. eapply itok_set_links; [rewrite T4; exact S5|].
change (Q (tt, upd_meta m (with_links x None None) s3)).
apply HQ.
- eapply sbmh_trans; [exact T1 | apply sbmh_upd_meta]. destruct T1 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& ->). exact Km.
- eapply hse_trans; [exact T2 | apply hse_upd_meta].
- rewrite head_of_upd_meta. exact T3.
- apply MT_upd_same.
- intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; left; reflexivity). rewrite T4. apply S6. exact Hq.
- intros z xz Hz Mz. rewrite MT_upd_other by (intros ->; apply Hmn; exact Hz). rewrite T4.
cbn [hd]. apply S7; assumption. }
destruct (osptr_eqb (head_of h s) (Some m)) eqn:Ehd.
+ mbinds. apply itok_set_head'. msimp. apply FIN.
* eapply sbmh_trans; [exact S1 | apply sbmh_set_head].
* eapply hse_trans; [exact S2 | apply hse_set_head].
* apply head_of_set_head. exact S4.
* intros q. apply MT_set_head.
* apply head_idx_ok_set_head. exact S4.
+ mbinds. apply itok_ret. msimp. apply FIN; auto.
Qed.
Lemma queue_op h m s x ms (lk : sptr -> option (option sptr * option sptr)) (Q : unit * astate -> Prop) :
MT s m = Some x -> links_of x = (None, None) ->
ring_ok lk (head_of h s) ms -> ~ In m ms ->
(forall q l, In q ms -> lk q = Some l -> LK s q = Some l) ->
head_idx_ok h s ->
(forall s',
same_but_metas_heads s s' ->
heads_same_except h s s' ->
head_of h s' = Some (hd m ms) ->
MT s' m = Some (with_links x (Some (last ms m)) (Some (hd m ms))) ->
(forall q, ~ In q (m :: ms) -> MT s' q = MT s q) ->
(forall y xy, In y ms -> MT s y = Some xy ->
MT s' y = Some (with_links xy
(if sptr_eqb y (hd m ms) then Some m else fst (links_of xy))
(if sptr_eqb y (last ms m) then Some m else snd (links_of xy)))) ->
Q (tt, s')) ->
itok (queue h m s) Q.
Proof.
intros Hm Lx Hring Hnin Hlk Hh HQ.
pose proof (In_keys_of_MT _ _ _ Hm) as Km.
unfold queue. mbinds. eapply itok_get_links; [exact Hm|]. msimp. rewrite Lx. cbn [fst snd].
mbinds. apply itok_massert; [reflexivity|]. msimp.
mbinds. apply itok_get_head'. msimp.
destruct Hring as [[Hnd Hch] Hhd].
destruct ms as [|h0 rest].
-
cbn in Hhd. rewrite Hhd.
mbinds. eapply itok_set_links'; [exact Hm|]. msimp.
apply itok_set_head'.
apply HQ.
+ eapply sbmh_trans; [apply sbmh_upd_meta; exact Km | apply sbmh_set_head].
+ eapply hse_trans; [apply hse_upd_meta | apply hse_set_head].
+ cbn [hd]. apply head_of_set_head. apply head_idx_ok_upd_meta. exact Hh.
+ rewrite MT_set_head, MT_upd_same. reflexivity.
+ intros q Hq. rewrite MT_set_head, MT_upd_other; [reflexivity|]. intros ->. apply Hq. left. reflexivity.
+ intros y xy Hy. destruct Hy.
- cbn in Hhd. rewrite Hhd.
assert (Hh0m : h0 <> m) by (intros ->; apply Hnin; left; reflexivity).
remember (last (h0 :: rest) m) as t eqn:Et.
assert (Et' : last (h0 :: rest) h0 = t) by (rewrite Et; apply last_indep; discriminate).
rewrite Et' in Hch.
assert (Htin : In t (h0 :: rest)) by (rewrite Et; apply In_last; discriminate).
assert (Htm : t <> m) by (intros E; apply Hnin; rewrite <- E; exact Htin).
pose proof Hch as Hch0. cbn [chain] in Hch0. destruct Hch0 as [Lh0 _].
pose proof (Hlk h0 _ (or_introl eq_refl) Lh0) as LKh0. unfold LK in LKh0.
destruct (MT s h0) as [xh|] eqn:Mh; [|discriminate]. injection LKh0 as Lxh.
destruct (chain_links _ _ _ _ t Hch Htin) as (tpr & tnx & Lt).
pose proof (Hlk t _ Htin Lt) as LKt. unfold LK in LKt.
destruct (MT s t) as [xt|] eqn:Mt; [|discriminate]. injection LKt as Lxt.
mbinds. eapply itok_get_links; [exact Mh|]. msimp. rewrite Lxh. cbn [fst].
mbinds. eapply itok_set_links'; [exact Hm|]. msimp.
mbinds. eapply (itok_set_next _ _ _ xt).
{ rewrite MT_upd_other by exact Htm. exact Mt. }
msimp. rewrite Lxt. cbn [fst].
apply (itok_set_prev _ _ _ (if sptr_eqb h0 t then with_links xt (Some tpr) (Some m) else xh)).
{ rewrite MT_upd. destruct (sptr_eqb h0 t); [reflexivity|]. rewrite MT_upd_other by exact Hh0m. exact Mh. }
match goal with |- Q (tt, ?st) => set (s' := st) end.
apply HQ; subst s'.
+ eapply sbmh_trans; [apply sbmh_upd_meta; exact Km|].
eapply sbmh_trans; [apply sbmh_upd_meta | apply sbmh_upd_meta].
* rewrite keys_upd_In by exact Km. eapply In_keys_of_MT; exact Mt.
* rewrite keys_upd_In; [| rewrite keys_upd_In by exact Km; eapply In_keys_of_MT; exact Mt].
rewrite keys_upd_In by exact Km. eapply In_keys_of_MT; exact Mh.
+ eapply hse_trans; [apply hse_upd_meta|]. eapply hse_trans; apply hse_upd_meta.
+ rewrite !head_of_upd_meta. cbn [hd]. exact Hhd.
+ cbn [hd]. rewrite MT_upd_other by (intros E; exact (Hh0m (eq_sym E))).
rewrite MT_upd_other by (intros E; exact (Htm (eq_sym E))).
rewrite MT_upd_same. reflexivity.
+ intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; right; left; reflexivity).
rewrite MT_upd_other by (intros ->; apply Hq; right; exact Htin).
rewrite MT_upd_other by (intros ->; apply Hq; left; reflexivity). reflexivity.
+ intros y xy Hy My. cbn [hd]. rewrite MT_upd. destruct (sptr_eqb y h0) eqn:Eyh.
* apply sptr_eqb_eq in Eyh. subst y. rewrite Mh in My. injection My as <-.
destruct (sptr_eqb h0 t) eqn:Eht.
-- apply sptr_eqb_eq in Eht. rewrite <- Eht in Mt. rewrite Mh in Mt. injection Mt as <-.
rewrite with_links_with_links, links_with_links. cbn [snd]. reflexivity.
-- rewrite Lxh. cbn [snd]. reflexivity.
* rewrite MT_upd. destruct (sptr_eqb y t) eqn:Eyt.
-- apply sptr_eqb_eq in Eyt. subst y. rewrite Mt in My. injection My as <-. rewrite Lxt. reflexivity.
-- rewrite MT_upd_other by (intros ->; apply Hnin; exact Hy). rewrite My. f_equal.
destruct (chain_links _ _ _ _ y Hch Hy) as (yp & yn & Ly).
pose proof (Hlk y _ Hy Ly) as LKy. unfold LK in LKy. rewrite My in LKy. injection LKy as Lxy.
destruct xy as [p1 n1| |am]; cbn in Lxy |- *; [injection Lxy as -> ->; reflexivity | discriminate |].
destruct am; cbn in Lxy |- *. injection Lxy as -> ->. reflexivity.
Qed.
