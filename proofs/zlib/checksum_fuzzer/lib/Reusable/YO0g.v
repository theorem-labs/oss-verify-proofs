(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Fixpoint itok {A : Type} (t : itree astate A) (Q : A -> Prop) : Prop :=
match t with
| IRet a => Q a
| IFail _ => False
| IAsk q snap k => req_ok snap q /\ forall z, answer_ok q z -> itok (k z) Q
end.
Lemma itok_mono {A} (t : itree astate A) (Q Q' : A -> Prop) :
(forall a, Q a -> Q' a) -> itok t Q -> itok t Q'.
Proof.
induction t as [a | q snap k IH | f]; cbn; intros HQ H.
- apply HQ, H.
- destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH; [exact HQ | apply Hk, Hz].
- exact H.
Qed.
Lemma itok_ibind {A B} (t : itree astate A) (k : A -> itree astate B) (Q : B -> Prop) :
itok t (fun a => itok (k a) Q) -> itok (ibind t k) Q.
Proof.
induction t as [a | q snap c IH | f]; cbn; intros H.
- exact H.
- destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH. apply Hk, Hz.
- exact H.
Qed.
Lemma itok_safe {A} (t : itree astate A) Q : itok t Q -> safe t.
Proof.
induction t as [a | q snap k IH | f]; cbn; intros H; [exact I | | exact H].
destruct H as [_ Hk]. intros z Hz. apply (IH z). apply Hk, Hz.
Qed.
Lemma itok_reqs_ok {A} (t : itree astate A) Q : itok t Q -> reqs_ok t.
Proof.
induction t as [a | q snap k IH | f]; cbn; intros H; [exact I | | exact I].
destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply (IH z). apply Hk, Hz.
Qed.
Lemma itok_yields {A} (t : itree astate A) Q tr a : itok t Q -> yields t tr a -> Q a.
Proof.
revert tr. induction t as [a' | q snap k IH | f]; cbn; intros tr H Hy.
- destruct tr; [subst; exact H | destruct Hy].
- destruct tr as [|[q' z] tr']; [destruct Hy|].
destruct Hy as (-> & Hz & Hy). destruct H as [_ Hk]. eapply IH; [apply Hk, Hz | exact Hy].
- destruct tr; destruct Hy.
Qed.
Lemma itok_conj {A} (t : itree astate A) (Q1 Q2 : A -> Prop) :
itok t Q1 -> itok t Q2 -> itok t (fun a => Q1 a /\ Q2 a).
Proof.
induction t as [a | q snap k IH | f]; cbn; intros H1 H2.
- split; assumption.
- destruct H1 as [Hr H1], H2 as [_ H2]. split; [exact Hr|]. intros z Hz. apply IH; auto.
- exact H1.
Qed.
Section u.
Context {A B : Type}.
Implicit Types (Q : A * astate -> Prop) (s : astate).
Lemma itok_ret (a : A) s Q : Q (a, s) -> itok (ret a s) Q.
Proof. intros H. exact H. Qed.
Lemma itok_bind (m : M B) (k : B -> M A) s Q :
itok (m s) (fun r => itok (k (fst r) (snd r)) Q) -> itok (bind m k s) Q.
Proof.
intros H. unfold bind. apply itok_ibind.
eapply itok_mono; [|exact H]. intros [b s'] Hb. exact Hb.
Qed.
Lemma itok_fail f s Q : False -> itok (@fail A f s) Q.
Proof. intros []. Qed.
Lemma itok_get s (Q : astate * astate -> Prop) : Q (s, s) -> itok (get s) Q.
Proof. intros H. exact H. Qed.
Lemma itok_put s s' (Q : unit * astate -> Prop) : Q (tt, s') -> itok (put s' s) Q.
Proof. intros H. exact H. Qed.
Lemma itok_modify f s (Q : unit * astate -> Prop) : Q (tt, f s) -> itok (modify f s) Q.
Proof. intros H. exact H. Qed.
Lemma itok_ask q s (Q : bool * astate -> Prop) :
req_ok s q -> (forall z, answer_ok q z -> Q (negb (z =? 0), s)) -> itok (ask q s) Q.
Proof. intros Hr H. cbn. split; [exact Hr|]. intros z Hz. apply H, Hz. Qed.
Lemma itok_askz q s (Q : Z * astate -> Prop) :
req_ok s q -> (forall z, answer_ok q z -> Q (z, s)) -> itok (askz q s) Q.
Proof. intros Hr H. cbn. split; [exact Hr|]. intros z Hz. apply H, Hz. Qed.
Lemma itok_massert (b : bool) site s (Q : unit * astate -> Prop) :
b = true -> Q (tt, s) -> itok (massert b site s) Q.
Proof. intros -> H. exact H. Qed.
Lemma itok_mcheck (b : bool) tag s (Q : unit * astate -> Prop) :
b = true -> Q (tt, s) -> itok (mcheck b tag s) Q.
Proof. intros -> H. exact H. Qed.
Lemma itok_if_true (b : bool) (m1 m2 : M A) s Q :
b = true -> itok (m1 s) Q -> itok ((if b then m1 else m2) s) Q.
Proof. intros -> H. exact H. Qed.
Lemma itok_if_false (b : bool) (m1 m2 : M A) s Q :
b = false -> itok (m2 s) Q -> itok ((if b then m1 else m2) s) Q.
Proof. intros -> H. exact H. Qed.
End u.
Lemma itok_getm p s am (Q : ameta * astate -> Prop) :
MT s p = Some (MUsed am) -> Q (am, s) -> itok (getm p s) Q.
Proof.
intros Hm H. unfold getm. apply itok_bind. apply itok_get. cbn [fst snd].
unfold MT in Hm. rewrite Hm. exact H.
Qed.
Lemma itok_setm p am s (Q : unit * astate -> Prop) :
Q (tt, set_metas (mupdate (st_metas s) p (MUsed am)) s) -> itok (setm p am s) Q.
Proof. intros H. exact H. Qed.
Lemma itok_setslot p x s (Q : unit * astate -> Prop) :
Q (tt, set_metas (mupdate (st_metas s) p x) s) -> itok (setslot p x s) Q.
Proof. intros H. exact H. Qed.
Lemma itok_get_links p s x (Q : (option sptr * option sptr) * astate -> Prop) :
MT s p = Some x -> Q (links_of x, s) -> itok (get_links p s) Q.
Proof.
intros Hm H. unfold get_links. apply itok_bind. apply itok_get. cbn [fst snd].
unfold MT in Hm. rewrite Hm. exact H.
Qed.
Lemma itok_set_links p pr nx s x (Q : unit * astate -> Prop) :
MT s p = Some x ->
Q (tt, set_metas (mupdate (st_metas s) p (with_links x pr nx)) s) ->
itok (set_links p pr nx s) Q.
Proof.
intros Hm H. unfold set_links. apply itok_bind. apply itok_get. cbn [fst snd].
unfold MT in Hm. rewrite Hm. exact H.
Qed.
Lemma itok_get_head h s (Q : option sptr * astate -> Prop) :
Q (match h with HActive sc => nth (Z.to_nat sc) (st_active s) None | HFreeMeta => st_free_meta_head s end, s) ->
itok (get_head h s) Q.
Proof. intros H. unfold get_head. apply itok_bind. apply itok_get. cbn [fst snd]. destruct h; exact H. Qed.
Lemma itok_set_head h v s (Q : unit * astate -> Prop) :
Q (tt, match h with
| HActive sc => set_active (lupd (st_active s) (Z.to_nat sc) v) s
| HFreeMeta => set_free_meta_head v s
end) ->
itok (set_head h v s) Q.
Proof. intros H. unfold set_head. destruct h; exact H. Qed.
Ltac mstep :=
lazymatch goal with
| |- itok (bind _ _ _) _ => apply itok_bind
| |- itok (ret _ _) _ => apply itok_ret
| |- itok (get _) _ => apply itok_get
| |- itok (put _ _) _ => apply itok_put
| |- itok (modify _ _) _ => apply itok_modify
| |- itok (setm _ _ _) _ => apply itok_setm
| |- itok (setslot _ _ _) _ => apply itok_setslot
| |- itok (get_head _ _) _ => apply itok_get_head
| |- itok (set_head _ _ _) _ => apply itok_set_head
| |- itok (massert _ _ _) _ => apply itok_massert
| |- itok (mcheck _ _ _) _ => apply itok_mcheck
| |- itok (ask _ _) _ => apply itok_ask
| |- itok (askz _ _) _ => apply itok_askz
| |- itok (IRet _) _ => cbn [itok]
end.
Ltac msimp := cbn beta iota delta [fst snd].
Ltac mrun := repeat (mstep; msimp).
Lemma sptr_eqb_refl p : sptr_eqb p p = true.
Proof. destruct p; cbn. rewrite Nat.eqb_refl, Z.eqb_refl. reflexivity. Qed.
Lemma sptr_eqb_eq p q : sptr_eqb p q = true <-> p = q.
Proof.
destruct p as [r o], q as [r' o']; cbn. rewrite andb_true_iff, Nat.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity | intros H; injection H; auto].
Qed.
Lemma sptr_eqb_neq p q : sptr_eqb p q = false <-> p <> q.
Proof.
destruct (sptr_eqb p q) eqn:E.
- apply sptr_eqb_eq in E. split; [discriminate | intros H; exfalso; exact (H E)].
- split; [|reflexivity]. intros _ Heq. subst. rewrite sptr_eqb_refl in E. discriminate.
Qed.
Lemma sptr_eqb_sym p q : sptr_eqb p q = sptr_eqb q p.
Proof.
destruct (sptr_eqb p q) eqn:E1, (sptr_eqb q p) eqn:E2; try reflexivity.
- apply sptr_eqb_eq in E1. subst. rewrite sptr_eqb_refl in E2. discriminate.
- apply sptr_eqb_eq in E2. subst. rewrite sptr_eqb_refl in E1. discriminate.
Qed.
Lemma sptr_eq_dec (p q : sptr) : {p = q} + {p <> q}.
Proof.
destruct (sptr_eqb p q) eqn:E; [left; apply sptr_eqb_eq, E | right; apply sptr_eqb_neq, E].
Defined.
Lemma osptr_eqb_eq a b : osptr_eqb a b = true <-> a = b.
Proof.
destruct a as [p|], b as [q|]; cbn; try (split; [discriminate|discriminate]); try (split; reflexivity).
rewrite sptr_eqb_eq. split; [intros ->; reflexivity | intros H; injection H; auto].
Qed.
Lemma mlookup_mupdate_same l p x : mlookup (mupdate l p x) p = Some x.
Proof.
induction l as [|[q y] t IH]; cbn.
- rewrite sptr_eqb_refl. reflexivity.
- destruct (sptr_eqb p q) eqn:E; cbn; rewrite E; [reflexivity | exact IH].
Qed.
Lemma mlookup_mupdate_other l p q x : q <> p -> mlookup (mupdate l p x) q = mlookup l q.
Proof.
intros Hne. induction l as [|[k y] t IH]; cbn.
- destruct (sptr_eqb q p) eqn:E; [apply sptr_eqb_eq in E; congruence | reflexivity].
- destruct (sptr_eqb p k) eqn:E; cbn.
+ apply sptr_eqb_eq in E. subst k.
destruct (sptr_eqb q p) eqn:E2; [apply sptr_eqb_eq in E2; congruence | reflexivity].
+ destruct (sptr_eqb q k); [reflexivity | exact IH].
Qed.
Lemma mlookup_mupdate l p q x :
mlookup (mupdate l p x) q = if sptr_eqb q p then Some x else mlookup l q.
Proof.
destruct (sptr_eqb q p) eqn:E.
- apply sptr_eqb_eq in E. subst. apply mlookup_mupdate_same.
- apply mlookup_mupdate_other. apply sptr_eqb_neq, E.
Qed.
Lemma mlookup_In_keys l p x : mlookup l p = Some x -> In p (map fst l).
Proof.
induction l as [|[q y] t IH]; cbn; [discriminate|].
destruct (sptr_eqb p q) eqn:E; intros H.
- left. symmetry. apply sptr_eqb_eq, E.
- right. apply IH, H.
Qed.
Lemma mlookup_None_iff l p : mlookup l p = None <-> ~ In p (map fst l).
Proof.
induction l as [|[q y] t IH]; cbn.
- split; [intros _ [] | reflexivity].
- destruct (sptr_eqb p q) eqn:E.
+ apply sptr_eqb_eq in E. subst. split; [discriminate | intros H; exfalso; apply H; left; reflexivity].
+ rewrite IH. apply sptr_eqb_neq in E. split; [intros H [Hq|Ht]; [congruence | exact (H Ht)] | intros H Ht; apply H; right; exact Ht].
Qed.
Lemma map_fst_mupdate_In l p x : In p (map fst l) -> map fst (mupdate l p x) = map fst l.
Proof.
induction l as [|[q y] t IH]; cbn; [intros [] |].
destruct (sptr_eqb p q) eqn:E; cbn; [reflexivity|].
intros [Hq | Ht]; [apply sptr_eqb_neq in E; congruence |]. rewrite IH by exact Ht. reflexivity.
Qed.
Lemma map_fst_mupdate_notIn l p x : ~ In p (map fst l) -> map fst (mupdate l p x) = map fst l ++ [p].
Proof.
induction l as [|[q y] t IH]; cbn; [reflexivity|].
destruct (sptr_eqb p q) eqn:E; cbn.
- apply sptr_eqb_eq in E. subst. intros H. exfalso. apply H. left. reflexivity.
- intros H. rewrite IH; [reflexivity|]. intros Ht. apply H. right. exact Ht.
Qed.
Lemma In_mupdate_iff l p x e :
NoDup (map fst l) ->
In e (mupdate l p x) <-> (e = (p, x) \/ (fst e <> p /\ In e l)).
Proof.
intros Hnd. induction l as [|[q y] t IH]; cbn.
- split.
+ intros [H|[]]. left. symmetry. exact H.
+ intros [H|[_ []]]. left. symmetry. exact H.
- inversion Hnd as [|q' t' Hq Ht]; subst.
destruct (sptr_eqb p q) eqn:E; cbn.
+ apply sptr_eqb_eq in E. subst q. split.
* intros [H|H]; [left; symmetry; exact H | right].
split; [| right; exact H].
intros Heq. apply Hq. rewrite <- Heq. apply in_map. exact H.
* intros [H | [Hne [H|H]]]; [left; symmetry; exact H | | right; exact H].
exfalso. apply Hne. rewrite <- H. reflexivity.
+ rewrite (IH Ht). apply sptr_eqb_neq in E. split.
* intros [H | [H | [Hne H]]].
-- right. split; [rewrite <- H; cbn; congruence | left; exact H].
-- left. exact H.
-- right. split; [exact Hne | right; exact H].
* intros [H | [Hne [H | H]]].
-- right. left. exact H.
-- left. exact H.
-- right. right. split; assumption.
Qed.
Lemma NoDup_app_single {T} (l : list T) (a : T) : NoDup l -> ~ In a l -> NoDup (l ++ [a]).
Proof.
induction l as [|b t IH]; cbn; intros Hnd Hn.
- constructor; [intros [] | constructor].
- inversion Hnd; subst. constructor.
+ rewrite in_app_iff. cbn. intros [H | [H | []]]; [auto | subst; apply Hn; left; reflexivity].
+ apply IH; [assumption | intros H; apply Hn; right; exact H].
Qed.
Lemma NoDup_keys_mupdate l p x : NoDup (map fst l) -> NoDup (map fst (mupdate l p x)).
Proof.
intros H. destruct (in_dec sptr_eq_dec p (map fst l)) as [Hi|Hn].
- rewrite map_fst_mupdate_In by exact Hi. exact H.
- rewrite map_fst_mupdate_notIn by exact Hn. apply NoDup_app_single; assumption.
Qed.
Lemma mlookup_of_In l p x : NoDup (map fst l) -> In (p, x) l -> mlookup l p = Some x.
Proof.
induction l as [|[q y] t IH]; cbn; [intros _ [] |].
intros Hnd [H|H]; inversion Hnd; subst.
- injection H as -> ->. rewrite sptr_eqb_refl. reflexivity.
- destruct (sptr_eqb p q) eqn:E.
+ apply sptr_eqb_eq in E. subst. exfalso. apply H2. apply (in_map fst) in H. exact H.
+ apply IH; assumption.
Qed.
Lemma In_of_mlookup l p x : mlookup l p = Some x -> In (p, x) l.
Proof.
induction l as [|[q y] t IH]; cbn; [discriminate|].
destruct (sptr_eqb p q) eqn:E; intros H.
- injection H as ->. apply sptr_eqb_eq in E. subst. left. reflexivity.
- right. apply IH, H.
Qed.
Lemma used_metas_iff s g am :
NoDup (keys s) -> (In (g, am) (used_metas s) <-> MT s g = Some (MUsed am)).
Proof.
intros Hnd. unfold used_metas, MT, keys in *. split.
- intros H. apply in_flat_map in H as [[p x] [Hin Hx]].
destruct x; cbn in Hx; try (destruct Hx as [Hx|[]]); try contradiction.
injection Hx as -> ->. apply mlookup_of_In; assumption.
- intros H. apply in_flat_map. exists (g, MUsed am). split; [apply In_of_mlookup, H | left; reflexivity].
Qed.
Lemma length_lupd {X} (l : list X) i v : length (lupd l i v) = length l.
Proof. revert i. induction l; intros [|i]; cbn; auto. Qed.
Lemma nth_lupd {X} (l : list X) i j v d :
nth j (lupd l i v) d = if (Nat.eqb j i && Nat.ltb i (length l))%bool then v else nth j l d.
Proof.
revert i j. induction l as [|h t IH]; intros [|i] [|j]; cbn; try reflexivity.
- destruct (Nat.eqb j i); reflexivity.
- rewrite IH. destruct (Nat.eqb j i); cbn; [|reflexivity].
unfold Nat.ltb. cbn. reflexivity.
Qed.
Lemma nth_error_lupd {X} (l : list X) i j v :
nth_error (lupd l i v) j = if (Nat.eqb j i && Nat.ltb i (length l))%bool then Some v else nth_error l j.
Proof.
revert i j. induction l as [|h t IH]; intros [|i] [|j]; cbn; try reflexivity.
- destruct (Nat.eqb j i); reflexivity.
- rewrite IH. destruct (Nat.eqb j i); cbn; [|reflexivity].
unfold Nat.ltb. cbn. reflexivity.
Qed.
Lemma length_zupd l i v : length (zupd l i v) = length l.
Proof. revert i. induction l; intros [|i]; cbn; auto. Qed.
Lemma nth_zupd l i j v d :
nth j (zupd l i v) d = if (Nat.eqb j i && Nat.ltb i (length l))%bool then v else nth j l d.
Proof.
revert i j. induction l as [|h t IH]; intros [|i] [|j]; cbn; try reflexivity.
- destruct (Nat.eqb j i); reflexivity.
- rewrite IH. destruct (Nat.eqb j i); cbn; [|reflexivity].
unfold Nat.ltb. cbn. reflexivity.
Qed.
Lemma znth_zset i j v l :
0 <= i -> 0 <= j ->
znth j (zset i v l) = if (j =? i) && (i <? Z.of_nat (length l)) then v else znth j l.
Proof.
intros Hi Hj. unfold znth, zset. rewrite nth_zupd.
replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with (j =? i).
2:{ destruct (j =? i) eqn:E; symmetry.
- apply Nat.eqb_eq. apply Z.eqb_eq in E. subst. reflexivity.
- apply Nat.eqb_neq. apply Z.eqb_neq in E. intros H. apply E. lia. }
replace (Nat.ltb (Z.to_nat i) (length l)) with (i <? Z.of_nat (length l)).
2:{ destruct (i <? Z.of_nat (length l)) eqn:E; symmetry.
- apply Nat.ltb_lt. apply Z.ltb_lt in E. lia.
- apply Nat.ltb_ge. apply Z.ltb_ge in E. lia. }
reflexivity.
Qed.
Lemma length_zset i v l : length (zset i v l) = length l.
Proof. apply length_zupd. Qed.
Lemma In_zseq lo n x : In x (zseq lo n) <-> lo <= x < lo + n.
Proof.
unfold zseq. rewrite in_map_iff. split.
- intros [k [<- Hk]]. apply in_seq in Hk. lia.
- intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.
Lemma forallb_zseq_iff f lo n :
forallb f (zseq lo n) = true <-> forall x, lo <= x < lo + n -> f x = true.
Proof.
rewrite forallb_forall. split; intros H x Hx; apply H; apply In_zseq; exact Hx.
Qed.
Lemma nth_repeat' {X} (x d : X) n i : nth i (repeat x n) d = if Nat.ltb i n then x else d.
Proof.
revert i. induction n as [|n IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.
Lemma ones_eq k : ones k = Z.ones (k + 1).
Proof. unfold ones. rewrite Z.ones_equiv. lia. Qed.
Lemma testbit_ones k i : 0 <= k -> Z.testbit (ones k) i = (0 <=? i) && (i <=? k).
Proof.
intros Hk. rewrite ones_eq, Z.testbit_ones by lia.
destruct (0 <=? i); cbn; [|reflexivity].
destruct (i <? k + 1) eqn:E1, (i <=? k) eqn:E2; try reflexivity.
- apply Z.ltb_lt in E1. apply Z.leb_gt in E2. lia.
- apply Z.ltb_ge in E1. apply Z.leb_le in E2. lia.
Qed.
Lemma ones_nonneg k : 0 <= k -> 0 <= ones k.
Proof. intros. unfold ones. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.
Lemma bit_eq k : bit k = 2 ^ k.
Proof. reflexivity. Qed.
Lemma testbit_bit k i : 0 <= k -> Z.testbit (bit k) i = (k =? i).
Proof. intros. unfold bit. apply Z.pow2_bits_eqb. assumption. Qed.
Lemma testbit_neg_idx a i : i < 0 -> Z.testbit a i = false.
Proof. intros. destruct i; try lia. reflexivity. Qed.
Lemma bits_inj_nonneg a b :
(forall i, 0 <= i -> Z.testbit a i = Z.testbit b i) -> a = b.
Proof. intros H. apply Z.bits_inj'. exact H. Qed.
Lemma add_bit_lor m k : 0 <= k -> Z.testbit m k = false -> m + bit k = Z.lor m (bit k).
Proof.
intros Hk Hb. rewrite <- Z.lxor_lor.
- apply Z.add_nocarry_lxor. apply bits_inj_nonneg. intros i Hi.
rewrite Z.land_spec, testbit_bit, Z.bits_0 by lia.
destruct (Z.eq_dec k i); [subst; rewrite Hb; reflexivity|].
replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
- apply bits_inj_nonneg. intros i Hi.
rewrite Z.land_spec, testbit_bit, Z.bits_0 by lia.
destruct (Z.eq_dec k i); [subst; rewrite Hb; reflexivity|].
replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma sub_bit_ldiff m k : 0 <= k -> Z.testbit m k = true -> m - bit k = Z.ldiff m (bit k).
Proof.
intros Hk Hb.
assert (E : Z.ldiff m (bit k) + bit k = m).
{ rewrite add_bit_lor by (try lia; rewrite Z.ldiff_spec, testbit_bit, Z.eqb_refl by lia; cbn; rewrite andb_false_r; reflexivity).
apply bits_inj_nonneg. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, testbit_bit by lia.
destruct (Z.eq_dec k i); [subst; rewrite Hb, Z.eqb_refl; reflexivity|].
replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
rewrite andb_true_r, orb_false_r. reflexivity. }
lia.
Qed.
Lemma land_double a b : Z.land (2 * a) (2 * b) = 2 * Z.land a b.
Proof.
apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec.
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite !Z.testbit_even_0. reflexivity.
- replace i with (Z.succ (i - 1)) by lia.
rewrite !Z.testbit_even_succ by lia. rewrite Z.land_spec. reflexivity.
Qed.
Lemma lowbit_double a : lowbit (2 * a) = 2 * lowbit a.
Proof. unfold lowbit. replace (- (2 * a)) with (2 * (- a)) by lia. apply land_double. Qed.
Lemma lowbit_odd a : lowbit (2 * a + 1) = 1.
Proof.
unfold lowbit. apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec.
replace (- (2 * a + 1)) with (2 * (- a - 1) + 1) by lia.
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite !Z.testbit_odd_0. reflexivity.
- replace i with (Z.succ (i - 1)) by lia.
rewrite !Z.testbit_odd_succ by lia.
replace (- a - 1) with (Z.lnot a) by (unfold Z.lnot; lia).
rewrite Z.lnot_spec by lia.
replace (Z.testbit 1 (Z.succ (i - 1))) with false
by (symmetry; apply Z.bits_above_log2; [lia | cbn; lia]).
destruct (Z.testbit a (i - 1)); reflexivity.
Qed.
Lemma lowbit_spec m : 0 < m ->
exists k, 0 <= k /\ lowbit m = bit k /\ Z.testbit m k = true /\
(forall j, 0 <= j < k -> Z.testbit m j = false).
Proof.
intros Hm.
remember (Z.to_nat m) as n eqn:En. revert m Hm En.
induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf); intros m Hm En.
destruct (Z.Even_or_Odd m) as [[a Ha] | [a Ha]].
- subst m. assert (0 < a) by lia.
destruct (IH (Z.to_nat a) ltac:(lia) a ltac:(lia) eq_refl) as (k & Hk & Hl & Hb & Hlow).
exists (k + 1). split; [lia|]. split.
{ rewrite lowbit_double, Hl. unfold bit. rewrite Z.pow_add_r by lia. lia. }
split.
{ replace (k + 1) with (Z.succ k) by lia. rewrite Z.testbit_even_succ by lia. exact Hb. }
intros j Hj. destruct (Z.eq_dec j 0) as [->|Hne].
+ apply Z.testbit_even_0.
+ replace j with (Z.succ (j - 1)) by lia. rewrite Z.testbit_even_succ by lia. apply Hlow. lia.
- subst m. exists 0. split; [lia|]. split; [apply lowbit_odd|]. split.
+ apply Z.testbit_odd_0.
+ intros j Hj. lia.
Qed.
Lemma ctz32_bit k : 0 <= k -> ctz32 (bit k) = k.
Proof.
intros Hk. unfold ctz32.
pose proof (lowbit_spec (bit k) ltac:(unfold bit; apply Z.pow_pos_nonneg; lia)) as (k' & Hk' & Hl & Hb & _).
rewrite Hl. rewrite testbit_bit in Hb by lia. apply Z.eqb_eq in Hb. subst k'.
unfold bit. apply Z.log2_pow2. exact Hk.
Qed.
Lemma testbit_false_of_lt m n i : 0 <= m < 2 ^ n -> 0 <= n <= i -> Z.testbit m i = false.
Proof.
intros Hm Hi. destruct (Z.eq_dec m 0) as [->|Hne]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Z.log2 m < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma lt_pow2_of_testbit m n : 0 <= m -> 0 <= n ->
(forall i, n <= i -> Z.testbit m i = false) -> m < 2 ^ n.
Proof.
intros Hm Hn H. destruct (Z.eq_dec m 0) as [->|Hne]; [apply Z.pow_pos_nonneg; lia|].
destruct (Z_lt_dec m (2 ^ n)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
assert (Hl : n <= Z.log2 m) by (apply Z.log2_le_pow2; lia).
pose proof (Z.bit_log2 m ltac:(lia)) as Hb. rewrite H in Hb; [discriminate | exact Hl].
Qed.
