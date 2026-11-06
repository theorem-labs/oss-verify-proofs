(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG04.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac cbnz := cbn -[Z.add Z.mul Z.sub Z.div Z.modulo Z.of_nat Z.to_nat Z.shiftl Z.shiftr Z.pow Z.max Z.min Z.leb Z.ltb Z.eqb Z.le Z.lt].
Tactic Notation "cbnz" "in" hyp(H) := cbn -[Z.add Z.mul Z.sub Z.div Z.modulo Z.of_nat Z.to_nat Z.shiftl Z.shiftr Z.pow Z.max Z.min Z.leb Z.ltb Z.eqb Z.le Z.lt] in H.
Tactic Notation "cbnz" "in" "*" := cbn -[Z.add Z.mul Z.sub Z.div Z.modulo Z.of_nat Z.to_nat Z.shiftl Z.shiftr Z.pow Z.max Z.min Z.leb Z.ltb Z.eqb Z.le Z.lt] in *.
Lemma lupd_length {X} : forall (l : list X) i v, length (lupd l i v) = length l.
Proof. induction l as [|h t IH]; intros [|i] v; cbn; auto. Qed.
Lemma nth_lupd_same {X} : forall (l : list X) i v d, (i < length l)%nat -> nth i (lupd l i v) d = v.
Proof. induction l as [|h t IH]; intros [|i] v d Hi; cbn in *; try lia; auto. apply IH. lia. Qed.
Lemma nth_lupd_other {X} : forall (l : list X) i j v d, i <> j -> nth j (lupd l i v) d = nth j l d.
Proof.
induction l as [|h t IH]; intros [|i] [|j] v d Hij; cbn; auto; try congruence.
Qed.
Lemma nth_error_lupd_same {X} : forall (l : list X) i v, (i < length l)%nat -> nth_error (lupd l i v) i = Some v.
Proof. induction l as [|h t IH]; intros [|i] v Hi; cbn in *; try lia; auto. apply IH. lia. Qed.
Lemma nth_error_lupd_other {X} : forall (l : list X) i j v, i <> j -> nth_error (lupd l i v) j = nth_error l j.
Proof.
induction l as [|h t IH]; intros [|i] [|j] v Hij; cbn; auto; try congruence.
Qed.
Lemma zupd_length {X} : forall i (v : X) l, length (zupd i v l) = length l.
Proof. intros. apply lupd_length. Qed.
Lemma znth_zupd_same {X} : forall (d : X) i v l, 0 <= i -> (Z.to_nat i < length l)%nat -> znth d i (zupd i v l) = v.
Proof. intros d i v l Hi Hl. unfold znth, zupd. apply nth_lupd_same. exact Hl. Qed.
Lemma znth_zupd_other {X} : forall (d : X) i j v l, 0 <= i -> 0 <= j -> i <> j -> znth d j (zupd i v l) = znth d j l.
Proof. intros d i j v l Hi Hj Hij. unfold znth, zupd. apply nth_lupd_other. intros E. apply Hij. lia. Qed.
Lemma reg_set_regions : forall v s c, reg (set_regions v s) c = znth region0 c v.
Proof. reflexivity. Qed.
Lemma cache_set_cache : forall v s c, cache (set_cache v s) c = znth pclass0 c v.
Proof. reflexivity. Qed.
Lemma reg_upd_same : forall s c r, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
reg (set_regions (zupd c r (st_regions s)) s) c = r.
Proof. intros. unfold reg. cbn. apply znth_zupd_same; assumption. Qed.
Lemma reg_upd_other : forall s c c' r, 0 <= c -> 0 <= c' -> c <> c' ->
reg (set_regions (zupd c r (st_regions s)) s) c' = reg s c'.
Proof. intros. unfold reg. cbn. apply znth_zupd_other; assumption. Qed.
Lemma cache_upd_same : forall s c p, 0 <= c -> (Z.to_nat c < length (st_cache s))%nat ->
cache (set_cache (zupd c p (st_cache s)) s) c = p.
Proof. intros. unfold cache. cbn. apply znth_zupd_same; assumption. Qed.
Lemma cache_upd_other : forall s c c' p, 0 <= c -> 0 <= c' -> c <> c' ->
cache (set_cache (zupd c p (st_cache s)) s) c' = cache s c'.
Proof. intros. unfold cache. cbn. apply znth_zupd_other; assumption. Qed.
Lemma NoDup_app_iff {X} : forall (l1 l2 : list X),
NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ (forall x, In x l1 -> In x l2 -> False).
Proof.
induction l1 as [|a l1 IH]; intros l2; cbn.
- split; [intros H; repeat split; auto; constructor | intros (_ & H & _); exact H].
- split.
+ intros H. inversion H as [|? ? Hni Hnd]; subst. apply IH in Hnd as (H1 & H2 & H3).
split; [constructor; [intros Hin; apply Hni; apply in_app_iff; auto | exact H1]|].
split; [exact H2|]. intros x [<-|Hx] Hx2; [apply Hni; apply in_app_iff; auto | eauto].
+ intros (H1 & H2 & H3). inversion H1 as [|? ? Hni Hnd]; subst. constructor.
* intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [auto | exact (H3 a (or_introl eq_refl) Hin)].
* apply IH. repeat split; auto. intros x Hx Hx2. exact (H3 x (or_intror Hx) Hx2).
Qed.
Lemma NoDup_Permutation {X} : forall (l l' : list X), Permutation l l' -> NoDup l -> NoDup l'.
Proof. intros l l' HP H. exact (Permutation_NoDup HP H). Qed.
Lemma Forall_Permutation {X} : forall (P : X -> Prop) l l', Permutation l l' -> Forall P l -> Forall P l'.
Proof.
intros P l l' HP H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hx].
Qed.
Lemma NoDup_cons_perm_notin {X} : forall (x : X) l l', NoDup l -> Permutation l (x :: l') -> ~ In x l' /\ NoDup l'.
Proof.
intros x l l' Hnd HP. pose proof (Permutation_NoDup HP Hnd) as H. inversion H; subst. auto.
Qed.
Lemma removelast_app_last {X} : forall (l : list X) d, l <> [] -> removelast l ++ [last l d] = l.
Proof.
induction l as [|a [|b t] IH]; intros d Hne; [congruence | reflexivity |].
cbn [removelast]. change (last (a :: b :: t) d) with (last (b :: t) d). cbn [app]. f_equal. apply IH. discriminate.
Qed.
Lemma removelast_length {X} : forall (l : list X), l <> [] -> length (removelast l) = (length l - 1)%nat.
Proof.
induction l as [|a [|b t] IH]; intros Hne; [congruence | reflexivity |].
change (length (removelast (a :: b :: t))) with (S (length (removelast (b :: t)))).
rewrite IH; [cbn; lia | discriminate].
Qed.
Lemma length_nonnil {X} : forall (l : list X), l <> [] -> (1 <= length l)%nat.
Proof. intros [|a t] H; [congruence | cbn; lia]. Qed.
Lemma firstn_skipn_perm {X} : forall n (l : list X), Permutation l (skipn n l ++ firstn n l).
Proof. intros n l. rewrite <- (firstn_skipn n l) at 1. apply Permutation_app_comm. Qed.
Lemma fold_right_add_app : forall {X} (f : X -> Z) (l1 l2 : list X),
fold_right (fun x acc => f x + acc) 0 (l1 ++ l2) = fold_right (fun x acc => f x + acc) 0 l1 + fold_right (fun x acc => f x + acc) 0 l2.
Proof. intros X f l1 l2. induction l1 as [|a t IH]; cbn; [reflexivity | rewrite IH; lia]. Qed.
Lemma fold_right_add_nonneg : forall {X} (f : X -> Z) (l : list X),
Forall (fun x => 0 <= f x) l -> 0 <= fold_right (fun x acc => f x + acc) 0 l.
Proof. intros X f l H. induction H; cbn; lia. Qed.
Lemma fold_right_add_perm : forall {X} (f : X -> Z) (l l' : list X),
Permutation l l' -> fold_right (fun x acc => f x + acc) 0 l = fold_right (fun x acc => f x + acc) 0 l'.
Proof. intros X f l l' HP. induction HP; cbn; try lia. Qed.
Lemma multiples_bound : forall sz A (l : list Z),
0 < sz -> 0 <= A -> A mod sz = 0 ->
NoDup l -> Forall (fun o => 0 <= o < A /\ o mod sz = 0) l ->
sz * Z.of_nat (length l) <= A.
Proof.
intros sz A l Hsz HA HAm Hnd Hall.
set (q := fun o : Z => Z.to_nat (o / sz)).
assert (Hinj : forall x y, In x l -> In y l -> q x = q y -> x = y).
{ intros x y Hx Hy Hq. pose proof (proj1 (Forall_forall _ _) Hall x Hx) as [Bx Mx].
pose proof (proj1 (Forall_forall _ _) Hall y Hy) as [By My]. unfold q in Hq.
apply Z.mod_divide in Mx as [kx ->]; [|lia]. apply Z.mod_divide in My as [ky ->]; [|lia].
rewrite !Z.div_mul in Hq by lia. f_equal. nia. }
assert (Hincl : incl (map q l) (seq 0 (Z.to_nat (A / sz)))).
{ intros i Hi. apply in_map_iff in Hi as (x & <- & Hx). apply in_seq.
pose proof (proj1 (Forall_forall _ _) Hall x Hx) as [Bx Mx]. unfold q.
assert (0 <= x / sz) by (apply Z.div_pos; lia).
assert (x / sz < A / sz).
{ apply Z.mod_divide in Mx as [k ->]; [|lia]. apply Z.mod_divide in HAm as [kA E]; [|lia]. rewrite E.
rewrite !Z.div_mul by lia. nia. }
lia. }
assert (Hnd' : NoDup (map q l)).
{ apply NoDup_map_NoDup_ForallPairs; [|exact Hnd]. intros x y Hx Hy Hq. apply Hinj; assumption. }
pose proof (NoDup_incl_length Hnd' Hincl) as Hlen. rewrite length_map, length_seq in Hlen.
pose proof (Z.div_mod A sz ltac:(lia)). pose proof (Z.div_pos A sz HA Hsz). nia.
Qed.
Lemma run_elems_length : forall lo sz k, length (run_elems lo sz k) = k.
Proof. intros lo sz k. revert lo. induction k as [|k IH]; intros lo; cbnz; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma In_run_elems : forall x lo sz k, In x (run_elems lo sz k) <-> exists i, (i < k)%nat /\ x = lo + Z.of_nat i * sz.
Proof.
intros x lo sz k. revert lo. induction k as [|k IH]; intros lo; cbnz.
- split; [intros [] | intros (i & Hi & _); lia].
- split.
+ intros [<-|H]; [exists 0%nat; split; [lia|cbnz; lia]|].
apply IH in H as (i & Hi & ->). exists (S i). split; [lia|]. rewrite Nat2Z.inj_succ. lia.
+ intros (i & Hi & ->). destruct i as [|i]; [left; cbnz; lia | right].
apply IH. exists i. split; [lia|]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma run_elems_bounds : forall lo sz k, 0 < sz -> 0 <= lo -> lo mod sz = 0 ->
Forall (fun o => lo <= o < lo + Z.of_nat k * sz /\ o mod sz = 0) (run_elems lo sz k).
Proof.
intros lo sz k Hsz Hlo Hm. apply Forall_forall. intros x Hx. apply In_run_elems in Hx as (i & Hi & ->).
split; [nia|]. rewrite Z.add_mod, Hm, Z_mod_mult by lia. reflexivity.
Qed.
Lemma run_elems_NoDup : forall lo sz k, 0 < sz -> NoDup (run_elems lo sz k).
Proof.
intros lo sz k Hsz. revert lo. induction k as [|k IH]; intros lo; cbnz; constructor; [|apply IH].
intros H. apply In_run_elems in H as (i & Hi & E). nia.
Qed.
Definition runs_ok (l : list fseg) : Prop := Forall (fun f => match f with FRun lo k => 1 <= k | FOne _ => True end) l.
Lemma fa_len_nonneg : forall l, runs_ok l -> 0 <= fa_len l.
Proof. intros l H. induction H as [|[lo k|o] t Hf Ht IH]; cbnz; lia. Qed.
Lemma fa_elems_cons_run : forall sz lo k t, fa_elems sz (FRun lo k :: t) = run_elems lo sz (Z.to_nat k) ++ fa_elems sz t.
Proof. reflexivity. Qed.
Lemma fa_elems_cons_one : forall sz o t, fa_elems sz (FOne o :: t) = o :: fa_elems sz t.
Proof. reflexivity. Qed.
Lemma fa_elems_length : forall sz l, runs_ok l -> Z.of_nat (length (fa_elems sz l)) = fa_len l.
Proof.
intros sz l H. induction H as [|[lo k|o] t Hf Ht IH]; [reflexivity| |].
- rewrite fa_elems_cons_run, length_app, run_elems_length, Nat2Z.inj_add, IH, Z2Nat.id; [cbnz; lia | lia].
- rewrite fa_elems_cons_one. cbn [length]. rewrite Nat2Z.inj_succ, IH. cbnz. lia.
Qed.
Lemma fa_pop_spec : forall sz l off l', runs_ok l -> fa_pop sz l = Some (off, l') ->
fa_elems sz l = off :: fa_elems sz l' /\ fa_len l' = fa_len l - 1 /\ runs_ok l'.
Proof.
intros sz l off l' Hr. induction Hr as [|[lo k|o] t Hf Ht IH]; cbn [fa_pop]; intros H.
- discriminate.
- destruct (k <=? 0) eqn:Ek; [apply Z.leb_le in Ek; lia|]. apply Z.leb_gt in Ek.
injection H as <- El'. destruct (k =? 1) eqn:E1.
+ apply Z.eqb_eq in E1. subst k l'. rewrite fa_elems_cons_run. cbn [Z.to_nat Pos.to_nat run_elems app fa_len]. repeat split; auto; lia.
+ apply Z.eqb_neq in E1. subst l'. rewrite !fa_elems_cons_run.
replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia. cbn [run_elems app fa_len].
replace (lo + Z.of_nat 0 * sz) with lo by lia.
split; [reflexivity|]. split; [lia|]. constructor; [lia | exact Ht].
- injection H as <- <-. rewrite fa_elems_cons_one. cbn [fa_len]. repeat split; auto. lia.
Qed.
Lemma fa_pop_None : forall sz l, runs_ok l -> fa_pop sz l = None -> fa_len l = 0.
Proof.
intros sz l Hr. induction Hr as [|[lo k|o] t Hf Ht IH]; cbn [fa_pop]; intros H; [reflexivity| |discriminate].
destruct (k <=? 0) eqn:Ek; [apply Z.leb_le in Ek; lia | discriminate].
Qed.
Lemma fa_pop_n_spec : forall fuel sz n l acc tops rest,
runs_ok l -> 0 <= n -> fa_pop_n fuel sz n l acc = Some (tops, rest) ->
rev acc ++ fa_elems sz l = tops ++ fa_elems sz rest /\ fa_len rest = fa_len l - n /\ runs_ok rest /\
Z.of_nat (length tops) = Z.of_nat (length acc) + n.
Proof.
induction fuel as [|fuel IH]; intros sz n l acc tops rest Hr Hn H; cbn [fa_pop_n] in H; [discriminate|].
destruct (n <=? 0) eqn:En.
- apply Z.leb_le in En. injection H as <- <-. repeat split; auto; [lia|]. rewrite length_rev. lia.
- apply Z.leb_gt in En. destruct (fa_pop sz l) as [[off l']|] eqn:Ep; [|discriminate].
destruct (fa_pop_spec sz l off l' Hr Ep) as (E1 & E2 & R').
destruct (IH sz (n - 1) l' (off :: acc) tops rest R' ltac:(lia) H) as (A1 & A2 & A3 & A4).
cbn [rev] in A1. rewrite <- app_assoc in A1. cbn [app] in A1. rewrite E1.
split; [exact A1|]. split; [lia|]. split; [exact A3|]. cbn [length] in A4. lia.
Qed.
Lemma fa_push_list_spec : forall sz l offs,
fa_elems sz (fa_push_list l offs) = rev offs ++ fa_elems sz l /\
fa_len (fa_push_list l offs) = fa_len l + Z.of_nat (length offs) /\ (runs_ok l -> runs_ok (fa_push_list l offs)).
Proof.
intros sz l offs. revert l. induction offs as [|o t IH]; intros l; cbn [fa_push_list rev length].
- repeat split; auto. cbn. lia.
- destruct (IH (FOne o :: l)) as (E1 & E2 & E3). rewrite E1, E2, fa_elems_cons_one. cbn [fa_len]. rewrite <- app_assoc. cbn [app].
split; [reflexivity|]. split; [lia|]. intros Hr. apply E3. constructor; [exact I | exact Hr].
Qed.
Lemma sptr_eqb_spec : forall p q, sptr_eqb p q = true <-> p = q.
Proof.
intros p q. destruct p, q; cbn; try (split; [discriminate | congruence]); rewrite ?Bool.andb_true_iff, ?Z.eqb_eq, ?Nat.eqb_eq.
- split; reflexivity.
- split; [intros ->; reflexivity | intros H; injection H; auto].
- split; [intros [-> ->]; reflexivity | intros H; injection H; auto].
- split; [intros [-> ->]; reflexivity | intros H; injection H; auto].
Qed.
Lemma sptr_eqb_refl : forall p, sptr_eqb p p = true.
Proof. intros p. apply sptr_eqb_spec. reflexivity. Qed.
Lemma find_user_spec : forall l p k, find_user l p = Some k -> In k l /\ ck_user k = p.
Proof.
induction l as [|k' t IH]; intros p k H; cbn in H; [discriminate|].
destruct (sptr_eqb (ck_user k') p) eqn:E.
- injection H as <-. apply sptr_eqb_spec in E. split; [left; reflexivity | exact E].
- apply IH in H as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.
Lemma find_user_None : forall l p, find_user l p = None -> forall k, In k l -> ck_user k <> p.
Proof.
induction l as [|k' t IH]; intros p H k Hk; cbn in H; [destruct Hk|].
destruct (sptr_eqb (ck_user k') p) eqn:E; [discriminate|].
destruct Hk as [<-|Hk]; [intros E'; apply sptr_eqb_spec in E'; congruence | apply IH; assumption].
Qed.
Lemma upd_chunk_fresh : forall l k, ~ In (ck_beg k) (map ck_beg l) -> upd_chunk l k = l ++ [k].
Proof.
induction l as [|k' t IH]; intros k H; cbn; [reflexivity|].
destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:E.
- exfalso. apply H. left. apply sptr_eqb_spec in E. exact E.
- rewrite IH; [reflexivity|]. intros Hin. apply H. right. exact Hin.
Qed.
Lemma upd_chunk_present : forall l1 k0 l2 k, ck_beg k0 = ck_beg k -> ~ In (ck_beg k) (map ck_beg l1) ->
upd_chunk (l1 ++ k0 :: l2) k = l1 ++ k :: l2.
Proof.
induction l1 as [|k' t IH]; intros k0 l2 k Hb H; cbn.
- rewrite Hb, sptr_eqb_refl. reflexivity.
- destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:E.
+ exfalso. apply H. left. apply sptr_eqb_spec in E. exact E.
+ rewrite IH; [reflexivity | exact Hb | intros Hin; apply H; right; exact Hin].
Qed.
Lemma del_chunk_present : forall l1 k0 l2, ~ In (ck_beg k0) (map ck_beg l1) ->
del_chunk (l1 ++ k0 :: l2) (ck_beg k0) = l1 ++ l2.
Proof.
induction l1 as [|k' t IH]; intros k0 l2 H; cbn.
- rewrite sptr_eqb_refl. reflexivity.
- destruct (sptr_eqb (ck_beg k') (ck_beg k0)) eqn:E.
+ exfalso. apply H. left. apply sptr_eqb_spec in E. exact E.
+ rewrite IH; [reflexivity | intros Hin; apply H; right; exact Hin].
Qed.
Lemma In_split_beg : forall (l : list chunk) k, In k l -> NoDup (map ck_beg l) ->
exists l1 l2, l = l1 ++ k :: l2 /\ ~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof.
intros l k Hin Hnd. apply in_split in Hin as (l1 & l2 & ->). exists l1, l2. split; [reflexivity|].
rewrite map_app in Hnd. cbn in Hnd. apply NoDup_app_iff in Hnd as (H1 & H2 & H3).
inversion H2; subst. split; [|assumption]. intros H. exact (H3 _ H (or_introl eq_refl)).
Qed.
Lemma mem_chunk_spec : forall k l, mem_chunk k l = true <-> In k l.
Proof.
intros k l. induction l as [|k' t IH]; cbn; [split; [discriminate | intros []]|].
rewrite Bool.orb_true_iff, IH, !Bool.andb_true_iff, sptr_eqb_spec, Z.eqb_eq. split.
- intros [((Hb & Hr) & Hs)|H]; [left | right; exact H].
destruct k' as [b' r' s'], k as [b r s0]; cbn in *. subst. destruct s', s0; try discriminate; reflexivity.
- intros [E|H]; [left; subst k' | right; exact H]. destruct k as [b r s0]; cbn. destruct s0; auto.
Qed.
Lemma blocks_app : forall l1 l2 s, st_chunks s = l1 ++ l2 ->
blocks s = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2).
Proof. intros l1 l2 s H. unfold blocks. rewrite H, filter_app, map_app. reflexivity. Qed.
Lemma In_blocks : forall s p n, In (p, n) (blocks s) <-> exists k, In k (st_chunks s) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Proof.
intros s p n. unfold blocks. rewrite in_map_iff. split.
- intros (k & E & Hk). apply filter_In in Hk as [Hk Ha]. injection E as <- <-. exists k.
unfold is_alloc in Ha. destruct (ck_state k) eqn:Es; [|discriminate]. auto.
- intros (k & Hk & Hs & <- & <-). exists k. split; [reflexivity|]. apply filter_In. unfold is_alloc. rewrite Hs. auto.
Qed.
