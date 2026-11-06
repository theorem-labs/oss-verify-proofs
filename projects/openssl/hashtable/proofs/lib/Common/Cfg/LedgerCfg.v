(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Finite.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intro w. exact (bv_unsigned_in_range _ w). Qed.

Lemma u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma u64_id : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intro w. apply bv_eq. rewrite u64_lit; [reflexivity | apply u64_range]. Qed.

Lemma bv_eqb_refl_true : forall (w : word), bv_eqb w w = true.
Proof. intro w. apply bv_eqb_eq. reflexivity. Qed.

Lemma bv_eqb_false_iff : forall (a b : word), bv_eqb a b = false <-> a <> b.
Proof.
  intros a b. destruct (bv_eqb a b) eqn:E.
  - apply bv_eqb_eq in E. split; [discriminate | intro H; contradiction].
  - split; [| reflexivity]. intros _ Hab. apply bv_eqb_eq in Hab. congruence.
Qed.

Lemma bv_eqb_false_unsigned : forall (a b : word),
  bv_unsigned a <> bv_unsigned b -> bv_eqb a b = false.
Proof. intros a b H. apply bv_eqb_false_iff. intros ->. apply H. reflexivity. Qed.

Lemma entry_eq_dec_prop : forall p q : word * word, p = q \/ p <> q.
Proof.
  intros [a n] [b s].
  destruct (bv_eqb a b) eqn:E1; destruct (bv_eqb n s) eqn:E2.
  - apply bv_eqb_eq in E1, E2. subst. left. reflexivity.
  - right. intros H. inversion H; subst. rewrite bv_eqb_refl_true in E2. discriminate.
  - right. intros H. inversion H; subst. rewrite bv_eqb_refl_true in E1. discriminate.
  - right. intros H. inversion H; subst. rewrite bv_eqb_refl_true in E1. discriminate.
Qed.

(* [comment removed for export] *)
Definition e_lo (p : word * word) : Z := bv_unsigned (fst p).
Definition e_sz (p : word * word) : Z := bv_unsigned (snd p).
Definition e_hi (p : word * word) : Z := e_lo p + e_sz p.

(* [comment removed for export] *)
Definition e_disj (p q : word * word) : Prop := e_hi p <= e_lo q \/ e_hi q <= e_lo p.

(* [comment removed for export] *)
Definition e_inside (q p : word * word) : Prop := e_lo p <= e_lo q /\ e_hi q <= e_hi p.

Lemma e_sz_nonneg : forall p, 0 <= e_sz p.
Proof. intro p. unfold e_sz. pose proof (u64_range (snd p)). lia. Qed.

Lemma e_lo_nonneg : forall p, 0 <= e_lo p.
Proof. intro p. unfold e_lo. pose proof (u64_range (fst p)). lia. Qed.

Lemma e_disj_sym : forall p q, e_disj p q -> e_disj q p.
Proof. intros p q [H | H]; [right | left]; exact H. Qed.

Lemma e_disj_inside : forall p q r, e_disj p q -> e_inside r q -> e_disj p r.
Proof.
  intros p q r [H | H] [H1 H2]; unfold e_disj.
  - left. lia.
  - right. lia.
Qed.

Lemma iv_overlap_false_iff : forall a1 n1 a2 n2,
  iv_overlap a1 n1 a2 n2 = false <-> e_disj (a1, n1) (a2, n2).
Proof.
  intros a1 n1 a2 n2. unfold iv_overlap, e_disj, e_hi, e_lo, e_sz. cbn [fst snd].
  rewrite andb_false_iff, !Z.ltb_ge. tauto.
Qed.

Lemma region_free_iff : forall l a n,
  region_free l a n = true <-> Forall (e_disj (a, n)) l.
Proof.
  induction l as [|[b s] l IH]; intros a n; cbn [region_free].
  - split; [constructor | reflexivity].
  - rewrite andb_true_iff, negb_true_iff, iv_overlap_false_iff, IH. split.
    + intros [H1 H2]. constructor; assumption.
    + intros H. inversion H; subst. split; assumption.
Qed.

Lemma region_free_app : forall l1 l2 a n,
  region_free (l1 ++ l2) a n = region_free l1 a n && region_free l2 a n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 a n; cbn [app region_free]; [reflexivity|].
  rewrite IH, andb_assoc. reflexivity.
Qed.

Lemma region_free_In_disj : forall l a n p,
  region_free l a n = true -> In p l -> e_disj (a, n) p.
Proof.
  intros l a n p H Hin. apply region_free_iff in H. rewrite Forall_forall in H. exact (H p Hin).
Qed.

(* [comment removed for export] *)
Lemma region_free_sub : forall l a n a' n',
  region_free l a n = true ->
  e_inside (a', n') (a, n) ->
  region_free l a' n' = true.
Proof.
  intros l a n a' n' H Hin. apply region_free_iff. apply region_free_iff in H.
  eapply Forall_impl; [| exact H]. intros p Hp.
  apply e_disj_sym. eapply e_disj_inside; [apply e_disj_sym; exact Hp | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma reserved_top_ge : forall R p, In p R -> e_hi p <= reserved_top R.
Proof.
  induction R as [|[b s] R IH]; intros p Hin; [contradiction|].
  cbn [reserved_top]. destruct Hin as [<- | Hin].
  - unfold e_hi, e_lo, e_sz. cbn [fst snd]. lia.
  - specialize (IH p Hin). lia.
Qed.

Lemma region_free_above_top : forall R a n,
  reserved_top R <= bv_unsigned a -> region_free R a n = true.
Proof.
  intros R a n H. apply region_free_iff. apply Forall_forall. intros p Hin.
  right. pose proof (reserved_top_ge R p Hin). unfold e_lo. cbn [fst]. lia.
Qed.

(* [comment removed for export] *)

Fixpoint pw_disj (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | p :: r => Forall (e_disj p) r /\ pw_disj r
  end.

Lemma pw_disj_In : forall l p q,
  pw_disj l -> In p l -> In q l -> p <> q -> e_disj p q.
Proof.
  induction l as [|x l IH]; intros p q Hd Hp Hq Hne; [contradiction|].
  destruct Hd as [Hx Hl]. rewrite Forall_forall in Hx.
  destruct Hp as [<- | Hp]; destruct Hq as [<- | Hq].
  - congruence.
  - apply Hx. exact Hq.
  - apply e_disj_sym. apply Hx. exact Hp.
  - apply IH; assumption.
Qed.

Lemma pw_disj_app_iff : forall l1 l2,
  pw_disj (l1 ++ l2) <->
  pw_disj l1 /\ pw_disj l2 /\ (forall p q, In p l1 -> In q l2 -> e_disj p q).
Proof.
  induction l1 as [|x l1 IH]; intros l2; cbn [app pw_disj].
  - split; [intros H; repeat split; [exact H | intros p q []] | intros (_ & H & _); exact H].
  - rewrite IH, Forall_app, !Forall_forall. split.
    + intros ((H1 & H2) & H3 & H4 & H5). repeat split; try assumption.
      intros p q [<- | Hp] Hq; [apply H2; exact Hq | apply H5; assumption].
    + intros ((H1 & H2) & H3 & H4). repeat split; try assumption.
      * intros q Hq. apply H4; [left; reflexivity | exact Hq].
      * intros p q Hp Hq. apply H4; [right; exact Hp | exact Hq].
Qed.

Lemma pw_disj_remove_mid : forall l1 p l2, pw_disj (l1 ++ p :: l2) -> pw_disj (l1 ++ l2).
Proof.
  intros l1 p l2 H. apply pw_disj_app_iff in H as (H1 & H2 & H3).
  apply pw_disj_app_iff. cbn [pw_disj] in H2. destruct H2 as [_ H2].
  repeat split; try assumption. intros a b Ha Hb. apply H3; [exact Ha | right; exact Hb].
Qed.

Lemma filter_all_true {A} (f : A -> bool) : forall l,
  (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  simpl. pose proof (H x (or_introl eq_refl)) as Hx.
  destruct (f x); [| discriminate Hx]. f_equal. apply IH.
  intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
Lemma e_disj_base_neq : forall p q,
  e_disj p q -> 0 < e_sz p -> 0 < e_sz q -> fst p <> fst q.
Proof.
  intros p q Hd Hp Hq Heq. unfold e_disj, e_hi, e_lo in Hd. rewrite Heq in Hd. lia.
Qed.

(* [comment removed for export] *)
Lemma map_remove_exact : forall l1 l2 a n,
  pw_disj (l1 ++ (a, n) :: l2) ->
  Forall (fun p => 0 < e_sz p) (l1 ++ (a, n) :: l2) ->
  map_remove (l1 ++ (a, n) :: l2) a = l1 ++ l2.
Proof.
  intros l1 l2 a n Hd Hpos. unfold map_remove.
  rewrite Forall_forall in Hpos.
  assert (Hother : forall q, In q (l1 ++ l2) -> negb (bv_eqb (fst q) a) = true).
  { intros q Hq. apply negb_true_iff, bv_eqb_false_iff.
    assert (Hq' : In q (l1 ++ (a, n) :: l2)).
    { apply in_app_iff in Hq as [Hq | Hq]; apply in_app_iff; [left | right; right]; exact Hq. }
    assert (Han : In (a, n) (l1 ++ (a, n) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    assert (Hne : q <> (a, n)).
    { intros ->. apply pw_disj_app_iff in Hd as (H1 & H2 & H3). cbn [pw_disj] in H2.
      destruct H2 as [H2 _]. rewrite Forall_forall in H2.
      pose proof (Hpos (a, n) Han) as Hp.
      apply in_app_iff in Hq as [Hq | Hq].
      - specialize (H3 (a, n) (a, n) Hq (or_introl eq_refl)).
        unfold e_disj, e_hi in H3. lia.
      - specialize (H2 (a, n) Hq). unfold e_disj, e_hi in H2. lia. }
    exact (e_disj_base_neq q (a, n) (pw_disj_In _ _ _ Hd Hq' Han Hne) (Hpos q Hq') (Hpos _ Han)). }
  rewrite List.filter_app. cbn [List.filter fst]. rewrite bv_eqb_refl_true. cbn [negb].
  rewrite (filter_all_true _ l1), (filter_all_true _ l2); [reflexivity | |];
    intros x Hx; apply Hother; apply in_app_iff; [right | left]; exact Hx.
Qed.

Lemma map_has_In : forall l a n, map_has l a n = true <-> In (a, n) l.
Proof.
  intros l a n. unfold map_has. rewrite existsb_exists. split.
  - intros ([b s] & Hin & Hb). cbn [fst snd] in Hb.
    apply andb_true_iff in Hb as [H1 H2]. apply bv_eqb_eq in H1, H2. subst. exact Hin.
  - intros Hin. exists (a, n). split; [exact Hin |]. cbn [fst snd].
    rewrite !bv_eqb_refl_true. reflexivity.
Qed.

Lemma map_contains_intro : forall l a n p,
  In p l -> e_inside (a, n) p -> map_contains l a n = true.
Proof.
  intros l a n p Hin [H1 H2]. unfold map_contains. apply existsb_exists.
  exists p. split; [exact Hin |].
  unfold e_lo, e_hi, e_lo, e_sz in *. cbn [fst snd] in *.
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof.
  induction l1 as [|[a s] l1 IH]; intros l2; cbn [app live_bytes]; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof.
  induction l as [|[a s] l IH]; cbn [live_bytes]; [lia|].
  pose proof (u64_range s). lia.
Qed.

Lemma live_bytes_cons : forall p l, live_bytes (p :: l) = e_sz p + live_bytes l.
Proof. intros [a s] l. reflexivity. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disj : forall a sz lo hi,
  lo <= hi -> 0 < bv_unsigned sz ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hlh Hpos Hd. unfold iv_subtract.
  pose proof (u64_range a). pose proof (u64_range sz).
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite Z.min_l by lia. rewrite u64_id. reflexivity.
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    rewrite Z.max_l by lia. cbn [app].
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !u64_id. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_inside : forall a sz lo hi,
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_pieces : forall a sz lo hi q,
  lo <= hi -> hi < 2 ^ 64 -> 0 < bv_unsigned sz ->
  In q (iv_subtract a sz lo hi) ->
  0 < e_sz q /\ e_inside q (a, sz) /\ (e_hi q <= lo \/ hi <= e_lo q).
Proof.
  intros a sz lo hi q Hlh Hhi Hszpos Hin. unfold iv_subtract in Hin.
  pose proof (u64_range a). pose proof (u64_range sz).
  apply in_app_iff in Hin as [Hin | Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [| contradiction]. apply Z.ltb_lt in E.
    destruct Hin as [<- | []].
    unfold e_sz, e_inside, e_hi, e_lo, e_sz. cbn [fst snd].
    rewrite u64_lit by lia.
    split; [lia | split; [split; lia | left; lia]].
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [| contradiction]. apply Z.ltb_lt in E.
    destruct Hin as [<- | []].
    unfold e_sz, e_inside, e_hi, e_lo, e_sz. cbn [fst snd].
    rewrite !u64_lit by lia.
    split; [lia | split; [split; lia | right; lia]].
Qed.

Lemma maps_subtract_In : forall l lo hi q,
  lo <= hi -> hi < 2 ^ 64 ->
  Forall (fun p => 0 < e_sz p) l ->
  In q (maps_subtract l lo hi) ->
  exists p, In p l /\ 0 < e_sz q /\ e_inside q p /\ (e_hi q <= lo \/ hi <= e_lo q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hlh Hhi Hpos Hin; [contradiction|].
  inversion Hpos as [| ? ? Hp0 Hposl]; subst.
  cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin | Hin].
  - exists (a, sz). split; [left; reflexivity |].
    exact (iv_subtract_pieces a sz lo hi q Hlh Hhi Hp0 Hin).
  - destruct (IH lo hi q Hlh Hhi Hposl Hin) as (p & Hp & H).
    exists p. split; [right; exact Hp | exact H].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_id : forall l lo hi,
  lo <= hi ->
  Forall (fun p => 0 < e_sz p /\ (e_hi p <= lo \/ hi <= e_lo p)) l ->
  maps_subtract l lo hi = l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh H; [reflexivity|].
  inversion H as [| ? ? [Hpos Hd] Hl]; subst. cbn [maps_subtract].
  rewrite iv_subtract_disj; [| exact Hlh | exact Hpos | exact Hd].
  cbn [app]. f_equal. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Definition e_inside_cut_b (lo hi : Z) (p : word * word) : bool :=
  (lo <=? e_lo p) && (e_hi p <=? hi).

Lemma maps_subtract_filter : forall l lo hi,
  lo <= hi ->
  Forall (fun p => 0 < e_sz p /\
                   ((lo <= e_lo p /\ e_hi p <= hi) \/ e_hi p <= lo \/ hi <= e_lo p)) l ->
  maps_subtract l lo hi = List.filter (fun p => negb (e_inside_cut_b lo hi p)) l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh H; [reflexivity|].
  inversion H as [| ? ? [Hpos Hc] Hl]; subst. cbn [maps_subtract List.filter].
  rewrite (IH lo hi Hlh Hl).
  set (tl := List.filter (fun p => negb (e_inside_cut_b lo hi p)) l).
  unfold e_inside_cut_b. unfold e_hi, e_lo, e_sz in *. cbn [fst snd] in *.
  destruct Hc as [[H1 H2] | Hd].
  - rewrite iv_subtract_inside by lia.
    rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
  - rewrite iv_subtract_disj by (first [exact Hlh | exact Hpos | exact Hd]).
    assert (E : (lo <=? bv_unsigned a) && (bv_unsigned a + bv_unsigned sz <=? hi) = false).
    { apply andb_false_iff. destruct Hd as [Hd | Hd]; [left | right]; apply Z.leb_gt; lia. }
    rewrite E. reflexivity.
Qed.

Lemma live_bytes_iv_subtract_le : forall a sz lo hi,
  lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (u64_range a). pose proof (u64_range sz).
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    try apply Z.ltb_lt in E1; try apply Z.ltb_lt in E2;
    try apply Z.ltb_ge in E1; try apply Z.ltb_ge in E2;
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l lo hi,
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; cbn [maps_subtract live_bytes]; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh).
  specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts l,
  live_bytes (maps_subtract_all l cuts) <= live_bytes l.
Proof.
  induction cuts as [|[a n] cuts IH]; intros l; cbn [maps_subtract_all]; [lia|].
  etransitivity; [apply IH |]. apply live_bytes_maps_subtract_le.
  pose proof (u64_range n). lia.
Qed.

Lemma live_bytes_map_remove_le : forall l a, live_bytes (map_remove l a) <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a; [cbn; lia|].
  unfold map_remove. cbn [List.filter fst]. fold (map_remove l a).
  pose proof (u64_range s). specialize (IH a).
  destruct (negb (bv_eqb b a)); cbn [live_bytes]; lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le : forall m,
  vm_backing_used m
  <= live_bytes (vm_maps (m_vmmaps m))
     + Z.of_nat (length (m_vm_materialized m)) * page_size.
Proof.
  intros m. unfold vm_backing_used, vm_backed_maps.
  pose proof (live_bytes_maps_subtract_all_le (m_vm_lazy m)
                (maps_subtract_all (vm_maps (m_vmmaps m)) (vm_noaccess (m_vmmaps m)))).
  pose proof (live_bytes_maps_subtract_all_le (vm_noaccess (m_vmmaps m)) (vm_maps (m_vmmaps m))).
  lia.
Qed.

Lemma vm_backing_used_le_live : forall m,
  m_vm_materialized m = [] ->
  vm_backing_used m <= live_bytes (vm_maps (m_vmmaps m)).
Proof.
  intros m Hmat. pose proof (vm_backing_used_le m) as H. rewrite Hmat in H. cbn in H. lia.
Qed.

Lemma vm_backing_used_nonneg : forall m, 0 <= vm_backing_used m.
Proof.
  intros m. unfold vm_backing_used.
  pose proof (live_bytes_nonneg (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m))).
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition z_conflict (nZ x : Z) (p : word * word) : Prop :=
  x < e_hi p /\ e_lo p < x + nZ.

Definition z_conflictb (nZ x : Z) (p : word * word) : bool :=
  (x <? e_hi p) && (e_lo p <? x + nZ).

Lemma z_conflictb_spec : forall nZ x p, z_conflictb nZ x p = true <-> z_conflict nZ x p.
Proof.
  intros. unfold z_conflictb, z_conflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma region_free_of_no_conflict : forall l x nZ,
  0 <= x -> 0 <= nZ -> x + nZ < 2 ^ 64 ->
  (forall p, In p l -> ~ z_conflict nZ x p) ->
  region_free l (Z_to_bv 64 x) (Z_to_bv 64 nZ) = true.
Proof.
  intros l x nZ Hx Hn Hw H. apply region_free_iff. apply Forall_forall. intros p Hin.
  specialize (H p Hin). unfold z_conflict in H. unfold e_disj.
  assert (Hlo : e_lo (Z_to_bv 64 x, Z_to_bv 64 nZ) = x)
    by (unfold e_lo; cbn [fst]; apply u64_lit; lia).
  assert (Hhi : e_hi (Z_to_bv 64 x, Z_to_bv 64 nZ) = x + nZ)
    by (unfold e_hi, e_lo, e_sz; cbn [fst snd]; rewrite !u64_lit by lia; reflexivity).
  rewrite Hlo, Hhi. lia.
Qed.

(* [comment removed for export] *)
Lemma NoDup_interval_length : forall (ks : list Z) u v,
  List.NoDup ks -> (forall k, In k ks -> u <= k <= v) ->
  Z.of_nat (length ks) <= Z.max 0 (v - u + 1).
Proof.
  intros ks u v Hnd Hin.
  set (univ := map (fun i => u + Z.of_nat i) (seq 0 (Z.to_nat (v - u + 1)))).
  assert (Hincl : incl ks univ).
  { intros k Hk. specialize (Hin k Hk). unfold univ. apply in_map_iff.
    exists (Z.to_nat (k - u)). split; [lia |]. apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  unfold univ in Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

(* [comment removed for export] *)
Lemma conflicts_bound : forall F nZ p (ks : list Z),
  0 <= nZ -> List.NoDup ks ->
  Z.of_nat (length (List.filter (fun k => z_conflictb nZ (F + 4096 * k) p) ks))
  <= (e_sz p + nZ) / 4096 + 1.
Proof.
  intros F nZ p ks Hn Hnd.
  pose proof (e_sz_nonneg p) as Hs.
  set (X := e_lo p - nZ - F). set (Y := e_hi p - F).
  assert (Hin : forall k, In k (List.filter (fun k => z_conflictb nZ (F + 4096 * k) p) ks) ->
                          X / 4096 + 1 <= k <= (Y - 1) / 4096).
  { intros k Hk. apply List.filter_In in Hk as [_ Hk]. apply z_conflictb_spec in Hk.
    destruct Hk as [H1 H2]. unfold X, Y. split.
    - assert ((e_lo p - nZ - F) / 4096 < k) by (apply Z.div_lt_upper_bound; lia). lia.
    - apply Z.div_le_lower_bound; lia. }
  pose proof (NoDup_interval_length _ _ _ (List.NoDup_filter _ Hnd) Hin) as Hlen.
  assert (HY : Y = X + (e_sz p + nZ)) by (unfold X, Y, e_hi; lia).
  assert (Hb : (Y - 1) / 4096 - (X / 4096 + 1) + 1 <= (e_sz p + nZ) / 4096 + 1).
  { rewrite HY. Z.div_mod_to_equations. lia. }
  assert (0 <= (e_sz p + nZ) / 4096) by (apply Z.div_pos; lia).
  lia.
Qed.

Fixpoint blocked_sum (nZ : Z) (l : list (word * word)) : Z :=
  match l with
  | [] => 0
  | p :: r => ((e_sz p + nZ) / 4096 + 1) + blocked_sum nZ r
  end.

Lemma blocked_sum_le : forall nZ l,
  0 <= nZ ->
  blocked_sum nZ l <= (live_bytes l + Z.of_nat (length l) * nZ) / 4096 + Z.of_nat (length l).
Proof.
  intros nZ l Hn. induction l as [|p l IH]; [cbn; lia|].
  cbn [blocked_sum length]. rewrite live_bytes_cons.
  pose proof (e_sz_nonneg p). pose proof (live_bytes_nonneg l).
  rewrite Nat2Z.inj_succ.
  assert (H1 : (e_sz p + nZ) / 4096 + (live_bytes l + Z.of_nat (length l) * nZ) / 4096
               <= (e_sz p + live_bytes l + Z.succ (Z.of_nat (length l)) * nZ) / 4096).
  { replace (e_sz p + live_bytes l + Z.succ (Z.of_nat (length l)) * nZ)
      with ((e_sz p + nZ) + (live_bytes l + Z.of_nat (length l) * nZ)) by lia.
    generalize (e_sz p + nZ) (live_bytes l + Z.of_nat (length l) * nZ). intros u v.
    Z.div_mod_to_equations. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma pigeonhole_free_candidate : forall F nZ l (ks : list Z),
  0 <= nZ -> List.NoDup ks ->
  blocked_sum nZ l < Z.of_nat (length ks) ->
  exists k, In k ks /\ forall p, In p l -> ~ z_conflict nZ (F + 4096 * k) p.
Proof.
  intros F nZ l. induction l as [|p l IH]; intros ks Hn Hnd Hlen.
  - destruct ks as [|k ks]; [cbn in Hlen; lia |].
    exists k. split; [left; reflexivity | intros p []].
  - cbn [blocked_sum] in Hlen.
    set (f := fun k => z_conflictb nZ (F + 4096 * k) p).
    set (ks' := List.filter (fun k => negb (f k)) ks).
    assert (Hsplit : (length (List.filter f ks) + length ks' = length ks)%nat).
    { unfold ks'. clear. induction ks as [|k ks IHk]; [reflexivity|].
      cbn [List.filter]. destruct (f k); cbn [negb length]; lia. }
    pose proof (conflicts_bound F nZ p ks Hn Hnd) as Hb. fold f in Hb.
    destruct (IH ks' Hn (List.NoDup_filter _ Hnd) ltac:(lia)) as (k & Hk & Hfree).
    unfold ks' in Hk. apply List.filter_In in Hk as [Hk Hnf].
    exists k. split; [exact Hk |]. intros q [<- | Hq].
    + intros Hc. apply z_conflictb_spec in Hc. unfold f in Hnf. rewrite Hc in Hnf. discriminate.
    + apply Hfree. exact Hq.
Qed.

(* [comment removed for export] *)
Theorem grant_candidate_exists : forall (l : list (word * word)) (F nZ C T top : Z),
  0 < F -> F mod 4096 = 0 ->
  0 <= nZ ->
  Z.of_nat (length l) <= C ->
  live_bytes l <= T ->
  F + T + C * (nZ + 4096) + nZ <= top ->
  top < 2 ^ 64 ->
  exists a : word,
    bv_unsigned a mod page_size = 0 /\ F <= bv_unsigned a /\
    bv_unsigned a + nZ <= top /\
    region_free l a (Z_to_bv 64 nZ) = true.
Proof.
  intros l F nZ C T top HF HFal Hn HC HT Hband Htop.
  pose proof (live_bytes_nonneg l) as Hlb.
  set (K := (live_bytes l + Z.of_nat (length l) * nZ) / 4096 + Z.of_nat (length l)).
  assert (HK0 : 0 <= K).
  { unfold K. assert (0 <= (live_bytes l + Z.of_nat (length l) * nZ) / 4096)
      by (apply Z.div_pos; nia). lia. }
  set (ks := map Z.of_nat (seq 0 (S (Z.to_nat K)))).
  assert (Hnd : List.NoDup ks).
  { unfold ks. apply Stdlib.Lists.Finite.Injective_map_NoDup; [intros x y; apply Nat2Z.inj | apply seq_NoDup]. }
  assert (Hlen : blocked_sum nZ l < Z.of_nat (length ks)).
  { unfold ks. rewrite length_map, length_seq. pose proof (blocked_sum_le nZ l Hn). fold K in H. lia. }
  destruct (pigeonhole_free_candidate F nZ l ks Hn Hnd Hlen) as (k & Hk & Hfree).
  assert (Hkr : 0 <= k <= K).
  { unfold ks in Hk. apply in_map_iff in Hk as (i & <- & Hi). apply in_seq in Hi. lia. }
  assert (H4K : 4096 * K <= live_bytes l + Z.of_nat (length l) * nZ + 4096 * Z.of_nat (length l)).
  { unfold K. generalize (live_bytes l + Z.of_nat (length l) * nZ). intro u.
    Z.div_mod_to_equations. lia. }
  assert (Hx : F + 4096 * k + nZ <= top) by nia.
  exists (Z_to_bv 64 (F + 4096 * k)).
  rewrite u64_lit by lia. repeat split.
  - unfold page_size. rewrite Z.add_mod, HFal, Z.mul_comm, Z_mod_mult by lia. reflexivity.
  - lia.
  - exact Hx.
  - apply region_free_of_no_conflict; [lia | lia | lia | exact Hfree].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_lo_bound : Z := sp_window_lo - stack_max_size.

Lemma alloc_lo_bound_val : alloc_lo_bound = 140735332483072.
Proof. reflexivity. Qed.

Record ledger_inv (R : list (word * word)) (L c S : Z) (h : VmMaps) : Prop := mk_ledger_inv {
  li_reserved : vm_reserved h = R;
  li_limit    : L <= vm_limit h;            (* [comment removed for export] *)
  li_sp_lo    : sp_window_lo <= bv_unsigned (vm_init_sp h);
  li_sp_hi    : bv_unsigned (vm_init_sp h) <= sp_window_hi;
  li_pos      : Forall (fun p => 0 < e_sz p) (vm_maps h);
  li_aligned  : Forall (fun p => e_lo p mod page_size = 0 /\ e_sz p mod page_size = 0) (vm_maps h);
  li_top      : Forall (fun p => 0 < e_lo p /\ e_hi p <= alloc_top h) (vm_maps h);
  li_disj_R   : Forall (fun p => Forall (e_disj p) R) (vm_maps h);
  li_disj     : pw_disj (vm_maps h);
  li_count    : Z.of_nat (length (vm_maps h)) <= c;
  li_size     : live_bytes (vm_maps h) <= S;
  li_noacc    : Forall (fun q => 0 < e_sz q /\ exists p, In p (vm_maps h) /\ e_inside q p)
                       (vm_noaccess h);
  li_brk_pos  : 0 < bv_unsigned (vm_brk h);
  li_brk_al   : bv_unsigned (vm_brk h) mod page_size = 0;
  li_brk_min  : bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h);
  li_brk_R    : reserved_top R <= bv_unsigned (vm_start_brk h)
}.

Lemma ledger_inv_weaken : forall R L c S c' S' h,
  ledger_inv R L c S h -> c <= c' -> S <= S' -> ledger_inv R L c' S' h.
Proof.
  intros R L c S c' S' h [] Hc HS. constructor; try assumption; lia.
Qed.

Lemma ledger_inv_alloc_top : forall R L c S h,
  ledger_inv R L c S h -> alloc_lo_bound <= alloc_top h /\ alloc_top h < TASK_SIZE.
Proof.
  intros R L c S h []. unfold alloc_lo_bound, alloc_top, TASK_SIZE, sp_window_hi, stack_max_size in *.
  lia.
Qed.

Lemma ledger_inv_params_nonneg : forall R L c S h,
  ledger_inv R L c S h -> 0 <= c /\ 0 <= S.
Proof.
  intros R L c S h []. pose proof (live_bytes_nonneg (vm_maps h)). lia.
Qed.

(* [comment removed for export] *)
Lemma ledger_inv_init : forall segs brk0 mbase sp lim inp,
  valid_sp sp -> valid_brk segs brk0 ->
  0 < reserved_top (segments_reserved segs) ->
  ledger_inv (segments_reserved segs) lim 0 0
    (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros segs brk0 mbase sp lim inp (Hs1 & Hs2 & _) (Hb1 & _ & Hb3) HR.
  change (m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp))
    with (mkVmMapsFull (segments_reserved segs) [] [] brk0 brk0 lim mbase sp).
  constructor; cbn [vm_reserved vm_limit vm_init_sp vm_maps vm_noaccess vm_brk vm_start_brk
                    length live_bytes pw_disj];
    try solve [constructor | reflexivity | assumption | lia].
Qed.

(* [comment removed for export] *)

Definition ledger_grant (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) (vm_noaccess h)
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition ledger_unmap (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition ledger_guard (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
    ((a, n) :: maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition ledger_brk_grow (req : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((vm_brk h, Z_to_bv 64 (bv_unsigned req - bv_unsigned (vm_brk h)))
                                :: vm_maps h)
    (vm_noaccess h) (vm_start_brk h) req (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Lemma alloc_top_same_sp : forall h h', vm_init_sp h' = vm_init_sp h -> alloc_top h' = alloc_top h.
Proof. intros h h' H. unfold alloc_top. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ledger_inv_cons_entry : forall R L c S h a n nacc sb b,
  ledger_inv R L c S h ->
  0 < bv_unsigned n ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned a -> bv_unsigned a + bv_unsigned n <= alloc_top h ->
  region_free (R ++ vm_maps h) a n = true ->
  (* [comment removed for export] *)
  Forall (fun q => 0 < e_sz q /\ exists p, In p ((a, n) :: vm_maps h) /\ e_inside q p) nacc ->
  0 < bv_unsigned b -> bv_unsigned b mod page_size = 0 ->
  bv_unsigned sb <= bv_unsigned b -> reserved_top R <= bv_unsigned sb ->
  ledger_inv R L (c + 1) (S + bv_unsigned n)
    (mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) nacc sb b
                  (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros R L c S h a n nacc sb b [] Hn Ha1 Hn1 Ha0 Htop Hfree Hnacc Hb0 Hb1 Hsb HsbR.
  rewrite region_free_app in Hfree. apply andb_true_iff in Hfree as [HfR Hfm].
  apply region_free_iff in HfR, Hfm.
  constructor; cbn [vm_reserved vm_limit vm_init_sp vm_maps vm_noaccess vm_brk vm_start_brk];
    try assumption.
  - constructor; [exact Hn | assumption].
  - constructor; [split; assumption | assumption].
  - constructor.
    + unfold e_lo, e_hi, e_lo, e_sz. cbn [fst snd]. split; [exact Ha0 |].
      unfold alloc_top in *. cbn [vm_init_sp]. exact Htop.
    + eapply Forall_impl; [| exact li_top0]. intros p Hp. unfold alloc_top in *. cbn [vm_init_sp]. exact Hp.
  - constructor; assumption.
  - cbn [pw_disj]. split; assumption.
  - cbn [length]. lia.
  - rewrite live_bytes_cons. unfold e_sz. cbn [snd]. lia.
Qed.

Lemma noacc_weaken_cons : forall (e : word * word) maps nacc,
  Forall (fun q => 0 < e_sz q /\ exists p, In p maps /\ e_inside q p) nacc ->
  Forall (fun q => 0 < e_sz q /\ exists p, In p (e :: maps) /\ e_inside q p) nacc.
Proof.
  intros e maps nacc H. eapply Forall_impl; [| exact H]. intros q (Hq & p & Hp & Hin).
  split; [exact Hq |]. exists p. split; [right; exact Hp | exact Hin].
Qed.

(* [comment removed for export] *)
Theorem ledger_inv_grant : forall R L c S h a nZ,
  ledger_inv R L c S h ->
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top h ->
  region_free (R ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  ledger_inv R L (c + 1) (S + nZ) (ledger_grant a (Z_to_bv 64 nZ) h).
Proof.
  intros R L c S h a nZ Hinv Hn Hnal Haal Ha Htop Hfree.
  pose proof (alloc_top_lt h) as Hlt. unfold two_pow_64 in Hlt.
  assert (Hu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  pose proof (ledger_inv_cons_entry R L c S h a (Z_to_bv 64 nZ) (vm_noaccess h)
                (vm_start_brk h) (vm_brk h) Hinv) as H.
  rewrite Hu in H. pose proof Hinv as [].
  unfold ledger_grant.
  exact (H Hn Haal Hnal Ha Htop Hfree (noacc_weaken_cons _ _ _ li_noacc0)
           li_brk_pos0 li_brk_al0 li_brk_min0 li_brk_R0).
Qed.

(* [comment removed for export] *)
Theorem ledger_inv_brk_grow : forall R L c S h req,
  ledger_inv R L c S h ->
  bv_unsigned (vm_brk h) < bv_unsigned req ->
  bv_unsigned req mod page_size = 0 ->
  bv_unsigned req <= alloc_top h ->
  region_free (R ++ vm_maps h) (vm_brk h)
    (Z_to_bv 64 (bv_unsigned req + page_size - bv_unsigned (vm_brk h))) = true ->
  ledger_inv R L (c + 1) (S + (bv_unsigned req - bv_unsigned (vm_brk h))) (ledger_brk_grow req h).
Proof.
  intros R L c S h req Hinv Hlt Hal Htop Hfree.
  pose proof (alloc_top_page_lt h) as Hat. unfold two_pow_64 in Hat.
  pose proof (u64_range (vm_brk h)) as Hb. pose proof (u64_range req) as Hr.
  pose proof Hinv as [].
  set (d := bv_unsigned req - bv_unsigned (vm_brk h)).
  assert (Hu : bv_unsigned (Z_to_bv 64 d) = d) by (apply u64_lit; unfold d; lia).
  pose proof (ledger_inv_cons_entry R L c S h (vm_brk h) (Z_to_bv 64 d) (vm_noaccess h)
                (vm_start_brk h) req Hinv) as H.
  rewrite Hu in H. unfold ledger_brk_grow. fold d.
  assert (Hdpos : 0 < d) by (unfold d; lia).
  assert (Hdal : d mod page_size = 0).
  { unfold d, page_size in *. rewrite Zminus_mod, Hal, li_brk_al0. reflexivity. }
  assert (Hdtop : bv_unsigned (vm_brk h) + d <= alloc_top h) by (unfold d; lia).
  assert (Hfree' : region_free (R ++ vm_maps h) (vm_brk h) (Z_to_bv 64 d) = true).
  { eapply region_free_sub; [exact Hfree |].
    unfold e_inside, e_hi, e_lo, e_sz. cbn [fst snd]. rewrite Hu.
    rewrite u64_lit by (unfold page_size in *; lia). unfold page_size, d. lia. }
  assert (Hreq0 : 0 < bv_unsigned req) by (clear - Hlt Hb; lia).
  assert (Hsb : bv_unsigned (vm_start_brk h) <= bv_unsigned req)
    by (clear - Hlt li_brk_min0; lia).
  exact (H Hdpos li_brk_al0 Hdal li_brk_pos0 Hdtop Hfree' (noacc_weaken_cons _ _ _ li_noacc0)
           Hreq0 Hal Hsb li_brk_R0).
Qed.

(* [comment removed for export] *)
Theorem ledger_inv_unmap : forall R L c S h a n,
  ledger_inv R L c S h ->
  In (a, n) (vm_maps h) ->
  ledger_inv R L (c - 1) (S - bv_unsigned n) (ledger_unmap a n h).
Proof.
  intros R L c S h a n Hinv Hin. pose proof Hinv as [].
  destruct (in_split _ _ Hin) as (l1 & l2 & Hsplit).
  assert (Hrem : map_remove (vm_maps h) a = l1 ++ l2).
  { rewrite Hsplit. apply map_remove_exact; rewrite <- Hsplit; assumption. }
  assert (Hsub : forall p, In p (l1 ++ l2) -> In p (vm_maps h)).
  { intros p Hp. rewrite Hsplit. apply in_app_iff in Hp as [Hp | Hp]; apply in_app_iff;
      [left | right; right]; exact Hp. }
  assert (Hfa : forall (P : word * word -> Prop), Forall P (vm_maps h) -> Forall P (l1 ++ l2)).
  { intros P HP. rewrite Forall_forall in *. intros p Hp. apply HP, Hsub, Hp. }
  unfold ledger_unmap. rewrite Hrem.
  constructor; cbn [vm_reserved vm_limit vm_init_sp vm_maps vm_noaccess vm_brk vm_start_brk].
  - exact li_reserved0.
  - exact li_limit0.
  - exact li_sp_lo0.
  - exact li_sp_hi0.
  - apply Hfa. exact li_pos0.
  - apply Hfa. exact li_aligned0.
  - apply Hfa. eapply Forall_impl; [| exact li_top0]. intros p Hp.
    unfold alloc_top in *. cbn [vm_init_sp]. exact Hp.
  - apply Hfa. exact li_disj_R0.
  - rewrite Hsplit in li_disj0. eapply pw_disj_remove_mid. exact li_disj0.
  - rewrite Hsplit in li_count0. rewrite length_app in *. cbn [length] in li_count0. lia.
  - rewrite Hsplit in li_size0. rewrite live_bytes_app in *. rewrite live_bytes_cons in li_size0.
    unfold e_sz in li_size0. cbn [snd] in li_size0. lia.
  - (* [comment removed for export] *)
    apply Forall_forall. intros q Hq.
    pose proof (u64_range n) as Hnr.
    assert (Hnapos : Forall (fun p => 0 < e_sz p) (vm_noaccess h)).
    { eapply Forall_impl; [| exact li_noacc0]. intros x [Hx _]. exact Hx. }
    assert (Hhi : bv_unsigned a + bv_unsigned n < 2 ^ 64).
    { rewrite Forall_forall in li_top0. destruct (li_top0 (a, n) Hin) as [_ Ht].
      pose proof (alloc_top_lt h) as Hlt. unfold two_pow_64 in Hlt.
      unfold e_hi, e_lo, e_sz in Ht. cbn [fst snd] in Ht. lia. }
    assert (Hlh : bv_unsigned a <= bv_unsigned a + bv_unsigned n) by lia.
    destruct (maps_subtract_In (vm_noaccess h) _ _ q Hlh Hhi Hnapos Hq)
      as (q0 & Hq0 & Hqpos & Hqin & Hqout).
    split; [exact Hqpos |].
    rewrite Forall_forall in li_noacc0. destruct (li_noacc0 q0 Hq0) as (_ & p & Hp & Hq0p).
    exists p. split.
    + (* [comment removed for export] *)
      assert (Hne : p <> (a, n)).
      { intros ->. destruct Hqin as [Hi1 Hi2]. destruct Hq0p as [Hj1 Hj2].
        unfold e_hi, e_lo, e_sz in *. cbn [fst snd] in *. lia. }
      rewrite Hsplit in Hp. apply in_app_iff in Hp as [Hp | [Hp | Hp]];
        [apply in_app_iff; left; exact Hp | congruence | apply in_app_iff; right; exact Hp].
    + destruct Hqin as [Hi1 Hi2]. destruct Hq0p as [Hj1 Hj2]. split; lia.
  - exact li_brk_pos0.
  - exact li_brk_al0.
  - exact li_brk_min0.
  - exact li_brk_R0.
Qed.

(* [comment removed for export] *)
Lemma ledger_unmap_noaccess_id : forall R L c S h a n,
  ledger_inv R L c S h ->
  In (a, n) (vm_maps h) ->
  (forall q, In q (vm_noaccess h) -> ~ e_inside q (a, n)) ->
  maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = vm_noaccess h.
Proof.
  intros R L c S h a n [] Hin Hnone. pose proof (u64_range n) as Hnr.
  apply maps_subtract_id; [lia |].
  apply Forall_forall. intros q Hq. rewrite Forall_forall in li_noacc0.
  destruct (li_noacc0 q Hq) as (Hqpos & p & Hp & Hqp). split; [exact Hqpos |].
  destruct (entry_eq_dec_prop p (a, n)) as [-> | Hne].
  - exfalso. exact (Hnone q Hq Hqp).
  - pose proof (pw_disj_In _ _ _ li_disj0 Hp Hin Hne) as Hd.
    pose proof (e_disj_inside _ _ _ (e_disj_sym _ _ Hd) Hqp) as Hd'.
    clear - Hd' Hnr.
    destruct Hd' as [Hd' | Hd']; [right | left];
      unfold e_hi, e_lo, e_sz in *; cbn [fst snd] in *; lia.
Qed.

(* [comment removed for export] *)
Theorem ledger_inv_guard : forall R L c S h a n p,
  ledger_inv R L c S h ->
  In p (vm_maps h) -> e_inside (a, n) p -> 0 < bv_unsigned n ->
  ledger_inv R L c S (ledger_guard a n h).
Proof.
  intros R L c S h a n p Hinv Hp Hin Hn. pose proof Hinv as [].
  pose proof (u64_range n) as Hnr.
  assert (Hhi : bv_unsigned a + bv_unsigned n < 2 ^ 64).
  { rewrite Forall_forall in li_top0. destruct (li_top0 p Hp) as [_ Ht].
    pose proof (alloc_top_lt h) as Hlt. unfold two_pow_64 in Hlt.
    destruct Hin as [_ Hi]. unfold e_hi at 1, e_lo, e_sz in Hi. cbn [fst snd] in Hi.
    clear - Ht Hlt Hi. lia. }
  unfold ledger_guard.
  constructor; cbn [vm_reserved vm_limit vm_init_sp vm_maps vm_noaccess vm_brk vm_start_brk];
    try assumption.
  constructor.
  - split; [exact Hn |]. exists p. split; assumption.
  - apply Forall_forall. intros q Hq.
    assert (Hnapos : Forall (fun p => 0 < e_sz p) (vm_noaccess h)).
    { eapply Forall_impl; [| exact li_noacc0]. intros x [Hx _]. exact Hx. }
    assert (Hlh : bv_unsigned a <= bv_unsigned a + bv_unsigned n) by (clear - Hnr; lia).
    destruct (maps_subtract_In (vm_noaccess h) _ _ q Hlh Hhi Hnapos Hq)
      as (q0 & Hq0 & Hqpos & Hqin & _).
    split; [exact Hqpos |].
    rewrite Forall_forall in li_noacc0. destruct (li_noacc0 q0 Hq0) as (_ & p' & Hp' & Hq0p).
    exists p'. split; [exact Hp' |].
    destruct Hqin as [Hi1 Hi2]. destruct Hq0p as [Hj1 Hj2]. split; lia.
Qed.

(* [comment removed for export] *)

Definition ledger_grant_na (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition ledger_expose (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h)
    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
Theorem ledger_inv_grant_na : forall R L c S h a nZ,
  ledger_inv R L c S h ->
  0 < nZ -> nZ mod page_size = 0 ->
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
  bv_unsigned a + nZ <= alloc_top h ->
  region_free (R ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
  ledger_inv R L (c + 1) (S + nZ) (ledger_grant_na a (Z_to_bv 64 nZ) h).
Proof.
  intros R L c S h a nZ Hinv Hn Hnal Haal Ha Htop Hfree.
  pose proof (alloc_top_lt h) as Hlt. unfold two_pow_64 in Hlt.
  assert (Hu : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  pose proof (ledger_inv_cons_entry R L c S h a (Z_to_bv 64 nZ)
                ((a, Z_to_bv 64 nZ) :: vm_noaccess h) (vm_start_brk h) (vm_brk h) Hinv) as H.
  rewrite Hu in H. pose proof Hinv as [].
  unfold ledger_grant_na.
  refine (H Hn Haal Hnal Ha Htop Hfree _ li_brk_pos0 li_brk_al0 li_brk_min0 li_brk_R0).
  constructor.
  - split; [unfold e_sz; cbn [snd]; rewrite Hu; exact Hn |].
    exists (a, Z_to_bv 64 nZ). split; [left; reflexivity | split; lia].
  - apply noacc_weaken_cons. exact li_noacc0.
Qed.

(* [comment removed for export] *)
Theorem ledger_inv_expose : forall R L c S h a n,
  ledger_inv R L c S h ->
  bv_unsigned a + bv_unsigned n < 2 ^ 64 ->
  ledger_inv R L c S (ledger_expose a n h).
Proof.
  intros R L c S h a n Hinv Hhi. pose proof Hinv as [].
  pose proof (u64_range n) as Hnr.
  unfold ledger_expose.
  constructor; cbn [vm_reserved vm_limit vm_init_sp vm_maps vm_noaccess vm_brk vm_start_brk];
    try assumption.
  apply Forall_forall. intros q Hq.
  assert (Hnapos : Forall (fun p => 0 < e_sz p) (vm_noaccess h)).
  { eapply Forall_impl; [| exact li_noacc0]. intros x [Hx _]. exact Hx. }
  assert (Hlh : bv_unsigned a <= bv_unsigned a + bv_unsigned n) by (clear - Hnr; lia).
  destruct (maps_subtract_In (vm_noaccess h) _ _ q Hlh Hhi Hnapos Hq)
    as (q0 & Hq0 & Hqpos & Hqin & _).
  split; [exact Hqpos |].
  rewrite Forall_forall in li_noacc0. destruct (li_noacc0 q0 Hq0) as (_ & p' & Hp' & Hq0p).
  exists p'. split; [exact Hp' |].
  destruct Hqin as [Hi1 Hi2]. destruct Hq0p as [Hj1 Hj2]. split; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_grant_b (m : Model) (a : word) (nZ : Z) : bool :=
  let h := m_vmmaps m in
  (bv_unsigned a mod page_size =? 0) && (0 <? bv_unsigned a)
  && (bv_unsigned a + nZ <=? alloc_top h)
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ)
  && (vm_backing_used m + nZ <=? vm_limit h).

Lemma mmap_grant_b_iff : forall m a nZ,
  mmap_grant_b m a nZ = true <->
  (bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a
   /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps m)
   /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 nZ) = true
   /\ vm_backing_used m + nZ <= vm_limit (m_vmmaps m)).
Proof.
  intros m a nZ. unfold mmap_grant_b. cbv zeta.
  rewrite !andb_true_iff, Z.eqb_eq, Z.ltb_lt, !Z.leb_le. tauto.
Qed.

(* [comment removed for export] *)
Theorem mmap_grant_exists_inv : forall R L c S m nZ,
  ledger_inv R L c S (m_vmmaps m) ->
  0 <= nZ ->
  page_size + (live_bytes R + S) + (Z.of_nat (length R) + c) * (nZ + page_size) + nZ
    <= alloc_lo_bound ->
  vm_backing_used m + nZ <= L ->
  exists a, mmap_grant_b m a nZ = true.
Proof.
  intros R L c S m nZ Hinv Hn Hband Hbud.
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hinv) as [Hlo _].
  pose proof (alloc_top_lt (m_vmmaps m)) as Hlt. unfold two_pow_64 in Hlt.
  pose proof Hinv as [].
  destruct (grant_candidate_exists (R ++ vm_maps (m_vmmaps m)) page_size nZ
              (Z.of_nat (length R) + c) (live_bytes R + S) (alloc_top (m_vmmaps m)))
    as (a & Ha1 & Ha2 & Ha3 & Ha4).
  - unfold page_size. lia.
  - reflexivity.
  - exact Hn.
  - rewrite length_app, Nat2Z.inj_add. clear - li_count0. lia.
  - rewrite live_bytes_app. clear - li_size0. lia.
  - unfold page_size in *. clear - Hband Hlo. lia.
  - exact Hlt.
  - exists a. apply mmap_grant_b_iff. rewrite li_reserved0.
    unfold page_size in Ha2. repeat split; try assumption; [clear - Ha2; lia | clear - Hbud li_limit0; lia].
Qed.

(* [comment removed for export] *)
Theorem mmap_grant_exists_inv_lim : forall R L c S m nZ,
  ledger_inv R L c S (m_vmmaps m) ->
  0 <= nZ ->
  page_size + (live_bytes R + S) + (Z.of_nat (length R) + c) * (nZ + page_size) + nZ
    <= alloc_lo_bound ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m) ->
  exists a, mmap_grant_b m a nZ = true.
Proof.
  intros R L c S m nZ Hinv Hn Hband Hbud.
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hinv) as [Hlo _].
  pose proof (alloc_top_lt (m_vmmaps m)) as Hlt. unfold two_pow_64 in Hlt.
  pose proof Hinv as [].
  destruct (grant_candidate_exists (R ++ vm_maps (m_vmmaps m)) page_size nZ
              (Z.of_nat (length R) + c) (live_bytes R + S) (alloc_top (m_vmmaps m)))
    as (a & Ha1 & Ha2 & Ha3 & Ha4).
  - unfold page_size. lia.
  - reflexivity.
  - exact Hn.
  - rewrite length_app, Nat2Z.inj_add. clear - li_count0. lia.
  - rewrite live_bytes_app. clear - li_size0. lia.
  - unfold page_size in *. clear - Hband Hlo. lia.
  - exact Hlt.
  - exists a. apply mmap_grant_b_iff. rewrite li_reserved0.
    unfold page_size in Ha2. repeat split; try assumption. clear - Ha2. lia.
Qed.

(* [comment removed for export] *)
Corollary mmap_grant_exists_inv_acct : forall R L c S m nZ,
  ledger_inv R L c S (m_vmmaps m) ->
  m_vm_materialized m = [] ->
  0 <= nZ ->
  page_size + (live_bytes R + S) + (Z.of_nat (length R) + c) * (nZ + page_size) + nZ
    <= alloc_lo_bound ->
  S + nZ <= L ->
  exists a, mmap_grant_b m a nZ = true.
Proof.
  intros R L c S m nZ Hinv Hmat Hn Hband Hbud.
  apply (mmap_grant_exists_inv R L c S m nZ Hinv Hn Hband).
  pose proof (vm_backing_used_le_live m Hmat) as Hu.
  pose proof (li_size _ _ _ _ _ Hinv) as Hs. lia.
Qed.

(* [comment removed for export] *)
Definition mmap_grant_na_b (h : VmMaps) (a : word) (nZ : Z) : bool :=
  (bv_unsigned a mod page_size =? 0) && (0 <? bv_unsigned a)
  && (bv_unsigned a + nZ <=? alloc_top h)
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

Lemma mmap_grant_na_b_iff : forall h a nZ,
  mmap_grant_na_b h a nZ = true <->
  (bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a
   /\ bv_unsigned a + nZ <= alloc_top h
   /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true).
Proof.
  intros h a nZ. unfold mmap_grant_na_b.
  rewrite !andb_true_iff, Z.eqb_eq, Z.ltb_lt, Z.leb_le. tauto.
Qed.

Theorem mmap_grant_na_exists_inv : forall R L c S h nZ,
  ledger_inv R L c S h ->
  0 <= nZ ->
  page_size + (live_bytes R + S) + (Z.of_nat (length R) + c) * (nZ + page_size) + nZ
    <= alloc_lo_bound ->
  exists a, mmap_grant_na_b h a nZ = true.
Proof.
  intros R L c S h nZ Hinv Hn Hband.
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hinv) as [Hlo _].
  pose proof (alloc_top_lt h) as Hlt. unfold two_pow_64 in Hlt.
  pose proof Hinv as [].
  destruct (grant_candidate_exists (R ++ vm_maps h) page_size nZ
              (Z.of_nat (length R) + c) (live_bytes R + S) (alloc_top h))
    as (a & Ha1 & Ha2 & Ha3 & Ha4).
  - unfold page_size. lia.
  - reflexivity.
  - exact Hn.
  - rewrite length_app, Nat2Z.inj_add. clear - li_count0. lia.
  - rewrite live_bytes_app. clear - li_size0. lia.
  - unfold page_size in *. clear - Hband Hlo. lia.
  - exact Hlt.
  - exists a. apply mmap_grant_na_b_iff. rewrite li_reserved0.
    unfold page_size in Ha2. repeat split; try assumption. clear - Ha2. lia.
Qed.

Lemma budget_of_inv_acct : forall R L c S m nZ,
  ledger_inv R L c S (m_vmmaps m) ->
  m_vm_materialized m = [] ->
  S + nZ <= L ->
  vm_backing_used m + nZ <= vm_limit (m_vmmaps m).
Proof.
  intros R L c S m nZ Hinv Hmat Hb.
  pose proof (vm_backing_used_le_live m Hmat) as Hu.
  pose proof (li_size _ _ _ _ _ Hinv) as Hs. pose proof (li_limit _ _ _ _ _ Hinv). lia.
Qed.

(* [comment removed for export] *)

Lemma page_round_up_Z_aligned : forall x, x mod page_size = 0 -> page_round_up_Z x = x.
Proof.
  intros x H. unfold page_round_up_Z, page_size in *. Z.div_mod_to_equations. lia.
Qed.

Lemma page_round_up_Z_ge : forall x, x <= page_round_up_Z x.
Proof. intros x. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Lemma page_round_up_Z_lt : forall x, page_round_up_Z x < x + page_size.
Proof. intros x. unfold page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Lemma page_round_up_Z_mod : forall x, page_round_up_Z x mod page_size = 0.
Proof. intros x. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_pos : forall x, 0 < x -> 0 < page_round_up_Z x.
Proof. intros x H. pose proof (page_round_up_Z_ge x). lia. Qed.

Lemma bv_sub_no_wrap : forall (x y : word),
  bv_unsigned y <= bv_unsigned x ->
  bv_sub x y = Z_to_bv 64 (bv_unsigned x - bv_unsigned y).
Proof. intros x y _. reflexivity. Qed.

(* [comment removed for export] *)
Lemma brk_model_next_same : forall h req, brk_model_next h req (vm_brk h) = h.
Proof.
  intros h req. unfold brk_model_next, brk_maps_next, brk_grants, brk_is_grow, brk_unmaps,
    brk_page_range, maps_subtract_ranges.
  rewrite (Z.ltb_irrefl (bv_unsigned (vm_brk h))), !andb_false_r.
  rewrite Z.ltb_irrefl. cbn [app].
  destruct (0 <? bv_unsigned (vm_brk h)); cbn [fold_left]; destruct h; reflexivity.
Qed.

Lemma brk_zeros_same : forall req b, brk_zeros req b b = [].
Proof.
  intros req b. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_unmaps_same : forall b, brk_unmaps b b = [].
Proof.
  intros b. unfold brk_unmaps, brk_page_range. rewrite Z.ltb_irrefl.
  destruct (0 <? bv_unsigned b); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_req_nonzero : forall (h : VmMaps) (req : word),
  0 < bv_unsigned (vm_brk h) ->
  bv_unsigned (vm_brk h) mod page_size = 0 ->
  bv_unsigned (vm_brk h) < bv_unsigned req ->
  bv_unsigned req mod page_size = 0 ->
  w_is0 req = false.
Proof.
  intros h req Hb0 Hbal Hlt Hral. unfold w_is0. apply bv_eqb_false_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

Lemma brk_unmaps_grow : forall (h : VmMaps) (req : word),
  0 < bv_unsigned (vm_brk h) ->
  bv_unsigned (vm_brk h) mod page_size = 0 ->
  bv_unsigned (vm_brk h) < bv_unsigned req ->
  bv_unsigned req mod page_size = 0 ->
  brk_unmaps req (vm_brk h) = [].
Proof.
  intros h req Hb0 Hbal Hlt Hral. unfold brk_unmaps, brk_page_range.
  rewrite !page_round_up_Z_aligned by assumption.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_brk h)))) by lia.
  destruct (0 <? bv_unsigned (vm_brk h)); reflexivity.
Qed.

Lemma brk_zeros_grow : forall (h : VmMaps) (req : word),
  0 < bv_unsigned (vm_brk h) ->
  bv_unsigned (vm_brk h) mod page_size = 0 ->
  bv_unsigned (vm_brk h) < bv_unsigned req ->
  bv_unsigned req mod page_size = 0 ->
  brk_zeros req req (vm_brk h)
  = [(vm_brk h, Z_to_bv 64 (bv_unsigned req - bv_unsigned (vm_brk h)))].
Proof.
  intros h req Hb0 Hbal Hlt Hral. unfold brk_zeros, brk_is_grow, brk_page_range.
  rewrite (brk_grow_req_nonzero h req Hb0 Hbal Hlt Hral). cbn [negb andb].
  rewrite (proj2 (Z.ltb_lt _ _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt). cbn [andb].
  rewrite !page_round_up_Z_aligned by assumption.
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite u64_id. reflexivity.
Qed.

Lemma brk_model_next_grow : forall (h : VmMaps) (req : word),
  0 < bv_unsigned (vm_brk h) ->
  bv_unsigned (vm_brk h) mod page_size = 0 ->
  bv_unsigned (vm_brk h) < bv_unsigned req ->
  bv_unsigned req mod page_size = 0 ->
  brk_model_next h req req = ledger_brk_grow req h.
Proof.
  intros h req Hb0 Hbal Hlt Hral.
  unfold brk_model_next, ledger_brk_grow, brk_maps_next, brk_grants, brk_is_grow.
  rewrite (brk_unmaps_grow h req Hb0 Hbal Hlt Hral). unfold maps_subtract_ranges. cbn [fold_left].
  rewrite (brk_grow_req_nonzero h req Hb0 Hbal Hlt Hral). cbn [negb andb].
  rewrite (proj2 (Z.ltb_lt _ _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt). cbn [andb].
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned (vm_brk h)))) by lia.
  cbn [app]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition brk_grow_b (m : Model) (req : word) : bool :=
  let h := m_vmmaps m in
  (bv_unsigned req <=? alloc_top h)
  && region_free (vm_reserved h ++ vm_maps h) (vm_brk h)
       (Z_to_bv 64 (bv_unsigned req + page_size - bv_unsigned (vm_brk h)))
  && (vm_backing_used m + (bv_unsigned req - bv_unsigned (vm_brk h)) <=? vm_limit h).

Lemma brk_grow_ok_aligned : forall m req,
  0 < bv_unsigned (vm_brk (m_vmmaps m)) ->
  bv_unsigned (vm_brk (m_vmmaps m)) mod page_size = 0 ->
  bv_unsigned (vm_brk (m_vmmaps m)) < bv_unsigned req ->
  bv_unsigned req mod page_size = 0 ->
  brk_grow_ok m req req = brk_grow_b m req.
Proof.
  intros m req Hb0 Hbal Hlt Hral. unfold brk_grow_ok, brk_grow_b, brk_budget_ok. cbv zeta.
  rewrite (proj2 (Z.ltb_lt _ _) Hb0), (proj2 (Z.ltb_lt _ _) Hlt). cbn [andb].
  rewrite !page_round_up_Z_aligned by assumption.
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). rewrite u64_id.
  pose proof (u64_range req) as Hr. pose proof (u64_range (vm_brk (m_vmmaps m))) as Hbr.
  rewrite bv_sub_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_same : forall m req, brk_grow_ok m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros m req. unfold brk_grow_ok. cbv zeta.
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_b_intro : forall R L c S m req,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned req <= alloc_top (m_vmmaps m) ->
  region_free (vm_maps (m_vmmaps m)) (vm_brk (m_vmmaps m))
    (Z_to_bv 64 (bv_unsigned req + page_size - bv_unsigned (vm_brk (m_vmmaps m)))) = true ->
  vm_backing_used m + (bv_unsigned req - bv_unsigned (vm_brk (m_vmmaps m))) <= L ->
  brk_grow_b m req = true.
Proof.
  intros R L c S m req Hinv Htop Hfree Hbud. pose proof Hinv as [].
  unfold brk_grow_b. cbv zeta. rewrite region_free_app, Hfree, li_reserved0.
  rewrite (region_free_above_top R) by (clear - li_brk_min0 li_brk_R0; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). rewrite (proj2 (Z.leb_le _ _)) by (clear - Hbud li_limit0; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grow_b_intro_lim : forall R L c S m req,
  ledger_inv R L c S (m_vmmaps m) ->
  bv_unsigned req <= alloc_top (m_vmmaps m) ->
  region_free (vm_maps (m_vmmaps m)) (vm_brk (m_vmmaps m))
    (Z_to_bv 64 (bv_unsigned req + page_size - bv_unsigned (vm_brk (m_vmmaps m)))) = true ->
  vm_backing_used m + (bv_unsigned req - bv_unsigned (vm_brk (m_vmmaps m))) <= vm_limit (m_vmmaps m) ->
  brk_grow_b m req = true.
Proof.
  intros R L c S m req Hinv Htop Hfree Hbud. pose proof Hinv as [].
  unfold brk_grow_b. cbv zeta. rewrite region_free_app, Hfree, li_reserved0.
  rewrite (region_free_above_top R) by (clear - li_brk_min0 li_brk_R0; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.leb_le _ _) Hbud). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_nil : forall a n, region_free [] a n = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma with_vmmaps_self : forall m, with_vmmaps (m_vmmaps m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Definition model_nolazy (m : Model) : Prop :=
  m_vm_lazy m = [] /\ m_vm_materialized m = [].

Lemma vm_forget_range_nolazy : forall lo hi m,
  model_nolazy m -> vm_forget_range lo hi m = m.
Proof.
  intros lo hi [fd [maps lazy mat] io fs proc lim tm] [H1 H2].
  cbn in H1, H2. subst. reflexivity.
Qed.

Lemma model_nolazy_with_vmmaps : forall h m, model_nolazy m -> model_nolazy (with_vmmaps h m).
Proof. intros h m H. exact H. Qed.

Lemma model_nolazy_init : forall reserved brk0 mbase sp lim inp,
  model_nolazy (init_model reserved brk0 mbase sp lim inp).
Proof. intros. split; reflexivity. Qed.

Lemma m_vmmaps_with_vmmaps' : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.

Lemma m_halted_with_vmmaps' : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.

Lemma vm_backing_used_nolazy : forall m,
  model_nolazy m ->
  vm_backing_used m = live_bytes (vm_backed_maps (m_vmmaps m)).
Proof.
  intros m [H1 H2]. unfold vm_backing_used. rewrite H1, H2. cbn [maps_subtract_all length].
  lia.
Qed.
