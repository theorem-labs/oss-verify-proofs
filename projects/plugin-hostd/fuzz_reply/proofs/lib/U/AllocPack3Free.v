From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0e YO0m YO0x YO03 YO0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocSI AllocGS AllocRealloc AllocPack AllocPackFree AllocPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require AllocFree AllocMalloc AllocBound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Lemma f3_len_split {A} (f g : A -> bool) l :
  length (filter f l) = (length (filter (fun x => f x && g x) l) + length (filter (fun x => f x && negb (g x)) l))%nat.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [filter]. destruct (f a), (g a); cbn [andb negb length]; lia.
Qed.

Lemma f3_filter_filter {A} (f g : A -> bool) l : filter f (filter g l) = filter (fun x => g x && f x) l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [filter]. destruct (g a); cbn [filter andb]; [destruct (f a)|]; rewrite ?IH; reflexivity.
Qed.

Lemma f3_len_mono {A} (f g : A -> bool) l : (forall x, In x l -> f x = true -> g x = true) ->
  (length (filter f l) <= length (filter g l))%nat.
Proof.
  induction l as [|a l IH]; intros H; cbn [filter]; [lia|].
  assert (IH' : (length (filter f l) <= length (filter g l))%nat) by (apply IH; intros x Hx; apply H; right; exact Hx).
  destruct (f a) eqn:Fa.
  - rewrite (H a (or_introl eq_refl) Fa). cbn [length]. lia.
  - destruct (g a); cbn [length]; lia.
Qed.

Lemma f3_filter_none {A} (f : A -> bool) l : (forall x, In x l -> f x = false) -> length (filter f l) = 0%nat.
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|]. cbn [filter]. rewrite (H a (or_introl eq_refl)).
  apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma f3_in_len {A} (x : A) l : In x l -> (1 <= length l)%nat.
Proof. destruct l as [|a l]; intros H; [destruct H | cbn [length]; lia]. Qed.

Lemma f3_nd_filter {A B} (f : A * B -> bool) l : NoDup (map fst l) -> NoDup (map fst (filter f l)).
Proof.
  induction l as [|a l IH]; intros N; cbn [filter]; [exact N|]. cbn [map] in N. apply NoDup_cons_iff in N as [Ha N].
  destruct (f a); cbn [map]; [|exact (IH N)]. constructor; [|exact (IH N)].
  intros Hin. apply Ha. apply in_map_iff in Hin as (y & Ey & Hy). apply filter_In in Hy as [Hy _]. rewrite <- Ey.
  apply in_map. exact Hy.
Qed.

Lemma f3_len1 {B} (l : list (sptr * B)) p : NoDup (map fst l) -> (forall e, In e l -> fst e = p) -> (length l <= 1)%nat.
Proof.
  intros N H. destruct l as [|a [|b t]]; cbn [length]; try lia.
  exfalso. cbn [map] in N. apply NoDup_cons_iff in N as [Ha _]. apply Ha. left.
  rewrite (H a (or_introl eq_refl)), (H b (or_intror (or_introl eq_refl))). reflexivity.
Qed.

Lemma f3_lookup_in M e : NoDup (map fst M) -> In e M -> mis_lookup M (fst e) = Some (snd e).
Proof.
  induction M as [|a M IH]; intros N Hin; [destruct Hin|]. cbn [map] in N. apply NoDup_cons_iff in N as [Ha N].
  unfold mis_lookup. cbn [find]. destruct Hin as [<-|Hin].
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb (fst a) (fst e)) eqn:E.
    + apply sptr_eqb_eq in E. exfalso. apply Ha. rewrite E. apply in_map. exact Hin.
    + exact (IH N Hin).
Qed.

Lemma f3_in_del (l1 l2 y : list (sptr * Z)) p n x m :
  In (x, m) (l1 ++ (p, n) :: l2) -> x <> p -> In (x, m) (l1 ++ y ++ l2).
Proof.
  intros H Hx. apply in_app_or in H as [H|[H|H]]; apply in_or_app.
  - left. exact H.
  - injection H as E _. exfalso. exact (Hx (eq_sym E)).
  - right. apply in_or_app. right. exact H.
Qed.

Definition bnd3 (c : Z) (b : sptr * Z) : bool := band (snd b) =? c - 1.

Definition isp3 (p : sptr) (b : sptr * Z) : bool := sptr_eqb (fst b) p.

Definition pmis3 (s : astate) (p : sptr) (c : Z) : bool :=
  existsb (fun b => sptr_eqb (fst b) p && (band (snd b) =? c - 1)) (ub_cls s c).

Definition mrp3 (s : astate) (M : list (sptr * Z)) (p : sptr) (c : Z) : Z :=
  match mis_lookup M p with Some c' => if (c' =? c) && pmis3 s p c then 1 else 0 | None => 0 end.

Definition keep3 (s s' : astate) (p : sptr) (c : Z) : Prop :=
  forall b, In b (ub_cls s c) -> fst b <> p -> In b (ub_cls s' c).

Lemma mrp3_range s M p c : 0 <= mrp3 s M p c <= 1.
Proof. unfold mrp3. destruct (mis_lookup M p) as [c'|]; [destruct ((c' =? c) && pmis3 s p c)|]; lia. Qed.

Lemma mrp3_le s M p c : mrp3 s M p c <= (if pmis3 s p c then 1 else 0).
Proof.
  unfold mrp3. destruct (mis_lookup M p) as [c'|]; [|destruct (pmis3 s p c); lia].
  destruct (c' =? c), (pmis3 s p c); cbn [andb]; lia.
Qed.

Lemma mis_step s s' M p c : NoDup (map fst M) -> keep3 s s' p c ->
  mis_in s M c <= mis_in s' (mis_del M p) c + mrp3 s M p c.
Proof.
  intros N K. unfold mis_in, mis_del. rewrite f3_filter_filter.
  rewrite (f3_len_split (mis_ok s c) (fun e => sptr_eqb (fst e) p) M). cbv beta.
  assert (A : (length (filter (fun x => mis_ok s c x && negb (sptr_eqb (fst x) p)) M) <=
               length (filter (fun x => negb (sptr_eqb (fst x) p) && mis_ok s' c x) M))%nat).
  { apply f3_len_mono. intros e _ He. cbv beta in He |- *. apply andb_prop in He as [He Hn]. apply negb_true_iff in Hn.
    rewrite Hn. cbn [negb andb]. apply sptr_eqb_neq in Hn.
    unfold mis_ok in He |- *. apply andb_prop in He as [Hc Hx]. rewrite Hc. cbn [andb].
    apply existsb_exists in Hx as (b & Hb & Eb). apply existsb_exists. exists b. split; [|exact Eb].
    cbv beta in Eb. apply K; [exact Hb|]. apply andb_prop in Eb as [Eb _]. apply sptr_eqb_eq in Eb. rewrite Eb. exact Hn. }
  assert (B : Z.of_nat (length (filter (fun x => mis_ok s c x && sptr_eqb (fst x) p) M)) <= mrp3 s M p c).
  { remember (filter (fun x => mis_ok s c x && sptr_eqb (fst x) p) M) as l eqn:El.
    assert (Hl : forall e, In e l -> In e M /\ mis_ok s c e = true /\ fst e = p).
    { intros e He. rewrite El in He. apply filter_In in He as [Hm He]. apply andb_prop in He as [Ho Hp].
      apply sptr_eqb_eq in Hp. split; [exact Hm|]. split; [exact Ho | exact Hp]. }
    assert (Nl : NoDup (map fst l)) by (rewrite El; apply f3_nd_filter; exact N).
    pose proof (f3_len1 l p Nl (fun e He => proj2 (proj2 (Hl e He)))) as L1.
    pose proof (mrp3_range s M p c) as Rr.
    destruct l as [|e t]; [cbn [length]; lia|].
    destruct (Hl e (or_introl eq_refl)) as (Hm & Ho & Hp).
    assert (Lk : mis_lookup M p = Some (snd e)) by (rewrite <- Hp; exact (f3_lookup_in M e N Hm)).
    unfold mrp3. rewrite Lk. cbv beta iota. unfold mis_ok in Ho. apply andb_prop in Ho as [Hc Hx]. rewrite Hc. cbn [andb].
    unfold pmis3. rewrite <- Hp, Hx. cbn [length] in L1 |- *. lia. }
  lia.
Qed.

Lemma in_ub3 X s g am i fr : NoDup (keys s) -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> In (frame_ptr am i fr, fr_n fr) (user_blocks s).
Proof.
  intros N U Hi Hf Hk. unfold user_blocks. apply in_flat_map. exists (g, am).
  split; [apply used_metas_iff; [exact N | exact (proj1 (usedX_MT _ _ _ _ U))]|]. cbn [snd].
  apply in_flat_map. exists i. split; [apply In_zseq; lia|]. cbv beta. rewrite Hf, Hk. left. reflexivity.
Qed.

Lemma in_ubc3 X s c g am i fr : NoDup (keys s) -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> am_sc am = c -> 1 <= am_last am ->
  In (frame_ptr am i fr, fr_n fr) (ub_cls s c).
Proof.
  intros N U Hi Hf Hk Hs Hl. unfold ub_cls. apply in_flat_map. exists (g, am).
  split; [apply used_metas_iff; [exact N | exact (proj1 (usedX_MT _ _ _ _ U))]|]. cbn [snd].
  rewrite (proj2 (Z.eqb_eq _ _) Hs), (proj2 (Z.leb_le 1 _) Hl). cbn [andb].
  apply in_flat_map. exists i. split; [apply In_zseq; lia|]. cbv beta. rewrite Hf, Hk. left. reflexivity.
Qed.

Lemma ubc_loc s c b : WF s -> In b (ub_cls s c) ->
  exists g am i fr, usedX [] s g am /\ am_sc am = c /\ 1 <= am_last am /\ 0 <= i <= am_last am /\
    ss_fr (nth_slot am i) = Some fr /\ fr_kind fr = FUser /\ b = (frame_ptr am i fr, fr_n fr).
Proof.
  intros HW H. unfold ub_cls in H. apply in_flat_map in H as ([g am] & Hg & Hb). cbn [snd] in Hb.
  destruct ((am_sc am =? c) && (1 <=? am_last am)) eqn:C; [|destruct Hb].
  apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C1. apply Z.leb_le in C2.
  apply in_flat_map in Hb as (i & Hi & Hb). apply In_zseq in Hi.
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:F; [|destruct Hb].
  destruct (fr_kind fr) eqn:K; [|destruct Hb]. destruct Hb as [<-|[]].
  exists g, am, i, fr. split; [apply (YO10.used_metas_usedX s g am HW); exact Hg|].
  split; [exact C1|]. split; [exact C2|]. split; [lia|]. split; [exact F|]. split; [exact K | reflexivity].
Qed.

Lemma loc_uniq s g1 a1 i1 f1 g2 a2 i2 f2 : WF s ->
  usedX [] s g1 a1 -> 0 <= i1 <= am_last a1 -> ss_fr (nth_slot a1 i1) = Some f1 ->
  usedX [] s g2 a2 -> 0 <= i2 <= am_last a2 -> ss_fr (nth_slot a2 i2) = Some f2 ->
  frame_ptr a1 i1 f1 = frame_ptr a2 i2 f2 -> g1 = g2 /\ i1 = i2 /\ a1 = a2 /\ f1 = f2.
Proof.
  intros HW U1 H1 F1 U2 H2 F2 E.
  pose proof (find_frame_in_spec [] None U0 s HW g1 a1 i1 f1 U1 H1 F1) as E1.
  pose proof (find_frame_in_spec [] None U0 s HW g2 a2 i2 f2 U2 H2 F2) as E2.
  rewrite E, E2 in E1. injection E1 as Eg Ei. subst g1 i1.
  pose proof (usedX_fun _ _ _ _ _ U1 U2) as Ea. subst a1. rewrite F1 in F2. injection F2 as Ef. subst f2.
  split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma pmis_loc s p c g am i fr : WF s -> usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  p = frame_ptr am i fr -> pmis3 s p c = true -> am_sc am = c /\ 1 <= am_last am /\ band (fr_n fr) = c - 1.
Proof.
  intros HW U Hi F Ep Pm. unfold pmis3 in Pm. apply existsb_exists in Pm as (b & Hb & Eb).
  cbv beta in Eb. apply andb_prop in Eb as [E1 E2]. apply sptr_eqb_eq in E1. apply Z.eqb_eq in E2.
  destruct (ubc_loc s c b HW Hb) as (g2 & a2 & i2 & f2 & U2 & Sc & Lt & Hi2 & F2 & K2 & Eb). subst b.
  cbn [fst snd] in E1, E2.
  destruct (loc_uniq s g2 a2 i2 f2 g am i fr HW U2 Hi2 F2 U Hi F ltac:(congruence)) as (_ & _ & Ea & Ef).
  subst a2 f2. exact (conj Sc (conj Lt E2)).
Qed.

Lemma keep_metas s s1 s2 p c : st_metas s2 = st_metas s1 -> keep3 s s1 p c -> keep3 s s2 p c.
Proof.
  intros E K b Hb Hp. assert (Eu : ub_cls s2 c = ub_cls s1 c) by (unfold ub_cls, used_metas; rewrite E; reflexivity).
  rewrite Eu. exact (K b Hb Hp).
Qed.

Lemma keep_upd s g am am1 i fr c : WF s -> usedX [] s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr ->
  (am_sc am = c -> 1 <= am_last am -> pk_shp am am1 /\ (forall j, 0 <= j -> j <> i -> nth_slot am1 j = nth_slot am j)) ->
  keep3 s (upd_meta g (MUsed am1) s) (frame_ptr am i fr) c.
Proof.
  intros HW U Hi F Hc [x nb] Hb Hx. cbn [fst] in Hx.
  pose proof (proj1 (inv_keys HW)) as N. pose proof (proj1 (usedX_MT _ _ _ _ U)) as Mg.
  assert (N' : NoDup (keys (upd_meta g (MUsed am1) s))) by (rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg); exact N).
  destruct (ubc_loc s c _ HW Hb) as (g2 & a2 & i2 & f2 & U2 & Sc & Lt & Hi2 & F2 & K2 & Eb).
  rewrite Eb. destruct (sptr_eq_dec g2 g) as [Eg|Ne].
  - subst g2. pose proof (usedX_fun _ _ _ _ _ U2 U) as Ea. subst a2.
    destruct (Hc Sc Lt) as [Sh Hj].
    assert (Ni : i2 <> i).
    { intros Ei. subst i2. rewrite F in F2. injection F2 as Ef. subst f2. apply Hx. injection Eb as Eb _. exact Eb. }
    pose proof Sh as (M & Lm & S & T).
    assert (Ep : frame_ptr am i2 f2 = frame_ptr am1 i2 f2) by (unfold frame_ptr; rewrite (pk_shp_slot_start am am1 i2 Sh); reflexivity).
    rewrite Ep. apply (in_ubc3 [] _ c g am1 i2 f2 N').
    + apply usedX_upd. left. split; [reflexivity|]. split; reflexivity.
    + lia.
    + rewrite (Hj i2 ltac:(lia) Ni). exact F2.
    + exact K2.
    + lia.
    + lia.
  - apply (in_ubc3 [] _ c g2 a2 i2 f2 N'); try assumption.
    apply usedX_upd. right. split; [exact Ne | exact U2].
Qed.

Lemma keep_free s p n tr s' c : WF s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') -> keep3 s s' p c.
Proof.
  intros HW Hin Y [x nb] Hb Hx. cbn [fst] in Hx.
  pose proof (free_wf s p n tr s' HW Hin Y) as HW'.
  pose proof (proj1 (inv_keys HW)) as N. pose proof (proj1 (inv_keys HW')) as N'.
  destruct (ubc_loc s c _ HW Hb) as (g & am & i & fr & U & Sc & Lt & Hi & F & K & Eb).
  pose proof (in_ub3 [] s g am i fr N U Hi F K) as Hu. rewrite <- Eb in Hu.
  destruct (free_blocks s p n tr s' HW Hin Y) as (l1 & l2 & E1 & E2).
  assert (Hu' : In (x, nb) (user_blocks s')).
  { rewrite E2. rewrite E1 in Hu. exact (f3_in_del l1 l2 [] p n x nb Hu Hx). }
  destruct (user_blocks_frame s' x nb HW' Hu') as (g' & a' & j & f & U' & Hj & F' & K' & En & Ex).
  destruct (free_rel s p tr s' Y g' a' (proj1 (usedX_MT _ _ _ _ U'))) as (a & Ha & M & Lm & S & T & Fr).
  assert (Ua : usedX [] s g' a) by (apply usedX_intro; [reflexivity | exact Ha]).
  assert (Fa : ss_fr (nth_slot a j) = Some f) by exact (Fr j f F').
  assert (Sh : pk_shp a a') by exact (conj M (conj Lm (conj S T))).
  assert (Ep : frame_ptr a j f = frame_ptr am i fr).
  { unfold frame_ptr. rewrite <- (pk_shp_slot_start a a' j Sh). change (frame_ptr a' j f = frame_ptr am i fr).
    rewrite <- Ex. injection Eb as Eb _. exact Eb. }
  destruct (loc_uniq s g' a j f g am i fr HW Ua ltac:(lia) Fa U Hi F Ep) as (Eg & Ei & Ea & Ef).
  subst g' j a f.
  rewrite Ex, <- En. apply (in_ubc3 [] s' c g a' i fr N' U'); [lia | exact F' | exact K' | lia | lia].
Qed.

Definition pcnt3 (P : sptr * Z -> bool) (c : Z) (x : option mslot) : nat :=
  match x with Some (MUsed am) => length (filter P (pk_ublk c am)) | _ => 0%nat end.

Lemma cls_sum3 s c P : NoDup (keys s) -> length (filter P (ub_cls s c)) = pk_sum (fun g => pcnt3 P c (MT s g)) (keys s).
Proof.
  intros N. change (ub_cls s c) with (flat_map (fun gm : sptr * ameta => pk_ublk c (snd gm)) (used_metas s)).
  rewrite (pk_um_keys (pk_ublk c) s N), pk_len_filter_flat. apply pk_sum_ext.
  intros g _. cbv beta. destruct (MT s g) as [[| |am]|]; reflexivity.
Qed.

Lemma pcnt_le3 P c a a' : pk_shp a a' -> AllocFree.af_frs a a' ->
  (pcnt3 P c (Some (MUsed a')) <= pcnt3 P c (Some (MUsed a)))%nat.
Proof.
  intros Sh F. pose proof Sh as (M & L & S & T). cbn [pcnt3]. unfold pk_ublk, blocks_of0. rewrite S, T.
  destruct ((am_sc a =? c) && (1 <=? am_last a)); cbv beta iota; [|cbn; lia].
  rewrite !pk_len_filter_flat. apply pk_sum_mono. intros j _. cbv beta.
  unfold slot_block0. rewrite (pk_shp_slot_start a a' j Sh).
  destruct (ss_fr (nth_slot a' j)) as [f|] eqn:E; [|cbn; lia].
  rewrite (F j f E). destruct (fr_kind f); cbn [filter];
    [match goal with |- context [P ?x] => destruct (P x) end|]; cbn; lia.
Qed.

Lemma cls_le3 s s' c P : NoDup (keys s') -> NoDup (keys s) ->
  (forall q a', MT s' q = Some (MUsed a') -> exists a, MT s q = Some (MUsed a) /\ pk_shp a a' /\ AllocFree.af_frs a a') ->
  (length (filter P (ub_cls s' c)) <= length (filter P (ub_cls s c)))%nat.
Proof.
  intros N' N H. rewrite (cls_sum3 s' c P N'), (cls_sum3 s c P N).
  apply (pk_sum_le sptr_eq_dec); [exact N' | exact N |].
  intros q _ Hnz. cbv beta in Hnz |- *. revert Hnz.
  destruct (MT s' q) as [[pr nx| |a']|] eqn:E; intros Hnz; try (exfalso; apply Hnz; reflexivity).
  destruct (H q a' E) as (a & Ea & Sh & F). rewrite Ea.
  split; [exact (MT_Some_In_keys _ _ _ Ea) | exact (pcnt_le3 P c a a' Sh F)].
Qed.

Lemma upc_free3 s p n tr s' c : WF s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') ->
  upc s' c + (if pmis3 s p c then 1 else 0) <= upc s c.
Proof.
  intros HW Hin Y.
  pose proof (free_wf s p n tr s' HW Hin Y) as HW'.
  pose proof (proj1 (inv_keys HW)) as N. pose proof (proj1 (inv_keys HW')) as N'.
  destruct (free_blocks s p n tr s' HW Hin Y) as (l1 & l2 & E1 & E2).
  assert (R : forall q a', MT s' q = Some (MUsed a') ->
              exists a, MT s q = Some (MUsed a) /\ pk_shp a a' /\ AllocFree.af_frs a a').
  { intros q a' Hm. destruct (free_rel s p tr s' Y q a' Hm) as (a & Ha & M & Lm & S & T & F).
    exists a. split; [exact Ha|]. split; [exact (conj M (conj Lm (conj S T))) | exact F]. }
  pose proof (f3_len_split (bnd3 c) (isp3 p) (ub_cls s c)) as Es.
  pose proof (f3_len_split (bnd3 c) (isp3 p) (ub_cls s' c)) as Es'.
  pose proof (cls_le3 s s' c (fun x => bnd3 c x && negb (isp3 p x)) N' N R) as Le.
  assert (Z0 : length (filter (fun x => bnd3 c x && isp3 p x) (ub_cls s' c)) = 0%nat).
  { apply f3_filter_none. intros x Hx. cbv beta. unfold isp3. cbv beta.
    destruct (sptr_eqb (fst x) p) eqn:E; [|apply andb_false_r].
    exfalso. apply sptr_eqb_eq in E.
    destruct (ubc_loc s' c x HW' Hx) as (g & am & i & fr & U & _ & _ & Hi & F & K & Ex).
    pose proof (in_ub3 [] s' g am i fr N' U Hi F K) as Hu. rewrite <- Ex, E2 in Hu.
    pose proof (YO10.user_block_ptrs_NoDup s HW) as ND. rewrite E1, map_app in ND. cbn [map fst] in ND.
    apply (NoDup_remove_2 _ _ _ ND). rewrite <- map_app, <- E. apply in_map. exact Hu. }
  change (upc s' c) with (Z.of_nat (length (filter (bnd3 c) (ub_cls s' c)))).
  change (upc s c) with (Z.of_nat (length (filter (bnd3 c) (ub_cls s c)))).
  rewrite Es, Es', Z0.
  destruct (pmis3 s p c) eqn:Pm; [|lia].
  assert (G1 : (1 <= length (filter (fun x => bnd3 c x && isp3 p x) (ub_cls s c)))%nat).
  { unfold pmis3 in Pm. apply existsb_exists in Pm as (b & Hb & Eb). apply (f3_in_len b).
    apply filter_In. split; [exact Hb|]. cbv beta in Eb |- *. unfold bnd3, isp3. cbv beta. apply andb_prop in Eb as [Ea Eb].
    rewrite Ea, Eb. reflexivity. }
  lia.
Qed.

Lemma PKC3_tr s s' caps mc : NoDup (keys s') -> NoDup (keys s) -> PKC3 [] caps mc s ->
  (forall q a', MT s' q = Some (MUsed a') -> am_sc a' < 48 ->
     exists a, MT s q = Some (MUsed a) /\ am_sc a' = am_sc a /\ am_last a' = am_last a) ->
  PKC3 [] caps mc s'.
Proof.
  intros N' N HP H c Hc. destruct (HP c Hc) as [F R]. split.
  - eapply Z.le_trans; [|exact F]. apply gcount_le; [exact N' | exact N |].
    intros q a' E Fa. unfold gfull in Fa. apply andb_prop in Fa as [S T]. apply Z.eqb_eq in S.
    destruct (H q a' E ltac:(lia)) as (a & Ea & Sa & Ta). exists a. split; [exact Ea|].
    unfold gfull. rewrite <- Sa, <- Ta, S, Z.eqb_refl. exact T.
  - eapply Z.le_trans; [|exact R]. apply gcount_le; [exact N' | exact N |].
    intros q a' E Fa. unfold gred in Fa. apply andb_prop in Fa as [S T]. apply Z.eqb_eq in S.
    destruct (H q a' E ltac:(lia)) as (a & Ea & Sa & Ta). exists a. split; [exact Ea|].
    unfold gred. rewrite <- Sa, <- Ta, S, Z.eqb_refl. exact T.
Qed.

Lemma PKC3_upd s g am am1 caps mc : WF s -> PKC3 [] caps mc s -> usedX [] s g am ->
  am_sc am1 = am_sc am -> am_last am1 = am_last am -> PKC3 [] caps mc (upd_meta g (MUsed am1) s).
Proof.
  intros HW HC Hg S T. pose proof (proj1 (usedX_MT _ _ _ _ Hg)) as Mg.
  pose proof (proj1 (inv_keys HW)) as N.
  assert (N' : NoDup (keys (upd_meta g (MUsed am1) s))) by (rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg); exact N).
  apply (PKC3_tr s _ caps mc N' N HC). intros q a' E _. rewrite MT_upd in E.
  destruct (sptr_eqb q g) eqn:Eq.
  - apply sptr_eqb_eq in Eq. subst q. injection E as <-. exists am. split; [exact Mg|]. split; [exact S | exact T].
  - exists a'. split; [exact E|]. split; reflexivity.
Qed.

Lemma PKC3_metas s s' caps mc : st_metas s' = st_metas s -> PKC3 [] caps mc s -> PKC3 [] caps mc s'.
Proof. intros E H. unfold PKC3, gcountX, keys, MTX, MT in *. rewrite E. exact H. Qed.

Lemma UPB3_mono s L L' M : (forall k, 0 <= k < 49 -> znth k L <= znth k L') -> UPB3 s L M -> UPB3 s L' M.
Proof.
  intros H (U1 & U2). split.
  - intros k Hk. specialize (U1 k Hk). specialize (H k Hk). lia.
  - intros c Hc. specialize (U2 c Hc). specialize (H c ltac:(lia)). lia.
Qed.

Lemma mis_del3 s s' M p mc : MIS s M mc ->
  (forall x m, In (x, m) (user_blocks s) -> x <> p -> In (x, m) (user_blocks s')) -> MIS s' (mis_del M p) mc.
Proof.
  intros (N & E & C) H. split; [|split].
  - apply f3_nd_filter. exact N.
  - intros e He. unfold mis_del in He. apply filter_In in He as [He Hp]. apply negb_true_iff in Hp.
    apply sptr_eqb_neq in Hp. destruct (E e He) as (Hr & m & Hm). split; [exact Hr|]. exists m.
    exact (H (fst e) m Hm Hp).
  - intros c Hc. eapply Z.le_trans; [|exact (C c Hc)]. unfold count_mis, mis_del. rewrite f3_filter_filter.
    apply Nat2Z.inj_le. apply f3_len_mono. intros x _ Hx. cbv beta in Hx |- *. apply andb_prop in Hx as [_ Hx]. exact Hx.
Qed.

Theorem free_pack3 : forall s p n caps mc L M tr u s',
  WF s -> SI s -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M -> MIS s M mc -> In (p, n) (user_blocks s) ->
  yields (free (Some p) s) tr (u, s') ->
  PKS [] s' /\ PKC3 [] caps mc s' /\ UPB3 s' (lv_add L (band n) (-1)) (mis_del M p) /\ MIS s' (mis_del M p) mc.
Proof.
  intros s p n caps mc L M tr u s' HW _ HP HC (U1 & U2) HM Hin Y. destruct u.
  pose proof (free_wf s p n tr s' HW Hin Y) as HW'.
  pose proof (proj1 (inv_keys HW)) as N. pose proof (proj1 (inv_keys HW')) as N'.
  pose proof (free_rel s p tr s' Y) as R.
  destruct (free_blocks s p n tr s' HW Hin Y) as (l1 & l2 & E1 & E2).
  pose proof (AllocBound.ub_nonneg s HW (p, n) Hin) as Hn. cbn [snd] in Hn.
  pose proof (band_range n Hn) as Bn.
  split; [|split; [|split]].
  - apply (PKS_tr s s' HP). intros q a' Hu. left.
    destruct (usedX_MT _ _ _ _ Hu) as [Hm _]. destruct (R q a' Hm) as (a & Ha & M0 & Lm & S & T & F).
    exists a. split; [apply usedX_intro; [reflexivity | exact Ha]|].
    split; [exact (conj M0 (conj Lm (conj S T)))|].
    intros j f _ Hf. left. exact (F j f Hf).
  - apply (PKC3_tr s s' caps mc N' N HC). intros q a' Hm _. destruct (R q a' Hm) as (a & Ha & _ & _ & S & T & _).
    exists a. split; [exact Ha|]. split; [exact S | exact T].
  - split.
    + intros j Hj. pose proof (bcount_del s s' l1 l2 (p, n) j E1 E2) as B. cbn [snd] in B. specialize (U1 j Hj).
      pose proof (lv_add_le_neg L (band n) (-1) j ltac:(lia) ltac:(lia) ltac:(lia)) as V.
      revert B V. destruct (Z.eqb_spec (band n) j); destruct (Z.eqb_spec j (band n)); cbv beta iota; intros B V; lia.
    + intros c Hc. pose proof (bcount_del s s' l1 l2 (p, n) c E1 E2) as B. cbn [snd] in B. specialize (U2 c Hc).
      pose proof (lv_add_le_neg L (band n) (-1) c ltac:(lia) ltac:(lia) ltac:(lia)) as V.
      pose proof (upc_free3 s p n tr s' c HW Hin Y) as W.
      pose proof (mis_step s s' M p c (proj1 HM) (keep_free s p n tr s' c HW Hin Y)) as Ms.
      pose proof (mrp3_le s M p c) as Rl.
      revert B V W Rl. destruct (Z.eqb_spec (band n) c); destruct (Z.eqb_spec c (band n)); destruct (pmis3 s p c);
        cbv beta iota; intros B V W Rl; lia.
  - apply (mis_del3 s s' M p mc HM). intros x m Hx Ne. rewrite E1 in Hx. rewrite E2.
    exact (f3_in_del l1 l2 [] p n x m Hx Ne).
Qed.
