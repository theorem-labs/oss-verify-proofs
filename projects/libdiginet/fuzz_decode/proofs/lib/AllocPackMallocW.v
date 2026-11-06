(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/AllocPackMallocW.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO03 YO0m YO0p.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import AllocSI AllocGS AllocMalloc AllocPack AllocPackMallocN.
Import ListNotations.
Local Open Scope Z_scope.

Definition PP (X : list sptr) (s : astate) (f : ameta -> bool) (g : sptr) : bool :=
  match MTX X s g with Some (MUsed am) => f am | _ => false end.

Lemma gcount_PP X s f : gcountX X s f = Z.of_nat (length (filter (PP X s f) (keys s))).
Proof. reflexivity. Qed.

Lemma PP_iff X s f g : PP X s f g = true <-> exists am, usedX X s g am /\ f am = true.
Proof.
  unfold PP, usedX. destruct (MTX X s g) as [[pr nx| |am]|]; split; intros H.
  all: try discriminate.
  all: try (destruct H as (am' & E & _); discriminate E).
  - exists am. split; [reflexivity | exact H].
  - destruct H as (am' & E & F). injection E as E. subst. exact F.
Qed.

Lemma usedX_keys X s g a : usedX X s g a -> In g (keys s).
Proof. intros U. exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ U))). Qed.

Lemma filter_len_eq {A} (p q : A -> bool) l1 l2 : NoDup l1 -> NoDup l2 ->
  (forall x, (In x l1 /\ p x = true) <-> (In x l2 /\ q x = true)) -> length (filter p l1) = length (filter q l2).
Proof.
  intros N1 N2 H. apply Permutation_length. apply NoDup_Permutation; [apply NoDup_filter, N1 | apply NoDup_filter, N2|].
  intros x. rewrite !filter_In. apply H.
Qed.

Lemma gcount_corr X s X' s' f : corr X s X' s' -> NoDup (keys s) -> NoDup (keys s') ->
  (forall a a', prj a = prj a' -> f a = f a') -> gcountX X' s' f = gcountX X s f.
Proof.
  intros [CB CF] N N' Hf. rewrite !gcount_PP. f_equal. apply filter_len_eq; [exact N' | exact N |].
  intros g. rewrite !PP_iff. split.
  - intros (_ & a' & U' & F'). destruct (CB g a' U') as (a & U & E). split; [exact (usedX_keys _ _ _ _ U)|].
    exists a. split; [exact U|]. rewrite (Hf a a' E). exact F'.
  - intros (_ & a & U & F). destruct (CF g a U) as (a' & U' & E). split; [exact (usedX_keys _ _ _ _ U')|].
    exists a'. split; [exact U'|]. rewrite <- (Hf a a' E). exact F.
Qed.

Lemma gfull_prj c a a' : prj a = prj a' -> gfull c a = gfull c a'.
Proof. intros E. destruct (prj_geo _ _ E) as (_ & L & S & _). unfold gfull. rewrite L, S. reflexivity. Qed.

Lemma gred_prj c a a' : prj a = prj a' -> gred c a = gred c a'.
Proof. intros E. destruct (prj_geo _ _ E) as (_ & L & S & _). unfold gred. rewrite L, S. reflexivity. Qed.

Lemma PKS_corr X s X' s' : corr X s X' s' -> PKS X s -> PKS X' s'.
Proof.
  intros [CB CF] (P1 & P2 & P3 & P4). split; [|split; [|split]].
  - intros g a' i fr U' Hsc Hi Hfr Hk. destruct (CB g a' U') as (a & U & E). destruct (prj_geo _ _ E) as (_ & L & S & _).
    rewrite <- S in *. rewrite <- L in Hi. rewrite <- (prj_fr _ _ i E) in Hfr. exact (P1 g a i fr U Hsc Hi Hfr Hk).
  - intros g a' i fr c ac' U' Hi Hfr Hk Uc' Hml Hmem.
    destruct (CB g a' U') as (a & U & E). destruct (prj_geo _ _ E) as (_ & L & S & _).
    destruct (CB c ac' Uc') as (ac & Uc & Ec). destruct (prj_geo _ _ Ec) as (M & Lc & Sc & Mc).
    rewrite <- S, <- Sc, <- Lc. rewrite <- L in Hi. rewrite <- (prj_fr _ _ i E) in Hfr. rewrite <- Mc in Hml.
    rewrite <- M, <- (prj_slot_start _ _ i E) in Hmem. exact (P2 g a i fr c ac U Hi Hfr Hk Uc Hml Hmem).
  - intros g a' U' Hsc. destruct (CB g a' U') as (a & U & E). destruct (prj_geo _ _ E) as (_ & L & S & _).
    rewrite <- S, <- L in *. exact (P3 g a U Hsc).
  - intros g a' U' Hsc Hml. destruct (CB g a' U') as (a & U & E). destruct (prj_geo _ _ E) as (_ & L & S & Ml).
    rewrite <- S in *. rewrite <- Ml in Hml. exact (P4 g a U Hsc Hml).
Qed.

Lemma PKC_corr X s X' s' caps : corr X s X' s' -> NoDup (keys s) -> NoDup (keys s') -> PKC X caps s -> PKC X' caps s'.
Proof.
  intros C N N' P c Hc.
  rewrite (gcount_corr X s X' s' (gfull c) C N N' (gfull_prj c)), (gcount_corr X s X' s' (gred c) C N N' (gred_prj c)).
  exact (P c Hc).
Qed.

Lemma PK_corr X s X' s' caps : corr X s X' s' -> NoDup (keys s) -> NoDup (keys s') ->
  PKS X s -> PKC X caps s -> PKS X' s' /\ PKC X' caps s'.
Proof. intros C N N' P1 P2. split; [exact (PKS_corr _ _ _ _ C P1) | exact (PKC_corr _ _ _ _ _ C N N' P2)]. Qed.

Lemma usedX_inst X s s' m a1 q a : memb m X = false -> MT s' m = Some (MUsed a1) -> (forall q, q <> m -> MT s' q = MT s q) ->
  usedX X s' q a <-> (q = m /\ a = a1) \/ (q <> m /\ usedX (m :: X) s q a).
Proof.
  intros NX EM EO. unfold usedX, MTX. destruct (sptr_eq_dec q m) as [->|Hq].
  - rewrite memb_cons, sptr_eqb_refl, NX, EM. cbn [orb]. split.
    + intros H. injection H as E. subst. left. auto.
    + intros [[_ ->]|[N _]]; [reflexivity | exfalso; apply N; reflexivity].
  - rewrite memb_cons, (proj2 (sptr_eqb_neq q m) Hq), (EO q Hq). cbn [orb]. split.
    + intros H. right. auto.
    + intros [[E _]|[_ H]]; [exfalso; exact (Hq E) | exact H].
Qed.

Lemma usedX_set X s s' g am' q a : memb g X = false -> MT s' g = Some (MUsed am') -> (forall q, q <> g -> MT s' q = MT s q) ->
  usedX X s' q a <-> (q = g /\ a = am') \/ (q <> g /\ usedX X s q a).
Proof.
  intros NX EM EO. unfold usedX, MTX. destruct (sptr_eq_dec q g) as [->|Hq].
  - rewrite NX, EM. cbn [orb]. split.
    + intros H. injection H as E. subst. left. auto.
    + intros [[_ ->]|[N _]]; [reflexivity | exfalso; apply N; reflexivity].
  - rewrite (EO q Hq). split.
    + intros H. right. auto.
    + intros [[E _]|[_ H]]; [exfalso; exact (Hq E) | exact H].
Qed.

Lemma gcount_inst X s s' m a1 f : NoDup (keys s) -> In m (keys s) -> keys s' = keys s -> memb m X = false ->
  MT s' m = Some (MUsed a1) -> (forall q, q <> m -> MT s' q = MT s q) ->
  gcountX X s' f = gcountX (m :: X) s f + (if f a1 then 1 else 0).
Proof.
  intros N Hm K NX EM EO. rewrite !gcount_PP, K. destruct (in_split _ _ Hm) as (l1 & l2 & E). rewrite E in N |- *.
  pose proof (NoDup_remove_2 _ _ _ N) as Hni. rewrite !filter_app. cbn [filter].
  assert (EQ : forall q, q <> m -> PP X s' f q = PP (m :: X) s f q).
  { intros q Hq. unfold PP, MTX. rewrite memb_cons, (proj2 (sptr_eqb_neq q m) Hq), (EO q Hq). reflexivity. }
  rewrite (filter_ext_in (PP X s' f) (PP (m :: X) s f) l1), (filter_ext_in (PP X s' f) (PP (m :: X) s f) l2).
  2,3: intros q Hq; apply EQ; intros ->; apply Hni; apply in_app_iff; auto.
  assert (Pm1 : PP X s' f m = f a1) by (unfold PP, MTX; rewrite NX, EM; reflexivity).
  assert (Pm2 : PP (m :: X) s f m = false) by (unfold PP, MTX; rewrite memb_cons, sptr_eqb_refl; reflexivity).
  rewrite Pm1, Pm2. destruct (f a1); rewrite !length_app; cbn [length]; lia.
Qed.

Lemma gcount_set X s s' g am am' f : NoDup (keys s) -> keys s' = keys s -> usedX X s g am ->
  MT s' g = Some (MUsed am') -> (forall q, q <> g -> MT s' q = MT s q) -> f am' = f am -> gcountX X s' f = gcountX X s f.
Proof.
  intros N K U EM EO Ef. pose proof (usedX_MT _ _ _ _ U) as [Mg NX]. rewrite !gcount_PP, K. do 2 f_equal.
  apply filter_ext_in. intros q _. unfold PP, MTX. destruct (sptr_eq_dec q g) as [->|Hq].
  - rewrite NX, EM, Mg. exact Ef.
  - rewrite (EO q Hq). reflexivity.
Qed.

Lemma gcount_metas X s s' f : st_metas s' = st_metas s -> gcountX X s' f = gcountX X s f.
Proof. intros E. unfold gcountX, keys, MTX, MT. rewrite E. reflexivity. Qed.

Lemma PK_metas X s s' caps : st_metas s' = st_metas s -> PKS X s -> PKC X caps s -> PKS X s' /\ PKC X caps s'.
Proof.
  intros E P1 P2. assert (C : corr X s X s') by (apply corr_metas; exact E). split; [exact (PKS_corr _ _ _ _ C P1)|].
  intros c Hc. rewrite !(gcount_metas X s s' _ E). exact (P2 c Hc).
Qed.

Lemma PK_install X s s' m a1 caps :
  memb m X = false -> NoDup (keys s) -> In m (keys s) -> keys s' = keys s ->
  MT s' m = Some (MUsed a1) -> (forall q, q <> m -> MT s' q = MT s q) ->
  (forall i, ss_fr (nth_slot a1 i) = None) ->
  (am_maplen a1 = 0 -> forall g am i fr, usedX (m :: X) s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
     fr_kind fr = FGroup -> am_mem a1 = slot_start am i -> am_sc am = jof (am_sc a1) (am_last a1 + 1)) ->
  (am_sc a1 < 48 -> am_last a1 + 1 <= FC (am_sc a1)) ->
  (am_sc a1 < 48 -> 0 < am_maplen a1 -> nestF (am_sc a1) = false) ->
  (forall c, 0 <= c < 48 -> gfull c a1 = true -> gcountX (m :: X) s (gfull c) + 1 <= znth c (NF caps)) ->
  (forall c, 0 <= c < 48 -> gred c a1 = true -> gcountX (m :: X) s (gred c) + 1 <= RED) ->
  PKS (m :: X) s -> PKC (m :: X) caps s -> PKS X s' /\ PKC X caps s'.
Proof.
  intros NX N Hm K EM EO Hfl H2 H3 H4 Hf Hr (P1 & P2 & P3 & P4) PC.
  pose proof (fun q a => usedX_inst X s s' m a1 q a NX EM EO) as UI.
  split; [split; [|split; [|split]]|].
  - intros g a i fr U Hsc Hi Hfr Hk. apply UI in U as [[-> ->]|[_ U]]; [rewrite Hfl in Hfr; discriminate|].
    exact (P1 g a i fr U Hsc Hi Hfr Hk).
  - intros g a i fr c ac U Hi Hfr Hk Uc Hml Hmem. apply UI in U as [[-> ->]|[_ U]]; [rewrite Hfl in Hfr; discriminate|].
    apply UI in Uc as [[-> ->]|[_ Uc]]; [exact (H2 Hml g a i fr U Hi Hfr Hk Hmem)|].
    exact (P2 g a i fr c ac U Hi Hfr Hk Uc Hml Hmem).
  - intros g a U Hsc. apply UI in U as [[-> ->]|[_ U]]; [exact (H3 Hsc) | exact (P3 g a U Hsc)].
  - intros g a U Hsc Hml. apply UI in U as [[-> ->]|[_ U]]; [exact (H4 Hsc Hml) | exact (P4 g a U Hsc Hml)].
  - intros c Hc. rewrite !(gcount_inst X s s' m a1 _ N Hm K NX EM EO). destruct (PC c Hc) as [C1 C2].
    split; [destruct (gfull c a1) eqn:E; [specialize (Hf c Hc E); lia | lia]
           | destruct (gred c a1) eqn:E; [specialize (Hr c Hc E); lia | lia]].
Qed.

Lemma PK_upd X s s' g am am' idx caps :
  usedX X s g am -> NoDup (keys s) -> keys s' = keys s -> MT s' g = Some (MUsed am') -> (forall q, q <> g -> MT s' q = MT s q) ->
  am_sc am' = am_sc am -> am_last am' = am_last am -> am_mem am' = am_mem am -> am_maplen am' = am_maplen am ->
  (forall i, 0 <= i -> i <> idx -> ss_fr (nth_slot am' i) = ss_fr (nth_slot am i)) ->
  (forall fr, ss_fr (nth_slot am' idx) = Some fr -> fr_kind fr = FUser -> am_sc am < 48 ->
     fr_n fr < MMAP_THRESHOLD /\ am_sc am <= size_to_class (fr_n fr) + 1) ->
  (forall fr, ss_fr (nth_slot am' idx) = Some fr -> fr_kind fr = FGroup -> forall c ac, usedX X s c ac -> am_maplen ac = 0 ->
     am_mem ac = slot_start am idx -> am_sc am = jof (am_sc ac) (am_last ac + 1)) ->
  PKS X s -> PKC X caps s -> PKS X s' /\ PKC X caps s'.
Proof.
  intros U N K EM EO S L M ML FR HU HG (P1 & P2 & P3 & P4) PC.
  pose proof (usedX_MT _ _ _ _ U) as [Mg NX].
  pose proof (fun q a => usedX_set X s s' g am' q a NX EM EO) as UI.
  assert (ST : stride_of am' = stride_of am) by (unfold stride_of; rewrite S, L, ML; reflexivity).
  assert (SS : forall i, slot_start am' i = slot_start am i) by (intros i; unfold slot_start; rewrite ST, M; reflexivity).
  split; [split; [|split; [|split]]|].
  - intros q a i fr Uq Hsc Hi Hfr Hk. apply UI in Uq as [[-> ->]|[_ Uq]]; [|exact (P1 q a i fr Uq Hsc Hi Hfr Hk)].
    rewrite S in Hsc |- *. rewrite L in Hi. destruct (Z.eq_dec i idx) as [->|Hne]; [exact (HU fr Hfr Hk Hsc)|].
    rewrite (FR i ltac:(lia) Hne) in Hfr. exact (P1 g am i fr U Hsc Hi Hfr Hk).
  - intros q a i fr c ac Uq Hi Hfr Hk Uc Hml Hmem.
    assert (Hc : exists ac0, usedX X s c ac0 /\ am_maplen ac0 = am_maplen ac /\ am_mem ac0 = am_mem ac /\
      am_sc ac0 = am_sc ac /\ am_last ac0 = am_last ac).
    { apply UI in Uc as [[-> ->]|[_ Uc]]; [exists am; split; [exact U|]; repeat split; congruence | exists ac; auto]. }
    destruct Hc as (ac0 & Uc0 & E1 & E2 & E3 & E4). rewrite <- E3, <- E4. rewrite <- E1 in Hml. rewrite <- E2 in Hmem.
    apply UI in Uq as [[-> ->]|[_ Uq]].
    + rewrite S. rewrite L in Hi. rewrite SS in Hmem. destruct (Z.eq_dec i idx) as [->|Hne]; [exact (HG fr Hfr Hk c ac0 Uc0 Hml Hmem)|].
      rewrite (FR i ltac:(lia) Hne) in Hfr. exact (P2 g am i fr c ac0 U Hi Hfr Hk Uc0 Hml Hmem).
    + exact (P2 q a i fr c ac0 Uq Hi Hfr Hk Uc0 Hml Hmem).
  - intros q a Uq Hsc. apply UI in Uq as [[-> ->]|[_ Uq]]; [|exact (P3 q a Uq Hsc)].
    rewrite S, L. rewrite S in Hsc. exact (P3 g am U Hsc).
  - intros q a Uq Hsc Hml. apply UI in Uq as [[-> ->]|[_ Uq]]; [|exact (P4 q a Uq Hsc Hml)].
    rewrite S. rewrite S in Hsc. rewrite ML in Hml. exact (P4 g am U Hsc Hml).
  - intros c Hc.
    rewrite (gcount_set X s s' g am am' (gfull c) N K U EM EO) by (unfold gfull; rewrite S, L; reflexivity).
    rewrite (gcount_set X s s' g am am' (gred c) N K U EM EO) by (unfold gred; rewrite S, L; reflexivity).
    exact (PC c Hc).
Qed.

Definition CL (s s' : astate) : Prop :=
  forall g a, MT s g = Some (MUsed a) -> blocks_of0 a <> [] ->
  exists a', MT s' g = Some (MUsed a') /\ am_sc a' = am_sc a /\ am_last a' = am_last a /\ blocks_of0 a' = blocks_of0 a.

Lemma CL_refl s : CL s s.
Proof. intros g a H _. exists a. repeat split; auto. Qed.

Lemma CL_trans s1 s2 s3 : CL s1 s2 -> CL s2 s3 -> CL s1 s3.
Proof.
  intros A B g a H Hb. destruct (A g a H Hb) as (a2 & H2 & S2 & L2 & B2).
  destruct (B g a2 H2 ltac:(rewrite B2; exact Hb)) as (a3 & H3 & S3 & L3 & B3).
  exists a3. split; [exact H3|]. repeat split; congruence.
Qed.

Lemma bo_frameless am : (forall i, ss_fr (nth_slot am i) = None) -> blocks_of0 am = [].
Proof. intros H. rewrite <- (map_fst_blocks_of (am_mem am) am), blocks_of_frameless by exact H. reflexivity. Qed.

Lemma bo_prj a a' : prj a = prj a' -> blocks_of0 a = blocks_of0 a'.
Proof.
  intros E. destruct (prj_geo _ _ E) as (_ & L & _ & _). unfold blocks_of0. rewrite L. apply flat_map_ext.
  intros i. unfold slot_block0. rewrite (prj_fr _ _ i E), (prj_slot_start _ _ i E). reflexivity.
Qed.

Lemma CL_corr X s X' s' : Xok X s -> corr X s X' s' -> CL s s'.
Proof.
  intros XO [CB CF] g a M Hb.
  assert (NX : memb g X = false).
  { destruct (memb g X) eqn:E; [|reflexivity]. exfalso. apply memb_In in E. destruct (XO g E) as [_ XM].
    rewrite M in XM. destruct XM as (_ & _ & Hfl). exact (Hb (bo_frameless a Hfl)). }
  destruct (CF g a (usedX_intro X s g a NX M)) as (a' & U' & E). exists a'.
  split; [exact (proj1 (usedX_MT _ _ _ _ U'))|]. destruct (prj_geo _ _ E) as (_ & L & S & _).
  split; [congruence|]. split; [congruence|]. symmetry. apply bo_prj. exact E.
Qed.

Lemma CL_RT s s' : RT s s' -> CL s s'.
Proof.
  intros (HM & _) g a M Hb. specialize (HM g). unfold MS in HM. rewrite M in HM.
  destruct (MT s' g) as [[pr nx| |a']|] eqn:M'; try discriminate. assert (E : prj a' = prj a) by congruence.
  exists a'. split; [reflexivity|]. destruct (prj_geo _ _ E) as (_ & L & S & _). split; [exact S|]. split; [exact L|].
  apply bo_prj. exact E.
Qed.

Lemma CL_metas s s' : st_metas s' = st_metas s -> CL s s'.
Proof. intros E g a M _. exists a. unfold MT in *. rewrite E. repeat split; auto. Qed.

Lemma CL_upd_X s s' m : (forall q, q <> m -> MT s' q = MT s q) ->
  (forall a, MT s m = Some (MUsed a) -> blocks_of0 a = []) -> CL s s'.
Proof.
  intros EO Hm g a M Hb. destruct (sptr_eq_dec g m) as [->|Hg]; [exfalso; exact (Hb (Hm a M))|].
  exists a. rewrite (EO g Hg). repeat split; auto.
Qed.

Lemma CL_upd_geom s s' g am am' : MT s g = Some (MUsed am) -> MT s' g = Some (MUsed am') ->
  (forall q, q <> g -> MT s' q = MT s q) -> am_sc am' = am_sc am -> am_last am' = am_last am ->
  blocks_of0 am' = blocks_of0 am -> CL s s'.
Proof.
  intros Mg EM EO S L B q a M Hb. destruct (sptr_eq_dec q g) as [->|Hq].
  - rewrite Mg in M. injection M as <-. exists am'. repeat split; auto.
  - exists a. rewrite (EO q Hq). repeat split; auto.
Qed.

Lemma Xok_bo X s m a : Xok X s -> In m X -> MT s m = Some (MUsed a) -> blocks_of0 a = [].
Proof. intros XO Hm M. destruct (XO m Hm) as [_ XM]. rewrite M in XM. destruct XM as (_ & _ & Hfl). exact (bo_frameless a Hfl). Qed.

Definition ucls (c : Z) (x : option mslot) : list (sptr * Z) :=
  match x with Some (MUsed am) => if (am_sc am =? c) && (1 <=? am_last am) then blocks_of0 am else [] | _ => [] end.

Lemma ub_cls_keys s c : NoDup (keys s) -> ub_cls s c = flat_map (fun g => ucls c (MT s g)) (keys s).
Proof.
  unfold ub_cls, used_metas, keys, MT. generalize (st_metas s) as l. clear s.
  induction l as [|[p x] t IH]; intros ND; cbn; [reflexivity|].
  inversion ND as [|p' t' Hp Ht]; subst. rewrite sptr_eqb_refl.
  assert (E : flat_map (fun g => ucls c (mlookup ((p, x) :: t) g)) (map fst t) = flat_map (fun g => ucls c (mlookup t g)) (map fst t)).
  { apply flat_map_ext_In. intros g Hg. cbn. destruct (sptr_eqb g p) eqn:Eg; [|reflexivity].
    apply sptr_eqb_eq in Eg. subst g. exfalso. exact (Hp Hg). }
  cbn in E. rewrite E, <- (IH Ht). destruct x as [| |am]; cbn; reflexivity.
Qed.

Lemma ucls_nil c x : ucontrib0 x = [] -> ucls c x = [].
Proof. destruct x as [[| |am]|]; cbn; intros H; try reflexivity. rewrite H. destruct (_ && _); reflexivity. Qed.

Lemma ub_cls_same s s' c : NoDup (keys s) -> NoDup (keys s') -> ub_same s s' -> CL s s' -> ub_cls s' c = ub_cls s c.
Proof.
  intros N N' (ext & K & Zx & Sm) HC. rewrite (ub_cls_keys s c N), (ub_cls_keys s' c N'), K, flat_map_app.
  rewrite (flat_map_nil_In _ ext).
  2:{ intros m Hm. apply ucls_nil. rewrite <- (map_fst_ucontrib m), (Zx m Hm). reflexivity. }
  rewrite app_nil_r. apply flat_map_ext_In. intros g Hg.
  specialize (Sm g Hg). apply (f_equal (map fst)) in Sm. rewrite !map_fst_ucontrib in Sm.
  destruct (MT s g) as [[pr nx| |a]|] eqn:M.
  1,2,4: apply ucls_nil; exact Sm.
  destruct (blocks_of0 a) as [|b bl] eqn:B.
  - cbn [ucontrib0] in Sm. rewrite B in Sm. rewrite (ucls_nil c _ Sm). cbn [ucls]. rewrite B. destruct (_ && _); reflexivity.
  - destruct (HC g a M ltac:(rewrite B; discriminate)) as (a' & M' & S' & L' & B'). rewrite M'. cbn [ucls].
    rewrite S', L', B', B. reflexivity.
Qed.

Lemma UPB_eq s s' L : user_blocks s' = user_blocks s -> (forall c, ub_cls s' c = ub_cls s c) -> UPB s L -> UPB s' L.
Proof.
  intros E1 E2 [U1 U2]. split.
  - intros k Hk. unfold bcount. rewrite E1. exact (U1 k Hk).
  - intros c Hc. unfold bcount, upc. rewrite E1, E2. exact (U2 c Hc).
Qed.

Lemma UPB_same s s' L : NoDup (keys s) -> NoDup (keys s') -> ub_same s s' -> CL s s' -> UPB s L -> UPB s' L.
Proof.
  intros N N' UB HC. apply UPB_eq; [exact (ub_same_user_blocks s s' N N' UB) | intros c; exact (ub_cls_same s s' c N N' UB HC)].
Qed.

Lemma usage_RT X R R' U s s' c : Inv X R U s -> Inv X R' U s' -> RT s s' -> 0 <= c < 48 -> usage_of s' c = usage_of s c.
Proof.
  intros HI HI' (HM & _ & _ & K) Hc. rewrite (inv_usage HI' c Hc), (inv_usage HI c Hc). f_equal. unfold class_sum. rewrite K.
  assert (EC : forall g, contrib X s' c g = contrib X s c g).
  { intros g. unfold contrib, MTX. destruct (memb g X); [reflexivity|]. specialize (HM g). unfold MS in HM.
    destruct (MT s' g) as [[| |a']|], (MT s g) as [[| |a]|]; try discriminate; try reflexivity.
    assert (E : prj a' = prj a) by congruence. destruct (prj_geo _ _ E) as (_ & L & S & _). rewrite L, S. reflexivity. }
  clear K. induction (keys s) as [|g l IH]; cbn [fold_right]; [reflexivity|]. rewrite IH, EC. reflexivity.
Qed.

Lemma usage_ig m sc cnt aidx maplen mem sl s c : 0 <= c < sc ->
  usage_of (ig_st m sc cnt aidx maplen mem sl s) c = usage_of s c.
Proof.
  intros Hc. unfold usage_of, ig_st, set_head_st. cbn [st_usage set_active upd_meta set_metas set_usage].
  rewrite znth_zset by lia. rewrite (proj2 (Z.eqb_neq c sc)) by lia. reflexivity.
Qed.
