From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0y YO03 YO0m YO0p.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import AllocSI AllocGS AllocMalloc AllocCount AllocPack AllocPackMallocN AllocPackMallocW.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zsumZ_cons f x l : zsumZ f (x :: l) = f x + zsumZ f l.
Proof. reflexivity. Qed.

Lemma zsumZ_ext_In (f g : Z -> Z) l : (forall x, In x l -> f x = g x) -> zsumZ f l = zsumZ g l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. rewrite !zsumZ_cons, (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma zsumZ_mono (f g : Z -> Z) l : (forall x, In x l -> f x <= g x) -> zsumZ f l <= zsumZ g l.
Proof.
  induction l as [|x l IH]; intros H; [unfold zsumZ; cbn [fold_right]; lia|]. rewrite !zsumZ_cons.
  pose proof (H x (or_introl eq_refl)). assert (zsumZ f l <= zsumZ g l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsumZ_add (f g : Z -> Z) l : zsumZ (fun x => f x + g x) l = zsumZ f l + zsumZ g l.
Proof. induction l as [|x l IH]; [reflexivity|]. rewrite !zsumZ_cons, IH. lia. Qed.

Lemma zsumZ_const k l : zsumZ (fun _ => k) l = k * Z.of_nat (length l).
Proof. induction l as [|x l IH]; [unfold zsumZ; cbn [fold_right length]; lia|]. rewrite zsumZ_cons, IH. cbn [length]. lia. Qed.

Lemma zseq_len lo n : length (zseq lo n) = Z.to_nat n.
Proof. unfold zseq. rewrite length_map, length_seq. reflexivity. Qed.

Lemma len_flat_map_Z {B} (f : Z -> list B) l : Z.of_nat (length (flat_map f l)) = zsumZ (fun x => Z.of_nat (length (f x))) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, zsumZ_cons, <- IH. lia. Qed.

Lemma nd_app {A} (l1 l2 : list A) : NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros N1 N2 D; cbn [app]; [exact N2|].
  inversion N1 as [|a' l1' Ha Hl]; subst. constructor.
  - rewrite in_app_iff. intros [H|H]; [exact (Ha H) | exact (D a (or_introl eq_refl) H)].
  - apply IH; [exact Hl | exact N2 |]. intros x Hx. apply D. right. exact Hx.
Qed.

Lemma nd_map_pair {A} (g : A) (z : list Z) : NoDup z -> NoDup (map (fun i => (g, i)) z).
Proof.
  induction z as [|i z IH]; intros N; cbn [map]; [constructor|]. inversion N as [|i' z' Hi Hz]; subst.
  constructor; [|apply IH; exact Hz]. intros H. apply in_map_iff in H as (j & E & Hj). injection E as E. subst. contradiction.
Qed.

Lemma nd_pairs {A} (G : list A) (z : list Z) : NoDup G -> NoDup z -> NoDup (flat_map (fun g => map (fun i => (g, i)) z) G).
Proof.
  induction G as [|g G IH]; intros NG Nz; cbn [flat_map]; [constructor|].
  inversion NG as [|g' G' Hg HG]; subst. apply nd_app; [apply nd_map_pair, Nz | apply IH; assumption |].
  intros [x i] H1 H2. apply in_map_iff in H1 as (j & E & _). injection E as E1 _. subst x.
  apply in_flat_map in H2 as (g' & Hg' & H2). apply in_map_iff in H2 as (k & E & _). injection E as E2 _. subst g'.
  contradiction.
Qed.

Lemma len_pairs {A} (G : list A) (z : list Z) : length (flat_map (fun g => map (fun i => (g, i)) z) G) = (length G * length z)%nat.
Proof. induction G as [|g G IH]; [reflexivity|]. cbn [flat_map length]. rewrite length_app, length_map, IH. lia. Qed.

Lemma user_blocks_eq s : user_blocks s = flat_map (fun gm => blocks_of0 (snd gm)) (used_metas s).
Proof. reflexivity. Qed.

Lemma ub_cls_eq s c : ub_cls s c =
  flat_map (fun gm => if (am_sc (snd gm) =? c) && (1 <=? am_last (snd gm)) then blocks_of0 (snd gm) else []) (used_metas s).
Proof. reflexivity. Qed.

Lemma in_blocks0 am i fr : 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser ->
  In (frame_ptr am i fr, fr_n fr) (blocks_of0 am).
Proof.
  intros Hi Hf Hk. unfold blocks_of0. apply in_flat_map. exists i. split; [apply In_zseq; lia|].
  unfold slot_block0. rewrite Hf, Hk. left. reflexivity.
Qed.

Lemma in_ub X s g am i fr : NoDup (keys s) -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> In (frame_ptr am i fr, fr_n fr) (user_blocks s).
Proof.
  intros N U Hi Hf Hk. rewrite user_blocks_eq. apply in_flat_map. exists (g, am).
  split; [apply used_metas_iff; [exact N | exact (proj1 (usedX_MT _ _ _ _ U))] | apply in_blocks0; assumption].
Qed.

Lemma in_ubc X s c g am i fr : NoDup (keys s) -> usedX X s g am -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FUser -> am_sc am = c -> 1 <= am_last am ->
  In (frame_ptr am i fr, fr_n fr) (ub_cls s c).
Proof.
  intros N U Hi Hf Hk Hs Hl. rewrite ub_cls_eq. apply in_flat_map. exists (g, am).
  split; [apply used_metas_iff; [exact N | exact (proj1 (usedX_MT _ _ _ _ U))]|]. cbn [snd].
  rewrite (proj2 (Z.eqb_eq _ _) Hs), (proj2 (Z.leb_le 1 _) Hl). cbn [andb]. apply in_blocks0; assumption.
Qed.

Lemma count_red X R s c : Inv X R U0 s -> 0 <= c < 48 -> gcountX X s (gred c) <= usage_of s c.
Proof.
  intros HI Hc. rewrite (inv_usage HI c Hc). unfold U0. rewrite Z.add_0_r. unfold class_sum. rewrite gcount_PP.
  induction (keys s) as [|g l IH]; cbn [filter fold_right length]; [lia|].
  assert (C0 : 0 <= contrib X s c g).
  { unfold contrib. destruct (MTX X s g) as [[| |am]|] eqn:E; try lia. destruct (am_sc am =? c); [|lia].
    pose proof (inv_groups HI g am E) as ((Hl & _) & _). lia. }
  destruct (PP X s (gred c) g) eqn:P; cbn [length]; [|lia].
  assert (C1 : 1 <= contrib X s c g).
  { apply PP_iff in P as (am & U & F). unfold contrib. unfold usedX in U. rewrite U. unfold gred in F.
    apply andb_prop in F as [F _]. rewrite F. pose proof (inv_groups HI g am U) as ((Hl & _) & _). lia. }
  lia.
Qed.

Lemma bo_len am : 0 <= am_last am -> Z.of_nat (length (blocks_of0 am)) <= am_last am + 1.
Proof.
  intros H. unfold blocks_of0.
  assert (G : forall l, (length (flat_map (slot_block0 am) l) <= length l)%nat).
  { induction l as [|i l IH]; [cbn; lia|]. cbn [flat_map length]. rewrite length_app.
    assert (length (slot_block0 am i) <= 1)%nat.
    { unfold slot_block0. destruct (ss_fr (nth_slot am i)) as [fr|]; [destruct (fr_kind fr)|]; cbn; lia. }
    lia. }
  pose proof (G (zseq 0 (am_last am + 1))) as T. rewrite zseq_len in T. lia.
Qed.

Lemma ub_cls_len R s c : Inv [] R U0 s -> 0 <= c < 48 -> Z.of_nat (length (ub_cls s c)) <= usage_of s c.
Proof.
  intros HI Hc. rewrite (ub_cls_keys s c (proj1 (inv_keys HI))), (inv_usage HI c Hc). unfold U0. rewrite Z.add_0_r.
  unfold class_sum. induction (keys s) as [|g l IH]; [cbn [flat_map fold_right length]; lia|]. cbn [flat_map fold_right]. rewrite length_app.
  assert (Z.of_nat (length (ucls c (MT s g))) <= contrib [] s c g).
  { unfold contrib, MTX. cbn [memb existsb]. destruct (MT s g) as [[| |am]|] eqn:E; cbn [ucls length]; try lia.
    pose proof (inv_groups HI g am (usedX_intro [] s g am eq_refl E)) as ((Hl0 & _) & _).
    destruct (am_sc am =? c) eqn:E1; destruct (1 <=? am_last am) eqn:E2; cbn [andb length]; try lia.
    apply Z.leb_le in E2. apply bo_len. lia. }
  lia.
Qed.

Definition tdec : forall x y : (sptr * Z) + sptr, {x = y} + {x <> y}.
Proof.
  intros [[p a]|p] [[q b]|q]; try (right; discriminate).
  - destruct (ac_sdec p q) as [<-|N]; [|right; congruence].
    destruct (Z.eq_dec a b) as [<-|N]; [left; reflexivity | right; congruence].
  - destruct (ac_sdec p q) as [<-|N]; [left; reflexivity | right; congruence].
Defined.

Section cnt.
Variables (X : list sptr) (R : option (sptr * Z)) (s : astate) (caps L : list Z) (c : Z).
Hypothesis HI : Inv X R U0 s.
Hypothesis HR : forall g i am, R = Some (g, i) -> usedX X s g am -> am_sc am <> c.
Hypothesis Hhd : active_hd s c = None.
Hypothesis HCO : children_ok X s.
Hypothesis HPS : PKS X s.
Hypothesis HPC : PKC X caps s.
Hypothesis HUP : UPB s L.
Hypothesis HL : forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps.
Hypothesis Hc : 0 <= c < 48.

Definition GF : list sptr := filter (PP X s (gfull c)) (keys s).

Definition SL : list (sptr * Z) := flat_map (fun g => map (fun i => (g, i)) (zseq 0 (FC c))) GF.

Definition KIDS : list sptr :=
  flat_map (fun k => (if jof k (FC k) =? c then filter (PP X s (gfull k)) (keys s) else []) ++ filter (PP X s (gred k)) (keys s))
    (zseq 0 c).

Definition TG : list ((sptr * Z) + sptr) :=
  map inl (filter (fun b => band (snd b) =? c) (user_blocks s)) ++
  (if 1 <=? c then map inl (filter (fun b => band (snd b) =? c - 1) (ub_cls s c)) else []) ++ map inr KIDS.

Definition Rel (a : sptr * Z) (t : (sptr * Z) + sptr) : Prop :=
  match t with
  | inl b => exists am fr, usedX X s (fst a) am /\ 0 <= snd a <= am_last am /\ ss_fr (nth_slot am (snd a)) = Some fr /\
      fr_kind fr = FUser /\ b = (frame_ptr am (snd a) fr, fr_n fr)
  | inr cg => exists am fr ac, usedX X s (fst a) am /\ 0 <= snd a <= am_last am /\ ss_fr (nth_slot am (snd a)) = Some fr /\
      fr_kind fr = FGroup /\ usedX X s cg ac /\ am_mem ac = slot_start am (snd a)
  end.

Lemma full_frame g am i : usedX X s g am -> gfull c am = true -> 0 <= i <= am_last am ->
  exists fr, ss_fr (nth_slot am i) = Some fr /\ frame_ok am i fr.
Proof.
  intros U F Hi. unfold gfull in F. apply andb_prop in F as [F1 F2]. apply Z.eqb_eq in F1. apply Z.eqb_eq in F2.
  destruct (inv_rings HI) as (_ & A & _). destruct (A c Hc) as (ms & Rg & _ & Full & _).
  destruct Rg as [_ Eh]. rewrite Hhd in Eh. destruct ms as [|m0 ms]; [|discriminate].
  destruct (Full g am U F1 (fun H => H)) as [Av Fr].
  pose proof (inv_groups HI g am U) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3). revert S3.
  destruct (ss_fr (nth_slot am i)) as [fr|] eqn:E; intros S3.
  - destruct S3 as (_ & _ & FO & _). exists fr. auto.
  - exfalso. destruct S3 as [S3|S3].
    + unfold allocated in S3. rewrite Av, Fr, Z.lor_0_l, Z.bits_0 in S3. discriminate.
    + exact (HR g i am S3 U F1).
Qed.

Lemma full_user_band g am i fr : usedX X s g am -> gfull c am = true -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> frame_ok am i fr -> fr_kind fr = FUser ->
  band (fr_n fr) = c \/ (1 <= c /\ band (fr_n fr) = c - 1).
Proof.
  intros U F Hi Hfr FO Hk. unfold gfull in F. apply andb_prop in F as [F1 F2]. apply Z.eqb_eq in F1. apply Z.eqb_eq in F2.
  destruct HPS as (P1 & _). destruct (P1 g am i fr U ltac:(lia) Hi Hfr Hk) as [Hn Hsc].
  pose proof (FC_bounds c Hc) as FB.
  assert (ST : stride_of am = class_size c).
  { unfold stride_of. rewrite (proj2 (Z.eqb_neq (am_last am) 0)) by lia. cbn [andb]. rewrite F1. reflexivity. }
  destruct FO as (N0 & O0 & B0 & _). rewrite ST in B0.
  assert (Hle : size_to_class (fr_n fr) <= c) by (apply stc_le; [lia | lia | unfold UNIT in B0; lia]).
  pose proof (size_to_class_range (fr_n fr) ltac:(lia)) as [Hr _].
  unfold band. rewrite (proj2 (Z.leb_gt MMAP_THRESHOLD (fr_n fr))) by lia. lia.
Qed.

Lemma kid_in g am i fr : usedX X s g am -> gfull c am = true -> 0 <= i <= am_last am ->
  ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FGroup ->
  exists cg ac, In cg KIDS /\ usedX X s cg ac /\ am_mem ac = slot_start am i.
Proof.
  intros U F Hi Hfr Hk. destruct (HCO g am i fr U Hi Hfr Hk) as (cg & ac & Uc & Ml & Mm & Lt).
  exists cg, ac. split; [|split; [exact Uc | exact Mm]].
  unfold gfull in F. apply andb_prop in F as [F1 _]. apply Z.eqb_eq in F1.
  destruct HPS as (_ & P2 & P3 & _). pose proof (P2 g am i fr cg ac U Hi Hfr Hk Uc Ml Mm) as J. rewrite F1 in J, Lt.
  assert (C0 : 0 <= am_sc ac).
  { pose proof (inv_groups HI cg ac Uc) as (_ & _ & _ & Gc & _). destruct Gc as [(E63 & _)|(Hr & _)]; lia. }
  pose proof (P3 cg ac Uc ltac:(lia)) as Hl.
  unfold KIDS. apply in_flat_map. exists (am_sc ac). split; [apply In_zseq; lia|]. apply in_app_iff.
  destruct (Z.eq_dec (am_last ac + 1) (FC (am_sc ac))) as [Ef|Ef].
  - left. rewrite Ef in J. rewrite (proj2 (Z.eqb_eq _ _) (eq_sym J)). apply filter_In.
    split; [exact (usedX_keys _ _ _ _ Uc)|]. apply PP_iff. exists ac. split; [exact Uc|].
    unfold gfull. apply andb_true_iff. split; apply Z.eqb_eq; [reflexivity | exact Ef].
  - right. apply filter_In. split; [exact (usedX_keys _ _ _ _ Uc)|]. apply PP_iff. exists ac. split; [exact Uc|].
    unfold gred. apply andb_true_iff. split; [apply Z.eqb_eq; reflexivity | apply Z.ltb_lt; lia].
Qed.

Lemma SL_TG : (length SL <= length TG)%nat.
Proof.
  pose proof (proj1 (inv_keys HI)) as ND.
  apply (ac_count tdec Rel SL TG); [apply nd_pairs; [apply NoDup_filter, ND | apply zseq_NoDup] | |].
  - intros [g i] Hin. unfold SL in Hin. apply in_flat_map in Hin as (g' & Hg' & Hgi).
    apply in_map_iff in Hgi as (i' & E & Hi'). injection E as E1 E2. subst g' i'.
    unfold GF in Hg'. apply filter_In in Hg' as [_ Hg']. apply PP_iff in Hg' as (am & U & F).
    apply In_zseq in Hi'. pose proof F as F'. unfold gfull in F'. apply andb_prop in F' as [F1 F2].
    apply Z.eqb_eq in F1. apply Z.eqb_eq in F2.
    assert (Hi : 0 <= i <= am_last am) by lia.
    destruct (full_frame g am i U F Hi) as (fr & Hfr & FO). destruct (fr_kind fr) eqn:Hk.
    + pose proof (FC_bounds c Hc) as FB.
      destruct (full_user_band g am i fr U F Hi Hfr FO Hk) as [B|[C1 B]].
      * exists (inl (frame_ptr am i fr, fr_n fr)). split.
        -- unfold TG. apply in_app_iff. left. apply in_map. apply filter_In.
           split; [exact (in_ub X s g am i fr ND U Hi Hfr Hk)|]. cbn [snd]. rewrite B. apply Z.eqb_refl.
        -- cbn [Rel fst snd]. exists am, fr. repeat split; auto; lia.
      * exists (inl (frame_ptr am i fr, fr_n fr)). split.
        -- unfold TG. apply in_app_iff. right. apply in_app_iff. left. rewrite (proj2 (Z.leb_le 1 c) C1).
           apply in_map. apply filter_In.
           split; [exact (in_ubc X s c g am i fr ND U Hi Hfr Hk F1 ltac:(lia))|]. cbn [snd]. rewrite B. apply Z.eqb_refl.
        -- cbn [Rel fst snd]. exists am, fr. repeat split; auto; lia.
    + destruct (kid_in g am i fr U F Hi Hfr Hk) as (cg & ac & Hk' & Uc & Mm). exists (inr cg). split.
      * unfold TG. apply in_app_iff. right. apply in_app_iff. right. apply in_map. exact Hk'.
      * cbn [Rel fst snd]. exists am, fr, ac. repeat split; auto; lia.
  - intros [g i] [g' i'] t _ _ R1 R2. destruct t as [b|cg]; cbn [Rel fst snd] in R1, R2.
    + destruct R1 as (am & fr & U & Hi & Hfr & Hk & Eb). destruct R2 as (am' & fr' & U' & Hi' & Hfr' & Hk' & Eb').
      rewrite Eb in Eb'. injection Eb' as Ep _.
      destruct (frame_ptrs_distinct X R U0 s HI g am i fr g' am' i' fr' U U' Hi Hi' Hfr Hfr' Ep) as [-> ->]. reflexivity.
    + destruct R1 as (am & fr & ac & U & Hi & Hfr & Hk & Uc & Mm).
      destruct R2 as (am' & fr' & ac' & U' & Hi' & Hfr' & Hk' & Uc' & Mm').
      rewrite (usedX_fun _ _ _ _ _ Uc Uc') in Mm. rewrite Mm in Mm'.
      destruct (slot_starts_distinct X R U0 s HI g am i g' am' i' U U' Hi Hi' Mm') as [-> ->]. reflexivity.
Qed.

Lemma len_KIDS : Z.of_nat (length KIDS) =
  zsumZ (fun k => (if jof k (FC k) =? c then gcountX X s (gfull k) else 0) + gcountX X s (gred k)) (zseq 0 c).
Proof.
  unfold KIDS. rewrite len_flat_map_Z. apply zsumZ_ext_In. intros k _. rewrite length_app, Nat2Z.inj_add.
  rewrite !gcount_PP. destruct (jof k (FC k) =? c); reflexivity.
Qed.

Theorem count_full : gcountX X s (gfull c) + 1 <= znth c (NF caps).
Proof.
  pose proof SL_TG as LT. pose proof (FC_bounds c Hc) as FB.
  assert (E1 : Z.of_nat (length SL) = gcountX X s (gfull c) * FC c).
  { unfold SL. rewrite len_pairs, zseq_len, Nat2Z.inj_mul, Z2Nat.id by lia. rewrite gcount_PP. reflexivity. }
  assert (E2 : Z.of_nat (length TG) = bcount s c + (if 1 <=? c then upc s c else 0) + Z.of_nat (length KIDS)).
  { unfold TG, bcount, upc. rewrite !length_app, !length_map. destruct (1 <=? c); rewrite ?length_map; cbn [length]; lia. }
  assert (K1 : Z.of_nat (length KIDS) <=
    zsumZ (fun k => if jof k (FC k) =? c then znth k (NF caps) else 0) (zseq 0 c) + RED * c).
  { rewrite len_KIDS.
    replace (RED * c) with (zsumZ (fun _ => RED) (zseq 0 c)) by (rewrite zsumZ_const, zseq_len, Z2Nat.id by lia; lia).
    rewrite <- zsumZ_add. apply zsumZ_mono. intros k Hk. apply In_zseq in Hk.
    destruct (HPC k ltac:(lia)) as [Q1 Q2]. destruct (jof k (FC k) =? c); lia. }
  assert (U : bcount s c + (if 1 <=? c then upc s c else 0) <= znth c caps + COARSE).
  { destruct HUP as [U1 U2]. pose proof (HL c ltac:(lia)) as Lc. unfold COARSE.
    destruct (1 <=? c) eqn:E; [apply Z.leb_le in E; pose proof (U2 c ltac:(lia)); unfold COARSE in *; lia|].
    pose proof (U1 c ltac:(lia)). lia. }
  rewrite (nf_at caps c Hc). unfold nf_next.
  rewrite (zsumZ_ext_In (fun c' => if jof c' (FC c') =? c then znth c' (nf_build caps (Z.to_nat c)) else 0)
    (fun c' => if jof c' (FC c') =? c then znth c' (NF caps) else 0)).
  2:{ intros k Hk. apply In_zseq in Hk. rewrite (nf_prefix caps c k) by lia. reflexivity. }
  enough (gcountX X s (gfull c) <= (znth c caps + COARSE +
    zsumZ (fun c' => if jof c' (FC c') =? c then znth c' (NF caps) else 0) (zseq 0 c) + RED * c) / FC c) by lia.
  apply Z.div_le_lower_bound; [lia|]. lia.
Qed.

End cnt.
