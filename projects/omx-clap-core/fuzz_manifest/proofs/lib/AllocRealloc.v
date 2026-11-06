From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0g YO0h YO0w YO0s YO11 YO15 YO12 YO0z YO14 YO0u YO0q YO0v YO0t YO0x YO03 YO0m YO0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import AllocSI AllocGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require AllocMalloc AllocFree AllocDepth.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Fixpoint rpath {A : Type} (F : kreq -> Z -> Prop) (t : itree astate A) (tr : list (kreq * Z)) (a : A) : Prop :=
  match t, tr with
  | IRet a', [] => a' = a
  | IAsk q _ k, (q', z) :: tr' => q' = q /\ F q z /\ rpath F (k z) tr' a
  | _, _ => False
  end.

Lemma rpath_yields {A} (t : itree astate A) tr a : yields t tr a -> rpath answer_ok t tr a.
Proof.
  revert tr. induction t as [a' | q sn k IH | f]; intros [|[q' z] tr] H; cbn in *; try exact H; try contradiction.
  destruct H as (E & Hz & H). split; [exact E|]. split; [exact Hz | apply IH; exact H].
Qed.

Lemma yields_rpath {A} (t : itree astate A) tr a : rpath answer_ok t tr a -> yields t tr a.
Proof.
  revert tr. induction t as [a' | q sn k IH | f]; intros [|[q' z] tr] H; cbn in *; try exact H; try contradiction.
  destruct H as (E & Hz & H). split; [exact E|]. split; [exact Hz | apply IH; exact H].
Qed.

Lemma rpath_cpath04 {A} (t : itree astate A) tr a : cpath04 t tr a -> rpath canswer04 t tr a.
Proof.
  revert tr. induction t as [a' | q sn k IH | f]; intros [|[q' z] tr] H; cbn in *; try exact H; try contradiction.
  destruct H as (E & Hz & H). split; [exact E|]. split; [exact Hz | apply IH; exact H].
Qed.

Lemma cpath04_rpath {A} (t : itree astate A) tr a : rpath canswer04 t tr a -> cpath04 t tr a.
Proof.
  revert tr. induction t as [a' | q sn k IH | f]; intros [|[q' z] tr] H; cbn in *; try exact H; try contradiction.
  destruct H as (E & Hz & H). split; [exact E|]. split; [exact Hz | apply IH; exact H].
Qed.

Lemma rpath_ibind_inv {A B} F (t : itree astate A) (f : A -> itree astate B) tr b :
  rpath F (ibind t f) tr b -> exists tr1 a tr2, tr = tr1 ++ tr2 /\ rpath F t tr1 a /\ rpath F (f a) tr2 b.
Proof.
  revert tr. induction t as [a' | q sn k IH | e]; intros tr H.
  - exists [], a', tr. split; [reflexivity|]. split; [reflexivity | exact H].
  - destruct tr as [|[q' z] tr]; cbn in H; [destruct H|]. destruct H as (Eq & Fz & H).
    destruct (IH z tr H) as (tr1 & a & tr2 & -> & H1 & H2).
    exists ((q', z) :: tr1), a, tr2. split; [reflexivity|]. split; [cbn; auto | exact H2].
  - destruct tr; cbn in H; destruct H.
Qed.

Lemma rpath_bind_inv {A B} F (m : M A) (f : A -> M B) s tr b :
  rpath F (bind m f s) tr b ->
  exists tr1 a s1 tr2, tr = tr1 ++ tr2 /\ rpath F (m s) tr1 (a, s1) /\ rpath F (f a s1) tr2 b.
Proof.
  intros H. unfold bind in H. destruct (rpath_ibind_inv F _ _ _ _ H) as (tr1 & [a s1] & tr2 & E & H1 & H2).
  exists tr1, a, s1, tr2. auto.
Qed.

Definition rs_am (am : ameta) (i off n : Z) : ameta :=
  upd_slot am i (resize_slot (stride_of am) i (nth_slot am i) off n).

Definition rm_need (n off : Z) : Z := page_round (n + UNIT * off + UNIT + IB).

Definition rm_am (s : astate) (am : ameta) (i off n : Z) : ameta :=
  remap_am am (length (st_regions s)) (rm_need n off / 4096) i off n.

Definition rm_mid (s : astate) (g : sptr) (am : ameta) (i off n : Z) : astate :=
  upd_meta g (MUsed (rm_am s am i off n)) (set_regions (st_regions s ++ [mkRegion RkMap (rm_need n off) [] true]) s).

Definition rm_state (s : astate) (g : sptr) (am : ameta) (i off n : Z) : astate :=
  set_regions (lupd (st_regions (rm_mid s g am i off n)) (prid (am_mem am))
    (mkRegion RkMap (rg_len (nth (prid (am_mem am)) (st_regions (rm_mid s g am i off n)) (mkRegion RkMap 0 [] false))) [] false))
    (rm_mid s g am i off n).

Definition ra_c1 (am : ameta) (off n : Z) : bool :=
  (n <=? stride_of am - IB - UNIT * off) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1).

Lemma ra_ffe p s x : find_frame_in (st_metas s) p = Some x -> find_frame p s = IRet (x, s).
Proof. intros H. unfold find_frame, bind, get, ret. cbn [ibind]. rewrite H. reflexivity. Qed.

Lemma ra_getm p s am : MT s p = Some (MUsed am) -> getm p s = IRet (am, s).
Proof. intros H. unfold getm, bind, get, ret. cbn [ibind]. unfold MT in H. rewrite H. reflexivity. Qed.

Ltac ra_red H := cbn [ibind fst snd bind setm modify ret massert mcheck ask get put new_region upd_region] in H.

Lemma ra_shape F s p n g i am fr tr r s' :
  size_overflows n = false -> find_frame_in (st_metas s) p = Some (g, i) -> MT s g = Some (MUsed am) ->
  ss_fr (nth_slot am i) = Some fr ->
  rpath F (realloc (Some p) n s) tr (r, s') ->
  (ra_c1 am (fr_off fr) n = true /\ r = Some p /\ s' = upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s)
  \/ (am_sc am = 63 /\ MMAP_THRESHOLD <= n /\ am_maplen am * 4096 = rm_need n (fr_off fr) /\
      r = Some p /\ s' = upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s)
  \/ (am_sc am = 63 /\ MMAP_THRESHOLD <= n /\ am_maplen am * 4096 <> rm_need n (fr_off fr) /\
      r = Some (padd (slot_start (rm_am s am i (fr_off fr) n) i) (UNIT * fr_off fr)) /\
      s' = rm_state s g am i (fr_off fr) n)
  \/ (exists tr', rpath F (realloc_move p n s) tr' (r, s')).
Proof.
  intros Hov Hff Hm Hfr H.
  unfold realloc in H. rewrite Hov in H. unfold bind in H.
  rewrite (ra_ffe p s (g, i) Hff) in H. cbn [ibind fst snd] in H.
  rewrite (ra_getm g s am Hm) in H. cbn [ibind] in H. rewrite Hfr in H.
  unfold ra_c1, rm_need.
  destruct ((n <=? stride_of am - IB - UNIT * fr_off fr) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1)) eqn:E1.
  - left. ra_red H. destruct tr; cbn [rpath] in H; [|contradiction]. injection H as <- <-.
    split; [reflexivity|]. split; reflexivity.
  - right. destruct ((48 <=? am_sc am) && (MMAP_THRESHOLD <=? n)) eqn:E2.
    + apply andb_prop in E2 as [E2a E2b]. apply Z.leb_le in E2a. apply Z.leb_le in E2b.
      destruct (am_sc am =? 63) eqn:E3; [apply Z.eqb_eq in E3 | ra_red H; destruct tr; cbn [rpath] in H; contradiction].
      ra_red H. destruct (am_maplen am * 4096 =? page_round (n + UNIT * fr_off fr + UNIT + IB)) eqn:E4.
      * left. apply Z.eqb_eq in E4. ra_red H. destruct tr; cbn [rpath] in H; [|contradiction]. injection H as <- <-.
        split; [exact E3|]. split; [exact E2b|]. split; [exact E4|]. split; reflexivity.
      * apply Z.eqb_neq in E4. destruct tr as [|[q z] tr]; cbn [rpath] in H; [contradiction|].
        destruct H as (_ & _ & H). destruct (negb (z =? 0)) eqn:E5.
        -- right. left. ra_red H. destruct tr; cbn [rpath] in H; [|contradiction]. injection H as <- <-.
           split; [exact E3|]. split; [exact E2b|]. split; [exact E4|]. split; reflexivity.
        -- right. right. exists tr. exact H.
    + right. right. exists tr. exact H.
Qed.

Lemma ra_move F p n s tr r s' :
  rpath F (realloc_move p n s) tr (r, s') ->
  exists tr1 q s1, rpath F (malloc n s) tr1 (q, s1) /\
  match q with
  | None => r = None /\ s' = s1
  | Some q => r = Some q /\ exists tr2, rpath F (free (Some p) s1) tr2 (tt, s')
  end.
Proof.
  intros H. unfold realloc_move in H. destruct (rpath_bind_inv F _ _ _ _ _ H) as (tr1 & q & s1 & tr2 & _ & H1 & H2).
  exists tr1, q, s1. split; [exact H1|]. cbv beta iota in H2. destruct q as [q|].
  - destruct (rpath_bind_inv F _ _ _ _ _ H2) as (tr3 & [] & s2 & tr4 & _ & H3 & H4).
    cbv beta in H4. unfold ret in H4. destruct tr4; cbn [rpath] in H4; [|contradiction]. injection H4 as <- <-.
    split; [reflexivity|]. exists tr3. exact H3.
  - unfold ret in H2. destruct tr2; cbn [rpath] in H2; [|contradiction]. injection H2 as <- <-. split; reflexivity.
Qed.

Lemma ra_cases F s p k n tr r s' :
  WF s -> In (p, k) (user_blocks s) -> rpath F (realloc (Some p) n s) tr (r, s') ->
  (r = None /\ s' = s) \/
  exists g am i fr, usedX [] s g am /\ 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr /\
    fr_kind fr = FUser /\ fr_n fr = k /\ p = frame_ptr am i fr /\
    ((ra_c1 am (fr_off fr) n = true /\ r = Some p /\ s' = upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s)
     \/ (am_sc am = 63 /\ MMAP_THRESHOLD <= n /\ am_maplen am * 4096 = rm_need n (fr_off fr) /\
         r = Some p /\ s' = upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s)
     \/ (am_sc am = 63 /\ MMAP_THRESHOLD <= n /\ am_maplen am * 4096 <> rm_need n (fr_off fr) /\
         r = Some (padd (slot_start (rm_am s am i (fr_off fr) n) i) (UNIT * fr_off fr)) /\
         s' = rm_state s g am i (fr_off fr) n)
     \/ (exists tr', rpath F (realloc_move p n s) tr' (r, s'))).
Proof.
  intros HW Hin H. destruct (size_overflows n) eqn:Ov.
  - left. unfold realloc in H. rewrite Ov in H. unfold ret in H.
    destruct tr; cbn [rpath] in H; [|contradiction]. injection H as <- <-. split; reflexivity.
  - right. destruct (user_blocks_frame s p k HW Hin) as (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep).
    exists g, am, i, fr. split; [exact Hu|]. split; [exact Hi|]. split; [exact Hfr|]. split; [exact Hk|].
    split; [exact En|]. split; [exact Ep|].
    apply (ra_shape F s p n g i am fr tr r s' Ov); [| exact (proj1 (usedX_MT _ _ _ _ Hu)) | exact Hfr | exact H].
    rewrite Ep. exact (find_frame_in_spec [] None U0 s HW g am i fr Hu Hi Hfr).
Qed.

Lemma ub_fold_app (l1 l2 : list (sptr * Z)) :
  fold_right (fun b acc => snd b + acc) 0 (l1 ++ l2) =
  fold_right (fun b acc => snd b + acc) 0 l1 + fold_right (fun b acc => snd b + acc) 0 l2.
Proof. induction l1 as [|x l1 IH]; cbn [app fold_right]; lia. Qed.

Lemma swap_counts s s' l1 l2 p k p' n :
  user_blocks s = l1 ++ (p, k) :: l2 -> user_blocks s' = l1 ++ (p', n) :: l2 ->
  nblocks s' = nblocks s /\ ubytes s' = ubytes s - k + n.
Proof.
  intros E E'. unfold nblocks, ubytes. rewrite E, E', !length_app, !ub_fold_app. cbn [length fold_right snd]. split; lia.
Qed.

Lemma ra_usedX_ext s s' : (forall q, MT s q = MT s' q) -> forall q a, usedX [] s q a <-> usedX [] s' q a.
Proof. intros E q a. unfold usedX, MTX. rewrite E. tauto. Qed.

Lemma gen_bwd s s' g am1 : (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) ->
  forall q a, usedX [] s' q a -> (q = g /\ a = am1) \/ (q <> g /\ usedX [] s q a).
Proof.
  intros EMT q a H. apply (ra_usedX_ext s' (upd_meta g (MUsed am1) s) EMT) in H.
  apply usedX_upd in H as [(-> & _ & E) | (Hne & H)].
  - left. injection E as E. split; [reflexivity | symmetry; exact E].
  - right. split; assumption.
Qed.

Lemma gen_fwd s s' g am1 : (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) ->
  forall q a, usedX [] s q a -> q <> g -> usedX [] s' q a.
Proof. intros EMT q a H Hne. apply (ra_usedX_ext s' (upd_meta g (MUsed am1) s) EMT). apply usedX_upd. right. split; assumption. Qed.

Lemma gen_g s s' g am1 : (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) -> usedX [] s' g am1.
Proof.
  intros EMT. apply (ra_usedX_ext s' (upd_meta g (MUsed am1) s) EMT). apply usedX_upd. left.
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma gen_SI s s' g am0 am1 :
  usedX [] s g am0 -> (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) -> SI s ->
  length (st_metas s') = length (st_metas s) -> hand s' = hand s ->
  owned_maps [] s' -> ~ frameless am1 ->
  (am_maplen am0 = 0 -> am_maplen am1 = 0 /\ am_mem am1 = am_mem am0 /\ am_sc am1 = am_sc am0) ->
  (forall j fr, 0 <= j <= am_last am1 -> ss_fr (nth_slot am1 j) = Some fr -> fr_kind fr = FGroup ->
     0 <= j <= am_last am0 /\ ss_fr (nth_slot am0 j) = Some fr /\ slot_start am1 j = slot_start am0 j /\ am_sc am1 = am_sc am0) ->
  SI s'.
Proof.
  intros Hg EMT (OM & EO & EU & CH & HK) Elen Eh OM' NF CG CF.
  split; [exact OM'|]. split; [|split; [|split]].
  - intros q a Hq Hfl Hun. destruct (gen_bwd s s' g am1 EMT q a Hq) as [[-> ->]|[Hne Hq']]; [exfalso; exact (NF Hfl)|].
    exact (EO q a Hq' Hfl Hun).
  - intros q1 a1 q2 a2 H1 H2 F1 F2 U1 U2 Es.
    destruct (gen_bwd s s' g am1 EMT q1 a1 H1) as [[-> ->]|[N1 H1']]; [exfalso; exact (NF F1)|].
    destruct (gen_bwd s s' g am1 EMT q2 a2 H2) as [[-> ->]|[N2 H2']]; [exfalso; exact (NF F2)|].
    exact (EU q1 a1 q2 a2 H1' H2' F1 F2 U1 U2 Es).
  - intros q a j fr Hq Hj Hf Hk. destruct (gen_bwd s s' g am1 EMT q a Hq) as [[-> ->]|[Hne Hq']].
    + destruct (CF j fr Hj Hf Hk) as (Hj0 & Hf0 & Ess & Esc).
      destruct (CH g am0 j fr Hg Hj0 Hf0 Hk) as (c & ac & Hc & Hm & Hmem & Hsc).
      assert (Hcg : c <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ Hc Hg) as ->; lia).
      exists c, ac. split; [exact (gen_fwd s s' g am1 EMT c ac Hc Hcg)|]. split; [exact Hm|].
      rewrite Ess, Esc. split; [exact Hmem | exact Hsc].
    + destruct (CH q a j fr Hq' Hj Hf Hk) as (c & ac & Hc & Hm & Hmem & Hsc).
      destruct (sptr_eq_dec c g) as [->|Hcg].
      * pose proof (usedX_fun _ _ _ _ _ Hc Hg) as ->. destruct (CG Hm) as (M1 & M2 & M3).
        exists g, am1. split; [exact (gen_g s s' g am1 EMT)|]. rewrite M2, M3. split; [exact M1|]. split; [exact Hmem | exact Hsc].
      * exists c, ac. split; [exact (gen_fwd s s' g am1 EMT c ac Hc Hcg)|]. split; [exact Hm|]. split; [exact Hmem | exact Hsc].
  - unfold hand_keys in *. rewrite Eh, HK, Elen. reflexivity.
Qed.

Lemma gen_GS s s' g am1 : (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) -> GS s ->
  (0 < am_maplen am1 -> (am_sc am1 < 48 -> am_maplen am1 * PGSZ <= MMAX) /\
     (am_sc am1 = 63 -> forall fr, ss_fr (nth_slot am1 0) = Some fr -> am_maplen am1 * PGSZ <= fr_n fr + 3 * PGSZ)) ->
  GS s'.
Proof.
  intros EMT HG H1 q a Hq Hm. destruct (gen_bwd s s' g am1 EMT q a Hq) as [[-> ->]|[_ Hq']]; [exact (H1 Hm) | exact (HG q a Hq' Hm)].
Qed.

Lemma gen_NL s s' g am1 : (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) -> NL s ->
  (am_maplen am1 = 0 -> 1 <= am_last am1) -> NL s'.
Proof.
  intros EMT HN H1 q a Hq Hm. destruct (gen_bwd s s' g am1 EMT q a Hq) as [[-> ->]|[_ Hq']]; [exact (H1 Hm) | exact (HN q a Hq' Hm)].
Qed.

Lemma gen_noraw s s' g am1 : (forall q, MT s' q = MT (upd_meta g (MUsed am1) s) q) -> noraw s -> noraw s'.
Proof. intros EMT HR q E. rewrite EMT, MT_upd in E. destruct (sptr_eqb q g); [discriminate | exact (HR q E)]. Qed.

Lemma ra_len_upd s g x : In g (keys s) -> length (st_metas (upd_meta g x s)) = length (st_metas s).
Proof.
  intros H. rewrite <- (length_map fst (st_metas (upd_meta g x s))), <- (length_map fst (st_metas s)).
  change (length (keys (upd_meta g x s)) = length (keys s)). rewrite keys_upd_In by exact H. reflexivity.
Qed.

Definition IPH (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) (n : Z) : Prop :=
  WF s /\ usedX [] s g am /\ 0 <= i <= am_last am /\ ss_fr (nth_slot am i) = Some fr /\ fr_kind fr = FUser /\ 0 <= n /\
  n <= stride_of am - IB - UNIT * fr_off fr /\
  (am_sc am < 48 \/ (am_sc am = 63 /\ MMAP_THRESHOLD <= n /\ am_maplen am * 4096 = rm_need n (fr_off fr))).

Lemma rs_fields am i off n :
  am_mem (rs_am am i off n) = am_mem am /\ am_last (rs_am am i off n) = am_last am /\
  am_sc (rs_am am i off n) = am_sc am /\ am_maplen (rs_am am i off n) = am_maplen am /\
  stride_of (rs_am am i off n) = stride_of am /\ (forall j, slot_start (rs_am am i off n) j = slot_start am j).
Proof. destruct am; repeat split; reflexivity. Qed.

Lemma ip_ns s g am i fr n j : IPH s g am i fr n -> 0 <= j ->
  nth_slot (rs_am am i (fr_off fr) n) j =
  if j =? i then resize_slot (stride_of am) i (nth_slot am i) (fr_off fr) n else nth_slot am j.
Proof.
  intros (HW & Hu & Hi & _) Hj. pose proof (inv_groups HW g am Hu) as ((_ & _ & Glen & _) & _).
  unfold rs_am. apply nth_slot_upd_slot; [lia | exact Hj | rewrite Glen; lia].
Qed.

Lemma ip_fr1 s g am i fr n : IPH s g am i fr n ->
  ss_fr (nth_slot (rs_am am i (fr_off fr) n) i) = Some (mkFrame (fr_off fr) n FUser).
Proof. intros H. pose proof H as (_ & _ & Hi & _). rewrite (ip_ns s g am i fr n i H) by lia. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma ip_wf s g am i fr n : IPH s g am i fr n -> WF (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s).
Proof.
  intros H. pose proof H as (HW & Hu & Hi & Hfr & Hk & Hn & Hav & Hcl).
  pose proof (inv_groups HW g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof Gm as (Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra).
  pose proof (Gsl i Hi) as (Si1 & Si2 & Si3). rewrite Hfr in Si3. destruct Si3 as (Hal & _ & Fok & _).
  destruct Fok as (Fn & Foff & Ffit & Fh16 & _).
  assert (Hscr : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C1 & _) | (C1 & _)]; [left | right]; exact C1).
  assert (Hsp : 16 <= stride_of am) by exact (stride_pos _ _ _ _ _ (inv_groups HW g am Hu)).
  set (am1 := rs_am am i (fr_off fr) n).
  assert (NS : forall j, 0 <= j -> nth_slot am1 j = if j =? i then resize_slot (stride_of am) i (nth_slot am i) (fr_off fr) n else nth_slot am j).
  { intros j Hj. exact (ip_ns s g am i fr n j H Hj). }
  assert (GS : geom_same am am1).
  { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros j frj Hj Hkj.
    assert (Hj0 : 0 <= j \/ j < 0) by lia.
    assert (E0 : nth_slot am1 j = nth_slot am1 (Z.max 0 j) /\ nth_slot am j = nth_slot am (Z.max 0 j)).
    { unfold nth_slot. replace (Z.to_nat j) with (Z.to_nat (Z.max 0 j)) by lia. split; reflexivity. }
    destruct E0 as [Ea Eb]. rewrite Ea. rewrite Eb in Hj. rewrite NS by lia.
    destruct (Z.max 0 j =? i) eqn:E; [|exact Hj].
    apply Z.eqb_eq in E. rewrite E in Hj. rewrite Hfr in Hj. injection Hj as <-. rewrite Hk in Hkj. discriminate. }
  unfold WF. eapply (Inv_used_update [] None None U0 s g am am1 HW Hu (geom_same_upto_of [] s _ _ GS)).
  - split; reflexivity.
  - unfold masks_ok. subst am1. unfold rs_am, upd_slot. cbn -[Z.le Z.lt Z.add Z.testbit]. rewrite length_lupd.
    repeat (split; [assumption|]). exact Gfra.
  - intros j Hj. change (am_last am1) with (am_last am) in Hj.
    pose proof (Gsl j Hj) as Sj. unfold slot_ok in Sj |- *. rewrite NS by lia.
    destruct (j =? i) eqn:Ej; [|exact Sj].
    apply Z.eqb_eq in Ej. subst j. unfold resize_slot. cbn [ss_hdr ss_fr].
    assert (FO : frame_ok am1 i (mkFrame (fr_off fr) n FUser)).
    { unfold frame_ok. cbn [fr_n fr_off fr_kind]. change (stride_of am1) with (stride_of am).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Fh16|]. intros HH; discriminate. }
    destruct (fr_off fr =? 0) eqn:Eo.
    + apply Z.eqb_eq in Eo. split; [intros HH; discriminate|]. split.
      { intros h3 h16 Eh. injection Eh as <- <-.
        assert (Hr : 0 <= (if 5 <=? stride_of am - IB - UNIT * fr_off fr - n then 5 else stride_of am - IB - UNIT * fr_off fr - n) <= 5).
        { destruct (5 <=? stride_of am - IB - UNIT * fr_off fr - n) eqn:E5; [apply Z.leb_le in E5 | apply Z.leb_gt in E5]; lia. }
        unfold hdr_off16 in Fh16. unfold UNIT in *.
        assert (0 <= stride_of am * i / 16) by (apply Z.div_pos; nia). lia. }
      split; [exact Hal|]. split; [discriminate|]. split; [exact FO|].
      intros _. f_equal. unfold hdr_byte3, rsv_code, hdr_off16. cbn [fr_kind fr_off fr_n].
      change (stride_of am1) with (stride_of am). rewrite Eo. f_equal; lia.
    + split; [exact Si1|]. split; [exact Si2|]. split; [exact Hal|]. split; [discriminate|]. split; [exact FO|].
      intros HH. cbn [fr_off] in HH. rewrite HH in Eo. discriminate.
  - destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | (C1 & C2 & C3 & C4)].
    + left. destruct Hcl as [Hlt | (_ & Hbig & _)]; [lia|].
      split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|].
      right. exists (mkFrame (fr_off fr) n FUser). rewrite NS by lia.
      replace (0 =? i) with true by (symmetry; apply Z.eqb_eq; lia).
      split; [reflexivity|]. split; [reflexivity | exact Hbig].
    + right. exact (conj C1 (conj C2 (conj C3 C4))).
  - intros p j Hp. tauto.
  - intros j HH. discriminate.
  - intros Hsc HL. exact (proj1 (ring_facts [] None U0 s g am HW Hu Hsc ltac:(lia)) HL).
  - intros Hsc Hav0. exact (proj1 (proj2 (ring_facts [] None U0 s g am HW Hu Hsc ltac:(lia))) Hav0).
  - intros Hsc HL Hnh HnR. exact (proj2 (proj2 (ring_facts [] None U0 s g am HW Hu Hsc ltac:(lia))) HL Hnh HnR).
  - intros Hpa p a Hp Hpg Hsca Hpa'. apply Hpg. symmetry.
    eapply (inv_partial HW g am p a Hu Hp); [symmetry; exact Hsca | exact Hpa | exact Hpa'].
Qed.

Lemma ip_of_c1 s g am i fr n : WF s -> usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  fr_kind fr = FUser -> 0 <= n -> ra_c1 am (fr_off fr) n = true -> IPH s g am i fr n.
Proof.
  intros HW Hu Hi Hfr Hk Hn Hc. unfold ra_c1 in Hc. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  split; [exact HW|]. split; [exact Hu|]. split; [exact Hi|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hn|].
  split; [exact H1|]. left.
  pose proof (size_to_class_range n (conj Hn H2)) as [R _].
  pose proof (inv_groups HW g am Hu) as (_ & _ & _ & Gcl & _).
  destruct Gcl as [(C1 & _) | (C1 & _)]; lia.
Qed.

Lemma ip_of_same s g am i fr n : WF s -> usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  fr_kind fr = FUser -> am_sc am = 63 -> MMAP_THRESHOLD <= n -> am_maplen am * 4096 = rm_need n (fr_off fr) ->
  IPH s g am i fr n.
Proof.
  intros HW Hu Hi Hfr Hk Hsc Hn Hml.
  pose proof (inv_groups HW g am Hu) as (_ & _ & _ & Gcl & _).
  destruct Gcl as [(_ & C2 & C3 & _) | (C1 & _)]; [|lia].
  assert (Hst : stride_of am = am_maplen am * 4096 - UNIT).
  { unfold stride_of. rewrite C2. destruct (am_maplen am =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
  split; [exact HW|]. split; [exact Hu|]. split; [exact Hi|]. split; [exact Hfr|]. split; [exact Hk|].
  split; [unfold MMAP_THRESHOLD in Hn; lia|]. split; [|right; split; [exact Hsc|]; split; [exact Hn | exact Hml]].
  rewrite Hst. pose proof (page_round_ge (n + UNIT * fr_off fr + UNIT + IB)). unfold rm_need in Hml. unfold UNIT, IB in *. lia.
Qed.

Lemma ip_SI s g am i fr n : IPH s g am i fr n -> SI s -> SI (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s).
Proof.
  intros H HS. pose proof H as (HW & Hu & Hi & Hfr & Hk & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  assert (EMT : forall q, MT (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) q =
    MT (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) q) by reflexivity.
  apply (gen_SI s _ g am _ Hu EMT HS).
  - apply ra_len_upd. exact (MT_Some_In_keys _ _ _ Mg).
  - reflexivity.
  - intros k rg Hk' Hkd Hl. destruct (proj1 HS k rg Hk' Hkd Hl) as (q & a & Hq & Hm & Hp).
    destruct (sptr_eq_dec q g) as [->|Hne].
    + pose proof (usedX_fun _ _ _ _ _ Hq Hu) as ->. exists g, (rs_am am i (fr_off fr) n).
      split; [exact (gen_g s _ g _ EMT)|]. split; [exact Hm | exact Hp].
    + exists q, a. split; [exact (gen_fwd s _ g _ EMT q a Hq Hne)|]. split; [exact Hm | exact Hp].
  - intros Hfl. pose proof (Hfl i Hi) as E. rewrite (ip_fr1 s g am i fr n H) in E. discriminate.
  - intros Hm0. split; [exact Hm0|]. split; reflexivity.
  - intros j f Hj Hf Hkf. assert (Hji : j <> i).
    { intros ->. rewrite (ip_fr1 s g am i fr n H) in Hf. injection Hf as <-. discriminate. }
    rewrite (ip_ns s g am i fr n j H) in Hf by lia. replace (j =? i) with false in Hf by (symmetry; apply Z.eqb_neq; exact Hji).
    split; [exact Hj|]. split; [exact Hf|]. split; reflexivity.
Qed.

Lemma ip_GS s g am i fr n : IPH s g am i fr n -> GS s -> GS (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s).
Proof.
  intros H HG. pose proof H as (HW & Hu & Hi & Hfr & Hk & Hn & Hav & Hcl).
  apply (gen_GS s _ g _ (fun q => eq_refl) HG).
  intros Hm. destruct (HG g am Hu Hm) as [G1 G2]. split; [exact G1|].
  intros H63 f Hf. change (am_sc am = 63) in H63.
  destruct Hcl as [Hlt | (_ & Hbig & Hml)]; [lia|].
  pose proof (inv_groups HW g am Hu) as (_ & _ & Gsl & Gcl & _).
  destruct Gcl as [(_ & C2 & _) | (C1 & _)]; [|lia].
  pose proof (Gsl i Hi) as (_ & _ & Si3). rewrite Hfr in Si3. destruct Si3 as (_ & _ & (_ & Foff & _) & _).
  rewrite (ip_ns s g am i fr n 0 H) in Hf by lia. replace (0 =? i) with true in Hf by (symmetry; apply Z.eqb_eq; lia).
  cbn [resize_slot ss_fr] in Hf. injection Hf as <-. cbn [fr_n].
  change (am_maplen am * PGSZ <= n + 3 * PGSZ).
  pose proof (page_round_lt (n + UNIT * fr_off fr + UNIT + IB)). unfold rm_need in Hml. unfold PGSZ, UNIT, IB in *. lia.
Qed.

Lemma ip_NL s g am i fr n : IPH s g am i fr n -> NL s -> NL (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s).
Proof. intros (HW & Hu & _) HN. apply (gen_NL s _ g _ (fun q => eq_refl) HN). intros Hm. exact (HN g am Hu Hm). Qed.

Lemma upd_noraw s g a : noraw s -> noraw (upd_meta g (MUsed a) s).
Proof. intros HR. exact (gen_noraw s _ g a (fun q => eq_refl) HR). Qed.

Lemma ip_blocks s g am i fr n : IPH s g am i fr n ->
  exists l1 l2, user_blocks s = l1 ++ (frame_ptr am i fr, fr_n fr) :: l2 /\
  user_blocks (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s) = l1 ++ (padd (slot_start am i) (UNIT * fr_off fr), n) :: l2.
Proof.
  intros (HW & Hu & Hi & Hfr & Hk & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (inv_groups HW g am Hu) as ((_ & _ & Glen & _) & _).
  pose proof (proj1 (inv_keys HW)) as ND.
  destruct (ublist_upd_slot s g am i (resize_slot (stride_of am) i (nth_slot am i) (fr_off fr) n) ND Mg Hi Glen) as (l1 & l2 & E1 & E2).
  assert (ND' : NoDup (keys (upd_meta g (MUsed (rs_am am i (fr_off fr) n)) s))).
  { rewrite keys_upd_In by exact (MT_Some_In_keys _ _ _ Mg). exact ND. }
  exists (map fst l1), (map fst l2).
  rewrite (user_blocks_ublist s ND), (user_blocks_ublist _ ND'). unfold rs_am. rewrite E1, E2.
  unfold slot_block, slotst_block. rewrite Hfr, Hk. cbn [resize_slot ss_fr fr_kind fr_off fr_n].
  rewrite !map_app. cbn [map fst app]. split; reflexivity.
Qed.

Definition RMH (s : astate) (g : sptr) (am : ameta) (fr : frame) (n : Z) : Prop :=
  WF s /\ usedX [] s g am /\ ss_fr (nth_slot am 0) = Some fr /\ fr_kind fr = FUser /\ am_sc am = 63 /\ MMAP_THRESHOLD <= n.

Lemma rm_basic s g am fr n : RMH s g am fr n ->
  am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0 /\ am_prev am = None /\ am_next am = None /\
  am_aidx am = 0 /\ am_slots am = [nth_slot am 0] /\ 0 <= fr_off fr <= 255 /\ ss_hdr (nth_slot am 0) <> None /\
  (forall h3 h16, ss_hdr (nth_slot am 0) = Some (h3, h16) -> 0 <= h3 <= 255 /\ 0 <= h16 <= 65535) /\
  (exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap) /\
  (prid (am_mem am) < length (st_regions s))%nat.
Proof.
  intros (HW & Hu & Hfr & Hk & Hsc & Hn).
  pose proof (inv_groups HW g am Hu) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof Gm as (Glast & Gaidx & Glen & _).
  destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | (C1 & _)]; [|lia].
  destruct (proj2 (proj2 (inv_rings HW)) g am Hu Hsc) as [Hp Hx].
  pose proof (Gsl 0 ltac:(lia)) as (S1 & S2 & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (_ & Foff & _) & _).
  destruct (Gmp ltac:(lia)) as (r & rg & Em & Hr & Hkd & Hl & _).
  split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact Hp|]. split; [exact Hx|].
  split; [lia|]. split.
  { rewrite C2 in Glen. unfold nth_slot. destruct (am_slots am) as [|x [|y l]]; cbn in Glen; [lia | reflexivity | lia]. }
  split; [exact Foff|]. split; [intros E; apply S1 in E; lia|]. split; [exact S2|].
  split; [exists rg; rewrite Em; cbn [prid]; split; [exact Hr | exact Hkd]|].
  exact (used_group_prid_lt [] None U0 s g am HW Hu).
Qed.

Lemma rm_need_facts n off : MMAP_THRESHOLD <= n -> 0 <= off <= 255 ->
  rm_need n off / 4096 * 4096 = rm_need n off /\ 1 <= rm_need n off / 4096 /\
  n + UNIT * off + UNIT + IB <= rm_need n off /\ rm_need n off <= n + 3 * PGSZ.
Proof.
  intros Hn Ho. unfold rm_need. pose proof (page_round_ge (n + UNIT * off + UNIT + IB)) as A.
  pose proof (page_round_lt (n + UNIT * off + UNIT + IB)) as B. pose proof (page_round_pages (n + UNIT * off + UNIT + IB)) as C.
  unfold PGSZ, UNIT, IB, MMAP_THRESHOLD in *. split; [lia|]. split; [lia|]. split; lia.
Qed.

Lemma rm_slot0 s am off n : am_slots am = [nth_slot am 0] ->
  nth_slot (rm_am s am 0 off n) 0 = resize_slot (rm_need n off / 4096 * 4096 - UNIT) 0 (nth_slot am 0) off n.
Proof. intros E. unfold nth_slot at 1. unfold rm_am, remap_am. cbn [am_slots]. rewrite E. reflexivity. Qed.

Lemma rm_region s g am i off n k rg : (prid (am_mem am) < length (st_regions s))%nat ->
  region_of (rm_state s g am i off n) k = Some rg -> rg_live rg = true ->
  k <> prid (am_mem am) /\
  (region_of s k = Some rg \/ (k = length (st_regions s) /\ rg = mkRegion RkMap (rm_need n off) [] true)).
Proof.
  intros Hlt Hk Hl. unfold rm_state, region_of in Hk. cbn [st_regions set_regions] in Hk.
  change (st_regions (rm_mid s g am i off n)) with (st_regions s ++ [mkRegion RkMap (rm_need n off) [] true]) in Hk.
  rewrite nth_error_lupd in Hk.
  destruct (Nat.eqb k (prid (am_mem am)) && Nat.ltb (prid (am_mem am)) (length (st_regions s ++ [mkRegion RkMap (rm_need n off) [] true])))%bool eqn:E.
  - injection Hk as <-. cbn in Hl. discriminate.
  - split.
    + intros ->. rewrite Nat.eqb_refl in E. cbn [andb] in E. apply Nat.ltb_ge in E. rewrite length_app in E. cbn [length] in E. lia.
    + destruct (Nat.lt_ge_cases k (length (st_regions s))) as [Hk1|Hk1].
      * left. unfold region_of. rewrite nth_error_app1 in Hk by exact Hk1. exact Hk.
      * right. rewrite nth_error_app2 in Hk by exact Hk1.
        destruct (k - length (st_regions s))%nat as [|d] eqn:Ed; cbn in Hk.
        -- injection Hk as <-. split; [lia | reflexivity].
        -- destruct d; discriminate.
Qed.

Lemma blocks_last0 g a : am_last a = 0 -> blocks_of g a = slot_block g a 0.
Proof. intros E. unfold blocks_of. rewrite E. change (zseq 0 (0 + 1)) with [0]. cbn [flat_map]. apply app_nil_r. Qed.

Lemma rm_SI s g am fr n : RMH s g am fr n -> SI s -> SI (rm_state s g am 0 (fr_off fr) n).
Proof.
  intros H HS. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hn).
  destruct (rm_basic s g am fr n H) as (Hl & Hml & _ & _ & _ & _ & _ & Hsl & Foff & _ & _ & _ & Hlt).
  destruct (rm_need_facts n (fr_off fr) Hn Foff) as (N1 & N2 & N3 & N4).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  assert (EMT : forall q, MT (rm_state s g am 0 (fr_off fr) n) q = MT (upd_meta g (MUsed (rm_am s am 0 (fr_off fr) n)) s) q)
    by reflexivity.
  pose proof (rm_slot0 s am (fr_off fr) n Hsl) as S0.
  assert (L1 : am_last (rm_am s am 0 (fr_off fr) n) = 0) by exact Hl.
  apply (gen_SI s _ g am _ Hu EMT HS).
  - exact (ra_len_upd s g (MUsed (rm_am s am 0 (fr_off fr) n)) (MT_Some_In_keys _ _ _ Mg)).
  - reflexivity.
  - intros k rg Hk' Hkd Hlv.
    destruct (rm_region s g am 0 (fr_off fr) n k rg Hlt Hk' Hlv) as [Hkr [Hold | (-> & ->)]].
    + destruct (proj1 HS k rg Hold Hkd Hlv) as (q & a & Hq & Hm & Hp).
      assert (Hqg : q <> g) by (intros ->; pose proof (usedX_fun _ _ _ _ _ Hq Hu) as ->; exact (Hkr (eq_sym Hp))).
      exists q, a. split; [exact (gen_fwd s _ g _ EMT q a Hq Hqg)|]. split; [exact Hm | exact Hp].
    + exists g, (rm_am s am 0 (fr_off fr) n). split; [exact (gen_g s _ g _ EMT)|].
      split; [change (0 < rm_need n (fr_off fr) / 4096); lia | reflexivity].
  - intros Hfl. pose proof (Hfl 0 ltac:(rewrite L1; lia)) as E. rewrite S0 in E. cbn [resize_slot ss_fr] in E. discriminate.
  - intros Hm0. lia.
  - intros j f Hj Hf Hkf. rewrite L1 in Hj. replace j with 0 in Hf by lia. rewrite S0 in Hf.
    cbn [resize_slot ss_fr] in Hf. injection Hf as <-. discriminate.
Qed.

Lemma rm_GS s g am fr n : RMH s g am fr n -> GS s -> GS (rm_state s g am 0 (fr_off fr) n).
Proof.
  intros H HG. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hn).
  destruct (rm_basic s g am fr n H) as (Hl & Hml & _ & _ & _ & _ & _ & Hsl & Foff & _).
  destruct (rm_need_facts n (fr_off fr) Hn Foff) as (N1 & N2 & N3 & N4).
  pose proof (rm_slot0 s am (fr_off fr) n Hsl) as S0.
  apply (gen_GS s _ g (rm_am s am 0 (fr_off fr) n) (fun q => eq_refl) HG). intros Hm. split.
  - intros Hlt'. change (am_sc am < 48) in Hlt'. lia.
  - intros _ f Hf. rewrite S0 in Hf. cbn [resize_slot ss_fr] in Hf. injection Hf as <-. cbn [fr_n].
    change (rm_need n (fr_off fr) / 4096 * PGSZ <= n + 3 * PGSZ). unfold PGSZ in *. lia.
Qed.

Lemma rm_NL s g am fr n : RMH s g am fr n -> NL s -> NL (rm_state s g am 0 (fr_off fr) n).
Proof.
  intros H HN. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hn).
  destruct (rm_basic s g am fr n H) as (_ & _ & _ & _ & _ & _ & _ & _ & Foff & _).
  destruct (rm_need_facts n (fr_off fr) Hn Foff) as (_ & N2 & _).
  apply (gen_NL s _ g (rm_am s am 0 (fr_off fr) n) (fun q => eq_refl) HN). intros Hm. exfalso.
  change (rm_need n (fr_off fr) / 4096 = 0) in Hm. lia.
Qed.

Lemma rm_noraw s g am fr n : noraw s -> noraw (rm_state s g am 0 (fr_off fr) n).
Proof. intros HR. exact (gen_noraw s _ g (rm_am s am 0 (fr_off fr) n) (fun q => eq_refl) HR). Qed.

Lemma rm_hand s g am i off n : hand (rm_state s g am i off n) = hand s.
Proof. reflexivity. Qed.

Lemma rm_blocks s g am fr n : RMH s g am fr n ->
  exists l1 l2, user_blocks s = l1 ++ (frame_ptr am 0 fr, fr_n fr) :: l2 /\
  user_blocks (rm_state s g am 0 (fr_off fr) n) =
  l1 ++ (padd (slot_start (rm_am s am 0 (fr_off fr) n) 0) (UNIT * fr_off fr), n) :: l2.
Proof.
  intros H. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hn).
  destruct (rm_basic s g am fr n H) as (Hl & _ & _ & _ & _ & _ & _ & Hsl & _).
  pose proof (usedX_MT _ _ _ _ Hu) as [Mg _]. pose proof (proj1 (inv_keys HW)) as ND.
  pose proof (MT_Some_In_keys _ _ _ Mg) as Kg.
  destruct (ublist_split s g ND Kg) as (L1 & L2 & Hup & Hs).
  assert (ND' : NoDup (keys (upd_meta g (MUsed (rm_am s am 0 (fr_off fr) n)) s))).
  { rewrite keys_upd_In by exact Kg. exact ND. }
  assert (EU : user_blocks (rm_state s g am 0 (fr_off fr) n) = user_blocks (upd_meta g (MUsed (rm_am s am 0 (fr_off fr) n)) s))
    by reflexivity.
  exists (map fst L1), (map fst L2). rewrite EU, (user_blocks_ublist s ND), (user_blocks_ublist _ ND'), Hup, Hs, Mg.
  cbn [ucontrib]. rewrite (blocks_last0 g am Hl), (blocks_last0 g (rm_am s am 0 (fr_off fr) n) Hl).
  unfold slot_block. rewrite Hfr, Hk, (rm_slot0 s am (fr_off fr) n Hsl). cbn [resize_slot ss_fr fr_kind fr_off fr_n].
  rewrite !map_app. cbn [map fst app]. split; reflexivity.
Qed.

Lemma mupd2 : forall l p x y, mupdate (mupdate l p x) p y = mupdate l p y.
Proof.
  induction l as [|[q z] t IH]; intros p x y; cbn; [rewrite sptr_eqb_refl; reflexivity|].
  destruct (sptr_eqb p q) eqn:E; cbn; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma upd_meta_twice g x y s : upd_meta g y (upd_meta g x s) = upd_meta g y s.
Proof. unfold upd_meta. cbn [st_metas set_metas]. rewrite mupd2. reflexivity. Qed.

Lemma Inv_U X R U U' s : Inv X R U s -> (forall c, 0 <= c < 48 -> U c = U' c) -> Inv X R U' s.
Proof.
  intros (C & K & A & XO & G & L & Mp & Rg & Us & Rs & P) HU.
  split; [exact C|]. split; [exact K|]. split; [exact A|]. split; [exact XO|]. split; [exact G|]. split; [exact L|].
  split; [exact Mp|]. split; [exact Rg|]. split; [|split; [exact Rs | exact P]].
  intros sc Hsc. rewrite (Us sc Hsc), (HU sc Hsc). reflexivity.
Qed.

Lemma rm_wf s g am fr n : RMH s g am fr n -> WF (rm_state s g am 0 (fr_off fr) n).
Proof.
  intros H. pose proof H as (HW & Hu & Hfr & Hk & Hsc & Hn).
  destruct (rm_basic s g am fr n H) as (Hl & Hml & Hav & Hfd & Hp & Hx & Hai & Hsl & Foff & Hh0 & Hhb & (rg & Hr & Hrk) & Hlt).
  destruct (rm_need_facts n (fr_off fr) Hn Foff) as (N1 & N2 & N3 & N4).
  set (r' := length (st_regions s)).
  set (s2 := set_regions (st_regions s ++ [mkRegion RkMap (rm_need n (fr_off fr)) [] true]) s).
  assert (HW2 : Inv [] None U0 s2) by (apply Inv_new_map; [exact HW | unfold UNIT, IB, MMAP_THRESHOLD in *; lia]).
  assert (Hu2 : usedX [] s2 g am) by exact Hu.
  set (x0 := mkSlot (ss_hdr (nth_slot am 0)) None).
  set (am3 := upd_slot am 0 x0).
  set (s3 := upd_meta g (MUsed am3) s2).
  assert (HW3 : Inv [] (Some (g, 0)) U0 s3).
  { apply (drop_frame_Inv [] U0 s2 g am 0 fr x0 HW2 Hu2); [lia | exact Hfr | intros Hg; rewrite Hk in Hg; discriminate | reflexivity | left; reflexivity]. }
  assert (Hu3 : usedX [] s3 g am3) by (apply usedX_upd; left; split; [reflexivity|]; split; reflexivity).
  assert (Fl3 : forall j, ss_fr (nth_slot am3 j) = None).
  { intros j. unfold nth_slot, am3, upd_slot, am_set_slots. cbn [am_slots]. rewrite Hsl. destruct (Z.to_nat j) as [|[|k]]; reflexivity. }
  set (U1 := fun c => U0 c + contrib [] s3 c g).
  assert (HW3x : Inv [g] None U1 s3).
  { apply (Inv_exempt [] (Some (g, 0)) U0 s3 g am3 HW3 Hu3 Fl3 Hp Hx). intros p' i' E. injection E as <- _. reflexivity. }
  assert (Hr' : region_of s3 r' = Some (mkRegion RkMap (rm_need n (fr_off fr)) [] true))
    by exact (region_of_app_new s (mkRegion RkMap (rm_need n (fr_off fr)) [] true)).
  assert (Hfresh : forall q a, usedX [g] s3 q a -> prid (am_mem a) <> r').
  { intros q a Hq. destruct (usedX_cons_inv [] g s3 q a Hq) as [Hne Hq'].
    apply usedX_upd in Hq' as [(E & _) | (_ & Hq'')]; [contradiction|].
    pose proof (used_group_prid_lt [] None U0 s q a HW Hq'') as L. unfold r'. lia. }
  set (ml := rm_need n (fr_off fr) / 4096).
  set (am4 := direct_am r' ml).
  assert (HW4 : Inv [] (Some (g, 0)) U1 (upd_meta g (MUsed am4) s3)).
  { exact (install_direct_spec [] U1 s3 g r' (mkRegion RkMap (rm_need n (fr_off fr)) [] true) ml
      (fun r => Inv [] (Some (g, 0)) U1 (snd r)) HW3x eq_refl Hr' eq_refl eq_refl
      ltac:(cbn [rg_len]; unfold ml, PGSZ; lia) ltac:(unfold ml; lia) Hfresh (fun s' E HI _ _ => HI)). }
  assert (Hst4 : stride_of am4 = ml * 4096 - UNIT).
  { unfold am4, direct_am, stride_of. cbn [am_last am_maplen am_sc]. destruct (ml =? 0) eqn:E; [apply Z.eqb_eq in E; unfold ml in E; lia | reflexivity]. }
  set (sl5 := resize_slot (ml * 4096 - UNIT) 0 (nth_slot am 0) (fr_off fr) n).
  set (am5 := upd_slot am4 0 sl5).
  assert (Hst5 : stride_of am5 = ml * 4096 - UNIT) by exact Hst4.
  assert (Hu4 : usedX [] (upd_meta g (MUsed am4) s3) g am4) by (apply usedX_upd; left; split; [reflexivity|]; split; reflexivity).
  assert (GS5 : geom_same am4 am5).
  { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros j frj Hj _. exfalso. unfold nth_slot, am4, direct_am in Hj. cbn [am_slots] in Hj.
    destruct (Z.to_nat j) as [|[|k]]; cbn in Hj; discriminate. }
  assert (FO5 : frame_ok am5 0 (mkFrame (fr_off fr) n FUser)).
  { unfold frame_ok, hdr_off16. rewrite Hst5. cbn [fr_n fr_off fr_kind].
    split; [unfold MMAP_THRESHOLD in Hn; lia|]. split; [lia|]. split; [unfold ml, UNIT, IB in *; lia|].
    split; [rewrite Z.mul_0_r; unfold UNIT; cbn [Z.div]; lia | intros HH; discriminate]. }
  assert (HW5 : Inv [] None U1 (upd_meta g (MUsed am5) (upd_meta g (MUsed am4) s3))).
  { eapply (Inv_used_update [] (Some (g, 0)) None U1 _ g am4 am5 HW4 Hu4 (geom_same_upto_of [] _ _ _ GS5)).
    - split; reflexivity.
    - change (masks_ok (mkAMeta None None (SP r' 0) 0 0 0 63 ml 0 [sl5])).
      unfold masks_ok. cbn [am_last am_aidx am_slots am_avail am_freed length].
      repeat split; try lia; intros; rewrite ?Z.bits_0; auto.
    - intros j Hj. change (0 <= j <= 0) in Hj. assert (j = 0) as -> by lia.
      unfold slot_ok. change (nth_slot am5 0) with sl5. unfold sl5, resize_slot. cbn [ss_hdr ss_fr].
      destruct (fr_off fr =? 0) eqn:Eo.
      + split; [intros HH; discriminate|]. split.
        { intros h3 h16 Eh. injection Eh as <- <-.
          assert (Hr5 : 0 <= (if 5 <=? ml * 4096 - UNIT - IB - UNIT * fr_off fr - n then 5 else ml * 4096 - UNIT - IB - UNIT * fr_off fr - n) <= 5).
          { destruct (5 <=? ml * 4096 - UNIT - IB - UNIT * fr_off fr - n) eqn:E5; [apply Z.leb_le in E5 | apply Z.leb_gt in E5]; unfold ml, UNIT, IB in *; lia. }
          rewrite Z.mul_0_r. change (0 / UNIT) with 0. lia. }
        split; [reflexivity|]. split; [discriminate|]. split; [exact FO5|].
        intros _. f_equal. unfold hdr_byte3, rsv_code, hdr_off16. rewrite Hst5. cbn [fr_kind fr_off fr_n].
        apply Z.eqb_eq in Eo. rewrite Eo. f_equal; lia.
      + split; [intros E; exfalso; exact (Hh0 E)|]. split; [exact Hhb|]. split; [reflexivity|]. split; [discriminate|].
        split; [exact FO5|]. intros HH. cbn [fr_off] in HH. rewrite HH in Eo. discriminate.
    - left. split; [reflexivity|]. split; [reflexivity|]. split; [exact N2|]. split; [reflexivity|]. split; [reflexivity|].
      right. exists (mkFrame (fr_off fr) n FUser). split; [reflexivity|]. split; [reflexivity | exact Hn].
    - intros p' j Hp'. split; intros HH; [discriminate | injection HH as E _; exfalso; exact (Hp' (eq_sym E))].
    - intros j HH. discriminate.
    - intros Hlt' _. exfalso. change (63 < 48) in Hlt'. lia.
    - intros Hlt'. exfalso. change (63 < 48) in Hlt'. lia.
    - intros Hlt'. exfalso. change (63 < 48) in Hlt'. lia.
    - intros Hai'. exfalso. change (0 < 0) in Hai'. lia. }
  assert (EU1 : forall c, 0 <= c < 48 -> U1 c = U0 c).
  { intros c Hc. unfold U1. cbv beta. rewrite (contrib_used [] s3 c g am3 Hu3). change (am_sc am3) with (am_sc am). rewrite Hsc.
    destruct (63 =? c) eqn:E; [apply Z.eqb_eq in E; lia | unfold U0; lia]. }
  assert (EA : rm_am s am 0 (fr_off fr) n = am5).
  { unfold rm_am, remap_am, am5, am4, sl5, upd_slot, am_set_slots, direct_am. rewrite Hp, Hx, Hav, Hfd, Hl, Hsc, Hai, Hsl. reflexivity. }
  assert (E6 : rm_mid s g am 0 (fr_off fr) n = upd_meta g (MUsed am5) (upd_meta g (MUsed am4) s3)).
  { unfold rm_mid, s3. rewrite !upd_meta_twice, EA. reflexivity. }
  assert (HW6 : Inv [] None U0 (rm_mid s g am 0 (fr_off fr) n)) by (rewrite E6; exact (Inv_U _ _ U1 U0 _ HW5 EU1)).
  assert (Hr6 : region_of (rm_mid s g am 0 (fr_off fr) n) (prid (am_mem am)) = Some rg).
  { change (region_of s2 (prid (am_mem am)) = Some rg). apply region_of_app. exact Hr. }
  assert (Hno : forall q a, usedX [] (rm_mid s g am 0 (fr_off fr) n) q a -> 0 < am_maplen a -> prid (am_mem a) <> prid (am_mem am)).
  { intros q a Hq Hm. destruct (gen_bwd s (rm_mid s g am 0 (fr_off fr) n) g (rm_am s am 0 (fr_off fr) n) (fun q => eq_refl) q a Hq) as [[-> ->]|[Hne Hq']].
    - change (length (st_regions s) <> prid (am_mem am)). lia.
    - intros E. apply Hne. exact (inv_maps HW q a g am Hq' Hu Hm ltac:(lia) E). }
  pose proof (Inv_kill_map [] None U0 _ (prid (am_mem am)) rg HW6 Hr6 Hrk Hno) as HW7.
  unfold WF, rm_state.
  replace (nth (prid (am_mem am)) (st_regions (rm_mid s g am 0 (fr_off fr) n)) (mkRegion RkMap 0 [] false)) with rg.
  - exact HW7.
  - symmetry. apply nth_error_nth. exact Hr6.
Qed.

Lemma last63 s g am : WF s -> usedX [] s g am -> am_sc am = 63 -> am_last am = 0.
Proof.
  intros HW Hu Hsc. pose proof (inv_groups HW g am Hu) as (_ & _ & _ & Gcl & _).
  destruct Gcl as [(_ & C2 & _) | (C1 & _)]; [exact C2 | lia].
Qed.

Lemma in_after_malloc s s1 l1 l2 q n b :
  user_blocks s1 = l1 ++ (q, n) :: l2 -> user_blocks s = l1 ++ l2 -> In b (user_blocks s) -> In b (user_blocks s1).
Proof.
  intros E1 E2 Hin. rewrite E1. rewrite E2 in Hin. apply in_app_or in Hin. apply in_or_app.
  destruct Hin as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma move_counts s s1 s' l1 l2 m1 m2 q n p k :
  user_blocks s1 = l1 ++ (q, n) :: l2 -> user_blocks s = l1 ++ l2 ->
  user_blocks s1 = m1 ++ (p, k) :: m2 -> user_blocks s' = m1 ++ m2 ->
  nblocks s' = nblocks s /\ ubytes s' = ubytes s - k + n.
Proof.
  intros E1 E2 F1 F2. pose proof (eq_trans (eq_sym E1) F1) as E.
  pose proof (f_equal (@length _) E) as EL. pose proof (f_equal (fold_right (fun b acc => snd b + acc) 0) E) as ES.
  rewrite !length_app in EL. rewrite !ub_fold_app in ES. cbn [length fold_right snd] in EL, ES.
  unfold nblocks, ubytes. rewrite F2, E2, !length_app, !ub_fold_app. split; lia.
Qed.

Lemma rm_of s g am i fr n : WF s -> usedX [] s g am -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
  fr_kind fr = FUser -> am_sc am = 63 -> MMAP_THRESHOLD <= n -> i = 0 /\ RMH s g am fr n.
Proof.
  intros HW Hu Hi Hfr Hk Hsc Hn. pose proof (last63 s g am HW Hu Hsc) as Hl.
  assert (i = 0) as -> by lia. split; [reflexivity|].
  split; [exact HW|]. split; [exact Hu|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hsc | exact Hn].
Qed.

Theorem realloc_wf : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') -> WF s'.
Proof.
  intros s p k n tr r s' HW Hin Hn Hy.
  destruct (ra_cases answer_ok s p k n tr r s' HW Hin (rpath_yields _ _ _ Hy))
    as [[-> ->] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [exact HW|].
  destruct C as [(Hc & -> & ->) | [(Hsc & Hbig & Hml & -> & ->) | [(Hsc & Hbig & Hne & -> & ->) | (tr' & Hm)]]].
  - exact (ip_wf s g am i fr n (ip_of_c1 s g am i fr n HW Hu Hi Hfr Hk Hn Hc)).
  - exact (ip_wf s g am i fr n (ip_of_same s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig Hml)).
  - destruct (rm_of s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig) as [-> R]. exact (rm_wf s g am fr n R).
  - destruct (ra_move answer_ok p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (yields_rpath _ _ _ H1) as Y1. pose proof (malloc_wf s n tr1 q s1 HW Hn Y1) as HW1.
    destruct q as [q|].
    + destruct Hq as (_ & tr2 & H2).
      destruct (malloc_blocks s n tr1 (Some q) s1 HW Hn Y1) as (l1 & l2 & E1 & E2 & _).
      exact (free_wf s1 p k tr2 s' HW1 (in_after_malloc s s1 l1 l2 q n (p, k) E1 E2 Hin) (yields_rpath _ _ _ H2)).
    + destruct Hq as (_ & ->). exact HW1.
Qed.

Theorem realloc_counts : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') ->
  match r with
  | Some _ => nblocks s' = nblocks s /\ ubytes s' = ubytes s - k + n
  | None => user_blocks s' = user_blocks s
  end.
Proof.
  intros s p k n tr r s' HW Hin Hn Hy.
  destruct (ra_cases answer_ok s p k n tr r s' HW Hin (rpath_yields _ _ _ Hy))
    as [[-> ->] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [reflexivity|].
  destruct C as [(Hc & -> & ->) | [(Hsc & Hbig & Hml & -> & ->) | [(Hsc & Hbig & Hne & -> & ->) | (tr' & Hm)]]].
  - destruct (ip_blocks s g am i fr n (ip_of_c1 s g am i fr n HW Hu Hi Hfr Hk Hn Hc)) as (l1 & l2 & E1 & E2).
    rewrite En in E1. exact (swap_counts _ _ _ _ _ _ _ _ E1 E2).
  - destruct (ip_blocks s g am i fr n (ip_of_same s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig Hml)) as (l1 & l2 & E1 & E2).
    rewrite En in E1. exact (swap_counts _ _ _ _ _ _ _ _ E1 E2).
  - destruct (rm_of s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig) as [-> R].
    destruct (rm_blocks s g am fr n R) as (l1 & l2 & E1 & E2).
    rewrite En in E1. exact (swap_counts _ _ _ _ _ _ _ _ E1 E2).
  - destruct (ra_move answer_ok p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (yields_rpath _ _ _ H1) as Y1. pose proof (malloc_wf s n tr1 q s1 HW Hn Y1) as HW1.
    pose proof (malloc_blocks s n tr1 q s1 HW Hn Y1) as MB.
    destruct q as [q|].
    + destruct Hq as (-> & tr2 & H2). destruct MB as (l1 & l2 & E1 & E2 & _).
      destruct (free_blocks s1 p k tr2 s' HW1 (in_after_malloc s s1 l1 l2 q n (p, k) E1 E2 Hin) (yields_rpath _ _ _ H2))
        as (m1 & m2 & F1 & F2).
      exact (move_counts s s1 s' l1 l2 m1 m2 q n p k E1 E2 F1 F2).
    + destruct Hq as (-> & ->). exact MB.
Qed.

Theorem realloc_inv : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> yields (realloc (Some p) n s) tr (r, s') ->
  SI s -> GS s -> NL s -> noraw s -> SI s' /\ GS s' /\ NL s' /\ noraw s'.
Proof.
  intros s p k n tr r s' HW Hin Hn Hy HS HG HN HR.
  destruct (ra_cases answer_ok s p k n tr r s' HW Hin (rpath_yields _ _ _ Hy))
    as [[-> ->] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [auto|].
  destruct C as [(Hc & -> & ->) | [(Hsc & Hbig & Hml & -> & ->) | [(Hsc & Hbig & Hne & -> & ->) | (tr' & Hm)]]].
  - pose proof (ip_of_c1 s g am i fr n HW Hu Hi Hfr Hk Hn Hc) as I.
    split; [exact (ip_SI _ _ _ _ _ _ I HS)|]. split; [exact (ip_GS _ _ _ _ _ _ I HG)|].
    split; [exact (ip_NL _ _ _ _ _ _ I HN) | exact (upd_noraw _ _ _ HR)].
  - pose proof (ip_of_same s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig Hml) as I.
    split; [exact (ip_SI _ _ _ _ _ _ I HS)|]. split; [exact (ip_GS _ _ _ _ _ _ I HG)|].
    split; [exact (ip_NL _ _ _ _ _ _ I HN) | exact (upd_noraw _ _ _ HR)].
  - destruct (rm_of s g am i fr n HW Hu Hi Hfr Hk Hsc Hbig) as [-> R].
    split; [exact (rm_SI _ _ _ _ _ R HS)|]. split; [exact (rm_GS _ _ _ _ _ R HG)|].
    split; [exact (rm_NL _ _ _ _ _ R HN) | exact (rm_noraw _ _ _ _ _ HR)].
  - destruct (ra_move answer_ok p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (yields_rpath _ _ _ H1) as Y1. pose proof (malloc_wf s n tr1 q s1 HW Hn Y1) as HW1.
    pose proof (AllocMalloc.malloc_SI s n tr1 q s1 HW HS Hn Y1) as HS1.
    pose proof (AllocMalloc.malloc_GS s n tr1 q s1 HW HG Hn Y1) as HG1.
    pose proof (AllocMalloc.malloc_NL s n tr1 q s1 HW HN Hn Y1) as HN1.
    pose proof (AllocMalloc.malloc_noraw s n tr1 q s1 HR Y1) as HR1.
    pose proof (malloc_blocks s n tr1 q s1 HW Hn Y1) as MB.
    destruct q as [q|].
    + destruct Hq as (_ & tr2 & H2). destruct MB as (l1 & l2 & E1 & E2 & _).
      pose proof (in_after_malloc s s1 l1 l2 q n (p, k) E1 E2 Hin) as Hin1. pose proof (yields_rpath _ _ _ H2) as Y2.
      split; [exact (AllocFree.free_SI s1 p k tr2 s' HW1 HS1 Hin1 Y2)|].
      split; [exact (AllocFree.free_GS s1 p k tr2 s' HW1 HG1 Hin1 Y2)|].
      split; [exact (AllocFree.free_NL s1 p k tr2 s' HW1 HN1 Hin1 Y2) | exact (AllocFree.free_noraw s1 p k tr2 s' HW1 Hin1 HR1 Y2)].
    + destruct Hq as (_ & ->). auto.
Qed.

Theorem realloc_hand : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> SI s -> NL s -> noraw s ->
  cpath04 (realloc (Some p) n s) tr (r, s') ->
  exists s1, WF s1 /\ SI s1 /\ NL s1 /\ nblocks s1 <= nblocks s + 1 /\ hand s' <= Z.max (hand s) (nused s1).
Proof.
  intros s p k n tr r s' HW Hin Hn HS HN HR Hc.
  assert (B0 : WF s /\ SI s /\ NL s /\ nblocks s <= nblocks s + 1 /\ hand s <= Z.max (hand s) (nused s))
    by (split; [exact HW|]; split; [exact HS|]; split; [exact HN|]; split; lia).
  destruct (ra_cases canswer04 s p k n tr r s' HW Hin (rpath_cpath04 _ _ _ Hc))
    as [[-> ->] | (g & am & i & fr & Hu & Hi & Hfr & Hk & En & Ep & C)]; [exists s; exact B0|].
  destruct C as [(Hc1 & -> & ->) | [(Hsc & Hbig & Hml & -> & ->) | [(Hsc & Hbig & Hne & -> & ->) | (tr' & Hm)]]].
  - exists s. exact B0.
  - exists s. exact B0.
  - exists s. rewrite rm_hand. exact B0.
  - destruct (ra_move canswer04 p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (cpath04_rpath _ _ _ H1) as C1. pose proof (cpath04_yields _ _ _ C1) as Y1.
    pose proof (malloc_wf s n tr1 q s1 HW Hn Y1) as HW1.
    pose proof (AllocMalloc.malloc_SI s n tr1 q s1 HW HS Hn Y1) as HS1.
    pose proof (AllocMalloc.malloc_NL s n tr1 q s1 HW HN Hn Y1) as HN1.
    pose proof (AllocMalloc.malloc_hand s n tr1 q s1 HW HS HR Hn C1) as HH1.
    pose proof (malloc_blocks s n tr1 q s1 HW Hn Y1) as MB.
    exists s1. split; [exact HW1|]. split; [exact HS1|]. split; [exact HN1|].
    destruct q as [q|].
    + destruct Hq as (_ & tr2 & H2). destruct MB as (l1 & l2 & E1 & E2 & _).
      pose proof (in_after_malloc s s1 l1 l2 q n (p, k) E1 E2 Hin) as Hin1.
      pose proof (cpath04_yields _ _ _ (cpath04_rpath _ _ _ H2)) as Y2.
      rewrite (AllocFree.free_hand s1 p k tr2 s' HW1 Hin1 Y2). split; [|exact HH1].
      unfold nblocks. rewrite E1, E2, !length_app. cbn [length]. lia.
    + destruct Hq as (_ & ->). split; [|exact HH1]. unfold nblocks. rewrite MB. lia.
Qed.

Theorem realloc_hand_bound : forall s p k n tr r s',
  WF s -> In (p, k) (user_blocks s) -> 0 <= n -> SI s -> NL s -> noraw s ->
  cpath04 (realloc (Some p) n s) tr (r, s') -> hand s' <= Z.max (hand s) (13 * (nblocks s + 1) + 48).
Proof.
  intros s p k n tr r s' HW Hin Hn HS HN HR Hc.
  destruct (realloc_hand s p k n tr r s' HW Hin Hn HS HN HR Hc) as (s1 & HW1 & HS1 & HN1 & Hb & Hh).
  pose proof (AllocDepth.nused_bound_depth s1 HW1 HS1 HN1) as Hu. lia.
Qed.
