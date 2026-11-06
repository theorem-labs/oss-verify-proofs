(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl KLedger JLedger
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_WCreate MI_Cnt MI_TF2 MI_WCreate2
  MI_WSlot MI_WSlot2 MI_WSlot3 MI_WMalloc MI_Nat MI_Joint1 MI_Joint2 MI_Joint3 MI_Joint4.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section PRUN2.
Context {OG OC : Type} (pansG : OG -> aptr -> Z -> Z -> Z) (pupdG : OG -> ev -> Z -> OG)
        (pansC : OC -> aptr -> Z -> Z -> Z) (pupdC : OC -> ev -> Z -> OC).

#[using="Type"] Lemma jsim_prun {R1 R2} (tG : M R1) : forall (tC : M R2) J Post oG oC,
  jsim J tG tC Post ->
  jsim J (prun pansG pupdG oG tG) (prun pansC pupdC oC tC) (fun J' x y => Post J' (snd x) (snd y)).
Proof.
  induction tG as [x|eG kG IH]; intros tC J Post oG oC H; destruct tC as [y|eC kC]; cbn in H; try contradiction.
  - exact H.
  - destruct eG; contradiction.
  - apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG, eC; cbn in UG, UC; try discriminate. unfold prun. cbn. exact I.
    + destruct (jev_rel_not_undef _ _ _ HR) as [NUG NUC].
      assert (PG : is_peek eG = false /\ is_peek eC = false) by (destruct eG, eC; cbn in HR |- *; try contradiction; auto).
      destruct PG as [PG PC].
      unfold prun. rewrite !eruns_vis_keep by (destruct eG, eC; cbn in PG, PC |- *; try discriminate; reflexivity).
      apply jsim_vis; [exact HR| exact HC|]. intros zG zC Hz. apply IH. apply HK. exact Hz.
Qed.
End PRUN2.

Lemma jsim_strel2 {A1 A2 B1 B2} (RA : A1 -> B1 -> Prop) (RB : A2 -> B2 -> Prop) (tG : M A1) :
  forall (tC : M A2) (tG' : M B1) (tC' : M B2) J Post,
  jsim J tG tC Post -> strel RA tG tG' -> strel RB tC tC' ->
  jsim J tG' tC' (fun J' x' y' => exists x y, Post J' x y /\ RA x x' /\ RB y y').
Proof.
  induction tG as [x|eG kG IH]; intros tC tG' tC' J Post H SA SB; destruct tC as [y|eC kC]; cbn in H; try contradiction.
  - inversion SA; subst. inversion SB; subst. cbn. exists x, y. auto.
  - destruct eG; contradiction.
  - inversion SA; subst. inversion SB; subst.
    apply jsim_vis_inv in H as [[UG UC]|(HR & HC & HK)].
    + destruct eG, eC; cbn in UG, UC; try discriminate. exact I.
    + apply jsim_vis; [exact HR| exact HC|]. intros zG zC Hz. eapply IH; [apply HK; exact Hz| auto| auto].
Qed.

Lemma jtree_ok_paths {R1 R2} (tG : M R1) : forall (tC : M R2) J (P1 P2 : jled -> R1 -> R2 -> Prop),
  jtree_ok J tG tC P1 -> (forall J' x y, jcpath J tG tC J' x y -> P2 J' x y) -> jtree_ok J tG tC P2.
Proof.
  induction tG as [x|eG kG IH]; intros tC J P1 P2 H HP; destruct tC as [y|eC kC]; cbn in H |- *; try contradiction.
  - apply HP. constructor.
  - destruct H as [HR HK]. split; [exact HR|]. intros zG zC Hz. apply (IH zG (kC zC) _ P1); [apply HK; exact Hz|].
    intros J' x y CP. apply HP. econstructor; [exact Hz| exact CP].
Qed.

Lemma jevent_post_live J eG eC zG zC : j_live (jevent_post J eG eC zG zC) = j_live J.
Proof.
  destruct eG, eC; cbn; try reflexivity.
  - destruct (addr =? 0); [reflexivity|]. destruct (zG =? addr); [| reflexivity]. destruct (j_brk J); try reflexivity; destruct (j_brkreg J) as [[[? ?] ?]|]; reflexivity.
  - destruct (Z.land flags MAP_FIXED =? 0); [| reflexivity]. destruct (is_err zG); [reflexivity|]. destruct (prot =? PROT_NONE); reflexivity.
  - destruct (mprot_okb zG); reflexivity.
Qed.

Lemma jcpath_live {R1 R2} (tG : M R1) : forall (tC : M R2) J J' x y, jcpath J tG tC J' x y -> j_live J' = j_live J.
Proof.
  induction tG as [x0|eG kG IH]; intros tC J J' x y CP; inversion CP; subst; [reflexivity|].
  match goal with H : jcpath _ (kG ?z) _ _ _ _ |- _ => rewrite (IH z _ _ _ _ _ H) end. apply jevent_post_live.
Qed.

Section CORE2.
Variables (BLG BLC : list blk).

Definition PostC (PUG PUC : mled -> mstate * option (aptr * Z) -> Prop) (J' : jled) (x y : mstate * option (aptr * Z)) : Prop :=
  snd y = snd x /\ PUG (projG J') x /\ PUC (projC J') y /\ exists rho', JR J' rho' (fst x) (fst y).

Definition KR : mstate -> option (aptr * Z) -> M (mstate * option (aptr * Z)) := fun st1 r => ret (st1, r).

#[using="Type"] Lemma alloc_slot_nobail sc st L BL LS req : INVL x0 st L BL LS -> TF0 st -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  gtree L (alloc_slot full_lay FUEL st sc req kP bP) (fun _ r => r <> None).
Proof.
  intros INV TF Hsc Hreq Hfit. apply ftree_gtree.
  apply (alloc_slot_ft (option (mstate * Z)) (fun _ r => r <> None) FUEL sc [] st L BL LS req kP bP); try assumption.
  - unfold FUEL. cbn. lia.
  - apply NoDup_nil_2.
  - intros st1 idx L1 LS1 _. cbn. discriminate.
Qed.

#[using="Type"] Lemma malloc_small_rel J rho sG sC LSG LSC n PUG PUC :
  ENT2 BLG BLC x0 J rho sG sC LSG LSC -> TF0 sG -> 0 <= n -> n < MMAP_THRESHOLD ->
  gtree (projG J) (malloc_small_ctrl full_lay sG n KR (ret (sG, None))) PUG ->
  gtree (projC J) (malloc_small_ctrl full_lay sC n KR (ret (sC, None))) PUC ->
  jsim J (malloc_small_ctrl full_lay sG n KR (ret (sG, None)))
         (malloc_small_ctrl full_lay sC n KR (ret (sC, None))) (PostC PUG PUC).
Proof.
  intros (INVG & INVC & R) TFG Hn Hlt FTG FTC. pose proof (jr_rc _ _ _ _ R) as HRC.
  pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl in FTG, FTC |- *.
  rewrite !(RC_active _ _ _ _ _ _ HRC), !(RC_usage _ _ _ _ _ _ HRC), !(RC_MRc _ _ _ _ _ _ HRC) in FTC |- *.
  set (sc0 := size_to_class n) in *.
  set (sc := match active sG sc0 with Some _ => sc0 | None => _ end) in *.
  assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { subst sc. destruct (active sG sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage sG sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].

  assert (SLOT : forall PUG0 PUC0,
    gtree (projG J) (alloc_slot full_lay FUEL sG sc n (fun st1 idx => if idx <? 0 then KR st1 None else match active st1 sc with Some gp => KR st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => ret (sG, @None (aptr * Z))) end) (ret (sG, None))) PUG0 ->
    gtree (projC J) (alloc_slot full_lay FUEL sC sc n (fun st1 idx => if idx <? 0 then KR st1 None else match active st1 sc with Some gp => KR st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => ret (sC, @None (aptr * Z))) end) (ret (sC, None))) PUC0 ->
    jsim J (alloc_slot full_lay FUEL sG sc n (fun st1 idx => if idx <? 0 then KR st1 None else match active st1 sc with Some gp => KR st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => ret (sG, @None (aptr * Z))) end) (ret (sG, None)))
           (alloc_slot full_lay FUEL sC sc n (fun st1 idx => if idx <? 0 then KR st1 None else match active st1 sc with Some gp => KR st1 (Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => ret (sC, @None (aptr * Z))) end) (ret (sC, None)))
           (PostC PUG0 PUC0)).
  { intros PUG0 PUC0 FTG0 FTC0.
    match goal with |- jsim _ (alloc_slot full_lay FUEL sG sc n ?kg ?bg) (alloc_slot full_lay FUEL sC sc n ?kc ?bc) _ =>
      apply (jsim_steq J (sbind (alloc_slot full_lay FUEL sG sc n kP bP) (KF kg bg)) _ (sbind (alloc_slot full_lay FUEL sC sc n kP bP) (KF kc bc)) _);
      [apply steq_sym; apply alloc_slot_natP| apply steq_sym; apply alloc_slot_natP|];
      apply (gtree_steq _ _ (alloc_slot_natP full_lay FUEL sG sc n kg bg)) in FTG0; apply (gtree_steq _ _ (alloc_slot_natP full_lay FUEL sC sc n kc bc)) in FTC0
    end.
    apply gtree_sbind_inv in FTG0. apply gtree_sbind_inv in FTC0.
    pose proof (alloc_slot_rel BLG BLC FUEL x0 J rho sG sC LSG LSC sc n _ _ ltac:(split; [exact INVG| split; [exact INVC| exact R]]) eq_refl eq_refl SC' Hn FIT' FTG0 FTC0) as AS.
    eapply jsim_bind_path; [exact AS|].
    intros J2 x y PR CP.
    destruct x as [[sG2 idxG]|]; destruct y as [[sC2 idxC]|]; cbn in PR; try contradiction.
    2:{ exfalso. exact (gtree_cpath _ _ _ _ _ (alloc_slot_nobail sc sG (projG J) BLG LSG n INVG TFG SC' Hn FIT') (jcpath_cpath_G _ _ _ _ _ _ _ AS CP) eq_refl). }
    clear FTG0 FTC0. destruct PR as (EI & FTG2 & FTC2 & rho2 & R2). subst idxC. cbn [KF] in FTG2, FTC2 |- *.
    pose proof (jr_rc _ _ _ _ R2) as HRC2.
    destruct (idxG <? 0).
    - apply jsim_ret. cbn. split; [reflexivity|]. split; [exact FTG2|]. split; [exact FTC2|]. exists rho2. exact R2.
    - rewrite (RC_active _ _ _ _ _ sc HRC2) in FTC2 |- *. destruct (active sG2 sc) as [g|]; [| apply jsim_undef].
      apply jsim_ret. cbn. split; [reflexivity|]. split; [exact FTG2|]. split; [exact FTC2|]. exists rho2. exact R2. }

  destruct (active sG sc) as [gp|] eqn:HA.
  - rewrite !(RC_MRc _ _ _ _ _ gp HRC) in FTC |- *.
    destruct (negb (lowbit (m_avail (get_meta_rec sG gp)) =? 0)).
    + apply jsim_ret. cbn. split; [reflexivity|]. split; [exact FTG|]. split; [exact FTC|]. exists rho. apply JR_upd_meta. exact R.
    + apply SLOT; [exact FTG| exact FTC].
  - cbn [lowbit Z.eqb negb] in FTG, FTC |- *. change (negb (lowbit 0 =? 0)) with false in *. cbn iota in FTG, FTC |- *. apply SLOT; [exact FTG| exact FTC].
Qed.

#[using="Type"] Lemma alloc_meta_nobail X BL st L LS : INVL X st L BL LS -> gtree L (alloc_meta st kP bP) (fun _ r => r <> None).
Proof.
  intros INV. apply ftree_gtree.
  eapply (alloc_meta_ft (option (mstate * optr)) BL (fun _ r => r <> None) kP bP X st L); [| | exact INV| apply amf_refl| apply lf_refl].
  - intros st1 L1 LS1 _ _ _. cbn. discriminate.
  - intros st1 L1 LS1 m _ _ _ _. cbn. discriminate.
Qed.

#[using="Type"] Lemma RC_gai rho resv ceil sG sC g : RC rho resv ceil sG sC -> group_active_idx sC g = group_active_idx sG g.
Proof. intros H. unfold group_active_idx, get_group. rewrite (RC_groups _ _ _ _ _ H). reflexivity. Qed.

#[using="Type"] Lemma JR_strip J rho sG sC : JR J rho sG sC <-> JR J rho (strip sG) (strip sC).
Proof.
  split; intros [R1 R2 R3 R4 R5]; constructor; cbn in *; auto. Qed.

#[using="Type"] Lemma JR_layout J rho sG sC sG' sC' : JR J rho sG sC -> strip sG' = strip sG -> strip sC' = strip sC -> JR J rho sG' sC'.
Proof. intros R EG EC. apply (proj2 (JR_strip _ _ _ _)). rewrite EG, EC. apply (proj1 (JR_strip _ _ _ _)). exact R. Qed.

#[using="Type"] Theorem malloc_core_rel J rho sG sC LSG LSC n :
  ENT2 BLG BLC x0 J rho sG sC LSG LSC -> TF0 sG -> TF0 sC -> 0 <= n ->
  jsim J (malloc_core full_lay sG n) (malloc_core full_lay sC n) (PostC (CORE_POST sG n (projG J) BLG) (CORE_POST sC n (projC J) BLC)).
Proof.
  intros ENT0 TFG TFC Hn. pose proof ENT0 as (INVG & INVC & R). pose proof (jr_rc _ _ _ _ R) as HRC.
  pose proof (ftree_gtree _ _ _ (malloc_core_ft sG (projG J) BLG LSG n INVG TFG Hn)) as FTG.
  pose proof (ftree_gtree _ _ _ (malloc_core_ft sC (projC J) BLC LSC n INVC TFC Hn)) as FTC.
  unfold malloc_core in FTG, FTC |- *.
  destruct (size_overflows n) eqn:Hov.
  { apply jsim_ret. cbn [PostC fst snd]. split; [reflexivity|]. split; [exact FTG|]. split; [exact FTC|]. exists rho. exact R. }
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
  2:{ exact (malloc_small_rel J rho sG sC LSG LSC n _ _ ENT0 TFG Hn Hsmall FTG FTC). }

  unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT) in *.
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  rewrite <- (RC_live_ranges_irrel) in FTC |- * || idtac.
  apply gtree_vis_inv in FTG as [PREG FKG]; [| reflexivity]. apply gtree_vis_inv in FTC as [PREC FKC]; [| reflexivity].
  apply jsim_vis.
  - cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. left.
    cbn in PREG. destruct PREG as [(Q & _ & _ & _ & LEN)|(cur & _ & _ & _ & _ & F)]; [| discriminate F].
    split; [exact Q|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity| exact LEN].
  - exact I.
  - intros zG zC Hz. pose proof (jans_ok_G _ _ _ _ _ Hz) as AG. pose proof (jans_ok_C _ _ _ _ _ Hz) as AC. pose proof (jans_ok_class _ _ _ _ _ Hz) as CL.
    specialize (FKG zG AG). specialize (FKC zC AC).
    apply gtree_not_bad in FKG as [OKG FKG]. apply gtree_not_bad in FKC as [OKC FKC]. rewrite OKG, OKC. cbn [negb].
    cbn in CL. apply Bool.eqb_prop in CL.
    cbn [jevent_post]. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    unfold event_post in FKG, FKC. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in FKG, FKC. change (PROT_RW =? PROT_NONE) with false in FKG, FKC. cbn iota in FKG, FKC.
    rewrite <- CL in FKC |- *.
    destruct (is_err zG) eqn:ER.
    { apply jsim_ret. cbn [PostC fst snd]. split; [reflexivity|]. split; [exact FKG|]. split; [exact FKC|]. exists rho. exact R. }

    cbn [new_region] in FKG, FKC |- *.
    change (set_next_rid (N.succ (s_next_rid sG)) (set_regions (<[s_next_rid sG := {| r_kind := RKGroup; r_base := zG; r_len := needed |}]> (s_regions sG)) sG))
      with (fst (new_region RKGroup zG needed sG)) in *.
    change (set_next_rid (N.succ (s_next_rid sC)) (set_regions (<[s_next_rid sC := {| r_kind := RKGroup; r_base := zC; r_len := needed |}]> (s_regions sC)) sC))
      with (fst (new_region RKGroup zC needed sC)) in *.
    rewrite (RC_next_rid _ _ _ _ _ HRC) in FKC |- *.
    pose proof (INVL_step_seq _ _ _ _ _ (INVL_new_group_region x0 sG (projG J) BLG LSG zG needed INVG eq_refl OKG ER ltac:(unfold LEN_MAX; clear -HN; lia))) as INVG2.
    pose proof (INVL_step_seq _ _ _ _ _ (INVL_new_group_region x0 sC (projC J) BLC LSC zC needed INVC eq_refl OKC ltac:(rewrite <- CL; reflexivity) ltac:(unfold LEN_MAX; clear -HN; lia))) as INVC2.
    rewrite (RC_next_rid _ _ _ _ _ HRC) in INVC2.
    pose proof (JR_new_group J rho sG sC zG zC needed x0 (projG J) R (proj1 INVG)) as R1.
    set (J1 := jset_groups ((zG, zC, needed) :: j_groups J) J) in *.
    set (rid := s_next_rid sG) in *. set (rho1 := nupd rho rid zC) in *.
    set (sG1 := fst (new_region RKGroup zG needed sG)) in *. set (sC1 := fst (new_region RKGroup zC needed sC)) in *.
    change (set_groups ((zG, needed) :: ld_groups (projG J)) (projG J)) with (projG J1) in *.
    change (set_groups ((zC, needed) :: ld_groups (projC J)) (projC J)) with (projC J1) in *.
    destruct (step_seq_fields sG1) as (SSG1 & SSG2 & SSG3 & SSG4 & SSG5 & _). destruct (step_seq_fields sC1) as (SSC1 & SSC2 & SSC3 & SSC4 & SSC5 & _).
    assert (R2 : JR J1 rho1 (step_seq sG1) (step_seq sC1)).
    { apply (JR_frame J1 rho1 sG1 sC1); [exact R1| exact SSG4| | | apply RC_step_seq; exact (jr_rc _ _ _ _ R1)];
        unfold step_seq; destruct (c_seq _ =? 255); reflexivity. }
    assert (HrG : s_regions (step_seq sG1) !! rid = Some (mkRegion RKGroup zG needed)) by (rewrite SSG4; unfold sG1; rewrite ng_lookup; fold rid; rewrite N.eqb_refl; reflexivity).
    assert (HrC : s_regions (step_seq sC1) !! rid = Some (mkRegion RKGroup zC needed)).
    { rewrite SSC4. unfold sC1. rewrite lookup_new_region, (RC_next_rid _ _ _ _ _ HRC). fold rid. rewrite N.eqb_refl. reflexivity. }
    assert (TFG2 : TF0 (step_seq sG1)).
    { apply (TF0_ctrl sG1); [exact SSG1| exact SSG2|]. apply (TF0_ctrl sG); [reflexivity| reflexivity| exact TFG]. }
    assert (TFC2 : TF0 (step_seq sC1)).
    { apply (TF0_ctrl sC1); [exact SSC1| exact SSC2|]. apply (TF0_ctrl sC); [reflexivity| reflexivity| exact TFC]. }

    match goal with |- jsim _ (alloc_meta ?s ?kg ?bg) (alloc_meta ?s' ?kc ?bc) _ =>
      apply (jsim_steq J1 (sbind (alloc_meta s kP bP) (KF kg bg)) _ (sbind (alloc_meta s' kP bP) (KF kc bc)) _);
      [apply steq_sym; apply alloc_meta_natP| apply steq_sym; apply alloc_meta_natP|];
      apply (gtree_steq _ _ (alloc_meta_natP s kg bg)) in FKG; apply (gtree_steq _ _ (alloc_meta_natP s' kc bc)) in FKC
    end.
    apply gtree_sbind_inv in FKG. apply gtree_sbind_inv in FKC.
    pose proof (alloc_meta_rel (xorph x0 (Some rid)) BLG BLC (step_seq sG1) (step_seq sC1) J1 J1 rho1 (step_seq sG1) (step_seq sC1) LSG LSC
                  ltac:(split; [exact INVG2|]; split; [exact INVC2|]; split; [exact R2|]; split; [apply amf_refl|]; split; [apply amf_refl| apply jf_refl])) as AM.
    eapply jsim_bind_path; [exact AM|].
    intros J3 x y PAM CP.
    pose proof (gtree_cpath _ _ _ _ _ FKG (jcpath_cpath_G _ _ _ _ _ _ _ AM CP)) as FKG3.
    pose proof (gtree_cpath _ _ _ _ _ FKC (jcpath_cpath_C _ _ _ _ _ _ _ AM CP)) as FKC3.
    destruct x as [[sG3 moG]|]; destruct y as [[sC3 moC]|]; cbn in PAM; try contradiction.
    2:{ exfalso. exact (gtree_cpath _ _ _ _ _ (alloc_meta_nobail _ BLG (step_seq sG1) (projG J1) LSG INVG2) (jcpath_cpath_G _ _ _ _ _ _ _ AM CP) eq_refl). }
    clear FKG FKC. cbn beta in FKG3, FKC3.
    destruct PAM as (EMO & rho3 & LSG3 & LSC3 & R3 & AFG & AFC & JF3 & INV3). subst moC.
    cbn [KF] in FKG3, FKC3 |- *.
    pose proof (jr_rc _ _ _ _ R3) as HRC3.
    pose proof (amf_regions _ _ AFG rid _ HrG eq_refl) as HrG3. pose proof (amf_regions _ _ AFC rid _ HrC eq_refl) as HrC3.
    assert (Erho : rho3 rid = zC).
    { pose proof (RC_region _ _ _ _ _ rid HRC3) as E. rewrite HrG3, HrC3 in E. cbn in E. unfold rebase_region in E. cbn in E. congruence. }

    destruct moG as [g|].
    +
      apply jsim_ret. cbn [PostC fst snd]. split; [reflexivity|]. split; [exact FKG3|]. split; [exact FKC3|].
      exists rho3. cbn [fst snd lh_hdr full_lay].
      match goal with |- JR _ _ (upd_ctx ?f (add_slots g ?p ?strG 1 (put_group ?p ?og ?aiG (hdr_havoc ?p ?s4G))))
                              (upd_ctx ?f (add_slots g ?p ?strC 1 (put_group ?p ?og ?aiC (hdr_havoc ?p ?s4C)))) =>
        set (st4G := s4G); set (st4C := s4C);
        assert (RC4 : RC rho3 (j_resvC J3) (j_ceilC J3) (hdr_havoc p st4G) (hdr_havoc p st4C))
          by (eapply RC_layout; [apply RC_upd_meta; exact HRC3| apply strip_hdr_havoc| apply strip_hdr_havoc]);
        replace aiC with aiG by (unfold st4G, st4C; rewrite (RC_gai _ _ _ _ _ p (RC_upd_meta _ _ _ g _ _ _ HRC3)); reflexivity)
      end.
      match goal with |- JR _ _ (upd_ctx ?f (add_slots g ?p ?strG 1 ?s5G)) (upd_ctx ?f (add_slots g ?p ?strC 1 ?s5C)) =>
        assert (RC5 : RC rho3 (j_resvC J3) (j_ceilC J3) s5G s5C) by (apply RC_put_group; exact RC4);
        replace strC with strG by (rewrite (RC_MRc _ _ _ _ _ g RC5); reflexivity)
      end.
      apply (JR_frame J3 rho3 sG3 sC3); [exact R3| reflexivity| reflexivity| reflexivity|].
      apply RC_upd_ctx. apply RC_add_slots. exact RC5.
    +
      destruct INV3 as [INVG3 INVC3].
      apply gtree_vis_inv in FKG3 as [PREG3 FKG4]; [| reflexivity]. apply gtree_vis_inv in FKC3 as [PREC3 FKC4]; [| reflexivity].
      assert (JREL : jev_rel J3 (EMunmap zG needed) (EMunmap zC needed)).
      { cbn. split; [reflexivity|]. split; [exact (brk_quiet_of _ _ _ (proj1 INVG3))|].
        exists needed. rewrite (jf_groups _ _ JF3). split; [left; reflexivity| left; reflexivity]. }
      assert (JCOH : jcoh J3 (EMunmap zG needed) (EMunmap zC needed)).
      { cbn. rewrite <- Erho. apply (coh_munmap (xorph x0 (Some rid)) BLG LSG3 J3 rho3 sG3 sC3 INVG3 (proj1 INVC3) R3 rid _ HrG3 eq_refl). }
      apply jsim_vis; [exact JREL| exact JCOH|].
      intros uG uC Hu. pose proof (jans_ok_G _ _ _ _ _ Hu) as UG. pose proof (jans_ok_C _ _ _ _ _ Hu) as UC. pose proof (jans_ok_class _ _ _ _ _ Hu) as UCL.
      specialize (FKG4 uG UG). specialize (FKC4 uC UC). cbn [answer_ok] in UG, UC. rewrite UG in FKG4 |- *. rewrite UC in FKC4 |- *.
      apply jsim_ret. unfold PostC. rewrite (projG_post J3 _ _ uG uC JREL UCL), (projC_post_coh J3 _ _ uG uC JREL JCOH UCL). cbn [fst snd].
      split; [reflexivity|]. split; [exact FKG4|]. split; [exact FKC4|].
      exists rho3. cbn [jevent_post].
      apply (JR_drop_group J3 rho3 sG3 sC3 rid (mkRegion RKGroup zG needed) _ (projG J3) _ (projC J3) R3 (proj1 INVG3) (proj1 INVC3) HrG3 eq_refl).
Qed.

Definition PostM (J' : jled) (x y : mstate * option cptr) : Prop :=
  snd y = snd x /\ exists rho', JR J' rho' (fst x) (fst y).

#[using="Type"] Theorem cmalloc_rel J rho sG sC LSG LSC n :
  ENT2 BLG BLC x0 J rho sG sC LSG LSC -> 0 <= n ->
  jsim J (cmalloc (strip sG) n) (cmalloc (strip sC) n) PostM.
Proof.
  intros (INVG & INVC & R) Hn.
  set (sG0 := set_tick (N.succ (s_tick sG)) sG). set (sC0 := set_tick (N.succ (s_tick sC)) sC).
  assert (INVG0 : INVL x0 sG0 (projG J) BLG LSG) by (apply INVL_set_tick; [cbn; lia| exact INVG]).
  assert (INVC0 : INVL x0 sC0 (projC J) BLC LSC) by (apply INVL_set_tick; [cbn; lia| exact INVC]).
  assert (TFG : TF0 sG0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INVG)| cbn; lia]).
  assert (TFC : TF0 sC0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INVC)| cbn; lia]).
  assert (R0 : JR J rho sG0 sC0) by (apply (JR_layout J rho sG sC); [exact R| apply strip_set_tick| apply strip_set_tick]).
  pose proof (malloc_core_rel J rho sG0 sC0 LSG LSC n ltac:(split; [exact INVG0| split; [exact INVC0| exact R0]]) TFG TFC Hn) as CORE.
  pose proof (jsim_prun pz pu pz pu _ _ _ _ tt tt CORE) as PR.
  pose proof (jsim_strel2 (CREL (O:=unit)) (CREL (O:=unit)) _ _ _ _ _ _ PR
                (malloc_core_ctrl pz pu n tt sG0 (strip sG) ltac:(unfold sG0; rewrite strip_set_tick; reflexivity))
                (malloc_core_ctrl pz pu n tt sC0 (strip sC) ltac:(unfold sC0; rewrite strip_set_tick; reflexivity))) as J2.
  unfold cmalloc. eapply jsim_bind; [exact J2|].
  intros J' [csG1 rG] [csC1 rC] ([oG [sG1 rG']] & [oC [sC1 rC']] & PC & [EG1 EG2] & [EC1 EC2]). cbn in EG1, EG2, EC1, EC2. subst rG' rC' csG1 csC1.
  destruct PC as (ER & _ & _ & rho' & R'). cbn in ER. subst rC.
  apply jsim_ret. split.
  - cbn. destruct rG as [[g idx]|]; [| reflexivity]. cbn in R'. rewrite !slot_of_strip, (RC_slot_of _ _ _ _ _ g idx (jr_rc _ _ _ _ R')). reflexivity.
  - exists rho'. cbn in R' |- *. exact (proj1 (JR_strip _ _ _ _) R').
Qed.
End CORE2.

