(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CBA.
Definition mem := (word -> option byte).

Definition has_range (cells : list kentry) (e : expr) (lo hi : Z) : bool :=
  existsb (fun X => match X with KRange e' lo' hi' => (expr_eqb e e' && Z.leb lo lo' && Z.leb hi' hi)%bool | _ => false end) cells.
Lemma has_range_sound : forall segs E (M : mem) cells e lo hi, (forall X, In X cells -> kentry_ok segs E M X) -> has_range cells e lo hi = true ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof.
  intros segs E M cells e lo hi HK H. unfold has_range in H. apply existsb_exists in H as (X & Hin & Hb).
  destruct X as [| | | | |e' lo' hi'| | | |]; try discriminate. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.leb_le in H2, H3. subst e'. pose proof (HK _ Hin) as G. cbn [kentry_ok] in G. lia.
Qed.

Fixpoint regions_eqb (a b : list SGP.region) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (expr_eqb (fst (fst x)) (fst (fst y)) && Z.eqb (snd (fst x)) (snd (fst y)) && expr_eqb (snd x) (snd y) && regions_eqb a' b')%bool
  | _, _ => false
  end.
Lemma regions_eqb_eq : forall a b, regions_eqb a b = true -> a = b.
Proof.
  induction a as [|[[x1 x2] x3] a IH]; intros [|[[y1 y2] y3] b] H; cbn [regions_eqb fst snd] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1, H3. apply Z.eqb_eq in H2. subst. rewrite (IH b H4). reflexivity.
Qed.

Section Shape.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable FPI : FPState -> Prop.
Definition cps_asanG (pc r sp scr : Z) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dd : Z)
           (Pre : bvmap 5 word -> mem -> Prop)
           (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet),
    ri_inv HI LB FF LK cr A M (vml_of model) -> CHA.amodel_ok A model -> K [] -> FPI fx ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    CHA.astk ar M sp scr -> CHA.ffroom FF LK dd -> CHA.ffrs FF sp -> Pre R M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
            (LK' : list fframe) (A' : list (Z * Z)),
        FPI fx' -> Post R M R' M' LB' cr' LBk W -> regs_preserved R R' ->
        CHA.ahpres L ar LBk FF sp scr W M M' -> model_rt model model' -> incl A A' -> CHA.amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 r) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) model) K.
End Shape.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBrest FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Hypothesis KNIL : K [].

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).
Abbreviation curB := (CHA.curB LBrest BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).
Abbreviation CFACTS := (CHA.common_facts L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).

Lemma amb_off : forall i E A M model, AAMB i E A M model -> H_off_segments (hl_segs L) (ahid A model).
Proof. intros i E A M model HA. exact (proj2 (proj2 (proj2 (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M model HA)))). Qed.

Lemma leaf_agree0 : forall i c E E' A M model, AAMB i E A M model -> (NF <= CC.cp_nx c)%nat -> env_agree (CC.cp_nx c) E E' -> env_agree NF E0 E'.
Proof.
  intros i c E E' A M model (_ & _ & _ & Hag0 & _) Hnf Hag. eapply CC.env_agree_trans; [exact Hag0 | eapply CC.env_agree_le; [exact Hag | exact Hnf]].
Qed.

Lemma leaf_frame : forall i c ps E E' R R' A M model M1 model1,
  CHA.foot_chk NF d c (nth i BLS []) (nth i FFS []) = true -> CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model ->
  env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ CHA.afoot_sem sp0 d Wo (CH2.den E (nth i BLS [])) (CHA.denF sp0 E (nth i FFS [])) a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros i c ps E E' R R' A M model M1 model1 Hf HAt HA Hag HLF a Ha Hn. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF).
  pose proof HA as (_ & _ & _ & Hag0 & (cr & LK & HH & _) & _).
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  apply (CHA.foot_chk_sound L ar NF E0 sp0 d Wo STK SCR_pos NF32 SP0 WRS_ok c _ _ _ _ E E' R _ (Z_to_bv 64 a) Hf HAt Hag0 Hag RFx (incl_appl _ (incl_refl _))).
  rewrite L5.unsigned_lit by exact Ha. exact Hn.
Qed.

Lemma nodup_ff : forall (FF LK : list fframe), base.NoDup (map ff_addr (FF ++ LK)) -> base.NoDup (map ff_addr FF).
Proof. intros FF LK H. rewrite map_app in H. apply list_relations.list.NoDup_app in H as (H & _ & _). exact H. Qed.
Lemma own_front : forall LB FF LK cr A M V b n, ri_inv HI LB FF LK cr A M V -> In (b, n) LB -> ri_inv HI ((b, n) :: lb_remove b LB) FF LK cr A M V.
Proof.
  intros LB FF LK cr A M V b n HH Hin. destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as [ND1 ND2].
  apply (PmHeapIfaceA.aio_perm _ _ _ _ _ HIok LB _ FF FF LK cr A M V HH).
  - intros x. split.
    + intros Hx. destruct (Z.eq_dec (fst x) b) as [e|ne].
      * left. symmetry. apply (CH2.nodup_fst_eq LB x (b, n) ND1 Hx Hin). exact e.
      * right. destruct x as [B m]. exact (L5C.in_lb_remove_neq b B m LB Hx ne).
    + intros [<-|Hx]; [exact Hin | exact (L5C.in_lb_remove b x LB Hx)].
  - cbn [map fst]. apply list_relations.list.NoDup_cons. split; [|exact (CH2.lb_remove_nodup b LB ND1)].
    intros H. apply list_elem_of_In in H. exact (CH2.lb_remove_fst_notin b LB ND1 H).
  - intros f. split; intros X; exact X.
  - exact (nodup_ff FF LK ND2).
Qed.
Lemma own_back : forall LB FF LK cr A M V b n, ri_inv HI ((b, n) :: lb_remove b LB) FF LK cr A M V -> In (b, n) LB -> base.NoDup (map fst LB) -> ri_inv HI LB FF LK cr A M V.
Proof.
  intros LB FF LK cr A M V b n HH Hin ND1. destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as [_ ND2].
  apply (PmHeapIfaceA.aio_perm _ _ _ _ _ HIok _ LB FF FF LK cr A M V HH); [| exact ND1 | intros f; split; intros X; exact X | exact (nodup_ff FF LK ND2)].
  intros x. split.
  - intros [<-|Hx]; [exact Hin | exact (L5C.in_lb_remove b x LB Hx)].
  - intros Hx. destruct (Z.eq_dec (fst x) b) as [e|ne].
    + left. apply (CH2.nodup_fst_eq LB (b, n) x ND1 Hin Hx). symmetry. exact e.
    + right. destruct x as [B m]. exact (L5C.in_lb_remove_neq b B m LB Hx ne).
Qed.

Lemma callee_leaf : forall pc scr ng BLk wregs news a0x dc i c ps j cj ci,
  nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI scr ng BLk (nth i FFS []) wregs news a0x c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = pc ->
  CHA.frames_eqb (nth j FFS []) (nth i FFS []) = true ->
  dc <= D0 - Z.of_nat (length (nth i FFS [])) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall cr LK,
       CFACTS scr ng c ps cj ci i E E' R' A M1 model1 ->
       ri_inv HI (curB i E) (curF i E) LK cr A M1 (vml_of model1) -> incl LK LK0 -> Cred i E cr ->
       exists (Pre : bvmap 5 word -> mem -> Prop)
              (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
       cps_asanG L ar HI FPI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr (curB i E) (curF i E) LK cr A dc Pre Post
       /\ Pre R' M1
       /\ forall R2 M2 model2 LB' cr' LBk Wc LK2 A2,
            Post R' M1 R2 M2 LB' cr' LBk Wc -> regs_preserved R' R2 ->
            CHA.ahpres L ar LBk (curF i E) (sp0 + CH2.ci_csp ci) scr Wc M1 M2 ->
            model_rt model1 model2 -> incl A A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK ->
            ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) ->
            exists ghosts, length ghosts = ng /\
              let E2 := CH2.retEx E' (CH2.ci_nx ci) ghosts R2 in
              match a0x with Some e => getr R2 10%bv = edenot E2 e | None => True end /\
              incl (CH2.den E' BLk ++ LBrest) LBk /\
              (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs /\ CHA.in_reg E' r a) /\
              (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LBrest FFrest sp0 SCR W a) /\
              ri_inv HI (curB j E2) (curF i E) LK2 cr' A2 M2 (vml_of model2) /\ Cred j E2 cr' /\ XI j E2 A2 M2 model2 /\
              (forall X, In X news -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros pc scr ng BLk wregs news a0x dc i c ps j cj ci Hcj Hchk Hpc Hfeq Hdc fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH USER.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI scr ng BLk (nth i FFS []) wregs news a0x i c ps j cj ci Hcj Hchk
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  destruct (USER cr LK CF HH1 HLK1 HC1) as (Pre & Post & SPEC & HPre & HPost).
  apply CHA.frames_eqb_eq in Hfeq.

  assert (FV : CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d scr ng c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z5]. exact Z5. }
  rewrite Hpc.
  apply (SPEC fx' R' M1 model1 K HH1 Hmo1 KNIL HFP Hra Hraok Hsp Htp Hstk); [apply (CHA.ffroom_le _ _ _ _ HRoom1); exact Hdc | exact Hffrs | exact HPre |].
  intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2) as (ghosts & Hlen & Ha0 & HiB & HWr & HWk & HHj & HCj & HXj & Hnews).
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) ghosts R2) in *.
  pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) ghosts R2 : env_agree (CH2.ci_nx ci) E' E2) as Hag2.
  assert (HFj : curF j E2 = curF i E).
  { unfold CHA.curF. rewrite Hfeq. rewrite (CHA.denF_agree sp0 _ E' E2 _ Hag2 FV). rewrite HdenF. reflexivity. }
  assert (HagEE2 : env_agree NF E E2).
  { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
  apply (CONT fx2 R2 A2 M2 model2 ghosts LBk (curF i E) Wc Hlen HFP2 (CH2.regs_preserved_kept R' R2 HRP) Ha0 HP HiB).
  - unfold CHA.curF. rewrite HdenF. apply incl_refl.
  - exact HWr.
  - split; [|exact HXj].
    apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j E E2 A A2 M1 M2 model1 model2
             (CH2.ci_csp ci) scr LBk (curF i E) Wc cr' LK2 HA' HP).
    + intros b Hb. apply HiB. apply in_or_app. right. exact Hb.
    + unfold CHA.curF. apply incl_appr, incl_refl.
    + exact Hc1.
    + exact Hs0.
    + exact Hc2.
    + exact HWk.
    + exact Hrt2.
    + exact Hmo2.
    + exact HA2.
    + rewrite HFj. exact HHj.
    + exact (incl_tran HLK2 HLK1).
    + exact HagEE2.
    + exact HCj.
    + rewrite HFj, Hfeq.
      pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHj)) as [_ ND].
      exact (CHA.ffroom_sub NF 0 NF32 _ _ _ _ HRoom1 HLK2 ND).
  - exact Hnews.
Qed.

Variable R0 : bvmap 5 word.
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.

Definition exit_base_chk (retpc : Z) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  (Z.eqb (SR.ps_pc ps) retpc && CL.ps_keeps ps CL5.CSAVED && Nat.leb NF (CC.cp_nx c))%bool.

Lemma exit_post : forall i E A M1 model1 cr LK (FFx : list fframe),
  CHA.amodel_ok A model1 -> model_rt model0 model1 -> incl A0 A ->
  (forall a, CHA.akept L ar LBrest FFrest sp0 SCR W a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBrest FFrest sp0 0 a -> M0 (Z_to_bv 64 a) <> None -> M1 (Z_to_bv 64 a) <> None) ->
  ri_inv HI (curB i E) FFx LK cr A M1 (vml_of model1) ->
  CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1.
Proof.
  intros i E A M1 model1 cr LK FFx Hmo Hrt HA0 Hfr Hdf HH.
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _). destruct STK as (S1 & S2 & S3).
  split; [exact Hfr|]. split.
  - intros k Hk. apply (Hdf (sp0 - SCR + k)); [lia | right; left; split; lia | apply DEF0; exact Hk].
  - intros a Ha Hc Hd. apply (Hdf a Ha); [|exact Hd]. eapply CHA.aclient_scr; [exact Hc | intros x Hx; lia].
Qed.

Lemma exit_ret : forall retpc i c ps,
  CL.is_ret_at (hl_segs L) retpc -> exit_base_chk retpc c ps = true ->
  CHA.foot_chk NF d c (nth i BLS []) (nth i FFS []) = true -> nth i FFS [] = [] ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    (forall model2 cr LK,
        regs_preserved R0 R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> model_rt model0 model2 -> incl A0 A -> CHA.amodel_ok A model2 -> incl LK LK0 ->
        ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model2) -> Cred i E cr -> env_agree NF E0 E' -> AAMB i E A M1 model1 ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0) M1 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros retpc i c ps Hret Hchk Hfoot HFi fx' E R A M model E' R' M1 model1 HAt HA Hag HLF Hcont.
  unfold exit_base_chk in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [C1 C2]. apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  pose proof (CHA.leaf_amb L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
                i c ps E E' R R' A M model M1 model1 Hfoot HAt HA Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  pose proof (leaf_agree0 i c E E' A M model HA C3 Hag) as HagE'.
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R0 x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat).
    { apply (Nat.lt_le_trans _ 32); [|exact NF32]. unfold CL5.CSAVED in Hx. cbn [In] in Hx. clear - Hx.
      repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply Nat.ltb_lt; reflexivity|]). destruct Hx. }
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' _ _ CL5.CSAVED NF x (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) C2 HagE' Hx Hx32). exact (EV0 x). }
  assert (HRP : regs_preserved R0 R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0).
  assert (HFx : curF i E = FFrest) by (unfold CHA.curF; rewrite HFi; reflexivity).
  rewrite HFx in HH1.
  pose proof (exit_post i E A M1 model1 cr LK FFrest Hmo1 Hrt1 HA01 Hfr1 Hdf1 HH1) as HP.
  destruct (CHA.aamb_model L ar C HI HIok LY_below NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i E A M1 model1 HA') as (Hh & HMI & HAwf & Hoff).
  rewrite C1. eapply (CCA.ret_cps (hl_segs L) fx' R' retpc M1 model1 A K Hret Hh HMI HAwf Hoff LY_nowrap).
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct RA0ok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  intros model2 HMI2 HS. rewrite Hra'.
  assert (VML : vml_of model2 = vml_of model1) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  apply (Hcont model2 cr LK HRP HP); [exact (L5LZ.model_rt_trans _ _ _ Hrt1 (L5LZ.sbm_model_rt _ _ HS)) | exact HA01 | | exact HLK1 | rewrite VML; exact HH1 | exact HC1 | exact HagE' | exact HA'].
  split; [rewrite (L5LZ.sbm_halted _ _ HS); exact (proj1 Hmo1) | exact HMI2].
Qed.

End Inst.
End CBA.
