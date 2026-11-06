(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitA EncBridgesA EncHtransA EncStransA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VDK.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Lemma kword16_intro : forall segs E (M : mem) a v A z0 z1, estart E a = A -> 0 <= A -> A + 2 <= 2 ^ 64 -> 0 <= z0 < 256 -> 0 <= z1 < 256 ->
  edenot E v = Z_to_bv 64 (z0 + 256 * z1) -> L5.u8_at segs M A z0 -> L5.u8_at segs M (A + 1) z1 -> kentry_ok segs E M (KWord a 2 v).
Proof.
  intros segs E M a v A z0 z1 Ha H0 H1 R0 R1 Hv Hu0 Hu1. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 2)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv.
  unfold L5.u8_at in Hu0, Hu1.
  cbn [rdn] in Hu0, Hu1 |- *. rewrite (L5C.add1_lit A).
  destruct (match M (Z_to_bv 64 A) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 A) end) as [b0|]; [|discriminate].
  destruct (match M (Z_to_bv 64 (A + 1)) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 (A + 1)) end) as [b1|]; [|discriminate].
  injection Hu0 as ->. injection Hu1 as ->. f_equal. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite u64_of_Z by lia.
  f_equal; [apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; replace (z0 + 256 * z1) with (z0 + z1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity|].
  f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.mul_comm, Z.div_add by lia. rewrite (Z.div_small z0 256) by lia. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma custom_chk_nx : forall NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci,
  CHA.custom_chk NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj = Some ci ->
  CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - ng)%nat.
Proof.
  intros NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci H. unfold CHA.custom_chk in H.
  destruct (CHA.common_chk NF d scr ng c ps cj BLi FLi) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection H as <-.
  unfold CHA.common_chk in Hc.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |]; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp]. destruct spb as [|v| | | | | |]; try discriminate.
  destruct v as [|[|[|v]]]; cbv beta iota in Hc; try discriminate.
  lazymatch type of Hc with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection Hc as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma custom_chk_nx_le : forall NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci,
  CHA.custom_chk NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj = Some ci ->
  (CC.cp_nx c <= CH2.ci_nx ci)%nat.
Proof.
  intros NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci H. pose proof (custom_chk_nx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as E. rewrite E.
  unfold CHA.custom_chk in H.
  destruct (CHA.common_chk NF d scr ng c ps cj BLi FLi) as [ci0|] eqn:Hc; [|discriminate]. clear H.
  unfold CHA.common_chk in Hc.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |]; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp]. destruct spb as [|v| | | | | |]; try discriminate.
  destruct v as [|[|[|v]]]; cbv beta iota in Hc; try discriminate.
  lazymatch type of Hc with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb _]. do 14 (apply andb_prop in Hb as [Hb _]). apply andb_prop in Hb as [Hb X]. apply Nat.leb_le in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma custom_chk_csp : forall NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci,
  CHA.custom_chk NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj = Some ci ->
  CH2.ci_csp ci <= 0 /\ - CH.hd_scr d <= CH2.ci_csp ci - scr.
Proof.
  intros NF d SC GLO GHI scr ng BLk FLk wregs news a0x c ps cj BLi FLi BLj FLj ci H. unfold CHA.custom_chk in H.
  destruct (CHA.common_chk NF d scr ng c ps cj BLi FLi) as [ci0|] eqn:Hc; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b; [|discriminate] end. injection H as <-.
  unfold CHA.common_chk in Hc.
  destruct (nth 1 (CA.ps_reglist ps) (ELit 0)) as [ra| | | | | | |]; try discriminate.
  destruct (split_lit (nth 2 (CA.ps_reglist ps) (ELit 0))) as [spb csp]. destruct spb as [|v| | | | | |]; try discriminate.
  destruct v as [|[|[|v]]]; cbv beta iota in Hc; try discriminate.
  lazymatch type of Hc with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hc as <-. cbn [CH2.ci_csp].
  apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb X18]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb X16].
  apply Z.leb_le in X16, X18. split; [exact X16 | exact X18].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Variable IMGHI : Z.                      (* [comment removed for export] *)
Hypothesis LY_imghi : IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES.
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

Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).
Abbreviation curB := (CHA.curB LBrest BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).


Lemma smalloc_leaf_u2 : forall (UN : kentry -> Prop) k news i c ps j cj ci,
  In k PM_FS_CLASSES -> nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI (hl_scr_stack_malloc L) 1 (nth i BLS []) (nth i FFS []) [] news None c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = hl_stack_malloc L k ->
  CHA.frames_eqb (nth j FFS []) ((EVar (CH2.ci_nx ci + 5), k, CH2.ci_csp ci) :: nth i FFS []) = true ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  (forall X, In X news -> (CHA.static_chk SCELLS GLO GHI X || CRA.smalloc_fact_ok IMGHI d (SR.ps_cells ps) (CH2.ci_nx ci) (nth i BLS []) (nth i FFS []) k (CH2.ci_nx ci + 5) (CH2.ci_nx ci) X)%bool = true \/ UN X) ->
  2 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall R2 M2 model2 F fl LK' cr, regs_preserved R' R2 -> getr R2 10%bv = Z_to_bv 64 F ->
        CRA.sm_facts L ar k (curB i E) (curF i E) LK' (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) M1 M2 F fl ->
        ri_inv HI (curB i E) ((F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E) LK' cr A M2 (vml_of model2) ->
        XI j (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 fl] R2) A M2 model2 /\
        (forall X, UN X -> In X news -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 fl] R2) (CCA.vis A model2 M2) X)) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros UN k news i c ps j cj ci Hk Hcj Hchk Hpc Hfeq Hbeq Hnews Hroom HCred fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH HXI.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI (hl_scr_stack_malloc L) 1%nat (nth i BLS []) (nth i FFS []) [] news None i c ps j cj ci Hcj Hchk
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  apply CHA.frames_eqb_eq in Hfeq. apply CH2.blocks_eqb_eq in Hbeq.
  assert (CHK2 : CH2.blocks_vars_lt (CH2.ci_nx ci) (nth i BLS []) = true /\ CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d (hl_scr_stack_malloc L) 1 c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Z5].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z2]. split; assumption. }
  destruct CHK2 as [BV FV].
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1)) as RF1.
  destruct (CHA.rf_ceil _ _ _ _ RF1) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RF1) as (SP1 & _). pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (USP : bv_unsigned (getr R' 2%bv) = sp0 + CH2.ci_csp ci) by (rewrite Hsp; apply u64_of_Z; lia).
  rewrite Hpc.
  apply (PmHeapIfaceA.aio_stack_malloc _ _ _ _ _ HIok k Hk fx' R' M1 model1 (curB i E) (curF i E) LK cr A K HH1 (proj1 Hmo1) (proj2 Hmo1) Htp).
  - rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'.
  - rewrite USP. split; [exact K1|]. split; [lia|]. split; [lia|]. split; [exact K4|]. split; [|exact K6].
    intros dd m Hdd Hm. exact (L5C.writable_of_defined (hl_segs L) M1 _ _ K5 ltac:(lia) ltac:(lia) dd m Hdd Hm).
  - unfold ff_room. specialize (HRoom1 k Hk). lia.
  - rewrite USP. exact Hffrs.
  - exact KNIL.
  - rewrite USP. intros R2 M2 model2 F fl LK' Ha0 HRP Q1 Q2 Q3 Q4 HLK' Q5 Q6 Q7 Q8 Q9 Qst Q10 HPres Hrt2 HMI2 HH2. rewrite Hra.
    assert (Hmo2 : CHA.amodel_ok A model2) by (split; [rewrite (L5LZ.model_rt_halted _ _ Hrt2); exact (proj1 Hmo1) | exact HMI2]).
    set (nx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' nx [Z_to_bv 64 fl] R2).
    pose proof (CH2.retEx_agree E' nx [Z_to_bv 64 fl] R2 : env_agree nx E' E2) as Hag2.
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    assert (FR : 0 <= F < 2 ^ 64) by (destruct Q1 as (G1 & G2 & _ & (G0 & _) & G5); pose proof (CHA.frame_class_facts k Hk); lia).
    assert (HvF : CL5A.uv E2 (EVar (nx + 5)) = F).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' nx [Z_to_bv 64 fl] R2) as G. cbn [length] in G. replace (nx + 1 + 4)%nat with (nx + 5)%nat in G by lia.
      unfold E2. rewrite G, Ha0. apply u64_of_Z. exact FR. }
    assert (Hvfl : CL5A.uv E2 (EVar nx) = fl).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 fl] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. cbn [nth] in G.
      unfold E2. rewrite G. apply u64_of_Z. destruct (CHA.rf_fs _ _ _ _ RF1) as ((G0 & _) & G3 & _). unfold FS_BYTES in *. lia. }
    assert (HBj : curB j E2 = curB i E).
    { unfold CHA.curB. rewrite Hbeq. rewrite (CH2.den_agree nx E' E2 _ Hag2 BV), HdenB. reflexivity. }
    assert (HFj : curF j E2 = (F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E).
    { unfold CHA.curF. rewrite Hfeq. unfold CHA.denF at 1. cbn [map fst snd app]. fold (CHA.denF sp0 E2 (nth i FFS [])).
      unfold CL5A.uv in HvF. rewrite HvF. rewrite (CHA.denF_agree sp0 nx E' E2 _ Hag2 FV), HdenF. reflexivity. }
    apply (CONT fx' R2 A M2 model2 [Z_to_bv 64 fl] (curB i E) (curF i E) [] eq_refl HFP (CH2.regs_preserved_kept R' R2 HRP) I (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
    + unfold CHA.curB. rewrite HdenB. apply incl_refl.
    + unfold CHA.curF. rewrite HdenF. apply incl_refl.
    + intros w a [].
    + split.
      * apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j E E2 A A M1 M2 model1 model2
                 (CH2.ci_csp ci) (hl_scr_stack_malloc L) (curB i E) (curF i E) [] cr LK' HA' (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
        -- unfold CHA.curB. apply incl_appr, incl_refl.
        -- unfold CHA.curF. apply incl_appr, incl_refl.
        -- exact Hc1.
        -- exact Hs0.
        -- exact Hc2.
        -- intros w a [].
        -- exact Hrt2.
        -- exact Hmo2.
        -- apply incl_refl.
        -- rewrite HBj, HFj. exact HH2.
        -- exact (incl_tran HLK' HLK1).
        -- exact HagEE2.
        -- exact (HCred E E2 cr HC1 HagEE2).
        -- rewrite HFj, Hfeq. cbn [length]. pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) as [_ ND].
           pose proof (CHA.ffroom_push NF 0 NF32 _ _ _ (F, k, sp0 + CH2.ci_csp ci + 32) _ HRoom1 HLK' ND) as G.
           replace (D0 - Z.of_nat (Datatypes.S (length (nth i FFS [])))) with (D0 - Z.of_nat (length (nth i FFS [])) - 1) by lia. exact G.
      * apply (proj1 (HXI R2 M2 model2 F fl LK' cr HRP Ha0 ltac:(constructor; assumption) HH2)).
    + assert (SMF : CRA.sm_facts L ar k (curB i E) (curF i E) LK' (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) M1 M2 F fl) by (constructor; assumption).
      intros X HXn _. destruct (Hnews X HXn) as [Hnews'|Hu]; [|exact (proj2 (HXI R2 M2 model2 F fl LK' cr HRP Ha0 SMF HH2) X Hu HXn)]. apply orb_prop in Hnews' as [Hs|Hs].
      * exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 Hs).
      * apply (CRA.smalloc_fact_sound L ar C HI HIok LY_img IMGHI LY_imghi NF E0 LBrest FFrest sp0 d Wo STK SCR_pos NF32 SP0 Wo_ok CRS_ok WRS_ok E' E2 nx (SR.ps_cells ps) (nth i BLS []) (nth i FFS []) k (nx + 5)%nat nx M1 M2 A A model1 model2 (curB i E) (curF i E) LK LK' cr F fl (sp0 + CH2.ci_csp ci + 32)
                 HagE' Hag2 HK HH1); try assumption.
        -- unfold CHA.curB. rewrite HdenB. reflexivity.
        -- unfold CHA.curF. rewrite HdenF. reflexivity.
Qed.


(* [comment removed for export] *)
Variable R0 : bvmap 5 word.            (* [comment removed for export] *)
Variable ra0 : Z.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis RA0 : getr R0 1%bv = Z_to_bv 64 ra0.
Hypothesis RA0ok : L5.ra_ok ra0.
Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Lemma exit_retire2 : forall retpc i c ps fle Fe k c0,
  CL.is_ret_at (hl_segs L) retpc -> CBA.exit_base_chk NF retpc c ps = true ->
  nth i FFS [] = [(Fe, k, c0)] -> CHA.retire_chk NF d c (nth i BLS []) (nth i FFS []) = Some fle ->
  CC.has_cell (SR.ps_cells ps) (KWord (SA fle 0) 1 (ELit 0)) = true ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AAMB i E A M model -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 ->
    ar_fs ar <= CL5A.uv E fle < ar_fs ar + FS_BYTES -> ~ aclient L ar LBrest FFrest sp0 SCR (CL5A.uv E fle) ->
    (forall model2 cr LK,
        regs_preserved R0 R' -> CHA.ahpres L ar LBrest FFrest sp0 SCR W M0 M1 -> model_rt model0 model2 -> incl A0 A -> CHA.amodel_ok A model2 -> incl LK LK0 ->
        ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model2) -> Cred i E cr -> env_agree NF E0 E' ->
        H_off_segments (hl_segs L) (ahid A model1) -> ri_inv HI (curB i E) FFrest LK cr A M1 (vml_of model1) ->
        srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 ra0) M1 (seg_rom (hl_segs L))) model2) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros retpc i c ps fle Fe k c0 Hret Hchk HFi Hrchk Hcell fx' E R A M model E' R' M1 model1 HAt HA Hag HLF Hflr Hflnc Hcont.
  unfold CBA.exit_base_chk in Hchk. apply andb_prop in Hchk as [Hchk C3]. apply andb_prop in Hchk as [C1 C2]. apply Z.eqb_eq in C1. apply Nat.leb_le in C3.
  apply CC.has_cell_In in Hcell.
  destruct (CHA.retire_exit L ar C HI HIok LY_img NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 Wo_incl Wo_ok WRS_ok
              i c ps fle Fe k c0 E E' R R' A M model M1 model1 HFi Hrchk HAt HA Hag HLF Hcell Hflr Hflnc) as (Hmo1 & Hrt1 & HA01 & (cr & LK & HH1 & HLK1 & HC1) & Hfr1 & Hdf1).
  pose proof (CBA.leaf_agree0 L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 i c E E' A M model HA C3 Hag) as HagE'.
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R0 x).
  { intros x Hx. assert (Hx32 : (ridx x < NF)%nat).
    { apply (Nat.lt_le_trans _ 32); [|exact NF32]. unfold CL5.CSAVED in Hx. cbn [In] in Hx. clear - Hx.
      repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; apply Nat.ltb_lt; reflexivity|]). destruct Hx. }
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps E0 E' R' _ _ CL5.CSAVED NF x (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) C2 HagE' Hx Hx32). exact (EV0 x). }
  assert (HRP : regs_preserved R0 R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  assert (Hra' : getr R' 1%bv = Z_to_bv 64 ra0) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact RA0).
  pose proof (CBA.exit_post L ar C HI HIok NF M0 model0 A0 LBrest FFrest sp0 d W BLS STK NF32 DEF0 i E A M1 model1 cr LK FFrest Hmo1 Hrt1 HA01 Hfr1 Hdf1 HH1) as HP.
  assert (Hoff : H_off_segments (hl_segs L) (ahid A model1)) by exact (CHA.vis_off_segments L ar C HI HIok LY_below _ _ _ _ _ _ model1 HH1).
  rewrite C1. eapply (CCA.ret_cps (hl_segs L) fx' R' retpc M1 model1 A K Hret (proj1 Hmo1) (proj2 Hmo1) (proj1 (PmHeapIfaceA.aio_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1)) Hoff LY_nowrap).
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct RA0ok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  intros model2 HMI2 HS. rewrite Hra'.
  assert (VML : vml_of model2 = vml_of model1) by (unfold vml_of; rewrite (L5LZ.sbm_vmmaps _ _ HS), (L5LZ.sbm_lazy _ _ HS); reflexivity).
  apply (Hcont model2 cr LK HRP HP); [exact (L5LZ.model_rt_trans _ _ _ Hrt1 (L5LZ.sbm_model_rt _ _ HS)) | exact HA01 | | exact HLK1 | rewrite VML; exact HH1 | exact HC1 | exact HagE' | exact Hoff | exact HH1].
  split; [rewrite (L5LZ.sbm_halted _ _ HS); exact (proj1 Hmo1) | exact HMI2].
Qed.

End Inst.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section InstB.
Import PMES.
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
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Variable CL : Z.                    (* [comment removed for export] *)
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBo : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable D0 : Z.
(* [comment removed for export] *)
Variable GR : list (Z * Z).
Abbreviation gB := (EBA.gB GR).
Variable kx bx : Z.
Abbreviation CredV := (EBA.CredV L CL kx bx).
Variable XIv : eghost -> nat -> env -> list (Z * Z) -> mem -> Model -> Prop.

Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis SCR8 : SCR mod 8 = 0.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBo FFrest sp0 SCR a
                                                       /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBo FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M00 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
(* [comment removed for export] *)
Variable STAT : list kentry.
Hypothesis STAT_ok : forallb (CHA.static_chk SCELLS GLO GHI) STAT = true.
(* [comment removed for export] *)
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis OBJS0 : PMESA.objs_encA M00 FFrest V S2.
Hypothesis STKSH0 : PMSA.stksh ar M00 sp0 SCR.
Hypothesis IMG0 : PMLA.img_ro IC M00.
Hypothesis IMG_RO_ok : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Hypothesis W_S2 : In (S2, 24) W.
(* [comment removed for export] *)
Hypothesis W_app : forall w a, In w W -> L5.in_rng w a -> ~ (BIGSHADOW_LO <= a < BIGSHADOW_HI) /\ ~ (PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
(* [comment removed for export] *)
Variable OB : expr.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : bv_unsigned (edenot E0 OB) = S2.

Abbreviation FPI := PMSA.fp_ok.
Abbreviation OKV := (CHV.okV L ar M00 LBo FFrest sp0 d W).
Abbreviation AAMBV := (CHV.aambV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV).
Abbreviation AMBXV := (CHV.ambXV L ar HI NF E0 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation AMBV := (CHV.ambV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv).
Abbreviation LEAFOKV := (CHV.leaf_okV L ar HI NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 eghost gB CredV XIv CPS K FPI).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).
Abbreviation curB := (CHA.curB BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).

(* [comment removed for export] *)

(* [comment removed for export] *)
Variable ERRNO : Z.
Hypothesis ERRNO_tp : ERRNO = hl_tp L - 164.
Hypothesis W_ERR : In (hl_tp L - 164, 4) W.

(* [comment removed for export] *)
Definition wd_chk (scr : Z) (unews : list kentry) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi : CA.blocks) (FFi : list (expr * Z * Z))
  (BLj : CA.blocks) (FFj : list (expr * Z * Z)) : option CH2.cinfo :=
  if (CH2.blocks_eqb BLj BLi && CHA.frames_eqb FFj FFi)%bool
  then CHA.custom_chk NF d SCELLS GLO GHI scr 0 BLi FFi [(OB, 0, ELit 24); (ELit 0, ERRNO, ELit 4)] (STAT ++ unews) (Some (ELit 0)) c ps cj BLi FFi BLj FFj
  else None.

Lemma wd_leaf_okV : forall (pc scr dc : Z) unews i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  wd_chk scr unews c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  CH2.blocks_vars_lt NF (nth i BLS []) = true ->
  dc <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (* [comment removed for export] *)
  (forall E R A (M : mem) model E' R' (M' : mem) model' cr LK, CCA.AtV (hl_segs L) c E R A M model -> AAMBV g M0c i E A M model -> XIv g i E A M model ->
     env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M' model' ->
     CHA.common_facts L ar HI NF E0 M0c model0 A0 (CHV.LBr LBo eghost gB g) FFrest LK0 sp0 d W BLS FFS (CredV g) D0 scr 0 c ps cj ci i E E' R' A M' model' ->
     ri_inv HI ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g)) (curF i E) LK cr A M' (vml_of model') -> incl LK LK0 -> PMESA.ecreditA L CL cr g kx bx ->
     shadow_zero M' V 51 -> shadow_zero M' S2 3 -> PMSA.stksh ar M' sp0 SCR -> PMLA.img_ro IC M' ->
     exists (Pre : bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
       PMSA.cps_asan L ar HI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) scr ((CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g)) (curF i E) LK cr A dc Pre Post /\ Pre R' M' /\
       forall R2 (M2 : mem) model2 LB' cr' LBk Wc LK2 A2, Post R' M' R2 M2 LB' cr' LBk Wc -> regs_preserved R' R2 ->
         CHA.ahpres L ar LBk (curF i E) (sp0 + CH2.ci_csp ci) scr Wc M' M2 -> model_rt model' model2 -> incl A A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK ->
         ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) ->
         exists (g' : eghost), let E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2 in
           g_sb g' = g_sb g /\ g_scap g' = g_scap g /\ LB' = (CH2.den E' (nth i BLS []) ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g') /\ LBk = CH2.den E' (nth i BLS []) ++ LBo ++ GR /\
           Wc = [(S2, 24); (hl_tp L - 164, 4)] /\ getr R2 10%bv = Z_to_bv 64 0 /\ PMESA.ecreditA L CL cr' g' kx bx /\
           XIv g' j E2 A2 M2 model2 /\ (forall X, In X unews -> In X (CC.cp_know cj) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X)) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc scr dc unews i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk BVN Hdc CALL.
  intros fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  unfold wd_chk in Hchk.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [B3 B4]. apply CH2.blocks_eqb_eq in B3.
  set (BLi := nth i BLS []) in *. set (FFi := nth i FFS []) in *.
  apply (CHV.callee_leafV L ar C HI HIok LY_img LY_ro NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W Wo BLS FFS D0 eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0 CRS_ok WRS_ok IMG_ok
           CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok K_nil g M0c pc scr 0%nat BLi [(OB, 0, ELit 24); (ELit 0, ERRNO, ELit 4)] _ (Some (ELit 0)) dc i c ps j cj ci HOKV Hcj Hchk Hpc B4 Hdc
           fx' E R A M model E' R' M1 model1 HAt HAX HFP Hag HLF HIH).
  intros cr LK CF HH1 HLK1 HC1.
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  destruct (EBA.amb_env L ar C HI HIok LY_img IC CL NF E0 M00 model0 A0 LBo FFrest LK0 sp0 d W BLS FFS D0 GR kx bx STK SCR_pos SCR8 NF32 V S2 OBJS0 STKSH0 IMG0 IMG_RO_ok W_app g M0c i E A M1 model1 HOKV HA')
    as (ZV & ZS & ZSTK & ZIMG).
  set (own := CH2.den E' BLi) in *. fold BLi in HdenB. fold FFi in HdenF.
  assert (HcB : CHA.curB (CHV.LBr LBo eghost gB g) BLS i E = own ++ LBo ++ PML.srep_blocks (g_rep g) ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB, own. fold BLi. rewrite <- HdenB. reflexivity. }
  rewrite HcB in HH1.
  (* [comment removed for export] *)
  assert (PERMG : forall g1, Permutation (own ++ LBo ++ PML.srep_blocks (g_rep g1) ++ GR) ((own ++ LBo ++ GR) ++ PML.srep_blocks (g_rep g1))).
  { intros g1. rewrite <- (app_assoc own (LBo ++ GR) _). apply Permutation_app_head. rewrite <- (app_assoc LBo GR _). apply Permutation_app_head. apply Permutation_app_comm. }
  pose proof (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH1 (PERMG g)) as HH1'.
  destruct (CALL E R A M model E' R' M1 model1 cr LK HAt HA HXI Hag HLF CF HH1' HLK1 HC1 ZV ZS ZSTK ZIMG) as (Pre & Post & SPEC & HPre & HPost).
  exists Pre, Post. split; [rewrite HcB; exact (EHTA.cps_perm L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ _ _ (PERMG g) SPEC)|]. split; [exact HPre|].
  intros R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2) as (g' & Gsb & Gscap & -> & -> & -> & Ha0 & HC' & HXI2 & Hunews).
  exists [], g'. split; [reflexivity|]. cbv zeta.
  set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
  assert (Hag2 : env_agree (CH2.ci_nx ci) E' E2) by apply CH2.retEx_agree.
  assert (Ho : estart E' (SA OB 0) = S2).
  { unfold estart. cbn [a_base a_off]. rewrite <- (SR.edenot_agree_AP NF E0 E' OB HagE' OB_frozen). rewrite OADDR. lia. }
  split; [cbn [edenot]; exact Ha0|].
  split; [intros bb Hb; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb | right; apply in_or_app; left; exact Hb]|].
  split.
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    - exists (OB, 0, ELit 24). split; [left; reflexivity|]. unfold CHA.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    - exists (ELit 0, ERRNO, ELit 4). split; [right; left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_of_Z by lia. rewrite ERRNO_tp. lia. }
  split.
  { intros w a [<-|[<-|[]]] Hin (_ & _ & Hout); [exact (Hout (S2, 24) W_S2 Hin) | exact (Hout (hl_tp L - 164, 4) W_ERR Hin)]. }
  assert (Hcur : CHA.curB (CHV.LBr LBo eghost gB g') BLS j E2 = own ++ LBo ++ PML.srep_blocks (g_rep g') ++ GR).
  { unfold CHA.curB, CHV.LBr, EBA.gB. rewrite B3. unfold own. rewrite (CH2.den_agree NF E' E2 BLi ltac:(eapply CC.env_agree_le; [exact Hag2 | lia]) BVN). reflexivity. }
  split; [rewrite Hcur; exact (CHV.ri_perm L ar C HI HIok _ _ _ _ _ _ _ _ HH2 (Permutation_sym (PERMG g')))|].
  split; [exact HC'|].
  split; [exact HXI2|].
  intros X HX HXc.
  apply in_app_or in HX as [HX|HX]; [|exact (Hunews X HX HXc)].
  rewrite forallb_forall in STAT_ok. exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 (STAT_ok X HX)).
Qed.

End InstB.
End VDK.
