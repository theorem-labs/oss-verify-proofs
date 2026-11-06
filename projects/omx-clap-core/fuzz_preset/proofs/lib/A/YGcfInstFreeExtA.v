(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstFreeExtA.v (commit eb934de95d13, blob b69c51657fb8) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); reply's depot_fits_incl_TfibB is false at preset (wild prefixes); the depot_fits hypothesis is passed through. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YF0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfBatch YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD2l CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR YGcfInstDrainX YGcfInstDrainQ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot YGcfInstDepot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDepotWpreset YGcfInstF1Wpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstCdealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_depkeep PresetImg_depfp PresetImg_dhash PresetImg_sbconst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_qapart CfInstImgA PresetImg_constapart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh YGcfInstFree YGcfInstFreeMidE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstEnqMisspreset YGcfRefillToppreset RepArmTcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstFreeImgpreset PresetImg_fvzones PresetImg_errbapart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetPfApartA PresetRelroGeoA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcCf DMrcSecCf DMcdF YGcfInstCdReads.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehideAR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m PresetImg_fqconst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFreeQ YGcfInstFreeModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainTopRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFA DMwalkIFRhA DMrcReadsA DMrcFhCf DMrcPrim DMrcRhOkA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstRcPrim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainDq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf YG06bcf YGcfRoomCf YGcfCker.
From Stdlib Require Import List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfAroPresetA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ADIfaceA.
Import ListNotations.
Local Open Scope Z_scope.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

Variable NMAXD : Z.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.
Variable Hp : list Z.
Local Notation B := TfibB.
Local Notation ARX := (ARX_cf TfibB IOK Hp).
Local Notation ARXr := (ARXr_cf TfibB IOK Hp).
Local Notation U := (U_cf TfibB).
Local Notation AOX := (aowned TfibB).
Local Notation dpost := (CLdepot.dpost_x im_segs TfibB).
Local Notation DRq := (DRq_cf TfibB NMAXD).

Lemma DRq_cf_mono : forall N1 N2, N1 <= N2 -> forall S its zs, DRq_cf TfibB N1 S its zs -> DRq_cf TfibB N2 S its zs.
Proof.
intros N1 N2 HN S its zs (RX & CD & UQ & Q1 & Q2 & SZ & PB & CI & HHO).
refine (conj RX (conj CD (conj UQ (conj Q1 (conj Q2 (conj _ (conj PB (conj CI HHO)))))))).
eapply Forall_impl; [| exact SZ]. intros k Hk. cbv beta in Hk |- *. lia.
Qed.

Lemma dep_keep_d_preset_A :
  YGcfInstDepot.dep_keep_img TfibB (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)).
Proof.
intros ly S W mem0 mem LY IMG TSD HDF CST DEP MEQ.
exact (PresetImg_depkeep.dep_keep_d_A TfibB TfibB_syms ly S W mem0 mem LY IMG TSD HDF CST DEP MEQ).
Qed.

Lemma exr_depot_preset_A :
  forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, dg_dzone ly (bv_unsigned x) \/ (dg_czone ly (bv_unsigned x) /\ ~ dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 dg_depot) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ dg_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly S W tr z mem').
Proof.
exact (YGcfInstDepot.di_depot_cf TfibB Hp ARX (ARX_cf_ARcf TfibB IOK Hp)
  YGcfInstF1Wpreset.IMG_COVER_preset dep_keep_d_preset_A (PresetImg_depfp.dep_fp_d_A TfibB TfibB_syms)
  (YGcfInstDepotWpreset.depot_spec_d_preset TfibB TfibB_syms PresetImg_dhash.dhash_img_A)).
Qed.

Lemma exr_dpost_aok_preset_A : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z.
Proof. exact (YGcfInstDepot.dpost_aok_cf TfibB). Qed.

Lemma exr_requar_e_preset_A : di_requar_e_t ARX ARXr DRq.
Proof.
intros inst ly S W mem md HR HD. exact (proj1 (ARX_cf_of_ARXr_end TfibB IOK Hp inst ly S W mem md NMAXD HR HD)).
Qed.

Lemma cr_budget_x_n : DMcdR.rd_budget_x TfibB ARXr DRq.
Proof.
intros inst ly X z W regs mem md (H & _) its zs D _.
destruct H as (_ & (M & L & (HA & _) & _) & _).
destruct D as (_ & _ & HU & HT & HG & _ & HN & _ & HHO).
pose proof (YGcfRoomCf.qloose_cut_of_pending X its HU HT HG HN) as QL.
pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (YGcfRoomCf.room_rec_cf_of_cut _ ly X md WF QL HHO) as R.
replace (eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768)
  with (eager_used md + A_bytes (w_A W) + (2 * kUserMapSize + 32768)) by lia.
apply (YGcfCker.room_wA_parts_R _ _ ly X md W _ WF L HA R).
apply Z.leb_le. reflexivity.
Qed.

Lemma cd_reads_n : DMcdR.cd_reads TfibB ARXr AOX DRq RMAXD_cf.
Proof.
destruct (YGcfInstCdReads.cd_reads_cf TfibB IOK Hp TfibB_syms HIOK).
constructor; try assumption. exact cr_budget_x_n.
Qed.

Lemma drq_cd_n : DMwalkIFA.drq_cd DRq RMAXD_cf.
Proof.
intros S its z zs HD. pose proof HD as (RX & CD & UQ & Q1 & Q2 & SZ & PB & CI & HHO).
pose proof (proj1 RX) as W.
pose proof (YG03cf.wfr_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
unfold wf_class_cf in CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F0 FM]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
pose proof (YG04.fa_len_nonneg (rg_free (reg S kBatchClass)) (wrc_runs _ _ _ _ _ _ CL)) as FN.
pose proof (YG03cf.mapped_bound_r_cf (as_universe TfibB) 0 0 0 S kBatchClass W ltac:(unfold kBatchClass; lia)) as MB.
pose proof (YGcfInstDrainDq.fa_len_room_cf TfibB _ S its (z :: zs) HD) as FA27.

assert (HCI : st_cache_inited S = true) by (apply CI; right; intros E; discriminate E).

destruct RX as (_ & _ & _ & _ & SF & _).
pose proof (proj1 (Forall_forall _ _) SF z ltac:(apply in_app_iff; left; left; reflexivity)) as (Z1 & Z2 & Z3).
pose proof (wrc_cache _ _ _ _ _ _ CL) as PC. rewrite HCI in PC. destruct PC as [PM PL].
split.
-
  unfold DMwalkIFA.cd_model. unfold RMAXD_cf, kFreeArrayOffset in *.
  split; [unfold kBatchClass; lia|]. split; [exact HCI|]. split; [exact PL|]. split; [exact PM|].
  split; [lia|]. split; [lia|]. split; [exact Z2|]. split; [exact Z3|].
  split; [lia|]. split; [exact A2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FM|].
  split; [exact FA27|].

  intros HG. pose proof (YG06bcf.fa_len_bound_cf _ _ _ _ _ _ CL ltac:(reflexivity)) as FBB.
  change (class_size kBatchClass) with 8192 in FBB. change (max_cached kBatchClass / 2) with 1 in HG.
  unfold kFreeArrayMapSize, kFreeArrayMax in *. lia.
-
  intros S' HRet.
  assert (OK : atok true (cache_dealloc kBatchClass z S)
    (YG03cf.cache_dealloc_post_cf (as_universe TfibB) 0 0 0 S kBatchClass (z - region_off kBatchClass)))
    by (apply (YG03cf.cache_dealloc_ok_cf (as_universe TfibB) 0 0 0 S kBatchClass z true W ltac:(unfold kBatchClass; lia));
        [lia | exact Z2 | exact Z3]).
  destruct (YGcfInstDrainDq.atok_cd_returns_cf _ _ _ _ _ _ OK HRet) as (ns' & POST).
  unfold YG03cf.cache_dealloc_post_cf in POST. cbv zeta in POST. cbn [snd] in POST.
  destruct POST as (W' & RO & CI' & AU & CE & MF & LEN).
  pose proof RO as (EC & ES & ESA & ESR & EQT & EQG & EFS & EDP & EII & ENV).

  assert (EQI : q_items S' = q_items S)
    by (unfold q_items, all_batches; rewrite EQT, EQG; reflexivity).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  +
    destruct HD as ((_ & IT & ND & BL & SF' & NDS) & _).
    split; [exact W'|]. split.
    * rewrite EC. exact IT.
    * split; [rewrite EQI; exact ND|]. split; [exact BL|].
      rewrite app_nil_r in SF', NDS. cbn [map] in *. rewrite app_nil_r. apply NoDup_cons_iff in NDS as [HZ NDS'].
      split; [|exact NDS'].
      apply Forall_forall. intros y Hy.
      pose proof (proj1 (Forall_forall _ _) SF' y ltac:(right; exact Hy)) as (Y1 & Y2 & Y3).
      rewrite (AU kBatchClass ltac:(unfold kBatchClass; lia)). split; [exact Y1|]. split; [exact Y2|].
      intros Hin. destruct (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[EY _]|Hold]; [|exact (Y3 Hold)].

      apply HZ. replace z with y by lia. exact Hy.
  +
    intros c' Hc'. pose proof (CD c' Hc') as CD'. unfold cdef in *.
    rewrite (AU c' ltac:(lia)), (LEN c' ltac:(lia)), Nat2Z.inj_add.
    destruct (Z.eqb_spec c' kBatchClass) as [->|NE].
    * replace (kBatchClass =? kBatchClass) with true in * by (symmetry; apply Z.eqb_refl).
      cbn [length] in CD'. rewrite Nat2Z.inj_succ in CD'. cbn [Z.of_nat]. lia.
    * replace (c' =? kBatchClass) with false in * by (symmetry; apply Z.eqb_neq; exact NE). cbn [Z.of_nat]. lia.
  +
    unfold YG03cf.unq_cf, quar_n, queued_n in *. rewrite EC, EQI. exact UQ.
  + rewrite EQT. exact Q1.
  + rewrite EQG. exact Q2.
  + exact SZ.
  + exact PB.
  + intros _. exact CI'.
  +
    apply (cf_hull_counts _ S); [unfold nsec_cf; rewrite ES; reflexivity | unfold sec_T_cf; rewrite ES; reflexivity | exact HHO].
Qed.

Lemma exr_cdealloc_preset_A : di_cdealloc_t B ARXr AOX DRq.
Proof.
pose proof (MnRecycle.de_cdealloc_em_e TfibB ARXr AOX DRq
  (DMcdF.cdealloc_m_of_reads TfibB ARXr AOX DRq RMAXD_cf TfibB_syms YGcfInstDrainR.rmaxd_ok_cf cd_reads_n drq_cd_n)) as CDE.
intros inst ly X its z zs W regs mem md PREX RX.
eapply amreal_mono; [| exact (CDE inst ly X its z zs W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & _ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | exact REST].
Qed.

Lemma exr_frame_r_preset_A : di_frame_t ARXr AOX.
Proof. exact (di_frame_r_cf TfibB IOK Hp). Qed.

Lemma exr_rview_preset_A : di_rview_t B ARXr DRq.
Proof.
intros inst ly X W mem md its zs (HI & HA & _) (RX & _). pose proof (HIOK _ HI) as ->.
destruct HA as (M & _).
assert (IT : forall k, In k its -> In k (st_chunks X)).
{ intros k Hk. destruct RX as (_ & IT & _). exact (proj1 (proj1 (Forall_forall _ _) IT k ltac:(apply in_app_iff; left; exact Hk))). }
split; [|split].
- pose proof (amr_const _ _ _ _ _ M) as C. rewrite (im_const_eq TfibB ly TfibB_syms) in C.
  pose proof (proj1 (Forall_forall _ _) C _ (PresetImg_sbconst.SB_CONST_A ly)) as Hc.
  pose proof (cell_holds_val_mem im_segs TfibB ly (w_H W) mem (AInst o_space) 8 (ASp 0) Hc) as V. cbn [aeval] in V.
  rewrite Z.add_0_r in V. exact V.
- intros k Hk. exact (item_facts_cf TfibB Hp ly X _ k M (IT k Hk)).
- intros z Hz.
  assert (SZ : slot_ok_cf X z)
    by (apply (RIx_cf_slots (as_universe TfibB) 0 0 0 X its [] zs z RX); cbn [map]; rewrite app_nil_r; exact Hz).
  pose proof (slot_carved_cf TfibB Hp ly X _ z M SZ) as (C1 & C2 & C3).
  pose proof SZ as (_ & Z2 & _). rewrite class_size_24_cf in Z2.
  split; [exact C1|]. split; [exact C2|]. split; [unfold kBatchBytes; exact Z2|].
  intros k a Hk Ha. exact (slot_vs_chunk_cf TfibB Hp ly X _ z k M SZ (IT k Hk) a Ha).
Qed.

Lemma rview_alloc_n : forall inst ly X W mem md its zs, ARXr inst ly X W mem md -> DRq X its zs ->
  rg_alloc_user (reg X kBatchClass) <= RMAXD_cf.
Proof.
intros inst ly X W mem md its zs (_ & HA & _) _.
pose proof (amr_wfr _ _ _ _ _ (proj1 HA)) as W0.
pose proof (YG03cf.wfr_classes _ _ _ _ _ W0 kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (YG03cf.mapped_bound_r_cf (as_universe TfibB) 0 0 0 X kBatchClass W0 ltac:(unfold kBatchClass; lia)) as MB.
unfold RMAXD_cf. lia.
Qed.

End r.

#[local] Existing Instance CfImg_A.

Section ra. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Variable NMAXD : Z.

Hypothesis HNQ : kQuarantineMax <= NMAXD.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.
Variable Hp : list Z.
Local Notation B := TfibB.
Local Notation ARX := (ARX_cf TfibB IOK Hp).
Local Notation ARXr := (ARXr_cf TfibB IOK Hp).
Local Notation AOX := (aowned TfibB).
Local Notation L24 := L24MAX_cf.
Local Notation QB := (QB_cf kQuarantineMax).
Local Notation DRq := (DRq_cf TfibB NMAXD).

Lemma exr_requar_x_preset_A : di_requar_x_t B ARX AOX L24 QB.
Proof.
exact (di_requar_x_cf TfibB IOK Hp HIOK TfibB_syms PresetImg_qapart.IMG_QAPART_A CfInstImgA.ERRB_QAPART_A
  PresetImg_constapart.CONST_APART_A L24MAX_cf kQuarantineMax).
Qed.

Lemma exr_requar_r_preset_A : di_requar_r_t B ARX ARXr AOX L24 QB DRq.
Proof.
pose proof (di_requar_r_cf TfibB IOK Hp HIOK TfibB_syms PresetImg_qapart.IMG_QAPART_A CfInstImgA.ERRB_QAPART_A
  PresetImg_constapart.CONST_APART_A kQuarantineMax L24MAX_cf) as RQ.
intros inst ly X W mem md sp0 tmp S' P mem' md' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
destruct (RQ inst ly X W mem md sp0 tmp S' P mem' md' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12) as (AR & D & OW).
exact (conj AR (conj (DRq_cf_mono kQuarantineMax NMAXD HNQ _ _ _ D) OW)).
Qed.

End ra.

#[local] Existing Instance CfParamsPreset.CfParams_preset.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable NMAXD : Z.

Hypothesis HNM : kQuarantineMax <= NMAXD < 2 ^ 30.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.
Local Notation AOX := (aowned TfibB).
Local Notation DRq := (DRq_cf TfibB NMAXD).

Lemma exr_drain_m_preset_A : forall Hp,
  DIfaceRh.de_drain_m_rh_t TfibB (ARX_cf TfibB IOK Hp) AOX drain_body_cf L24MAX_cf (QB_cf kQuarantineMax).
Proof.
intros Hp.
exact (YGcfInstDrainTopRh.ds_drain_rh_cf TfibB IOK Hp HIOK TfibB_syms TfibB_syms CfInstImgA.ERRB_QAPART_A
  (YGcfInstFreeQ.di_qview_cf TfibB IOK Hp L24MAX_cf (QB_cf kQuarantineMax) HIOK YGcfInstF1Wpreset.IMG_COVER_preset
    (AF0m.ts_tsd TfibB TfibB_syms) (PresetImg_fqconst.FQ_CONST_A TfibB TfibB_syms) (fun X H => proj1 H))
  (YGcfInstFreeQ.di_qowned_cf TfibB IOK Hp L24MAX_cf (QB_cf kQuarantineMax) HIOK)
  (YGcfInstFreeModel.di_stack_cf TfibB IOK Hp) (YGcfInstFreeModel.di_frame_cf TfibB IOK Hp)
  YGcfInstDrainTopRh.rec_le_preset).
Qed.

Lemma nmaxd_ok_n : DMwalkIFA.nmaxd_ok (NMAXD + 1).
Proof. pose proof HNM as [N1 N2]. unfold DMwalkIFA.nmaxd_ok. unfold kQuarantineMax in N1. lia. Qed.

Lemma lmaxd_ok_n : DMwalkIFA.lmaxd_ok (NMAXD + 1) (sec_map_size NMAXD).
Proof.
pose proof HNM as [N1 N2]. unfold kQuarantineMax in N1. unfold DMwalkIFA.lmaxd_ok.
assert (N0 : 0 <= NMAXD) by lia.
split.
- pose proof (rounded_size_bounds NMAXD N0) as [R1 _].
  pose proof (rz_size_bounds NMAXD) as [Z1 _].
  pose proof (req_size_bounds NMAXD N0) as (_ & _ & Q3).
  assert (FP : from_primary NMAXD = false).
  { unfold from_primary, needed_primary. apply Z.leb_gt. unfold kMaxSize. lia. }
  pose proof (secondary_geometry NMAXD N0 FP) as (_ & _ & S3 & _).
  unfold kPage, kSecRz in S3. lia.
- pose proof (YGcfInstDrainR.sec_map_size_mono_cf NMAXD (2 ^ 30) ltac:(lia)) as MO.
  assert (SM : sec_map_size (2 ^ 30) <= 2 ^ 31 - 8192) by (vm_compute; discriminate). lia.
Qed.

Lemma drq_sizes_n : DMwalkIFA.drq_sizes DRq (NMAXD + 1) (sec_map_size NMAXD).
Proof.
intros S its zs k D Hin.
assert (H2 : 2 * kMaxSize + 96 <= NMAXD) by (pose proof HNM as [N1 _]; unfold kMaxSize, kQuarantineMax in *; lia).
exact (YGcfInstDrainR.drq_sizes_cf TfibB NMAXD H2 S its zs k D Hin).
Qed.

Lemma rc_prim_step_n : forall Hp,
  DMrcReadsA.rc_prim_step_t TfibB (ARXr_cf TfibB IOK Hp) AOX DRq RMAXD_cf.
Proof.
intros Hp inst ly X k ks zs cbp W regs mem md off mem' md' PRE DR Hb AG VIS NEW HK CONST Ev El Ee.
assert (HR : kFreeArrayOffset <= RMAXD_cf) by (unfold RMAXD_cf; lia).
destruct (YGcfInstRcPrim.rc_prim_step_cf TfibB IOK Hp NMAXD RMAXD_cf HR inst ly X k ks zs cbp W regs mem md off mem' md'
  PRE DR Hb AG VIS NEW HK CONST Ev El Ee) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact (DMrcCf.cd_model_of_cf _ _ _ _ A2)|].
split; [exact A3|]. split; [exact A4 | exact A5].
Qed.

Lemma rc_prim_mach_rh_n : forall Hp,
  DMrcRhOkA.rc_prim_mach_rh_t TfibB (ARXr_cf TfibB IOK Hp) AOX DRq RMAXD_cf.
Proof.
intros Hp TB RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb.
eapply YG0dH.amreal'_mono; [| exact (YG0dH.amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _
  (DMrcPrim.rchunk_prim_m TfibB TB _ AOX _ RMAXD_cf RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb))].
intros r0 W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of TfibB _ AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.

Lemma rc_reads_n : forall Hp,
  DMrcRhOkA.rc_reads_rh TfibB (ARXr_cf TfibB IOK Hp) (DMrcSecCf.ARXsl_cf TfibB IOK Hp) AOX DRq RMAXD_cf.
Proof.
intros Hp.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [|split; [|split; [|split]]].
  + exact (YGcfInstRcPrim.rc_head_cf TfibB NMAXD).
  + exact (YGcfInstRcPrim.rc_model_cf TfibB NMAXD).
  + exact (DMrcFhCf.rc_prim_fh_of_cut TfibB TfibB_syms _ _
      (YGcfInstRcPrim.rc_fh_cut_facts_cf TfibB IOK Hp NMAXD HIOK ADIfaceA.img_cover_A)).
  + exact (rc_prim_step_n Hp).
  + intros inst ly X k ks zs cbp W regs mem md off PRE RX Hb G.
    exact (YGcfInstRcPrim.rc_prim_room_cf TfibB IOK Hp NMAXD inst ly X k ks zs cbp W regs mem md off PRE RX Hb G).
- exact (rc_prim_mach_rh_n Hp).
- exact (DMrcCf.SC_cf TfibB TfibB_syms IOK Hp HIOK).
- exact (DMrcCf.SM_cf TfibB TfibB_syms IOK Hp).
- exact (DMrcSecCf.rc_sec_step_sl_of_cf TfibB TfibB_syms IOK Hp CfInstImgA.ERRB_QAPART_A
    YGcfInstDrainTopRh.rec_le_preset).
- exact (YGcfInstRcPrim.rc_split_cf TfibB NMAXD).
- exact (DMrcCf.rc_sec_pre_rh_cf TfibB IOK Hp).
- exact (DMrcCf.rc_sec_rehide_all_cf TfibB IOK Hp).
Qed.

Lemma exr_rchunk_preset_A : forall Hp, DIfaceRh.di_rchunk_rh_t TfibB (ARXr_cf TfibB IOK Hp) AOX DRq.
Proof.
intros Hp.
pose proof (DMrcRhOkA.rchunk_ok_rh TfibB _ (DMrcSecCf.ARXsl_cf TfibB IOK Hp) _ _ (NMAXD + 1) (sec_map_size NMAXD) RMAXD_cf
  (rc_reads_n Hp) TfibB_syms nmaxd_ok_n lmaxd_ok_n YGcfInstDrainR.rmaxd_ok_cf drq_sizes_n
  (di_frame_r_cf TfibB IOK Hp)
  (conj (exr_rview_preset_A NMAXD IOK HIOK Hp) (rview_alloc_n NMAXD IOK Hp))
  (DMcdF.cdealloc_g_of_reads TfibB (ARXr_cf TfibB IOK Hp) AOX DRq RMAXD_cf TfibB_syms YGcfInstDrainR.rmaxd_ok_cf
    (cd_reads_n NMAXD IOK HIOK Hp))) as RM.
intros inst ly X k ks zs cbp W regs mem md P D.
eapply YG0dH.amreal'_mono; [| exact (RM inst ly X k ks zs cbp W regs mem md P D)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & _ & _ & HT).
exists regs', mem', md'. exact (conj Hc (conj HP HT)).
Qed.

Theorem diface_ext_rh_preset_A_n : forall Hp,
  YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr_cf TfibB IOK Hp) L24MAX_cf (QB_cf kQuarantineMax) (DRq_cf TfibB NMAXD).
Proof.
intros Hp. constructor.
- exact (exr_depot_preset_A IOK Hp).
- exact exr_dpost_aok_preset_A.
- exact (YGcfInstFreeMidE.exr_enqueue_cf TfibB IOK Hp
    (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) YGcfInstFreeImgpreset.FP_IZONE_ROM_TfibB
    YGcfInstFreeImgpreset.FP_DSTAT_TfibB (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms)
    YGcfInstFreeImgpreset.FP_DZONE_FP_TfibB YGcfInstFreeImgpreset.FP_CONST_TfibB
    (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms) YGcfInstF1Wpreset.IMG_COVER_preset
    PresetImg_errbapart.ERRB_APART_A PresetPfApartA.pf_apart_preset_A
    (YGcfInstEnqMisspreset.enq_arms_cf_preset TfibB TfibB_syms IOK Hp HIOK CfAroPresetA.relro_seg_preset_A
      (YGcfRefillToppreset.refill_spec_cf_preset_inst TfibB IOK TfibB_syms HIOK
        (@RepArmTcf.classfull_cf_of_hyps fx rc CfParamsPreset.CfParams_preset)))).
- eapply YGcfInstFree.exr_drain_of_g. exact (exr_drain_m_preset_A Hp).
- exact (exr_requar_x_preset_A IOK HIOK Hp).
- exact (exr_requar_r_preset_A NMAXD (proj1 HNM) IOK HIOK Hp).
- exact (exr_requar_e_preset_A NMAXD IOK Hp).
- exact (exr_rchunk_preset_A Hp).
- exact (exr_cdealloc_preset_A NMAXD IOK HIOK Hp).
- exact (exr_frame_r_preset_A IOK Hp).
- exact (exr_rview_preset_A NMAXD IOK HIOK Hp).
Qed.

End e.

Lemma nmaxd_small_ok : kQuarantineMax <= kQuarantineMax < 2 ^ 30.
Proof. unfold kQuarantineMax. lia. Qed.

Lemma nmaxd_big_ok_preset : kQuarantineMax <= NMAXD_big_cf < 2 ^ 30.
Proof. unfold NMAXD_big_cf. split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.

Theorem diface_ext_rh_preset_A : forall Hp,
  YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr_cf TfibB IOK Hp) L24MAX_cf (QB_cf kQuarantineMax) (DRq_cf TfibB kQuarantineMax).
Proof. exact (diface_ext_rh_preset_A_n kQuarantineMax nmaxd_small_ok IOK HIOK). Qed.

Theorem diface_ext_rh_preset_A_big : forall Hp,
  YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr_cf TfibB IOK Hp) L24MAX_cf (QB_cf kQuarantineMax) (DRq_cf TfibB NMAXD_big_cf).
Proof. exact (diface_ext_rh_preset_A_n NMAXD_big_cf nmaxd_big_ok_preset IOK HIOK). Qed.
End i.
