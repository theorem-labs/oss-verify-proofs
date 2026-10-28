(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnAEmbRP_b PnAEmbRF_b PnASrcKit_b Ba0_code_ac29c_ac2a0_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreB_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PNAERE.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem empty : PMA.opnew_spec L ar HI -> forall (fx : FPState) R M model K LBX FF LK Aw cr v sp r p1 p2 p3 m n q,
    ri_inv HI LBX FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    L5.u64_at RSEGS M v 0 -> L5.u64_at RSEGS M (v + 8) 0 -> L5.u64_at RSEGS M (v + 16) 0 ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> getr R (reg 13) = Z_to_bv 64 p3 -> p1 mod 4 = 0 -> p2 mod 4 = 0 -> p3 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 -> byte_at M (S p3) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 -> PNAEK.argp (ar_sptop ar) FF sp v p3 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> L5.u32_at RSEGS M p3 q -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 -> 0 <= q < 2 ^ 31 -> acredit_ok L cr 40 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) R' M' model' LK' Aw' b', regs_preserved R R' -> PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M' v b' 0 [PNM.BS m n q 0 0] ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b' 0 ++ LBX) FF LK' (adebit L cr 40) Aw' M' (vml_of model') ->
        getr R' (reg 10) = Z_to_bv 64 (b' + 40) -> 4096 <= b' -> b' + 40 < 2 ^ 47 -> (v + 24 <= b' \/ b' + 40 <= v) ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xad11c M model) K.
Proof.
  intros OPN fx R M model K LBX FF LK Aw cr v sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV V0 V8' V16 A11 A12 A13 P14 P24 P34 SP1 SP2 SP3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ CR BASE KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LBX FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LBX FF LK cr Aw M _ sp 12288 v p1 4 HH ASTK ltac:(lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LBX FF LK cr Aw M _ sp 12288 v p2 4 HH ASTK ltac:(lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & Pb2 & Pb3 & Pb4 & Pb5 & Pb6).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LBX FF LK cr Aw M _ sp 12288 v p3 4 HH ASTK ltac:(lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & Pc2 & Pc3 & Pc4 & Pc5 & Pc6).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LBX FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  (* [comment removed for export] *)
  pose proof BASE as (ICB & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB.
  assert (X0 : L5.img_clear MV 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X4 : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (PNAERF.stack_zeros12 M sp STKSH A16). exact Hi.
    assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LBX FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v 0) by (apply (proj2 (L5A.u64_at_vis H M v 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact V0).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact V8').
  assert (X8 : L5.u64_at RSEGS MV (v + 16) 0) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) 0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact V16).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R (reg 23))) as UR23. pose proof (PMAIS1.bvu (getr R (reg 24))) as UR24.
  LeanFeed.pfeed P (PNAERP.azrE0_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [assumption | unfold PNAERP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & eR1 & eR2 & eR8 & eR9 & eR10 & eR11 & eR12 & eR13 & eR14 & eR15 & eR18 & eR19 & eR20 & eR21 & eR22 & eR23
                 & T128 & T120 & T80 & T72 & T64 & T56 & T48 & T40 & T32 & T24 & T16 & T8 & T136 & T144 & T152 & T160 & T168).
  set (W1 := fun a => sp - 192 <= a < sp - 192 + 192).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBX FF LK cr Aw M model fx fx1 R 0xad11c R1 0x130338 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  (* [comment removed for export] *)
  unfold PMA.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMA.AD ADDR_A] in OPN.
  apply (OPN fx1 R1 M1 model1 K LBX FF LK Aw cr 40 (sp - 176) 710136 HH1 AM1 K0).
  { rewrite L5K.rl10. exact eR10. }
  { lia. }
  { exact CR. }
  { rewrite L5K.rl1. exact eR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact eR2. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M1 M1 sp 12288 176 (16 + 4096) (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1) (fun x X => X)); [lia| lia| lia|].
    replace (sp - 176) with (sp + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx2 R2 M2 model2 Aw2 B RB RP2 FRESH HP2 MRT2 IA2 AM2 HH2.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP2. change (16 + 4096) with 4112 in HP2. rewrite L5K.rl10 in RB.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH). pose proof QR as (Q0 & Q1 & Q16 & _ & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1.
  set (LB1 := (B, 40) :: LBX) in *. set (cr1 := adebit L cr 40) in *.
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF (sp - 176) 4112 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP2). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 4288 <= a < sp) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N. rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LBX FF 0 0); [exact Hc| lia]]. apply FR1; [exact Ha| unfold W1; lia]. }
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after L ar C HI HIok LBX FF LK cr Aw M1 M1 M2 _ sp 12288 (sp - 176) 4112 [] HH1 (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1) (fun x X => X) HP2); lia. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M2 model2 v 24 sp 12288 HH2 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  assert (STKSH2 : shadow_zero M2 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAERF.S_add8 (sp - 12288) j) as E. pose proof (PNAERF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T20; [rewrite <- E; apply STKSH; exact Hj| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia]. }
  assert (Y4 : L5KA.zeros_at MV2 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2). apply (PNAERF.stack_zeros12 M2 sp STKSH2 A16). exact Hi.
    assert (AV : L5A.avis H2 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH2 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV2 : PMSPA.accA M2 v 24).
  { apply (PMFA.accA_agree M M2 v 24); [| exact ACCV]. intros x Hx. pose proof (PNAERF.S_range x ltac:(lia)) as SRx. apply T20; [lia| | lia].
    exact (PNAEK.frame_sh_client L ar FF v 24 x LBX 0 0 AOV Hx). }
  assert (Y5 : L5KA.zeros_at MV2 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M2 model2 v 24 HH2 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV2). }
  assert (TV : forall a, v <= a < v + 24 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply T20; [lia| apply (L5SAR.obj_client L ar LBX FF 0 0 v 24 a AOB); lia| lia]. }
  assert (Y7 : L5.u64_at RSEGS MV2 v 0).
  { apply (proj2 (L5A.u64_at_vis H2 M2 v 0 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact V0]. }
  assert (Y8 : L5.u64_at RSEGS MV2 (v + 8) 0).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (v + 8) 0 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact V8']. }
  assert (Y9 : L5.u64_at RSEGS MV2 (v + 16) 0).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (v + 16) 0 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact V16]. }
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB1 FF LK cr1 Aw2 M2 model2 sp 12288 v p1 4 HH2 ASTK2 ltac:(lia) AG1 ltac:(lia)) as (AV1 & AVS1).
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB1 FF LK cr1 Aw2 M2 model2 sp 12288 v p2 4 HH2 ASTK2 ltac:(lia) AG2 ltac:(lia)) as (AV2 & AVS2).
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB1 FF LK cr1 Aw2 M2 model2 sp 12288 v p3 4 HH2 ASTK2 ltac:(lia) AG3 ltac:(lia)) as (AV3 & AVS3).
  assert (TP : forall p x, 6905856 <= p -> p + 4 <= 2 ^ 47 -> (sp <= p \/ p + 4 <= ahl_ceil ar) -> (forall i sp' scr', 0 <= i < 4 -> sp' <= sp -> aclient L ar LBX FF sp' scr' (p + i)) ->
             p <= x < p + 4 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros p x Q0' Q1' Q3 CLp Hx. apply T20; [lia| replace x with (p + (x - p)) by lia; apply CLp; lia| lia]. }
  assert (TPS : forall p, PNAEK.argp (ar_sptop ar) FF sp v p 4 -> 0 <= p < 2 ^ 47 -> byte_at M (S p) 0 -> byte_at M2 (S p) 0).
  { intros p AP Hp X. pose proof (PNAERF.S_range p Hp) as SRp. unfold byte_at in *. rewrite T20; [exact X| lia| | lia].
    exact (PNAEK.arg_client L ar HI LBX FF LK cr Aw M _ sp 12288 v p 4 HH ASTK ltac:(lia) AP ltac:(lia) LBX 0 0). }
  assert (Y10 : L5.u32_at RSEGS MV2 p1 m).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p1 m AV1 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p1 i Pa0 Pa1 Pa4 Pa6 Hi)| lia| lia| exact U1]. }
  assert (Y11 : L5.u32_at RSEGS MV2 p2 n).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p2 n AV2 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p2 i Pb0 Pb1 Pb4 Pb6 Hi)| lia| lia| exact U2]. }
  assert (Y11b : L5.u32_at RSEGS MV2 p3 q).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p3 q AV3 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p3 i Pc0 Pc1 Pc4 Pc6 Hi)| lia| lia| exact U3]. }
  assert (Y12 : L5KA.zeros_at MV2 (p1 / 8 + 2147450880) 1).
  { apply PNAERF.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p1 AG1 ltac:(lia) SP1)|].
    pose proof (AVS1 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y13 : L5KA.zeros_at MV2 (p2 / 8 + 2147450880) 1).
  { apply PNAERF.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p2 AG2 ltac:(lia) SP2)|].
    pose proof (AVS2 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y13b : L5KA.zeros_at MV2 (p3 / 8 + 2147450880) 1).
  { apply PNAERF.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p3 AG3 ltac:(lia) SP3)|].
    pose proof (AVS3 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  (* [comment removed for export] *)
  assert (BIN : In (B, 40) LB1) by (left; reflexivity).
  assert (Y14 : L5KA.zeros_at MV2 (B / 8 + 2147450880) 5).
  { destruct QSH as (ZB & _). intros i Hi. change (40 / 8) with 5 in ZB.
    assert (AV : L5A.avis H2 (S B + i) 1).
    { apply (VBSH2 B 40 _ 1 BIN). intros j Hj. replace (S B + i + j) with (S B + (i + j)) by lia. apply PNAEK.sh_in; [lia| lia| lia| lia]. }
    unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
    - replace (B / 8 + 2147450880 + i) with (S B + i) by (unfold S, SB; lia). apply ZB. lia.
    - replace (B / 8 + 2147450880 + i) with (S B + i) by (unfold S, SB; lia). pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y15 : L5.writable RSEGS MV2 B 40).
  { apply (proj2 (L5A.writable_vis H2 M2 B 40 (VBLK2 B 40 B 40 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]. }
  pose proof (PNAEK.arg_fresh_apart ar M FF LK sp 12288 v p1 4 B 40 ASTK ltac:(lia) AG1 QFA Q4 ltac:(lia)) as PB1.
  pose proof (PNAEK.arg_fresh_apart ar M FF LK sp 12288 v p2 4 B 40 ASTK ltac:(lia) AG2 QFA Q4 ltac:(lia)) as PB2.
  pose proof (PNAEK.arg_fresh_apart ar M FF LK sp 12288 v p3 4 B 40 ASTK ltac:(lia) AG3 QFA Q4 ltac:(lia)) as PB3.
  assert (VB : v + 24 <= B \/ B + 40 <= v).
  { destruct AOV as (f & Hf & Yv1 & Yv2). destruct (QFA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; [right; lia| left; lia]. }
  (* [comment removed for export] *)
  assert (TS : forall a v0, sp - 176 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  pose proof (TS (sp - 24) _ ltac:(lia) ltac:(lia) T24) as Z24.
  pose proof (TS (sp - 32) _ ltac:(lia) ltac:(lia) T32) as Z32.
  pose proof (TS (sp - 40) _ ltac:(lia) ltac:(lia) T40) as Z40.
  pose proof (TS (sp - 48) _ ltac:(lia) ltac:(lia) T48) as Z48.
  pose proof (TS (sp - 56) _ ltac:(lia) ltac:(lia) T56) as Z56.
  pose proof (TS (sp - 64) _ ltac:(lia) ltac:(lia) T64) as Z64.
  pose proof (TS (sp - 72) _ ltac:(lia) ltac:(lia) T72) as Z72.
  pose proof (TS (sp - 80) _ ltac:(lia) ltac:(lia) T80) as Z80.
  pose proof (TS (sp - 120) _ ltac:(lia) ltac:(lia) T120) as Z120.
  pose proof (TS (sp - 128) _ ltac:(lia) ltac:(lia) T128) as Z128.
  pose proof (TS (sp - 136) _ ltac:(lia) ltac:(lia) T136) as Z136. pose proof (TS (sp - 144) _ ltac:(lia) ltac:(lia) T144) as Z144.
  pose proof (TS (sp - 152) _ ltac:(lia) ltac:(lia) T152) as Z152. pose proof (TS (sp - 160) _ ltac:(lia) ltac:(lia) T160) as Z160.
  pose proof (TS (sp - 168) _ ltac:(lia) ltac:(lia) T168) as Z168.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 176)) by (rewrite CS2 by inl; exact eR2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 (sp - 80)) by (rewrite CS2 by inl; exact eR8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 1) by (rewrite CS2 by inl; exact eR9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 (sp - 104)) by (rewrite CS2 by inl; exact eR18).
  assert (J19 : getr R2 (reg 19) = Z_to_bv 64 0) by (rewrite CS2 by inl; exact eR19).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 ((sp - 80) / 8 + 2147450880)) by (rewrite CS2 by inl; exact eR20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact eR21).
  assert (J22 : getr R2 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact eR22).
  assert (J23 : getr R2 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS2 by inl; rewrite eR23; symmetry; apply Z_to_bv_bv_unsigned).
  assert (EK02 : L5SAR.ek L ar LBX FF sp 12288 [] M M2).
  { intros a (Ha & Hc & Ho). pose proof (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc) as Hc0.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBX FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; (apply T20; [exact Ha| exact Hc0| lia]). }
  assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2) by (apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [] M M2 EK02); [intros a Ha r0 []| exact BASE]).
  pose proof BASE2 as (ICB2 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB2.
  assert (Y0b : L5.img_clear MV2 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB2).
  LeanFeed.pfeed P (PNAERP.azrE1_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [assumption | unfold PNAERP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & fR1 & fR2 & fR8 & fR9 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & fR17 & fR18 & fR19 & fR20 & fR22 & fR23 & fR24
                 & U152 & U144 & U136 & U128 & U120 & U96 & B32 & B24 & B16 & B8 & B0 & U88 & U104 & U8 & U16 & U24 & U32 & U40 & U48 & U56 & U64 & U72 & U80
                 & U160 & U168 & U176 & U184 & U192).
  set (W3 := fun a => (sp - 256 <= a < sp - 256 + 256) \/ (B + 0 <= a < B + 0 + 40)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M2 model2 fx2 fx3 R2 0xad5f8 R3 0x77c94 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [|lia]. unfold aclientw, aclient_g. left. exists (B, 40). split; [exact BIN| cbn [fst snd]; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  pose proof AM3 as (Mh3 & MI3).
  assert (ASTK3 : L5CA.astk ar M3 sp 12288) by (apply (L5SAR.astk_grows ar M2 M3 sp 12288 ASTK2 MGM3)).
  (* [comment removed for export] *)
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as MCP. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MCP.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memcpy L C LYa), (L5A.aly_scr_mem L C LYa) in MCP.
  assert (UX2 : bv_unsigned (getr R3 2%bv) = sp - 192) by (rewrite L5K.rl2, fR2; apply L5.unsigned_lit; lia).
  apply (MCP fx3 R3 M3 model3 LB1 FF LK cr1 Aw2 B 0 0 [] K); clear MCP.
  { split; [exact HH3|]. split; [exact Mh3|]. split; [exact MI3|].
    split; [rewrite L5K.rl10, (KS3 10%nat) by inl; exact RB|]. split; [rewrite L5K.rl12; exact fR12|]. split; [lia|].
    split; [rewrite L5K.rl4, (KS3 4%nat) by inl; rewrite CS2 by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    split; [rewrite L5K.rl1, fR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
    split. { rewrite UX2. apply (L5SAR.astack_ok_of_astk L ar C LYa M3 M3 sp 12288 192 2560 ASTK3 (fun x X => X)); [lia| lia| lia|].
             replace (sp - 192) with (sp + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    split; [intros a Ha; lia|]. split; [intros i Hi; lia|]. split; [intros i m0 Hi Hm; assert (Em : m0 = 0%nat) by lia; subst m0; reflexivity|].
    split; [exact K0|]. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. lia. }
  { rewrite L5K.rl11. exact fR11. }
  { intros a Ha; lia. }
  { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. lia. }
  { intros i Hi; lia. }
  { reflexivity. }
  { intros _; lia. }
  intros R4 M4 model4 mR10 RP4 BYTES PRES4 SDEF4 RT4 MI4 HH4. rewrite UX2 in PRES4, SDEF4. rewrite L5K.rl1, fR1.
  assert (Mh4 : m_halted model4 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT4); exact Mh3).
  assert (AM4 : L5CA.amodel_ok Aw2 model4) by (split; [exact Mh4| exact MI4]).
  assert (ASTK4 : L5CA.astk ar M4 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB1 FF LK cr1 Aw2 M3 M3 M4 _ sp _ (sp - 192) 2560 HH3 ASTK3 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES4. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF4.
    - lia. - lia. - lia. }
  assert (CS4 : forall k0, In k0 L5SAR.cs_all -> getr R4 (reg k0) = getr R3 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R3 R4 k0 RP4 Hk)).
  (* [comment removed for export] *)
  assert (T42 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB1 FF 0 0 a -> ~ (sp - 2752 <= a < sp) -> ~ (B <= a < B + 40) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB1 FF 0 0); [exact Hc| lia]| lia]. apply FR3; [exact Ha| unfold W3; lia]. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  set (H4 := ahid Aw2 model4) in *. set (MV4 := mrestrict H4 M4) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M4 model4 v 24 sp 12288 HH4 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF4 & OVIS4 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as ST4. rewrite (L5A.aly_segs L C LYa) in ST4.
  pose proof (L5A.statics_facts L C M4 LYa ST4) as (GOT4 & CSB4 & CUAR4 & _).
  assert (EK04 : L5SAR.ek L ar LBX FF sp 12288 [] M M4).
  { intros a (Ha & Hc & Ho).
    pose proof (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc) as Hc0.
    assert (HcB : aclient L ar LB1 FF 0 0 a) by (apply (L5SAR.aclient_consb L ar LBX FF (B, 40) 0 0 a Hc0)).
    assert (NB : ~ (B <= a < B + 40)) by (exact (PNAEK.own_notclient L ar C HI LY HIok B 40 LBX FF LK cr1 Aw2 M2 _ HH2 a 0 0 Hc0)).
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBX FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1];
      (rewrite T42; [apply T20; [exact Ha| exact Hc0| lia]| exact Ha| exact HcB| lia| exact NB]). }
  assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4).
  { apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [] M M4 EK04); [| exact BASE]. intros a Ha r0 []. }
  pose proof BASE4 as (ICB4 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB4.
  assert (Z0' : L5.img_clear MV4 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB4).
  assert (Z1' : L5.u64_at RSEGS MV4 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H4 M4 1309752 2147450880 (VIMG4 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB4).
  assert (Z2' : L5.u32_at RSEGS MV4 1309760 1) by (apply (proj2 (L5A.u32_at_vis H4 M4 1309760 1 (VIMG4 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR4).
  assert (Z3' : L5.writable RSEGS MV4 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H4 M4 (sp - 4096) 4096 (VIS4 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M4 sp 12288); [exact ASTK4| lia| lia| lia]. }
  assert (STKSH4 : shadow_zero M4 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAERF.S_add8 (sp - 12288) j) as E. pose proof (PNAERF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T42; [rewrite <- E; apply STKSH2; exact Hj| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia| lia]. }
  assert (Z4' : L5KA.zeros_at MV4 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV4. rewrite (AsanAcct.mrestrict_visible H4 M4). apply (PNAERF.stack_zeros12 M4 sp STKSH4 A16). exact Hi.
    assert (AV : L5A.avis H4 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH4 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV4 : PMSPA.accA M4 v 24).
  { apply (PMFA.accA_agree M2 M4 v 24); [| exact ACCV2]. intros x Hx. pose proof (PNAERF.S_range x ltac:(lia)) as SRx. apply T42; [lia| | lia| lia].
    exact (PNAEK.frame_sh_client L ar FF v 24 x LB1 0 0 AOV Hx). }
  assert (Z5' : L5KA.zeros_at MV4 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M4 model4 v 24 HH4 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV4). }
  assert (TV4 : forall a, v <= a < v + 24 -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha. apply T42; [lia| apply (L5SAR.obj_client L ar LB1 FF 0 0 v 24 a AOB); lia| lia| lia]. }
  assert (Z6' : L5.writable RSEGS MV4 v 24).
  { apply (proj2 (L5A.writable_vis H4 M4 v 24 OVIS4 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF4. lia. lia. }
  assert (Z7' : L5.u64_at RSEGS MV4 v 0).
  { apply (proj2 (L5A.u64_at_vis H4 M4 v 0 ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; rewrite TV4 by lia; apply TV; lia| lia| lia| exact V0]. }
  assert (Z8' : L5.u64_at RSEGS MV4 (v + 8) 0).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (v + 8) 0 ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; rewrite TV4 by lia; apply TV; lia| lia| lia| exact V8']. }
  assert (Z9' : L5.u64_at RSEGS MV4 (v + 16) 0).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (v + 16) 0 ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; rewrite TV4 by lia; apply TV; lia| lia| lia| exact V16]. }
  assert (ZB4 : shadow_zero M4 B 5).
  { destruct QSH as (ZB & _). change (40 / 8) with 5 in ZB. intros j Hj. unfold byte_at. pose proof (PNAERF.shadow_low B 40 j ltac:(lia) ltac:(lia) ltac:(change (40 / 8) with 5; lia)) as SL.
    rewrite T42; [apply ZB; exact Hj| lia| | lia| lia].
    unfold aclient, aclient_g. do 6 right. exists (B, 40). split; [exact BIN| cbn [fst snd]; apply PNAEK.sh_in; [lia| lia| lia| change (40 / 8) with 5; lia]]. }
  assert (Z10' : L5KA.zeros_at MV4 (B / 8 + 2147450880) 5).
  { intros i Hi.
    assert (AV : L5A.avis H4 (S B + i) 1).
    { apply (VBSH4 B 40 _ 1 BIN). intros j Hj. replace (S B + i + j) with (S B + (i + j)) by lia. apply PNAEK.sh_in; [lia| lia| lia| lia]. }
    unfold MV4. rewrite (AsanAcct.mrestrict_visible H4 M4).
    - replace (B / 8 + 2147450880 + i) with (S B + i) by (unfold S, SB; lia). apply ZB4. lia.
    - replace (B / 8 + 2147450880 + i) with (S B + i) by (unfold S, SB; lia). pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (BDEF4 : L5.defined M4 B 40).
  { intros i Hi. rewrite PRES4; [apply (L5.defined_grows M2 M3 _ _ MGM3 QDEF i Hi)| lia| | lia].
    unfold aclient, aclient_g. left. exists (B, 40). split; [exact BIN| cbn [fst snd]; lia]. }
  assert (Z11' : L5.writable RSEGS MV4 B 40).
  { apply (proj2 (L5A.writable_vis H4 M4 B 40 (VBLK4 B 40 B 40 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [exact BDEF4| lia| lia]. }
  assert (TS4 : forall a v0, sp - 192 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v0 -> L5.u64_at RSEGS MV4 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H4 M4 a v0 (VIS4 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M3); [intros i Hi; apply PRES4; [lia| apply L5SAR.stack_client; lia| lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply VIS2; lia| lia| lia| exact X]. }
  pose proof (TS4 (sp - 8) _ ltac:(lia) ltac:(lia) U8) as V8x.
  pose proof (TS4 (sp - 16) _ ltac:(lia) ltac:(lia) U16) as V16x.
  pose proof (TS4 (sp - 24) _ ltac:(lia) ltac:(lia) U24) as V24x.
  pose proof (TS4 (sp - 32) _ ltac:(lia) ltac:(lia) U32) as V32x.
  pose proof (TS4 (sp - 40) _ ltac:(lia) ltac:(lia) U40) as V40x.
  pose proof (TS4 (sp - 48) _ ltac:(lia) ltac:(lia) U48) as V48x.
  pose proof (TS4 (sp - 56) _ ltac:(lia) ltac:(lia) U56) as V56x.
  pose proof (TS4 (sp - 64) _ ltac:(lia) ltac:(lia) U64) as V64x.
  pose proof (TS4 (sp - 72) _ ltac:(lia) ltac:(lia) U72) as V72x.
  pose proof (TS4 (sp - 80) _ ltac:(lia) ltac:(lia) U80) as V80x.
  pose proof (TS4 (sp - 88) _ ltac:(lia) ltac:(lia) U88) as V88x.
  pose proof (TS4 (sp - 96) _ ltac:(lia) ltac:(lia) U96) as V96x.
  pose proof (TS4 (sp - 104) _ ltac:(lia) ltac:(lia) U104) as V104x.
  pose proof (TS4 (sp - 160) _ ltac:(lia) ltac:(lia) U160) as V160x. pose proof (TS4 (sp - 168) _ ltac:(lia) ltac:(lia) U168) as V168x.
  pose proof (TS4 (sp - 120) _ ltac:(lia) ltac:(lia) U120) as V120x.
  pose proof (TS4 (sp - 128) _ ltac:(lia) ltac:(lia) U128) as V128x.
  pose proof (TS4 (sp - 136) _ ltac:(lia) ltac:(lia) U136) as V136x.
  pose proof (TS4 (sp - 144) _ ltac:(lia) ltac:(lia) U144) as V144x.
  pose proof (TS4 (sp - 152) _ ltac:(lia) ltac:(lia) U152) as V152x.
  pose proof (TS4 (sp - 176) _ ltac:(lia) ltac:(lia) U176) as V176x. pose proof (TS4 (sp - 184) _ ltac:(lia) ltac:(lia) U184) as V184x.
  pose proof (TS4 (sp - 192) _ ltac:(lia) ltac:(lia) U192) as V192x.
  assert (E24 : getr R2 (reg 24) = getr R (reg 24)) by (rewrite CS2 by inl; rewrite (KS1 24%nat) by inl; reflexivity). rewrite E24 in V192x.
  assert (K2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 192)) by (rewrite CS4 by inl; exact fR2).
  assert (K8 : getr R4 (reg 8) = Z_to_bv 64 (sp - 104)) by (rewrite CS4 by inl; exact fR8).
  assert (K9 : getr R4 (reg 9) = Z_to_bv 64 v) by (rewrite CS4 by inl; exact fR9).
  assert (K18 : getr R4 (reg 18) = Z_to_bv 64 (v + 8)) by (rewrite CS4 by inl; exact fR18).
  assert (K19 : getr R4 (reg 19) = Z_to_bv 64 (sp - 96)) by (rewrite CS4 by inl; exact fR19).
  assert (K20 : getr R4 (reg 20) = Z_to_bv 64 B) by (rewrite CS4 by inl; exact fR20).
  assert (K21 : getr R4 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS4 by inl; rewrite (KS3 21%nat) by inl; exact J21).
  assert (K22 : getr R4 (reg 22) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS4 by inl; exact fR22).
  assert (K23 : getr R4 (reg 23) = Z_to_bv 64 ((sp - 96) / 8 + 2147450880)) by (rewrite CS4 by inl; exact fR23).
  assert (K24 : getr R4 (reg 24) = Z_to_bv 64 (v / 8 + 2147450880)) by (rewrite CS4 by inl; exact fR24).
  LeanFeed.pfeed P (PNAERP.azrE2_conc fx3 R4 MV4 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 24%nat => bv_unsigned (getr R (reg 24)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [assumption | unfold PNAERP.aligned; lia | lia]).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FZ5 & MS5 & KS5 & hR1 & hR2 & hR5 & hR8 & hR10 & hR11 & hR12 & hR13 & hR14 & hR15 & hR16 & hR17 & hR18 & hR19 & hR20 & hR21 & hR22 & hR23 & hR24
                 & H128 & H120 & H88 & H16v & H96 & H8v & H104 & H0v & H8 & H16 & H24 & H32 & H40 & H48 & H56 & H64 & H72 & H80).
  set (W5 := fun a => (sp - 256 <= a < sp - 256 + 256) \/ (v + 0 <= a < v + 0 + 24)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK cr1 Aw2 M4 model4 fx3 fx5 R4 0xad7f4 R5 0x7ba7c M5v W5 K HH4 AM4 MS5 MG5).
  { intros a Ha N. apply FZ5; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB1 FF 0 0 v 24 a AOB); lia| lia]. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
  pose proof AM5 as (Mh5 & MI5).
  assert (ASTK5 : L5CA.astk ar M5 sp 12288) by (apply (L5SAR.astk_grows ar M4 M5 sp 12288 ASTK4 MGM5)).
  assert (ZB5 : shadow_zero M5 B 5).
  { intros j Hj. pose proof (PNAERF.shadow_low B 40 j ltac:(lia) ltac:(lia) ltac:(change (40 / 8) with 5; lia)) as SL. unfold byte_at.
    rewrite FR5; [apply ZB4; exact Hj| lia| unfold W5; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
  (* [comment removed for export] *)
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx5 R5 M5 model5 LB1 FF LK cr1 Aw2 K B 40 40 40); clear ANN.
  { exact HH5. }
  { exact Mh5. }
  { exact MI5. }
  { rewrite L5K.rl10. exact hR10. }
  { rewrite L5K.rl11. exact hR11. }
  { rewrite L5K.rl12. exact hR12. }
  { rewrite L5K.rl13. exact hR13. }
  { exact BIN. }
  { exact Q16. }
  { lia. }
  { lia. }
  { split; [change (40 / 8) with 5; exact ZB5| split; [intros X; exfalso; apply X; reflexivity| intros j Hj; change ((40 + 7) / 8) with 5 in Hj; lia]]. }
  { rewrite L5K.rl4, (KS5 4%nat) by inl. rewrite CS4 by inl. rewrite (KS3 4%nat) by inl. rewrite CS2 by inl. rewrite (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, hR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, hR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M5 M5 sp 12288 128 2304 ASTK5 (fun x X => X)); [lia| lia| lia|].
    replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx6 R6 M6 model6 Aw6 RP6 ANN6 KEEP6 DSH6 SCR6 MRT6 INC6 MI6 HH6.
  rewrite L5K.rl2, hR2, L5.unsigned_lit in KEEP6, SCR6 by lia. rewrite L5K.rl1, hR1.
  assert (AM6 : L5CA.amodel_ok Aw6 model6) by (split; [rewrite (L5LZ.model_rt_halted model5 model6 MRT6); exact Mh5| exact MI6]).
  assert (CS6 : forall k0, In k0 L5SAR.cs_all -> getr R6 (reg k0) = getr R5 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R5 R6 k0 RP6 Hk)).
  assert (ASTK6 : L5CA.astk ar M6 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB1 FF LK cr1 Aw2 M5 M5 M6 _ sp 12288 (sp - 128) 2304 HH5 ASTK5 (fun x X => X)).
    - intros a Ha Hs Hns. apply KEEP6; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNAEK.in_shadow_range B 40 a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR6.
    - lia. - lia. - lia. }
  (* [comment removed for export] *)
  assert (T65 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB1 FF 0 0 a -> ~ (sp - 2432 <= a < sp - 128) -> ~ in_shadow_of B 40 a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply KEEP6; [exact Ha| apply (L5SAR.aclient_narrow L ar LB1 FF 0 0); [exact Hc| lia]| exact N2]. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB1 FF LK cr1 Aw6 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
  set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB1 FF LK cr1 Aw6 M6 model6 v 24 sp 12288 HH6 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF6 & OVIS6 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as ST6. rewrite (L5A.aly_segs L C LYa) in ST6.
  pose proof (L5A.statics_facts L C M6 LYa ST6) as (GOT6 & CSB6 & CUAR6 & _).
  assert (Q0' : L5.img_clear MV6 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT6).
  assert (Q1' : L5.u64_at RSEGS MV6 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H6 M6 1309752 2147450880 (VIMG6 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB6).
  assert (Q2' : L5.u32_at RSEGS MV6 1309760 1) by (apply (proj2 (L5A.u32_at_vis H6 M6 1309760 1 (VIMG6 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR6).
  assert (Q3' : L5.writable RSEGS MV6 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H6 M6 (sp - 4096) 4096 (VIS6 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M6 sp 12288); [exact ASTK6| lia| lia| lia]. }
  assert (STKSH6 : shadow_zero M6 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAERF.S_add8 (sp - 12288) j) as E. pose proof (PNAERF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T65; [| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia| apply (PNAEK.sh_apart B 40 (sp - 12288 + 8 * j)); lia].
    rewrite FR5; [| lia| unfold W5; intros [XW|XW]; lia]. rewrite <- E. apply STKSH4. exact Hj. }
  assert (Q4' : L5KA.zeros_at MV6 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV6. rewrite (AsanAcct.mrestrict_visible H6 M6). apply (PNAERF.stack_zeros12 M6 sp STKSH6 A16). exact Hi.
    assert (AV : L5A.avis H6 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH6 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV6 : PMSPA.accA M6 v 24).
  { apply (PMFA.accA_agree M4 M6 v 24); [| exact ACCV4]. intros x Hx. pose proof (PNAERF.S_range x ltac:(lia)) as SRx.
    rewrite T65; [| lia| exact (PNAEK.frame_sh_client L ar FF v 24 x LB1 0 0 AOV Hx)| lia| apply (PNAEK.sh_apart B 40 x); lia].
    apply FR5; [lia| unfold W5; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
  assert (Q5' : L5KA.zeros_at MV6 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB1 FF LK cr1 Aw6 M6 model6 v 24 HH6 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV6). }
  assert (Q6' : L5.writable RSEGS MV6 v 24).
  { apply (proj2 (L5A.writable_vis H6 M6 v 24 OVIS6 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF6. lia. lia. }
  assert (TV6 : forall a, v <= a < v + 24 -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
  { intros a Ha. apply T65; [lia| apply (L5SAR.obj_client L ar LB1 FF 0 0 v 24 a AOB); lia| lia|].
    intros X. pose proof (PNAEK.in_shadow_range B 40 a ltac:(lia) ltac:(lia) X). destruct OBIG as [YW|YW]; lia. }
  assert (TS6 : forall a v0, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M5v a v0 -> L5.u64_at RSEGS MV6 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H6 M6 a v0 (VIS6 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply T65; [lia| apply L5SAR.stack_client; lia| lia| intros XS; pose proof (PNAEK.in_shadow_range B 40 i ltac:(lia) ltac:(lia) XS); lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS5); [apply VIS4; lia| lia| lia| exact X]. }
  pose proof (TS6 (sp - 8) _ ltac:(lia) ltac:(lia) H8) as Q8x.
  pose proof (TS6 (sp - 16) _ ltac:(lia) ltac:(lia) H16) as Q16x.
  pose proof (TS6 (sp - 24) _ ltac:(lia) ltac:(lia) H24) as Q24x.
  pose proof (TS6 (sp - 32) _ ltac:(lia) ltac:(lia) H32) as Q32x.
  pose proof (TS6 (sp - 40) _ ltac:(lia) ltac:(lia) H40) as Q40x.
  pose proof (TS6 (sp - 48) _ ltac:(lia) ltac:(lia) H48) as Q48x.
  pose proof (TS6 (sp - 56) _ ltac:(lia) ltac:(lia) H56) as Q56x.
  pose proof (TS6 (sp - 64) _ ltac:(lia) ltac:(lia) H64) as Q64x.
  pose proof (TS6 (sp - 72) _ ltac:(lia) ltac:(lia) H72) as Q72x.
  pose proof (TS6 (sp - 80) _ ltac:(lia) ltac:(lia) H80) as Q80x.
  pose proof (TS6 (sp - 88) _ ltac:(lia) ltac:(lia) H88) as Q88x.
  pose proof (TS6 (sp - 96) _ ltac:(lia) ltac:(lia) H96) as Q96x.
  pose proof (TS6 (sp - 104) _ ltac:(lia) ltac:(lia) H104) as Q104x.
  pose proof (TS6 (sp - 120) _ ltac:(lia) ltac:(lia) H120) as Q120x.
  pose proof (TS6 (sp - 128) _ ltac:(lia) ltac:(lia) H128) as Q128x.
  assert (QV0 : L5.u64_at RSEGS MV6 v B).
  { apply (proj2 (L5A.u64_at_vis H6 M6 v B ltac:(eapply L5A.avis_sub; [exact OVIS6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply TV6; lia| lia| lia|]. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS5); [eapply L5A.avis_sub; [exact OVIS4| lia| lia]| lia| lia| exact H0v]. }
  assert (QV8 : L5.u64_at RSEGS MV6 (v + 8) (B + 40)).
  { apply (proj2 (L5A.u64_at_vis H6 M6 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply TV6; lia| lia| lia|]. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS5); [eapply L5A.avis_sub; [exact OVIS4| lia| lia]| lia| lia| exact H8v]. }
  assert (QV16 : L5.u64_at RSEGS MV6 (v + 16) (B + 40)).
  { apply (proj2 (L5A.u64_at_vis H6 M6 (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply TV6; lia| lia| lia|]. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS5); [eapply L5A.avis_sub; [exact OVIS4| lia| lia]| lia| lia| exact H16v]. }
  assert (CH6 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (v <= a < v + 24) -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2.
    assert (HcB : aclient L ar LB1 FF 0 0 a) by (apply (L5SAR.aclient_consb L ar LBX FF (B, 40) 0 0 a Hc)).
    assert (NB : ~ (B <= a < B + 40)) by (exact (PNAEK.own_notclient L ar C HI LY HIok B 40 LBX FF LK cr1 Aw2 M2 _ HH2 a 0 0 Hc)).
    pose proof (PNAEK.own_sh_notclient L ar C HI LY HIok B 40 LBX FF LK cr1 Aw2 M2 _ HH2 ltac:(lia) a 0 0 Hc) as NS.
    rewrite T65; [| exact Ha| exact HcB| lia| exact NS]. rewrite FR5; [| exact Ha| unfold W5; lia].
    rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB1 FF 0 0); [exact HcB| lia]| lia]. rewrite FR3; [| exact Ha| unfold W3; lia].
    rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LBX FF 0 0); [exact Hc| lia]]. apply FR1; [exact Ha| unfold W1; lia]. }
  assert (EK06 : L5SAR.ek L ar LBX FF sp 12288 [(v, 24)] M M6).
  { intros a (Ha & Hc & Ho).
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBX FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1];
      (apply CH6; [exact Ha| exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc)| lia| intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]]). }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
  { apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [(v, 24)] M M6 EK06); [| exact BASE]. intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  pose proof BASE6 as (ICB6 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB6.
  assert (Q0b : L5.img_clear MV6 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB6).
  assert (L2 : getr R6 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite CS6 by inl; exact hR2).
  assert (L8 : getr R6 (reg 8) = Z_to_bv 64 (v + 8)) by (rewrite CS6 by inl; exact hR8).
  assert (L9 : getr R6 (reg 9) = Z_to_bv 64 v) by (rewrite CS6 by inl; rewrite (KS5 9%nat) by inl; exact K9).
  assert (L18 : getr R6 (reg 18) = Z_to_bv 64 p3) by (rewrite CS6 by inl; exact hR18).
  assert (L19 : getr R6 (reg 19) = Z_to_bv 64 p2) by (rewrite CS6 by inl; exact hR19).
  assert (L20 : getr R6 (reg 20) = Z_to_bv 64 p1) by (rewrite CS6 by inl; exact hR20).
  assert (L21 : getr R6 (reg 21) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS6 by inl; exact hR21).
  assert (L22 : getr R6 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS6 by inl; exact hR22).
  assert (L23 : getr R6 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS6 by inl; exact hR23).
  LeanFeed.pfeed P (PNAERP.azrE3_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 38%nat => m | 39%nat => n | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [assumption | unfold PNAERP.aligned; lia | lia]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FZ7 & MS7 & KS7 & iR1 & iR2 & iR8 & iR9 & iR10 & iR11 & iR12 & iR13 & iR14 & iR15 & iR16 & iR17 & iR18 & iR19 & iR20 & iR21 & iR22 & iR23 & I8v).
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite iR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xad314 W_ad314 r F_ad314 eq_refl D_ad314 R7ra ltac:(lia) Hr2) as MS8.
  set (W7 := fun a => (sp - 256 <= a < sp - 256 + 256) \/ (v + 8 <= a < v + 8 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB1 FF LK cr1 Aw6 M6 model6 fx6 fx7 R6 0xadb38 R7 r M7v W7 K HH6 AM6 ltac:(eapply msteps_trans; [exact MS7| exact MS8]) MG7).
  { intros a Ha N. apply FZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB1 FF 0 0 v 24 a AOB); lia| lia]. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7.
  (* [comment removed for export] *)
  assert (CHAIN : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (v <= a < v + 24) -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2.
    assert (HcB : aclient L ar LB1 FF 0 0 a) by (apply (L5SAR.aclient_consb L ar LBX FF (B, 40) 0 0 a Hc)).
    assert (NB : ~ (B <= a < B + 40)) by (exact (PNAEK.own_notclient L ar C HI LY HIok B 40 LBX FF LK cr1 Aw2 M2 _ HH2 a 0 0 Hc)).
    assert (NS : ~ in_shadow_of B 40 a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok B 40 LBX FF LK cr1 Aw2 M2 _ HH2 ltac:(lia) a 0 0 Hc)).
    rewrite FR7; [| exact Ha| unfold W7; lia]. rewrite T65; [| exact Ha| exact HcB| lia| exact NS]. rewrite FR5; [| exact Ha| unfold W5; lia].
    rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB1 FF 0 0); [exact HcB| lia]| lia]. rewrite FR3; [| exact Ha| unfold W3; lia].
    rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LBX FF 0 0); [exact Hc| lia]]. apply FR1; [exact Ha| unfold W1; lia]. }
  assert (TB7 : forall a, B <= a < B + 40 -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha. rewrite FR7; [| lia| unfold W7; lia]. rewrite T65; [| lia| unfold aclient, aclient_g; left; exists (B, 40); split; [exact BIN| cbn [fst snd]; lia]| lia|].
    2:{ intros X. pose proof (PNAEK.in_shadow_range B 40 a ltac:(lia) ltac:(lia) X). lia. }
    rewrite FR5; [| lia| unfold W5; lia]. apply PRES4; [lia| unfold aclient, aclient_g; left; exists (B, 40); split; [exact BIN| cbn [fst snd]; lia]| lia]. }
  assert (SH76 : forall j, 0 <= j < 5 -> M7 (Z_to_bv 64 (S B + j)) = M6 (Z_to_bv 64 (S B + j))).
  { intros j Hj. pose proof (PNAERF.shadow_low B 40 j ltac:(lia) ltac:(lia) ltac:(change (40 / 8) with 5; lia)) as SL.
    apply FR7; [lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
  assert (HP07 : L5CA.ahpres L ar LBX FF sp 12288 [(v, 24)] M M7).
  { apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M7).
      + intros a (Ha & Hc & Ho).
        destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBX FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1];
          (apply CHAIN; [exact Ha| exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc)| lia| intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]]).
      + pose proof ASTK6 as (_ & _ & _ & _ & SD6 & _). apply (L5.defined_grows M6 M7 _ _ MGM7). exact SD6.
      + intros a Ha Hc HM. destruct (L5SAR.rng_dec a v (v + 24)) as [IV|NV].
        * replace a with (v + (a - v)) by lia. apply (L5.defined_grows M6 M7 _ _ MGM7 ODEF6 (a - v)). lia.
        * destruct (L5SAR.aclient_cases L ar C HI LYa HIok LBX FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1];
            (rewrite CHAIN; [exact HM| exact Ha| exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc)| lia| exact NV]). }
  assert (EK07 : L5SAR.ek L ar LBX FF sp 12288 [(v, 24)] M M7).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 12288 sp 12288 [(v, 24)] [(v, 24)] M M7 HP07); [lia| lia| intros a _ Ho; exact Ho]. }
  assert (BASE7 : PMSTA.base_okA RSEGS PMA.AD M7).
  { apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [(v, 24)] M M7 EK07); [| exact BASE]. intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  apply (KONT fx7 R7 M7 model7 LK Aw6 B).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 25; 26; 27]%nat -> getr R7 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PNAERP.KS_azrE3 /\ In k' L5SAR.cs_all /\ In k' PNAERP.KS_azrE2 /\ In k' PNAERP.KS_azrE1 /\ In k' PNAERP.KS_azrE0)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[]]]]]]; (split; [inl| split; [inl| split; [inl| split; inl]]])).
      destruct Y as (Yk1 & Yk2 & Yk3 & Yk4 & Yk5). rewrite (KS7 k' Yk1), (CS6 k' Yk2), (KS5 k' Yk3), (CS4 k' Yk2), (KS3 k' Yk4), (CS2 k' Yk2), (KS1 k' Yk5). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]]]].
    + rewrite iR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite iR8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite iR23, Z_to_bv_bv_unsigned; reflexivity.
    + destruct Hk as [<-|Hk]; [rewrite (KS7 24%nat) by inl; rewrite (CS6 24%nat) by inl; rewrite hR24, Z_to_bv_bv_unsigned; reflexivity| apply CH; right; right; exact Hk].
  - unfold PNM.bvec_at, PNM.BSZ. cbn [length Z.of_nat]. change (2 ^ 0) with 1.
    split. { apply (L5C.u64_at_agree RSEGS M6 M7); [intros i Hi; apply FR7; [lia| unfold W7; lia]| lia| lia|].
             apply (PMAIS1.vis_u64 H6 M6 MV6 _ _ eq_refl); [eapply L5A.avis_sub; [exact OVIS6| lia| lia]| lia| lia| exact QV0]. }
    split. { replace (B + 40 * 1) with (B + 40) by lia. apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS6| lia| lia]| lia| lia| exact I8v]. }
    split. { replace (B + 40 * 1) with (B + 40) by lia. apply (L5C.u64_at_agree RSEGS M6 M7); [intros i Hi; apply FR7; [lia| unfold W7; lia]| lia| lia|].
             apply (PMAIS1.vis_u64 H6 M6 MV6 _ _ eq_refl); [eapply L5A.avis_sub; [exact OVIS6| lia| lia]| lia| lia| exact QV16]. }
    split; [lia|]. split; [lia|]. split; [exact Q16|].
    split. { apply (L5.defined_grows M6 M7 _ _ MGM7). intros i Hi. change (40 * 1) with 40 in Hi.
             rewrite T65; [| lia| unfold aclient, aclient_g; left; exists (B, 40); split; [exact BIN| cbn [fst snd]; lia]| lia|].
             - apply (L5.defined_grows M4 M5 _ _ MGM5 BDEF4 i Hi).
             - intros X. pose proof (PNAEK.in_shadow_range B 40 (B + i) ltac:(lia) ltac:(lia) X). lia. }
    destruct ANN6 as (ZA6 & PM6 & PA6).
    split. { unfold PMSPA.accA. apply (PMFA.accA_agree M6 M7 B 40).
             - intros x Hx. pose proof (PNAERF.S_range x ltac:(lia)) as SRx. apply FR7; [lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]].
             - apply (L5CB.aacc_of_zero M6 B (40 / 8) B 40 ZA6); [lia| lia| lia| change (40 / 8) with 5; lia]. }
    split. { apply (PNAEK.ann_agree M6 M7 B 40 40); [intros j Hj; change ((40 + 7) / 8) with 5 in Hj; apply SH76; lia| lia| lia| split; [exact ZA6| split; [exact PM6| exact PA6]]]. }
    intros i0 Hi0. assert (Ei : i0 = 0%nat) by (cbn [length] in Hi0; lia). subst i0. cbn [nth]. replace (B + 40 * Z.of_nat 0) with B by lia.
    assert (AVB : forall a n0, B <= a -> a + n0 <= B + 40 -> L5A.avis (ahid Aw2 model2) a n0) by (intros a n0 Ya1 Ya2; apply (VBLK2 B 40 a n0 BIN); lia).
    unfold PNM.bstate_at. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    split; [apply (PMF.u32_at_agree RSEGS M3 M7); [intros i Hi; apply TB7; lia| lia| lia| apply (PMAIS1.vis_u32 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact B0]]|].
    split; [apply (L5C.u64_at_agree RSEGS M3 M7); [intros i Hi; apply TB7; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact B8]]|].
    split; [apply (L5C.u64_at_agree RSEGS M3 M7); [intros i Hi; apply TB7; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact B16]]|].
    split; [apply (L5C.u8_at_agree RSEGS M3 M7); [intros i Hi; apply TB7; lia| lia| lia| apply (PNAERF.vis_u8 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact B24]]|].
    apply (L5C.u64_at_agree RSEGS M3 M7); [intros i Hi; apply TB7; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact B32]].
  - apply (PMFA.accA_agree M6 M7 v 24); [| exact ACCV6]. intros x Hx. pose proof (PNAERF.S_range x ltac:(lia)) as SRx.
    apply FR7; [lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]].
  - exact BASE7.
  - exact HP07.
  - apply (L5LZ.model_rt_trans model model6 model7); [|exact MRT7]. apply (L5LZ.model_rt_trans model model5 model6); [|exact MRT6].
    apply (L5LZ.model_rt_trans model model4 model5); [|exact MRT5]. apply (L5LZ.model_rt_trans model model3 model4); [|exact RT4].
    apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - intros x Hx. apply INC6. apply IA2. exact Hx.
  - exact AM7.
  - exact HH7.
  - exact iR10.
  - lia.
  - lia.
  - exact VB.
Qed.
End Stage.
End PNAERE.
