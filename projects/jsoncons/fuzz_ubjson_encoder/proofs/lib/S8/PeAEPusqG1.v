(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PmStep PeStepA PeStepA2 PmCertKitG PeAIss1 PeAEmbKitJ PeASrcKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCEPushSpecsA PeAEPusqP1 PeAEPusqP2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_ae600_ae604.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeAEPushF PeAEPushG1 PeAEPusqGStmts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.asan Require Import L5CoreBS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PEAEQG1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac amod := match goal with H : ?x mod ?m = 0 |- ?x mod ?m = 0 => exact H end.
Ltac sassum := match goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.
Ltac ftac := lazymatch goal with |- PEAEQP1.aligned _ _ => unfold PEAEQP1.aligned; first [amod | lia] | |- PEAEQP2.aligned _ _ => unfold PEAEQP2.aligned; first [amod | lia] end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem grow1 : PMSPA.opnew_spec RSEGS AD L ar HI -> forall (fx : FPState) R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk pl kd ln,
    ri_inv HI (PEC.enc_own (PEC.ENC b k stk d) ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 (ov + 24) -> PMSPA.aobjA FF ov 56 -> ov mod 8 = 0 ->
    PECA.enc_atA RSEGS EE L ar M ov fb (PEC.ENC b k stk d) -> Z.of_nat (length stk) = PEC.ecap k -> 0 < k <= 11 ->
    PMSTA.base_okA RSEGS AD M ->
    getr R (reg 11) = Z_to_bv 64 pk -> getr R (reg 12) = Z_to_bv 64 pl -> pk mod 4 = 0 -> pl mod 8 = 0 -> byte_at M (S pk) 0 -> byte_at M (S pl) 0 ->
    PMAEK.argp (ar_sptop ar) FF sp (ov + 32) pk 4 -> PMAEK.argp (ar_sptop ar) FF sp (ov + 32) pl 8 -> (pk + 4 <= ov \/ ov + 56 <= pk) -> (pl + 8 <= ov \/ ov + 56 <= pl) ->
    L5.u32_at RSEGS M pk kd -> L5.u64_at RSEGS M pl ln -> 0 <= kd <= 3 -> 0 <= ln <= UbjRef.MAX_ITEMS -> acredit_ok L cr (24 * PEC.ecap (k + 1)) ->
    (forall (fx8 : FPState) R8 M8 model8 Aw8 B, PEAEQGS.gmid L ar HI R M model LBX FF LK Aw cr ov b k stk sp pk pl kd ln B R8 M8 model8 Aw8 ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx8 R8 0xaecb4 M8 model8) K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xae3ec M model) K.
Proof.
  intros OPN fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk pl kd ln HH AM K0 ENT A10 AOV O8 EA LEN K11 BASE A11 A12 P14 P24 SP1 SP2 AG1 AG2 APK APL U1 U2 RKD RLN CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH. change UbjRef.MAX_ITEMS with 16777216 in RLN.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof EA as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EK, ELEN, EDEP, EKB, EBLK, EITEMS.
  change PEC.ESZ with 24 in EV32, EV40, ELEN, EBLK, EITEMS.
  destruct (EBLK ltac:(clear - K11; Lia.lia)) as (B8 & BDEF & BRNG & BACC & BANN).
  pose proof (PEAEPG1.ecap_rng11 k K11) as HC. rewrite (PEAEPG1.ecap_succ k) in CR by (clear - K11; Lia.lia).
  unfold PEAEQGS.gmid, PEAEQGS.SZ in KONT.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by (clear - K11; Lia.lia).
  remember (PEC.ecap k) as cap eqn:Ecap.
  remember (24 * cap) as SZ eqn:ESZ. remember (2 * cap) as NC eqn:ENC.
  assert (LENz : 24 * Z.of_nat (length stk) = SZ) by (clear - LEN ESZ; Lia.lia). rewrite LENz in EV32, BACC, BANN.
  set (len := Z.of_nat (length stk)) in *.
  set (LB := PEC.enc_own (PEC.ENC b k stk d) ++ LBX) in *.
  assert (ELB : LB = (b, SZ) :: LBX).
  { subst LB. unfold PEC.enc_own, PEC.ESZ. cbn [PEC.en_k PEC.en_b]. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; clear - K11; Lia.lia). rewrite <- Ecap, <- ESZ. reflexivity. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, SZ) LB) by (rewrite ELB; left; reflexivity).
  destruct (PMAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b SZ HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKA.aobj_of_aobjA FF ov 56 AOV O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ov 56 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  destruct (PMAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 (ov + 32) pk 4 HH ASTK ltac:(lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6).
  pose proof (Pa5 b SZ BIN) as PaB.
  destruct (PMAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 (ov + 32) pl 8 HH ASTK ltac:(lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & Pb2 & Pb3 & Pb4 & Pb5 & Pb6).
  pose proof (Pb5 b SZ BIN) as PbB.
  assert (VBLK : ov + 56 <= b \/ b + SZ <= ov).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof BASE as (IC & _). cbn [pa_rw_lo PeCLayoutA.CADDR_A] in IC.
  assert (X0 : L5.img_clear MV 65536 1286144) by (apply L5A.img_clear_mrestrict; exact IC).
  assert (X1 : L5.u64_at RSEGS MV 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1317368 2147450880 (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X4 : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (PEAEPF.stack_zeros12 M sp STKSH A16). exact Hi.
    assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (X5 : L5KA.zeros_at MV (ov / 8 + 2147450880) 7).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ov 56 HH AOV O8 ltac:(lia) ltac:(reflexivity) EACC). }
  assert (X6 : L5.u64_at RSEGS MV (ov + 24) b) by (apply (proj2 (L5A.u64_at_vis H M (ov + 24) b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact EV24).
  assert (X7 : L5.u64_at RSEGS MV (ov + 32) (b + SZ)) by (apply (proj2 (L5A.u64_at_vis H M (ov + 32) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact EV32).
  assert (X8 : L5.u64_at RSEGS MV (ov + 40) (b + SZ)) by (apply (proj2 (L5A.u64_at_vis H M (ov + 40) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact EV40).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R (reg 22))) as UR22.

  assert (PS : exists fx1 R1 M1v, mem_grows MV M1v
    /\ (forall a : word, ~ ((sp - 128) <= bv_unsigned a < (sp - 128) + 128) -> M1v a = MV a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((sp - 128) <= i < (sp - 128) + 128) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae3ec MV) (st fx1 R1 0x131ec0 M1v)
        /\ (forall x, In x PEAEQP2.KS_aeqS1 -> getr R1 (reg x) = getr R (reg x))
        /\ getr R1 (reg 1) = Z_to_bv 64 716508 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R1 (reg 8) = Z_to_bv 64 NC
        /\ getr R1 (reg 9) = Z_to_bv 64 (ov + 24) /\ getr R1 (reg 10) = Z_to_bv 64 (2 * SZ) /\ getr R1 (reg 11) = Z_to_bv 64 (32 * NC)
        /\ getr R1 (reg 12) = Z_to_bv 64 384307168202282325 /\ getr R1 (reg 13) = Z_to_bv 64 12297829382473034411 /\ getr R1 (reg 14) = Z_to_bv 64 768614336404564651
        /\ getr R1 (reg 18) = Z_to_bv 64 pl /\ getr R1 (reg 19) = Z_to_bv 64 pk /\ getr R1 (reg 20) = Z_to_bv 64 SZ
        /\ getr R1 (reg 21) = Z_to_bv 64 (((ov + 32) / 8) + 2147450880) /\ getr R1 (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M1v (sp - 128) (ov + 32) /\ L5.u64_at RSEGS M1v (sp - 120) 714076 /\ L5.u64_at RSEGS M1v (sp - 72) (ov + 24)
        /\ L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22))) /\ L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20))) /\ L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18))) /\ L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1))))).
  { clear KONT.
    destruct KC as [Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]]]]]]; subst k; subst cap; subst SZ NC.
    - change (24 * PEC.ecap 1) with 24 in X7, X8. pose proof (PEAEQP2.aeqS1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 2) with 48 in X7, X8. pose proof (PEAEQP2.aeqS2_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 3) with 96 in X7, X8. pose proof (PEAEQP2.aeqS3_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 4) with 192 in X7, X8. pose proof (PEAEQP2.aeqS4_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 5) with 384 in X7, X8. pose proof (PEAEQP2.aeqS5_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 6) with 768 in X7, X8. pose proof (PEAEQP2.aeqS6_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 7) with 1536 in X7, X8. pose proof (PEAEQP2.aeqS7_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 8) with 3072 in X7, X8. pose proof (PEAEQP2.aeqS8_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 9) with 6144 in X7, X8. pose proof (PEAEQP2.aeqS9_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 10) with 12288 in X7, X8. pose proof (PEAEQP2.aeqS10_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P.
    - change (24 * PEC.ecap 11) with 24576 in X7, X8. pose proof (PEAEQP2.aeqS11_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 38%nat => kd | 39%nat => ln | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]). exact P. }
  destruct PS as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & sR1 & sR2 & sR8 & sR9 & sR10 & sR11 & sR12 & sR13 & sR14 & sR18 & sR19 & sR20 & sR21 & sR22
                  & T128 & T120 & T72 & T64 & T56 & T48 & T40 & T32 & T24 & T16 & T8).
  clear X0 X1 X2 X3 X4 X5 X6 X7 X8 KC FSIMG.
  assert (HSZ : 24 <= SZ <= 24576) by (clear - HC ESZ; Lia.lia).
  assert (SZ8 : SZ mod 8 = 0) by (clear - ESZ; Lia.lia).
  set (W1 := fun a => sp - 128 <= a < sp - 128 + 128).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xae3ec R1 0x131ec0 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.

  unfold PMSPA.opnew_spec in OPN. cbn [pa_opnew PeCLayoutA.CADDR_A] in OPN.
  apply (OPN fx1 R1 M1 model1 K LB FF LK Aw cr (2 * SZ) (sp - 128) 716508 HH1 AM1 K0).
  { rewrite L5K.rl10. exact sR10. }
  { lia. }
  { replace (2 * SZ) with (24 * NC) by lia. exact CR. }
  { rewrite L5K.rl1. exact sR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact sR2. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M1 M1 sp 12288 128 (16 + 4096) (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1) (fun x X => X)); [lia| lia| lia|].
    replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx2 R2 M2 model2 Aw2 B RB RP2 FRESH HP2 MRT2 IA2 AM2 HH2.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP2. change (16 + 4096) with 4112 in HP2. rewrite L5K.rl10 in RB.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH). pose proof QR as (Q0 & Q1 & Q16 & _ & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1.
  set (LB2 := (B, 2 * SZ) :: LB) in *. set (cr2 := adebit L cr (2 * SZ)) in *.
  pose proof AM2 as (Mh2 & MI2).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 128) 4112 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP2). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 4240 <= a < sp) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N. rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]]. apply FR1; [exact Ha| unfold W1; lia]. }
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK cr Aw M1 M1 M2 _ sp 12288 (sp - 128) 4112 [] HH1 (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1) (fun x X => X) HP2); lia. }
  assert (EK2 : L5SAR.ek L ar LB FF sp 12288 [] M M2).
  { apply (PEAEPF.ek_of_keep L ar HI LB FF LK cr Aw M _ sp [] M M2 HH). intros a Ha Hc _.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; (apply T20; [exact Ha| exact (L5SAR.aclient_00 L ar LB FF sp 12288 a Hc)| lia]). }
  assert (BASE2 : PMSTA.base_okA RSEGS AD M2).
  { apply (PMASK.base_keep L ar C LY LB FF sp 12288 [] M M2 EK2); [| exact BASE]. intros a Ha. unfold L5.outside. intros rg []. }
  pose proof (PMAEK.arg_fresh_apart ar M FF LK sp 12288 (ov + 32) pk 4 B (2 * SZ) ASTK ltac:(lia) AG1 QFA Q4 ltac:(lia)) as PB1.
  pose proof (PMAEK.arg_fresh_apart ar M FF LK sp 12288 (ov + 32) pl 8 B (2 * SZ) ASTK ltac:(lia) AG2 QFA Q4 ltac:(lia)) as PB2.
  assert (VBf : ov + 56 <= B \/ B + 2 * SZ <= ov).
  { destruct AOV as (f & Hf & Yv1 & Yv2). destruct (QFA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; [right; lia| left; lia]. }
  assert (bB : B + 2 * SZ <= b \/ b + SZ <= B) by (destruct (QAP (b, SZ) BIN) as [Y|Y]; cbn [fst snd] in Y; lia).

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 ov 56 sp 12288 HH2 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  pose proof BASE2 as (IC2 & _). cbn [pa_rw_lo PeCLayoutA.CADDR_A] in IC2.
  assert (Y0 : L5.img_clear MV2 65536 1286144) by (apply L5A.img_clear_mrestrict; exact IC2).
  assert (Y1 : L5.u64_at RSEGS MV2 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1317368 2147450880 (VIMG2 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1317376 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1317376 1 (VIMG2 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  assert (STKSH2 : shadow_zero M2 (sp - 12288) 1536).
  { intros j Hj. pose proof (PEAEPF.S_add8 (sp - 12288) j) as E. pose proof (PEAEPF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T20; [rewrite <- E; apply STKSH; exact Hj| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia]. }
  assert (Y4 : L5KA.zeros_at MV2 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2). apply (PEAEPF.stack_zeros12 M2 sp STKSH2 A16). exact Hi.
    assert (AV : L5A.avis H2 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH2 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV2 : PMSPA.accA M2 ov 56).
  { apply (PMFA.accA_agree M M2 ov 56); [| exact EACC]. intros x Hx. pose proof (PEAEPF.S_range x ltac:(lia)) as SRx. apply T20; [lia| | lia].
    exact (PMAEK.frame_sh_client L ar FF ov 56 x LB 0 0 AOV Hx). }
  assert (Y5 : L5KA.zeros_at MV2 (ov / 8 + 2147450880) 7).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 ov 56 HH2 AOV O8 ltac:(lia) ltac:(reflexivity) ACCV2). }
  assert (TV : forall a, ov <= a < ov + 56 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 ov 56 a AOB); lia| lia]. }
  assert (Y7 : L5.u64_at RSEGS MV2 (ov + 24) b).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (ov + 24) b ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact EV24]. }
  assert (Y8 : L5.u64_at RSEGS MV2 (ov + 32) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (ov + 32) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact EV32]. }
  assert (Y9 : L5.u64_at RSEGS MV2 (ov + 40) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (ov + 40) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact EV40]. }
  destruct (PMAEK.arg_vis L ar C HI LY HIok LB2 FF LK cr2 Aw2 M2 model2 sp 12288 (ov + 32) pk 4 HH2 ASTK2 ltac:(lia) AG1 ltac:(lia)) as (AV1 & AVS1).
  destruct (PMAEK.arg_vis L ar C HI LY HIok LB2 FF LK cr2 Aw2 M2 model2 sp 12288 (ov + 32) pl 8 HH2 ASTK2 ltac:(lia) AG2 ltac:(lia)) as (AV2 & AVS2).
  assert (TP : forall x, pk <= x < pk + 4 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros x Hx. apply T20; [lia| replace x with (pk + (x - pk)) by lia; apply Pa6; lia| lia]. }
  assert (TP2 : forall x, pl <= x < pl + 8 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros x Hx. apply T20; [lia| replace x with (pl + (x - pl)) by lia; apply Pb6; lia| lia]. }
  assert (TPS2 : byte_at M2 (S pl) 0).
  { pose proof (PEAEPF.S_range pl ltac:(lia)) as SRp. unfold byte_at in *. rewrite T20; [exact SP2| lia| | lia].
    exact (PMAEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 (ov + 32) pl 8 HH ASTK ltac:(lia) AG2 ltac:(lia) LB 0 0). }
  assert (Y11 : L5.u64_at RSEGS MV2 pl ln).
  { apply (proj2 (L5A.u64_at_vis H2 M2 pl ln AV2 ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TP2; lia| lia| lia| exact U2]. }
  assert (Y13 : L5KA.zeros_at MV2 (pl / 8 + 2147450880) 1).
  { apply PEAEPF.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact TPS2|].
    pose proof (AVS2 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (TPS : byte_at M2 (S pk) 0).
  { pose proof (PEAEPF.S_range pk ltac:(lia)) as SRp. unfold byte_at in *. rewrite T20; [exact SP1| lia| | lia].
    exact (PMAEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 (ov + 32) pk 4 HH ASTK ltac:(lia) AG1 ltac:(lia) LB 0 0). }
  assert (Y10 : L5.u32_at RSEGS MV2 pk kd).
  { apply (proj2 (L5A.u32_at_vis H2 M2 pk kd AV1 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply TP; lia| lia| lia| exact U1]. }
  assert (Y12 : L5KA.zeros_at MV2 (pk / 8 + 2147450880) 1).
  { apply PEAEPF.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact TPS|].
    pose proof (AVS1 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }

  assert (BIN2 : In (B, 2 * SZ) LB2) by (left; reflexivity).
  assert (E8 : SZ / 8 = 3 * cap) by (rewrite ESZ; apply PEAEPF.d24).
  assert (E16 : 2 * SZ / 8 = 6 * cap) by (replace (2 * SZ) with (24 * (2 * cap)) by lia; rewrite PEAEPF.d24; lia).
  assert (Y14 : L5KA.zeros_at MV2 ((B + SZ) / 8 + 2147450880) 3).
  { destruct QSH as (ZB & _). rewrite (PMAEK.sh_idx B SZ) by (clear - Q16 SZ8; lia). intros i Hi.
    assert (AV : L5A.avis H2 (S B + SZ / 8 + i) 1).
    { apply (VBSH2 B (2 * SZ) _ 1 BIN2). intros j Hj. replace (S B + SZ / 8 + i + j) with (S B + (SZ / 8 + i + j)) by lia.
      apply PMAEK.sh_in; [lia| lia| lia|]. rewrite E8, E16. lia. }
    unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
    - replace (S B + SZ / 8 + i) with (S B + (SZ / 8 + i)) by lia. apply ZB. rewrite E8, E16. lia.
    - pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y15 : L5.writable RSEGS MV2 (B + SZ) 24).
  { apply (proj2 (L5A.writable_vis H2 M2 (B + SZ) 24 (VBLK2 B (2 * SZ) (B + SZ) 24 BIN2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 B (2 * SZ)); [exact QDEF| lia| lia]| lia| lia]. }

  assert (TS : forall a v0, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
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
  pose proof (TS (sp - 120) _ ltac:(lia) ltac:(lia) T120) as Z120.
  pose proof (TS (sp - 128) _ ltac:(lia) ltac:(lia) T128) as Z128.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite CS2 by inl; exact sR2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 NC) by (rewrite CS2 by inl; exact sR8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 (ov + 24)) by (rewrite CS2 by inl; exact sR9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 pl) by (rewrite CS2 by inl; exact sR18).
  assert (J19 : getr R2 (reg 19) = Z_to_bv 64 pk) by (rewrite CS2 by inl; exact sR19).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 SZ) by (rewrite CS2 by inl; exact sR20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 ((ov + 32) / 8 + 2147450880)) by (rewrite CS2 by inl; exact sR21).
  assert (J22 : getr R2 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact sR22).
  pose proof (PEAEQP1.aeqG_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 37%nat => SZ | 38%nat => kd | 39%nat => ln | 40%nat => B | 42%nat => NC | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8 & gR10 & gR11 & gR12 & gR13 & gR14 & gR19
                 & U176 & U168 & U152 & U144 & U136 & U128 & U120 & U88 & GS16 & GS8 & GS0 & U80 & U96 & U104 & U8 & U16 & U24 & U32 & U40 & U48 & U56 & U64 & U72).
  replace (SZ + B) with (B + SZ) in U88, GS16, GS8, GS0, U96 by lia.
  clear Y0 Y1 Y2 Y3 Y4 Y5 Y7 Y8 Y9 Y10 Y12 Y11 Y13 Y14 Y15 TS Z8 Z16 Z24 Z32 Z40 Z48 Z56 Z64 Z72 Z120 Z128.
  set (W3 := fun a => (sp - 176 <= a < sp - 176 + 176) \/ (B + SZ + 0 <= a < B + SZ + 0 + 24)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 fx2 fx3 R2 0xaeedc R3 0x7c400 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [|lia]. unfold aclientw, aclient_g. left. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  pose proof AM3 as (Mh3 & MI3).
  assert (ASTK3 : L5CA.astk ar M3 sp 12288) by (apply (L5SAR.astk_grows ar M2 M3 sp 12288 ASTK2 MGM3)).
  assert (EK3 : L5SAR.ek L ar LB2 FF sp 12288 [(B + SZ, 24)] M2 M3).
  { apply (PEAEPF.ek_of_keep L ar HI LB2 FF LK cr2 Aw2 M2 _ sp _ M2 M3 HH2). intros a Ha Hc Ho. apply FR3; [exact Ha|].
    intros [X|X]; [| apply (Ho (B + SZ, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]].
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 _ sp 12288 a HH2 SPT Hc) as [Z1|Z1]; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS AD M3).
  { apply (PMASK.base_keep L ar C LY LB2 FF sp 12288 [(B + SZ, 24)] M2 M3 EK3); [| exact BASE2].
    intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (BDEF3 : L5.defined M3 B (2 * SZ)) by (apply (L5.defined_grows M2 M3 _ _ MGM3); exact QDEF).

  assert (BIN2b : In (b, SZ) LB2) by (right; exact BIN).
  assert (ANN5 : HAJ.ann_shadow M3 b SZ SZ).
  { apply (PMAEK.ann_agree M M3 b SZ SZ); [| lia| lia| exact BANN| exact SZ8].
    intros j Hj. pose proof (PEAEPF.shadow_low b SZ j ltac:(lia) ltac:(lia) Hj) as SL.
    rewrite FR3; [| lia| unfold W3; intros [XW|XW]; [lia| destruct Q5 as (_ & [YW|YW] & _); lia]].
    apply T20; [lia| | lia]. unfold aclient, aclient_g. do 6 right. exists (b, SZ). split; [exact BIN| cbn [fst snd]; apply PMAEK.sh_in; lia]. }
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD PeLayoutA.AADDR_A PeCLayoutA.CAADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx3 R3 M3 model3 LB2 FF LK cr2 Aw2 K b SZ SZ SZ); clear ANN.
  { exact HH3. }
  { exact Mh3. }
  { exact MI3. }
  { rewrite L5K.rl10. exact gR10. }
  { rewrite L5K.rl11. exact gR11. }
  { rewrite L5K.rl12. exact gR12. }
  { rewrite L5K.rl13. exact gR13. }
  { exact BIN2b. }
  { exact Bq4. }
  { lia. }
  { lia. }
  { exact ANN5. }
  { rewrite L5K.rl4, (KS3 4%nat) by inl. rewrite CS2 by inl. rewrite (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, gR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, gR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M3 M3 sp 12288 176 2304 ASTK3 (fun x X => X)); [lia| lia| lia|].
    replace (sp - 176) with (sp + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx6 R6 M6 model6 Aw6 RP6 ANN6 KEEP6 DSH6 SCR6 MRT6 INC6 MI6 HH6.
  rewrite L5K.rl2, gR2, L5.unsigned_lit in KEEP6, SCR6 by lia. rewrite L5K.rl1, gR1.
  assert (AM6 : L5CA.amodel_ok Aw6 model6) by (split; [rewrite (L5LZ.model_rt_halted model3 model6 MRT6); exact Mh3| exact MI6]).
  pose proof AM6 as (Mh6 & _).
  assert (CS6 : forall k0, In k0 L5SAR.cs_all -> getr R6 (reg k0) = getr R3 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R3 R6 k0 RP6 Hk)).
  assert (ASTK6 : L5CA.astk ar M6 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw2 M3 M3 M6 _ sp 12288 (sp - 176) 2304 HH3 ASTK3 (fun x X => X)).
    - intros a Ha Hs Hns. apply KEEP6; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PMAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR6.
    - lia. - lia. - lia. }
  assert (T65 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2480 <= a < sp - 176) -> ~ in_shadow_of b SZ a -> M6 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply KEEP6; [exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc| lia]| exact N2]. }
  assert (T64m : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2480 <= a < sp) -> ~ in_shadow_of b SZ a -> ~ (B + SZ <= a < B + SZ + 24) -> M6 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2 N3. rewrite T65; [| exact Ha| exact Hc| lia| exact N2]. apply FR3; [exact Ha| unfold W3; lia]. }
  assert (EK6 : L5SAR.ek L ar LB2 FF sp 12288 [(S b, 3 * cap)] M3 M6).
  { apply (PEAEPF.ek_of_keep L ar HI LB2 FF LK cr2 Aw2 M3 _ sp _ M3 M6 HH3). intros a Ha Hc Ho.
    assert (NS : ~ in_shadow_of b SZ a).
    { intros X. apply (Ho (S b, 3 * cap)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. unfold in_shadow_of, S in X. unfold S. clear - X B8 HC ESZ.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply KEEP6; [exact Ha| apply (L5SAR.aclient_mono L ar LB2 FF sp 12288 (sp - 176) 2304 a Hc); intros x Hx; lia| exact NS]. }
  assert (BASE6 : PMSTA.base_okA RSEGS AD M6).
  { apply (PMASK.base_keep L ar C LY LB2 FF sp 12288 [(S b, 3 * cap)] M3 M6 EK6); [| exact BASE3].
    intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. pose proof (PEAEPF.S_range b ltac:(lia)) as SR. lia. }

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
  set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 ov 56 sp 12288 HH6 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF6 & OVIS6 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as ST6. rewrite (L5A.aly_segs L C LYa) in ST6.
  pose proof (L5A.statics_facts L C M6 LYa ST6) as (GOT6 & CSB6 & CUAR6 & _).
  pose proof BASE6 as (IC6 & _). cbn [pa_rw_lo PeCLayoutA.CADDR_A] in IC6.
  assert (Z0' : L5.img_clear MV6 65536 1286144) by (apply L5A.img_clear_mrestrict; exact IC6).
  assert (Z1' : L5.u64_at RSEGS MV6 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H6 M6 1317368 2147450880 (VIMG6 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB6).
  assert (Z2' : L5.u32_at RSEGS MV6 1317376 1) by (apply (proj2 (L5A.u32_at_vis H6 M6 1317376 1 (VIMG6 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR6).
  assert (Z3' : L5.writable RSEGS MV6 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H6 M6 (sp - 4096) 4096 (VIS6 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M6 sp 12288); [exact ASTK6| lia| lia| lia]. }
  assert (STKSH6 : shadow_zero M6 (sp - 12288) 1536).
  { intros j Hj. pose proof (PEAEPF.S_add8 (sp - 12288) j) as E. pose proof (PEAEPF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T64m; [rewrite <- E; apply STKSH2; exact Hj| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia| apply (PMAEK.sh_apart b SZ); lia| lia]. }
  assert (Z4' : L5KA.zeros_at MV6 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV6. rewrite (AsanAcct.mrestrict_visible H6 M6). apply (PEAEPF.stack_zeros12 M6 sp STKSH6 A16). exact Hi.
    assert (AV : L5A.avis H6 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH6 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV6 : PMSPA.accA M6 ov 56).
  { apply (PMFA.accA_agree M2 M6 ov 56); [| exact ACCV2]. intros x Hx. pose proof (PEAEPF.S_range x ltac:(lia)) as SRx. apply T64m; [lia| | lia| apply (PMAEK.sh_apart b SZ x); lia| lia].
    exact (PMAEK.frame_sh_client L ar FF ov 56 x LB2 0 0 AOV Hx). }
  assert (Z5' : L5KA.zeros_at MV6 (ov / 8 + 2147450880) 7).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 ov 56 HH6 AOV O8 ltac:(lia) ltac:(reflexivity) ACCV6). }
  assert (TV6 : forall a, ov <= a < ov + 56 -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite T64m; [apply TV; lia| lia| apply (L5SAR.obj_client L ar LB2 FF 0 0 ov 56 a AOB); lia| lia| | lia].
    intros X. pose proof (PMAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). destruct OBIG as [YW|YW]; lia. }
  assert (Z7' : L5.u64_at RSEGS MV6 (ov + 24) b).
  { apply (proj2 (L5A.u64_at_vis H6 M6 (ov + 24) b ltac:(eapply L5A.avis_sub; [exact OVIS6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M6); [intros i Hi; apply TV6; lia| lia| lia| exact EV24]. }
  assert (Z8' : L5.u64_at RSEGS MV6 (ov + 32) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H6 M6 (ov + 32) _ ltac:(eapply L5A.avis_sub; [exact OVIS6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M6); [intros i Hi; apply TV6; lia| lia| lia| exact EV32]. }
  assert (Z9' : L5.u64_at RSEGS MV6 (ov + 40) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H6 M6 (ov + 40) _ ltac:(eapply L5A.avis_sub; [exact OVIS6| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M6); [intros i Hi; apply TV6; lia| lia| lia| exact EV40]. }
  assert (SHB6 : forall j, 0 <= j < (2 * SZ) / 8 -> M6 (Z_to_bv 64 (S B + j)) = M2 (Z_to_bv 64 (S B + j))).
  { intros j Hj. pose proof (PEAEPF.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. apply T64m; [lia| | lia| |].
    - unfold aclient, aclient_g. do 6 right. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; apply PMAEK.sh_in; lia].
    - intros X. unfold in_shadow_of in X. pose proof (PMAEK.sh_in B (2 * SZ) j ltac:(clear - Q16; lia) ltac:(clear - SZ8; lia) ltac:(clear - Q0; lia) Hj) as Y. unfold in_shadow_of in Y.
      clear - X Y bB Bq0 Q0 B8 Q16 HSZ. unfold S, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
    - intros X. destruct Q5 as (_ & [YW|YW] & _); lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (QSH6 : shadow_zero M6 B (2 * SZ / 8)).
  { destruct QSH as (ZB & _). intros j Hj. unfold byte_at. rewrite SHB6 by exact Hj. apply ZB. exact Hj. }
  assert (BDEF6 : L5.defined M6 B (2 * SZ)).
  { intros i Hi. rewrite T65; [apply BDEF3; exact Hi| lia| | lia|].
    - unfold aclient, aclient_g. left. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; lia].
    - intros X. pose proof (PMAEK.in_shadow_range b SZ (B + i) ltac:(lia) ltac:(lia) X). destruct Q5 as (_ & [YW|YW] & _); lia. }
  assert (Y14' : L5KA.zeros_at MV6 ((B + SZ) / 8 + 2147450880) 3).
  { rewrite (PMAEK.sh_idx B SZ) by (clear - Q16 SZ8; lia). intros i Hi.
    assert (AV : L5A.avis H6 (S B + SZ / 8 + i) 1).
    { apply (VBSH6 B (2 * SZ) _ 1 BIN2). intros j Hj. replace (S B + SZ / 8 + i + j) with (S B + (SZ / 8 + i + j)) by lia.
      apply PMAEK.sh_in; [lia| lia| lia|]. rewrite E8, E16. lia. }
    unfold MV6. rewrite (AsanAcct.mrestrict_visible H6 M6).
    - replace (S B + SZ / 8 + i) with (S B + (SZ / 8 + i)) by lia. apply QSH6. rewrite E8, E16. lia.
    - pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y15' : L5.writable RSEGS MV6 (B + SZ) 24).
  { apply (proj2 (L5A.writable_vis H6 M6 (B + SZ) 24 (VBLK6 B (2 * SZ) (B + SZ) 24 BIN2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M6 B (2 * SZ)); [exact BDEF6| lia| lia]| lia| lia]. }
  assert (TS6 : forall a v0, sp - 176 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v0 -> L5.u64_at RSEGS MV6 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H6 M6 a v0 (VIS6 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M3); [intros i Hi; apply T65; [lia| apply L5SAR.stack_client; lia| lia|]| lia| lia|].
    - intros XS. pose proof (PMAEK.in_shadow_range b SZ i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply VIS2; lia| lia| lia| exact X]. }
  pose proof (TS6 (sp - 8) _ ltac:(lia) ltac:(lia) U8) as W8x.
  pose proof (TS6 (sp - 16) _ ltac:(lia) ltac:(lia) U16) as W16x.
  pose proof (TS6 (sp - 24) _ ltac:(lia) ltac:(lia) U24) as W24x.
  pose proof (TS6 (sp - 32) _ ltac:(lia) ltac:(lia) U32) as W32x.
  pose proof (TS6 (sp - 40) _ ltac:(lia) ltac:(lia) U40) as W40x.
  pose proof (TS6 (sp - 48) _ ltac:(lia) ltac:(lia) U48) as W48x.
  pose proof (TS6 (sp - 56) _ ltac:(lia) ltac:(lia) U56) as W56x.
  pose proof (TS6 (sp - 64) _ ltac:(lia) ltac:(lia) U64) as W64x.
  pose proof (TS6 (sp - 72) _ ltac:(lia) ltac:(lia) U72) as W72x.
  pose proof (TS6 (sp - 80) _ ltac:(lia) ltac:(lia) U80) as W80x.
  pose proof (TS6 (sp - 88) _ ltac:(lia) ltac:(lia) U88) as W88x.
  pose proof (TS6 (sp - 96) _ ltac:(lia) ltac:(lia) U96) as W96x.
  pose proof (TS6 (sp - 104) _ ltac:(lia) ltac:(lia) U104) as W104x.
  pose proof (TS6 (sp - 120) _ ltac:(lia) ltac:(lia) U120) as W120x.
  pose proof (TS6 (sp - 128) _ ltac:(lia) ltac:(lia) U128) as W128x.
  pose proof (TS6 (sp - 136) _ ltac:(lia) ltac:(lia) U136) as W136x.
  pose proof (TS6 (sp - 144) _ ltac:(lia) ltac:(lia) U144) as W144x.
  pose proof (TS6 (sp - 152) _ ltac:(lia) ltac:(lia) U152) as W152x.
  pose proof (TS6 (sp - 168) _ ltac:(lia) ltac:(lia) U168) as W168x.
  pose proof (TS6 (sp - 176) _ ltac:(lia) ltac:(lia) U176) as W176x.
  assert (L2 : getr R6 (reg 2) = Z_to_bv 64 (sp - 176)) by (rewrite CS6 by inl; exact gR2).
  assert (L8 : getr R6 (reg 8) = Z_to_bv 64 (sp - 104)) by (rewrite CS6 by inl; exact gR8).
  assert (L9 : getr R6 (reg 9) = Z_to_bv 64 (ov + 24)) by (rewrite CS6 by inl; rewrite (KS3 9%nat) by inl; exact J9).
  assert (L18 : getr R6 (reg 18) = Z_to_bv 64 pl) by (rewrite CS6 by inl; rewrite (KS3 18%nat) by inl; exact J18).
  assert (L19 : getr R6 (reg 19) = Z_to_bv 64 2147450880) by (rewrite CS6 by inl; exact gR19).
  assert (L20 : getr R6 (reg 20) = Z_to_bv 64 SZ) by (rewrite CS6 by inl; rewrite (KS3 20%nat) by inl; exact J20).
  assert (L21 : getr R6 (reg 21) = Z_to_bv 64 ((ov + 32) / 8 + 2147450880)) by (rewrite CS6 by inl; rewrite (KS3 21%nat) by inl; exact J21).
  assert (L22 : getr R6 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS6 by inl; rewrite (KS3 22%nat) by inl; exact J22).
  pose proof (PEAEQP1.aeqH_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 35%nat => pl | 36%nat => b | 37%nat => SZ | 38%nat => kd | 39%nat => ln | 40%nat => B | 42%nat => NC | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [ftac | sassum | lia | assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FZ7 & MS7 & KS7 & iR1 & iR2 & iR10 & iR11 & iR12 & iR18
                 & I8 & I16 & I24 & I32 & I40 & I48 & I56 & I64 & I120 & I128 & I136 & I144 & I152 & I104 & I96 & I88 & I80 & I72).
  clear Z0' Z1' Z2' Z3' Z4' Z5' Z7' Z8' Z9' Y14' Y15' TS6 W8x W16x W24x W32x W40x W48x W56x W64x W72x W80x W88x W96x W104x W120x W128x W136x W144x W152x W168x W176x.
  set (W7 := fun a => sp - 176 <= a < sp - 176 + 176).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 fx6 fx7 R6 0xaef64 R7 0x78618 M7v W7 K HH6 AM6 MS7 MG7).
  { intros a Ha N. apply FZ7; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W7 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7.
  pose proof AM7 as (Mh7 & MI7).
  assert (ASTK7 : L5CA.astk ar M7 sp 12288) by (apply (L5SAR.astk_grows ar M6 M7 sp 12288 ASTK6 MGM7)).
  assert (EK7 : L5SAR.ek L ar LB2 FF sp 12288 [] M6 M7).
  { apply (PEAEPF.ek_of_keep L ar HI LB2 FF LK cr2 Aw6 M6 _ sp [] M6 M7 HH6). intros a Ha Hc _.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 _ sp 12288 a HH6 SPT Hc) as [Z1|Z1]; (apply FR7; [exact Ha| unfold W7; lia]). }
  assert (BASE7 : PMSTA.base_okA RSEGS AD M7).
  { apply (PMASK.base_keep L ar C LY LB2 FF sp 12288 [] M6 M7 EK7); [| exact BASE6]. intros a Ha. unfold L5.outside. intros rg []. }
  assert (HHb : ri_inv HI ((b, SZ) :: LBX) FF LK cr Aw M (vml_of model)) by (rewrite <- ELB; exact HH).

  assert (TB7 : forall a, b <= a < b + SZ -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite FR7; [| lia| unfold W7; lia].
    assert (Ca : forall LBz, In (b, SZ) LBz -> aclient L ar LBz FF 0 0 a) by (intros LBz Hin; unfold aclient, aclient_g; left; exists (b, SZ); split; [exact Hin| cbn [fst snd]; lia]).
    rewrite T64m; [| lia| apply Ca; exact BIN2b| lia| | lia].
    2:{ intros X. pose proof (PMAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). destruct Bq6 as [YW|YW]; lia. }
    apply T20; [lia| apply Ca; exact BIN| lia]. }
  assert (BDEF7 : L5.defined M7 b SZ).
  { intros i Hi. rewrite TB7 by lia. apply BDEF. exact Hi. }
  destruct (PMCG.rdn_some RSEGS M7 (Z.to_nat SZ) b ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN & Lbs).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply BDEF7. lia. }

  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as MCP. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MCP.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memcpy L C LYa), (L5A.aly_scr_mem L C LYa) in MCP.
  assert (SP160 : bv_unsigned (getr R7 2%bv) = sp - 160) by (rewrite L5K.rl2, iR2; apply L5.unsigned_lit; lia).
  assert (QSH7 : shadow_zero M7 B (2 * SZ / 8)).
  { intros j Hj. pose proof (PEAEPF.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at. rewrite FR7; [apply QSH6; exact Hj| lia| unfold W7; lia]. }
  assert (BSH7 : shadow_zero M7 b (SZ / 8)).
  { destruct ANN6 as (ZA6 & _). intros j Hj. pose proof (PEAEPF.shadow_low b SZ j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at. rewrite FR7; [apply ZA6; exact Hj| lia| unfold W7; lia]. }
  apply (MCP fx7 R7 M7 model7 LB2 FF LK cr2 Aw6 B b SZ bs K); clear MCP.
  { split; [exact HH7|]. split; [exact Mh7|]. split; [exact MI7|].
    split; [rewrite L5K.rl10; exact iR10|]. split; [rewrite L5K.rl12; exact iR12|]. split; [lia|].
    split; [rewrite L5K.rl4, (KS7 4%nat) by inl; rewrite CS6 by inl; rewrite (KS3 4%nat) by inl; rewrite CS2 by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    split; [rewrite L5K.rl1, iR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
    split. { rewrite SP160. apply (L5SAR.astack_ok_of_astk L ar C LYa M7 M7 sp 12288 160 2560 ASTK7 (fun x X => X)); [lia| lia| lia|].
             replace (sp - 160) with (sp + (-10) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    split. { apply (L5CB.aacc_of_zero M7 B (2 * SZ / 8) B SZ QSH7); [lia| lia| lia|]. rewrite E16. lia. }
    split. { intros i Hi. rewrite SP160. unfold aclientw, aclient_g. left. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; lia]. }
    split. { intros i m0 Hi Hm. apply (L5C.writable_of_defined RSEGS M7 B (2 * SZ)); [apply (L5.defined_grows M6 M7 _ _ MGM7); exact BDEF6| lia| lia| lia| lia]. }
    split; [exact K0|]. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. destruct Q5 as (_ & [YW|YW] & _); lia. }
  { rewrite L5K.rl11. exact iR11. }
  { apply (L5CB.aacc_of_zero M7 b (SZ / 8) b SZ BSH7); [lia| lia| lia|]. rewrite E8. lia. }
  { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. destruct Bq6 as [YW|YW]; lia. }
  { intros i Hi. right. rewrite SP160. unfold aclient, aclient_g. left. exists (b, SZ). split; [exact BIN2b| cbn [fst snd]; lia]. }
  { exact RDN. }
  { intros _; lia. }
  intros R8 M8 model8 mR10' RP8 BYTES8 PRES8 SDEF8 RT8 MI8 HH8. rewrite SP160 in PRES8, SDEF8. rewrite L5K.rl1, iR1.
  assert (Mh8 : m_halted model8 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT8); exact Mh7).
  assert (CS8 : forall k0, In k0 L5SAR.cs_all -> getr R8 (reg k0) = getr R7 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R7 R8 k0 RP8 Hk)).
  assert (ASTK8 : L5CA.astk ar M8 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw6 M7 M7 M8 _ sp _ (sp - 160) 2560 HH7 ASTK7 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES8. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF8.
    - lia. - lia. - lia. }

  assert (COPY : forall i, 0 <= i < SZ -> M7 (Z_to_bv 64 (b + i)) <> None /\ M8 (Z_to_bv 64 (B + i)) = M7 (Z_to_bv 64 (b + i))).
  { intros i Hi. split; [apply BDEF7; lia|]. destruct (BYTES8 i Hi) as (w & (Ew & Rw) & Bw). unfold byte_at in Bw. rewrite Bw.
    pose proof (PMAEK.rdn_nth RSEGS M7 (Z.to_nat SZ) b bs RDN (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    rewrite (X ltac:(apply BDEF7; lia)). symmetry. exact Ew. }

  apply (KONT fx7 R8 M8 model8 Aw6 B).
  assert (T87 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2720 <= a < sp) -> ~ (B <= a < B + SZ) -> M8 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite PRES8; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc| lia]| exact N2]. apply FR7; [exact Ha| unfold W7; lia]. }
  assert (TS8 : forall a v0, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M7v a v0 -> L5.u64_at RSEGS M8 a v0).
  { intros a v0 Ha Ha' X. apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply PRES8; [lia| apply L5SAR.stack_client; lia| lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [apply VIS6; lia| lia| lia| exact X]. }
  split; [rewrite CS8 by inl; exact iR2|]. split; [rewrite CS8 by inl; rewrite (KS7 8%nat) by inl; exact L8|].
  split; [rewrite CS8 by inl; rewrite (KS7 9%nat) by inl; exact L9|]. split; [rewrite CS8 by inl; exact iR18|].
  split; [rewrite CS8 by inl; rewrite (KS7 19%nat) by inl; exact L19|]. split; [rewrite CS8 by inl; rewrite (KS7 20%nat) by inl; exact L20|].
  split; [rewrite CS8 by inl; rewrite (KS7 21%nat) by inl; exact L21|]. split; [rewrite CS8 by inl; rewrite (KS7 22%nat) by inl; exact L22|].
  split. { intros x Hx. assert (Y : In x L5SAR.cs_all /\ In x PEAEQP1.KS_aeqH /\ In x PEAEQP1.KS_aeqG /\ In x PEAEQP2.KS_aeqS1)
             by (destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; (split; [inl| split; [inl| split; inl]])).
           destruct Y as (Yk1 & Yk2 & Yk4 & Yk5). rewrite (CS8 x Yk1), (KS7 x Yk2), (CS6 x Yk1), (KS3 x Yk4), (CS2 x Yk1), (KS1 x Yk5). reflexivity. }
  split; [apply (TS8 (sp - 8) _ ltac:(lia) ltac:(lia) I8)|].
  split; [apply (TS8 (sp - 16) _ ltac:(lia) ltac:(lia) I16)|].
  split; [apply (TS8 (sp - 24) _ ltac:(lia) ltac:(lia) I24)|].
  split; [apply (TS8 (sp - 32) _ ltac:(lia) ltac:(lia) I32)|].
  split; [apply (TS8 (sp - 40) _ ltac:(lia) ltac:(lia) I40)|].
  split; [apply (TS8 (sp - 48) _ ltac:(lia) ltac:(lia) I48)|].
  split; [apply (TS8 (sp - 56) _ ltac:(lia) ltac:(lia) I56)|].
  split; [apply (TS8 (sp - 64) _ ltac:(lia) ltac:(lia) I64)|].
  split; [apply (TS8 (sp - 120) _ ltac:(lia) ltac:(lia) I120)|].
  split; [apply (TS8 (sp - 128) _ ltac:(lia) ltac:(lia) I128)|].
  split; [apply (TS8 (sp - 136) _ ltac:(lia) ltac:(lia) I136)|].
  split; [apply (TS8 (sp - 144) _ ltac:(lia) ltac:(lia) I144)|].
  split; [apply (TS8 (sp - 152) _ ltac:(lia) ltac:(lia) I152)|].
  split; [apply (TS8 (sp - 104) _ ltac:(lia) ltac:(lia) I104)|].
  split; [apply (TS8 (sp - 96) _ ltac:(lia) ltac:(lia) I96)|].
  split; [apply (TS8 (sp - 88) _ ltac:(lia) ltac:(lia) I88)|].
  split; [replace (B + 2 * SZ) with (B + 24 * NC) by lia; apply (TS8 (sp - 80) _ ltac:(lia) ltac:(lia) I80)|].
  split; [apply (TS8 (sp - 72) _ ltac:(lia) ltac:(lia) I72)|].
  assert (TV8 : forall a, ov <= a < ov + 56 -> M8 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite T87; [apply TV6; lia| lia| apply (L5SAR.obj_client L ar LB2 FF 0 0 ov 56 a AOB); lia| lia| lia]. }
  split; [apply (L5C.u64_at_agree RSEGS M M8); [intros i Hi; apply TV8; lia| lia| lia| exact EV24]|].
  split; [apply (L5C.u64_at_agree RSEGS M M8); [intros i Hi; apply TV8; lia| lia| lia| exact EV32]|].
  split; [apply (L5C.u64_at_agree RSEGS M M8); [intros i Hi; apply TV8; lia| lia| lia| exact EV40]|].
  split. { apply (PMFA.accA_agree M6 M8 ov 56); [| exact ACCV6]. intros x Hx. pose proof (PEAEPF.S_range x ltac:(lia)) as SRx. apply T87; [lia| | lia| destruct Q5 as (_ & [YW|YW] & _); lia].
           exact (PMAEK.frame_sh_client L ar FF ov 56 x LB2 0 0 AOV Hx). }
  split; [lia|]. split; [lia|]. split; [exact Q16|]. split; [unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; exact Q5|]. split; [exact Q1|].
  split; [exact bB|]. split; [exact VBf|]. split; [exact QR|].
  split. { intros i Hi. destruct (Z_lt_le_dec i SZ) as [Li|Li].
           - destruct (COPY i ltac:(lia)) as (D7 & E8'). rewrite E8'. exact D7.
           - rewrite T87; [apply BDEF6; exact Hi| lia| unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact BIN2| cbn [fst snd]; lia]| lia| lia]. }
  split. { intros j Hj. pose proof (PEAEPF.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at.
           rewrite PRES8; [apply QSH7; exact Hj| lia| | destruct Q5 as (_ & [YW|YW] & _); lia].
           unfold aclient, aclient_g. do 6 right. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; apply PMAEK.sh_in; lia]. }
  split. { intros i Hi. assert (Hi' : 24 * Z.of_nat i + 24 <= SZ) by (clear - Hi LENz; Lia.lia).
           apply (PEAEPG1.eitem_copy RSEGS M7 M8 (b + 24 * Z.of_nat i) (B + 24 * Z.of_nat i)).
           - intros j Hj. replace (b + 24 * Z.of_nat i + j) with (b + (24 * Z.of_nat i + j)) by lia. replace (B + 24 * Z.of_nat i + j) with (B + (24 * Z.of_nat i + j)) by lia. apply COPY. lia.
           - destruct (EITEMS i Hi) as (IT0 & IT8 & IT16). unfold PEC.eitem_at.
             split; [apply (PMF.u32_at_agree RSEGS M M7); [intros x Hx; apply TB7; lia| lia| lia| exact IT0]|].
             split; [apply (L5C.u64_at_agree RSEGS M M7); [intros x Hx; apply TB7; lia| lia| lia| exact IT8]|].
             apply (L5C.u64_at_agree RSEGS M M7); [intros x Hx; apply TB7; lia| lia| lia| exact IT16]. }
  split. { assert (TSL : forall a, B + SZ <= a < B + SZ + 24 -> M8 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
           { intros a Ha. rewrite T87; [| lia| unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact BIN2| cbn [fst snd]; lia]| lia| lia].
             apply T65; [lia| unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact BIN2| cbn [fst snd]; lia]| lia|].
             intros X. pose proof (PMAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). destruct Q5 as (_ & [YW|YW] & _); lia. }
           assert (AVB : forall a n0, B <= a -> a + n0 <= B + 2 * SZ -> L5A.avis H2 a n0) by (intros a n0 Ya1 Ya2; apply (VBLK2 B (2 * SZ) a n0 BIN2); lia).
           unfold PEC.eitem_at. cbn [ei_kind ei_len ei_cnt].
           split; [apply (PMF.u32_at_agree RSEGS M3 M8); [intros i Hi; apply TSL; lia| lia| lia| apply (PMAIS1.vis_u32 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS0]]|].
           split; [apply (L5C.u64_at_agree RSEGS M3 M8); [intros i Hi; apply TSL; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS8]]|].
           apply (L5C.u64_at_agree RSEGS M3 M8); [intros i Hi; apply TSL; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS16]]. }
  split; [unfold LB2 in HH8; rewrite ELB in HH8; exact HH8|]. split; [split; [exact Mh8| exact MI8]|].
  split. { apply (L5LZ.model_rt_trans model model7 model8); [|exact RT8]. apply (L5LZ.model_rt_trans model model6 model7); [|exact MRT7].
           apply (L5LZ.model_rt_trans model model3 model6); [|exact MRT6]. apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3].
           apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2]. }
  split; [intros x Hx; apply INC6; apply IA2; exact Hx|]. split; [exact ASTK8|].
  split. { intros j Hj. pose proof (PEAEPF.S_add8 (sp - 12288) j) as E. pose proof (PEAEPF.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
           unfold byte_at. rewrite E. rewrite PRES8; [| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia].
           rewrite FR7; [rewrite <- E; apply STKSH6; exact Hj| lia| unfold W7; lia]. }
  split. { assert (EK8 : L5SAR.ek L ar LB2 FF sp 12288 [(B, SZ)] M7 M8).
           { apply (PEAEPF.ek_of_keep L ar HI LB2 FF LK cr2 Aw6 M7 _ sp _ M7 M8 HH7). intros a Ha Hc Ho. apply PRES8; [exact Ha| apply (L5SAR.aclient_mono L ar LB2 FF sp 12288 (sp - 160) 2560 a Hc); intros x Hx; lia|].
             intros X. apply (Ho (B, SZ)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. lia. }
           apply (PMASK.base_keep L ar C LY LB2 FF sp 12288 [(B, SZ)] M7 M8 EK8); [| exact BASE7].
           intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. destruct Q5 as (_ & [YW|YW] & _); lia. }
  assert (CL : forall a, aclient L ar LBX FF 0 0 a -> aclient L ar LB2 FF 0 0 a /\ aclient L ar LB FF 0 0 a).
  { intros a Hc. assert (X : aclient L ar LB FF 0 0 a) by (rewrite ELB; apply (L5SAR.aclient_consb L ar LBX FF (b, SZ) 0 0 a Hc)).
    split; [apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a X)| exact X]. }
  split. { intros a Ha Hc N1 N2. destruct (CL a Hc) as (Hc2 & Hc1).
           assert (NB : ~ (B <= a < B + 2 * SZ)) by (exact (PMAEK.own_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw2 M2 _ HH2 a 0 0 Hc1)).
           assert (NS : ~ in_shadow_of b SZ a) by (exact (PMAEK.own_sh_notclient L ar C HI LY HIok b SZ LBX FF LK cr Aw M _ HHb ltac:(lia) a 0 0 Hc)).
           rewrite T87; [| exact Ha| exact Hc2| lia| lia]. rewrite T64m; [| exact Ha| exact Hc2| lia| exact NS| lia]. apply T20; [exact Ha| exact Hc1| lia]. }
  intros a Ha Hc HM. destruct (CL a Hc) as (Hc2 & Hc1).
  assert (NS : ~ in_shadow_of b SZ a) by (exact (PMAEK.own_sh_notclient L ar C HI LY HIok b SZ LBX FF LK cr Aw M _ HHb ltac:(lia) a 0 0 Hc)).
  destruct (L5SAR.rng_dec a (B) (B + 2 * SZ)) as [IB|NB].
  - exfalso. exact (PMAEK.own_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw2 M2 _ HH2 a 0 0 Hc1 IB).
  - destruct (L5SAR.rng_dec a (sp - 12288) sp) as [IW|NW].
    + pose proof ASTK8 as (_ & _ & _ & _ & SD8 & _). replace a with (sp - 12288 + (a - (sp - 12288))) by lia. apply SD8. lia.
    + rewrite PRES8; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc2| lia]| lia].
      apply MGM7. rewrite T65; [| exact Ha| exact Hc2| lia| exact NS]. apply MGM3. rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc1| lia]].
      apply MGM1. exact HM.
Qed.
End Stage.
End PEAEQG1.
