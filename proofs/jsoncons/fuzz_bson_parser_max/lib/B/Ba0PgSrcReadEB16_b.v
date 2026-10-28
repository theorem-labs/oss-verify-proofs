(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PgSrcReadK16_b Ba0PgSrcReadA0d16_b Ba0PgSrcReadA0e16_b Ba0PgSrcReadM16_b Ba0PgSrcReadC16_b Ba0PgSrcReadCD16_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDEB16.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Section EB.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.


Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.

Lemma srd_entry_body_ok : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PMA.xsgetn_spec L ar HI ->
  PGSRDK16.srd_a0_T L ar HI 16 PGSRDK16.srd_pthF -> PGSRDK16.srd_entry_body_T L ar HI 16.
Proof using LY HIok ICok ILY.
  intros FB XS A0F. unfold PGSRDK16.srd_entry_body_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb F fl LK2 M2 model2 fxc Rc Mc modelc LKc Ac V POST.
  assert (EXIT : PGSRDK16.srd_exit_T L ar HI 16) by (eapply PGSRDK16.srd_exit_ok; eassumption).
  assert (FRT : PGSRDK16.srd_fill_ret_T L ar HI 16) by (eapply PGSRDCD16.srd_fill_ret_ok; first [exact EXIT | eassumption]).
  assert (MC : PGSRDK16.srd_a0_T L ar HI 16 PGSRDK16.srd_pathG) by (eapply PGSRDM16.srd_mc_ok; first [exact FB | exact EXIT | exact FRT | eassumption]).
  assert (A0E : PGSRDK16.srd_a0_T L ar HI 16 PGSRDA0E16.srd_pthE) by (eapply PGSRDA0E16.srd_a0e_ok; first [exact EXIT | eassumption]).
  assert (A0D : PGSRDK16.srd_a0_T L ar HI 16 PGSRDA0D16.srd_pthD) by (eapply PGSRDA0D16.srd_a0d_ok; first [exact XS | exact EXIT | eassumption]).
  pose proof POST as (CTX & R11 & R12 & G & BD & XV2 & XV36 & XV37 & XV38 & XV50 & XV51 & XVS & XR3 & XR4 & XV34 & XV35 & XV45 & IAc & STA & C288).
  set (MVc := mrestrict (ahid Ac modelc) Mc) in *.
  assert (FACTS : 1 <= kb <= 16384 /\ (sst = 0 \/ sst = 2) /\ 0 <= rem <= 16384 /\ 4096 <= de <= 140737488338944
     /\ (kb = 16384 -> rem = 0 -> sst = 2 -> PGSRDA0E16.srd_pA0e V Rc MVc)
     /\ (kb = 16384 -> rem = 0 -> sst = 0 -> PGSRDA0D16.srd_pA0d V Rc MVc)).
  { pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & S32 & ARGS & WX & PA & IA & BASE & INCS & KONT).
  set (src := PM.SRC qc de rem) in *. set (sm := PM.STRM g eg sst) in *.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'. unfold PM.CHUNK in Hk.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEF0).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M model os _ _ src sp 20480 HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M model ois str sm sp 20480 HH AOI I8 IA ASTK)
    as ((I1 & _ & IBIG) & IZ & IW & ICE & IAV & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 80 HH ASTK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132c30 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132b98 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof OFR as (ff & Hff & FLO & FHI). destruct (WF _ Hff) as (FB1 & FB2 & _).
  unfold src, sm in *. clear src sm.
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as PSRC0.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _ & _).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP, FSAPP.
    pose proof STA as STA'. unfold PGSRDK16.srd_stA in STA'. pdestr STA'.
    assert (B38 : 0 <= kb < 2 ^ 64) by (rewrite <- XV38; assumption).
    assert (B37 : 0 <= pb < 2 ^ 64) by (rewrite <- XV37; assumption).
    assert (Ekb : kb = k).
    { rewrite R12 in A12. apply (f_equal bv_unsigned) in A12. rewrite !L5.unsigned_lit in A12 by lia. exact A12. }
    rewrite Ekb in *.
    split; [exact Hk|]. split; [exact IST|]. split; [clear - G1 G2 G3; lia|]. split; [clear - Q0 Q4 G1 G2 G3 SLO SHI SPT; lia|].
    assert (A0C : k = 16384 -> rem = 0 ->
      L5.u64_at RSEGS MVc (os + 240) ois /\ L5.u64_at RSEGS MVc (os + 248) (ois + 16)
      /\ L5.u64_at RSEGS MVc ois 1265968 /\ L5.u64_at RSEGS MVc (ois + 16) 1265728
      /\ L5.u32_at RSEGS MVc (ois + 152) sst /\ L5.u32_at RSEGS MVc (ois + 156) 0 /\ L5.u64_at RSEGS MVc (ois + 160) (ois + 16)
      /\ L5KA.zeros_at MVc 2147609123 1 /\ L5KA.zeros_at MVc 2147609104 1
      /\ (6905856 <= ois <= 140737488355056) /\ ois mod 8 = 0 /\ (2147446784 + 17592186048512 <= ois \/ ois + 272 <= 2147446784)
      /\ L5KA.zeros_at MVc (ois / 8 + 2147450880) 34 /\ L5.writable RSEGS MVc ois 272
      /\ (sp - 16 - 160 + 160 <= ois \/ ois + 272 <= sp - 16 - 160) /\ (os + 296 <= ois \/ ois + 272 <= os)
      /\ (F + 128 <= ois \/ ois + 272 <= F) /\ (fl + 1 <= ois \/ ois + 272 <= fl)
      /\ (F / 8 + 2147450880 + 16 <= ois \/ ois + 272 <= F / 8 + 2147450880)
      /\ (F + 128 <= ois / 8 + 2147450880 \/ ois / 8 + 2147450880 + 34 <= F) /\ (fl + 1 <= ois / 8 + 2147450880 \/ ois / 8 + 2147450880 + 34 <= fl)
      /\ 4096 <= pb <= 140737488338944).
    { intros E16 R0z. subst rem. rewrite E16 in *.
      assert (PW : exists B m, In (B, m) LB /\ B <= p /\ p + 16384 <= B + m).
      { destruct DST as [(AOD & Hk16 & _)|DW]; [exfalso; lia|].
        destruct (PGSA.oo_win _ _ _ _ _ _ OK M (PM.SRC qc de 0) OB p 16384 PA DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
        - exists B, m. split; [exact (OBIN B m BIN)|]. lia.
        - exfalso. unfold PM.CHUNK in WL3. lia. }
      destruct PW as (B & m & TIN & WB1 & WB2).
      destruct (WB _ TIN) as ((T0 & TI & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, TI, T4, TAPP.
      assert (Epb : pb = p).
      { rewrite R11 in A11. apply (f_equal bv_unsigned) in A11. rewrite !L5.unsigned_lit in A11 by lia. exact A11. }
      rewrite Epb in *.
      assert (Epk : p' = p /\ k' = 16384).
      { rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'.
        rewrite !L5.unsigned_lit in A11', A12' by lia. split; congruence. }
      destruct Epk as (-> & ->).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m os 296 HH TIN AO) as APB.
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 os 296 HH QIN AO) as APQ.
      pose proof BD as BD'. unfold PGSRDK16.srd_body in BD'. destruct BD' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). cbn [app] in B1.
      pose proof G as G'. unfold PGSRDK16.srd_frame in G'.
      destruct G' as [Hg SPTg SLOg SHIg SPCg OCRg OWNg FS1g FS2g FCEILg LKI2g FLPg FLNCg HH2g FLCg FRg F8g FBIGg F32g FLAg FLRg FLBIGg NCFg NCSg].
      change (ff_bytes 1) with 128 in *.
      assert (AOI' : PMSPA.aobjA ((F, 1, sp - 160 - 16 + 32) :: FF) ois 272).
      { destruct AOI as (f & Hf & X1 & X2). exists f. split; [right; exact Hf| split; assumption]. }
      pose proof (PGSKA.iss_visG L ar C HI LY HIok LB _ LKc cr Ac Mc modelc ois str _ sp _ B1 AOI' I8 IAc B6)
        as ((I1c & _ & IBIGc) & IZc & IWc & ICEc & IAVc & _).
      pose proof IAc as (H0c & _ & _ & H16c & _ & _ & _ & _ & _ & _ & _ & _ & IOSBc & _ & _).
      destruct IOSBc as (I0c & I32c & I36c & I40c & _).
      cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in H0c, H16c, I0c, I32c, I36c, I40c.
      replace (ois + 120 + 32) with (ois + 152) in I32c by lia. replace (ois + 120 + 36) with (ois + 156) in I36c by lia.
      replace (ois + 120 + 40) with (ois + 160) in I40c by lia.
      pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB _ LKc cr Ac Mc modelc 1265944 1 B1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VZ1.
      pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB _ LKc cr Ac Mc modelc 1265792 1 B1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VZ2.
      cbn in VZ1, VZ2.
      assert (VIo : forall a n, os <= a -> a + n <= os + 296 -> L5A.avis (ahid Ac modelc) a n).
      { intros a n Ha Hn j Hj. apply (PGSRDC16.srd_vis L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r _ str _ _ F fl LK2 M2 model2 Mc modelc LKc Ac (a + j) CTX G BD).
        right; right; right; left. clear - Ha Hn Hj; lia. }
      assert (OUT : forall i, os + 240 <= i < os + 256 -> L5.outside (PGS.W_srcG os ois (PM.SRC qc de 0) ++ [(p, 16384)]) i).
      { intros i Hi r0 Hr0. unfold PGS.W_srcG, PGS.W_srcfG in Hr0. cbn [app PM.sr_qc] in Hr0.
        repeat destruct Hr0 as [<-|Hr0]; [unfold L5.in_rng, PM.CHUNK; cbn [fst snd]; clear - Hi LYD APQ APB WB1 WB2; lia ..| destruct Hr0]. }
      assert (KEEP : forall i, os + 240 <= i < os + 256 -> Mc (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
      { intros i Hi. apply B7. split; [clear - Hi O1; lia|].
        split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF os 296 i AO ltac:(clear - Hi; lia))| exact (OUT i Hi)]. }
      assert (CL : forall a, ois <= a < ois + 272 -> aclient L ar LB FF sp 20480 a).
      { intros a Ha. apply PMASR1.cl_of_bf. right. exact (PMASR1.in_fframe_of_aobjA FF ois 272 a AOI Ha). }
      assert (APX : forall x n y mm, 0 < n -> 0 < mm -> (forall a, x <= a < x + n -> ~ (y <= a < y + mm)) -> x + n <= y \/ y + mm <= x).
      { intros x n y mm Hn Hm H. destruct (Z_le_gt_dec (x + n) y) as [Z1|Z1]; [left; exact Z1|].
        destruct (Z_le_gt_dec (y + mm) x) as [Z2|Z2]; [right; exact Z2|]. exfalso. apply (H (Z.max x y)); clear - Hn Hm Z1 Z2; lia. }
      split.
      { apply (proj2 (L5A.u64_at_vis _ Mc (os + 240) ois (VIo (os + 240) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
        apply (L5C.u64_at_agree RSEGS M Mc); [intros i Hi; apply KEEP; clear - Hi; lia| clear - O1; lia| clear - O1; lia| exact S240]. }
      split.
      { apply (proj2 (L5A.u64_at_vis _ Mc (os + 248) (ois + 16) (VIo (os + 248) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))).
        apply (L5C.u64_at_agree RSEGS M Mc); [intros i Hi; apply KEEP; clear - Hi; lia| clear - O1; lia| clear - O1; lia| exact S248]. }
      split; [apply (proj2 (L5A.u64_at_vis _ Mc ois _ (IAVc ois 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1c; lia) ltac:(clear - I1c; lia))); exact H0c|].
      split; [apply (proj2 (L5A.u64_at_vis _ Mc (ois + 16) _ (IAVc (ois + 16) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1c; lia) ltac:(clear - I1c; lia))); exact H16c|].
      split; [apply (proj2 (L5A.u32_at_vis _ Mc (ois + 152) _ (IAVc (ois + 152) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1c; lia) ltac:(clear - I1c; lia))); exact I32c|].
      split; [apply (proj2 (L5A.u32_at_vis _ Mc (ois + 156) _ (IAVc (ois + 156) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1c; lia) ltac:(clear - I1c; lia))); exact I36c|].
      split; [apply (proj2 (L5A.u64_at_vis _ Mc (ois + 160) _ (IAVc (ois + 160) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - I1c; lia) ltac:(clear - I1c; lia))); exact I40c|].
      split; [exact VZ1|]. split; [exact VZ2|].
      split; [clear - I1c; lia|]. split; [exact I8|]. split; [exact IBIGc|]. split; [exact IZc|]. split; [exact IWc|].
      split.
      { apply (APX (sp - 16 - 160) 160 ois 272); [clear; lia| clear; lia|]. intros a Ha Hb. apply (NCSg a); [clear - Ha; lia| exact (CL a Hb)]. }
      split; [clear - LYD; lia|].
      split.
      { apply (APX F 128 ois 272); [clear; lia| clear; lia|]. intros a Ha Hb. apply (NCFg a); [left; exact Ha| exact (CL a Hb)]. }
      split.
      { apply (APX fl 1 ois 272); [clear; lia| clear; lia|]. intros a Ha Hb. apply FLNCg. replace fl with a by (clear - Ha; lia).
        apply PMASR1.cl_of_bf. right. exact (PMASR1.in_fframe_of_aobjA _ ois 272 a AOI' Hb). }
      split.
      { apply (APX (F / 8 + 2147450880) 16 ois 272); [clear; lia| clear; lia|]. intros a Ha Hb. apply (NCFg a); [right; unfold HeapIfaceA.S, HeapIfaceA.SB; clear - Ha F32g; lia| exact (CL a Hb)]. }
      split; [clear - FRg FBIGg I1c IBIGc; lia|]. split; [clear - FLRg FLBIGg I1c IBIGc; lia|].
      clear - T0 T4 WB1 WB2 SLO SHI SPT; lia. }
    split.
    - intros E16 R0z Hs2. destruct (A0C E16 R0z) as (M240 & M248 & MI0 & MI16 & MI152 & MI156 & MI160 & MZ1 & MZ2 & IR & I8' & IBG & IZ' & IW' & D1 & D2 & D3 & D4 & D5 & D6 & D7 & PB).
      subst sst. unfold PGSRDA0E16.srd_pA0e. rewrite XV36, XV45, XV2, XV38. rewrite R0z in C288.
      repeat split; first [ assumption | (clear - IR I8' IBG D1 D2 D3 D4 D5 D6 D7 XV50 XV51 E16; lia) ].
    - intros E16 R0z Hs0. destruct (A0C E16 R0z) as (M240 & M248 & MI0 & MI16 & MI152 & MI156 & MI160 & MZ1 & MZ2 & IR & I8' & IBG & IZ' & IW' & D1 & D2 & D3 & D4 & D5 & D6 & D7 & PB).
      subst sst. unfold PGSRDA0D16.srd_pA0d. rewrite XV36, XV45, XV2, XV38, XV37. rewrite R0z in C288.
      repeat split; first [ assumption | (clear - IR I8' IBG D1 D2 D3 D4 D5 D6 D7 XV50 XV51 E16 PB; lia) ]. }
  destruct FACTS as (Hkb & Hst & Hrem & Hde & PE & PD).
  destruct (Z_le_gt_dec 1 rem) as [Rpos|Rz].
  - set (V' := fun j => if Nat.eqb j 33 then rem else V j).
    assert (E33 : V' 33%nat = rem) by reflexivity.
    assert (E36 : V' 36%nat = PGS.ow_os O) by exact XV36.
    assert (E35 : V' 35%nat = de) by exact XV35.
    apply (MC O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V' BD
             XV2 XV36 XV37 XV38 XV50 XV51); [| exact XR3| exact XR4| exact XV34| exact XV35| exact XV45| exact IAc| exact STA|].
    + intros i Hi. cbn in Hi. repeat destruct Hi as [<-|Hi]; first [(unfold V'; cbn [Nat.eqb]; apply XVS; cbn; tauto) | destruct Hi].
    + unfold PGSRDK16.srd_pathG, PGSRDK16.srd_pG. rewrite E33, E36, E35.
      split; [reflexivity|]. split; [exact Rpos|]. split; [lia|]. split; [exact C288| lia].
  - assert (R0z : rem = 0) by lia.
    destruct (Z.eq_dec kb 16384) as [K16|K16].
    + destruct Hst as [S0|S2].
      * apply (A0D O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD
                 XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 IAc STA).
        unfold PGSRDA0D16.srd_pthD. split; [exact R0z|]. split; [rewrite XV38; exact K16|]. split; [exact S0| exact (PD K16 R0z S0)].
      * apply (A0E O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD
                 XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 IAc STA).
        unfold PGSRDA0E16.srd_pthE. split; [exact R0z|]. split; [rewrite XV38; exact K16|]. split; [exact S2| exact (PE K16 R0z S2)].
    + apply (A0F O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12 F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD
               XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4 XV34 XV35 XV45 IAc STA).
      unfold PGSRDK16.srd_pthF, PGSRDK16.srd_pA0f. split; [exact R0z|]. rewrite XV36, XV38. rewrite R0z in C288. split; [exact C288| lia].
Qed.

End EB.
End PGSRDEB16.
