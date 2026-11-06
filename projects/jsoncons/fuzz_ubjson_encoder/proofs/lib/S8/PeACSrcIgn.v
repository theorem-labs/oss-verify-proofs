(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PeStepA PmStep PmParStep PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeASrcKitJ PeAPeekP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b4e64_b4e68.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PECIGNA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem ignore_ok : PECSA.fill_buffer_spec L ar HI -> PECSA.ignore_spec L ar HI.
Proof.
  intros FB. unfold PECSA.ignore_spec, PECSPA.ignore_spec, PECSPA.csrc_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb pl s str sm Wextra HH AM K0 ENT FRM FRS FOK ALN A10 A11 WX PA IA BASE ACCP INCS POK CONT KONT.
  pose proof CONT as (CSZ & CBS & CPOS & CBW & CST2). unfold PEC.pos_of, PM.unread in CPOS, CBW.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  unfold PMSPA.no_W in WX. subst Wextra. rewrite app_nil_r in KONT. unfold PMSPA.ignore_args in A11.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (LB := PM.parser_own s ++ LBX) in *.
  pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK cr Aw M model fb (PMSPA.o_is PeCLayoutA.CADDR_A fb) s sp 20480 HH FOK PA ASTK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  set (os := PMSPA.o_src PeCLayoutA.CADDR_A fb) in *.
  pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 112 HH ASTK ltac:(lia)) as (SL112 & SH112 & V3).
  destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
  cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st PM.p_more PM.p_done PM.p_depth PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EGD & IE2). cbn [PM.sm_g PM.sm_eg] in EGD, IE2.
  pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  fold os in S240, S248, SD256, S264, S272, S280, S288.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (VD256 : L5.defined MV (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M (os + 256) 8 ltac:(apply OAV; lia))); exact SD256).
  assert (BOWN : incl (PM.parser_own (PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk)) LB) by (unfold LB; apply incl_appl, incl_refl).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  set (W1 := fun a => (sp - 112 <= a < sp - 112 + 112) \/ (os + 256 <= a < os + 256 + 40)).
  assert (W1ok : forall a, 0 <= a < 2 ^ 64 -> W1 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6914048).
  { intros a Ha Wa. split; [|unfold W1 in Wa; intros X; lia]. destruct Wa as [Wa|Wa].
    - unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - unfold aclientw, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
  destruct (Z_le_gt_dec 2 rem) as [REM2|REM1].
  {

    pose proof (PMAPKP.aigA1b_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | _ => 0 end)) as P.
    cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMAPKP.aligned _ _ => unfold PMAPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PP). pdestr PP.
    unfold PMSPA.cfg. cbn [pa_ignore PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A].
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb4cf4 R1 0xb4eb4 M1v W1 K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M M1 W1 FR1). intros a Ha CL O [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 20480 a HH SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
    assert (Rr : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K LB FF LK cr Aw 0xb4eb4 r W_b4e64 HH1 AM1 F_b4e64 eq_refl D_b4e64 Rr ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx1 R1 M1 model2 LK Aw (PM.SRC qc (de + 1) (rem - 1)) (PM.STRM g eg st)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk]; [ first [ rewrite (KS1 _) by inl; reflexivity ] |]). destruct Hk.
    + apply (PMASKJ.src_piece_parser L ar C HI HIok LB FF LK cr Aw M M1 _ fb _ _ (de + 1) (rem - 1) sp 20480 HH FOK BOWN EK01 MGM1 PA); cbn [PM.p_src PM.sr_qc]; unfold PM.CHUNK.
      * apply TO1; [lia|lia| assumption]. * apply TO1; [lia|lia| assumption]. * apply TO1; [lia|lia| assumption]. * apply TO1; [lia|lia| assumption].
      * lia. * lia. * lia.
    + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M M1 _ fb str _ sp 20480 HH FOK SOWN EK01 IA).
    + unfold PMSPA.src_step, PM.unread. cbn. lia.
    +
      unfold PECSPA.cignore_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sm_eg PM.sm_g PM.sm_st].
      split. { split; [clear - CPOS REM2 IE2; lia|]. split; [| exact CST2].
               replace (blen pl - (rem - 1 + (eg - g))) with (blen pl - (rem + (eg - g)) + 1) by (clear; lia).
               apply (PECSD.bytes_agree RSEGS M M1 (de + 1) (rem - 1)); [apply PECF.slice_length_le; clear - REM2; lia| clear - Q0 G1; lia| clear - Q4 G3 SLO SHI SPT; lia| | exact (PECSD.window_advance RSEGS M pl de (blen pl - (rem + (eg - g))) 1 rem ltac:(clear - CPOS; lia) ltac:(clear - REM2; lia) ltac:(clear - IE2; lia) CBW)].
               intros i Hi. apply FR1; [clear - Hi Q0 Q4 G1 G3 SLO SHI SPT; lia| unfold W1].
               destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 os 296 HH QIN AO) as [X|X]; clear - X Hi Q0 Q4 G1 G3 SLO SHI SPT; lia. }
      left. clear - REM2; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M1).
      * apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M M1 EK01). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
      * pose proof ASTK1 as (_ & _ & _ & _ & DS1 & _). exact DS1.
      * apply L5SAR.dk_grows. exact MGM1.
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM2.
    + exact HH2. }
  destruct (Z.eq_dec rem 1) as [REQ1|REM0].
  {
    assert (REMZ : rem = 1) by lia. subst rem. assert (REQ1 : 1 <= 1) by (clear; lia).
    pose proof (PMAPKP.aigA1a_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | _ => 0 end)) as P.
    cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMAPKP.aligned _ _ => unfold PMAPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PP). pdestr PP.
    unfold PMSPA.cfg. cbn [pa_ignore PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A].
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb4cf4 R1 0xb4eb4 M1v W1 K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M M1 W1 FR1). intros a Ha CL O [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 20480 a HH SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
    assert (Rr : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K LB FF LK cr Aw 0xb4eb4 r W_b4e64 HH1 AM1 F_b4e64 eq_refl D_b4e64 Rr ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx1 R1 M1 model2 LK Aw (PM.SRC qc (de + 1) 0) (PM.STRM g eg st)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk]; [ first [ rewrite (KS1 _) by inl; reflexivity ] |]). destruct Hk.
    + apply (PMASKJ.src_piece_parser L ar C HI HIok LB FF LK cr Aw M M1 _ fb _ _ (de + 1) 0 sp 20480 HH FOK BOWN EK01 MGM1 PA); cbn [PM.p_src PM.sr_qc]; unfold PM.CHUNK.
      * apply TO1; [lia|lia| assumption]. * apply TO1; [lia|lia| assumption]. * apply TO1; [lia|lia| assumption]. * apply TO1; [lia|lia| assumption].
      * lia. * lia. * lia.
    + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M M1 _ fb str _ sp 20480 HH FOK SOWN EK01 IA).
    + unfold PMSPA.src_step, PM.unread. cbn. lia.
    +
      unfold PECSPA.cignore_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sm_eg PM.sm_g PM.sm_st].
      split. { split; [clear - CPOS REQ1 IE2; lia|]. split; [| exact CST2].
               replace (blen pl - (0 + (eg - g))) with (blen pl - (1 + (eg - g)) + 1) by (clear; lia).
               apply (PECSD.bytes_agree RSEGS M M1 (de + 1) (1 - 1)); [apply PECF.slice_length_le; clear; lia| clear - Q0 G1; lia| clear - Q4 G3 SLO SHI SPT; lia| | exact (PECSD.window_advance RSEGS M pl de (blen pl - (1 + (eg - g))) 1 1 ltac:(clear - CPOS; lia) ltac:(clear; lia) ltac:(clear - IE2; lia) CBW)].
               intros i Hi. apply FR1; [clear - Hi Q0 Q4 G1 G3 SLO SHI SPT; lia| unfold W1].
               destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 os 296 HH QIN AO) as [X|X]; clear - X Hi Q0 Q4 G1 G3 SLO SHI SPT; lia. }
      left. clear; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M1).
      * apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M M1 EK01). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
      * pose proof ASTK1 as (_ & _ & _ & _ & DS1 & _). exact DS1.
      * apply L5SAR.dk_grows. exact MGM1.
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM2.
    + exact HH2. }

  assert (REMZ : rem = 0) by lia. subst rem.
  pose proof (PMAPKP.aigA0_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMAPKP.aligned _ _ => unfold PMAPKP.aligned; lia
        | |- _ => lia end]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27
                 & C280 & C112 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C264 & C272 & C288 & CD256).
  unfold PMSPA.cfg. cbn [pa_ignore PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb4cf4 R1 0xb58c8 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { exact W1ok. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M M1 W1 FR1). intros a Ha CL O [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 20480 a HH SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
    - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (TS1 : forall k v, 8 <= k <= 112 -> L5.u64_at RSEGS M1v (sp - k) v -> L5.u64_at RSEGS M1 (sp - k) v).
  { intros k v Hk X. rewrite <- VIS1, <- HID1 in X.
    apply (proj1 (L5A.u64_at_vis _ M1 (sp - k) v (VIS1s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  set (ois := PMSPA.o_is PeCLayoutA.CADDR_A fb) in *. set (op := PMSPA.o_p PeCLayoutA.CADDR_A fb) in *.
  change (PMSP.o_is PeCLayoutA.CADDR_A fb) with ois in CBS.

  assert (DLOC : (PM.vs_data (ois + 80) str = ois + 81 /\ blen pl <= 22 /\ 0 <= ois /\ ois + 272 <= ahl_ceil ar)
              \/ (exists c1 n1 q1, str = PM.VLong c1 n1 q1 /\ PM.vs_data (ois + 80) str = q1 /\ 4096 <= q1 /\ q1 + c1 <= ahl_ceil ar /\ blen pl < c1
                                   /\ (q1 + c1 <= os \/ os + 296 <= q1))).
  { pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
    destruct str as [n0|c1 n1 q1]; cbn [PM.vs_data PM.vs_size] in VSF, CSZ |- *.
    - left. pose proof FOK as ((rs0 & Hfb0) & F2048). destruct (WF (fb, 5, rs0) Hfb0) as (Yw1 & Yw2 & _). unfold ff_addr, ff_class in Yw1, Yw2. cbn [fst snd] in Yw1, Yw2.
      unfold app_mem, FS_BYTES, ff_bytes in FSAPP, FSCEIL, Yw1, Yw2.
      unfold ois, PMSPA.o_is. cbn [pa_off_is PeCLayoutA.CADDR_A]. split; [clear; lia|]. split; [clear - VSF CSZ; lia| clear - Yw1 Yw2 FSAPP FSCEIL; lia].
    - right. exists c1, n1, q1. assert (SIN : In (q1, c1) LB) by (apply SOWN; cbn; left; reflexivity).
      destruct (WB _ SIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4.
      destruct VSF as (_ & _ & _ & Hn1 & _). split; [reflexivity|]. split; [reflexivity|]. split; [clear - B0; lia|]. split; [clear - B4; lia|]. split; [clear - Hn1 CSZ; lia|].
      destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH SIN AO) as [X|X]; clear - X; lia. }
  assert (PA1 : PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M1 op ois (PMSPA.with_src (PM.PST mo dn dp (PM.SRC qc de 0) tb tg vb vk stk) (PM.SRC qc qc 0))).
  { apply (PMASKJ.src_piece_parser L ar C HI HIok LB FF LK cr Aw M M1 _ fb _ _ qc 0 sp 20480 HH FOK BOWN EK01 MGM1 PA); cbn [PM.p_src PM.sr_qc]; unfold PM.CHUNK.
    - apply TO1; [lia|lia| exact C264]. - apply TO1; [lia|lia| exact C272]. - apply TO1; [lia|lia| exact C280].
    - apply TO1; [lia|lia| exact C288]. - lia. - lia. - lia. }
  cbn [PMSPA.with_src PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in PA1.
  set (s1 := PM.PST mo dn dp (PM.SRC qc qc 0) tb tg vb vk stk) in PA1.
  assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
  assert (OUTO : forall i, ~ (os + 256 <= i < os + 296) -> L5.outside [(os + 256, 40)] i).
  { intros i N r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (BASE1 : PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M1).
  { apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M M1 EK01); [intros a Ha; apply OUTO; lia| exact BASE]. }
  assert (IA1 : PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M1 ois str (PM.STRM g eg st)) by (apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M M1 _ fb str _ sp 20480 HH FOK SOWN EK01 IA)).
  assert (WS1 : PMKA.wapp [(os + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG as [X|X]; [right; lia| left; lia]| apply PMKA.wapp_nil]. }
  assert (STK1 : shadow_zero M1 (sp - 112 - 18432) (18432 / 8)).
  { change (18432 / 8) with 2304. change (20480 / 8) with 2560 in STKSH.
    assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (sp - 112 - 18432) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 112 - 18432) with (sp + (-1159) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    apply (PMKA.shadow_zero_sub M1 (sp - 20480) 2560); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKA.stksh_keepA L ar LB FF sp 20480 _ M M1 EK01 WS1 (sp - 20480) 2560); [lia|lia|lia| exact M8a| lia| exact STKSH]. }

  unfold PECSA.fill_buffer_spec, PECSPA.fill_buffer_spec, PECSPA.csrc_spec in FB.
  apply (FB fx1 R1 M1 model1 K LBX FF LK Aw cr (sp - 112) 0xb4e20 fb pl s1 str (PM.STRM g eg st) [] HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact T1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
    split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 3) with 18432. split; [|exact STK1].
    apply (L5SAR.astk_sub ar M1 M1 sp 20480 112 18432 ASTK1 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { intros k Hk. specialize (FRM k Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { exact FOK. }
  { replace (sp - 112) with (sp + (-7) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
  { rewrite L5K.rl10. rewrite (KS1 10%nat) by inl. rewrite A10. reflexivity. }
  { split; [rewrite L5SAR.r12; exact T12|]. exists os, qc. split; [rewrite L5K.rl10; rewrite (KS1 10%nat) by inl; exact A10|]. split; [clear - O1; lia|].
    split; [rewrite L5SAR.r11; exact T11|]. split; [clear - Q0 Q4 SLO SHI SPT; lia|]. apply TO1; [clear; lia| clear; lia| exact C264]. }
  { reflexivity. }
  { exact PA1. }
  { exact IA1. }
  { exact BASE1. }
  {
    pose proof FOK as ((rs0 & Hfb0) & F2048). destruct (WF (fb, 5, rs0) Hfb0) as (Yf1 & Yf2 & _). unfold ff_addr, ff_class, ff_bytes in Yf1, Yf2. cbn in Yf1, Yf2.
    unfold app_mem, FS_BYTES in FSAPP, Yf2.
    apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [| exact ACCP]. unfold PECA.RDR_BYTES.
    intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(unfold op, PMSPA.o_p in Hx; cbn [pa_off_p PeCLayoutA.CADDR_A] in Hx; clear - Hx Yf1 Yf2 FSAPP; lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR1; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; clear - SX; lia| unfold W1; unfold HeapIfaceA.S, HeapIfaceA.SB in *; clear - SX OBIG SLO SHI SPT O1; lia]. }
  { exact INCS. }
  { exact POK. }
  {
    unfold PEC.content_ok. change (PMSP.o_is PeCLayoutA.CADDR_A fb) with ois. unfold s1. cbn [PM.p_src PM.sr_de PM.sr_rem PM.sm_st PM.sm_g PM.sm_eg].
    split; [exact CSZ|]. split.
    { apply (PECSD.bytes_agree RSEGS M M1 (PM.vs_data (ois + 80) str) (blen pl)); [unfold blen; clear; lia| | | | exact CBS].
      - destruct DLOC as [(-> & _ & Y0 & _)|(c1 & n1 & q1 & _ & -> & B0 & _)]; [clear - Y0; lia| clear - B0; lia].
      - destruct DLOC as [(-> & Hn & _ & Yc)|(c1 & n1 & q1 & _ & -> & _ & B4 & Hc & _)]; [clear - Hn Yc SLO SHI SPT; lia| clear - B4 Hc SLO SHI SPT; lia].
      - intros i Hi. destruct DLOC as [(E & Hn & Y0 & Yc)|(c1 & n1 & q1 & Es & E & B0 & B4 & Hc & AP)]; rewrite E in Hi.
        + apply FR1; [clear - Hi Hn Y0 Yc SLO SHI SPT; lia| unfold W1; unfold ois, os, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *; cbn [pa_off_is pa_off_p PeCLayoutA.CADDR_A] in *; clear - Hi Hn Yc SLO; lia].
        + apply FR1; [clear - Hi B0 B4 Hc SLO SHI SPT; lia| unfold W1; clear - Hi B4 Hc AP SLO; lia]. }
    split; [unfold PEC.pos_of, PM.unread; cbn [PM.sr_rem PM.sm_eg PM.sm_g]; clear - CPOS; lia|].
    split; [unfold UbjRef.slice; cbn [PM.sr_de PM.sr_rem Z.to_nat firstn]; apply PECSD.bytes_at_nil| cbn [PM.sm_st PM.sm_g PM.sm_eg]; exact CST2]. }
  intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 MRT2 INC2 INCA2 AM2 HH2. clear FB.
  destruct RES2 as (E2 & c & A10c & Hc & G2c & RSC & RS2 & CHK2 & ST2c). subst src2. unfold PM.CHUNK in Hc, RSC.
  destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *. unfold s1 in CHK2. cbn [PM.p_src PM.sr_qc] in CHK2.
  pose proof IA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEG2 & KE2). cbn [PM.sm_g PM.sm_eg] in KEG2, KE2.
  cbn [PMSPA.with_src PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk] in PA2. fold s1 in PA2.
  change (PM.parser_own s1 ++ LBX) with LB in HH2, HP2. rewrite app_nil_r in HP2. change (PMSPA.pm_scr 3) with 18432 in HP2.
  assert (EK12 : L5SAR.ek L ar LB FF sp 20480 (PMSPA.W_src PeCLayoutA.CADDR_A fb (PM.SRC qc qc 0)) M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 112) 18432 _ _ M1 M2 HP2); [lia|lia|]. intros a _ O. exact O. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 112) 18432 _ M1 M2 HP2); lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP2 & _).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 112) 18432 _ ASTK1 HP2); lia. }
  pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof FOK as ((rs & Hfb) & F1024).
  assert (FBI : ar_fs ar <= fb) by (destruct (WF (fb, 5, rs) Hfb) as (Y1 & _); unfold ff_addr in Y1; cbn in Y1; exact Y1).
  pose proof (PMASKJ.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qc 16384 HH QIN) as QIMG.
  assert (OUTW : forall a, 65536 <= a < 6914048 -> L5.outside (PMSPA.W_src PeCLayoutA.CADDR_A fb (PM.SRC qc qc 0)) a).
  { intros a Ha r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
    unfold ois, os, op, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A] in *.
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK; lia. }
  assert (BASE2 : PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M2) by (apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M1 M2 EK12 OUTW BASE1)).
  assert (KF2 : forall a, sp - 112 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar LB FF (sp - 112) 18432 a); [lia| lia].
    - intros r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
      unfold ois, os, op, PMSPA.o_is, PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A] in *.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; unfold s1 in *; cbn [fst snd PM.p_src PM.sr_qc] in *; unfold PM.CHUNK; lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  assert (TS2 : forall k v, 8 <= k <= 112 -> L5.u64_at RSEGS M1 (sp - k) v -> L5.u64_at RSEGS MV2 (sp - k) v).
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - k) v (VIS2s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; lia| lia| lia| exact X]. }
  pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb ois s1 sp 20480 HH2 FOK PA2 ASTK2)
    as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
  fold os in P1, P8, PBIG, PZ, PW, PCE, PAV.
  pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0 & W1' & W2').
  pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 20480 112 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3).
  fold MV2 in W0, W1', W2', W3.
  pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
  destruct PSRC2 as (_ & _ & SD2 & S264b & S272b & S280b & S288b & _ & _ & _ & _ & DCH2 & ACH2 & _). cbn [PM.sr_qc PM.sr_de PM.sr_rem s1] in *. unfold s1 in S264b, S280b, S288b, DCH2, ACH2. cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  fold os in SD2, S264b, S272b, S280b, S288b.
  assert (VD2 : L5.defined MV2 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))); exact SD2).
  assert (RG2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact T2).
  rewrite L5K.rl10 in A10c.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8. pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18. pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20. pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22. pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24. pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26. pose proof (bv_unsigned_in_range 64 (getr R (reg 27))) as B27.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (EK02 : L5SAR.ek L ar LB FF sp 20480 (PMSPA.W_src PeCLayoutA.CADDR_A fb (PM.SRC qc de 0)) M M2).
  { apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M1 M2); [|exact EK12].
    apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M M1 EK01). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X]. }
  assert (DK02 : L5SAR.dk L ar LB FF sp 20480 M M2) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]).
  set (VS := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 40%nat => bv_unsigned (getr R (reg 1))
                                | 41%nat => bv_unsigned (getr R (reg 8)) | 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18))
                                | 44%nat => bv_unsigned (getr R (reg 19)) | 45%nat => bv_unsigned (getr R (reg 20)) | 46%nat => bv_unsigned (getr R (reg 21))
                                | 47%nat => bv_unsigned (getr R (reg 22)) | 48%nat => bv_unsigned (getr R (reg 23)) | 49%nat => bv_unsigned (getr R (reg 24))
                                | 50%nat => bv_unsigned (getr R (reg 25)) | 51%nat => bv_unsigned (getr R (reg 26)) | 52%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end).
  assert (RVs : forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr R1 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R1 R2 k RP2). cbn in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk. }
  assert (RG8 := T8). rewrite <- (RVs 8%nat ltac:(inl)) in RG8.
  assert (RG9 := T9). rewrite <- (RVs 9%nat ltac:(inl)) in RG9.
  assert (RG18 := T18). rewrite <- (RVs 18%nat ltac:(inl)) in RG18.
  assert (RG19 := T19). rewrite <- (RVs 19%nat ltac:(inl)) in RG19.
  assert (RG20 := T20). rewrite <- (RVs 20%nat ltac:(inl)) in RG20.
  assert (RG21 := T21). rewrite <- (RVs 21%nat ltac:(inl)) in RG21.
  assert (RG22 := T22). rewrite <- (RVs 22%nat ltac:(inl)) in RG22.
  assert (RG23 := T23). rewrite <- (RVs 23%nat ltac:(inl)) in RG23.
  assert (RG24 := T24). rewrite <- (RVs 24%nat ltac:(inl)) in RG24.
  assert (RG25 := T25). rewrite <- (RVs 25%nat ltac:(inl)) in RG25.
  assert (RG26 := T26). rewrite <- (RVs 26%nat ltac:(inl)) in RG26.
  assert (RG27 := T27). rewrite <- (RVs 27%nat ltac:(inl)) in RG27.
  destruct (Z.eq_dec c 0) as [C0|CN0].
  {
    subst c.
    pose proof (PMAPKP.aigB0_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- PMAPKP.aligned _ _ => unfold PMAPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb4e20 R3 0xb4eb4 M3v W1 K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M2 M3 W1 FR3). intros a Ha CL O [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb4eb4 r W_b4e64 HH3 AM3 F_b4e64 eq_refl D_b4e64 Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc qc 0) (PM.STRM g2 eg2 st2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (PMASKJ.src_piece_parser L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb _ s1 qc 0 sp 20480 HH2 FOK BOWN EK23 MGM3 PA2); cbn [PM.p_src PM.sr_qc s1]; unfold s1; cbn [PM.p_src PM.sr_qc]; unfold PM.CHUNK.
      * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption].
      * lia. * lia. * lia.
    + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
    + clear - STEP2 G2c. unfold PMSPA.src_step, PM.unread in *. cbn in *. lia.
    +
      pose proof (RSC ltac:(clear; lia)) as (GE2 & SE2).
      unfold PMSPA.src_step in STEP2. cbn [PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st PM.unread PM.sr_rem] in STEP2. destruct STEP2 as (_ & EE2 & _).
      unfold PECSPA.cignore_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st].
      split. { split; [clear - GE2 G2c EE2 CPOS; lia|]. split; [unfold UbjRef.slice; cbn [Z.to_nat firstn]; apply PECSD.bytes_at_nil| exact ST2c]. }
      right. clear - GE2 G2c EE2; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M3).
      * apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3 EK02).
        apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M2 M3 EK23). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
  destruct (Z.eq_dec c 1) as [C1|CN1].
  {
    subst c.
    pose proof (PMAPKP.aigB1a_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- PMAPKP.aligned _ _ => unfold PMAPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb4e20 R3 0xb4eb4 M3v W1 K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M2 M3 W1 FR3). intros a Ha CL O [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb4eb4 r W_b4e64 HH3 AM3 F_b4e64 eq_refl D_b4e64 Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc (qc + 1) 0) (PM.STRM g2 eg2 st2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (PMASKJ.src_piece_parser L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb _ s1 (qc + 1) 0 sp 20480 HH2 FOK BOWN EK23 MGM3 PA2); cbn [PM.p_src PM.sr_qc s1]; unfold s1; cbn [PM.p_src PM.sr_qc]; unfold PM.CHUNK.
      * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption].
      * lia. * lia. * lia.
    + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
    + clear - STEP2 G2c. unfold PMSPA.src_step, PM.unread in *. cbn in *. lia.
    +
      unfold PMSPA.src_step in STEP2. cbn [PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st PM.unread PM.sr_rem] in STEP2. destruct STEP2 as (_ & EE2 & _). subst eg2.
      unfold PECSPA.cignore_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st].
      split. { split; [clear - CPOS G2c KE2 IE2 ; lia|]. split; [| exact ST2c].
               unfold UbjRef.slice; cbn [Z.to_nat firstn]; apply PECSD.bytes_at_nil. }
      left. clear - G2c ; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M3).
      * apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3 EK02).
        apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M2 M3 EK23). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
  {

    pose proof (PMAPKP.aigB1b_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- PMAPKP.aligned _ _ => unfold PMAPKP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb4e20 R3 0xb4eb4 M3v W1 K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M2 M3 W1 FR3). intros a Ha CL O [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia].
      - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb4eb4 r W_b4e64 HH3 AM3 F_b4e64 eq_refl D_b4e64 Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc (qc + 1) (c - 1)) (PM.STRM g2 eg2 st2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (PMASKJ.src_piece_parser L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb _ s1 (qc + 1) (c - 1) sp 20480 HH2 FOK BOWN EK23 MGM3 PA2); cbn [PM.p_src PM.sr_qc s1]; unfold s1; cbn [PM.p_src PM.sr_qc]; unfold PM.CHUNK.
      * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption]. * apply TO3; [lia|lia| assumption].
      * lia. * lia. * lia.
    + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
    + clear - STEP2 G2c. unfold PMSPA.src_step, PM.unread in *. cbn in *. lia.
    +
      unfold PMSPA.src_step in STEP2. cbn [PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st PM.unread PM.sr_rem] in STEP2. destruct STEP2 as (_ & EE2 & _). subst eg2.
      unfold PECSPA.cignore_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_rem PM.sr_de PM.sr_qc PM.sm_eg PM.sm_g PM.sm_st].
      split. { split; [clear - CPOS G2c KE2 IE2 CN0 CN1 Hc; lia|]. split; [| exact ST2c].
               replace (blen pl - (c - 1 + (eg - g2))) with (blen pl - (eg - g) + 1) by (clear - G2c; lia).
               apply (PECSD.bytes_agree RSEGS M2 M3 (qc + 1) (c - 1)); [apply PECF.slice_length_le; clear - CN0 CN1 Hc; lia| clear - Q0; lia| clear - Q4 SLO SHI SPT Hc; lia| | exact (PECSD.window_advance RSEGS M2 pl qc (blen pl - (eg - g)) 1 c ltac:(clear - CPOS; lia) ltac:(clear - CN0 CN1 Hc; lia) ltac:(clear - KE2 G2c; lia) CHK2)].
               intros i Hi. apply FR3; [clear - Hi Q0 Q4 SLO SHI SPT Hc; lia| unfold W1].
               destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 os 296 HH QIN AO) as [X|X]; clear - X Hi Q0 Q4 SLO SHI SPT Hc; lia. }
      left. clear - G2c CN0 CN1 Hc; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 _ M M3).
      * apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M M2 M3 EK02).
        apply (L5SAR.ek_W L ar LB FF sp 20480 _ [(os + 256, 40)] M2 M3 EK23). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [left; reflexivity| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
Qed.

End WithHeap.
End PECIGNA.
