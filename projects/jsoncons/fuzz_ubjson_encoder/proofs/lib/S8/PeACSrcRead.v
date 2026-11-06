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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PeStepA PmStep PmParStep PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeACBytes PeCSrcXsgetnA PeASrcKitJ PeASrcReadK PeASrcRead1 PeASrcReadP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b56f8_b56fc.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PECREADA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis32 OAV := lazymatch goal with |- L5.u32_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u32_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem src_read_gen : PECSA.fill_buffer_spec L ar HI ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (sp r fb : Z) (pl : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PeCLayoutA.CADDR_A L ar R M sp r 4 -> PMSPA.ffroomA 4 FF LK -> PMSPA.ffrsA FF sp -> PECA.frame_ok5 FF fb ->
    getr R 10%bv = Z_to_bv 64 (PMSPA.o_src PeCLayoutA.CADDR_A fb) ->
    (exists q k, getr R 11%bv = Z_to_bv 64 q /\ getr R 12%bv = Z_to_bv 64 k /\ 1 <= k <= PM.CHUNK /\ PMSPA.read_dst PeCLayoutA.CADDR_A FF M sp fb s q k) ->
    PMSPA.read_W R Wextra ->
    PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M (PMSPA.o_p PeCLayoutA.CADDR_A fb) (PMSPA.o_is PeCLayoutA.CADDR_A fb) s ->
    PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M (PMSPA.o_is PeCLayoutA.CADDR_A fb) str sm -> PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M ->
    PMSPA.accA M (PMSPA.o_p PeCLayoutA.CADDR_A fb) PECA.RDR_BYTES -> incl (PM.vs_own str) LBX ->
    PECSPA.payload_ok pl -> PEC.content_ok RSEGS PeCLayoutA.CADDR_A M fb pl (PM.p_src s) str sm ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M' (PMSPA.o_p PeCLayoutA.CADDR_A fb) (PMSPA.o_is PeCLayoutA.CADDR_A fb)
          (PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) src' (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s)) ->
        PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M' (PMSPA.o_is PeCLayoutA.CADDR_A fb) str sm' -> PMSPA.src_step (PM.p_src s) src' sm sm' ->
        PECSPA.cread_res RSEGS pl R R' M' (PM.p_src s) src' sm sm' ->
        (PMSPA.consumed (PM.p_src s) src' sm sm' = 0 -> PM.sm_st sm' = 2) ->
        L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp (PMSPA.pm_scr 4) (PMSPA.W_src PeCLayoutA.CADDR_A fb (PM.p_src s) ++ Wextra) M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R (pa_src_read PeCLayoutA.CADDR_A) M model) K.
Proof.
  intros FB. pose proof (PECXGA.cxsgetn_ok L ar C IL HI LY HIok ICok ILY) as XS.
  intros fx R M model K LBX FF LK Aw cr sp r fb pl s str sm Wextra HH AM K0 ENT FRM FRS FOK A10 ARGS WX PA IA BASE ACCP INCS POK CONT KONT.
  pose proof CONT as (CSZ & CBS & CPOS & CBW & CST2). unfold PEC.pos_of, PM.unread in CPOS, CBW.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'. unfold PM.CHUNK in Hk.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (LB := PM.parser_own s ++ LBX) in *.
  pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK cr Aw M model fb (PMSPA.o_is PeCLayoutA.CADDR_A fb) s sp 20480 HH FOK PA ASTK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof (PMASKJ.iss_vis L ar C HI LY HIok LB FF LK cr Aw M model fb str sm sp 20480 HH FOK IA ASTK)
    as ((I1 & I8 & IBIG) & IZ & IW & ICE & IAV & AOI & IOS).
  set (os := PMSPA.o_src PeCLayoutA.CADDR_A fb) in *. set (ois := PMSPA.o_is PeCLayoutA.CADDR_A fb) in *. set (op := PMSPA.o_p PeCLayoutA.CADDR_A fb) in *.
  assert (Eop : op = fb + 592) by (unfold op, PMSPA.o_p; cbn [pa_off_p PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; reflexivity).
  assert (Eos : os = fb + 616) by (unfold os, PMSPA.o_src, PMSPA.o_p; cbn [pa_off_p PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia).
  assert (Eois : ois = fb + 96) by (unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; reflexivity).
  pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 80 HH ASTK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x136e10 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x136d78 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof FOK as ((rs & Hfb) & F1024).
  destruct (WF _ Hfb) as (FB1 & FB2 & _). unfold ff_addr, ff_class, ff_bytes in FB1, FB2. cbn in FB1, FB2.
  assert (AOP : PMSPA.aobjA FF op 384) by (apply (PMASKJ.aobj_fb FF fb); [exact FOK| lia| lia]).
  destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg sst].
  cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st PM.p_more PM.p_done PM.p_depth PM.p_tg PM.p_b PM.p_k PM.p_stk] in *.
  pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _ & _ & PC320 & PTB & _). cbn [PM.p_tb] in PTB.
  unfold PMSPA.read_dst in DST. cbn [PM.p_tb] in DST.
  change (PMSP.o_is PeCLayoutA.CADDR_A fb) with ois in CBS.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  fold os ois in S240, S248, SD256, S264, S272, S280, S288.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & EGD & IE2).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  set (s0 := PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) in *.
  assert (BOWN : incl (PM.parser_own s0) LB) by (unfold LB; apply incl_appl, incl_refl).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
  assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
  assert (ND : NoDup (map fst LB)) by exact (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  destruct (WB _ VIN) as ((VB0 & VBI & _ & _ & VB4 & VAPP) & _). cbn [fst snd] in VB0, VBI, VB4, VAPP.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI, VBI.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP, VAPP, FSAPP.
  set (MV := mrestrict (ahid Aw model) M) in *.

  assert (DF : 4096 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (op <= a < op + 337) /\ ~ (op + 360 <= a < op + 384)
           /\ (forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> ~ (op + 336 <= a < op + 360))
           /\ ~ (qc <= a < qc + 16384) /\ ~ (vb <= a < vb + 32 * 2 ^ vk) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6914048))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> exists c0 n0 q0, tb = PM.VLong c0 n0 q0 /\ q0 <= p /\ p + k <= q0 + c0 /\ In (q0, c0) LB)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)).
  { assert (TBb : forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> In (q0, c0) LB).
    { intros c0 n0 q0 E. apply BOWN. unfold s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own. rewrite E. cbn. right. right. left. reflexivity. }
    assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
    { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
    destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47). destruct VAPP as (VA0 & VAs & VA47).
    destruct DST as [(AOD & Hk8 & DD & AD & APi & APo)|[((n0 & ETB) & D1 & D2)|(c0 & n0 & q0 & ETB & D1 & D2)]].
    -
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) p k HH VIN AOD) as APV.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
      split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia|
               split; [intros E; clear - E Hk8; lia| split; [left; exact AOD| clear - APQ; Lia.lia]]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|]. split; [clear - Ha APo; lia|].
      split; [intros c0 n0 q0 _; clear - Ha APo; lia|]. split; [clear - Ha APQ; lia|]. split; [clear - Ha APV; lia|].
      split; [|clear - Ha X1 Y1 FSI; lia].
      intros c1 n1 q1 E; destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia.
    -
      unfold PMSPA.o_tb in D1, D2. fold op in D1, D2.
      assert (AOD : PMSPA.aobjA FF p k) by (apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - D1 Eop; lia| clear - D2 Eop; lia]).
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) p k HH VIN AOD) as APV.
      split; [clear - D1 Eop FB1 FSI; lia|]. split; [clear - D2 Eop FB2 FSCEIL SLO SHI SPT; lia|].
      split; [apply (L5.defined_sub M op 384); [exact PDEF| clear - D1; lia| clear - D2 Hk; lia]|].
      split; [intros a Ha; apply PC320; clear - Ha D1 D2; lia|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - D1 D2 Eop FB1 FB2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
      split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z D1 D2 Eop FB1 FB2; lia|
               split; [intros E; clear - E D1 D2; lia| split; [left; exact AOD| clear - APQ; Lia.lia]]]].
      intros a Ha. split; [clear - Ha D2 Eop FB2 FSCEIL SLO; lia|]. split; [clear - Ha D1 Eop Eois; lia|]. split; [clear - Ha D1; lia|]. split; [clear - Ha D2; lia|].
      split; [intros c0 n1 q0 E; rewrite ETB in E; discriminate E|]. split; [clear - Ha APQ; lia|]. split; [clear - Ha APV; lia|].
      split; [|clear - Ha D1 Eop FB1 FSI; lia].
      intros c1 n1 q1 E; destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia.
    -
      pose proof (TBb c0 n0 q0 ETB) as TIN. rewrite ETB in PTB.
      pose proof PTB as (_ & _ & _ & _ & _ & _ & _ & _ & TBD & TBC).
      destruct (WB _ TIN) as ((T0 & TI & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, TI, T4, TAPP.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in TAPP. destruct TAPP as (TA0 & TAs & TA47).
      assert (NQ : q0 <> qc).
      { intros E. subst q0. unfold LB, s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own in ND. rewrite ETB in ND. cbn in ND.
        inversion ND as [|x l NI _]. apply NI. apply PMASKJ.elem_of_InA. right. left. reflexivity. }
      assert (NV : q0 <> vb).
      { intros E. subst q0. unfold LB, s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own in ND. rewrite ETB in ND. cbn in ND.
        inversion ND as [|x l _ ND2]. inversion ND2 as [|x2 l2 NI _]. apply NI. apply PMASKJ.elem_of_InA. left. reflexivity. }
      pose proof (PMASKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 qc 16384 HH TIN QIN NQ) as APQ.
      pose proof (PMASKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 vb (32 * 2 ^ vk) HH TIN VIN NV) as APV.
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 op 384 HH TIN AOP) as APP.
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 ois 272 HH TIN AOI) as API.
      split; [clear - D1 T0; lia|]. split; [clear - D2 T4 SLO SHI SPT; lia|].
      split; [apply (L5.defined_sub M q0 c0); [exact TBD| clear - D1; lia| clear - D2; lia]|].
      split; [intros a Ha; apply TBC; clear - Ha D1 D2; lia|].
      split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M _ q0 c0 p k HH TIN); clear - D1 D2; lia|].
      split; [intros a Ha; left; apply (PMASR1.in_block_of LB q0 c0 a TIN); clear - Ha D1 D2; lia|].
      split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TAs as [Z|Z]; [left|right]; clear - Z D1 D2; lia
                      | split; [intros _; exists c0, n0, q0; split; [exact ETB|]; split; [clear - D1; lia|]; split; [clear - D2; lia| exact TIN]|
                        split; [right; exists q0, c0; split; [exact TIN|]; split; [exact D1| exact D2]| clear - APQ D1 D2; Lia.lia]]]].
      intros a Ha. split; [clear - Ha D1 D2 T4 SLO; lia|]. split; [clear - Ha D1 D2 API; lia|]. split; [clear - Ha D1 D2 APP; lia|]. split; [clear - Ha D1 D2 APP; lia|].
      split; [intros c2 n2 q2 _; clear - Ha D1 D2 APP; lia|]. split; [clear - Ha D1 D2 APQ; lia|]. split; [clear - Ha D1 D2 APV; lia|].
      split; [|clear - Ha D1 D2 TI T0; lia].
      intros c1 n1 q1 E. assert (SIN : In (q1, c1) LBX) by (apply INCS; rewrite E; left; reflexivity).
      assert (NS : q0 <> q1) by (apply (PMASKJ.fst_neq_appA (PM.parser_own s0) LBX q0 c0 q1 c1); [exact ND| unfold s0, PM.parser_own, PM.vs_own; rewrite ETB; cbn; right; right; left; reflexivity| exact SIN]).
      destruct (PMASKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha D1 D2 Z; lia. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & D16K & DLOC & DQA).
  assert (pk : p' = p /\ k' = k).
  { rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'.
    rewrite !L5.unsigned_lit in A11', A12' by (clear - Hp' Hk' DP0 DP1 Hk; lia). split; congruence. }
  destruct pk as (-> & ->). clear A11' A12'.
  destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47). destruct VAPP as (VA0 & VAs & VA47).
  assert (TBb : forall c0 n0 q0, tb = PM.VLong c0 n0 q0 -> In (q0, c0) LB).
  { intros c0 n0 q0 E. apply BOWN. unfold s0, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own. rewrite E. cbn. right. right. left. reflexivity. }
  assert (APQO : forall o n, PMSPA.aobjA FF o n -> qc + 16384 <= o \/ o + n <= qc).
  { intros o n AOo. exact (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 o n HH QIN AOo). }

  set (WA := PMSPA.W_src PeCLayoutA.CADDR_A fb (PM.SRC qc de rem) ++ [(p, k)]).
  assert (OUTWA : forall i, ~ (os + 256 <= i < os + 296) -> ~ (ois + 40 <= i < ois + 48) -> ~ (ois + 152 <= i < ois + 156) ->
                  ~ (qc <= i < qc + 16384) -> ~ (p <= i < p + k) -> L5.outside WA i).
  { intros i N1 N2 N3 N4 N5 r0 Hr. unfold WA, PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. fold os ois in Hr. unfold L5.in_rng.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - N1 N2 N3 N4 N5; lia. }
  assert (WAPP : PMKA.wapp WA).
  { unfold WA, PMSPA.W_src, PMSPA.W_srcf. cbn [PM.sr_qc app]. fold os ois. unfold BIGSHADOW_LO, BIGSHADOW_HI in OBIG, IBIG, DSH.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK; clear - QAs; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - DSH; Lia.lia| apply PMKA.wapp_nil]. }
  assert (OUTIMG : forall a, 65536 <= a < 6914048 -> L5.outside WA a).
  { intros a Ha. apply OUTWA; [clear - Ha O1; lia| clear - Ha I1; lia| clear - Ha I1; lia| clear - Ha QI; lia|].
    intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & _ & _ & _ & X9). apply X9. exact Ha. }

  assert (STRK : forall M1, L5SAR.ek L ar LB FF sp 20480 WA M M1 -> L5.bytes_at RSEGS M1 (PM.vs_data (ois + 80) str) pl).
  { intros M1 EK1. pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
    destruct str as [n0|c1 n1 q1]; cbn [PM.vs_data PM.vs_size] in VSF, CSZ, CBS |- *.
    - assert (AOS : PMSPA.aobjA FF (ois + 80 + 1) 23) by (destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| clear - X1 X2; lia]).
      apply (PECSD.bytes_agree RSEGS M M1 (ois + 80 + 1) 23); [unfold blen in *; clear - VSF CSZ; lia| clear - I1; lia| clear - I1; lia| | exact CBS].
      refine (proj1 (PMKA.agA_obj L ar LB FF sp 20480 WA M M1 EK1 WAPP FRB (ois + 80 + 1) 23 AOS _)).
      intros i Hi. pose proof (APQO (ois + 80 + 1) 23 AOS) as ZQ.
      apply OUTWA; [clear - Hi Eos Eois; lia| clear - Hi; lia| clear - Hi; lia| clear - Hi ZQ; lia|].
      intros Y. destruct (DX i Y) as (_ & X2 & _). apply X2. clear - Hi; lia.
    - assert (SIN : In (q1, c1) LB) by (apply SOWN; cbn; left; reflexivity).
      destruct (WB _ SIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4. destruct VSF as (_ & _ & _ & Hn1 & _).
      apply (PECSD.bytes_agree RSEGS M M1 q1 c1); [unfold blen in *; clear - Hn1 CSZ; lia| clear - B0; lia| clear - B4 SLO SHI SPT; lia| | exact CBS].
      assert (NQ1 : qc <> q1).
      { apply (PMASKJ.fst_neq_appA (PM.parser_own s0) LBX qc 16384 q1 c1); [exact ND| unfold s0, PM.parser_own, PM.src_own; cbn; left; reflexivity| apply INCS; cbn; left; reflexivity]. }
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH SIN AO) as Z1.
      pose proof (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 ois 272 HH SIN AOI) as Z2.
      pose proof (PMASKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 q1 c1 HH QIN SIN NQ1) as Z3.
      apply (proj1 (PMKA.agA_blk L ar LB FF sp 20480 WA M M1 EK1 WAPP BRB q1 c1 SIN ltac:(intros i Hi;
        apply OUTWA; [clear - Hi Z1; lia| clear - Hi Z2; lia| clear - Hi Z2; lia| clear - Hi Z3; lia| intros Y; destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & _ & X8 & _); exact (X8 c1 n1 q1 eq_refl Hi)]))). }

  assert (PARS : forall (M3 : word -> option byte) (de' rem' : Z),
      L5SAR.ek L ar LB FF sp 20480 WA M M3 -> L5SAR.dk L ar LB FF sp 20480 M M3 ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M3 op ois (PMSPA.with_src s0 (PM.SRC qc de' rem'))).
  { intros M3 de' rem' EK DK C264 C272 C280 C288 Q1' Q2' Q3'.
  assert (OUTP : forall i, op <= i < op + 384 -> ~ (op + 280 <= i < op + 320) -> ~ (p <= i < p + k) -> L5.outside WA i).
  { intros i Hi N Np. apply OUTWA; [clear - Hi N Eos Eop; lia| clear - Hi Eois Eop; lia| clear - Hi Eois Eop; lia| |exact Np].
    destruct (APQO op 384 AOP) as [Z|Z]; clear - Hi Z; lia. }
  assert (NPk : forall i, (op <= i < op + 337 \/ op + 360 <= i < op + 384) -> ~ (p <= i < p + k)).
  { intros i Hi Y. destruct (DX i Y) as (_ & _ & X3 & X4 & _). clear - Hi X3 X4. lia. }
  assert (VNE : vb <> qc).
  { intros E. subst vb. unfold LB, s0, PM.parser_own, PM.src_own, PM.vec_own in ND. cbn in ND. inversion ND as [|x l NI _]. apply NI. apply PMASKJ.elem_of_InA. left. reflexivity. }
    apply (PMASR1.parser_src_tbA M M3 op ois s0 de' rem' PA); cbn [s0 PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; unfold PM.CHUNK.
    * clear - Eop FB1 FSI. lia.
    * clear - Eop FB2 FSA47. lia.
    * apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB op 280); [apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
      intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia| apply NPk; clear - Hi; lia].
    * apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 320) 17); [apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
      intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia| apply NPk; clear - Hi; lia].
    * apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 360) 24); [apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
      intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia| apply NPk; clear - Hi; lia].
    * apply (PMKA.agsh_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 280) 104). apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia].
    * apply (PMASKJ.defined_dk L ar LB FF sp 20480 M M3 op 384 DK); [| clear - Eop FB1 FSI; lia| clear - Eop FB2 FSA47; lia| exact PDEF].
      intros i Hi. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF op 384 i AOP Hi).
    * intros c0 n0 q0 E. pose proof (TBb c0 n0 q0 E) as TIN. pose proof PTB as PTB'. rewrite E in PTB'.
      destruct PTB' as (_ & _ & _ & _ & _ & _ & _ & _ & TBD & _). destruct (BRB _ TIN) as (T0 & T1). cbn [fst snd] in T0, T1.
      split; [|split].
      -- apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (op + 336) 24); [apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| clear - Eop; lia]|].
         intros i Hi. apply OUTP; [clear - Hi; lia| clear - Hi; lia|]. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & X5 & _). apply (X5 c0 n0 q0 E). clear - Hi; lia.
      -- apply (PMASKJ.defined_dk L ar LB FF sp 20480 M M3 q0 c0 DK); [| clear - T0; lia| clear - T1; lia| exact TBD].
         intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB q0 c0 i TIN Hi).
      -- apply (PMASKJ.agsh_blk L ar LB FF sp 20480 WA M M3 q0 c0 EK WAPP TIN); clear - T0 T1; lia.
    * apply (PMASKJ.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
      intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB qc 16384 i QIN Hi).
    * apply (PMASKJ.agsh_blk L ar LB FF sp 20480 WA M M3 qc 16384 EK WAPP QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
    * clear - VB0. lia.
    * clear - VB4 SLO SHI SPT. lia.
    * apply (PMKA.agA_blk L ar LB FF sp 20480 WA M M3 EK WAPP BRB vb _ VIN). intros i Hi.
      destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) os 296 HH VIN AO) as [Z1|Z1];
      destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) ois 272 HH VIN AOI) as [Z2|Z2];
      destruct (PMASKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ vb (32 * 2 ^ vk) qc 16384 HH VIN QIN VNE) as [Z3|Z3].
      all: apply OUTWA; [clear - Hi Z1; lia| clear - Hi Z2; lia| clear - Hi Z2; lia| clear - Hi Z3; lia|].
      all: intros Y; destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & X7 & _); apply X7; exact Hi.
    * replace (op + 288) with (os + 264) by (clear - Eop Eos; lia). exact C264.
    * replace (op + 296) with (os + 272) by (clear - Eop Eos; lia). exact C272.
    * replace (op + 304) with (os + 280) by (clear - Eop Eos; lia). exact C280.
    * replace (op + 312) with (os + 288) by (clear - Eop Eos; lia). exact C288.
    * exact Q1'.
    * exact Q2'.
    * exact Q3'. }
  assert (FIN : forall (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (model3 : Model) (LK3 : list fframe) (Aw3 : list (Z * Z))
                       (de' rem' g' st' d : Z),
      getr R3 (reg 1) = Z_to_bv 64 r ->
      (forall x, In x L5SAR.cs_all -> getr R3 (reg x) = getr R (reg x)) ->
      getr R3 (reg 10) = Z_to_bv 64 d ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M3 ois str (PM.STRM g' eg st') ->
      g <= g' <= eg -> (sst = 2 -> st' = 2) ->
      0 <= d <= k -> (rem + (eg - g)) - (rem' + (eg - g')) = d ->
      (1 <= rem -> 1 <= d) -> (d = 0 -> rem' = 0 /\ st' = 2) ->
      (st' = 2 -> g' = eg) -> (d < k -> rem' + (eg - g') = 0) ->
      L5.bytes_at RSEGS M3 p (UbjRef.slice pl (blen pl - (rem + (eg - g))) d) ->
      L5.bytes_at RSEGS M3 de' (UbjRef.slice pl (blen pl - (rem + (eg - g)) + d) rem') ->
      L5.defined M3 p d ->
      L5SAR.ek L ar LB FF sp 20480 WA M M3 -> L5SAR.dk L ar LB FF sp 20480 M M3 -> L5CA.astk ar M3 sp 20480 ->
      ri_inv HI LB FF LK3 cr Aw3 M3 (vml_of model3) -> L5CA.amodel_ok Aw3 model3 -> model_rt model model3 -> incl LK3 LK -> incl Aw Aw3 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx3 R3 0xb5748 M3 model3) K).
  { intros fx3 R3 M3 model3 LK3 Aw3 de' rem' g' st' d E1 E2 E10 C264 C272 C280 C288 Q1' Q2' Q3' IA3 Hg Hst2 Hd Hcons HR1 HR0 HST2 HUNR BYT WIN DD3 EK DK ASTK3 HH3 AM3 MRT3 INC3 INCA3.
    unfold PMSPA.cfg.
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK3 cr Aw3 0xb5748 r W_b56f8 HH3 AM3 F_b56f8 eq_refl D_b56f8 E1 ltac:(clear - Hr1; lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    apply (KONT fx3 R3 M3 model4 LK3 Aw3 (PM.SRC qc de' rem') (PM.STRM g' eg st')).
    + apply L5SAR.preserved_by_index. exact E2.
    + apply PARS; assumption.
    + exact IA3.
    + unfold PMSPA.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. split; [reflexivity|]. split; [reflexivity|].
      split; [clear - Hg; lia|]. split; [exact Hst2| clear - Hcons Hd; lia].
    + unfold PECSPA.cread_res, PECSPA.cwin, PMSPA.consumed, PEC.pos_of, PM.unread. cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st].
      split. { split; [clear - CPOS Hcons Hd Q2' Hg; lia|].
               split; [replace (blen pl - (rem' + (eg - g'))) with (blen pl - (rem + (eg - g)) + d) by (clear - Hcons; lia); exact WIN| exact HST2]. }
      exists p, k, d. rewrite L5SAR.r11, L5SAR.r12, L5K.rl10. split; [exact A11|]. split; [exact A12|]. split; [clear - DP0; lia|]. split; [clear - DP1; lia|].
      split; [unfold PM.CHUNK; clear - Hk; lia|]. split; [exact E10|]. split; [exact Hd|]. split; [exact Hcons|]. split; [exact HUNR|].
      split; [exact DD3| exact BYT].
    + unfold PMSPA.consumed, PM.unread. cbn [PM.sr_rem PM.sm_eg PM.sm_g PM.sm_st]. intros C0. exact (proj2 (HR0 ltac:(clear - C0 Hcons; lia))).
    + apply (L5SAR.ahpres_of L ar LB FF sp 20480 WA M M3 EK); [pose proof ASTK3 as (_ & _ & _ & _ & DS3 & _); exact DS3| exact DK].
    + eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC3.
    + exact INCA3.
    + exact AM4.
    + exact HH4. }
  assert (AGSHP : forall M0 M1 W, L5SAR.ek L ar LB FF sp 20480 W M0 M1 -> PMKA.wapp W -> PMFA.agsh M0 M1 p k).
  { intros M0 M1 W E WP. destruct DLOC as [AOD'|(q & m & Hq & X1 & X2)].
    - exact (PMKA.agsh_obj L ar LB FF sp 20480 W M0 M1 E WP FRB p k AOD').
    - destruct (BRB _ Hq) as (Y1 & Y2). cbn [fst snd] in Y1, Y2.
      intros x Hx. apply (PMASKJ.agsh_blk L ar LB FF sp 20480 W M0 M1 q m E WP Hq ltac:(clear - Y1; lia) ltac:(clear - Y2; lia)). clear - Hx X1 X2; lia. }
  assert (CLP : forall a sp0 scr0, p <= a < p + k -> aclient L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMASR1.cl_of_bf; exact (DCL a Ha)).
  assert (CLPw : forall a sp0 scr0, p <= a < p + k -> aclientw L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMASR1.cl_of_bf; exact (DCL a Ha)).
  assert (CLQ : forall a sp0 scr0, qc <= a < qc + 16384 -> aclient L ar LB FF sp0 scr0 a).
  { intros a sp0 scr0 Ha. apply PMASR1.cl_of_bf. left. exact (PMASR1.in_block_of LB qc 16384 a QIN Ha). }
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8. pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18. pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20. pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22. pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24.
  set (W1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (os + 256 <= a < os + 256 + 40)).
  assert (W1ok : forall a, 0 <= a < 2 ^ 64 -> W1 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6914048).
  { intros a Ha Wa. split; [|unfold W1 in Wa; intros X; clear - Wa X O1 SL80 SPT; lia]. destruct Wa as [Wa|Wa].
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SL80 SH80; lia| intros X; clear - X; lia].
    - unfold aclientw, aclient_g. do 3 right. left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [clear - Wa X1 X2; lia| intros X; clear - Wa X X1; lia]. }
  assert (EKW1 : forall M0 M1 LK0 Aw0 V0, ri_inv HI LB FF LK0 cr Aw0 M0 V0 -> (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                 L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M0 M1).
  { intros M0 M1 LK0 Aw0 Vv HH0 FR. apply (L5SAR.ek_piece L ar LB FF sp 20480 [(os + 256, 40)] M0 M1 W1 FR). intros a Ha CL O [X|X].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 _ sp 20480 a HH0 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; clear - X; lia| clear - X Y SL80; lia].
    - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (EKWA : forall M0 M1, L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M0 M1 -> L5SAR.ek L ar LB FF sp 20480 WA M0 M1).
  { intros M0 M1 E. apply (L5SAR.ek_W L ar LB FF sp 20480 WA [(os + 256, 40)] M0 M1 E). intros a O r0 [<-|[]] X. apply (O (os + 256, 40)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; cbn [PM.sr_qc app]; left; reflexivity| exact X]. }

  assert (CPART : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (LK2 : list fframe) (Aw2 : list (Z * Z)) (len1 c g2 st2 : Z),
      getr R2 (reg 10) = Z_to_bv 64 c -> getr R2 (reg 2) = Z_to_bv 64 (sp - 80) -> getr R2 (reg 8) = Z_to_bv 64 len1 -> getr R2 (reg 9) = Z_to_bv 64 os ->
      getr R2 (reg 18) = Z_to_bv 64 (os + 288) -> getr R2 (reg 19) = Z_to_bv 64 p -> getr R2 (reg 20) = Z_to_bv 64 (os + 280) ->
      getr R2 (reg 21) = Z_to_bv 64 (k - len1) -> getr R2 (reg 22) = Z_to_bv 64 2147450880 ->
      getr R2 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> getr R2 (reg 24) = Z_to_bv 64 ((os + 280) / 8 + 2147450880) ->
      (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x)) ->
      L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
      L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
      L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (reg 20))) ->
      L5.u64_at RSEGS M2 (sp - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M2 (sp - 64) (bv_unsigned (getr R (reg 22))) ->
      L5.u64_at RSEGS M2 (sp - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M2 (sp - 80) (bv_unsigned (getr R (reg 24))) ->
      PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M2 op ois (PMSPA.with_src s0 (PM.SRC qc qc 0)) ->
      PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M2 ois str (PM.STRM g2 eg st2) -> PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M2 ->
      len1 = rem -> len1 < k -> k - len1 <= 16383 -> 0 <= c <= 16384 -> g2 = g + c -> g2 <= eg -> (sst = 2 -> st2 = 2) -> (c = 0 -> st2 = 2) ->
      (c < 16384 -> g2 = eg) -> (st2 = 2 -> g2 = eg) ->
      L5.bytes_at RSEGS M2 p (UbjRef.slice pl (blen pl - (rem + (eg - g))) len1) ->
      L5.bytes_at RSEGS M2 qc (UbjRef.slice pl (blen pl - (rem + (eg - g)) + len1) c) ->
      L5.defined M2 p len1 ->
      L5SAR.ek L ar LB FF sp 20480 WA M M2 -> L5SAR.dk L ar LB FF sp 20480 M M2 -> L5CA.astk ar M2 sp 20480 ->
      ri_inv HI LB FF LK2 cr Aw2 M2 (vml_of model2) -> L5CA.amodel_ok Aw2 model2 -> model_rt model model2 -> incl LK2 LK -> incl Aw Aw2 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xb5544 M2 model2) K).
  { intros fx2 R2 M2 model2 LK2 Aw2 len1 c g2 st2 Y10 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 Y24 KS2 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 PA2 IA2 BASE2
           Hl1 Hl1k Hl1k' Hc Hg2 Hg2e Hst2 Hc0 HcC HST2c BY1 CHK DP2 EK2 DK2 ASTK2 HH2 AM2 MRT2 INC2 INCA2.
    set (pos := blen pl - (rem + (eg - g))) in *.
    pose proof (PECF.slice_length_le pl pos len1 ltac:(clear - Hl1 G2; lia)) as SL1.
    set (MV2 := mrestrict (ahid Aw2 model2) M2).
    pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb ois _ sp 20480 HH2 FOK PA2 ASTK2) as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
    fold os MV2 in P1, P8, PBIG, PZ, PW, PCE, PAV.
    pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0 & W1' & W2'). fold MV2 in W0, W1', W2'.
    pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 20480 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3). fold MV2 in W3.
    pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
    destruct PSRC2 as (_ & _ & SD2 & S264b & S272b & S280b & S288b & _ & _ & _ & _ & DCH2 & ACH2 & _).
    cbn [PMSPA.with_src PM.p_src PM.sr_qc PM.sr_de PM.sr_rem s0] in SD2, S264b, S272b, S280b, S288b, DCH2, ACH2. unfold PM.CHUNK in *.
    fold os in SD2, S264b, S272b, S280b, S288b.
    assert (VD2 : L5.defined MV2 (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))); exact SD2).
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
    assert (TS2 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M2 (sp - kk) v -> L5.u64_at RSEGS MV2 (sp - kk) v).
    { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - kk) v (VIS2s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    set (VS := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 36%nat => os | 37%nat => p | 38%nat => k - len1 | 39%nat => len1
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
    destruct (Z.eq_dec c 0) as [CZ|CNZ].
    -
      subst c.
      pose proof (PMASRP.asrC0_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
      unfold PMSPA.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb5544 R3 0xb5748 M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK2 Aw2 _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      apply (FIN fx3 R3 M3 model3 LK2 Aw2 qc 0 g2 st2 len1).
      + match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end. rewrite Z_to_bv_bv_unsigned. exact Rra.
      + intros x Hx. unfold L5SAR.cs_all in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                  | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                  | rewrite (KS3 _) by inl; apply KS2; inl ] |]).
        destruct Hx.
      + assumption.
      + apply TO3; [lia|lia| assumption].
      + apply TO3; [lia|lia| assumption].
      + apply TO3; [lia|lia| assumption].
      + apply TO3; [lia|lia| assumption].
      + clear; lia.
      + clear; lia.
      + clear - Q0; lia.
      + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
      + clear - Hg2 Hg2e; lia.
      + exact Hst2.
      + clear - Hl1 Hl1k G2; lia.
      + clear - Hl1 Hg2; lia.
      + clear - Hl1; lia.
      + intros X. split; [reflexivity| apply Hc0; reflexivity].
      + exact HST2c.
      + intros _. pose proof (HcC ltac:(clear; lia)) as EG. clear - EG; lia.
      + apply (PECSD.bytes_agree RSEGS M2 M3 p len1); [exact SL1| clear - DP0; lia| clear - DP1 Hl1k; lia| | exact BY1].
        intros i Hi. destruct (DX i ltac:(clear - Hi Hl1k Hl1 G2; lia)) as (X1 & _ & X3 & _). apply FR3; [clear - Hi DP0 DP1 Hl1k; lia| unfold W1; clear - X1 X3 Eos Eop; lia].
      + unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
      + apply (L5.defined_grows M2 M3 p len1 MGM3 DP2).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2). apply EKWA. exact EK23.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2). apply L5SAR.dk_grows. exact MGM3.
      + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
      + exact HH3.
      + exact AM3.
      + eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
      + exact INC2.
      + exact INCA2.
    -
      set (len2 := Z.min c (k - len1)).
      assert (L2R : 1 <= len2 <= k - len1 /\ len2 <= c /\ (len2 = k - len1 \/ len2 = c)).
      { unfold len2. clear - CNZ Hc Hl1k. destruct (Z.min_spec c (k - len1)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
      assert (HEADC : exists fx3 R3 M3v, msteps RSEGS (st fx2 R2 0xb5544 MV2) (st fx3 R3 0x78618 M3v) /\ mem_grows MV2 M3v
                 /\ (forall a, 0 <= a < 2 ^ 64 -> ~ W1 a -> M3v (Z_to_bv 64 a) = MV2 (Z_to_bv 64 a))
                 /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x))
                 /\ getr R3 (reg 1) = Z_to_bv 64 742772 /\ getr R3 (reg 10) = Z_to_bv 64 (p + len1) /\ getr R3 (reg 11) = Z_to_bv 64 qc
                 /\ getr R3 (reg 12) = Z_to_bv 64 len2 /\ getr R3 (reg 21) = Z_to_bv 64 len2
                 /\ L5.u64_at RSEGS M3v (os + 288) c /\ L5.u64_at RSEGS M3v (os + 280) qc /\ L5.u64_at RSEGS M3v (os + 264) qc
                 /\ L5.u64_at RSEGS M3v (os + 272) 16384 /\ L5.defined M3v (os + 256) 8
                 /\ L5.u64_at RSEGS M3v (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M3v (sp - 16) (bv_unsigned (getr R (reg 8)))
                 /\ L5.u64_at RSEGS M3v (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M3v (sp - 32) (bv_unsigned (getr R (reg 18)))
                 /\ L5.u64_at RSEGS M3v (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M3v (sp - 48) (bv_unsigned (getr R (reg 20)))
                 /\ L5.u64_at RSEGS M3v (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M3v (sp - 64) (bv_unsigned (getr R (reg 22)))
                 /\ L5.u64_at RSEGS M3v (sp - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M3v (sp - 80) (bv_unsigned (getr R (reg 24)))).
      { destruct (Z_le_gt_dec c (k - len1)) as [CLE|CGT].
        - assert (E2 : len2 = c) by (unfold len2; clear - CLE; lia).
          assert (Cr1 : 1 <= c <= 16383) by (clear - CNZ Hc CLE Hl1k'; lia).
          assert (Cr2 : 0 <= -1 * c + (k - len1) <= 16383) by (clear - CNZ Hc CLE Hl1k'; lia).
          assert (Cr3 : 0 <= p <= 140737488355328) by (clear - DP0 DP1 Hk; lia).
          pose proof (PMASRP.asrCge_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
          L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
              | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| assumption]
              | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
              | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
              | |- _ \/ _ => right; L5FastLia.plia
              | |- _ => L5FastLia.plia end]).
          destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T21 & U288 & U264 & U272 & U280 & UD & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
          exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|].
          split; [intros a Ha N; apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]|].
          split; [intros x Hx; apply KS3; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrCge); vm_compute; reflexivity|].
          rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T21|].
          split; [exact U288|]. split; [exact U280|]. split; [exact U264|]. split; [exact U272|]. split; [exact UD|].
          split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
          split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80].
        - assert (E2 : len2 = k - len1) by (unfold len2; clear - CGT; lia).
          assert (Cr1 : 2 <= c <= 16384) by (clear - CGT Hc Hl1k; lia).
          assert (Cr2 : 1 <= c - (k - len1) <= 16383) by (clear - CGT Hc Hl1k; lia).
          assert (Cr3 : 0 <= p <= 140737488355328) by (clear - DP0 DP1 Hk; lia).
          pose proof (PMASRP.asrClt_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
          L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
              | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| assumption]
              | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
              | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
              | |- _ \/ _ => right; L5FastLia.plia
              | |- _ => L5FastLia.plia end]).
          destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & T1 & T10 & T11 & T12 & U288 & U264 & U272 & U280 & UD & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
          exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|].
          split; [intros a Ha N; apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]|].
          split; [intros x Hx; apply KS3; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrClt); vm_compute; reflexivity|].
          rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [rewrite (KS3 21%nat) by inl; exact Y21|].
          split; [exact U288|]. split; [exact U280|]. split; [exact U264|]. split; [exact U272|]. split; [exact UD|].
          split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
          split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80]. }
      destruct HEADC as (fx3 & R3 & M3v & MS3 & MG3 & FRZ3 & KS3 & T1 & T10 & T11 & T12 & T21 & U288 & U280 & U264 & U272 & UD
                         & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
      unfold PMSPA.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb5544 R3 0x78618 M3v W1 K HH2 AM2 MS3 MG3 FRZ3 W1ok).
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK2 Aw2 _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M3 model3 HH3) as (_ & VIS3s & _).
      assert (TS3 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M3v (sp - kk) v -> L5.u64_at RSEGS M3 (sp - kk) v).
      { intros kk v Hkk X. rewrite <- VIS3, <- HID3 in X.
        apply (proj1 (L5A.u64_at_vis _ M3 (sp - kk) v (VIS3s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (EK03 : L5SAR.ek L ar LB FF sp 20480 WA M M3) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2); apply EKWA; exact EK23).
      assert (DK03 : L5SAR.dk L ar LB FF sp 20480 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2); apply L5SAR.dk_grows; exact MGM3).
      assert (ASTK3 : L5CA.astk ar M3 sp 20480) by (apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)).
      assert (WS1 : PMKA.wapp [(os + 256, 40)]).
      { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; Lia.lia| apply PMKA.wapp_nil]. }
      assert (Hl10 : 0 <= len1) by (clear - Hl1 G2; lia).

      apply (PECAB.memcpy_call_c L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 (sp - 80) 742772 (p + len1) qc len2 HH3 AM3 K0).
      { exact T1. }
      { split; [clear; lia| reflexivity]. }
      { rewrite (KS3 2%nat) by inl. exact Y2. }
      { rewrite (KS3 4%nat) by inl. rewrite (KS2 4%nat) by inl. exact Rtp. }
      { exact T10. }
      { exact T11. }
      { exact T12. }
      { clear - L2R Hl1k'; lia. }
      { apply (L5SAR.astk_sub ar M3 M3 sp 20480 80 2560 ASTK3 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
        replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
      { intros a Ha. apply (PMFA.accA_agree M M3 p k (AGSHP M M3 WA EK03 WAPP) DAP a). clear - Ha L2R Hl10; lia. }
      { intros i Hi. apply CLPw. clear - Hi L2R Hl10; lia. }
      { apply (L5.defined_sub M3 p k); [| clear - L2R Hl10; lia| clear - L2R Hl10; lia].
        apply (PMASKJ.defined_dk L ar LB FF sp 20480 M M3 p k DK03); [intros i Hi; apply CLP; exact Hi| clear - DP0; lia| clear - DP1; lia| exact DDP]. }
      { clear - DP0 Hl10; lia. }
      { clear - DP1 L2R Hl10; lia. }
      { unfold app_rng in DAPP |- *. clear - DAPP L2R Hl10. Lia.lia. }
      { intros a Ha. apply (PMFA.accA_agree M2 M3 qc 16384); [apply (PMASKJ.agsh_blk L ar LB FF sp 20480 _ M2 M3 qc 16384 EK23 WS1 QIN); clear - Q0 Q4 SLO SHI SPT; lia| exact ACH2| clear - Ha L2R Hl1k'; lia]. }
      { clear - Q0; lia. }
      { clear - Q4 SLO SHI SPT L2R Hl1k'; lia. }
      { apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK2 cr Aw2 M3 _ qc 16384 qc len2 HH3 QIN); clear - L2R Hl1k'; lia. }
      { intros i Hi. apply CLQ. clear - Hi L2R Hl1k'; lia. }
      { apply (L5.defined_sub M3 qc 16384); [apply (L5.defined_grows M2 M3 qc 16384 MGM3 DCH2)| clear; lia| clear - L2R Hl1k'; lia]. }
      { clear - DQA L2R Hl10 Hl1k'. Lia.lia. }
      intros fx4 R4 M4 model4 RP4 DEF4 CPY4 HP4 MRT4 AM4 HH4.
      pose proof (PECF.slice_length_le pl (pos + len1) len2 ltac:(clear - L2R; lia)) as SL2.
      assert (KQ4 : forall a, qc <= a < qc + 16384 -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha Q0 Q4 SLO SHI SPT; lia|]. split; [apply CLQ; exact Ha|].
        intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha DQA L2R Hl10 Hl1k'. Lia.lia. }
      assert (KP4 : forall a, p <= a < p + len1 -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha DP0 DP1 Hl10 Hl1k; lia|]. split; [apply CLP; clear - Ha Hl10 Hl1k; lia|].
        intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha; lia. }

      assert (BY2 : L5.bytes_at RSEGS M4 (p + len1) (UbjRef.slice pl (pos + len1) len2)).
      { apply (PECAB.bytes_at_copy M3 M4 qc (p + len1)).
        - intros i Hi. apply CPY4. clear - Hi SL2. lia.
        - apply (L5.defined_grows M2 M3 _ _ MGM3). apply (L5.defined_sub M2 qc 16384); [exact DCH2| clear; lia| clear - SL2 L2R Hl1k' Hl10; lia].
        - apply (PECSD.bytes_agree RSEGS M2 M3 qc 16384); [clear - SL2 L2R Hl1k' Hl10; lia| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| | exact (PECSD.window_head RSEGS M2 pl qc (pos + len1) len2 c ltac:(clear - CPOS Hl1 G2; unfold pos; lia) ltac:(clear - L2R; lia) CHK)].
          intros i Hi. pose proof (APQO os 296 AO) as ZQ. apply FR3; [clear - Hi Q0 Q4 SLO SHI SPT; lia| unfold W1; clear - Hi ZQ Q4 SLO; lia]. }
      assert (OUTD : forall a, aclient L ar LB FF sp 20480 a -> L5.outside WA a -> L5.outside [(p + len1, len2)] a).
      { intros a _ O r0 [<-|[]] X. apply (O (p, k)); [unfold WA; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - X L2R Hl10; lia]. }
      assert (EK34 : L5SAR.ek L ar LB FF sp 20480 WA M3 M4).
      { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 WA [(p + len1, len2)] M3 M4 HP4); [clear; lia| clear; lia| exact OUTD]. }
      assert (EK34d : L5SAR.ek L ar LB FF sp 20480 [(p + len1, len2)] M3 M4).
      { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ [(p + len1, len2)] M3 M4 HP4); [clear; lia| clear; lia| intros a _ O; exact O]. }
      assert (DK34 : L5SAR.dk L ar LB FF sp 20480 M3 M4) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ M3 M4 HP4); clear; lia).
      assert (ASTK4 : L5CA.astk ar M4 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M3 M4 sp 20480 (sp - 80) 2560 _ ASTK3 HP4); clear - TOP; lia).
      assert (NDP : forall a, ~ (p <= a < p + k) -> ~ (p + len1 <= a < p + len1 + len2)) by (intros a N X; apply N; clear - X L2R Hl10; lia).
      assert (KF4 : forall a, sp - 80 <= a < sp -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
        - apply (L5SAR.stack_client L ar LB FF (sp - 80) 2560 a); clear - Ha SL80 SHI SPT; lia.
        - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (X1 & _). apply X1. clear - Ha; lia. }
      assert (KO4 : forall a, os + 256 <= a < os + 296 -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha O1; lia|]. split.
        - apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
        - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & X3 & _). apply X3. clear - Ha Eos Eop; lia. }
      assert (WSP : PMKA.wapp [(p + len1, len2)]).
      { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH L2R Hl10; Lia.lia| apply PMKA.wapp_nil]. }
      assert (EK04 : L5SAR.ek L ar LB FF sp 20480 WA M M4) by exact (L5SAR.ek_trans L ar LB FF sp 20480 WA M M3 M4 EK03 EK34).
      assert (DK04 : L5SAR.dk L ar LB FF sp 20480 M M4) by exact (L5SAR.dk_trans L ar LB FF sp 20480 M M3 M4 DK03 DK34).
      assert (T4 : forall a v, os + 256 <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M4 a v).
      { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KO4; clear - Ha Hb Hi; lia| clear - Ha O1; lia| clear - Hb O1; lia|].
        apply TO3; [clear - Ha; lia| clear - Hb; lia| exact X]. }
      assert (PA4 : PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M4 op ois (PMSPA.with_src s0 (PM.SRC qc qc c))).
      { apply (PARS M4 qc c EK04 DK04); [apply T4; [clear; lia| clear; lia| exact U264]| apply T4; [clear; lia| clear; lia| exact U272]
                                        | apply T4; [clear; lia| clear; lia| exact U280]| apply T4; [clear; lia| clear; lia| exact U288]| clear; lia| clear - Hc; lia| clear - Hc; lia]. }
      assert (IA3 : PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M3 ois str (PM.STRM g2 eg st2)) by exact (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
      assert (IA4 : PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M4 ois str (PM.STRM g2 eg st2)).
      { apply (PMKA.iss_keepA RSEGS PeCLayoutA.CADDR_A L ar LB FF sp 20480 _ M3 M4 EK34d WSP FRB BRB ois str _ AOI SOWN); [| |exact IA3].
        - intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & X2 & _). apply X2. exact Hi.
        - intros c1 n1 q1 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & _ & X8 & _). apply (X8 c1 n1 q1 E). exact Hi. }
      assert (BASE3 : PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M3).
      { apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M2 M3 EK23); [intros a Ha r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - Ha O1; lia| exact BASE2]. }
      assert (BASE4 : PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M4).
      { apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M3 M4 EK34d); [| exact BASE3].
        intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & _ & _ & _ & X9). apply X9. exact Ha. }
      set (MV4 := mrestrict (ahid Aw2 model4) M4).
      pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M4 model4 fb ois _ sp 20480 HH4 FOK PA4 ASTK4) as ((P1' & P8' & PBIG') & PZ' & PW' & PCE' & PAV' & _ & _).
      fold os MV4 in P1', P8', PBIG', PZ', PW', PCE', PAV'.
      pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M4 model4 HH4 BASE4) as (X0' & X1' & X2'). fold MV4 in X0', X1', X2'.
      pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M4 model4 sp 20480 80 HH4 ASTK4 ltac:(lia)) as (_ & _ & X3'). fold MV4 in X3'.
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M4 model4 HH4) as (_ & VIS4s & _).
      assert (TS4 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M3v (sp - kk) v -> L5.u64_at RSEGS MV4 (sp - kk) v).
      { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M4 (sp - kk) v (VIS4s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
        apply (L5C.u64_at_agree RSEGS M3 M4); [intros i Hi; apply KF4; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia|].
        apply TS3; [exact Hkk| exact X]. }
      assert (TO4 : forall a v, os + 256 <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV4 a v).
      { intros a v Ha Hb X. apply (proj2 (L5A.u64_at_vis _ M4 a v ltac:(apply PAV'; clear - Ha Hb; lia) ltac:(clear - Ha O1; lia) ltac:(clear - Hb O1; lia))). apply T4; assumption. }
      assert (VD4 : L5.defined MV4 (os + 256) 8).
      { apply (proj2 (L5A.defined_vis _ M4 (os + 256) 8 ltac:(apply PAV'; lia))). pose proof PA4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PS4 & _).
        destruct PS4 as (_ & _ & SD4 & _). exact SD4. }
      assert (RG : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg x) = getr R3 (reg x)).
      { intros x Hx. apply (L5SAR.cs_of_preserved R3 R4 x RP4). cbn in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx. }
      assert (Dr1 : 1 <= c <= 16384) by (clear - CNZ Hc; lia).
      assert (Dr2 : 0 <= c - len2 <= 16383) by (clear - L2R Hc Hl1k'; lia).
      assert (Dr3 : 0 <= len1 <= 16383) by (clear - Hl10 Hl1k Hk Hl1k'; lia).
      assert (Dr4 : 1 <= len2 <= 16383) by (clear - L2R Hl1k'; lia).
      assert (Dr5 : 4096 <= qc <= 140737488338944) by (clear - Q0 Q4 SLO SHI SPT; lia).
      set (VD := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => qc | 36%nat => os | 37%nat => p | 38%nat => len2 | 39%nat => len1
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
      pose proof (PMASRP.asrD_conc fx4 R4 MV4 VD) as P. unfold VD in P. cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- getr R4 (reg ?x) = _ => rewrite (RG x) by inl; first [assumption | rewrite (KS3 x) by inl; assumption]
          | |- L5.u64_at _ _ (sp - _) _ => apply TS4; [lia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => apply TO4; [lia| lia| assumption]
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; lia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z2 & Z8 & Z9 & Z10 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                     & V288 & V280 & V264 & V272 & _).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M4 model4 fx4 fx5 R4 0xb5574 R5 0xb5748 M5v W1 K HH4 AM4 MS5 MG5).
      { intros a Ha N. apply FRZ5; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
      assert (EK45 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M4 M5) by exact (EKW1 M4 M5 LK2 Aw2 _ HH4 FR5).
      assert (TO5 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS M5 a v).
      { intros a v Ha Hb X. rewrite <- VIS5 in X. apply (proj1 (L5A.u64_at_vis _ M5 a v ltac:(apply PAV'; lia) ltac:(lia) ltac:(lia))). exact X. }
      assert (AGQ25 : forall i, qc <= i < qc + 16384 -> M5 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)).
      { intros i Hi. pose proof (APQO os 296 AO) as ZQ.
        rewrite (FR5 i) by (first [clear - Hi Q0 Q4 SLO SHI SPT; lia | unfold W1; clear - Hi ZQ Q4 SLO; lia]).
        rewrite (KQ4 i Hi). apply FR3; [clear - Hi Q0 Q4 SLO SHI SPT; lia| unfold W1; clear - Hi ZQ Q4 SLO; lia]. }
      assert (AGP25 : forall i, p <= i < p + len1 -> M5 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)).
      { intros i Hi. destruct (DX i ltac:(clear - Hi Hl10 Hl1k; lia)) as (X1 & _ & X3 & _).
        rewrite (FR5 i) by (first [clear - Hi DP0 DP1 Hl10 Hl1k; lia | unfold W1; clear - X1 X3 Eos Eop; lia]).
        rewrite (KP4 i Hi). apply FR3; [clear - Hi DP0 DP1 Hl10 Hl1k; lia| unfold W1; clear - X1 X3 Eos Eop; lia]. }
      apply (FIN fx5 R5 M5 model5 LK2 Aw2 (qc + len2) (c - len2) g2 st2 (len2 + len1)).
      + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
      + intros x Hx. unfold L5SAR.cs_all in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ first [ match goal with H : getr R5 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R5 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                  | rewrite Z2; exact (eq_sym Rsp)
                  | rewrite (KS5 _) by inl; rewrite (RG _) by inl; rewrite (KS3 _) by inl; apply KS2; inl ] |]).
        destruct Hx.
      + exact Z10.
      + apply TO5; [lia| lia| exact V264].
      + apply TO5; [lia| lia| exact V272].
      + apply TO5; [lia| lia| exact V280].
      + apply TO5; [lia| lia| exact V288].
      + clear - Dr4; lia.
      + clear - Dr2; lia.
      + clear - Hc; lia.
      + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M4 M5 _ fb str _ sp 20480 HH4 FOK SOWN EK45 IA4).
      + clear - Hg2 Hg2e Hc; lia.
      + exact Hst2.
      + clear - L2R Hl10; lia.
      + clear - Hl1 Hg2; lia.
      + intros _. clear - Dr4 Hl10; lia.
      + intros X. exfalso. clear - X Dr4 Hl10; lia.
      + exact HST2c.
      + intros Hdk. assert (E2c : len2 = c) by (clear - Hdk L2R; Lia.lia). rewrite (HcC ltac:(clear - E2c L2R Hl1k' Hdk Hl10; lia)). clear - E2c; lia.
      +
        replace (len2 + len1) with (len1 + len2) by (clear; lia). rewrite (PECSD.slice_app pl pos len1 len2) by (clear - CPOS Hl10 L2R; lia).
        apply (proj2 (PECSD.bytes_at_app RSEGS M5 p _ _)). split.
        * apply (PECSD.bytes_agree RSEGS M2 M5 p len1); [exact SL1| clear - DP0; lia| clear - DP1 Hl1k; lia| exact AGP25| exact BY1].
        * rewrite (PECSD.slice_len pl pos len1) by (clear - CPOS Hl1 Hl10 IE2; unfold pos; lia). rewrite Z2Nat.id by (clear - Hl10; lia).
          apply (PECSD.bytes_agree RSEGS M4 M5 (p + len1) len2); [exact SL2| clear - DP0 Hl10; lia| clear - DP1 L2R Hl10; lia| | exact BY2].
          intros i Hi. destruct (DX i ltac:(clear - Hi Hl10 L2R; lia)) as (X1 & _ & X3 & _). apply FR5; [clear - Hi DP0 DP1 Hl10 L2R; lia| unfold W1; clear - X1 X3 Eos Eop; lia].
      +
        replace (pos + (len2 + len1)) with (pos + len1 + len2) by (clear; lia).
        apply (PECSD.bytes_agree RSEGS M2 M5 (qc + len2) (c - len2)); [apply PECF.slice_length_le; clear - L2R; lia| clear - Q0 L2R; lia| clear - Q4 SLO SHI SPT Hc L2R; lia| intros i Hi; apply AGQ25; clear - Hi L2R Hc; lia|].
        exact (PECSD.window_advance RSEGS M2 pl qc (pos + len1) len2 c ltac:(clear - CPOS Hl1 G2; unfold pos; lia) ltac:(clear - L2R; lia) ltac:(clear - Hl1 Hg2 Hg2e IE2 CPOS; unfold pos; lia) CHK).
      + rewrite Z.add_comm. apply (PMASR1.defined_app M5 p len1 len2 Hl10).
        * apply (PMASKJ.defined_dk L ar LB FF sp 20480 M2 M5 p len1); [| | clear - DP0; lia| clear - DP1 L2R Hl10; lia| exact DP2].
          -- apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M4 M5); [apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M3 M4); [apply L5SAR.dk_grows; exact MGM3| exact DK34]| apply L5SAR.dk_grows; exact MGM5].
          -- intros i Hi. apply CLP. clear - Hi L2R Hl10; lia.
        * apply (L5.defined_grows M4 M5 _ _ MGM5 DEF4).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M4 M5 EK04). apply EKWA. exact EK45.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M4 M5 DK04). apply L5SAR.dk_grows. exact MGM5.
      + apply (L5SAR.astk_grows ar M4 M5 sp 20480 ASTK4 MGM5).
      + exact HH5.
      + exact AM5.
      + eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3|]. eapply L5LZ.model_rt_trans; [exact MRT4| exact MRT5].
      + exact INC2.
      + exact INCA2. }

  assert (FILLC : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (len1 : Z),
      getr R1 (reg 1) = Z_to_bv 64 742724 -> getr R1 (reg 2) = Z_to_bv 64 (sp - 80) -> getr R1 (reg 8) = Z_to_bv 64 len1 -> getr R1 (reg 9) = Z_to_bv 64 os ->
      getr R1 (reg 10) = Z_to_bv 64 os -> getr R1 (reg 11) = Z_to_bv 64 qc -> getr R1 (reg 12) = Z_to_bv 64 16384 ->
      getr R1 (reg 18) = Z_to_bv 64 (os + 288) -> getr R1 (reg 19) = Z_to_bv 64 p -> getr R1 (reg 20) = Z_to_bv 64 (os + 280) ->
      getr R1 (reg 21) = Z_to_bv 64 (k - len1) -> getr R1 (reg 22) = Z_to_bv 64 2147450880 ->
      getr R1 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> getr R1 (reg 24) = Z_to_bv 64 ((os + 280) / 8 + 2147450880) ->
      (forall x, In x [3; 4; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x)) ->
      L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
      L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
      L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (reg 20))) ->
      L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (reg 22))) ->
      L5.u64_at RSEGS M1 (sp - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M1 (sp - 80) (bv_unsigned (getr R (reg 24))) ->
      L5.u64_at RSEGS M1 (os + 264) qc -> L5.u64_at RSEGS M1 (os + 272) 16384 -> L5.u64_at RSEGS M1 (os + 280) qc -> L5.u64_at RSEGS M1 (os + 288) 0 ->
      len1 = rem -> len1 < k -> k - len1 <= 16383 -> L5.defined M1 p len1 ->
      L5.bytes_at RSEGS M1 p (UbjRef.slice pl (blen pl - (rem + (eg - g))) len1) ->
      L5SAR.ek L ar LB FF sp 20480 WA M M1 -> L5SAR.dk L ar LB FF sp 20480 M M1 -> L5CA.astk ar M1 sp 20480 -> PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M1 ->
      PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M1 ois str (PM.STRM g eg sst) ->
      ri_inv HI LB FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xb58c8 M1 model1) K).
  { intros fx1 R1 M1 model1 len1 T1 T2 T8 T9 T10 T11 T12 T18 T19 T20 T21 T22 T23 T24 KS1 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C264 C272 C280 C288
           Hl1 Hl1k Hl1k' DP1' BY1 EK1 DK1 ASTK1 BASE1 IA1 HH1 AM1 MRT1.
    pose proof (STRK M1 EK1) as STR1.
    assert (PA1 : PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M1 op ois (PMSPA.with_src s0 (PM.SRC qc qc 0))).
    { apply (PARS M1 qc 0 EK1 DK1 C264 C272 C280 C288); clear; lia. }
    assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (sp - 80 - 18432) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 80 - 18432) with (sp + (-1157) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
    assert (STK1 : shadow_zero M1 (sp - 80 - 18432) (18432 / 8)).
    { change (18432 / 8) with 2304. change (20480 / 8) with 2560 in STKSH.
      apply (PMKA.shadow_zero_sub M1 (sp - 20480) 2560); [exact M8a| exact M8b| clear; lia| clear; lia| clear; lia|].
      apply (PMKA.stksh_keepA L ar LB FF sp 20480 WA M M1 EK1 WAPP (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact M8a| clear; lia| exact STKSH]. }
    unfold PECSA.fill_buffer_spec, PECSPA.fill_buffer_spec, PECSPA.csrc_spec in FB.
    apply (FB fx1 R1 M1 model1 K LBX FF LK Aw cr (sp - 80) 0xb5544 fb pl (PMSPA.with_src s0 (PM.SRC qc qc 0)) str (PM.STRM g eg sst) [] HH1 AM1 K0).
    { split; [rewrite L5K.rl1; exact T1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
      split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
      change (PMSPA.pm_scr 3) with 18432. split; [|exact STK1].
      apply (L5SAR.astk_sub ar M1 M1 sp 20480 80 18432 ASTK1 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
      replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
    { intros kk Hkk. specialize (FRM kk Hkk). clear - FRM. lia. }
    { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
    { exact FOK. }
    { replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
    { rewrite L5K.rl10. exact T10. }
    { split; [rewrite L5SAR.r12; exact T12|]. exists os, qc. split; [rewrite L5K.rl10; exact T10|]. split; [clear - O1; lia|].
      split; [rewrite L5SAR.r11; exact T11|]. split; [clear - Q0 Q4 SLO SHI SPT; lia| exact C264]. }
    { reflexivity. }
    { exact PA1. }
    { exact IA1. }
    { exact BASE1. }
    {
      apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [| exact ACCP].
      apply (PMKA.agsh_obj L ar LB FF sp 20480 WA M M1 EK1 WAPP FRB op PECA.RDR_BYTES).
      apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }
    { exact INCS. }
    { exact POK. }
    {
      unfold PEC.content_ok. change (PMSP.o_is PeCLayoutA.CADDR_A fb) with ois. cbn [PMSPA.with_src PM.p_src PM.sr_de PM.sr_rem PM.sm_st PM.sm_g PM.sm_eg s0].
      split; [exact CSZ|]. split; [exact STR1|].
      split; [unfold PEC.pos_of, PM.unread; cbn [PM.sr_rem PM.sm_eg PM.sm_g]; clear - CPOS G2; lia|].
      split; [unfold UbjRef.slice; cbn [PM.sr_de PM.sr_rem Z.to_nat firstn]; apply PECSD.bytes_at_nil| cbn [PM.sm_st PM.sm_g PM.sm_eg]; exact CST2]. }
    intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 RP2 PA2 IA2 STEP2 RES2 HP2 MRT2 INC2 INCA2 AM2 HH2. clear FB.
    destruct RES2 as (E2 & c & A10c & Hc & G2c & RSC & RS2 & CHK2 & ST2c). subst src2. unfold PM.CHUNK in Hc, RSC.
    cbn [PMSPA.with_src PM.p_src PM.sr_qc PM.sm_g PM.sm_eg s0] in CHK2.
    destruct sm2 as [g2 eg2 st2]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
    pose proof STEP2 as (_ & EG2 & _ & _ & _). cbn [PM.sm_eg] in EG2. subst eg2.
    change (PM.parser_own (PMSPA.with_src s0 (PM.SRC qc qc 0)) ++ LBX) with LB in HH2, HP2. rewrite app_nil_r in HP2. change (PMSPA.pm_scr 3) with 18432 in HP2.
    cbn [PMSPA.with_src PM.p_src] in HP2, PA2.
    assert (EK12 : L5SAR.ek L ar LB FF sp 20480 WA M1 M2).
    { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 18432 WA _ M1 M2 HP2); [clear; lia| clear; lia|].
      intros a _ O r0 Hr X. apply (O r0); [| exact X]. unfold WA. apply in_or_app. left. exact Hr. }
    assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 18432 _ M1 M2 HP2); clear; lia).
    assert (ASTK2 : L5CA.astk ar M2 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 80) 18432 _ ASTK1 HP2); clear - TOP; lia).
    assert (KF2 : forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
      - apply (L5SAR.stack_client L ar LB FF (sp - 80) 18432 a); clear - Ha SL80 SHI SPT; lia.
      - intros r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. fold os ois in Hr. unfold L5.in_rng.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - Ha OCE ICE Q4 SL80 SLO; lia. }
    assert (SV : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1 (sp - kk) v -> L5.u64_at RSEGS M2 (sp - kk) v).
    { intros kk v Hkk X. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia| exact X]. }
    assert (RG : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
    pose proof (PMASKJ.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
    apply (CPART fx2 R2 M2 model2 LK2 Aw2 len1 c g2 st2).
    - rewrite L5K.rl10 in A10c. exact A10c.
    - rewrite (RG 2%nat) by inl. exact T2.
    - rewrite (RG 8%nat) by inl. exact T8.
    - rewrite (RG 9%nat) by inl. exact T9.
    - rewrite (RG 18%nat) by inl. exact T18.
    - rewrite (RG 19%nat) by inl. exact T19.
    - rewrite (RG 20%nat) by inl. exact T20.
    - rewrite (RG 21%nat) by inl. exact T21.
    - rewrite (RG 22%nat) by inl. exact T22.
    - rewrite (RG 23%nat) by inl. exact T23.
    - rewrite (RG 24%nat) by inl. exact T24.
    - intros x Hx. rewrite (RG x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KS1. exact Hx.
    - apply SV; [clear; lia| exact C8].
    - apply SV; [clear; lia| exact C16].
    - apply SV; [clear; lia| exact C24].
    - apply SV; [clear; lia| exact C32].
    - apply SV; [clear; lia| exact C40].
    - apply SV; [clear; lia| exact C48].
    - apply SV; [clear; lia| exact C56].
    - apply SV; [clear; lia| exact C64].
    - apply SV; [clear; lia| exact C72].
    - apply SV; [clear; lia| exact C80].
    - exact PA2.
    - exact IA2.
    - apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 WA M1 M2 EK12 OUTIMG BASE1).
    - exact Hl1.
    - exact Hl1k.
    - exact Hl1k'.
    - exact Hc.
    - exact G2c.
    - pose proof IA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KE2). cbn [PM.sm_g PM.sm_eg] in KE2. clear - KE2; lia.
    - pose proof STEP2 as (_ & _ & _ & SST2 & _). cbn [PM.sm_st] in SST2. exact SST2.
    - intros CZ. exact (proj2 (RSC ltac:(clear - CZ; lia))).
    - intros HC. exact (proj1 (RSC HC)).
    - exact ST2c.
    -
      apply (PECSD.bytes_agree RSEGS M1 M2 p len1); [apply PECF.slice_length_le; clear - Hl1 G2; lia| clear - DP0; lia| clear - DP1 Hl1k; lia| | exact BY1].
      intros i Hi. destruct HP2 as (E & _). apply E. split; [clear - Hi DP0 DP1 Hl1k; lia|]. split; [apply CLP; clear - Hi Hl1k; lia|].
      intros r0 Hr. unfold PMSPA.W_src, PMSPA.W_srcf in Hr. cbn [PM.sr_qc app] in Hr. fold os ois in Hr. unfold L5.in_rng.
      destruct (DX i ltac:(clear - Hi Hl1k; lia)) as (_ & X2 & X3 & _ & _ & X6 & _).
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - X2 X3 X6 Eos Eop; lia.
    - replace (blen pl - (rem + (eg - g)) + len1) with (blen pl - (eg - g)) by (clear - Hl1; lia). exact CHK2.
    - apply (PMASKJ.defined_dk L ar LB FF sp 20480 M1 M2 p len1 DK12); [intros i Hi; apply CLP; clear - Hi Hl1 Hl1k; lia| clear - DP0; lia| clear - DP1 Hl1k; lia| exact DP1'].
    - exact (L5SAR.ek_trans L ar LB FF sp 20480 WA M M1 M2 EK1 EK12).
    - exact (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2 DK1 DK12).
    - exact ASTK2.
    - exact HH2.
    - exact AM2.
    - eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    - exact INC2.
    - exact INCA2. }

  assert (MEMC1 : forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (len1 : Z),
      getr R2 (reg 2) = Z_to_bv 64 (sp - 80) -> getr R2 (reg 8) = Z_to_bv 64 len1 -> getr R2 (reg 9) = Z_to_bv 64 os ->
      getr R2 (reg 18) = Z_to_bv 64 (os + 288) -> getr R2 (reg 19) = Z_to_bv 64 p -> getr R2 (reg 20) = Z_to_bv 64 (os + 280) ->
      getr R2 (reg 21) = Z_to_bv 64 k -> getr R2 (reg 22) = Z_to_bv 64 2147450880 -> getr R2 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) ->
      (forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R (reg x)) ->
      L5.u64_at RSEGS M2 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M2 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
      L5.u64_at RSEGS M2 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M2 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
      L5.u64_at RSEGS M2 (sp - 40) (bv_unsigned (getr R (reg 19))) -> L5.u64_at RSEGS M2 (sp - 48) (bv_unsigned (getr R (reg 20))) ->
      L5.u64_at RSEGS M2 (sp - 56) (bv_unsigned (getr R (reg 21))) -> L5.u64_at RSEGS M2 (sp - 64) (bv_unsigned (getr R (reg 22))) ->
      L5.u64_at RSEGS M2 (sp - 72) (bv_unsigned (getr R (reg 23))) -> L5.u64_at RSEGS M2 (sp - 80) (bv_unsigned (getr R (reg 24))) ->
      L5.u64_at RSEGS M2 (os + 264) qc -> L5.u64_at RSEGS M2 (os + 272) 16384 -> L5.u64_at RSEGS M2 (os + 280) de -> L5.u64_at RSEGS M2 (os + 288) rem ->
      1 <= rem -> len1 = Z.min k rem -> L5.defined M2 p len1 ->
      L5.bytes_at RSEGS M2 p (UbjRef.slice pl (blen pl - (rem + (eg - g))) len1) ->
      L5.bytes_at RSEGS M2 de (UbjRef.slice pl (blen pl - (rem + (eg - g))) rem) ->
      L5SAR.ek L ar LB FF sp 20480 WA M M2 -> L5SAR.dk L ar LB FF sp 20480 M M2 -> L5CA.astk ar M2 sp 20480 -> PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M2 ->
      PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M2 ois str (PM.STRM g eg sst) ->
      ri_inv HI LB FF LK cr Aw M2 (vml_of model2) -> L5CA.amodel_ok Aw model2 -> model_rt model model2 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 0xb549c M2 model2) K).
  { intros fx2 R2 M2 model2 len1 Y2 Y8 Y9 Y18 Y19 Y20 Y21 Y22 Y23 KS2 C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C264 C272 C280 C288 Hr1' Hl1 DP2 BY1 WDE EK2 DK2 ASTK2 BASE2 IA2 HH2 AM2 MRT2.
    assert (PA2 : PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M2 op ois (PMSPA.with_src s0 (PM.SRC qc de rem))).
    { apply (PARS M2 de rem EK2 DK2 C264 C272 C280 C288); [exact G1| exact G2| exact G3]. }
    set (MV2 := mrestrict (ahid Aw model2) M2).
    pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 fb ois _ sp 20480 HH2 FOK PA2 ASTK2) as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
    fold os MV2 in P1, P8, PBIG, PZ, PW, PCE, PAV.
    pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 HH2 BASE2) as (W0 & W1' & W2'). fold MV2 in W0, W1', W2'.
    pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M2 model2 sp 20480 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3). fold MV2 in W3.
    assert (VD2 : L5.defined MV2 (os + 256) 8).
    { apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))). pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PS2 & _).
      destruct PS2 as (_ & _ & SD2 & _). exact SD2. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M2 model2 HH2) as (_ & VIS2s & _).
    assert (TS2 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M2 (sp - kk) v -> L5.u64_at RSEGS MV2 (sp - kk) v).
    { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - kk) v (VIS2s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    set (VS := fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | 39%nat => len1
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
    destruct (Z.eq_dec len1 k) as [LK1|LNK].
    -
      assert (Rr1 : 1 <= rem <= 16384) by (clear - Hr1' G3 G1; lia).
      assert (Rl1 : 1 <= len1 <= 16384) by (clear - LK1 Hk; lia).
      assert (Rr2 : 0 <= rem - len1 <= 16383) by (clear - Hl1 LK1 Rr1 Hk; rewrite LK1 in Hl1; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; lia).
      assert (Y21' : getr R2 (reg 21) = Z_to_bv 64 len1) by (rewrite LK1; exact Y21).
      pose proof (PMASRP.asrBeq_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z10 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                     & V288 & V280 & V264 & V272 & _).
      unfold PMSPA.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M2 model2 fx2 fx3 R2 0xb549c R3 0xb5748 M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK Aw _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      apply (FIN fx3 R3 M3 model3 LK Aw (de + len1) (rem - len1) g sst len1).
      + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
      + intros x Hx. unfold L5SAR.cs_all in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                  | rewrite Z2; exact (eq_sym Rsp)
                  | rewrite (KS3 _) by inl; apply KS2; inl ] |]).
        destruct Hx.
      + exact Z10.
      + apply TO3; [lia| lia| exact V264].
      + apply TO3; [lia| lia| exact V272].
      + apply TO3; [lia| lia| exact V280].
      + apply TO3; [lia| lia| exact V288].
      + clear - G1 Rl1; lia.
      + clear - Rr2; lia.
      + clear - G3 Rl1; lia.
      + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
      + pose proof (PMASKJ.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. clear - SZ; lia.
      + intros X; exact X.
      + clear - LK1 Hk; lia.
      + clear; lia.
      + intros _; clear - Rl1; lia.
      + intros X. exfalso. clear - X Rl1; lia.
      + exact CST2.
      + intros X. exfalso. clear - X LK1; lia.
      + apply (PECSD.bytes_agree RSEGS M2 M3 p len1); [apply PECF.slice_length_le; clear - Rl1; lia| clear - DP0; lia| clear - DP1 LK1; lia| | exact BY1].
        intros i Hi. destruct (DX i ltac:(clear - Hi LK1; lia)) as (X1 & _ & X3 & _). apply FR3; [clear - Hi DP0 DP1 LK1; lia| unfold W1; clear - X1 X3 Eos Eop; lia].
      + apply (PECSD.bytes_agree RSEGS M2 M3 (de + len1) (rem - len1)); [apply PECF.slice_length_le; clear - Rr2; lia| clear - G1 Q0 Rl1; lia| clear - G3 Q4 SLO SHI SPT Rl1 Rr2; lia| | exact (PECSD.window_advance RSEGS M2 pl de (blen pl - (rem + (eg - g))) len1 rem ltac:(clear - CPOS; lia) ltac:(clear - Rl1 Hl1; Lia.lia) ltac:(clear - IE2; lia) WDE)].
        intros i Hi. pose proof (APQO os 296 AO) as ZQ. apply FR3; [clear - Hi G1 G3 Q0 Q4 SLO SHI SPT Rr2 Rl1; lia| unfold W1; clear - Hi ZQ G1 G3 Q4 SLO Rr2 Rl1; lia].
      + apply (L5.defined_grows M2 M3 p len1 MGM3 DP2).
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2). apply EKWA. exact EK23.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2). apply L5SAR.dk_grows. exact MGM3.
      + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
      + exact HH3.
      + exact AM3.
      + eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
      + apply incl_refl.
      + apply incl_refl.
    -
      assert (LR : len1 = rem /\ rem < k) by (clear - Hl1 LNK; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; lia).
      destruct LR as (LR1 & LR2).
      assert (Rr1 : 1 <= len1 <= 16383) by (clear - Hr1' LR1 LR2 Hk; lia).
      assert (Rr2 : 2 <= k <= 16384) by (clear - Hr1' LR2 Hk; lia).
      assert (Rr3 : 1 <= k - len1 <= 16383) by (clear - Hr1' LR1 LR2 Hk; lia).
      assert (C288' : L5.u64_at RSEGS M2 (os + 288) len1) by (rewrite LR1; exact C288).
      pose proof (PMASRP.asrBne_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
          | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z10 & Z11 & Z12 & Z21 & Z24 & V280 & V288 & V264 & V272 & PP). pdestr PP.
      unfold PMSPA.cfg.
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M2 model2 fx2 fx3 R2 0xb549c R3 0xb58c8 M3v W1 K HH2 AM2 MS3 MG3).
      { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
      { exact W1ok. }
      intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
      assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK Aw _ HH2 FR3).
      assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M3 model3 HH3) as (_ & VIS3s & _).
      assert (TS3 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M3v (sp - kk) v -> L5.u64_at RSEGS M3 (sp - kk) v).
      { intros kk v Hkk X. rewrite <- VIS3, <- HID3 in X.
        apply (proj1 (L5A.u64_at_vis _ M3 (sp - kk) v (VIS3s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (KSB : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%nat -> getr R3 (reg x) = getr R2 (reg x)).
      { intros x Hx. apply KS3. revert x Hx. apply (PMASR1.sub_in PMASRP.KS_asrBne). vm_compute. reflexivity. }
      apply (FILLC fx3 R3 M3 model3 len1); try (apply TS3; [clear; lia| assumption]); try (apply TO3; [clear; lia| clear; lia| assumption]).
      + exact Z1. + rewrite (KSB 2%nat) by inl. exact Y2. + rewrite (KSB 8%nat) by inl. exact Y8. + rewrite (KSB 9%nat) by inl. exact Y9.
      + exact Z10. + exact Z11. + exact Z12.
      + rewrite (KSB 18%nat) by inl. exact Y18. + rewrite (KSB 19%nat) by inl. exact Y19. + rewrite (KSB 20%nat) by inl. exact Y20.
      + exact Z21. + rewrite (KSB 22%nat) by inl. exact Y22. + rewrite (KSB 23%nat) by inl. exact Y23. + exact Z24.
      + intros x Hx. rewrite (KSB x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KS2. revert x Hx. apply (PMASR1.sub_in [3; 4; 24; 25; 26; 27]%nat). vm_compute. reflexivity.
      + exact LR1.
      + clear - LR1 LR2; lia.
      + clear - Rr3; lia.
      + apply (L5.defined_grows M2 M3 p len1 MGM3 DP2).
      + apply (PECSD.bytes_agree RSEGS M2 M3 p len1); [apply PECF.slice_length_le; clear - Rr1; lia| clear - DP0; lia| clear - DP1 LR1 LR2; lia| | exact BY1].
        intros i Hi. destruct (DX i ltac:(clear - Hi LR1 LR2; lia)) as (X1 & _ & X3 & _). apply FR3; [clear - Hi DP0 DP1 LR1 LR2; lia| unfold W1; clear - X1 X3 Eos Eop; lia].
      + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK2). apply EKWA. exact EK23.
      + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK2). apply L5SAR.dk_grows. exact MGM3.
      + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
      + apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 WA M2 M3 (EKWA M2 M3 EK23) OUTIMG BASE2).
      + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
      + exact HH3.
      + exact AM3.
      + eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]. }

  assert (VD0 : L5.defined MV (os + 256) 8) by (apply (proj2 (L5A.defined_vis _ M (os + 256) 8 ltac:(apply OAV; lia))); exact SD256).
  assert (DEB : 4096 <= de <= 140737488338944) by (clear - G1 G2 G3 Q0 Q4 SLO SHI SPT; lia).
  set (W0 := fun a => sp - 80 <= a < sp - 80 + 80).
  assert (W0ok : forall a, 0 <= a < 2 ^ 64 -> W0 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6914048).
  { intros a Ha Wa. unfold W0 in Wa. split; [|intros X; clear - Wa X SL80 SPT; lia].
    unfold aclientw, aclient_g. right; left. split; [clear - Wa SL80 SH80; lia| intros X; clear - X; lia]. }
  assert (EKW0 : forall M0 M1 LK0 Aw0 Vv, ri_inv HI LB FF LK0 cr Aw0 M0 Vv -> (forall a, 0 <= a < 2 ^ 64 -> ~ W0 a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                 L5SAR.ek L ar LB FF sp 20480 [] M0 M1).
  { intros M0 M1 LK0 Aw0 Vv HH0 FR. apply (L5SAR.ek_piece L ar LB FF sp 20480 [] M0 M1 W0 FR). intros a Ha CL O X.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 _ sp 20480 a HH0 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; unfold W0 in X; clear - X; lia| unfold W0 in X; clear - X Y SL80; lia]. }
  unfold PMSPA.cfg. cbn [pa_src_read PeCLayoutA.CADDR_A].
  destruct (Z.eq_dec rem 0) as [RZ|RNZ].
  {
    subst rem.
    destruct (Z.eq_dec k 16384) as [KF|KNF].
    {
      subst k. destruct (D16K eq_refl) as (c0 & n0 & q0 & ETB & Dq1 & Dq2 & TIN).
      destruct IST as [ST0|ST2].
      2:{
        subst sst.
        pose proof (PMASRP.asrA0e_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois | _ => 0 end)) as P.
        cbn beta iota in P.
        L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
            | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
            | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
            | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
            | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
            | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
            | |- _ \/ _ => right; L5FastLia.plia
            | |- _ => L5FastLia.plia end]).
        destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & Z10 & Z11 & Z12 & V288 & PP). pdestr PP.
        apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb540c R1 0xb5748 M1v W1 K HH AM MS1 MG1).
        { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
        { exact W1ok. }
        intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
        assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1) by exact (EKW1 M M1 LK Aw _ HH FR1).
        assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
        { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
        assert (KSA : forall x, In x L5SAR.cs_all -> getr R1 (reg x) = getr R (reg x)).
        { intros x Hx. apply KS1. revert x Hx. apply (PMASR1.sub_in PMASRP.KS_asrA0e). vm_compute. reflexivity. }
        apply (FIN fx1 R1 M1 model1 LK Aw de 0 g 2 0).
        + rewrite (KS1 1%nat) by inl. exact Rra.
        + exact KSA.
        + exact Z10.
        + apply TO1; [lia| lia| assumption].
        + apply TO1; [lia| lia| assumption].
        + apply TO1; [lia| lia| assumption].
        + apply TO1; [lia| lia| exact V288].
        + exact G1.
        + clear; lia.
        + clear - G3; lia.
        + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M M1 _ fb str _ sp 20480 HH FOK SOWN EK01 IA).
        + pose proof (PMASKJ.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. clear - SZ; lia.
        + intros X; exact X.
        + clear; lia.
        + clear; lia.
        + intros X. exfalso. clear - X; lia.
        + intros _. split; reflexivity.
        + intros _. exact (CST2 eq_refl).
        + intros _. pose proof (CST2 eq_refl) as EG. clear - EG; lia.
        + unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
        + unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
        + intros i Hi. exfalso. clear - Hi; lia.
        + apply EKWA. exact EK01.
        + apply L5SAR.dk_grows. exact MGM1.
        + apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1).
        + exact HH1.
        + exact AM1.
        + exact MRT1.
        + apply incl_refl.
        + apply incl_refl. }
      subst sst.

      pose proof (PMASRP.asrA0d_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois | _ => 0 end)) as P.
      cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
          | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
          | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
          | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T13 & T18 & T19 & T20 & T21 & T22 & T23 & T24
                     & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
      apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb540c R1 0xdc384 M1v W0 K HH AM MS1 MG1).
      { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
      { exact W0ok. }
      intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
      assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1) by exact (EKW0 M M1 LK Aw _ HH FR1).
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
      assert (TS1 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M1 (sp - kk) v).
      { intros kk v Hkk X. rewrite <- VIS1, <- HID1 in X.
        apply (proj1 (L5A.u64_at_vis _ M1 (sp - kk) v (VIS1s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
      assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
      assert (OS1 : forall a, os <= a < os + 296 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. apply FR1; [clear - Ha O1; lia| unfold W0; clear - Ha OCE SL80 SLO; lia]. }
      assert (IA1 : PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M1 ois str (PM.STRM g eg 0)).
      { apply (PMKA.iss_keepA RSEGS PeCLayoutA.CADDR_A L ar LB FF sp 20480 _ M M1 EK01 PMKA.wapp_nil FRB BRB ois str _ AOI SOWN); [intros i _ r0 []| intros c1 n1 p1 _ i _ r0 []| exact IA]. }
      assert (BASE1 : PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M1) by (apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M M1 EK01); [intros a _ r0 []| exact BASE]).
      assert (M8a : (sp - 20480) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 20480) with (sp + (-1280) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
      assert (M8b : (sp - 80 - 16384) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 80 - 16384) with (sp + (-1029) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16).
      assert (STK1 : shadow_zero M1 (sp - 80 - 16384) (16384 / 8)).
      { change (16384 / 8) with 2048. change (20480 / 8) with 2560 in STKSH.
        apply (PMKA.shadow_zero_sub M1 (sp - 20480) 2560); [exact M8a| exact M8b| clear; lia| clear; lia| clear; lia|].
        apply (PMKA.stksh_keepA L ar LB FF sp 20480 [] M M1 EK01 PMKA.wapp_nil (sp - 20480) 2560); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| exact M8a| clear; lia| exact STKSH]. }

      assert (APG : p + 16384 <= g \/ eg <= p).
      { pose proof (PMASKJ.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c1 & n1 & q1 & E & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
        - destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 ois 272 HH TIN AOI) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; Lia.lia.
        - assert (SIN : In (q1, c1) LBX) by (apply INCS; rewrite E; left; reflexivity).
          assert (NS : q0 <> q1) by (apply (PMASKJ.fst_neq_appA (PM.parser_own s0) LBX q0 c0 q1 c1); [exact ND| unfold s0, PM.parser_own, PM.vs_own; rewrite ETB; cbn; right; right; left; reflexivity| exact SIN]).
          destruct (PMASKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q0 c0 q1 c1 HH TIN (SOWN _ ltac:(rewrite E; left; reflexivity)) NS) as [Z1|Z1]; clear - Y1 Y2 Z1 Dq1 Dq2; Lia.lia. }
      unfold PECXGA.cxsgetn_spec in XS. cbn [pa_xsgetn PeCLayoutA.CADDR_A] in XS.
      apply (XS fx1 R1 M1 model1 K LB FF LK Aw cr (sp - 80) 743028 ois p str (PM.STRM g eg 0) HH1 AM1 K0).
      { split; [rewrite L5K.rl1; exact T1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
        split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
        change (PMSPA.pm_scr 2) with 16384. split; [|exact STK1].
        apply (L5SAR.astk_sub ar M1 M1 sp 20480 80 16384 ASTK1 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
        replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
      { intros kk Hkk. specialize (FRM kk Hkk). clear - FRM. lia. }
      { intros f Hf. specialize (FRS f Hf). clear - FRS. lia. }
      { rewrite L5K.rl10. exact T10. }
      { rewrite L5SAR.r11. rewrite (KS1 11%nat) by inl. exact A11. }
      { rewrite L5SAR.r12. rewrite (KS1 12%nat) by inl. exact A12. }
      { exact AOI. }
      { exact I8. }
      { exact IA1. }
      { exact BASE1. }
      { exact SOWN. }
      { exists q0, c0. split; [exact TIN| unfold PM.CHUNK; split; [exact Dq1| exact Dq2]]. }
      { unfold PM.CHUNK. intros a Ha. apply (PMFA.accA_agree M M1 p 16384 (AGSHP M M1 [] EK01 PMKA.wapp_nil) DAP a). exact Ha. }
      { cbn [PM.sm_g PM.sm_eg]. unfold PM.CHUNK. exact APG. }
      intros fx2 R2 M2 model2 LK2 Aw2 c RP2 A10c Hc IA2 D2 COPYB HP2 MRT2 INC2 INCA2 AM2 HH2.
      change (PMSPA.pm_scr 2) with 16384 in HP2. unfold PM.CHUNK in Hc, HP2. cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hc, IA2. rewrite L5K.rl10 in A10c.
      assert (C0 : 0 <= c <= 16384 /\ g + c <= eg).
      { pose proof (PMASKJ.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ. rewrite Hc. clear - SZ.
        destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
      assert (OUTX : forall a, aclient L ar LB FF sp 20480 a -> L5.outside WA a -> L5.outside [(ois + 40, 8); (p, 16384)] a).
      { intros a _ O r0 [<-|[<-|[]]] X.
        - apply (O (ois + 40, 8)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; cbn [PM.sr_qc app]; right; left; reflexivity| exact X].
        - apply (O (p, 16384)); [unfold WA; apply in_or_app; right; left; reflexivity| exact X]. }
      assert (EK12 : L5SAR.ek L ar LB FF sp 20480 WA M1 M2).
      { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 16384 WA _ M1 M2 HP2); [clear; lia| clear; lia| exact OUTX]. }
      assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 16384 _ M1 M2 HP2); clear; lia).
      assert (ASTK2 : L5CA.astk ar M2 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 80) 16384 _ ASTK1 HP2); clear - TOP; lia).
      assert (KF2 : forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
        - apply (L5SAR.stack_client L ar LB FF (sp - 80) 16384 a); clear - Ha SL80 SHI SPT; lia.
        - intros r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Ha ICE SL80 SLO; lia|].
          intros Y. destruct (DX a Y) as (X1 & _). apply X1. clear - Ha; lia. }
      assert (KO2 : forall a, os <= a < os + 296 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha O1; lia|]. split.
        - apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
        - intros r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Ha IOS; lia|].
          intros Y. destruct (DX a Y) as (_ & _ & X3 & _). apply X3. clear - Ha Eos Eop; lia. }
      assert (CO : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
      { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; rewrite KO2, OS1 by (clear - Ha Hb Hi; lia); reflexivity| clear - Ha O1; lia| clear - Hb O1; lia| exact X]. }
      assert (EK02 : L5SAR.ek L ar LB FF sp 20480 WA M M2).
      { apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M1 M2); [| exact EK12]. apply (L5SAR.ek_W L ar LB FF sp 20480 WA [] M M1 EK01). intros a _ r0 []. }
      assert (DK02 : L5SAR.dk L ar LB FF sp 20480 M M2) by (apply (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]).
      assert (PA2 : PM.parser_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA PMSPA.annA M2 op ois (PMSPA.with_src s0 (PM.SRC qc de 0))).
      { apply (PARS M2 de 0 EK02 DK02); [apply CO; [clear; lia| clear; lia| exact S264]| apply CO; [clear; lia| clear; lia| exact S272]
                                       | apply CO; [clear; lia| clear; lia| exact S280]| apply CO; [clear; lia| clear; lia| exact S288]| exact G1| clear; lia| clear - G3; lia]. }
      assert (BASE2 : PMSTA.base_okA RSEGS PeCLayoutA.CADDR_A M2) by (apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 WA M1 M2 EK12 OUTIMG BASE1)).
      set (MV2 := mrestrict (ahid Aw2 model2) M2).
      pose proof (PMASKJ.src_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb ois _ sp 20480 HH2 FOK PA2 ASTK2) as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
      fold os MV2 in P1, P8, PBIG, PZ, PW, PCE, PAV.
      pose proof (PMASKJ.iss_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb str _ sp 20480 HH2 FOK IA2 ASTK2) as ((J1 & J8 & JBIG) & JZ & JW & JCE & JAV & _ & _).
      fold ois MV2 in J1, J8, JBIG, JZ, JW, JCE, JAV.
      pose proof (PMASKJ.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0' & W1' & W2'). fold MV2 in W0', W1', W2'.
      pose proof (PMASKJ.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 20480 80 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3'). fold MV2 in W3'.
      pose proof (PMASKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x136e10 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1'.
      pose proof (PMASKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x136d78 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2'.
      cbn in VT1', VT2'. fold MV2 in VT1', VT2'.
      pose proof IA2 as (H0j & _ & _ & H16j & _ & _ & _ & _ & _ & _ & _ & _ & IOSBj & _ & _).
      destruct IOSBj as (I0j & I32j & I36j & I40j & _ & _ & _ & _ & _).
      cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A] in H0j, H16j, I0j, I32j, I36j, I40j.
      replace (ois + 120 + 32) with (ois + 152) in I32j by lia. replace (ois + 120 + 36) with (ois + 156) in I36j by lia.
      replace (ois + 120 + 40) with (ois + 160) in I40j by lia.
      assert (S264' : L5.u64_at RSEGS M2 (os + 264) qc) by (apply CO; [clear; lia| clear; lia| exact S264]).
      assert (S272' : L5.u64_at RSEGS M2 (os + 272) 16384) by (apply CO; [clear; lia| clear; lia| exact S272]).
      assert (S280' : L5.u64_at RSEGS M2 (os + 280) de) by (apply CO; [clear; lia| clear; lia| exact S280]).
      assert (S288' : L5.u64_at RSEGS M2 (os + 288) 0) by (apply CO; [clear; lia| clear; lia| exact S288]).
      assert (S240' : L5.u64_at RSEGS M2 (os + 240) ois) by (apply CO; [clear; lia| clear; lia| exact S240]).
      assert (S248' : L5.u64_at RSEGS M2 (os + 248) (ois + 16)) by (apply CO; [clear; lia| clear; lia| exact S248]).
      pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
      assert (TS2 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS MV2 (sp - kk) v).
      { intros kk v Hkk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - kk) v (VIS2s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
        apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia|].
        apply TS1; [exact Hkk| exact X]. }
      assert (VD2 : L5.defined MV2 (os + 256) 8).
      { apply (proj2 (L5A.defined_vis _ M2 (os + 256) 8 ltac:(apply PAV; lia))). pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PS2 & _).
        destruct PS2 as (_ & _ & SD2 & _). exact SD2. }
      assert (RG : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
      assert (Y2 := T2). rewrite <- (RG 2%nat ltac:(inl)) in Y2. assert (Y8 := T8). rewrite <- (RG 8%nat ltac:(inl)) in Y8.
      assert (Y9 := T9). rewrite <- (RG 9%nat ltac:(inl)) in Y9. assert (Y18 := T18). rewrite <- (RG 18%nat ltac:(inl)) in Y18.
      assert (Y19 := T19). rewrite <- (RG 19%nat ltac:(inl)) in Y19. assert (Y20 := T20). rewrite <- (RG 20%nat ltac:(inl)) in Y20.
      assert (Y21 := T21). rewrite <- (RG 21%nat ltac:(inl)) in Y21. assert (Y22 := T22). rewrite <- (RG 22%nat ltac:(inl)) in Y22.
      assert (Y23 := T23). rewrite <- (RG 23%nat ltac:(inl)) in Y23. assert (Y24 := T24). rewrite <- (RG 24%nat ltac:(inl)) in Y24.
      set (VE := fun j => match j with 2%nat => sp | 33%nat => c | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 45%nat => ois
                                | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9))
                                | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20))
                                | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23))
                                | 73%nat => bv_unsigned (getr R (reg 24)) | _ => 0 end).
      destruct (Z.eq_dec c 16384) as [CF|CNF].
      -
        rewrite CF in A10c, D2, C0, IA2.
        pose proof (PMASRP.asrE1_conc fx2 R2 MV2 VE) as P. unfold VE in P. cbn beta iota in P.
        L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
            | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
            | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
            | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
            | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
            | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
            | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
            | |- _ \/ _ => right; L5FastLia.plia
            | |- _ => L5FastLia.plia end]).
        destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                       & V264 & V272 & V280 & V288 & _).
        apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb5674 R3 0xb5748 M3v W1 K HH2 AM2 MS3 MG3).
        { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
        { exact W1ok. }
        intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
        assert (EK23 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M2 M3) by exact (EKW1 M2 M3 LK2 Aw2 _ HH2 FR3).
        assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
        { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }

        set (data := PM.vs_data (ois + 80) str) in EGD, IE2, CBS.
        set (sl := UbjRef.slice pl (g - data) c).
        pose proof (PECF.slice_length_le pl (g - data) c ltac:(clear - C0 CF; lia)) as SL. fold sl in SL.
        assert (GW : (ois + 81 <= g /\ eg <= ois + 104 /\ ois + 272 <= ahl_ceil ar /\ 0 <= ois) \/ (4096 <= g /\ eg <= ahl_ceil ar)).
        { destruct (PMASKJ.iss_unread_whereA M ois str _ IA) as [(Yg1 & Yg2)|(c9 & n9 & p9 & Hs9 & Yg1 & Yg2)]; cbn [PM.sm_g PM.sm_eg] in Yg1, Yg2.
          - left. destruct AOI as (f0 & Hf0 & F01 & F02). destruct (WF f0 Hf0) as (Yw1 & Yw2 & _).
            unfold FS_BYTES in FSCEIL, Yw1, Yw2. clear - Yg1 Yg2 F01 F02 Yw1 Yw2 FSA0 FSCEIL. lia.
          - right. assert (PIN : In (p9, c9) LB) by (apply SOWN; rewrite Hs9; left; reflexivity).
            destruct (WB _ PIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4. clear - Yg1 Yg2 B0 B4. lia. }
        assert (BYg : L5.bytes_at RSEGS M g sl).
        { apply (PECSD.payload_at_gptr RSEGS M pl data g c CBS); clear - EGD IE2 CSZ C0 CF; Lia.lia. }
        assert (BYg1 : L5.bytes_at RSEGS M1 g sl).
        { apply (L5C.bytes_at_agree RSEGS M M1 g sl); [| clear - GW SLO; lia | clear - GW SL C0 CF EGD IE2 SLO SHI SPT; Lia.lia | exact BYg].
          intros i Hi. apply FR1; [clear - Hi GW SL C0 CF SLO SHI SPT; Lia.lia| unfold W0; clear - Hi GW SL C0 CF SLO; Lia.lia]. }
        pose proof (COPYB sl SL BYg1) as BY2.
        assert (BY3 : L5.bytes_at RSEGS M3 p sl).
        { apply (L5C.bytes_at_agree RSEGS M2 M3 p sl); [| clear - DP0; lia | clear - DP1 SL C0 CF; lia | exact BY2].
          intros i Hi. destruct (DX i ltac:(clear - Hi SL C0 CF; lia)) as (X1 & X2 & X3 & _). apply FR3; [clear - Hi DP0 DP1 SL C0 CF; lia|].
          unfold W1. clear - X1 X2 X3 Eos Eop. lia. }
        apply (FIN fx3 R3 M3 model3 LK2 Aw2 de 0 (g + 16384) 0 16384).
        + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
        + intros x Hx. unfold L5SAR.cs_all in Hx.
          repeat (destruct Hx as [<-|Hx];
            [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                    | rewrite Z2; exact (eq_sym Rsp)
                    | rewrite (KS3 _) by inl; rewrite (RG _) by inl; apply KS1; inl ] |]).
          destruct Hx.
        + rewrite (KS3 10%nat) by inl. exact A10c.
        + apply TO3; [lia| lia| exact V264].
        + apply TO3; [lia| lia| exact V272].
        + apply TO3; [lia| lia| exact V280].
        + apply TO3; [lia| lia| exact V288].
        + exact G1.
        + clear; lia.
        + clear - G3; lia.
        + apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK2 cr Aw2 M2 M3 _ fb str _ sp 20480 HH2 FOK SOWN EK23 IA2).
        + clear - C0; lia.
        + intros X; exact X.
        + clear; lia.
        + clear; lia.
        + intros X. exfalso. clear - X; lia.
        + intros X. exfalso. clear - X; lia.
        + intros X; discriminate X.
        + intros X. exfalso. clear - X; lia.
        + rewrite <- CF. replace (blen pl - (0 + (eg - g))) with (g - data) by (clear - EGD CSZ; lia). exact BY3.
        + unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
        + apply (L5.defined_grows M2 M3 p 16384 MGM3 D2).
        + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK02). apply EKWA. exact EK23.
        + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
        + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
        + exact HH3.
        + exact AM3.
        + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
        + exact INC2.
        + exact INCA2.
      -
        assert (Cr : 0 <= c <= 16383) by (clear - C0 CNF; lia).
        pose proof (PMASRP.asrE2_conc fx2 R2 MV2 VE) as P. unfold VE in P. cbn beta iota in P.
        L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
            | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [L5FastLia.plia| assumption]
            | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
            | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
            | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
            | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
            | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
            | |- _ \/ _ => right; L5FastLia.plia
            | |- _ => L5FastLia.plia end]).
        destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Z1 & Z2 & Z8 & Z9 & Z12 & Z13 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24
                       & V152 & V264 & V272 & V280 & V288 & _).
        set (W2 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (os + 256 <= a < os + 256 + 40) \/ (ois + 152 <= a < ois + 152 + 4)).
        assert (W2ok : forall a, 0 <= a < 2 ^ 64 -> W2 a -> aclientw L ar LB FF 0 0 a /\ ~ 65536 <= a < 6914048).
        { intros a Ha Wa. destruct Wa as [Wa|[Wa|Wa]]; [apply W1ok; [exact Ha| left; exact Wa]| apply W1ok; [exact Ha| right; exact Wa]|].
          split; [|intros X; clear - Wa X I1; lia].
          unfold aclientw, aclient_g. do 3 right. left. destruct AOI as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [clear - Wa X1 X2; lia| intros X; clear - Wa X X1; lia]. }
        apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb5674 R3 0xb5748 M3v W2 K HH2 AM2 MS3 MG3).
        { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
        { exact W2ok. }
        intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
        set (WE := [(os + 256, 40); (ois + 152, 4)]).
        assert (EK23 : L5SAR.ek L ar LB FF sp 20480 WE M2 M3).
        { apply (L5SAR.ek_piece L ar LB FF sp 20480 WE M2 M3 W2 FR3). intros a Ha CL O [X|[X|X]].
          - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 20480 a HH2 SPT CL) as [(Yc1 & Yc2)|Yc]; [apply Yc2; clear - X; lia| clear - X Yc SL80; lia].
          - apply (O (os + 256, 40)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
          - apply (O (ois + 152, 4)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
        assert (WSE : PMKA.wapp WE).
        { unfold WE. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - OBIG; Lia.lia|].
          apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - IBIG; Lia.lia| apply PMKA.wapp_nil]. }
        assert (EK23W : L5SAR.ek L ar LB FF sp 20480 WA M2 M3).
        { apply (L5SAR.ek_W L ar LB FF sp 20480 WA WE M2 M3 EK23). intros a O r0 [<-|[<-|[]]] X.
          - apply (O (os + 256, 40)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; cbn [PM.sr_qc app]; left; reflexivity| exact X].
          - apply (O (ois + 152, 4)); [unfold WA, PMSPA.W_src, PMSPA.W_srcf; cbn [PM.sr_qc app]; right; right; left; reflexivity| exact X]. }
        assert (TO3 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
        { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u64_at_vis _ M3 a v ltac:(apply PAV; lia) ltac:(lia) ltac:(lia))). exact X. }
        assert (U152 : L5.u32_at RSEGS M3 (ois + 152) 2).
        { rewrite <- VIS3 in V152. apply (proj1 (L5A.u32_at_vis _ M3 (ois + 152) 2 ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))). exact V152. }
        assert (OUTI : forall i, ois <= i < ois + 272 -> ~ (ois + 152 <= i < ois + 156) -> L5.outside WE i).
        { intros i Hi N r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; [clear - Hi IOS; lia| clear - N; lia]. }
        assert (IA3 : PM.iss_at RSEGS PeCLayoutA.CADDR_A PMSPA.accA M3 ois str (PM.STRM (g + c) eg 2)).
        { apply (PMASKJ.iss_st_updA M2 M3 ois str (g + c) eg 0 2 IA2); [clear - J1; lia| clear - J1; lia| | | | exact MGM3| | exact U152| right; reflexivity].
          - apply (PMKA.agA_obj L ar LB FF sp 20480 WE M2 M3 EK23 WSE FRB ois 152); [apply (PMASKJ.aobj_fb FF fb); [exact FOK| unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia| unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia]|].
            intros i Hi. apply OUTI; clear - Hi; lia.
          - apply (PMKA.agA_obj L ar LB FF sp 20480 WE M2 M3 EK23 WSE FRB (ois + 156) 116); [apply (PMASKJ.aobj_fb FF fb); [exact FOK| unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia| unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia]|].
            intros i Hi. apply OUTI; clear - Hi; lia.
          - apply (PMKA.agsh_obj L ar LB FF sp 20480 WE M2 M3 EK23 WSE FRB (ois + 152) 4). apply (PMASKJ.aobj_fb FF fb); [exact FOK| unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia| unfold ois, PMSPA.o_is; cbn [pa_off_is PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A]; lia].
          - intros c1 n1 q1 E. assert (SIN : In (q1, c1) LB) by (apply SOWN; rewrite E; left; reflexivity).
            apply (PMKA.agA_blk L ar LB FF sp 20480 WE M2 M3 EK23 WSE BRB q1 c1 SIN). intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd].
            + destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH SIN AO) as [Z|Z]; clear - Hi Z; lia.
            + destruct (PMASKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 ois 272 HH SIN AOI) as [Z|Z]; clear - Hi Z; lia. }

        set (data := PM.vs_data (ois + 80) str) in EGD, IE2, CBS.
        set (sl := UbjRef.slice pl (g - data) c).
        pose proof (PECF.slice_length_le pl (g - data) c ltac:(clear - C0 Cr; lia)) as SL. fold sl in SL.
        assert (GW : (ois + 81 <= g /\ eg <= ois + 104 /\ ois + 272 <= ahl_ceil ar /\ 0 <= ois) \/ (4096 <= g /\ eg <= ahl_ceil ar)).
        { destruct (PMASKJ.iss_unread_whereA M ois str _ IA) as [(Yg1 & Yg2)|(c9 & n9 & p9 & Hs9 & Yg1 & Yg2)]; cbn [PM.sm_g PM.sm_eg] in Yg1, Yg2.
          - left. destruct AOI as (f0 & Hf0 & F01 & F02). destruct (WF f0 Hf0) as (Yw1 & Yw2 & _).
            unfold FS_BYTES in FSCEIL, Yw1, Yw2. clear - Yg1 Yg2 F01 F02 Yw1 Yw2 FSA0 FSCEIL. lia.
          - right. assert (PIN : In (p9, c9) LB) by (apply SOWN; rewrite Hs9; left; reflexivity).
            destruct (WB _ PIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4. clear - Yg1 Yg2 B0 B4. lia. }
        assert (BYg : L5.bytes_at RSEGS M g sl).
        { apply (PECSD.payload_at_gptr RSEGS M pl data g c CBS); clear - EGD IE2 CSZ C0 Cr; Lia.lia. }
        assert (BYg1 : L5.bytes_at RSEGS M1 g sl).
        { apply (L5C.bytes_at_agree RSEGS M M1 g sl); [| clear - GW SLO; lia | clear - GW SL C0 Cr EGD IE2 SLO SHI SPT; Lia.lia | exact BYg].
          intros i Hi. apply FR1; [clear - Hi GW SL C0 Cr SLO SHI SPT; Lia.lia| unfold W0; clear - Hi GW SL C0 Cr SLO; Lia.lia]. }
        pose proof (COPYB sl SL BYg1) as BY2.
        assert (BY3 : L5.bytes_at RSEGS M3 p sl).
        { apply (L5C.bytes_at_agree RSEGS M2 M3 p sl); [| clear - DP0; lia | clear - DP1 SL C0 Cr; lia | exact BY2].
          intros i Hi. destruct (DX i ltac:(clear - Hi SL C0 Cr; lia)) as (X1 & X2 & X3 & _). apply FR3; [clear - Hi DP0 DP1 SL C0 Cr; lia|].
          unfold W2. clear - X1 X2 X3 Eos Eop. lia. }
        apply (FIN fx3 R3 M3 model3 LK2 Aw2 de 0 (g + c) 2 c).
        + rewrite Z1, Z_to_bv_bv_unsigned. exact Rra.
        + intros x Hx. unfold L5SAR.cs_all in Hx.
          repeat (destruct Hx as [<-|Hx];
            [ first [ match goal with H : getr R3 (reg ?y) = Z_to_bv 64 (bv_unsigned (getr R (reg ?y))) |- getr R3 (reg ?y) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                    | rewrite Z2; exact (eq_sym Rsp)
                    | rewrite (KS3 _) by inl; rewrite (RG _) by inl; apply KS1; inl ] |]).
          destruct Hx.
        + rewrite (KS3 10%nat) by inl. exact A10c.
        + apply TO3; [lia| lia| exact V264].
        + apply TO3; [lia| lia| exact V272].
        + apply TO3; [lia| lia| exact V280].
        + apply TO3; [lia| lia| exact V288].
        + exact G1.
        + clear; lia.
        + clear - G3; lia.
        + exact IA3.
        + clear - C0; lia.
        + intros X; discriminate X.
        + clear - Cr; lia.
        + clear; lia.
        + intros X. exfalso. clear - X; lia.
        + intros _. split; reflexivity.
        + intros _. clear - Hc Cr C0; Lia.lia.
        + intros _. clear - Hc Cr C0; Lia.lia.
        + replace (blen pl - (0 + (eg - g))) with (g - data) by (clear - EGD CSZ; lia). exact BY3.
        + unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
        + apply (L5.defined_grows M2 M3 p c MGM3 D2).
        + apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M2 M3 EK02 EK23W).
        + apply (L5SAR.dk_trans L ar LB FF sp 20480 M M2 M3 DK02). apply L5SAR.dk_grows. exact MGM3.
        + apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3).
        + exact HH3.
        + exact AM3.
        + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3].
        + exact INC2.
        + exact INCA2. }

    assert (Kr : 1 <= k <= 16383) by (clear - Hk KNF; lia).
    pose proof (PMASRP.asrA0f_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) as P.
    cbn beta iota in P.
    L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
        | |- _ \/ _ => right; L5FastLia.plia
        | |- _ => L5FastLia.plia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & U280
                   & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8 & U264 & U272 & U288 & UD).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb540c R1 0xb58c8 M1v W1 K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { exact W1ok. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [(os + 256, 40)] M M1) by exact (EKW1 M M1 LK Aw _ HH FR1).
    assert (TO1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. rewrite <- VIS1 in X. apply (proj1 (L5A.u64_at_vis _ M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). exact X. }
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
    assert (TS1 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M1 (sp - kk) v).
    { intros kk v Hkk X. rewrite <- VIS1, <- HID1 in X.
      apply (proj1 (L5A.u64_at_vis _ M1 (sp - kk) v (VIS1s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
    apply (FILLC fx1 R1 M1 model1 0); try (apply TS1; [clear; lia| assumption]); try (apply TO1; [clear; lia| clear; lia| assumption]).
    - exact T1. - exact T2. - exact T8. - exact T9.
    - rewrite (KS1 10%nat) by inl. unfold os. rewrite <- L5K.rl10. exact A10.
    - exact T11. - exact T12. - exact T18. - exact T19. - exact T20.
    - replace (k - 0) with k by (clear; lia). exact T21.
    - exact T22. - exact T23. - exact T24.
    - intros x Hx. apply KS1. revert x Hx. apply (PMASR1.sub_in PMASRP.KS_asrA0f). vm_compute. reflexivity.
    - reflexivity.
    - clear - Hk; lia.
    - clear - Kr; lia.
    - intros i Hi. exfalso. clear - Hi; lia.
    - unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
    - apply EKWA. exact EK01.
    - apply L5SAR.dk_grows. exact MGM1.
    - apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1).
    - apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 WA M M1 (EKWA M M1 EK01) OUTIMG BASE).
    - apply (PMASKJ.src_piece_iss L ar C HI HIok LB FF LK cr Aw M M1 _ fb str _ sp 20480 HH FOK SOWN EK01 IA).
    - exact HH1.
    - exact AM1.
    - exact MRT1. }

  assert (Rr0 : 1 <= rem <= 16384) by (clear - RNZ G1 G2 G3; lia).
  assert (HEADA : exists fx1 R1 M1v, msteps RSEGS (st fx R 0xb540c MV) (st fx1 R1 0x78618 M1v) /\ mem_grows MV M1v
             /\ (forall a, 0 <= a < 2 ^ 64 -> ~ W0 a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a))
             /\ (forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R1 (reg x) = getr R (reg x))
             /\ getr R1 (reg 1) = Z_to_bv 64 742556 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 80) /\ getr R1 (reg 8) = Z_to_bv 64 (Z.min k rem)
             /\ getr R1 (reg 9) = Z_to_bv 64 os /\ getr R1 (reg 10) = Z_to_bv 64 p /\ getr R1 (reg 11) = Z_to_bv 64 de
             /\ getr R1 (reg 12) = Z_to_bv 64 (Z.min k rem) /\ getr R1 (reg 18) = Z_to_bv 64 (os + 288) /\ getr R1 (reg 19) = Z_to_bv 64 p
             /\ getr R1 (reg 20) = Z_to_bv 64 (os + 280) /\ getr R1 (reg 21) = Z_to_bv 64 k /\ getr R1 (reg 22) = Z_to_bv 64 2147450880
             /\ getr R1 (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)
             /\ L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8)))
             /\ L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18)))
             /\ L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20)))
             /\ L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22)))
             /\ L5.u64_at RSEGS M1v (sp - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M1v (sp - 80) (bv_unsigned (getr R (reg 24)))).
  { destruct (Z_le_gt_dec rem k) as [RLE|RGT].
    - assert (E1 : Z.min k rem = rem) by (clear - RLE; lia).
      assert (Ar : 0 <= -1 * rem + k <= 16383) by (clear - RLE Rr0 Hk; lia).
      pose proof (PMASRP.asrAge_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) as P.
      cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23
                     & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
      exists fx1, R1, M1v. rewrite E1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
      split; [intros x Hx; apply KS1; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrAge); vm_compute; reflexivity|].
      split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|].
      split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23|].
      split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
      split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80].
    - assert (E1 : Z.min k rem = k) by (clear - RGT; lia).
      assert (Ar1 : 2 <= rem <= 16384) by (clear - RGT Rr0 Hk; lia).
      assert (Ar2 : 1 <= k <= 16383) by (clear - RGT Rr0 Hk; lia).
      assert (Ar3 : 1 <= rem - k <= 16383) by (clear - RGT Rr0 Hk; lia).
      pose proof (PMASRP.asrAlt_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => rem | 34%nat => qc | 35%nat => de | 36%nat => os | 37%nat => p | 38%nat => k | _ => 0 end)) as P.
      cbn beta iota in P.
      L5SAR.feed P ltac:(idtac; first [assumption | lazymatch goal with
          | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
          | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; L5FastLia.plia
          | |- _ \/ _ => right; L5FastLia.plia
          | |- _ => L5FastLia.plia end]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & T21 & T22 & T23
                     & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
      exists fx1, R1, M1v. rewrite E1. split; [exact MS1|]. split; [exact MG1|]. split; [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
      split; [intros x Hx; apply KS1; revert x Hx; apply (PMASR1.sub_in PMASRP.KS_asrAlt); vm_compute; reflexivity|].
      split; [exact T1|]. split; [exact T2|]. split; [exact T8|]. split; [exact T9|]. split; [exact T10|]. split; [exact T11|].
      split; [rewrite (KS1 12%nat) by inl; rewrite <- L5SAR.r12; exact A12|].
      split; [exact T18|]. split; [exact T19|]. split; [exact T20|]. split; [exact T21|]. split; [exact T22|]. split; [exact T23|].
      split; [exact S8|]. split; [exact S16|]. split; [exact S24|]. split; [exact S32|]. split; [exact S40|].
      split; [exact S48|]. split; [exact S56|]. split; [exact S64|]. split; [exact S72| exact S80]. }
  destruct HEADA as (fx1 & R1 & M1v & MS1 & MG1 & FRZ1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T18 & T19 & T20 & T21 & T22 & T23
                     & S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80).
  set (len1 := Z.min k rem) in *.
  assert (Hl1r : 1 <= len1 <= k /\ len1 <= rem) by (unfold len1; clear - Rr0 Hk; destruct (Z.min_spec k rem) as [[X1 X2]|[X1 X2]]; rewrite X2; lia).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb540c R1 0x78618 M1v W0 K HH AM MS1 MG1 FRZ1 W0ok).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (EK01 : L5SAR.ek L ar LB FF sp 20480 [] M M1) by exact (EKW0 M M1 LK Aw _ HH FR1).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (TS1 : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M1 (sp - kk) v).
  { intros kk v Hkk X. rewrite <- VIS1, <- HID1 in X.
    apply (proj1 (L5A.u64_at_vis _ M1 (sp - kk) v (VIS1s (sp - kk) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M M1 sp 20480 ASTK MGM1)).
  assert (OS1 : forall a, os <= a < os + 296 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply FR1; [clear - Ha O1; lia| unfold W0; clear - Ha OCE SL80 SLO; lia]. }
  assert (DPL : L5.defined M1 p len1).
  { apply (L5.defined_sub M1 p k); [apply (L5.defined_grows M M1 p k MGM1 DDP)| clear; lia| clear - Hl1r; lia]. }

  apply (PECAB.memcpy_call_c L ar C HI LY HIok fx1 R1 M1 model1 K LB FF LK cr Aw (sp - 80) 742556 p de len1 HH1 AM1 K0).
  { exact T1. }
  { split; [clear; lia| reflexivity]. }
  { exact T2. }
  { rewrite (KS1 4%nat) by inl. exact Rtp. }
  { exact T10. }
  { exact T11. }
  { exact T12. }
  { clear - Hl1r Hk; lia. }
  { apply (L5SAR.astk_sub ar M1 M1 sp 20480 80 2560 ASTK1 (fun _ X => X)); [clear; lia| clear; lia| clear; lia|].
    replace (sp - 80) with (sp + (-5) * 16) by (clear; lia). rewrite Z.mod_add by (clear; lia). exact A16. }
  { intros a Ha. apply (PMFA.accA_agree M M1 p k (AGSHP M M1 [] EK01 PMKA.wapp_nil) DAP a). clear - Ha Hl1r; lia. }
  { intros i Hi. apply CLPw. clear - Hi Hl1r; lia. }
  { exact DPL. }
  { clear - DP0; lia. }
  { clear - DP1 Hl1r; lia. }
  { unfold app_rng in DAPP |- *. clear - DAPP Hl1r. Lia.lia. }
  { intros a Ha. apply (PMFA.accA_agree M M1 qc 16384); [apply (PMASKJ.agsh_blk L ar LB FF sp 20480 _ M M1 qc 16384 EK01 PMKA.wapp_nil QIN); clear - Q0 Q4 SLO SHI SPT; lia| exact ACH| clear - Ha Hl1r G1 G3; lia]. }
  { clear - DEB; lia. }
  { clear - DEB Hl1r G3 Q4 SLO SHI SPT; lia. }
  { apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M1 _ qc 16384 de len1 HH1 QIN); clear - G1 G3 Hl1r; lia. }
  { intros i Hi. apply CLQ. clear - Hi G1 G3 Hl1r; lia. }
  { apply (L5.defined_sub M1 qc 16384); [apply (L5.defined_grows M M1 qc 16384 MGM1 DCH)| clear - G1; lia| clear - G3 Hl1r; lia]. }
  { clear - DQA G1 G3 Hl1r. Lia.lia. }
  intros fx2 R2 M2 model2 RP2 DEF2 CPY2 HP2 MRT2 AM2 HH2.

  pose proof (PECF.slice_length_le pl (blen pl - (rem + (eg - g))) len1 ltac:(clear - Hl1r; lia)) as SLe.
  assert (WDE1 : L5.bytes_at RSEGS M1 de (UbjRef.slice pl (blen pl - (rem + (eg - g))) rem)).
  { apply (PECSD.bytes_agree RSEGS M M1 de rem); [apply PECF.slice_length_le; exact G2| clear - DEB; lia| clear - DEB G1 G3 Q4 SLO SHI SPT; lia| | exact CBW].
    intros i Hi. apply FR1; [clear - Hi DEB G1 G3 Q4 SLO SHI SPT; lia| unfold W0; clear - Hi G1 G3 Q4 SLO; lia]. }
  assert (KQ2 : forall a, qc <= a < qc + 16384 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha Q0 Q4 SLO SHI SPT; lia|]. split; [apply CLQ; exact Ha|].
    intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha DQA Hl1r. Lia.lia. }
  assert (WDE2 : L5.bytes_at RSEGS M2 de (UbjRef.slice pl (blen pl - (rem + (eg - g))) rem)).
  { apply (PECSD.bytes_agree RSEGS M1 M2 de rem); [apply PECF.slice_length_le; exact G2| clear - DEB; lia| clear - DEB G1 G3 Q4 SLO SHI SPT; lia| intros i Hi; apply KQ2; clear - Hi G1 G3; lia| exact WDE1]. }
  assert (BY1e : L5.bytes_at RSEGS M2 p (UbjRef.slice pl (blen pl - (rem + (eg - g))) len1)).
  { apply (PECAB.bytes_at_copy M1 M2 de p).
    - intros i Hi. apply CPY2. clear - Hi SLe. lia.
    - apply (L5.defined_sub M1 qc 16384); [apply (L5.defined_grows M M1 qc 16384 MGM1 DCH)| clear - G1; lia| clear - G3 Hl1r SLe; lia].
    - exact (PECSD.window_head RSEGS M1 pl de (blen pl - (rem + (eg - g))) len1 rem ltac:(clear - CPOS; lia) ltac:(clear - Hl1r; lia) WDE1). }
  assert (OUTD : forall a, aclient L ar LB FF sp 20480 a -> L5.outside WA a -> L5.outside [(p, len1)] a).
  { intros a _ O r0 [<-|[]] X. apply (O (p, k)); [unfold WA; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; clear - X Hl1r; lia]. }
  assert (EK12 : L5SAR.ek L ar LB FF sp 20480 WA M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 WA [(p, len1)] M1 M2 HP2); [clear; lia| clear; lia| exact OUTD]. }
  assert (EK12d : L5SAR.ek L ar LB FF sp 20480 [(p, len1)] M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ [(p, len1)] M1 M2 HP2); [clear; lia| clear; lia| intros a _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 80) 2560 _ M1 M2 HP2); clear; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480) by (apply (PMKA.astk_after_ahpres L ar LB FF M1 M2 sp 20480 (sp - 80) 2560 _ ASTK1 HP2); clear - TOP; lia).
  assert (NDP : forall a, ~ (p <= a < p + k) -> ~ (p <= a < p + len1)) by (intros a N X; apply N; clear - X Hl1r; lia).
  assert (KF2 : forall a, sp - 80 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha SLO SHI SPT; lia|]. split.
    - apply (L5SAR.stack_client L ar LB FF (sp - 80) 2560 a); clear - Ha SL80 SHI SPT; lia.
    - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (X1 & _). apply X1. clear - Ha; lia. }
  assert (KO2 : forall a, os <= a < os + 296 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [clear - Ha O1; lia|]. split.
    - apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
    - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX a Y) as (_ & _ & X3 & _). apply X3. clear - Ha Eos Eop; lia. }
  assert (WSP : PMKA.wapp [(p, len1)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH Hl1r; Lia.lia| apply PMKA.wapp_nil]. }
  assert (CO : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M2 a v).
  { intros a v Ha Hb X. apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; rewrite KO2, OS1 by (clear - Ha Hb Hi; lia); reflexivity| clear - Ha O1; lia| clear - Hb O1; lia| exact X]. }
  assert (SV : forall kk v, 8 <= kk <= 80 -> L5.u64_at RSEGS M1v (sp - kk) v -> L5.u64_at RSEGS M2 (sp - kk) v).
  { intros kk v Hkk X. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; clear - Hkk Hi; lia| clear - Hkk SLO SHI SPT; lia| clear - Hkk SLO SHI SPT; lia|].
    apply TS1; [exact Hkk| exact X]. }
  assert (RG : forall x, In x L5SAR.cs_all -> getr R2 (reg x) = getr R1 (reg x)) by (intros x Hx; apply (L5SAR.cs_of_preserved R1 R2 x RP2 Hx)).
  apply (MEMC1 fx2 R2 M2 model2 len1).
  - rewrite (RG 2%nat) by inl. exact T2.
  - rewrite (RG 8%nat) by inl. exact T8.
  - rewrite (RG 9%nat) by inl. exact T9.
  - rewrite (RG 18%nat) by inl. exact T18.
  - rewrite (RG 19%nat) by inl. exact T19.
  - rewrite (RG 20%nat) by inl. exact T20.
  - rewrite (RG 21%nat) by inl. exact T21.
  - rewrite (RG 22%nat) by inl. exact T22.
  - rewrite (RG 23%nat) by inl. exact T23.
  - intros x Hx. rewrite (RG x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KS1. exact Hx.
  - apply SV; [clear; lia| exact S8].
  - apply SV; [clear; lia| exact S16].
  - apply SV; [clear; lia| exact S24].
  - apply SV; [clear; lia| exact S32].
  - apply SV; [clear; lia| exact S40].
  - apply SV; [clear; lia| exact S48].
  - apply SV; [clear; lia| exact S56].
  - apply SV; [clear; lia| exact S64].
  - apply SV; [clear; lia| exact S72].
  - apply SV; [clear; lia| exact S80].
  - apply CO; [clear; lia| clear; lia| exact S264].
  - apply CO; [clear; lia| clear; lia| exact S272].
  - apply CO; [clear; lia| clear; lia| exact S280].
  - apply CO; [clear; lia| clear; lia| exact S288].
  - clear - Rr0; lia.
  - reflexivity.
  - exact DEF2.
  - exact BY1e.
  - exact WDE2.
  - apply (L5SAR.ek_trans L ar LB FF sp 20480 WA M M1 M2); [| exact EK12].
    apply (L5SAR.ek_W L ar LB FF sp 20480 WA [] M M1 EK01). intros a _ r0 [].
  - apply (L5SAR.dk_trans L ar LB FF sp 20480 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12].
  - exact ASTK2.
  - apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M1 M2 EK12 OUTIMG).
    apply (PMASKJ.base_keep L ar C LY LB FF sp 20480 _ M M1 EK01); [intros a _ r0 []| exact BASE].
  - apply (PMKA.iss_keepA RSEGS PeCLayoutA.CADDR_A L ar LB FF sp 20480 _ M1 M2 EK12d WSP FRB BRB ois str _ AOI SOWN).
    + intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & X2 & _). apply X2. exact Hi.
    + intros c1 n1 q1 E i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. apply NDP. intros Y. destruct (DX i Y) as (_ & _ & _ & _ & _ & _ & _ & X8 & _). apply (X8 c1 n1 q1 E). exact Hi.
    + apply (PMKA.iss_keepA RSEGS PeCLayoutA.CADDR_A L ar LB FF sp 20480 _ M M1 EK01 PMKA.wapp_nil FRB BRB ois str _ AOI SOWN); [intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
  - exact HH2.
  - exact AM2.
  - eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
Qed.

Theorem src_read_ok : PECSA.fill_buffer_spec L ar HI -> PECSA.src_read_spec L ar HI.
Proof.
  intros FB. unfold PECSA.src_read_spec, PECSPA.src_read_spec, PECSPA.csrc_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb pl s str sm Wextra HH AM K0 ENT FRM FRS FOK ALN A10 ARGS WX PA IA BASE ACCP INCS POK CONT KONT.
  apply (src_read_gen FB fx R M model K LBX FF LK Aw cr sp r fb pl s str sm Wextra HH AM K0 ENT FRM FRS FOK A10);
    [| exact WX| exact PA| exact IA| exact BASE| exact ACCP| exact INCS| exact POK| exact CONT|].
  - destruct ARGS as (q & kk & A11 & A12 & Hkk & AOD & DD & AD & APi & APo). exists q, kk. split; [exact A11|]. split; [exact A12|].
    split; [unfold PM.CHUNK; clear - Hkk; lia|]. left. split; [exact AOD|]. split; [clear - Hkk; lia|]. split; [exact DD|]. split; [exact AD|].
    split; [exact APi|]. unfold PECA.RDR_BYTES in APo. clear - APo. lia.
  - intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' ST RES _ HP MRT ICL ICA AM' HH'.
    exact (KONT fx' R' M' model' LK' Aw' src' sm' RP PA' IA' ST RES HP MRT ICL ICA AM' HH').
Qed.

End WithHeap.
End PECREADA.
