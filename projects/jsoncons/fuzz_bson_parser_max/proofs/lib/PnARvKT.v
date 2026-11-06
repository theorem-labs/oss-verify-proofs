(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmParSpecs PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PnSpecsAa
     PmModelFactsA PnStepA PmStep PgSrc PgV8 PgSrcA PnLayout PnModel PnModelFacts PnStatics PnStaticsA PnRunA PnRunAa PnASrcKit PmAUarK PmAUar PnBrObj PnBrObjA PnAParKit PnAReset1 PnOwnerOkA PnBrKitA PnARvK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.

Module PNARVKT.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.


Let base_keepW := PNBKA.base_keepW L ar C LY.
Let berr_keep := PNBKA.berr_keep L ar C LY.
Let pre_after_call := PNBKA.pre_after_call L ar.
Let blk_ceil := PNBKA.blk_ceil L ar C HI HIok.

Lemma rv_call_resize K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra nn wb : Z) :
  PMA.str_resize_spec L ar HI -> (wb = 0 \/ wb = 1) ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 224) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + PNRA.bcs_off wb) -> getr R1 (reg 11) = Z_to_bv 64 nn ->
  0 <= nn <= PM.vs_size (PNRA.bcs_str wb s1) + PM.CHUNK -> nn < 2 ^ 26 + PM.CHUNK ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 x' g' cr3,
      regs_preserved R1 R2 -> PM.vs_size x' = nn ->
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 (set_cs wb s1 x' g') sm1 ax1 cr3 ->
      (forall a, sp - 224 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_str_resize PMA.AD) M1 model1) K.
Proof.
  intros PB Hwb CTX G LM X1 RAok X2 X3 X4 X10 X11 Hn1 Hn2 KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *. change (28672 / 8) with 3584 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6897664 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 224 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF1 & _).
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044352 ltac:(lia) ltac:(lia)); lia).
  pose proof (bcs_off_rng wb Hwb) as HOFF.
  set (o := op + PNRA.bcs_off wb) in *.
  set (x := PNRA.bcs_str wb s1) in *.
  set (g := if Z.eqb wb 0 then PNM.b_ng s1 else PNM.b_tg s1).
  set (LBr := own_rest wb s1 ++ LBX).
  assert (AOo : PMSPA.aobjA FF o 24) by (apply (PNAPAR.aobj_fbB FF fb o 24 FOK); unfold o, op; clear - HOFF; lia).
  (* [comment removed for export] *)
  assert (HHp : ri_inv HI (PM.vs_own x ++ LBr) FF' LK1 cr1 Aw1 M1 (vml_of model1)).
  { apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK1 cr1 Aw1 M1 _ HH1).
    - intros b. split; [apply Permutation_in| apply Permutation_in; apply Permutation_sym]; unfold LBr, x; apply perm_cs; exact Hwb.
    - apply (ln_nodup_perm (PNM.bparser_own s1 ++ LBX)); [| exact ND1]. unfold LBr, x; apply perm_cs; exact Hwb.
    - intros f. tauto.
    - rewrite map_app in NDF1. apply stdpp.list_relations.list.NoDup_app in NDF1. exact (proj1 NDF1). }
  (* [comment removed for export] *)
  assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 o x /\ PM.tb_ok x g).
  { pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NB1 & TB1 & _). pose proof GR1 as (GNB & GTB & GBB).
    unfold o, x, g, PNRA.bcs_off, PNRA.bcs_str. destruct Hwb as [->| ->]; cbn [Z.eqb]; [exact (conj NB1 GNB)| exact (conj TB1 GTB)]. }
  destruct VS1 as (VS1 & TG1).
  pose proof (PMA.ly_cost L C LY) as (LCK & LCL & LCO).
  assert (CRX : PMSP.credit_le (PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) x g)) cr1).
  { pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _). pose proof GR1 as (GNB & GTB & GBB).
    assert (P1 : forall y gy oy, PM.vstr_at RSEGS PMSPA.accA M1 oy y -> PM.tb_ok y gy -> 0 <= fst (PM.pot_text (PMSPA.HV L ar) y gy) /\ 0 <= snd (PM.pot_text (PMSPA.HV L ar) y gy)).
    { intros y gy oy (_ & _ & VSy) (Hg & _ & _). unfold PM.pot_text. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
      assert (Cy : PM.vs_cap y <= 2 ^ 27) by (destruct y as [n|cc n p]; cbn [PM.vs_cap]; [clear; lia| destruct VSy as (_ & _ & _ & _ & Hcc & _); clear - Hcc; lia]). clear - Hg Cy. lia. }
    assert (P2 : 0 <= fst (PGV8.pot_v8 (PMSPA.HV L ar) (PNM.b_bb s1) (PNM.b_bg s1)) /\ 0 <= snd (PGV8.pot_v8 (PMSPA.HV L ar) (PNM.b_bb s1) (PNM.b_bg s1))).
    { destruct BB1 as (_ & _ & VSb). pose proof (PGV8.v8_ok_cap _ _ GBB) as (Hg & _). unfold PGV8.pot_v8. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
      assert (Cy : PGV8.v8_cap (PNM.b_bb s1) <= 2 ^ 27) by (destruct (PNM.b_bb s1) as [|b n cc]; cbn [PGV8.v8_cap]; [clear; lia| destruct VSb as (_ & _ & _ & _ & Hcc & _); clear - Hcc; lia]). clear - Hg Cy. lia. }
    assert (P3 : 0 <= fst (PNRA.pot_bstack L ar (PNM.b_sk s1)) /\ 0 <= snd (PNRA.pot_bstack L ar (PNM.b_sk s1))).
    { destruct SV1 as (_ & _ & _ & Hk & _). unfold PNRA.pot_bstack, PNM.BSZ. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
      assert (P : 2 ^ (PNM.b_sk s1 + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - Hk; lia). clear - Hk P. lia. }
    pose proof (P1 _ _ _ NB1 GNB) as P4. pose proof (P1 _ _ _ TB1 GTB) as P5.
    revert CRED CK1 P2 P3 P4 P5. unfold PMSP.credit_le, PMSP.credit_keep, PMSPA.scA, PNRA.pot_bparser, PM.credit_add, x, g, PNRA.bcs_str. cbn [fst snd]. rewrite LCL.
    destruct Hwb as [->| ->]; cbn [Z.eqb]; clear; intros; lia. }
  unfold PMA.str_resize_spec, PMSPA.str_resize_spec in PB.
  apply (PB fx1 R1 M1 model1 K LBr FF' LK1 Aw1 cr1 o nn (sp - 224) ra g x HHp AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 28672 224 14336 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 224) with (sp + (-14) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 28672) 3584); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 224 - 14336) with (sp + (-910) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 28672 WR M M1 EK1 WAPPR (sp - 28672) 3584); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 8 1 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 224) F 3 (sp - 224 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. }
  { apply PMAUAR.aobjA_push. exact AOo. }
  { unfold o, op. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm. unfold PNRA.bcs_off, PNM.OFF_NB, PNM.OFF_TB.
    destruct Hwb as [->| ->]; cbn [Z.eqb]; [replace (2048 * (fb / 2048) + 464 + 344) with ((256 * (fb / 2048) + 101) * 8) by (clear; lia)| replace (2048 * (fb / 2048) + 464 + 368) with ((256 * (fb / 2048) + 104) * 8) by (clear; lia)]; apply Z_mod_mult. }
  { exact VS1. } { exact TG1. } { exact Hn1. } { exact Hn2. } { exact CRX. }
  intros fx6 R6 M6 model6 LK6 Aw6 x' g' cr6 RP6 VS6 SZ6 TG6 _ HP6 CK6 MRT6 INCL6 INCA6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (s2 := set_cs wb s1 x' g').
  assert (HH6' : ri_inv HI (PNM.bparser_own s2 ++ LBX) FF' LK6 cr6 Aw6 M6 (vml_of model6)).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND6 & NDF6 & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK6 cr6 Aw6 M6 _ HH6).
    - intros b. split; [apply Permutation_in| apply Permutation_in; apply Permutation_sym]; unfold LBr, s2; apply perm_cs'; exact Hwb.
    - apply (ln_nodup_perm (PM.vs_own x' ++ LBr)); [| exact ND6]. unfold LBr, s2; apply perm_cs'; exact Hwb.
    - intros f. tauto.
    - rewrite map_app in NDF6. apply stdpp.list_relations.list.NoDup_app in NDF6. exact (proj1 NDF6). }
  set (Wc := [(o, 24)] : list L5.range) in HP6.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> o <= a < o + 24).
  { intros rr a [<-|[]] Hr. exact Hr. }
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 224 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64)).
  { intros rr a Hin Hr. pose proof (WcR rr a Hin Hr) as X. unfold o, op in X. unfold SB.
    split; [clear - X GSLO F2 FSCEIL HOFF; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2 HOFF; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 28672 a -> L5.outside WR a -> L5.outside Wc a).
  { intros a Hc' Ho rr Hin Hr. pose proof (WcR rr a Hin Hr) as X. unfold o, PNRA.bcs_off, PNM.OFF_NB, PNM.OFF_TB in X. destruct Hwb as [->| ->]; cbn [Z.eqb] in X.
    - apply (Ho (PNRA.o_nb PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 5 right; left; reflexivity| unfold L5.in_rng, PNRA.o_nb, PNRA.o_p, PMSP.o_p, PNM.OFF_NB; cbn [fst snd pa_off_p PMA.AD PnLayoutA.ADDR_A]; unfold op in X; clear - X; lia].
    - apply (Ho (PNRA.o_tb PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng, PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB; cbn [fst snd pa_off_p PMA.AD PnLayoutA.ADDR_A]; unfold op in X; clear - X; lia]. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 224) (own sp R) F 3 WR (PNM.bparser_own s2) M6 model6 LK6 cr6 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 224) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (own_rest wb s1) (PNM.bparser_own s2) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr6 Aw6 14336 Wc BI HP6 HH6' AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (proj1 HP6 : ek L ar LBr FF' (sp - 224) 14336 Wc M1 M6) as EK6.
  assert (WAPP6 : PMKA.wapp Wc).
  { intros rr [<-|[]]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI, o, op. destruct FA1 as [Y|Y]; clear - Y F1 F2 HOFF; lia. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHp) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHp) as BRBp.
  assert (BRB1 : forall b, In b LBr -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRBp; apply in_or_app; right; exact Hb).
  assert (OUTB : forall q m, In (q, m) LBr -> forall i, q <= i < q + m -> L5.outside Wc i).
  { intros q m Hq i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m o 24 HHp (in_or_app _ _ _ (or_intror Hq)) (PMAUAR.aobjA_push FF o 24 _ AOo)) as [Z0|Z0]; clear - Hi Y Z0; lia. }
  assert (AGB : forall q m, In (q, m) (own_rest wb s1) -> 0 <= q /\ q + m <= 2 ^ 64 /\ PMFA.agA M1 M6 q m).
  { intros q m Hq. assert (HqL : In (q, m) LBr) by (apply in_or_app; left; exact Hq). destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
    split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar LBr FF' (sp - 224) 14336 Wc M1 M6 EK6 WAPP6 BRB1 q m HqL). apply OUTB. exact HqL. }
  assert (PA6 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M6 op ois s2).
  { apply (bparser_set_csS M1 M6 (pa_vp_parser PMA.AD) op ois s1 wb x' g' Hwb ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | exact AGB| exact VS6| exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i o) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar LBr FF' (sp - 224) 14336 Wc M1 M6 EK6 WAPP6 FRB1 op (PNRA.bcs_off wb) _ _) i _); [| | unfold o in X; clear - Hi X; lia].
        * apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op (PNRA.bcs_off wb) FOK); unfold op; clear - HOFF; lia.
        * intros i' Hi' rr Hin Hr. pose proof (WcR rr i' Hin Hr) as Y. unfold o in Y. clear - Hi' Y; lia.
      + refine (proj1 (PMKA.agA_obj L ar LBr FF' (sp - 224) 14336 Wc M1 M6 EK6 WAPP6 FRB1 (o + 24) (416 - PNRA.bcs_off wb - 24) _ _) i _); [| | unfold o in X, Hn |- *; clear - Hi X Hn; lia].
        * apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (o + 24) (416 - PNRA.bcs_off wb - 24) FOK); unfold o, op; clear - HOFF; lia.
        * intros i' Hi' rr Hin Hr. pose proof (WcR rr i' Hin Hr) as Y. clear - Hi' Y; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar LBr FF' (sp - 224) 14336 Wc M1 M6 EK6 WAPP6 FRB1 op 416 _ i Hi).
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia. }
  assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 224) 14336 Wc M1 M6 EK6 WAPP6 FRB1 BRB1 ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LBr. apply incl_appr. exact INCS.
    - intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. unfold o, op in Y. unfold ois in Hi. clear - Hi Y HOFF; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB. unfold LBr. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
  { apply (PMASK.base_keep L ar C LY _ FF' (sp - 224) 14336 Wc M1 M6 EK6); [| exact BASE1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold o, op in Y. clear - Ha Y FBI HOFF; lia. }
  assert (ERR6 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M6 ax1).
  { apply (berr_keep _ FF' (sp - 224) 14336 Wc M1 M6 ax1 EK6); [| exact ERR1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold o, op in Y. clear - Ha Y FBI HOFF; lia. }
  assert (GR6 : PNM.bgrow_ok s2).
  { pose proof GR1 as (GNB & GTB & GBB). unfold s2, set_cs, PNM.bgrow_ok. unfold g, x, PNRA.bcs_str in TG6.
    destruct Hwb as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in TG6 |- *;
      [exact (conj TG6 (conj GTB GBB))| exact (conj GNB (conj TG6 GBB))]. }
  apply (KR fx6 R6 M6 model6 LK6 Aw6 x' g' cr6 RP6 SZ6).
  - split; [exact BI6|].
    split. { apply (pre_after_call LBr FF' (sp - 224) 14336 Wc M1 M6 fb s1 s2 str sm1 sm1 ax1 ax1 FRB1 EK6 WAPP6 FOK');
               [| exact RP1| exact PA6| exact IA6| exact GR6| exact BASE6| exact ERR6].
             intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. unfold o, op in Y. clear - Hi Y HOFF; lia. }
    split; [unfold s2, set_cs; destruct Hwb as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_src]; exact STEP1|].
    split; [exact AXL1|].
    split. { revert CK1 CK6. unfold PMSP.credit_keep, PMSPA.credit_keep, PMSPA.scA, PNRA.pot_bparser, PM.credit_add, s2, set_cs, x, g, PNRA.bcs_str. cbn [fst snd].
             destruct Hwb as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]; clear; intros; lia. }
    split; [| exact I].
    apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK6. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 224) 14336 F 3 (sp - 224 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 224) 14336 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 224) 14336 Wc M1 M6 EK6 WAPP6 FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. unfold o, op in Y. clear - Hi Y HOFF; lia.
Qed.

End WithHeap.
End PNARVKT.
