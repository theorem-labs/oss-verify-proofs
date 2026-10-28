(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b PnBrKitA_b PnARvK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.

Module PNARVKX.
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

Lemma in_elem_of (x : Z) (l : list Z) : In x l -> base.elem_of x l.
Proof. induction l as [|y l IH]; [intros []|]. intros [E|H]; [subst y; left| right; apply IH; exact H]. Qed.

(* [comment removed for export] *)
Lemma rv_call_pbw K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra c wb : Z) :
  PNRAa.str_push_back_spec L ar HI -> (wb = 0 \/ wb = 1) ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + PNRA.bcs_off wb) -> getr R1 (reg 11) = Z_to_bv 64 c -> 0 <= c < 256 ->
  PM.vs_size (PNRA.bcs_str wb s1) < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 x' g' cr3,
      regs_preserved R1 R2 -> PM.vs_size x' = PM.vs_size (PNRA.bcs_str wb s1) + 1 ->
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 (set_cs wb s1 x' g') sm1 ax1 cr3 ->
      (forall a, sp - 160 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (PNL.pn_str_push_back PMA.AN) M1 model1) K.
Proof.
  intros PB Hwb CTX G LM X1 RAok X2 X3 X4 X10 X11 Hc SZ KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *. change (28672 / 8) with 3584 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 160 + 32) :: FF) in *.
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
  unfold PNRAa.str_push_back_spec, PNRA.str_push_back_spec in PB.
  apply (PB fx1 R1 M1 model1 K LBr FF' LK1 Aw1 cr1 o c (sp - 160) ra g x HHp AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 28672 160 14336 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 28672) 3584); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 14336) with (sp + (-906) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 28672 WR M M1 EK1 WAPPR (sp - 28672) 3584); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 8 1 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 3 (sp - 160 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hc. }
  { apply PMAUAR.aobjA_push. exact AOo. }
  { unfold o, op. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm. unfold PNRA.bcs_off, PNM.OFF_NB, PNM.OFF_TB.
    destruct Hwb as [->| ->]; cbn [Z.eqb]; [replace (2048 * (fb / 2048) + 464 + 344) with ((256 * (fb / 2048) + 101) * 8) by (clear; lia)| replace (2048 * (fb / 2048) + 464 + 368) with ((256 * (fb / 2048) + 104) * 8) by (clear; lia)]; apply Z_mod_mult. }
  { exact VS1. } { exact TG1. } { exact SZ. } { exact CRX. }
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
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64)).
  { intros rr a Hin Hr. pose proof (WcR rr a Hin Hr) as X. unfold o, op in X. unfold SB.
    split; [clear - X GSLO F2 FSCEIL HOFF; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2 HOFF; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 28672 a -> L5.outside WR a -> L5.outside Wc a).
  { intros a Hc' Ho rr Hin Hr. pose proof (WcR rr a Hin Hr) as X. unfold o, PNRA.bcs_off, PNM.OFF_NB, PNM.OFF_TB in X. destruct Hwb as [->| ->]; cbn [Z.eqb] in X.
    - apply (Ho (PNRA.o_nb PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 5 right; left; reflexivity| unfold L5.in_rng, PNRA.o_nb, PNRA.o_p, PMSP.o_p, PNM.OFF_NB; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; unfold op in X; clear - X; lia].
    - apply (Ho (PNRA.o_tb PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng, PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; unfold op in X; clear - X; lia]. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 160) (own sp R) F 3 WR (PNM.bparser_own s2) M6 model6 LK6 cr6 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (own_rest wb s1) (PNM.bparser_own s2) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr6 Aw6 14336 Wc BI HP6 HH6' AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (proj1 HP6 : ek L ar LBr FF' (sp - 160) 14336 Wc M1 M6) as EK6.
  assert (WAPP6 : PMKA.wapp Wc).
  { intros rr [<-|[]]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI, o, op. destruct FA1 as [Y|Y]; clear - Y F1 F2 HOFF; lia. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHp) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHp) as BRBp.
  assert (BRB1 : forall b, In b LBr -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRBp; apply in_or_app; right; exact Hb).
  assert (OUTB : forall q m, In (q, m) LBr -> forall i, q <= i < q + m -> L5.outside Wc i).
  { intros q m Hq i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m o 24 HHp (in_or_app _ _ _ (or_intror Hq)) (PMAUAR.aobjA_push FF o 24 _ AOo)) as [Z0|Z0]; clear - Hi Y Z0; lia. }
  assert (AGB : forall q m, In (q, m) (own_rest wb s1) -> 0 <= q /\ q + m <= 2 ^ 64 /\ PMFA.agA M1 M6 q m).
  { intros q m Hq. assert (HqL : In (q, m) LBr) by (apply in_or_app; left; exact Hq). destruct (BRB1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
    split; [exact B0|]. split; [clear - B1; lia|]. apply (PMKA.agA_blk L ar LBr FF' (sp - 160) 14336 Wc M1 M6 EK6 WAPP6 BRB1 q m HqL). apply OUTB. exact HqL. }
  assert (PA6 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M6 op ois s2).
  { apply (bparser_set_csS M1 M6 (pa_vp_parser PMA.AD) op ois s1 wb x' g' Hwb ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | exact AGB| exact VS6| exact PA1].
    - intros i Hi Hn. destruct (Z_lt_le_dec i o) as [X|X].
      + refine (proj1 (PMKA.agA_obj L ar LBr FF' (sp - 160) 14336 Wc M1 M6 EK6 WAPP6 FRB1 op (PNRA.bcs_off wb) _ _) i _); [| | unfold o in X; clear - Hi X; lia].
        * apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op (PNRA.bcs_off wb) FOK); unfold op; clear - HOFF; lia.
        * intros i' Hi' rr Hin Hr. pose proof (WcR rr i' Hin Hr) as Y. unfold o in Y. clear - Hi' Y; lia.
      + refine (proj1 (PMKA.agA_obj L ar LBr FF' (sp - 160) 14336 Wc M1 M6 EK6 WAPP6 FRB1 (o + 24) (416 - PNRA.bcs_off wb - 24) _ _) i _); [| | unfold o in X, Hn |- *; clear - Hi X Hn; lia].
        * apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (o + 24) (416 - PNRA.bcs_off wb - 24) FOK); unfold o, op; clear - HOFF; lia.
        * intros i' Hi' rr Hin Hr. pose proof (WcR rr i' Hin Hr) as Y. clear - Hi' Y; lia.
    - intros i Hi. refine (PMKA.agsh_obj L ar LBr FF' (sp - 160) 14336 Wc M1 M6 EK6 WAPP6 FRB1 op 416 _ i Hi).
      apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia. }
  assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 160) 14336 Wc M1 M6 EK6 WAPP6 FRB1 BRB1 ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LBr. apply incl_appr. exact INCS.
    - intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. unfold o, op in Y. unfold ois in Hi. clear - Hi Y HOFF; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB. unfold LBr. apply in_or_app; right. apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
  { apply (PMASK.base_keep L ar C LY _ FF' (sp - 160) 14336 Wc M1 M6 EK6); [| exact BASE1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold o, op in Y. clear - Ha Y FBI HOFF; lia. }
  assert (ERR6 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M6 ax1).
  { apply (berr_keep _ FF' (sp - 160) 14336 Wc M1 M6 ax1 EK6); [| exact ERR1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold o, op in Y. clear - Ha Y FBI HOFF; lia. }
  assert (GR6 : PNM.bgrow_ok s2).
  { pose proof GR1 as (GNB & GTB & GBB). unfold s2, set_cs, PNM.bgrow_ok. unfold g, x, PNRA.bcs_str in TG6.
    destruct Hwb as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in TG6 |- *;
      [exact (conj TG6 (conj GTB GBB))| exact (conj GNB (conj TG6 GBB))]. }
  apply (KR fx6 R6 M6 model6 LK6 Aw6 x' g' cr6 RP6 SZ6).
  - split; [exact BI6|].
    split. { apply (pre_after_call LBr FF' (sp - 160) 14336 Wc M1 M6 fb s1 s2 str sm1 sm1 ax1 ax1 FRB1 EK6 WAPP6 FOK');
               [| exact RP1| exact PA6| exact IA6| exact GR6| exact BASE6| exact ERR6].
             intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. unfold o, op in Y. clear - Hi Y HOFF; lia. }
    split; [unfold s2, set_cs; destruct Hwb as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_src]; exact STEP1|].
    split; [exact AXL1|].
    split. { revert CK1 CK6. unfold PMSP.credit_keep, PMSPA.scA, PNRA.pot_bparser, PM.credit_add, s2, set_cs, x, g, PNRA.bcs_str. cbn [fst snd].
             destruct Hwb as [->| ->]; cbn [Z.eqb PNBO.set_nb PNBO.set_tb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]; clear; intros; lia. }
    split; [| exact I].
    apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK6. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 14336 F 3 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 14336 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) 14336 Wc M1 M6 EK6 WAPP6 FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. unfold o, op in Y. clear - Hi Y HOFF; lia.
Qed.


(* [comment removed for export] *)
Lemma rv_piece_tb K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) (x' : PM.vstr) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> (fb + 832 <= a < fb + 856) \/ (exists B m, In (B, m) (PM.vs_own (PNM.b_tb s1)) /\ B <= a < B + m) \/ (sp - 160 <= a < sp - 104)) ->
  PM.vs_own x' = PM.vs_own (PNM.b_tb s1) -> PM.tb_ok x' (PNM.b_tg s1) ->
  PM.pot_text (PMSPA.HV L ar) x' (PNM.b_tg s1) = PM.pot_text (PMSPA.HV L ar) (PNM.b_tb s1) (PNM.b_tg s1) ->
  (forall (M3 : mem), (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
                      PM.vstr_at RSEGS PMSPA.accA M3 (fb + 464 + 368) x') ->
  (forall (M3 : mem) model3,
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 (set_cs 1 s1 x' (PNM.b_tg s1)) sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WN EOWN TBOK POTE VS KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044352 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 28672 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (s3 := set_cs 1 s1 x' (PNM.b_tg s1)) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (_ & _ & GF3 & _).
  assert (AOP : PMSPA.aobjA FF' op 416) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia).
  assert (OWNB : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s1)) -> In (B, m) (PNM.bparser_own s1 ++ LBX)).
  { intros B m Hin. apply in_or_app; left. exact (PNBOA.PNM_own_tb s1 B m Hin). }
  assert (WB1 : forall B m a, In (B, m) (PM.vs_own (PNM.b_tb s1)) -> B <= a < B + m ->
                  (a + 1 <= op \/ op + 416 <= a) /\ ~ (65536 <= a < 6905856) /\ (a + 1 <= 2147446784 \/ 17594333495296 <= a) /\ 0 <= a < 2 ^ 47 /\ ~ (sp - 160 <= a < sp) /\ ~ (F <= a < F + 512)).
  { intros B m a Hin Ha. pose proof (OWNB B m Hin) as HinL.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m op 416 HH1 HinL AOP) as [Z0|Z0].
    all: pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HinL) as (BC & (BA0 & BAPP & BA2)); unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
    all: pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ B m HH1 HinL) as BIMG.
    all: pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBx & _); destruct (WBx _ HinL) as (_ & _ & _ & _ & _ & BFA & _).
    all: pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1 _ HinL) as (Q0 & Q1); cbn [fst snd] in Q0, Q1.
    all: pose proof (BFA (fb, 5, rs) (in_or_app FF' LK1 (fb, 5, rs) (or_introl (or_intror Hfb)))) as Zf; cbn [ff_addr ff_class fst snd] in Zf; change (ff_bytes 5) with 2048 in Zf.
    all: pose proof (BFA (F, 3, sp - 160 + 32) (in_or_app FF' LK1 _ (or_introl (or_introl eq_refl)))) as ZF; cbn [ff_addr ff_class fst snd] in ZF; change (ff_bytes 3) with 512 in ZF.
    all: clear - Ha Z0 BC BA0 BAPP BA2 BIMG Q0 Q1 Zf ZF GSLO GSHI GSPT SLO SHI SPT; lia. }
  assert (WAPP : forall a, W a -> ~ (65536 <= a < 6905856) /\ (a + 1 <= 2147446784 \/ 17594333495296 <= a) /\ 0 <= a < 2 ^ 47 /\ ~ (sp - 104 <= a < sp) /\ ~ (F <= a < F + 512)).
  { intros a Wa. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]].
    3:{ split; [clear - X GSLO FSCEIL FSAPP; lia|]. split; [right; clear - X SL160 SHI SPT; lia|]. split; [clear - X GSLO GSHI GSPT; lia|]. split; [clear - X; lia|]. clear - X GFCEIL GSLO; lia. }
    - split; [clear - X FBI; lia|]. split; [destruct FA1 as [Y|Y]; clear - X Y F1 F2; lia|]. split; [clear - X F2 FSCEIL GSLO GSHI GSPT FBI; lia|].
      split; [clear - X GSLO F2 FSCEIL; lia|]. intros Y. apply (GNCF a); [left; exact Y|]. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
      change (ff_bytes 5) with 2048. split; [clear - X; lia| intros Y0; clear - X Y0; lia].
    - destruct (WB1 B m a Hin X) as (_ & Y1 & Y2 & Y3 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [clear - Y5; lia| exact Y6]. }
  assert (NSH : forall i, 0 <= i < 2 ^ 47 -> ~ W (i / 8 + 2147450880)).
  { intros i Hi Wa. destruct (WAPP _ Wa) as (_ & Y & _). pose proof (Z.div_pos i 8 ltac:(clear - Hi; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi; lia)) as D1. clear - Y D0 D1. lia. }
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. destruct (WAPP a Wa) as (Y1 & _). split; [| exact Y1]. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]].
    3:{ unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]. }
    - unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - X; lia| intros Y; clear - X Y; lia].
    - unfold aclientw, aclient_g. left. exists (B, m). split; [exact (OWNB B m Hin)| cbn [fst snd]; exact X]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (BRBx : forall b, In b LBX -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB1; apply in_or_app; right; exact Hb).
  set (Wl := [(fb + 832, 24)] : list L5.range).
  assert (NCWe : forall a, W a -> aclient L ar LBX FF' (sp - 104) 120 a -> fb + 832 <= a < fb + 856).
  { intros a Wa Hc. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]]; [exact X| |].
    - exfalso. exact (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ B m a (sp - 104) 120 HH1 (PNBOA.PNM_own_tb s1 B m Hin) X Hc).
    - exfalso. pose proof (L5SAR.aclient_appb L ar LBX (PNM.bparser_own s1) FF' (sp - 104) 120 a Hc) as Hc'.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ (sp - 104) 120 a HH1 GSPT Hc') as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia]. }
  assert (NCWb : forall a, W a -> aclient L ar LBX FF sp 28672 a -> fb + 832 <= a < fb + 856).
  { intros a Wa Hc. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]]; [exact X| |].
    - exfalso. exact (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ B m a sp 28672 HH1 (PNBOA.PNM_own_tb s1 B m Hin) X (L5SAR.aclient_cons L ar _ _ _ _ _ _ Hc)).
    - exfalso. apply (GNCS a); [clear - X; lia| exact Hc]. }
  assert (EK13 : L5SAR.ek L ar LBX FF' (sp - 104) 120 Wl M1 M3).
  { intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. pose proof (NCWe a Wa Hc) as X. apply (Ho (fb + 832, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (WAPPl : PMKA.wapp Wl).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 104) 120 Wl M1 M3 EK13 WAPPl FRB1 (fb + 1024) v0 c0); [| | exact E0].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia. }
  assert (EO3 : PNM.bparser_own s3 = PNM.bparser_own s1).
  { unfold s3, set_cs, PNBO.set_tb, PNM.bparser_own, PNM.brest_own. cbn [Z.eqb PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. rewrite EOWN. reflexivity. }
  assert (VS3 : PM.vstr_at RSEGS PMSPA.accA M3 (fb + 464 + 368) x') by (apply (VS M3 FR3 MG3); exact VIS3).
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { rewrite EO3. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold PMAUK.binv.
    split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact MRT3]|]. split; [exact B4|]. split; [exact B5|].
    split; [eapply L5SAR.astk_grows; [exact B6| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. pose proof (NCWb a Wa Hc) as X.
             apply (Ho (PNRA.o_tb PMA.AD fb, 24)); [unfold PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng, PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia]. }
    split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG3]|].
    split. { apply (own_agree sp R M1 M3 ltac:(clear - GSPC; lia) ltac:(clear - GSPC; lia) B9). intros a Ha. unfold ocell in Ha. apply FR3; [clear - Ha GSPC; lia|]. intros Wa. destruct (WAPP a Wa) as (_ & _ & _ & Y & _). apply Y. clear - Ha; lia. }
    eapply L5.defined_grows; [exact MG3| exact B10]. }
  split.
  { apply (pre_after_call LBX FF' (sp - 104) 120 Wl M1 M3 fb s1 s3 str sm1 sm1 ax1 ax1 FRB1 EK13 WAPPl FOK'); [| exact RP1| | | | |].
    - intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia.
    - apply (PNBKA.bparser_set_csS M1 M3 (pa_vp_parser PMA.AD) op ois s1 1 x' (PNM.b_tg s1) (or_intror eq_refl) ltac:(unfold op; clear - FBI; lia) ltac:(unfold op; clear - F2 FSCEIL GSLO GSHI GSPT FBI; lia)); [| | | exact VS3| exact PA1].
      + intros i Hi Hn. unfold PNBOA.snt. apply FR3; [unfold op in Hi; clear - Hi FBI F2 FSCEIL GSLO GSHI GSPT FBI; lia|]. intros Wa. destruct (WN i Wa) as [X|[(B & m & Hin & X)|X]]; [| | unfold op in Hi; clear - X Hi F2 FSCEIL GSLO; lia].
        * apply Hn. unfold PNRA.bcs_off, PNM.OFF_TB. cbn [Z.eqb]. unfold op. clear - X; lia.
        * destruct (WB1 B m i Hin X) as (Y & _). clear - Y Hi; lia.
      + intros i Hi. unfold PNBOA.sns, S, SB. apply FR3; [unfold op in Hi; pose proof (Z.div_pos i 8 ltac:(clear - Hi FBI; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi F2 FSCEIL GSLO GSHI GSPT FBI; lia)); lia|].
        apply NSH. unfold op in Hi. clear - Hi FBI F2 FSCEIL GSLO GSHI GSPT FBI; lia.
      + intros B m HB. assert (HBL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (incl_rest 1 s1 _ HB)).
        destruct (BRB1 _ HBL) as (B0 & B1'). cbn [fst snd] in B0, B1'. split; [exact B0|]. split; [clear - B1'; lia|].
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBx & _). destruct (WBx _ HBL) as ((_ & _ & _ & Bpos & _) & _). cbn [fst snd] in Bpos.
        split.
        * intros x Hx. apply FR3; [clear - Hx B0 B1'; lia|]. intros Wa. destruct (WN x Wa) as [X|[(B2 & m2 & Hin2 & X)|X]]; [| | pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HBL) as (BCx & _); clear - X Hx BCx GSLO; lia].
          -- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m op 416 HH1 HBL AOP) as [Z0|Z0]; unfold op in Z0; clear - Hx X Z0; lia.
          -- assert (NE : B <> B2).
             { pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1) as ND. intros E. subst B2.
               pose proof (perm_cs 1 s1 LBX (or_intror eq_refl)) as PE. pose proof (ln_nodup_perm _ _ PE ND) as ND2. unfold PNRA.bcs_str in ND2. cbn [Z.eqb] in ND2.
               rewrite map_app in ND2. pose proof (proj1 (stdpp.list_relations.list.NoDup_app _ _) ND2) as (_ & ND3 & _). apply (ND3 B).
               - apply in_elem_of. apply (in_map fst _ (B, m2)). exact Hin2.
               - apply in_elem_of. rewrite map_app. apply in_or_app; left. apply (in_map fst _ (B, m)). exact HB. }
             destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ B m B2 m2 HH1 HBL (OWNB B2 m2 Hin2) NE) as [Z0|Z0]; clear - Hx X Z0; lia.
        * intros x Hx. unfold S, SB. apply FR3; [pose proof (Z.div_pos x 8 ltac:(clear - Hx B0; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx B1'; lia)); lia|].
          apply NSH. clear - Hx B0 B1'; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 104) 120 Wl M1 M3 EK13 WAPPl FRB1 BRBx (fb + 96) str sm1); [| exact INCS| | | exact IA1].
      + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
      + intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia.
      + intros c0 n0 p0 E0 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
        assert (HqL : In (p0, c0) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E0; left; reflexivity).
        destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p0 c0 op 416 HH1 HqL AOP) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia.
    - unfold s3, set_cs, PNM.bgrow_ok, PNBO.set_tb. cbn [Z.eqb PNM.b_nb PNM.b_ng PNM.b_tb PNM.b_tg PNM.b_bb PNM.b_bg]. destruct GR1 as (G1 & _ & G3). split; [exact G1|]. split; [exact TBOK| exact G3].
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 104) 120 Wl M1 M3 EK13); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia.
    - apply (berr_keep _ FF' (sp - 104) 120 Wl M1 M3 ax1 EK13); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  split; [unfold s3, set_cs, PNBO.set_tb; cbn [Z.eqb PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
  split. { revert CK1. unfold s3, set_cs, PNBO.set_tb, PNRA.pot_bparser. cbn [Z.eqb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. rewrite POTE. intros X; exact X. }
  split; [| exact I].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. destruct (WAPP j Wj) as (_ & Y & _). pose proof (Z.div_pos F 8 ltac:(clear - GFR; lia) ltac:(clear; lia)) as D0. pose proof (Z.div_lt_upper_bound F 8 17592186044416 ltac:(clear; lia) ltac:(clear - GFR; lia)) as D1. clear - Hj Y D0 D1. lia.
Qed.

Lemma rv_piece_tbs K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) (x' : PM.vstr) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> (fb + 832 <= a < fb + 856) \/ (exists B m, In (B, m) (PM.vs_own (PNM.b_tb s1)) /\ B <= a < B + m) \/ (sp - 160 <= a < sp - 104) \/ (sp - 28672 <= a < sp - 160)) ->
  PM.vs_own x' = PM.vs_own (PNM.b_tb s1) -> PM.tb_ok x' (PNM.b_tg s1) ->
  PM.pot_text (PMSPA.HV L ar) x' (PNM.b_tg s1) = PM.pot_text (PMSPA.HV L ar) (PNM.b_tb s1) (PNM.b_tg s1) ->
  (forall (M3 : mem), (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
                      PM.vstr_at RSEGS PMSPA.accA M3 (fb + 464 + 368) x') ->
  (forall (M3 : mem) model3,
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 (set_cs 1 s1 x' (PNM.b_tg s1)) sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WN EOWN TBOK POTE VS KR.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044352 ltac:(lia) ltac:(lia)); lia).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 28672 160 HH1 ASTK1 ltac:(lia)) as (SL160 & SH160 & SWR).
  set (H1 := ahid Aw1 model1) in *.
  set (op := fb + 464) in *. set (ois := fb + 96) in *.
  set (s3 := set_cs 1 s1 x' (PNM.b_tg s1)) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  pose proof GFR as (_ & _ & GF3 & _).
  assert (AOP : PMSPA.aobjA FF' op 416) by (apply PMAUAR.aobjA_push; apply (PNAPAR.aobj_fbB FF fb op 416 FOK); unfold op; clear; lia).
  assert (OWNB : forall B m, In (B, m) (PM.vs_own (PNM.b_tb s1)) -> In (B, m) (PNM.bparser_own s1 ++ LBX)).
  { intros B m Hin. apply in_or_app; left. exact (PNBOA.PNM_own_tb s1 B m Hin). }
  assert (WB1 : forall B m a, In (B, m) (PM.vs_own (PNM.b_tb s1)) -> B <= a < B + m ->
                  (a + 1 <= op \/ op + 416 <= a) /\ ~ (65536 <= a < 6905856) /\ (a + 1 <= 2147446784 \/ 17594333495296 <= a) /\ 0 <= a < 2 ^ 47 /\ ~ (sp - 160 <= a < sp) /\ ~ (F <= a < F + 512)).
  { intros B m a Hin Ha. pose proof (OWNB B m Hin) as HinL.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m op 416 HH1 HinL AOP) as [Z0|Z0].
    all: pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HinL) as (BC & (BA0 & BAPP & BA2)); unfold BIGSHADOW_LO, BIGSHADOW_HI in BAPP.
    all: pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ B m HH1 HinL) as BIMG.
    all: pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBx & _); destruct (WBx _ HinL) as (_ & _ & _ & _ & _ & BFA & _).
    all: pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1 _ HinL) as (Q0 & Q1); cbn [fst snd] in Q0, Q1.
    all: pose proof (BFA (fb, 5, rs) (in_or_app FF' LK1 (fb, 5, rs) (or_introl (or_intror Hfb)))) as Zf; cbn [ff_addr ff_class fst snd] in Zf; change (ff_bytes 5) with 2048 in Zf.
    all: pose proof (BFA (F, 3, sp - 160 + 32) (in_or_app FF' LK1 _ (or_introl (or_introl eq_refl)))) as ZF; cbn [ff_addr ff_class fst snd] in ZF; change (ff_bytes 3) with 512 in ZF.
    all: clear - Ha Z0 BC BA0 BAPP BA2 BIMG Q0 Q1 Zf ZF GSLO GSHI GSPT SLO SHI SPT; lia. }
  assert (WAPP : forall a, W a -> ~ (65536 <= a < 6905856) /\ (a + 1 <= 2147446784 \/ 17594333495296 <= a) /\ 0 <= a < 2 ^ 47 /\ ~ (sp - 104 <= a < sp) /\ ~ (F <= a < F + 512)).
  { intros a Wa. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]].
    3:{ split; [clear - X GSLO FSCEIL FSAPP; lia|]. split; [right; clear - X SL160 GSLO SHI SPT; lia|]. split; [clear - X GSLO GSHI GSPT; lia|]. split; [clear - X; lia|]. clear - X GFCEIL GSLO; lia. }
    - split; [clear - X FBI; lia|]. split; [destruct FA1 as [Y|Y]; clear - X Y F1 F2; lia|]. split; [clear - X F2 FSCEIL GSLO GSHI GSPT FBI; lia|].
      split; [clear - X GSLO F2 FSCEIL; lia|]. intros Y. apply (GNCF a); [left; exact Y|]. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
      change (ff_bytes 5) with 2048. split; [clear - X; lia| intros Y0; clear - X Y0; lia].
    - destruct (WB1 B m a Hin X) as (_ & Y1 & Y2 & Y3 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [clear - Y5; lia| exact Y6]. }
  assert (NSH : forall i, 0 <= i < 2 ^ 47 -> ~ W (i / 8 + 2147450880)).
  { intros i Hi Wa. destruct (WAPP _ Wa) as (_ & Y & _). pose proof (Z.div_pos i 8 ltac:(clear - Hi; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi; lia)) as D1. clear - Y D0 D1. lia. }
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. destruct (WAPP a Wa) as (Y1 & _). split; [| exact Y1]. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]].
    3:{ unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]. }
    - unfold aclientw, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [right; exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. split; [clear - X; lia| intros Y; clear - X Y; lia].
    - unfold aclientw, aclient_g. left. exists (B, m). split; [exact (OWNB B m Hin)| cbn [fst snd]; exact X]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (BRBx : forall b, In b LBX -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; apply BRB1; apply in_or_app; right; exact Hb).
  set (Wl := [(fb + 832, 24)] : list L5.range).
  assert (NCWe : forall a, W a -> aclient L ar LBX FF' sp 28672 a -> fb + 832 <= a < fb + 856).
  { intros a Wa Hc. destruct (WN a Wa) as [X|[(B & m & Hin & X)|X]]; [exact X| |].
    - exfalso. exact (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ B m a sp 28672 HH1 (PNBOA.PNM_own_tb s1 B m Hin) X Hc).
    - exfalso. pose proof (L5SAR.aclient_appb L ar LBX (PNM.bparser_own s1) FF' sp 28672 a Hc) as Hc'.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ sp 28672 a HH1 GSPT Hc') as [Y|Y]; [clear - X Y; lia| clear - X Y GSLO; lia]. }
  assert (NCWb : forall a, W a -> aclient L ar LBX FF sp 28672 a -> fb + 832 <= a < fb + 856).
  { intros a Wa Hc. destruct (WN a Wa) as [X|[(B & m & Hin & X)|[X|X]]]; [exact X| | |].
    - exfalso. exact (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ B m a sp 28672 HH1 (PNBOA.PNM_own_tb s1 B m Hin) X (L5SAR.aclient_cons L ar _ _ _ _ _ _ Hc)).
    - exfalso. apply (GNCS a); [clear - X; lia| exact Hc].
    - exfalso. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ sp 28672 a HH1 GSPT (L5SAR.aclient_appb L ar LBX (PNM.bparser_own s1) FF' sp 28672 a (L5SAR.aclient_cons L ar _ _ _ _ _ _ Hc))) as [Y|Y]; clear - X Y GSLO; lia. }
  assert (EK13 : L5SAR.ek L ar LBX FF' sp 28672 Wl M1 M3).
  { intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. pose proof (NCWe a Wa Hc) as X. apply (Ho (fb + 832, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
  assert (WAPPl : PMKA.wapp Wl).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct FA1 as [Y|Y]; clear - Y F1 F2; lia. }
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' sp 28672 Wl M1 M3 EK13 WAPPl FRB1 (fb + 1024) v0 c0); [| | exact E0].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    - intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia. }
  assert (EO3 : PNM.bparser_own s3 = PNM.bparser_own s1).
  { unfold s3, set_cs, PNBO.set_tb, PNM.bparser_own, PNM.brest_own. cbn [Z.eqb PNM.b_src PNM.b_sb PNM.b_sk PNM.b_bb PNM.b_nb PNM.b_tb]. rewrite EOWN. reflexivity. }
  assert (VS3 : PM.vstr_at RSEGS PMSPA.accA M3 (fb + 464 + 368) x') by (apply (VS M3 FR3 MG3); exact VIS3).
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { rewrite EO3. destruct BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). unfold PMAUK.binv.
    split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact MRT3]|]. split; [exact B4|]. split; [exact B5|].
    split; [eapply L5SAR.astk_grows; [exact B6| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact B7|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa. pose proof (NCWb a Wa Hc) as X.
             apply (Ho (PNRA.o_tb PMA.AD fb, 24)); [unfold PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 6 right; left; reflexivity| unfold L5.in_rng, PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia]. }
    split; [eapply L5SAR.dk_trans; [exact B8| apply L5SAR.dk_grows; exact MG3]|].
    split. { apply (own_agree sp R M1 M3 ltac:(clear - GSPC; lia) ltac:(clear - GSPC; lia) B9). intros a Ha. unfold ocell in Ha. apply FR3; [clear - Ha GSPC; lia|]. intros Wa. destruct (WAPP a Wa) as (_ & _ & _ & Y & _). apply Y. clear - Ha; lia. }
    eapply L5.defined_grows; [exact MG3| exact B10]. }
  split.
  { apply (pre_after_call LBX FF' sp 28672 Wl M1 M3 fb s1 s3 str sm1 sm1 ax1 ax1 FRB1 EK13 WAPPl FOK'); [| exact RP1| | | | |].
    - intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia.
    - apply (PNBKA.bparser_set_csS M1 M3 (pa_vp_parser PMA.AD) op ois s1 1 x' (PNM.b_tg s1) (or_intror eq_refl) ltac:(unfold op; clear - FBI; lia) ltac:(unfold op; clear - F2 FSCEIL GSLO GSHI GSPT FBI; lia)); [| | | exact VS3| exact PA1].
      + intros i Hi Hn. unfold PNBOA.snt. apply FR3; [unfold op in Hi; clear - Hi FBI F2 FSCEIL GSLO GSHI GSPT FBI; lia|]. intros Wa. destruct (WN i Wa) as [X|[(B & m & Hin & X)|X]]; [| | unfold op in Hi; clear - X Hi F2 FSCEIL GSLO; lia].
        * apply Hn. unfold PNRA.bcs_off, PNM.OFF_TB. cbn [Z.eqb]. unfold op. clear - X; lia.
        * destruct (WB1 B m i Hin X) as (Y & _). clear - Y Hi; lia.
      + intros i Hi. unfold PNBOA.sns, S, SB. apply FR3; [unfold op in Hi; pose proof (Z.div_pos i 8 ltac:(clear - Hi FBI; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi F2 FSCEIL GSLO GSHI GSPT FBI; lia)); lia|].
        apply NSH. unfold op in Hi. clear - Hi FBI F2 FSCEIL GSLO GSHI GSPT FBI; lia.
      + intros B m HB. assert (HBL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (incl_rest 1 s1 _ HB)).
        destruct (BRB1 _ HBL) as (B0 & B1'). cbn [fst snd] in B0, B1'. split; [exact B0|]. split; [clear - B1'; lia|].
        pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WBx & _). destruct (WBx _ HBL) as ((_ & _ & _ & Bpos & _) & _). cbn [fst snd] in Bpos.
        split.
        * intros x Hx. apply FR3; [clear - Hx B0 B1'; lia|]. intros Wa. destruct (WN x Wa) as [X|[(B2 & m2 & Hin2 & X)|X]]; [| | pose proof (blk_ceil _ _ _ _ _ _ _ _ _ HH1 HBL) as (BCx & _); clear - X Hx BCx GSLO; lia].
          -- destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ B m op 416 HH1 HBL AOP) as [Z0|Z0]; unfold op in Z0; clear - Hx X Z0; lia.
          -- assert (NE : B <> B2).
             { pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1) as ND. intros E. subst B2.
               pose proof (perm_cs 1 s1 LBX (or_intror eq_refl)) as PE. pose proof (ln_nodup_perm _ _ PE ND) as ND2. unfold PNRA.bcs_str in ND2. cbn [Z.eqb] in ND2.
               rewrite map_app in ND2. pose proof (proj1 (stdpp.list_relations.list.NoDup_app _ _) ND2) as (_ & ND3 & _). apply (ND3 B).
               - apply in_elem_of. apply (in_map fst _ (B, m2)). exact Hin2.
               - apply in_elem_of. rewrite map_app. apply in_or_app; left. apply (in_map fst _ (B, m)). exact HB. }
             destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ B m B2 m2 HH1 HBL (OWNB B2 m2 Hin2) NE) as [Z0|Z0]; clear - Hx X Z0; lia.
        * intros x Hx. unfold S, SB. apply FR3; [pose proof (Z.div_pos x 8 ltac:(clear - Hx B0; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx B1'; lia)); lia|].
          apply NSH. clear - Hx B0 B1'; lia.
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' sp 28672 Wl M1 M3 EK13 WAPPl FRB1 BRBx (fb + 96) str sm1); [| exact INCS| | | exact IA1].
      + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
      + intros i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi Hr; lia.
      + intros c0 n0 p0 E0 i Hi rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
        assert (HqL : In (p0, c0) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E0; left; reflexivity).
        destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p0 c0 op 416 HH1 HqL AOP) as [Z0|Z0]; unfold op in Z0; clear - Hi Hr Z0; lia.
    - unfold s3, set_cs, PNM.bgrow_ok, PNBO.set_tb. cbn [Z.eqb PNM.b_nb PNM.b_ng PNM.b_tb PNM.b_tg PNM.b_bb PNM.b_bg]. destruct GR1 as (G1 & _ & G3). split; [exact G1|]. split; [exact TBOK| exact G3].
    - apply (PMASK.base_keep L ar C LY _ FF' sp 28672 Wl M1 M3 EK13); [| exact BASE1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia.
    - apply (berr_keep _ FF' sp 28672 Wl M1 M3 ax1 EK13); [| exact ERR1]. intros a Ha rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr FBI; lia. }
  split; [unfold s3, set_cs, PNBO.set_tb; cbn [Z.eqb PNM.b_src]; exact STEP1|]. split; [exact AXL1|].
  split. { revert CK1. unfold s3, set_cs, PNBO.set_tb, PNRA.pot_bparser. cbn [Z.eqb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. rewrite POTE. intros X; exact X. }
  split; [| exact I].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. destruct (WAPP j Wj) as (_ & Y & _). pose proof (Z.div_pos F 8 ltac:(clear - GFR; lia) ltac:(clear; lia)) as D0. pose proof (Z.div_lt_upper_bound F 8 17592186044416 ltac:(clear; lia) ltac:(clear - GFR; lia)) as D1. clear - Hj Y D0 D1. lia.
Qed.


(* [comment removed for export] *)
Lemma tbfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 464 + 368) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 464 + 369) / 8) + 2147450880) 1
  /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 464 + 376) / 8) + 2147450880) 1 /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) (((fb + 464 + 384) / 8) + 2147450880) 1
  /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 368) 2 /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 376) 8
  /\ PM.vstr_at RSEGS PMSPA.accA M1 (fb + 464 + 368) (PNM.b_tb s1)
  /\ match PNM.b_tb s1 with
     | PM.VShort n => 0 <= n <= 22 /\ L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 368) (2 * n) /\ 0 <= 2 * n <= 255 /\ Z.testbit (2 * n) 0 = false
     | PM.VLong c n p =>
         L5.u8_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 368) ((c + 1) mod 256) /\ 0 <= (c + 1) mod 256 <= 255 /\ Z.testbit ((c + 1) mod 256) 0 = true
         /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 384) p /\ L5.u64_at RSEGS (mrestrict (ahid Aw1 model1) M1) (fb + 464 + 376) n
         /\ 0 <= n < c /\ 26 <= c <= 2 ^ 27 /\ 4096 <= p <= 140737488355320 /\ p mod 8 = 0
         /\ (2147446784 + 17592186048512 <= p \/ p + 1 <= 2147446784) /\ L5KA.zeros_at (mrestrict (ahid Aw1 model1) M1) ((p / 8) + 2147450880) 1
         /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) p 1 /\ ((sp - 160) + 160 <= p \/ p + 1 <= (sp - 160)) /\ (p + 1 <= fb + 464 \/ (fb + 464) + 416 <= p)
         /\ (65536 + 6840320 <= p \/ p + 1 <= 65536) /\ In (p, c) (PNM.bparser_own s1)
     end.
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
  assert (FBI : 6905856 <= fb) by (clear - F1 FSAPP FSIMG; lia).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  set (FF' := (F, 3, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  pose proof RP1 as (PA1 & IA1 & VIS1 & VREF1 & OACC1 & BASE1 & ERR1 & GR1).
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA1, IA1, VIS1, VREF1, OACC1. change (PNRA.o_is PMA.AD fb) with (fb + 96) in PA1, IA1. change (PNRA.o_v PMA.AD fb) with (fb + 432) in VIS1, VREF1.
  change (PNM.PSIZE + 8) with 424 in OACC1.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 fb _ s1 HH1 FOK' PA1 OACC1) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  set (op := fb + 464) in *.
  set (H1 := ahid Aw1 model1) in *. set (MV := mrestrict H1 M1) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ LK1 cr1 Aw1 M1 model1 HH1) as VP; cbv zeta in VP; destruct VP as (_ & _ & _ & VFS & VB & VBS & VFSS & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF' LK1 cr1 Aw1 M1 model1 sp 28672 160 HH1 ASTK1 ltac:(clear; lia)) as (SL224 & _ & _).
  assert (ZZ : forall o k, 0 <= o -> o / 8 = k -> k <= 52 -> L5KA.zeros_at MV ((op + o) / 8 + 2147450880) 1).
  { intros o k Ho Ek Hk i Hi. replace ((op + o) / 8 + 2147450880 + i) with (op / 8 + 2147450880 + (k + i)) by (rewrite (div8_add op o O8 Ho), Ek; clear; lia).
    apply Zop. pose proof (Z.div_pos o 8 Ho ltac:(clear; lia)) as D. rewrite Ek in D. clear - Hi Hk D; lia. }
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB1 & _). unfold PNM.OFF_TB in TB1.
  split; [exact (ZZ 368 46 ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia))|]. split; [exact (ZZ 369 46 ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia))|].
  split; [exact (ZZ 376 47 ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia))|]. split; [exact (ZZ 384 48 ltac:(clear; lia) ltac:(reflexivity) ltac:(clear; lia))|].
  split; [apply (L5.writable_sub RSEGS MV op 424); [exact OWR| clear; lia| clear; lia]|].
  split; [apply (L5.writable_sub RSEGS MV op 424); [exact OWR| clear; lia| clear; lia]|].
  split; [exact TB1|].
  destruct (PNM.b_tb s1) as [n|c n p] eqn:ETB.
  - destruct TB1 as (D & Cc & Hn & U).
    split; [exact Hn|]. split; [| split; [clear - Hn; lia| apply PMF.even_byte]].
    apply (proj2 (L5A.u8_at_vis H1 M1 (op + 368) _ (OVIS (op + 368) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia))). exact U.
  - destruct TB1 as (D & Cc & W0 & W8 & W16 & Hn & Hc & Hev & DBp & CBp).
    assert (Ip : In (p, c) (PNM.bparser_own s1)) by (apply (PNBOA.PNM_own_tb s1 p c); rewrite ETB; left; reflexivity).
    assert (IpL : In (p, c) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Ip).
    pose proof (WB1 _ IpL) as ((Y0 & Y1 & Y2 & Y3 & Y4 & Y5) & _ & _ & _ & _ & _ & YFS). cbn [fst snd] in *.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Y1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5.
    pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(clear; lia)) as HVB.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p c op 416 HH1 IpL (PMAUAR.aobjA_push FF _ 416 _ (PNAPAR.aobj_fbB FF fb op 416 FOK ltac:(unfold op; clear; lia) ltac:(unfold op; clear; lia)))) as [Z0|Z0].
    all: split; [apply (proj2 (L5A.u8_at_vis H1 M1 (op + 368) _ (OVIS (op + 368) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia)));
                 exact (PMF.u8_of_u64 RSEGS M1 (op + 368) (c + 1) ltac:(clear - Hc; lia) W0)|].
    all: split; [clear - HVB; lia|]. all: split; [exact (PMF.odd_byte c Hev ltac:(clear - Hc; lia))|].
    all: split; [apply (proj2 (L5A.u64_at_vis H1 M1 (op + 384) _ (OVIS (op + 384) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia)));
                 replace (op + 384) with (op + 368 + 16) by (clear; lia); exact W16|].
    all: split; [apply (proj2 (L5A.u64_at_vis H1 M1 (op + 376) _ (OVIS (op + 376) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1; lia)));
                 replace (op + 376) with (op + 368 + 8) by (clear; lia); exact W8|].
    all: split; [exact Hn|]. all: split; [exact Hc|]. all: split; [clear - Y0 Y5 Hc; lia|]. all: split; [apply PMKA.mod16_8'; exact Y2|]. all: split; [clear - Y5 Hc; lia|].
    all: split; [pose proof (PMKA.blk_shadow_vis L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 p c p 8 HH1 IpL ltac:(clear; lia) ltac:(clear - Hc; lia) (PMKA.mod16_8' p Y2) ltac:(clear; lia) ltac:(reflexivity)) as ZP;
                 change (8 / 8) with 1 in ZP; apply ZP; intros a Ha; apply CBp; clear - Ha Hc; lia|].
    all: split; [apply (proj2 (L5A.writable_vis H1 M1 p 1 (VB p c p 1 IpL ltac:(clear; lia) ltac:(clear - Hc; lia)) ltac:(clear - Y0; lia) ltac:(clear - Y5 Hc; lia)));
                 apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M1 p c); [exact DBp| clear; lia| clear - Hc; lia]| clear - Y0; lia| clear - Y5 Hc; lia]|].
    all: split; [right; clear - Y4 GSLO Hc; lia|]. all: split; [unfold op in Z0; clear - Z0 Hc; lia|]. all: split; [clear - Y1 Hc; lia|]. all: exact Ip.
Qed.

End WithHeap.
End PNARVKX.
