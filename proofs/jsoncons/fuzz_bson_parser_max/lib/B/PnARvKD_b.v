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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b PnBrKitA_b PnOwnerFactsA_b PnSpecsAXD_b PnARvK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.

Module PNARVKD.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

(* [comment removed for export] *)
Lemma cap48 c n p tg : PM.tb_ok (PM.VLong c n p) tg -> 48 <= c.
Proof.
  intros (Htg & Hcap & (j & Hj & _ & _ & Hm) & H1). cbn [PM.vs_cap] in Hcap.
  assert (P2 : 2 <= 2 ^ tg) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; Lia.lia).
  assert (M8 : c mod 8 = 0).
  { apply Z.mod_divide; [Lia.lia|]. apply Z.mod_divide in Hm; [| apply Z.pow_nonzero; Lia.lia]. destruct Hm as (q & Eq). exists (q * 2 ^ j).
    rewrite Eq. rewrite Z.pow_add_r by Lia.lia. change (2 ^ 3) with 8. Lia.lia. }
  pose proof (Z.div_mod c 8 ltac:(Lia.lia)) as Dm. rewrite M8 in Dm. Lia.lia.
Qed.
Lemma set_cs1_id s : set_cs 1 s (PNM.b_tb s) (PNM.b_tg s) = s.
Proof. destruct s; reflexivity. Qed.
(* [comment removed for export] *)
Lemma aacc_of_sz (M : mem) a g : a mod 8 = 0 -> 0 <= a -> shadow_zero M a g -> aacc M a (8 * g).
Proof.
  intros A8 A0 SZ x Hx. left. unfold S in *.
  pose proof (Z.div_mod a 8 ltac:(Lia.lia)) as Da. rewrite A8, Z.add_0_r in Da.
  assert (E : x / 8 = a / 8 + (x - a) / 8).
  { replace x with ((x - a) + (a / 8) * 8) at 1 by Lia.lia. rewrite Z.div_add by Lia.lia. Lia.lia. }
  rewrite E. replace (a / 8 + (x - a) / 8 + SB) with (a / 8 + SB + (x - a) / 8) by Lia.lia.
  apply SZ. split; [apply Z.div_pos; Lia.lia| apply Z.div_lt_upper_bound; Lia.lia].
Qed.

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
Definition dec128_specS : Prop := PNSAXD.dec128_spec RSEGS PMA.AD PMA.AN PMA.AAD L ar HI.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rv_call_dec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra c p : Z) :
  dec128_specS ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNM.b_tb s1 = PM.VLong c 42 p ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 p -> getr R1 (reg 11) = Z_to_bv 64 (p + 42) -> getr R1 (reg 12) = Z_to_bv 64 (sp - 120) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 ptr,
      regs_preserved R1 R2 -> getr R2 (reg 10) = Z_to_bv 64 ptr -> p <= ptr <= p + 42 ->
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s1 sm1 (PNST.bax_add_dec ax1) cr1 ->
      (forall a, sp - 160 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c0, PMSPA.ec_at RSEGS M1 (fb + 1024) v c0 -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c0) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (PNL.pn_dec128 PMA.AN) M1 model1) K.
Proof.
  intros DEC CTX G LM ETB X1 RAok X2 X3 X4 X10 X11 X12 KR.
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
  set (op := fb + 464) in *. set (ois := fb + 96) in *. set (oec := fb + 1024) in *.
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDF1 & _).
  pose proof GFR as (GF1 & GF2 & _).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - GF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - GF2; pose proof (Z.div_le_upper_bound F 8 17592186044352 ltac:(lia) ltac:(lia)); lia).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  (* [comment removed for export] *)
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB1 & _). unfold PNM.OFF_TB in TB1. rewrite ETB in TB1.
  destruct TB1 as (Dtb & Atb & (W0 & W8 & W16 & Hvn & Hvc & Hev & DBp & CBp)).
  assert (GTB : PM.tb_ok (PM.VLong c 42 p) (PNM.b_tg s1)) by (rewrite <- ETB; exact (proj1 (proj2 GR1))).
  pose proof (cap48 c 42 p _ GTB) as C48.
  assert (Ip : In (p, c) (PNM.bparser_own s1)) by (apply (PNBOA.PNM_own_tb s1 p c); rewrite ETB; left; reflexivity).
  assert (IpL : In (p, c) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Ip).
  pose proof (WB1 _ IpL) as ((Y0 & Y1 & Y2 & Y3 & Y4 & Y5) & _ & _ & _ & _ & _ & YFS). cbn [fst snd] in Y0, Y1, Y2, Y3, Y4, Y5, YFS.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Y1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5.
  (* [comment removed for export] *)
  assert (SZ1 : shadow_zero M1 (sp - 28672) 3584).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 28672 WR M M1 EK1 WAPPR (sp - 28672) 3584); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
    apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (SP8 : (sp - 120) mod 8 = 0).
  { replace (sp - 120) with (sp + (-15) * 8) by (clear; lia). rewrite Z_mod_plus_full. apply PMKA.mod16_8'. exact A16. }
  unfold dec128_specS, PNSAXD.dec128_spec in DEC.
  apply (DEC fx1 R1 M1 model1 K (PNM.bparser_own s1 ++ LBX) FF' LK1 Aw1 cr1 p (sp - 120) (sp - 160) ra ax1 HH1 AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 3) with 18432. change (18432 / 8) with 2304.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 28672 160 18432 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 28672) 3584); [| | clear; lia| clear; lia| clear; lia| exact SZ1].
    - apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 18432) with (sp + (-1162) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 8 3 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 3 (sp - 160 + 32) FRS); clear; lia. }
  { replace (sp - 160) with (sp + (-5) * 32) by (clear; lia). rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { rewrite L5K.rl12. exact X12. }
  { exists p, c. split; [exact IpL| clear - C48; lia]. }
  { apply (L5.defined_sub M1 p c); [exact DBp| clear; lia| clear - C48; lia]. }
  { clear; lia. }
  { clear - GSHI; lia. }
  { destruct ASTK1 as (_ & _ & _ & _ & SDEF1 & _). apply (L5.defined_sub M1 (sp - 28672) 28672); [exact SDEF1| clear; lia| clear; lia]. }
  { unfold PMSPA.accA. apply (PNOKA.aacc_sub M1 (sp - 28672) (8 * 3584)); [| clear; lia| clear; lia].
    apply aacc_of_sz; [apply PMKA.mod16_8'; replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16| clear - SLO SPT GSLO GSPT; lia| exact SZ1]. }
  { apply PMKA.mod16_8'. exact Y2. }
  { intros x Hx. apply CBp. clear - Hx C48. lia. }
  { exact SP8. }
  { exact BASE1. } { exact ERR1. }
  intros fx6 R6 M6 model6 LK6 Aw6 ptr RP6 Y10 Hptr DEF6 ERR6 HP6 MRT6 INCL6 INCA6 AM6 HH6.
  change (PMSPA.pm_scr 3) with 18432 in HP6.
  set (Wc6 := (p, 42) :: (if PNST.bax_dec ax1 then [] else PNST.dec_W PMA.AD PMA.AN)) in HP6.
  assert (Wc6D : forall rr, In rr Wc6 -> rr = (p, 42) \/ In rr (PNST.dec_W PMA.AD PMA.AN)).
  { intros rr Hin. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; reflexivity|]. right. destruct (PNST.bax_dec ax1); [destruct Hin| exact Hin]. }
  assert (DWR : forall rr a, In rr (PNST.dec_W PMA.AD PMA.AN) -> L5.in_rng rr a -> 65536 <= a < 6905856).
  { intros rr a Hin Hr. unfold PNST.dec_W in Hin. cbn [pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (p <= a < p + 42) \/ (65536 <= a < 6905856)).
  { intros rr a Hin Hr. destruct (Wc6D rr Hin) as [->|Hd]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; exact Hr| right; exact (DWR rr a Hd Hr)]. }
  assert (WAV : forall rr a, In rr Wc6 -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64)).
  { intros rr a Hin Hr. unfold SB. destruct (Wc6R rr a Hin Hr) as [X|X].
    - split; [clear - X Y4 GSLO C48; lia| clear - X Y5 C48 DF1 DF2; lia].
    - split; [clear - X GSLO GSHI GSPT; lia| clear - X DF1; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 28672 a -> L5.outside WR a -> L5.outside Wc6 a).
  { intros a Hcl Ho rr Hin Hr. destruct (Wc6D rr Hin) as [->|Hd].
    - exfalso. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
      apply (PMARS1.own_not_aclient L ar C HI HIok (PNM.bparser_own s1) LBX FF' LK1 cr1 Aw1 M1 _ p c a sp 28672 HH1 Ip ltac:(clear - Hr C48; lia)). apply L5SAR.aclient_cons. exact Hcl.
    - apply (Ho rr); [| exact Hr]. unfold WR, PNRA.W_brun. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. unfold PNST.berr_W. apply in_or_app; right. exact Hd. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 160) (own sp R) F 3 WR (PNM.bparser_own s1) M6 model6 LK6 cr1 Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) (PNM.bparser_own s1) (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 M6 model6 LK6 cr1 Aw6 18432 Wc6 BI HP6 HH6 AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1' & Y2'); split; [unfold ocell; clear - Y1'; lia| exact Y2']| exact WOUT| intros a X; exact X]. }
  pose proof (proj1 HP6 : ek L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 18432 Wc6 M1 M6) as EK6.
  assert (WAPP6 : PMKA.wapp Wc6).
  { intros rr Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct (Wc6D rr Hin) as [->|Hd]; cbn [fst snd]; [clear - Y5 C48; lia|].
    unfold PNST.dec_W in Hd. cbn [pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj] in Hd.
    repeat (destruct Hd as [<-|Hd]; [cbn [fst snd]; clear; lia|]). destruct Hd. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  assert (OUTo : forall i, fb + 32 <= i < fb + 2040 -> L5.outside Wc6 i).
  { intros i Hi rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y|Y]; [| clear - Hi Y FBI; lia].
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ p c (fb + 32) 2008 HH1 IpL (PMAUAR.aobjA_push FF _ 2008 _ (PNAPAR.aobj_fbB FF fb (fb + 32) 2008 FOK ltac:(clear; lia) ltac:(clear; lia)))) as [Z0|Z0]; clear - Hi Y Z0 C48; lia. }
  assert (AGX : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> (forall i, a <= i < a + n -> aclient L ar (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 18432 i /\ L5.outside Wc6 i) -> L5C.agree_on M1 M6 a n).
  { intros a n Ha Hn HC i Hi. apply EK6. split; [clear - Hi Ha Hn; lia|]. exact (HC i Hi). }
  (* [comment removed for export] *)
  assert (SHO : forall x, 0 <= x < 2 ^ 47 -> L5.outside Wc6 (S x)).
  { intros x Hx rr Hin Hr. unfold S, SB in Hr. pose proof (Z.div_pos x 8 ltac:(clear - Hx; lia) ltac:(clear; lia)) as D0.
    pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx; lia)) as D1.
    destruct (Wc6R rr _ Hin Hr) as [Y|Y]; [clear - Y Y5 C48 D0 D1; lia| clear - Y D0; lia]. }
  assert (AGB : forall q m, In (q, m) (own_rest 1 s1) -> 0 <= q /\ q + m <= 2 ^ 64 /\ PMFA.agA M1 M6 q m).
  { intros q m Hq. assert (HqL : In (q, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact (incl_rest 1 s1 _ Hq)).
    destruct (BRB1 _ HqL) as (B0 & B1'). cbn [fst snd] in B0, B1'. split; [exact B0|]. split; [clear - B1'; lia|].
    assert (NE : q <> p).
    { pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1) as ND. intros E. subst q.
      pose proof (perm_cs 1 s1 LBX (or_intror eq_refl)) as PE. pose proof (ln_nodup_perm _ _ PE ND) as ND2. unfold PNRA.bcs_str in ND2. cbn [Z.eqb] in ND2. rewrite ETB in ND2.
      cbn [PM.vs_own app map fst] in ND2. apply stdpp.list_relations.list.NoDup_cons in ND2 as (NI & _). apply NI.
      apply in_elem_of. rewrite map_app. apply in_or_app; left. apply (in_map fst _ (p, m)). exact Hq. }
    destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q m p c HH1 HqL IpL NE) as [Z0|Z0].
    all: split; [intros x Hx; apply EK6; split; [clear - Hx B0 B1'; lia|]; split; [left; exists (q, m); split; [exact HqL| cbn [fst snd]; exact Hx]|];
                 intros rr Hin Hr; destruct (Wc6R rr x Hin Hr) as [Y|Y]; [clear - Hx Y Z0 C48; lia| pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH1 HqL) as ZI; destruct ZI as [ZI|ZI]; clear - Hx Y ZI; lia]
               | intros x Hx; apply EK6; split; [unfold S, SB; pose proof (Z.div_pos x 8 ltac:(clear - Hx B0; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx B1'; lia)); lia|];
                 split; [do 6 right; exists (q, m); split; [exact HqL| cbn [fst snd]; unfold in_shadow_of; split; apply PNOFA.S_mono; clear - Hx; lia]| apply SHO; clear - Hx B0 B1'; lia]]. }
  assert (VS6 : PM.vstr_at RSEGS PMSPA.accA M6 (op + 368) (PM.VLong c 42 p)).
  { assert (AGh : L5C.agree_on M1 M6 (op + 368) 24).
    { apply AGX; [clear - O1; lia| clear - O1; lia|]. intros i Hi. split; [| apply OUTo; unfold op in Hi; clear - Hi; lia].
      apply (L5SAR.fframe_client L ar _ FF' (sp - 160) 18432 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; unfold op in Hi; clear - Hi; lia]. }
    assert (SHh : forall x, op + 368 <= x < op + 368 + 24 -> M6 (Z_to_bv 64 (S x)) = M1 (Z_to_bv 64 (S x))).
    { intros x Hx. apply EK6. split; [unfold S, SB; pose proof (Z.div_pos x 8 ltac:(clear - Hx O1; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx O1; lia)); lia|].
      split; [| apply SHO; clear - Hx O1; lia].
      apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 18432 fb 5 rs); [right; exact Hfb|]. change (ff_bytes 5) with 2048. unfold in_shadow_of. split; apply PNOFA.S_mono; unfold op in Hx; clear - Hx; lia. }
    assert (SHp : forall x, p <= x < p + c -> M6 (Z_to_bv 64 (S x)) = M1 (Z_to_bv 64 (S x))).
    { intros x Hx. apply EK6. split; [unfold S, SB; pose proof (Z.div_pos x 8 ltac:(clear - Hx Y0; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hx Y5; lia)); lia|].
      split; [| apply SHO; clear - Hx Y0 Y5; lia].
      do 6 right. exists (p, c). split; [exact IpL|]. cbn [fst snd]. unfold in_shadow_of. split; apply PNOFA.S_mono; clear - Hx; lia. }
    unfold PM.vstr_at. split; [intros i Hi; rewrite (AGh (op + 368 + i) ltac:(clear - Hi; lia)); exact (Dtb i Hi)|].
    split; [apply (PMFA.accA_agree M1 M6 (op + 368) 24); [exact SHh| exact Atb]|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M6 (op + 368) (c + 1)); [intros j Hj; apply AGh; clear - Hj; lia| clear - O1; lia| clear - O1; lia| exact W0]|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M6 (op + 368 + 8) 42); [intros j Hj; apply AGh; clear - Hj; lia| clear - O1; lia| clear - O1; lia| exact W8]|].
    split; [apply (L5C.u64_at_agree RSEGS M1 M6 (op + 368 + 16) p); [intros j Hj; apply AGh; clear - Hj; lia| clear - O1; lia| clear - O1; lia| exact W16]|].
    split; [exact Hvn|]. split; [exact Hvc|]. split; [exact Hev|].
    split.
    - intros i Hi. destruct (Z_lt_le_dec i 42) as [X|X]; [exact (DEF6 i ltac:(clear - Hi X; lia))|].
      assert (E : M6 (Z_to_bv 64 (p + i)) = M1 (Z_to_bv 64 (p + i))).
      { apply EK6. split; [clear - Hi Y0 Y5; lia|]. split; [left; exists (p, c); split; [exact IpL| cbn [fst snd]; clear - Hi; lia]|].
        intros rr Hin Hr. destruct (Wc6R rr _ Hin Hr) as [Y|Y]; [clear - Hi X Y; lia| clear - Hi Y Y1; lia]. }
      rewrite E. exact (DBp i Hi).
    - apply (PMFA.accA_agree M1 M6 p c); [exact SHp| exact CBp]. }
  assert (PA6 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M6 op ois s1).
  { rewrite <- (set_cs1_id s1) at 1. rewrite ETB.
    apply (bparser_set_csS M1 M6 (pa_vp_parser PMA.AD) op ois s1 1 (PM.VLong c 42 p) (PNM.b_tg s1) (or_intror eq_refl) ltac:(clear - O1; lia) ltac:(clear - O1; lia)); [| | exact AGB| exact VS6| exact PA1].
    - intros i Hi Hn'. unfold PNBOA.snt. apply EK6. split; [clear - Hi O1; lia|]. split; [| apply OUTo; unfold op in Hi; clear - Hi; lia].
      apply (L5SAR.fframe_client L ar _ FF' (sp - 160) 18432 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; unfold op in Hi; clear - Hi; lia].
    - intros i Hi. unfold PNBOA.sns. apply EK6. split; [unfold S, SB; pose proof (Z.div_pos i 8 ltac:(clear - Hi O1; lia) ltac:(clear; lia)); pose proof (Z.div_lt_upper_bound i 8 17592186044416 ltac:(clear; lia) ltac:(clear - Hi O1; lia)); lia|].
      split; [| apply SHO; clear - Hi O1; lia].
      apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 18432 fb 5 rs); [right; exact Hfb|]. change (ff_bytes 5) with 2048. unfold in_shadow_of. split; apply PNOFA.S_mono; unfold op in Hi; clear - Hi; lia. }
  assert (OUTB : forall q m, In (q, m) LBX -> forall i, q <= i < q + m -> L5.outside Wc6 i).
  { intros q m Hq i Hi rr Hin Hr. assert (HqL : In (q, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; right; exact Hq).
    destruct (Wc6R rr i Hin Hr) as [Y|Y].
    - assert (NE : q <> p).
      { pose proof (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH1) as ND. intros E. subst q. rewrite map_app in ND.
        pose proof (proj1 (proj2 (proj1 (stdpp.list_relations.list.NoDup_app _ _) ND)) p) as NI. apply NI; apply in_elem_of; [exact (in_map fst _ (p, c) Ip)| exact (in_map fst _ (p, m) Hq)]. }
      destruct (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q m p c HH1 HqL IpL NE) as [Z0|Z0]; clear - Hi Y Z0 C48; lia.
    - pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q m HH1 HqL) as ZI. destruct ZI as [ZI|ZI]; clear - Hi Y ZI; lia. }
  assert (IA6 : PM.iss_at RSEGS PMA.AD PMSPA.accA M6 ois str sm1).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF' (sp - 160) 18432 Wc6 M1 M6 EK6 WAPP6 FRB1 BRB1 ois str sm1); [| | | | exact IA1].
    - apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - apply incl_appr. exact INCS.
    - intros i Hi. apply OUTo. unfold ois in Hi. clear - Hi; lia.
    - intros c0 n0 p0 E0. unfold PMKA.blk_out. apply (OUTB p0 c0). apply INCS. rewrite E0. left; reflexivity. }
  assert (BASE6 : PMSTA.base_okA RSEGS PMA.AD M6).
  { destruct (PNST.bax_dec ax1) eqn:EDX.
    - apply (PMASK.base_keep L ar C LY _ FF' (sp - 160) 18432 Wc6 M1 M6 EK6); [| exact BASE1].
      intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|[]]. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Ha Hr Y1 C48; lia.
    - apply (base_keepW _ FF' (sp - 160) 18432 Wc6 M1 M6 EK6); [| | | | exact BASE1].
      all: try (intros a Ha rr Hin Hr); try (intros rr Hin Hr); destruct (Wc6D rr Hin) as [->|Hd];
        [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Y1 C48 + clear - Ha Hr Y1 C48; lia
        | unfold PNST.dec_W in Hd; cbn [pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj] in Hd; unfold L5.in_rng in Hr;
          repeat (destruct Hd as [<-|Hd]; [cbn [fst snd] in Hr; clear - Hr + clear - Ha Hr; lia|]); destruct Hd]. }
  apply (KR fx6 R6 M6 model6 LK6 Aw6 ptr RP6); [rewrite <- L5K.rl10; exact Y10| exact Hptr| | |].
  - split; [exact BI6|].
    split. { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF' (sp - 160) 18432 Wc6 M1 M6 fb s1 s1 str sm1 sm1 ax1 (PNST.bax_add_dec ax1) FRB1 EK6 WAPP6 FOK');
               [| exact RP1| exact PA6| exact IA6| exact GR1| exact BASE6| exact ERR6].
             intros i Hi. apply OUTo. clear - Hi; lia. }
    split; [exact STEP1|]. split; [exact (PNST.bax_le_trans _ _ _ AXL1 (PNST.bax_le_dec ax1))|]. split; [exact CK1|].
    split; [| exact EBB1].
    apply (L5C.u8_at_agree RSEGS M1 M6); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK6. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 18432 F 3 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK6. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 18432 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) 18432 Wc6 M1 M6 EK6 WAPP6 FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + intros i Hi. apply OUTo. clear - Hi; lia.
Qed.

End WithHeap.
End PNARVKD.
