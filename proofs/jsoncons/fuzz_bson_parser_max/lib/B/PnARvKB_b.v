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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b PnBrKitA_b PgV8A_b PnARvK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From stdpp Require list_relations list_basics.

Module PNARVKB.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

(* [comment removed for export] *)
Lemma perm_vw {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (a ++ c ++ (b ++ n ++ t) ++ x).
Proof.
  rewrite <- !app_assoc. apply Permutation_app_head. rewrite !app_assoc. do 3 apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma with_src_bb_id s : PNM.with_src_bb s (PNM.b_src s) (PNM.b_bb s) (PNM.b_bg s) = s.
Proof. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Definition midb (R Rc : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr Rc (reg 2) = Z_to_bv 64 (sp - 160) /\ getr Rc (reg 3) = getr R (reg 3) /\ getr Rc (reg 4) = getr R (reg 4)
  /\ getr Rc (reg 8) = Z_to_bv 64 sp /\ getr Rc (reg 9) = Z_to_bv 64 (sp - 160)
  /\ getr Rc (reg 18) = Z_to_bv 64 (F / 8 + 2147450880) /\ getr Rc (reg 19) = Z_to_bv 64 F /\ getr Rc (reg 20) = Z_to_bv 64 (fb + 464)
  /\ getr Rc (reg 21) = Z_to_bv 64 (fb + 1024) /\ getr Rc (reg 22) = Z_to_bv 64 (fb + 432) /\ getr Rc (reg 23) = Z_to_bv 64 (fb + 464 + 400)
  /\ getr Rc (reg 25) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880) /\ getr Rc (reg 26) = Z_to_bv 64 2147450880 /\ getr Rc (reg 27) = Z_to_bv 64 F.
Definition MIDBREGS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat.
Lemma midb_keep R Rc R1 sp fb F : midb R Rc sp fb F -> (forall k, In k MIDBREGS -> getr R1 (reg k) = getr Rc (reg k)) -> midb R R1 sp fb F.
Proof.
  intros (X2 & X3 & X4 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X25 & X26 & X27) KS. unfold midb.
  rewrite !KS by (cbn; tauto). repeat split; assumption.
Qed.
(* [comment removed for export] *)
Definition ecsp (M : mem) (sp fb : Z) : Prop := L5.u64_at RSEGS M (sp - 136) (fb + 464 + 16).

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

(* [comment removed for export] *)
Lemma rv_call_rsv K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (ra len : Z) :
  PNRAa.read_span_v_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (sp - 160) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (fb + 464 + 16) -> getr R1 (reg 11) = Z_to_bv 64 len -> getr R1 (reg 12) = Z_to_bv 64 (fb + 464 + 320) ->
  0 <= len < 2 ^ 64 -> PM.unread (PNM.b_src s1) sm1 < 2 ^ 26 -> PGV8.v8_room (PNM.b_bb s1) (PM.unread (PNM.b_src s1) sm1) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3 src3 bb3 bg3 sm3 cr3 ptr n,
      regs_preserved R1 R2 -> getr R2 (reg 10) = Z_to_bv 64 ptr -> getr R2 (reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
      PMSP.consumed (PNM.b_src s1) src3 sm1 sm3 = n ->
      ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own (PNM.with_src_bb s1 src3 bb3 bg3)) ptr n) ->
      L5.defined M3 ptr n -> PMSPA.accA M3 ptr n ->
      (n = len -> PGV8.v8_room bb3 (PM.unread src3 sm3)) ->
      PM.unread src3 sm3 <= PM.unread (PNM.b_src s1) sm1 ->
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 (PNM.with_src_bb s1 src3 bb3 bg3) sm3 ax1 cr3 ->
      (forall a, sp - 160 <= a < sp - 104 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (PNL.pn_read_span_v PMA.AN) M1 model1) K.
Proof.
  intros SPN CTX G LM X1 RAok X2 X3 X4 X10 X11 X12 Hlen UN1 ROOM1 KR.
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
  assert (WAPPR : PMKA.wapp WR).
  { unfold WR, PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  (* [comment removed for export] *)
  set (T := PNM.vec_owner RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) op ois (fb + 32) (fb + 2040) s1).
  assert (OK : PGV8A.vowner_ok RSEGS PMA.AD L ar HI T).
  { apply (PNOKA.vec_owner_ok RSEGS PMA.AD (pa_vp_parser PMA.AD) L ar HI op ois (fb + 32) (fb + 2040) s1 (HAJ.aior_wf _ _ _ _ _ HIok)).
    - change PNM.PSIZE with 416. unfold op, ois.
      assert (M8 : (fb + 464) mod 8 = 0 /\ (fb + 96) mod 8 = 0).
      { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. split.
        - rewrite Dm. replace (2048 * (fb / 2048) + 464) with ((256 * (fb / 2048) + 58) * 8) by (clear; lia). apply Z_mod_mult.
        - rewrite Dm. replace (2048 * (fb / 2048) + 96) with ((256 * (fb / 2048) + 12) * 8) by (clear; lia). apply Z_mod_mult. }
      clear - M8 F1 F2 FSCEIL GSLO GSHI GSPT FBI. lia.
    - right. unfold op, ois. change PNM.PSIZE with 416. clear; lia. }
  set (src1 := PNM.b_src s1) in *. set (bb1 := PNM.b_bb s1) in *. set (bg1 := PNM.b_bg s1) in *. set (OB := PNM.vec_rest_own s1).
  set (LB1 := PM.src_own src1 ++ PGV8.v8_own bb1 ++ OB ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) LB1).
  { unfold LB1, OB, src1, bb1, PNM.bparser_own, PNM.brest_own, PNM.vec_rest_own. apply perm_vw. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF1 & _).
  assert (NDFF : base.NoDup (map ff_addr FF')) by (rewrite map_app in NDF1; apply stdpp.list_relations.list.NoDup_app in NDF1; exact (proj1 NDF1)).
  assert (HHp : ri_inv HI LB1 FF' LK1 cr1 Aw1 M1 (vml_of model1)).
  { apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK1 cr1 Aw1 M1 _ HH1).
    - intros b. split; [apply Permutation_in; exact PERM1| apply Permutation_in; apply Permutation_sym; exact PERM1].
    - apply (ln_nodup_perm (PNM.bparser_own s1 ++ LBX)); [exact PERM1| exact ND1].
    - intros f. tauto.
    - exact NDFF. }
  pose proof GFR as (GF1 & GF2 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (R4a : 0 <= F / 8 + 2147450880) by (clear - DF1; lia).
  assert (R4b : F / 8 + 2147450880 + 1 <= 2 ^ 64) by (clear - DF2; lia).
  pose proof GR1 as (GNB & GTB & GBB).
  pose proof (PMA.ly_cost L C LY) as (LCK & LCL & LCO).
  assert (CRX : PMSP.credit_le (PMSPA.scA L (PGV8.pot_v8 (PMSPA.HV L ar) bb1 bg1)) cr1).
  { pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _).
    assert (P1 : forall y gy oy, PM.vstr_at RSEGS PMSPA.accA M1 oy y -> PM.tb_ok y gy -> 0 <= fst (PM.pot_text (PMSPA.HV L ar) y gy) /\ 0 <= snd (PM.pot_text (PMSPA.HV L ar) y gy)).
    { intros y gy oy (_ & _ & VSy) (Hg & _ & _). unfold PM.pot_text. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
      assert (Cy : PM.vs_cap y <= 2 ^ 27) by (destruct y as [n|cc n p]; cbn [PM.vs_cap]; [clear; lia| destruct VSy as (_ & _ & _ & _ & Hcc & _); clear - Hcc; lia]). clear - Hg Cy. lia. }
    assert (P2 : 0 <= fst (PGV8.pot_v8 (PMSPA.HV L ar) bb1 bg1) /\ 0 <= snd (PGV8.pot_v8 (PMSPA.HV L ar) bb1 bg1)).
    { destruct BB1 as (_ & _ & VSb). pose proof (PGV8.v8_ok_cap _ _ GBB) as (Hg & _). unfold PGV8.pot_v8. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
      assert (Cy : PGV8.v8_cap bb1 <= 2 ^ 27) by (unfold bb1 in *; revert VSb; destruct (PNM.b_bb s1) as [|b n cc]; intros VSb; cbn [PGV8.v8_cap]; [clear; lia| destruct VSb as (_ & _ & _ & _ & Hcc & _); clear - Hcc; lia]). clear - Hg Cy. lia. }
    assert (P3 : 0 <= fst (PNRA.pot_bstack L ar (PNM.b_sk s1)) /\ 0 <= snd (PNRA.pot_bstack L ar (PNM.b_sk s1))).
    { destruct SV1 as (_ & _ & _ & Hk & _). unfold PNRA.pot_bstack, PNM.BSZ. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead PMSPA.HV LibIfaceAB.heap_view]. rewrite LCK, LCO.
      assert (P : 2 ^ (PNM.b_sk s1 + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; clear - Hk; lia). clear - Hk P. lia. }
    pose proof (P1 _ _ _ NB1 GNB) as P4. pose proof (P1 _ _ _ TB1 GTB) as P5.
    revert CRED CK1 P2 P3 P4 P5. unfold PMSP.credit_le, PMSP.credit_keep, PMSPA.scA, PNRA.pot_bparser, PM.credit_add, bb1, bg1. cbn [fst snd]. rewrite LCL.
    clear; intros; lia. }
  unfold PNRAa.read_span_v_spec, PNRA.read_span_v_spec, PGV8A.read_span_v_specG in SPN.
  apply (SPN T OK fx1 R1 M1 model1 K OB LBX FF' LK1 Aw1 cr1 (sp - 160) ra len src1 bb1 bg1 str sm1 HHp AM1 K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 6) with 24576. change (24576 / 8) with 3072.
    split; [apply (L5SAR.astk_sub ar M1 M1 sp 28672 160 24576 ASTK1 (mem_grows_refl M1)); [clear; lia| clear; lia| clear; lia| replace (sp - 160) with (sp + (-10) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub M1 (sp - 28672) 3584); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (sp - 160 - 24576) with (sp + (-1546) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar LBX FF sp 28672 WR M M1 EK1 WAPPR (sp - 28672) 3584); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
      apply PMKA.mod16_8'. replace (sp - 28672) with (sp + (-1792) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 8 6 FF LK LK1 _ FRM INCL1); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 160) F 3 (sp - 160 + 32) FRS); clear; lia. }
  { unfold PGSA.ofr. cbn [T PNM.vec_owner PGV8.vw_lo PGV8.vw_hi]. apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 32) (fb + 2040 - (fb + 32)) FOK); clear; lia. }
  { rewrite L5K.rl10. cbn [T PNM.vec_owner PGV8.vw_os]. unfold PNM.OFF_SRC. exact X10. }
  { rewrite L5K.rl11. exact X11. }
  { rewrite L5K.rl12. cbn [T PNM.vec_owner PGV8.vw_ov]. unfold PNM.OFF_BB. exact X12. }
  { exact Hlen. }
  { cbn [T PNM.vec_owner PGV8.vw_at]. split; [| split; [exact GBB| reflexivity]]. unfold src1, bb1, bg1. rewrite with_src_bb_id. exact PA1. }
  { cbn [T PNM.vec_owner PGV8.vw_ois]. exact IA1. }
  { exact BASE1. } { exact INCS. } { exact UN1. } { exact ROOM1. } { exact CRX. }
  intros fx4 R4 M4 model4 LK4 Aw4 src4 bb4 bg4 sm4 cr4 ptr n RP4 Y10 Y11 Hn1 Hn2 CONS4 LOC DEF4 ACC4 ROOM4 TW4 IA4 STEP4 HP4 CK4 MRT4 INCL4 INCA4 AM4 HH4.
  cbn [T PNM.vec_owner PGV8.vw_at PGV8.vw_ois PGV8.vw_os PGV8.vw_ov] in TW4, IA4, HP4, LOC. destruct TW4 as (PA4 & GBB4 & _).
  change (PMSPA.pm_scr 6) with 24576 in HP4. unfold PNM.OFF_SRC, PNM.OFF_BB in HP4, LOC.
  rewrite L5K.rl10 in Y10. rewrite L5K.rl11 in Y11.
  set (s2 := PNM.with_src_bb s1 src4 bb4 bg4).
  set (LB2 := PM.src_own src4 ++ PGV8.v8_own bb4 ++ OB ++ LBX) in HH4.
  assert (PERM2 : Permutation LB2 (PNM.bparser_own s2 ++ LBX)).
  { unfold LB2, OB, s2, PNM.bparser_own, PNM.brest_own, PNM.vec_rest_own. cbn [PNM.with_src_bb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
    apply Permutation_sym. apply perm_vw. }
  assert (HH4' : ri_inv HI (PNM.bparser_own s2 ++ LBX) FF' LK4 cr4 Aw4 M4 (vml_of model4)).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND4 & NDF4 & _).
    apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF' FF' LK4 cr4 Aw4 M4 _ HH4).
    - intros b. split; [apply Permutation_in; exact PERM2| apply Permutation_in; apply Permutation_sym; exact PERM2].
    - apply (ln_nodup_perm LB2); [exact PERM2| exact ND4].
    - intros f. tauto.
    - exact NDFF. }
  set (Wc := PGS.W_srcfG (op + 16) ois ++ [(op + 320, 24)]) in HP4.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
            (fb + 736 <= a < fb + 776) \/ (fb + 136 <= a < fb + 144) \/ (fb + 248 <= a < fb + 252) \/ (fb + 784 <= a < fb + 808)).
  { intros rr a Hin Hr. unfold Wc, PGS.W_srcfG in Hin. unfold L5.in_rng in Hr. cbn [app] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; unfold op, ois in Hr; clear - Hr; lia|]). destruct Hin. }
  pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (sp - 160 <= a < sp) /\ ~ (F / 8 + SB <= a < F / 8 + SB + 64)).
  { intros rr a Hin Hr. unfold SB. pose proof (WcR rr a Hin Hr) as X.
    split; [clear - X GSLO F2 FSCEIL; lia| destruct FA1 as [Y|Y]; clear - X Y DF1 DF2 F1 F2; lia]. }
  assert (WOUT : forall a, aclient L ar LBX FF sp 28672 a -> L5.outside WR a -> L5.outside Wc a).
  { intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X|[X|[X|X]]].
    - apply (Ho (PNRA.o_src PMA.AD fb + 256, 40)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; right; left; reflexivity| unfold L5.in_rng, PNRA.o_src, PNRA.o_p, PMSP.o_p, PNM.OFF_SRC; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - apply (Ho (PNRA.o_is PMA.AD fb + 40, 8)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; right; right; left; reflexivity| unfold L5.in_rng, PNRA.o_is, PMSP.o_is; cbn [fst snd pa_off_is PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - apply (Ho (PNRA.o_is PMA.AD fb + 152, 4)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; right; right; right; left; reflexivity| unfold L5.in_rng, PNRA.o_is, PMSP.o_is; cbn [fst snd pa_off_is PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia].
    - apply (Ho (PNRA.o_bb PMA.AD fb, 24)); [unfold WR, PNRA.W_brun, PGS.W_srcfG; cbn [app]; do 4 right; left; reflexivity| unfold L5.in_rng, PNRA.o_bb, PNRA.o_p, PMSP.o_p, PNM.OFF_BB; cbn [fst snd pa_off_p PMA.AD PnLayoutA_b.ADDR_A]; clear - X; lia]. }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 28672 (sp - 160) (own sp R) F 3 WR (PNM.bparser_own s2) M4 model4 LK4 cr4 Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 28672 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 3 LK2 M2 model2 cr (PNM.bparser_own s) G
             WR WR (PNM.bparser_own s1) [] (PNM.bparser_own s2) M1 model1 LK1 cr1 Aw1 M4 model4 LK4 cr4 Aw4 24576 Wc BI HP4 HH4' AM4 MRT4 INCA4 INCL4);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]| exact WOUT| intros a X; exact X]. }
  pose proof (proj1 HP4 : ek L ar LBX FF' (sp - 160) 24576 Wc M1 M4) as EK4.
  assert (WAPPc : PMKA.wapp Wc).
  { intros rr Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. unfold Wc, PGS.W_srcfG in Hin. cbn [app] in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd]; unfold op, ois; destruct FA1 as [Y|Y]; clear - Y F1 F2; lia|]). destruct Hin. }
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as FRB1.
  assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4).
  { apply (PMASK.base_keep L ar C LY _ FF' (sp - 160) 24576 Wc M1 M4 EK4); [| exact BASE1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. clear - Ha Y FBI; lia. }
  assert (ERR4 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M4 ax1).
  { apply (berr_keep _ FF' (sp - 160) 24576 Wc M1 M4 ax1 EK4); [| exact ERR1].
    intros a Ha rr Hin Hr. pose proof (WcR rr a Hin Hr) as Y. clear - Ha Y FBI; lia. }
  assert (GR4 : PNM.bgrow_ok s2).
  { unfold s2, PNM.bgrow_ok. cbn [PNM.with_src_bb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg]. exact (conj GNB (conj GTB GBB4)). }
  apply (KR fx4 R4 M4 model4 LK4 Aw4 src4 bb4 bg4 sm4 cr4 ptr n RP4 Y10 Y11 Hn1 Hn2 CONS4).
  - destruct LOC as [W0|(B & m & Hin & Xa & Xb)]; [left; exact W0| right].
    exists B, m. split; [| split; [exact Xa| exact Xb]].
    unfold OB, PNM.bparser_own, PNM.brest_own, PNM.vec_rest_own in *. cbn [PNM.with_src_bb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
    revert Hin. clear. rewrite !in_app_iff. tauto.
  - exact DEF4.
  - exact ACC4.
  - exact ROOM4.
  - destruct STEP4 as (_ & _ & _ & _ & LE). exact LE.
  - split; [exact BI4|].
    split. { apply (pre_after_call LBX FF' (sp - 160) 24576 Wc M1 M4 fb s1 s2 str sm1 sm4 ax1 ax1 FRB1 EK4 WAPPc FOK');
               [| exact RP1| exact PA4| exact IA4| exact GR4| exact BASE4| exact ERR4].
             intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. clear - Hi Y; lia. }
    split; [unfold s2; cbn [PNM.with_src_bb PNM.b_src]; exact (src_step_trans _ _ _ _ _ _ STEP1 STEP4)|].
    split; [exact AXL1|].
    split. { revert CK1 CK4. unfold PMSP.credit_keep, PMSPA.scA, PNRA.pot_bparser, PM.credit_add, s2, bb1, bg1. cbn [fst snd].
             cbn [PNM.with_src_bb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear; intros; lia. }
    split; [| exact I].
    apply (L5C.u8_at_agree RSEGS M1 M4); [| exact R4a| exact R4b| exact SHC1].
    intros j Hj. apply EK4. split; [clear - Hj R4a R4b; lia|]. split.
    + apply (L5SAR.fframe_shadow_client L ar _ FF' (sp - 160) 24576 F 3 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hj; lia.
    + intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hj; lia.
  - intros a Ha. apply EK4. split; [clear - Ha GSLO GSHI GSPT; lia|]. split.
    + apply (L5SAR.stack_client L ar _ FF' (sp - 160) 24576 a); clear - Ha GSLO GSHI GSPT; lia.
    + intros rr Hin Hr. destruct (WAV rr a Hin Hr) as (Y & _). apply Y. clear - Ha; lia.
  - intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF' (sp - 160) 24576 Wc M1 M4 EK4 WAPPc FRB1 (fb + 1024) v0 c0); [| | exact E0].
    + apply PMAUAR.aobjA_push. apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia.
    + intros i Hi rr Hin Hr. pose proof (WcR rr i Hin Hr) as Y. clear - Hi Y; lia.
Qed.


(* [comment removed for export] *)
Lemma rv_piece_scr K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) (W : Z -> Prop) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall a, W a -> sp - 160 <= a < sp - 104 \/ F + 32 <= a < F + 480 \/ F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 60 \/ sp - 28672 <= a < sp - 160) ->
  (forall (M3 : mem) model3,
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 -> mrestrict (ahid Aw1 model1) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> mem_grows M1 M3 ->
      (forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ WP KR.
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
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  assert (DF3 : F / 8 * 8 = F) by (exact (proj1 GF8)).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2v W K HH1 AM1 MS MG FRZ).
  { intros a Ha Wa. split.
    - destruct (WP a Wa) as [X|[X|[X|X]]]; [| | | unfold aclientw, aclient_g; right; left; split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X GSLO GSHI GSPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar _ FF' 0 0 F 3 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 3) with 512; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar _ FF' 0 0 F 3 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct (WP a Wa) as [X|[X|[X|X]]]; clear - X GFR SL160 GSLO GSHI GSPT FBI FSAPP FSCEIL DF1 F1 F2; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as BRB1.
  (* [comment removed for export] *)
  assert (NCW3 : forall a, (sp - 160 <= a < sp - 104 \/ F + 32 <= a < F + 480 \/ F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 60) -> ~ aclient L ar (PNM.bparser_own s1 ++ LBX) FF sp 28672 a).
  { intros a WP3. apply nc_lift.
    - intros b Hb. destruct b as (q, m). cbn [fst snd].
      destruct (L5ADHR.blocks_off_fs L ar C HI HIok _ _ _ _ _ _ _ (PNM.bparser_own s1) LBX HH1 eq_refl (q, m) Hb) as ((Q0 & _ & _ & Q3 & Q4 & (_ & Q5 & _)) & Q6).
      cbn [fst snd] in Q0, Q3, Q4, Q5, Q6. unfold BIGSHADOW_LO, BIGSHADOW_HI in Q5. unfold FS_BYTES in Q6, GFS2.
      assert (QD1 : 0 <= q / 8) by (apply Z.div_pos; clear - Q0; lia).
      assert (QD2 : (q + m - 1) / 8 <= 17592186044415) by (apply Z.div_le_upper_bound; clear - Q4 GSLO GSHI GSPT; lia).
      unfold in_shadow_of, S, SB.
      destruct WP3 as [X|[X|X]].
      + split; [intros Y; clear - X Y Q4 GSLO; lia| intros Y; clear - X Y QD2 SL160 SLO SHI SPT GSLO GSHI GSPT; lia].
      + split; [intros Y; clear - X Y Q6 GFS1 GFS2; lia| intros Y; clear - X Y QD1 QD2 GFBIG; lia].
      + split; [intros Y; clear - X Y Q5 DF1 DF2; lia|]. intros (Y1 & Y2). destruct Q6 as [Q6|Q6].
        * assert (QD3 : (q + m - 1) / 8 < F / 8) by (apply Z.div_lt_upper_bound; [clear; lia| rewrite Z.mul_comm, DF3; clear - Q6 GFS1; lia]).
          clear - X Y2 QD3; lia.
        * assert (QD4 : F / 8 + 64 <= q / 8) by (apply Z.div_le_lower_bound; [clear; lia| clear - Q6 GFS2 DF3; lia]).
          clear - X Y1 QD4; lia.
    - destruct WP3 as [X|[X|X]].
      + apply GNCS. clear - X; lia.
      + apply GNCF. left. clear - X; lia.
      + apply GNCF. right. unfold S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia. }
  assert (NCW : forall a, W a -> ~ aclient L ar (PNM.bparser_own s1 ++ LBX) FF sp 28672 a).
  { intros a Wa. destruct (WP a Wa) as [X0|[X0|[X0|X0]]]; [apply NCW3; left; exact X0| apply NCW3; right; left; exact X0| apply NCW3; right; right; exact X0|].
    intros Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF' LK1 cr1 Aw1 M1 _ sp 28672 a HH1 GSPT (L5SAR.aclient_cons L ar _ FF _ _ _ _ Hc)) as [Y|Y]; clear - X0 Y GSLO; lia. }
  assert (EKx : L5SAR.ek L ar (PNM.bparser_own s1 ++ LBX) FF sp 28672 [] M1 M3).
  { intros a (Ha & Hc & _). apply FR3; [exact Ha|]. intros Wa. exact (NCW a Wa Hc). }
  assert (ECK : forall v c, PMSPA.ec_at RSEGS M1 (fb + 1024) v c -> PMSPA.ec_at RSEGS M3 (fb + 1024) v c).
  { intros v0 c0 E0. apply (PMKA.ec_keepA RSEGS L ar _ FF sp 28672 [] M1 M3 EKx PMKA.wapp_nil FRB (fb + 1024) v0 c0); [| intros i _ rr []| exact E0].
    apply (PNAPAR.aobj_fbB FF fb (fb + 1024) 16 FOK); clear; lia. }
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3| exact MG3| exact ECK].
  split.
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT3]|]. split; [exact INCA1|]. split; [exact INCL1|].
    split; [eapply L5SAR.astk_grows; [exact ASTK1| exact MG3]|].
    split. { eapply L5SAR.ek_trans; [exact EK1|]. intros a (Ha & Hc & Ho). apply FR3; [exact Ha|]. intros Wa.
             destruct (WP a Wa) as [X|[X|[X|X]]].
             - apply (GNCS a); [clear - X; lia| exact Hc].
             - apply (GNCF a); [left; clear - X; lia| exact Hc].
             - apply (GNCF a); [right; unfold S; rewrite (proj1 (proj2 GF8)); unfold SB; clear - X; lia| exact Hc].
             - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 28672 a HH GSPT (L5SAR.aclient_appb L ar _ (PNM.bparser_own s) _ _ _ _ Hc)) as [Y|Y]; clear - X Y GSLO; lia. }
    split. { eapply L5SAR.dk_trans; [exact DK1|]. apply L5SAR.dk_grows. exact MG3. }
    split. { apply (GOWN M1 M3 OWN1). intros a Ha. pose proof (GOCR a Ha) as OC. apply FR3; [clear - OC GSPC GSLO; lia|]. intros Wa.
             destruct (WP a Wa) as [X|[X|[X|X]]]; [clear - X OC; lia| clear - X OC GFCEIL GSLO; lia| clear - X OC DF2 GSLO GSHI GSPT; lia| clear - X OC; lia]. }
    eapply L5.defined_grows; [exact MG3| exact DSH1]. }
  split.
  { apply (pre_after_call (PNM.bparser_own s1 ++ LBX) FF sp 28672 [] M1 M3 fb s1 s1 str sm1 sm1 ax1 ax1 FRB EKx (PMKA.wapp_nil) FOK); [intros i _ rr []| exact RP1| | | exact GR1| |].
    - assert (AOP : PMSPA.aobjA FF (fb + 464) PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb (fb + 464) PNM.PSIZE FOK); unfold PNM.PSIZE; clear; lia).
      destruct (PMKA.aobjA_bounds FF FRB (fb + 464) PNM.PSIZE AOP) as [O0 O1'].
      apply (PNBOA.bparser_keepS RSEGS PMA.AD (pa_vp_parser PMA.AD) M1 M3 (fb + 464) (fb + 96) s1); [exact O0| unfold PNM.PSIZE in *; clear - O1'; lia| | | exact PA1].
      + exact (PMKA.agA_obj L ar _ FF sp 28672 [] M1 M3 EKx PMKA.wapp_nil FRB (fb + 464) PNM.PSIZE AOP (fun i _ rr (X : In rr []) => match X with end)).
      + intros B m Hi. assert (HiL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hi).
        destruct (BRB1 _ HiL) as [B0 B1]. cbn [fst snd] in B0, B1.
        split; [exact B0|]. split; [clear - B1; lia|]. exact (PMKA.agA_blk L ar _ FF sp 28672 [] M1 M3 EKx PMKA.wapp_nil BRB1 B m HiL (fun i _ rr (X : In rr []) => match X with end)).
    - apply (PMKA.iss_keepA RSEGS PMA.AD L ar _ FF sp 28672 [] M1 M3 EKx (PMKA.wapp_nil) FRB BRB1 (fb + 96) str sm1); [| apply incl_appr; exact INCS| intros i _ rr []| intros c0 n0 p0 _ i _ rr []| exact IA1].
      apply (PNAPAR.aobj_fbB FF fb (fb + 96) 272 FOK); clear; lia.
    - apply (PMASK.base_keep L ar C LY _ FF sp 28672 [] M1 M3 EKx); [intros a _ rr []| exact BASE1].
    - apply (berr_keep _ FF sp 28672 [] M1 M3 ax1 EKx); [intros a _ rr []| exact ERR1]. }
  split; [exact STEP1|]. split; [exact AXL1|]. split; [exact CK1|]. split; [| exact EBB1].
  apply (L5C.u8_at_agree RSEGS M1 M3); [| exact R4a| exact R4b| exact SHC1].
  intros j Hj. apply FR3; [clear - Hj R4a R4b; lia|]. intros Wj. destruct (WP _ Wj) as [X|[X|[X|X]]]; [clear - X Hj SL160 SLO SHI SPT GSLO GSHI GSPT DF2; lia| clear - X Hj GFBIG DF1 DF2; lia| clear - X Hj; lia| clear - X Hj SLO SHI SPT GSLO GSHI GSPT DF2; lia].
Qed.

(* [comment removed for export] *)
Lemma sfacts_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  140735332487408 <= sp <= 140737488355328 /\ L5.writable RSEGS (mrestrict (ahid Aw1 model1) M1) (sp - 176) 176
  /\ ((sp - 176) + 176 <= fb + 464 \/ (fb + 464) + 416 <= (sp - 176))
  /\ ((sp - 176) + 176 <= F \/ F + 512 <= (sp - 176)) /\ ((sp - 176) + 176 <= fl \/ fl + 1 <= (sp - 176))
  /\ ((sp - 176) + 176 <= fb + 432 \/ (fb + 432) + 8 <= (sp - 176)).
Proof.
  intros CTX G LM.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 8) with 28672 in *.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FSIMG, F1, F2.
  pose proof LM as (BI & _).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *.
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 sp 28672 240 HH1 ASTK1 ltac:(clear; lia)) as (SL240 & SH240 & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK1 cr1 Aw1 M1 model1 sp 28672 176 HH1 ASTK1 ltac:(clear; lia)) as (_ & _ & SWR).
  split; [clear - SL240 SHI SPT SLO GSLO GSHI GSPT; lia|]. split; [exact SWR|].
  split; [right; clear - F1 F2 FSCEIL GSLO; lia|].
  split; [right; clear - GFCEIL GSLO; lia|]. split; [right; clear - GFLR GSLO; lia|].
  right; clear - F1 F2 FSCEIL GSLO; lia.
Qed.

End WithHeap.
End PNARVKB.
