From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac CmpCut CmpCut0 CmpCutSM CmpCutSmA BzCFactsSmA BzCFactsSd U0_cmp_sdBV U0_sd4P U0_cmp_smV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpHmKit CmpSmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import ListNotations. Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma smq_u8 : forall W W' (m m' m'' : word -> option byte) A bs,
  u8arr s0segs m A bs -> munch W m m' -> wmono s0segs m m' -> munch W' m' m'' -> wmono s0segs m' m'' ->
  disjoint_from W A (Z.of_nat (length bs)) -> disjoint_from W' A (Z.of_nat (length bs)) -> u8arr s0segs m'' A bs.
Proof.
  intros W W' m m' m'' A bs H M1 V1 M2 V2 D1 D2.
  eapply u8arr_transport; [eapply u8arr_transport; [exact H| exact M1| exact V1| exact D1]| exact M2| exact V2| exact D2].
Qed.

Lemma smq_u32 : forall W W' (m m' m'' : word -> option byte) A ws,
  u32arr s0segs m A ws -> munch W m m' -> wmono s0segs m m' -> munch W' m' m'' -> wmono s0segs m' m'' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> disjoint_from W' A (4 * Z.of_nat (length ws)) -> u32arr s0segs m'' A ws.
Proof.
  intros W W' m m' m'' A ws H M1 V1 M2 V2 D1 D2.
  eapply u32arr_transport; [eapply u32arr_transport; [exact H| exact M1| exact V1| exact D1]| exact M2| exact V2| exact D2].
Qed.

Lemma smq_rw : forall W W' (m m' m'' : word -> option byte) A cs,
  rw_cells s0segs m A cs -> munch W m m' -> wmono s0segs m m' -> munch W' m' m'' -> wmono s0segs m' m'' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> disjoint_from W' A (Z.of_nat (cells_size cs)) -> rw_cells s0segs m'' A cs.
Proof.
  intros W W' m m' m'' A cs H M1 V1 M2 V2 D1 D2.
  eapply rw_cells_transport; [eapply rw_cells_transport; [exact H| exact M1| exact V1| exact D1]| exact M2| exact V2| exact D2].
Qed.

Ltac smq_len :=
  try unfold FTAB_WORDS, ESTATE_SIZE;
  rewrite ?ovb_length, ?ovw_length, ?zb8_length, ?zw32_length by lia;
  cbn [cells_size csize length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
Ltac smq_dj := smq_len; unfold sdWP, sdWe, sdWd; cbv [disjoint_from fst snd app]; repeat split; try exact I; lia.

Lemma U0_sm_post : sm_post_ok.
Proof.
  unfold sm_post_ok.
  intros cx g e lo usp sv m m1 m2 m3 m0' J0 Jm J3 Jx J44 Jf w16 w896 w912 w936 w1024 H' i16' v976 v984 v1024
         x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra.
  cbv zeta.
  intros Gmtf Gbs Gzb EM AM CM MI ST LOU CLO AL CX SEP IMG BOK NB ROOM SFA SDF
         EM1 AM1 CM1 MI1 ST1 MU1 WM1 L0 Lm L3 Lx L44 Lf FJ0 SL16 FJm SL816 FJ3 SL888 FJx FJ44 FJf SAV
         MA RO2 ST2 MU2 WM2 Li16 BEOK ME SL976 SL1024 ROK.
  clear EM AM CM MI ST AL IMG BOK NB ROOM SFA SDF CM1 MI1 ST1 SL888 FJ44 BEOK Gmtf Gbs Gzb.
  pose proof CX as CXL; unfold cctx_ok in CXL; cbv zeta in CXL.
  cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LJ & _).
  pose proof SEP as SPX; unfold cctx_sep, apart in SPX; cbv zeta in SPX.
  cps_destruct SPX as (AEA1 & AEA2 & AEF & _ & _ & AA12 & AA1F & _ & _ & AA2F & _).
  unfold ESTATE_SIZE, FTAB_WORDS in *.
  cps_destruct MA as (EH1c & EH2c & AR2c & HC & I16 & MI2 & _ & _).
  cps_destruct ME as (EH1 & EH2 & AR2 & AR1 & LEN & COD & SL1032 & MI3 & MU3 & WM3).
  cps_destruct RO2 as (AR1b & INU2 & SLM2 & SEL2 & LEN2 & COD2 & _).
  cps_destruct EM1 as (EH1a & INU1 & UNS1 & EH2a & MTF1 & SEL1 & SLM1 & LEN1 & COD1 & RFQ1 & LNP1).
  cps_destruct AM1 as (AR1a & AR2a & FTB1).
  clear EH1c EH2c AR2c MI2 AR1b LEN2 COD2 EH1a EH2a SEL1 SLM1 LEN1 COD1 AR1a AR2a INU1.
  assert (STa : stk s0segs m3 lo (usp - 1200)).
  { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. smq_dj. }
  unfold sd_hc in HC.
  apply (proj1 (rw_cells_app2 s0segs m2 _ [_; _; _; _; _; _; _; _; _; _; _] _)) in HC. destruct HC as [HCa HCb].
  apply (proj1 (rw_cells_app2 s0segs m2 _ [_; _] _)) in HCb. destruct HCb as [_ HCd].
  apply (proj1 (rw_cells_app2 s0segs m2 _ [_; _; _; _] _)) in HCd. destruct HCd as [HCe _].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HCa, HCe.
  assert (HCa3 : rw_cells s0segs m3 (usp - 1200 + 888) [C8 (h888 H'); C8 (h896 H'); C8 (h904 H'); C8 (h912 H'); C8 (h920 H'); C8 (h928 H');
                                                      C8 (h936 H'); C8 (h944 H'); C8 (h952 H'); C8 (h960 H'); C8 (h968 H')]).
  { eapply rw_cells_transport; [exact HCa| exact MU3| exact WM3|]. smq_dj. }
  assert (HCe3 : rw_cells s0segs m3 (usp - 1200 + 888 + 88 + 16) [C8 (h992 H'); C8 (h1000 H'); C8 (h1008 H'); C8 (h1016 H')]).
  { eapply rw_cells_transport; [exact HCe| exact MU3| exact WM3|]. smq_dj. }
  assert (I163 : u8arr s0segs m3 (usp - 1200 + 1044) i16').
  { eapply u8arr_transport; [exact I16| exact MU3| exact WM3|]. smq_dj. }
  clear HCa HCe I16.
  assert (FJ03 : u8arr s0segs m3 (usp - 1200) J0) by (eapply smq_u8; [exact FJ0| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (SL163 : rw_cells s0segs m3 (usp - 1200 + 16) [C8 w16]) by (eapply smq_rw; [exact SL16| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (FJm3 : u8arr s0segs m3 (usp - 1200 + 24) Jm) by (eapply smq_u8; [exact FJm| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (SL8163 : rw_cells s0segs m3 (usp - 1200 + 816) [C8 (Z_to_bv 64 (c_E cx + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))])
    by (eapply smq_rw; [exact SL816| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (FJ33 : u8arr s0segs m3 (usp - 1200 + 832) J3) by (eapply smq_u8; [exact FJ3| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (FJx3 : u8arr s0segs m3 (usp - 1200 + 1040) Jx) by (eapply smq_u8; [exact FJx| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (FJf3 : u8arr s0segs m3 (usp - 1200 + 1060) Jf) by (eapply smq_u8; [exact FJf| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (SAV3 : rw_cells s0segs m3 (usp - 1200 + 1096) [C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra])
    by (eapply smq_rw; [exact SAV| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  clear FJ0 SL16 FJm SL816 FJ3 FJx FJf SAV.
  assert (INU3 := INU2). eapply u8arr_transport in INU3; [| exact MU3| exact WM3| smq_dj].
  assert (SEL3 := SEL2). eapply u8arr_transport in SEL3; [| exact MU3| exact WM3| smq_dj].
  assert (SLM3 := SLM2). eapply u8arr_transport in SLM3; [| exact MU3| exact WM3| smq_dj].
  assert (UNS3 : u8arr s0segs m3 (c_E cx + 384) (ovb (e_unseqToSeq e) (jseg (c_J cx) 384 256) 256))
    by (eapply smq_u8; [exact UNS1| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (MTF3 : u32arr s0segs m3 (c_E cx + 672) (ovw (e_mtfFreq e) (jseg (c_J cx) 672 1032) 258))
    by (eapply smq_u32; [exact MTF1| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj]).
  assert (RFQ3 := RFQ1). eapply smq_u32 in RFQ3; [| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj].
  assert (LNP3 := LNP1). eapply smq_u32 in LNP3; [| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj].
  assert (FTB3 := FTB1). eapply smq_u32 in FTB3; [| exact MU2| exact WM2| exact MU3| exact WM3| smq_dj| smq_dj].
  clear INU2 SEL2 SLM2 UNS1 MTF1 RFQ1 LNP1 FTB1.
  split.
  { eapply munch_trans; [exact MU1|]. eapply munch_trans.
    - eapply munch_weaken; [| exact MU2]. unfold sub_fp, sdWP. intros x Ho. cbv [outside app fst snd] in Ho |- *. lia.
    - eapply munch_weaken; [| exact MU3]. unfold sub_fp, sdWe, sdWd. intros x Ho. cbv [outside app fst snd] in Ho |- *. lia. }
  split; [exact (wmono_trans s0segs _ _ _ WM1 (wmono_trans s0segs _ _ _ WM2 WM3))|].
  split; [exact MI3|].
  split.
  { pose proof STa as STK.
    pose proof (stk_of_u8arr s0segs _ _ _ FJ03) as K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ SL163) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_u8arr s0segs _ _ _ FJm3) as K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ SL8163) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_u8arr s0segs _ _ _ FJ33) as K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ HCa3) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ SL976) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ HCe3) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ SL1024) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ SL1032) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    pose proof (stk_of_u8arr s0segs _ _ _ FJx3) as K. stk_add STK K.
    pose proof (stk_of_u8arr s0segs _ _ _ I163) as K. stk_add STK K.
    pose proof (stk_of_u8arr s0segs _ _ _ FJf3) as K. stk_add STK K.
    pose proof (stk_of_rw_cells s0segs _ _ _ SAV3) as K. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K. stk_add STK K.
    lazymatch type of STK with stk _ _ _ ?hi => replace hi with usp in STK by lia end. exact STK. }
  split.
  { apply emem_intro; [exact EH1| exact INU3| exact UNS3| exact EH2| exact MTF3| exact SEL3| exact SLM3| exact LEN| exact COD| exact RFQ3| exact LNP3]. }
  split; [exact AR1|]. split; [exact AR2|]. split; [exact FTB3|]. split; [exact ROK|]. exact SAV3.
Qed.

End ACeilS1.
