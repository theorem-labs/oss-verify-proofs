(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Znumtheory FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep PmFrame PmParSpecs PmParKit PmCertKitG PgSrc PgV8.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj PnBrKit PnBrKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnBrKitS_u PnSRvK_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVKD.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.
Abbreviation mem := (word -> option byte).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD)).
Abbreviation BENT := PNBK.BENT.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KH := PNBKS.kh_S L HI LY HIok.
Let KL := PMKS.klayout_S L LY.
Abbreviation brel := (PNBK.brel RSEGS AD AN L HI 8).
Abbreviation pot := (PNR.pot_bparser L).

Lemma decW_edep a : PMK.inW (PNST.dec_W AD AN) a -> PNKP.edep AD AN a.
Proof. intros I. apply (PNBK2.berrW_edep AD AN). unfold PNST.berr_W. apply PMK.inW_app_r. exact I. Qed.

(* [comment removed for export] *)
Lemma brel_dec128 LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' vp c p : Z) K :
  PNRS.dec128_spec L HI -> K [] ->
  brel LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok AD L sp fb -> incl (PM.vs_own str) LBX ->
  PNM.b_tb s1 = PM.VLong c 42 p ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 p -> getr R1 (PMK.reg 11) = Z_to_bv 64 (p + 42) -> getr R1 (PMK.reg 12) = Z_to_bv 64 vp ->
  sp' <= sp -> sp - PMSP.pm_scr 8 <= sp' - PMSP.pm_scr 3 -> sp' mod 16 = 0 ->
  sp' <= vp -> vp + 16 <= sp -> vp mod 8 = 0 ->
  (forall (fx2 : FPState) R2 (M2 : mem) ptr,
      regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 ptr -> p <= ptr <= p + 42 ->
      brel LBX sp fb str E0 (BENT M2 model1 cr1 s1 sm1 (PNST.bax_add_dec ax1)) ->
      (forall a n, sp' <= a -> a + n <= fb + 784 -> L5C.agree_on M1 M2 a n) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 r' M2 model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (PNL.pn_dec128 AN) M1 model1) K.
Proof.
  intros DEC K0 BR FOK INCS ETB X1 RA1 X2 X3 X4 X10 X11 X12 S1 S2 S3 V1 V2 V3 KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). cbn [pa_frame AD PnLayoutS_u.ADDR_S] in F2.
  set (sc := PMSP.pm_scr 8) in *. change (PMSP.pm_scr 3) with 18432 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img RSEGS L KL) as (IMG0 & IMG1). pose proof (PMK.kl_errno RSEGS L KL) as (ERN0 & ERN1).
  rewrite (PMS.ly_img_lo L LY) in IMG0, ERN0. rewrite (PMS.ly_img_hi L LY) in IMG1, ERN1.
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  cbn [pa_off_p pa_off_is pa_off_v AD PnLayoutS_u.ADDR_S] in PA1, IA1, VIS1, VREF1.
  set (LB1 := PNM.bparser_own s1 ++ LBX) in *.
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 18432) by (apply (PMK.stk_call L M1 sp sc sp' 18432 STK); [exact S1| exact S2| lia| exact S3]).
  assert (BRG : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH); apply incl_refl).
  assert (NDL : NoDup (map fst LB1)) by exact (PMPK.heap_nodup L HI HIok LB1 cr1 M1 _ HH).
  pose proof (PNSRVK.tb_facts M1 fb s1 PA1) as TBF. rewrite ETB in TBF. destruct TBF as (B0 & U8 & U16 & Hn & Hc & He & Dp & U0 & D24).
  assert (TBIN : In (p, c) (PNM.bparser_own s1)).
  { unfold PNM.bparser_own, PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
  assert (TBIN1 : In (p, c) LB1) by (unfold LB1; apply in_or_app; left; exact TBIN).
  destruct (BRG p c TBIN1) as (P0 & PIMG & P4). unfold hl_ceil in P4. rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in PIMG.
  unfold PNRS.dec128_spec, PNR.dec128_spec in DEC.
  apply (DEC fx1 R1 M1 model1 K LB1 cr1 p vp sp' r' ax1 HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { rewrite L5K.rl12. exact X12. }
  { exists p, c. split; [exact TBIN1| lia]. }
  { apply (L5.defined_sub M1 p c); [exact Dp| lia| lia]. }
  { exact V1. } { lia. } { apply (L5.defined_sub M1 (sp - sc) sc); [exact SDEF| unfold sc, PMSP.pm_scr in *; lia| unfold sc, PMSP.pm_scr in *; lia]. } { exact V3. }
  { exact BASE1. } { exact ERR1. }
  intros fx2 R2 M2 ptr RP2 Y10 Hptr DEF2 ERR2 HP2 HH2.
  set (WE := (p, 42) :: (if PNST.bax_dec ax1 then [] else PNST.dec_W AD AN)) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> (p <= a < p + 42) \/ PMK.inW (PNST.dec_W AD AN) a).
  { intros a (r0 & Hin & Hr). unfold WE in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
    destruct (PNST.bax_dec ax1); [destruct Hin| right; exists r0; split; [exact Hin| exact Hr]]. }
  pose proof (PNBK.kh_EDI _ _ _ _ _ KH) as EDI. pose proof (PNBK.kh_BDI _ _ _ _ _ KH) as BDI. pose proof (PNBK.kh_EDB _ _ _ _ _ KH) as EDB.
  assert (WIMG : forall a, PMK.inW WE a -> (p <= a < p + 42) \/ (65536 <= a < 962560)).
  { intros a I. destruct (WCE a I) as [X|X]; [left; exact X| right]. pose proof (EDI a (decW_edep a X)) as Q. rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in Q. exact Q. }
  assert (EKc : PMK.ek L LB1 sp' 18432 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  (* [comment removed for export] *)
  assert (AGH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2. apply (PMFR.ag_hi RSEGS L KL LB1 sp' 18432 WE M1 M2 EKc STKc ltac:(lia) a n H1 H2). intros i Hi I. destruct (WIMG i I); lia. }
  assert (AGB : forall B m, In (B, m) LB1 -> (B + m <= p \/ p + 42 <= B) -> L5C.agree_on M1 M2 B m).
  { intros B m Hin HB i Hi. destruct (BRG B m Hin) as (Q0 & Q1 & Q4). rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in Q1. unfold hl_ceil in Q4.
    apply EKc. split; [lia|]. split; [left; exists (B, m); split; [exact Hin| cbn [fst snd]; lia]|].
    split; [unfold in_errno; lia|]. apply PMFR.outside_of_not_inW. intros I. destruct (WIMG i I); lia. }
  assert (DKH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M1 M2 a n) by (intros a n H1 H2; apply (PMPK.dkr_hpres_hi RSEGS L KL LB1 sp' 18432 WE M1 M2 a n HP2 STKc ltac:(lia) H1 H2)).
  assert (DKB : forall B m, In (B, m) LB1 -> PMPK.dkr M1 M2 B m) by (intros B m Hin; apply (PMPK.dkr_hpres_blk RSEGS L KL LB1 sp' 18432 WE M1 M2 B m HP2 Hin BRG); lia).
  (* [comment removed for export] *)
  assert (APT : forall B m, In (B, m) LB1 -> B <> p -> B + m <= p \/ p + c <= B).
  { intros B m Hin NE. exact (PMPK.blocks_apart_heap L HI HIok LB1 cr1 M1 _ _ _ _ _ HH Hin TBIN1 NE). }
  assert (QIN : In (PM.sr_qc (PNM.b_src s1), PM.CHUNK) LB1) by (unfold LB1, PNM.bparser_own, PM.src_own; cbn; left; reflexivity).
  assert (SIN : In (PNM.b_sb s1, PNM.BSZ * 2 ^ PNM.b_sk s1) LB1).
  { unfold LB1, PNM.bparser_own, PNM.brest_own, PNM.bvec_own. apply in_or_app. left. apply in_or_app. right. cbn. auto. }
  assert (NEq : PM.sr_qc (PNM.b_src s1) <> p).
  { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1)) (PNM.brest_own s1 ++ LBX) _ PM.CHUNK p c);
      [unfold LB1, PNM.bparser_own in NDL; rewrite <- app_assoc in NDL; exact NDL| unfold PM.src_own; cbn; auto|].
    apply in_or_app. left. unfold PNM.brest_own. rewrite ETB. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. cbn. auto. }
  assert (NEs : PNM.b_sb s1 <> p).
  { apply (PMPK.fst_neq_app (PM.src_own (PNM.b_src s1) ++ PNM.bvec_own (PNM.b_sb s1) (PNM.b_sk s1)) (PGV8.v8_own (PNM.b_bb s1) ++ PM.vs_own (PNM.b_nb s1) ++ PM.vs_own (PNM.b_tb s1) ++ LBX) _ (PNM.BSZ * 2 ^ PNM.b_sk s1) p c);
      [unfold LB1, PNM.bparser_own, PNM.brest_own in NDL; rewrite <- !app_assoc in NDL; rewrite <- !app_assoc; exact NDL
      | apply in_or_app; right; unfold PNM.bvec_own; cbn; auto
      | rewrite ETB; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; cbn; auto]. }
  assert (PA2 : bparser_at M2 (fb + 40) (fb + 472) s1).
  { unfold PNM.bparser_at, PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    destruct PA1 as (H0 & PDEF & _ & H8 & H9 & H10 & H12 & NI & SRC1 & H312 & _ & BB1 & NB1 & TB1 & SV1 & M01 & D01).
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
    split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H0]|].
    split; [apply (PMPK.defined_dkr M1 M2 (fb + 40) 416); [apply DKH; lia| exact PDEF]|]. split; [exact I|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H8]|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H9]|].
    split; [apply (L5C.u8_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H10]|].
    split; [apply (PMF.u32_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H12]|].
    split; [apply (PMF.nullis_at_agree RSEGS AD M1 M2); [lia|lia| apply AGH; lia| exact NI]|].
    split.
    { destruct (BRG _ _ QIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PMF.src_fields_at_agree RSEGS M1 M2); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AGH; lia| apply AGB; [exact QIN| destruct (APT _ _ QIN NEq); unfold PM.CHUNK in *; lia]| exact SRC1]. }
    split; [apply (PMF.u32_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia|exact H312]|]. split; [exact I|].
    split.
    { apply (PNMF.v8_at_keep RSEGS M1 M2); [lia|lia| apply AGH; lia| | exact BB1].
      intros b n c0 E. apply DKB. unfold LB1, PNM.bparser_own, PNM.brest_own. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite E. cbn. auto. }
    split.
    { apply (PNMF.vstr_at_keep RSEGS M1 M2 (fb + 40 + 344) (PNM.b_nb s1)); [lia|lia| destruct (PNM.b_nb s1); cbn [PNMF.vs_cells fst snd]; apply AGH; lia| apply DKH; lia| | exact NB1].
      intros c0 n p0 E. apply DKB. unfold LB1, PNM.bparser_own, PNM.brest_own. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite E. cbn. auto. }
    split.
    { rewrite ETB in TB1 |- *. apply (PNMF.vstr_at_keep RSEGS M1 M2 (fb + 40 + 368) (PM.VLong c 42 p)); [lia|lia| cbn [PNMF.vs_cells fst snd]; apply AGH; lia| apply DKH; lia| | exact TB1].
      intros c0 n p0 E. injection E as <- <- <-. apply DKB. exact TBIN1. }
    split.
    { destruct (BRG _ _ SIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PNMF.bvec_at_agree RSEGS M1 M2); [lia|lia|lia|lia| apply AGH; lia| apply AGB; [exact SIN| destruct (APT _ _ SIN NEs); unfold PNM.BSZ in *; lia]| exact SV1]. }
    split; [exact M01| exact D01]. }
  assert (INCS1 : incl (PM.vs_own str) LB1) by (unfold LB1; apply incl_appr; exact INCS).
  assert (IA2 : PM.iss_at RSEGS AD PMSP.T3 M2 (fb + 472) str sm1).
  { apply (PMF.iss_at_agree RSEGS AD M1 M2 (fb + 472) str sm1); [lia|lia| apply AGH; lia| | exact IA1].
    intros c0 n p0 E. assert (Hin : In (p0, c0) LB1) by (apply INCS1; rewrite E; cbn; auto).
    apply AGB; [exact Hin|].
    assert (NEx : p0 <> p).
    { intros ->. apply (PMPK.fst_neq_app (PNM.bparser_own s1) LBX p c p c0); [exact NDL| exact TBIN| apply INCS; rewrite E; cbn; auto| reflexivity]. }
    destruct (APT _ _ Hin NEx); lia. }
  assert (BASE2 : PMST.base_ok RSEGS AD M2).
  { apply (PMKP.base_ok_keep RSEGS AD L KL (PNBK.kh_SF _ _ _ _ _ KH) LB1 sp' 18432 WE M1 M2 EKc); [| | | | exact BASE1].
    all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; destruct (WCE a I) as [X|X];
      [assert (Hi : hl_img_lo L <= a < hl_img_hi L) by (apply BDI; unfold PNBK.bdom; tauto); rewrite (PMS.ly_img_lo L LY), (PMS.ly_img_hi L LY) in Hi; lia
      | apply (EDB a (decW_edep a X)); unfold PNBK.bdom; tauto]. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after RSEGS L KL LB1 M1 M2 sp sc sp' 18432 WE STK HP2); lia).
  assert (OWN1 : PNBK.own_ok L (PNM.bparser_own s1) LBX) by (apply (PNBK.own_ok_heap RSEGS AD AN L HI KH _ LBX cr1 M1 (m_vmmaps model1)); exact HH).
  apply (KONT fx2 R2 M2 ptr RP2).
  - rewrite <- L5K.rl10. exact Y10.
  - exact Hptr.
  - unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax].
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. cbn [pa_off_p pa_off_is pa_off_v AD PnLayoutS_u.ADDR_S].
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree RSEGS M1 M2); [apply AGH; lia|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2| exact GR1]. }
    split; [exact STEP|]. split; [apply (PNST.bax_le_trans _ _ _ AXL); apply PNST.bax_le_dec|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PNBK.ek_lbx_callee RSEGS AD AN L HI KH (PNM.bparser_own s1) LBX sp sc sp' 18432 _ WE M1 M1 M2 HP2 S2 S1 OWN1); [|exact STK|].
        + apply (PNBK.brange_hi_x RSEGS AD AN L HI KH (PNM.bparser_own s1) LBX cr1 M1 (m_vmmaps model1)). exact HH.
        + intros a I. destruct (WCE a I) as [X|X].
          * right. right. exists (p, c). split; [exact TBIN| cbn [fst snd]; lia].
          * right. left. unfold PNR.W_brun. rewrite !app_assoc. apply PMK.inW_app_r. unfold PNST.berr_W. apply PMK.inW_app_r. exact X.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LB1 sp sc sp' 18432 WE M1 M2 HP2); [unfold LB1; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split; [exact CK|]. split; [exact MB|]. split; [exact HH2|]. split; [exact STK2| exact MOK].
  - intros a n H1 H2. apply AGH; [exact H1| lia].
Qed.

End WithHeap.
End PNSRVKD.
