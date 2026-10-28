(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSRdSpanVP_u Bs0_code_37954_37958_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSVu8Grow_u PnSSrdV1_u PnSRdSpanV1_u PnSRdSpanV2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSRSV3.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).
Ltac kept_tac KS KP := intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); apply KP; exact Hy.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
#[local] Abbreviation own2 := PNSSV1.own2.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (V : PGV8.vowner) (OB : list (Z * Z)) (src0 : PM.srcst) (x0 : PGV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGV8.vw_os V).
#[local] Abbreviation ois := (PGV8.vw_ois V).
#[local] Abbreviation ov := (PGV8.vw_ov V).
#[local] Abbreviation lo := (PGV8.vw_lo V).
#[local] Abbreviation hi := (PGV8.vw_hi V).
Hypothesis VOK : PGV8.vowner_ok RSEGS AD L HI V.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis SPLO : S <= lo.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis ROOM0 : PGV8.v8_room x0 (PM.unread src0 sm0).
Hypothesis FBS : PGS.fill_buffer_specG RSEGS AD L HI.
Hypothesis SRDS : PNRS.srd_read_v_spec L HI.
#[local] Abbreviation W0 := (PNSSV1.W0 V).
#[local] Abbreviation lay := (PNSSV1.lay L HI V VOK).
#[local] Abbreviation tsrc := (PNSSV1.tsrc L HI V OB VOK).
#[local] Abbreviation inW_W0' := (PNSSV1.inW_W0' L HI V VOK).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : PGV8.v8) (g' : Z)
                         (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  PMSP.consumed src0 src' sm0 sm' = n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PGV8.v8_own x' ++ OB) ptr n) ->
  L5.defined M' ptr n ->
  (n = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at V M' src' x' g' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 6) (PGS.W_srcfG os ois ++ [(ov, 24)]) M0 M' ->
  PMSP.credit_keep cr0 cr' (PGV8.pot_v8 L x0 g0) (PGV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.


#[local] Abbreviation own2 := PNSSV1.own2.
#[local] Abbreviation base_keep := (PNSRSV1.base_keep L HI LY LBX S V VOK SPLO).
#[local] Abbreviation st_piece := (PNSRSV1.st_piece L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation src_keep_P := (PNSRSV1.src_keep_P L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation v8_keep_P := (PNSRSV1.v8_keep_P L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation saves4 := (PNSRSV1.saves4 R0 S).
#[local] Abbreviation kept_rs := (PNSRSV1.kept_rs R0).
#[local] Abbreviation memrel := (PNSRSV1.memrel L M0 LBX S V).
#[local] Abbreviation st_ok := (PNSRSV1.st_ok L HI R0 M0 model0 LBX cr0 S V OB x0 g0 str).
#[local] Abbreviation bregs := (PNSRSV1.bregs R0 S len V).
#[local] Abbreviation finish_rs := (PNSRSV1.finish_rs L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation call_fill := (PNSRSV1.call_fill L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PNSRSV1.call_srd L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation unread_nn := (PNSRSV1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation fast := (PNSRSV2.fast L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation slow := (PNSRSV2.slow L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_fill (fx : FPState) R M model src x g sm sm1 cr (c : Z) :
  bregs R -> getr R (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> 1 <= len ->
  st_ok M model src x g sm1 cr -> PMSP.src_step src0 src sm0 sm -> PM.unread src sm = PM.unread src0 sm0 ->
  PGV8.v8_room x (PM.unread src0 sm0) ->
  PMSP.src_step src src sm sm1 -> PM.sr_rem src = 0 -> PM.sm_g sm1 = PM.sm_g sm + c ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x389f8 M model) K.
Proof using All.
  intros BR0 A10 Hc Hl SO STEP CONS0 RMx STEP1 RZ G1. pose proof BR0 as (A2 & A8 & A9 & A18 & KP).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & DJ1 & DJ2 & DJ3). pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (tsrc M src x g PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & Q1 & Q2 & Q3 & Q4 & DC & _ & _) & _ & PD & VS & TB).
  assert (INC : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply in_or_app; left; unfold PM.src_own; left; reflexivity).
  destruct (BR _ _ INC) as (C0' & _ & C4').
  assert (W16 : L5.writable RSEGS M (os + 280) 16) by (apply (L5C.writable_of_defined RSEGS M _ 16); [apply (L5.defined_sub M os 296 _ 16 PD); lia| lia| destruct STOP; lia]).
  unfold PM.CHUNK in Hc.
  LeanFeed.pfeed PP (PNSRVP.rvB_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len
       | 56%nat => PM.sr_qc src | 53%nat => c | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & EX).
  assert (CC : L5.u64_at RSEGS M1 (os + 288) c /\ L5.u64_at RSEGS M1 (os + 280) (PM.sr_qc src)).
  { destruct EX as [(_ & _ & _ & _ & _ & C1 & C2) | (_ & _ & _ & _ & _ & C1 & C2)]; split; assumption. }
  destruct CC as (C1 & C2).
  set (P := fun a => os + 280 <= a < os + 280 + 16).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ1; [lia| unfold P; lia]. }
  set (src2 := PM.SRC (PM.sr_qc src) (PM.sr_qc src) c).
  assert (SO2f : hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M1 (m_vmmaps model) -> st_ok M1 model src2 x g sm1 cr).
  { intros HH1. apply (st_piece M M1 model src src2 x x g sm1 cr P SO MG1);
      [intros a Ha N; apply FRZ1; [exact Ha| exact N] | intros a Pa; left; unfold P in Pa; lia | | reflexivity | | exact TB | reflexivity | reflexivity | exact HH1].
    - unfold src2, PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F1]|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F2]|].
      split; [apply (L5.defined_grows M M1 _ _ MG1); exact F3|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F4]|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F5]|].
      split; [exact C2|]. split; [exact C1|].
      split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact Q4|].
      split; [apply (L5.defined_grows M M1 _ _ MG1); exact DC|]. split; exact I.
    - apply (v8_keep_P M M1 model src x g sm1 cr P SO MG1); [intros a Ha N; apply FRZ1; [exact Ha| exact N]|].
      intros a Pa. unfold P in Pa. lia. }
  assert (STEP2 : PMSP.src_step src0 src2 sm0 sm1).
  { apply (PNSRSV2.src_step_trans _ _ _ _ _ _ STEP). destruct STEP1 as (_ & E2 & L2 & S2 & U2).
    unfold PMSP.src_step, PM.unread in *. cbn [src2 PM.sr_qc PM.sr_rem].
    split; [reflexivity|]. split; [exact E2|]. split; [lia|]. split; [exact S2| rewrite RZ in *; lia]. }
  assert (CONS2 : PM.unread src2 sm1 = PM.unread src0 sm0).
  { destruct STEP1 as (_ & E2 & _). unfold PM.unread in *. cbn [src2 PM.sr_rem]. rewrite RZ in CONS0. lia. }
  assert (RM2 : PGV8.v8_room x (PM.unread src2 sm1)) by (rewrite CONS2; exact RMx).
  assert (SPC : forall pc1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x389f8) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
            (st_ok M1 model src2 x g sm1 cr -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x389f8 M model) K).
  { intros pc1 MS NEXT. unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M model fx fx1 R 0x389f8 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG1).
    - intros a Ha N. apply FRZ1; [exact Ha| exact N].
    - intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) M S 24576 a STK). lia.
    - intros a. unfold P. apply PMK.rng_dec.
    - intros HH1. apply NEXT. exact (SO2f HH1). }
  destruct EX as [(MS1 & KS1 & E10 & E11 & C0 & _ & _) | (MS1 & KS1 & E10 & E11 & C0 & _ & _)]; apply (SPC _ MS1); intros SO2.
  - (* [comment removed for export] *)
    apply (slow fx1 R1 M1 model src2 x g sm1 cr); try assumption.
    unfold PNSRSV1.bregs.
    split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
    split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
    kept_tac KS1 KP.
  - (* [comment removed for export] *)
    apply (fast fx1 R1 M1 model src2 x g sm1 cr); try assumption.
    + unfold PNSRSV1.bregs.
      split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
      kept_tac KS1 KP.
    + cbn [src2 PM.sr_rem]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_rs (fx : FPState) :
  hi_heap HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) cr0 M0 (m_vmmaps model0) -> PMSP.model_ok model0 -> L5C.stk (hl_sptop L) M0 S 24576 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 len -> getr R0 (reg 12) = Z_to_bv 64 ov ->
  PGV8.vw_at V M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD T3 M0 ois str sm0 -> PMST.base_ok RSEGS AD M0 ->
  PMSP.credit_le (PGV8.pot_v8 L x0 g0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x38984 M0 model0) K.
Proof using All.
  intros HH MOK STK A10 A11 A12 PA IA BASE CRL.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & DJ1 & DJ2 & DJ3).
  pose proof (L5C.stk_writable RSEGS _ M0 S 24576 STK) as WR.
  assert (BR : PMFR.brange L (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_refl).
  destruct (tsrc M0 src0 x0 g0 PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & Q1 & Q2 & Q3 & Q4 & DC & _ & _) & _ & PD & VS0 & TB0).
  assert (INL : incl (OB ++ LBX) (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX)) by (intros y Hy; rewrite own2; apply in_or_app; right; exact Hy).
  change PM.CHUNK with 16384 in F5, Q3.
  assert (RM : PM.sr_rem src0 <= 16384) by lia.
  LeanFeed.pfeed PP (PNSRVP.rvA_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len
       | 36%nat => PM.sr_rem src0 | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
  set (P := fun a => S - 32 <= a < S - 32 + 32).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= S - 32 \/ S <= a) -> L5C.agree_on M0 M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ; lia. }
  assert (AGH : forall B m, In (B, m) (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) -> L5C.agree_on M0 M1 B m).
  { intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4'). apply AG; lia. }
  assert (EKw : forall scr, 32 <= scr <= 24576 -> PMK.ek L (OB ++ LBX) S scr W0 M0 M1).
  { intros scr Hs. apply (PMK.ek_piece_in RSEGS L KL (OB ++ LBX) S scr W0 M0 M1 P); [intros a Ha N; apply FRZ; [exact Ha| exact N]| | |].
    - apply (PMK.stk_call L M0 S 24576 S scr STK); [lia|lia|lia| exact A16].
    - exact (PMFR.brange_hi L (OB ++ LBX) (PMFR.brange_incl L (OB ++ LBX) _ BR INL)).
    - intros a Pa. left. unfold P in Pa. lia. }
  assert (EKn : PMK.ek L LBX S 24576 W0 M0 M1).
  { apply (PMK.ek_weaken L LBX (OB ++ LBX) S 24576 S 24576 W0 W0 M0 M1 (EKw 24576 ltac:(lia))); [intros y Hy; apply in_or_app; right; exact Hy| intros y Hy; exact Hy| intros a Ha; exact Ha]. }
  assert (SPC : forall pc1, msteps RSEGS (@mkst fx R0 (Z_to_bv 64 0x38984) M0 (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
            (hi_heap HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) cr0 M1 (m_vmmaps model0) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model0) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x38984 M0 model0) K).
  { intros pc1 MS NEXT. unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) cr0 M0 model0 fx fx1 R0 0x38984 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
    - intros a Ha N. apply FRZ; [exact Ha| exact N].
    - intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) M0 S 24576 a STK). lia.
    - intros a. unfold P. apply PMK.rng_dec.
    - exact NEXT. }
  assert (SO1 : forall (C1 : L5.u64_at RSEGS M1 (S - 32) (bv_unsigned (getr R0 (reg 18)))) (C2 : L5.u64_at RSEGS M1 (S - 24) (bv_unsigned (getr R0 (reg 9))))
                       (C3 : L5.u64_at RSEGS M1 (S - 16) (bv_unsigned (getr R0 (reg 8)))) (C4 : L5.u64_at RSEGS M1 (S - 8) (bv_unsigned (getr R0 (reg 1)))),
                hi_heap HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) cr0 M1 (m_vmmaps model0) -> st_ok M1 model0 src0 x0 g0 sm0 cr0).
  { intros C1 C2 C3 C4 HH1.
    assert (INC : In (PM.sr_qc src0, PM.CHUNK) (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX)) by (apply in_or_app; left; unfold PM.src_own; left; reflexivity).
    destruct (BR _ _ INC) as (Z0 & _ & Z4). unfold hl_ceil in Z4.
    split; [split; [|split]|].
    - exact EKn.
    - apply PMK.dk_grows. exact MG.
    - exact (PMK.stk_grows L M0 M1 S 24576 MG STK).
    - split; [unfold PNSRSV1.saves4; repeat split; assumption|].
      split.
      { apply (PNSSV1.vw_xfer L HI HIok LBX S V OB VOK SPLO M0 M1 src0 src0 x0 x0 g0 g0 cr0 (m_vmmaps model0) 24576 S 32 [] PA HH STK); [lia|lia|lia| | constructor| | reflexivity| | exact TB0].
        - apply (PMK.hpres_of L (OB ++ LBX) S 32 _ M0 M1).
          + rewrite app_nil_r. exact (EKw 32 ltac:(lia)).
          + apply (L5.defined_grows M0 M1 _ _ MG). intros i Hi. replace (S - 32 + i) with (S - 24576 + (24576 - 32 + i)) by lia. apply SDEF. lia.
          + apply PMK.dk_grows. exact MG.
        - apply (PMF.src_fields_at_agree RSEGS M0 M1 os ois (ois + 16) src0); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AG; lia| exact (AGH _ _ INC)|].
          unfold PM.src_fields_at. repeat split; assumption.
        - apply (PNSVG.v8_at_agree M0 M1 ov x0 P VS0 MG ltac:(lia) ltac:(lia)); [intros a Ha N; apply FRZ; [exact Ha| exact N]|].
          intros a Ha Pa. unfold P in Pa. lia. }
      split.
      { apply (PMF.iss_at_agree RSEGS AD M0 M1 ois str sm0); [lia|lia| apply AG; lia| |exact IA].
        intros c n p E. apply AGH. apply PNSSV1.in4. apply INCS. rewrite E. left. reflexivity. }
      split; [exact (base_keep M0 M1 EKn STK BASE)|].
      split; [exact TB0|]. split; [exact HH1|]. split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|].
      split; [exact CRL| unfold PMSP.credit_keep; lia]. }
  assert (STEP0 : PMSP.src_step src0 src0 sm0 sm0) by (unfold PMSP.src_step; split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]).
  destruct EX as [(MS & KS & E10 & E11 & C0 & C1 & C2 & C3 & C4) | [(MS & KS & E2 & E8 & E9 & E11 & E18 & C0 & C0' & C0'' & C1 & C2 & C3 & C4)
                 | [(MS & KS & E2 & E8 & E9 & E11 & E18 & C0 & C0' & C0'' & C1 & C2 & C3 & C4) | (MS & KS & E2 & E8 & E9 & E11 & E18 & C0 & C0' & C1 & C2 & C3 & C4)]]];
    apply (SPC _ MS); intros HH1; pose proof (SO1 C1 C2 C3 C4 HH1) as SOk.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0 by lia. assert (L0 : len = 0) by lia.
    apply (finish_rs fx1 R1 M1 model0 src0 x0 g0 sm0 cr0 0 0); try assumption.
    all: try (rewrite (KS 2%nat) by PMK.inl; exact Rsp0).
    all: try (rewrite (KS _) by PMK.inl; symmetry; apply Z_to_bv_bv_unsigned).
    + intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); reflexivity.
    + lia.
    + lia.
    + left. split; reflexivity.
    + intros i Hi. lia.
    + intros _. exact ROOM0.
    + unfold PMSP.consumed. lia.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0', C0'' by lia.
    apply (fast fx1 R1 M1 model0 src0 x0 g0 sm0 cr0); try assumption.
    + unfold PNSRSV1.bregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|].
      intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); reflexivity.
    + lia.
    + reflexivity.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0', C0'' by lia.
    apply (slow fx1 R1 M1 model0 src0 x0 g0 sm0 cr0); try assumption.
    + unfold PNSRSV1.bregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|].
      intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); reflexivity.
    + reflexivity.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0, C0' by lia. assert (RZ : PM.sr_rem src0 = 0) by lia.
    pose proof SOk as ((EK1 & DK1 & STK1) & SV1 & PA1 & IA1 & BASE1 & TBOK1 & HH1' & MOK1 & MB1 & CRL1 & CRK1).
    pose proof (L5C.stk_writable RSEGS _ M1 S 24576 STK1) as WR1.
    assert (F5' : L5.u64_at RSEGS M1 (os + 272) 16384) by (apply (L5C.u64_at_agree RSEGS M0 M1); [apply AG; lia| lia| lia| exact F5]).
    assert (F4' : L5.u64_at RSEGS M1 (os + 264) (PM.sr_qc src0)) by (apply (L5C.u64_at_agree RSEGS M0 M1); [apply AG; lia| lia| lia| exact F4]).
    assert (Hq : 0 <= PM.sr_qc src0 < 2 ^ 64).
    { assert (INC : In (PM.sr_qc src0, PM.CHUNK) (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
      destruct (BR _ _ INC) as (Z0 & _ & Z4). unfold PM.CHUNK in Z4. destruct STOP. lia. }
    LeanFeed.pfeed PP (PNSRVP.rvR0_conc fx1 R1 M1 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len
         | 56%nat => PM.sr_qc src0 | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx2 & R2 & M2 & MG2 & FRw & _ & [(MS2 & KS2 & E12 & D0) | (MS2 & KS2 & E1 & E10 & E11' & E12 & D0)]);
      (assert (EM : M2 = M1) by (apply functional_extensionality; exact FRw)); subst M2;
      unfold PMSP.cfg; apply (PMK.spiece_ro RSEGS model0 fx1 fx2 R1 0x389e4 R2 _ M1 K Mh Ml MS2).
    + (* [comment removed for export] *)
      apply (slow fx2 R2 M1 model0 src0 x0 g0 sm0 cr0); try assumption.
      * unfold PNSRSV1.bregs.
        split; [rewrite (KS2 2%nat) by PMK.inl; exact E2|]. split; [rewrite (KS2 8%nat) by PMK.inl; exact E8|].
        split; [rewrite (KS2 9%nat) by PMK.inl; exact E9|]. split; [rewrite (KS2 18%nat) by PMK.inl; exact E18|].
        intros y Hy. rewrite (KS2 y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
        rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). reflexivity.
      * reflexivity.
    + (* [comment removed for export] *)
      assert (BRG : bregs R2).
      { unfold PNSRSV1.bregs.
        split; [rewrite (KS2 2%nat) by PMK.inl; exact E2|]. split; [rewrite (KS2 8%nat) by PMK.inl; exact E8|].
        split; [rewrite (KS2 9%nat) by PMK.inl; exact E9|]. split; [rewrite (KS2 18%nat) by PMK.inl; exact E18|].
        intros y Hy. rewrite (KS2 y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
        rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). reflexivity. }
      pose proof BRG as (B2 & B8 & B9 & B18 & BKP).
      apply (call_fill fx2 R2 M1 model0 src0 x0 g0 sm0 cr0 231928 E1 ltac:(split; [lia| reflexivity]) B2 BKP E10 E11' E12 SOk).
      intros fx3 R3 M3 sm3 c RP3 Y10 Hc G3 ST0 ST2 STEP3 SO3.
      apply (after_fill fx3 R3 M3 model0 src0 x0 g0 sm0 sm3 cr0 c); try assumption.
      * unfold PNSRSV1.bregs.
        split; [rewrite (PMK.cs_of_preserved R2 R3 2%nat RP3) by PMK.inl; exact B2|].
        split; [rewrite (PMK.cs_of_preserved R2 R3 8%nat RP3) by PMK.inl; exact B8|].
        split; [rewrite (PMK.cs_of_preserved R2 R3 9%nat RP3) by PMK.inl; exact B9|].
        split; [rewrite (PMK.cs_of_preserved R2 R3 18%nat RP3) by PMK.inl; exact B18|].
        intros y Hy. rewrite (PMK.cs_of_preserved R2 R3 y RP3) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply BKP. exact Hy.
      * reflexivity.
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem read_span_v_okG : PGS.fill_buffer_specG RSEGS AD L HI -> PNRS.srd_read_v_spec L HI -> PNRS.read_span_v_spec L HI.
Proof.
  intros FBS SRDS. unfold PNRS.read_span_v_spec, PNR.read_span_v_spec, PGV8.read_span_v_specG. cbn [PNL.pn_read_span_v PnLayoutS_u.NADDR_S].
  intros V VOK fx R M model K OB LBX cr sp r len src x g str sm HH MOK K0 EN SPLO A10 A11 A12 Hlen PA IA BASE INCS UN ROOM CRL KONT.
  unfold PMSP.entry in EN. destruct EN as (E1 & RA & E2 & E3 & E4 & STK).
  change (PMSP.pm_scr 6) with 24576 in STK.
  apply (entry_rs R M model K LBX cr sp r len V OB src x g str sm VOK E1 RA E2 E3 E4 K0 SPLO Hlen INCS UN ROOM FBS SRDS KONT fx HH MOK STK A10 A11 A12 PA IA BASE CRL).
Qed.

End WithHeap.
End PNSRSV3.
