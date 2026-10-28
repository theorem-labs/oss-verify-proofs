(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnARdSpanP_b Ba0PgRdSpan1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b Ba0PgSrd1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRSA2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSRSA1.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tx0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGSSRA1.os T).   (* [comment removed for export] *)
#[local] Abbreviation ois := (PGSSRA1.ois T).   (* [comment removed for export] *)
#[local] Abbreviation tb := (PGSSRA1.tb T).   (* [comment removed for export] *)
#[local] Abbreviation lo := (PGSSRA1.lo T).   (* [comment removed for export] *)
#[local] Abbreviation hi := (PGSSRA1.hi T).   (* [comment removed for export] *)
Hypothesis TOK : PGSA.towner_ok RSEGS AD L ar HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 6 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 24576) 3072.
Hypothesis FBS : PGSA.fill_buffer_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis SRDS : PGSA.srd_read_specG RSEGS AD L ar HI PNRA.FCB (pa_srd_read AD).
#[local] Abbreviation W0 := (PGSSRA1.W0 T).   (* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (tx' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PM.vs_own tx' ++ OB) ptr n \/ (tb + 1 <= ptr /\ ptr + n <= tb + 24)) ->
  L5.defined M' ptr n -> PMSPA.accA M' ptr n ->
  PGS.tw_at T M' src' tx' tg' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar tx0 tg0) (pot L ar tx' tg') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PM.vs_own tx' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGSSRA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGSSRA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGSSRA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation frame_app := (PGSSRA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGSSRA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGSSRA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGSSRA1.stw_ok L ar C HI LY HIok T TOK).
#[local] Abbreviation own2 := PGSSRA1.own2.
#[local] Abbreviation unread_nn := (PGSRSA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation centry := (PGSRSA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation U := (PGSRSA1.U R0).
#[local] Abbreviation saves9 := (PGSRSA1.saves9 R0 S).
#[local] Abbreviation kept_rs := (PGSRSA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSRSA1.memrel L ar M0 LBX FF S T).
#[local] Abbreviation fields_eq := (PGSRSA1.fields_eq).
#[local] Abbreviation st_ok := (PGSRSA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S T OB tx0 tg0 str).
#[local] Abbreviation bregs := (PGSRSA1.bregs R0 S len T).
#[local] Abbreviation finish_rs := (PGSRSA1.finish_rs L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PGSRSA1.call_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation vpack := (PGSRSA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PGSSRA1.outside_W0 L ar HI T TOK).

Lemma src_step_trans a b c sa sb sc : PMSP.src_step a b sa sb -> PMSP.src_step b c sb sc -> PMSP.src_step a c sa sc.
Proof.
  unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.

(* [comment removed for export] *)
Lemma src_eta (src : PM.srcst) : PM.SRC (PM.sr_qc src) (PM.sr_de src) (PM.sr_rem src) = src.
Proof. destruct src; reflexivity. Qed.

(* [comment removed for export] *)
Lemma fast (fx : FPState) R M model src tx tg sm cr LK Aw :
  bregs R -> getr R (reg 12) = Z_to_bv 64 (PM.sr_rem src) -> 1 <= len <= PM.sr_rem src ->
  st_ok M model src tx tg sm cr LK Aw -> fields_eq src tx tg -> PMSP.src_step src0 src sm0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4ee0 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP) A12 Hl SO FE STEP.
  pose proof (vpack M model src tx tg sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (tsrc M src tx tg PA) as (SRC & PNI & PD & VS & _).
  pose proof SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
  set (qc := PM.sr_qc src) in *. set (de := PM.sr_de src) in *. set (rem := PM.sr_rem src) in *.
  unfold PM.CHUNK in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  assert (QIN : In (qc, 16384) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (WB _ QIN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMARSPP.arpF_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => rem | 35%nat => de | 36%nat => os | 37%nat => tb | 38%nat => len
       | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
       | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E13 & E18 & E19 & E20 & E21 & E22 & E23 & C288 & C280).
  unfold PMSPA.cfg, PMSP.cfg.
  set (P := fun a => os + 256 <= a < os + 256 + 8 \/ os + 280 <= a < os + 280 + 16).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb4ee0 R1 0xb501c M1v P K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
    - clear - Wa O1. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  (* [comment removed for export] *)
  set (src' := PM.SRC qc (de + len) (rem - len)).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
  assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X Y i Hi. apply FR1; [lia| unfold P; lia]. }
  assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
  { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (AGB : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) -> PMFA.agA M M1 q m).
  { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
  (* [comment removed for export] *)
  assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) src').
  { apply (PGSKA.src_fields_updG M M1 os ois (ois + 16) qc de rem (de + len) (rem - len) ltac:(rewrite <- (src_eta src) in SRC; exact SRC)); unfold PM.CHUNK; [lia| lia| | | | | | | | | | lia| lia| lia].
    - split; [apply AGO; lia| apply AGSH; lia].
    - apply AGSH; lia.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact F256.
    - apply AGSH; lia.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact DC.
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F264].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F272].
    - apply BK1; [lia| lia| exact C280].
    - apply BK1; [lia| lia| exact C288]. }
  assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 tb tx).
  { apply (PMFA.vstr_at_agreeA RSEGS M M1 tb tx); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact VS].
    intros c0 n0 p0 E. apply AGB. apply in_or_app; right; apply in_or_app; left. rewrite E. left; reflexivity. }
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMFA.iss_at_agreeA RSEGS AD M M1 ois str sm); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact IA].
    intros c0 n0 p0 E. apply AGB. rewrite !in_app_iff. right; right; right. apply INCS. rewrite E. left; reflexivity. }
  assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGSSRA1.W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGSSRA1.W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (PA1 : PGS.tw_at T M1 src' tx tg OB).
  { apply (tw_xferA M M1 src src' tx tx tg tg LK cr Aw (vml_of model) S 24576 [] PA HH); [| constructor| exact SF1| reflexivity| exact VS1| exact TBOK].
    apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M1).
    - exact EKo.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    - apply L5SAR.dk_grows. exact MGM1. }
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  assert (SO1 : st_ok M1 model1 src' tx tg sm cr LK Aw).
  { split; [split; [|split]|].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
    - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
      split; [exact PA1|]. split; [exact IA1|].
      split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
      split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK]. }
  apply (finish_rs fx1 R1 M1 model1 src' tx tg sm cr LK Aw de len); try assumption.
  - intros x Hx. rewrite (KS1 x) by (revert x Hx; intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
  - lia.
  - lia.
  - right. left. exists qc, 16384. split; [left; reflexivity| lia].
  - intros i Hi. apply MGM1. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
  - destruct SF1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CC1 & _).
    change (PM.sr_qc src') with qc in CC1. unfold PM.CHUNK in CC1. intros x Hx. apply CC1. lia.
  - apply (src_step_trans _ _ _ _ _ _ STEP). unfold src', PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srd (fx : FPState) R M model src tx tg sm cr LK Aw :
  getr R (reg 1) = Z_to_bv 64 741280 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 tb -> getr R (reg 18) = Z_to_bv 64 os ->
  getr R (reg 19) = Z_to_bv 64 (tb / 8 + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 tb -> getr R (reg 12) = Z_to_bv 64 len -> 1 <= len ->
  st_ok M model src tx tg sm cr LK Aw -> fields_eq src tx tg -> PMSP.src_step src0 src sm0 sm -> PM.vs_size tx = 0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb50e0 M model) K.
Proof using All.
  intros A1 A2 A8 A9 A18 A19 A21 A22 KP A10 A11 A12 Hl SO FE STEP SZ0.
  pose proof SO as (_ & _ & PA & IA & _).
  assert (UN : 0 <= PM.unread src sm < 2 ^ 26).
  { pose proof (tsrc M src tx tg PA) as (SRC & PNI_ & PD_ & VS0 & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
    pose proof (PMASK.iss_size_ltA M ois str sm IA). destruct STEP as (_ & _ & _ & _ & U1). unfold PM.unread in *. lia. }
  apply (call_srd fx R M model src tx tg sm cr LK Aw 741280 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO ltac:(lia) ltac:(lia)).
  intros fx2 R2 M2 model2 LK2 Aw2 src2 tx2 tg2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 STEP2 SO2.
  pose proof (vpack M2 model2 src2 tx2 tg2 sm2 cr2 LK2 Aw2 SO2) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & AM2 & MRT2 & ILK2 & IAW2 & CRL2 & CRK2).
  pose proof lay as LAY.
  assert (UN2 : 0 <= PM.unread src2 sm2).
  { pose proof (tsrc M2 src2 tx2 tg2 PA2) as (SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2' & _).
    pose proof (PMASK.iss_size_ltA M2 ois str sm2 IA2). unfold PM.unread in *. lia. }
  assert (Hd2 : d < 2 ^ 26) by (unfold PMSP.consumed in CONS2; lia).
  assert (FE2 : fields_eq src2 tx2 tg2) by exact I.
  assert (STEP02 : PMSP.src_step src0 src2 sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  pose proof SV2 as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
  pose proof (tsrc M2 src2 tx2 tg2 PA2) as (_ & _ & _ & VS & _).
  assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (L5SAR.cs_of_preserved R R2 2%nat RP2) by inl; exact A2).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R R2 8%nat RP2) by inl; exact A8).
  assert (B9 : getr R2 (reg 9) = Z_to_bv 64 tb) by (rewrite (L5SAR.cs_of_preserved R R2 9%nat RP2) by inl; exact A9).
  assert (B18 : getr R2 (reg 18) = Z_to_bv 64 os) by (rewrite (L5SAR.cs_of_preserved R R2 18%nat RP2) by inl; exact A18).
  assert (B19 : getr R2 (reg 19) = Z_to_bv 64 (tb / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 19%nat RP2) by inl; exact A19).
  assert (B21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R R2 21%nat RP2) by inl; exact A21).
  assert (B22 : getr R2 (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 22%nat RP2) by inl; exact A22).
  assert (KP2 : forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R0 (reg x)).
  { intros x Hx. rewrite (L5SAR.cs_of_preserved R R2 x RP2) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  destruct VS as (VD & VC & VS). destruct tx2 as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ2, SZ0.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & BY0). pose proof (PMF.even_byte n1) as EV.
    LeanFeed.pfeed PP (PMARSPP.arpES_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => 2 * n1
         | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
         | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
        | |- L5.u8_at _ _ tb _ => unfold MV2; vis8 TAV
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
    unfold PMSPA.cfg, PMSP.cfg.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xb4fa0 R3 0xb501c M3v K HH2 AM2 MS3 MG3 FRZ3).
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (SO3 : st_ok M2 model3 src2 (PM.VShort n1) tg2 sm2 cr2 LK2 Aw2).
    { split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
      split; [exact TBOK2|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
      split; [exact ILK2|]. split; [exact IAW2|]. split; [exact CRL2| exact CRK2]. }
    replace (2 * n1 / 2) with n1 in E11 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    apply (finish_rs fx3 R3 M2 model3 src2 (PM.VShort n1) tg2 sm2 cr2 LK2 Aw2 (tb + 1) n1); try assumption.
    + intros x Hx. rewrite (KS3 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
    + lia. + lia.
    + right. right. lia.
    + apply (L5.defined_sub M2 tb 24 (tb + 1) n1 VD); lia.
    + intros x Hx. apply VC. lia.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M2 tb (c1 + 1) ltac:(lia) W0') as BY0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (Hq1 : 0 <= q1 < 2 ^ 64 /\ 0 <= n1 < 2 ^ 64).
    { pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH2 (q1, c1)) as X. cbn [fst snd] in X.
      destruct X as (X0 & X1); [apply in_or_app; right; apply in_or_app; left; left; reflexivity|]. lia. }
    LeanFeed.pfeed PP (PMARSPP.arpEL_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => (c1 + 1) mod 256
         | 40%nat => n1 | 41%nat => q1
         | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
         | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
        | |- L5.u8_at _ _ tb _ => unfold MV2; vis8 TAV
        | |- L5.u64_at _ _ (tb + _) _ => unfold MV2; vis64 TAV
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
    unfold PMSPA.cfg, PMSP.cfg.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xb4fa0 R3 0xb501c M3v K HH2 AM2 MS3 MG3 FRZ3).
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (SO3 : st_ok M2 model3 src2 (PM.VLong c1 n1 q1) tg2 sm2 cr2 LK2 Aw2).
    { split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
      split; [exact TBOK2|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
      split; [exact ILK2|]. split; [exact IAW2|]. split; [exact CRL2| exact CRK2]. }
    apply (finish_rs fx3 R3 M2 model3 src2 (PM.VLong c1 n1 q1) tg2 sm2 cr2 LK2 Aw2 q1 n1); try assumption.
    + intros x Hx. rewrite (KS3 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
    + lia. + lia.
    + right. left. exists q1, c1. split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| lia].
    + apply (L5.defined_sub M2 q1 c1 q1 n1 DQ); lia.
    + intros x Hx. apply CQ. lia.
Qed.

End Call.
End WithHeap.
End PGSRSA2.
