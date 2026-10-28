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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnARdSpanP_b Ba0PgRdSpan1_b Ba0PgRdSpan2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b Ba0PgSrd1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRSA2b.
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
#[local] Abbreviation tw_side := (PGSSRA1.tw_side L ar C HI HIok LBX FF T OB TOK OFR).
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

#[local] Abbreviation at_srd := (PGSRSA2.at_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slow (fx : FPState) R M model src tx tg sm cr LK Aw :
  bregs R -> 1 <= len -> st_ok M model src tx tg sm cr LK Aw -> fields_eq src tx tg -> PMSP.src_step src0 src sm0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4e9c M model) K.
Proof using All.
  intros BR0 Hl SO FE STEP. pose proof BR0 as (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP).
  pose proof (vpack M model src tx tg sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & _ & NDL & _).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (tsrc M src tx tg PA) as (SRC & PNI & PD & VS & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  (* [comment removed for export] *)
  assert (AOF : PMSPA.aobjA FF lo (hi - lo)) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| lia| lia]).
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) -> q + m <= lo \/ hi <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m lo (hi - lo) HH Hq AOF) as [X|X]; [left| right]; lia. }
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (NOTSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> forall x, a <= x < a + n -> 0 <= HeapIfaceA.S x < 2 ^ 64 /\ 2147446784 <= HeapIfaceA.S x < 17594333495296).
  { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia. }
  destruct VS as (VD & VC & VS). destruct tx as [n0|c0 n0 q0].
  - (* [comment removed for export] *)
    destruct VS as (Hn0 & BY0). pose proof (PMF.even_byte n0) as EV.
    assert (TZ1 : L5KA.zeros_at MV ((tb + 1) / 8 + 2147450880) 1).
    { replace ((tb + 1) / 8) with (tb / 8) by (apply Z.div_unique with 1; [left; lia| pose proof (Z.div_mod tb 8 ltac:(lia)); lia]).
      intros i Hi. apply TZ. lia. }
    LeanFeed.pfeed PP (PMARSPP.arpSS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => 2 * n0 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
        | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & E19 & C0 & C1).
    set (P := fun a => tb + 0 <= a < tb + 0 + 2).
    unfold PMSPA.cfg, PMSP.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb4e9c R1 0xb50e0 M1v P K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
    { intros a Ha Wa. unfold P in Wa. split.
      - unfold aclientw, aclient_g. right; right; right; left. destruct AT as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
      - clear - Wa T1. lia. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= tb \/ tb + 2 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn x Hx. destruct (NOTSH a n Ha Hn x Hx) as (X1 & X2). apply FR1; [lia| unfold P; destruct TBIG; lia]. }
    assert (AGB : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own (PM.VShort n0) ++ OB ++ LBX) -> PMFA.agA M M1 q m).
    { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AG; lia| apply AGSH; lia]). }
    assert (BK1 : forall a v, tb <= a -> a + 1 <= tb + 24 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u8_at_vis (ahid Aw model) M1 a v ltac:(apply TAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    (* [comment removed for export] *)
    assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) src).
    { apply (PGSKA.src_fields_keepG M M1 os ois (ois + 16) src SRC); [lia| lia| split; [apply AG; lia| apply AGSH; lia]| apply AGSH; lia|].
      apply (L5.defined_grows M M1 _ _ MGM1). exact DC. }
    assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 tb (PM.VShort 0)).
    { split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
      split; [apply (PMFA.accA_agree M M1 tb 24); [apply AGSH; lia| exact VC]|]. split; [lia|]. replace (2 * 0) with 0 by lia. apply BK1; [lia| lia| exact C0]. }
    assert (TB1 : PM.tb_ok (PM.VShort 0) tg) by (unfold PM.tb_ok in *; cbn [PM.vs_cap] in *; exact TBOK).
    assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (tb, 24)); [unfold PGSSRA1.W0; apply in_or_app; right; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
    assert (PA1 : PGS.tw_at T M1 src (PM.VShort 0) tg OB).
    { apply (tw_xferA M M1 src src (PM.VShort n0) (PM.VShort 0) tg tg LK cr Aw (vml_of model) S 24576 [] PA HH); [| constructor| exact SF1| reflexivity| exact VS1| exact TB1].
      apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M1); [exact EKo| apply (L5.defined_grows M M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1]. }
    set (Wp := [(tb, 2)]).
    assert (EK1 : L5SAR.ek L ar (PM.src_own src ++ PM.vs_own (PM.VShort n0) ++ OB ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (tb, 2)); [left; reflexivity|]. unfold L5.in_rng, P in *; cbn [fst snd]. lia. }
    assert (WAPPp : PMKA.wapp Wp) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]).
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
    { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
      - intros c n p E i Hi r0 Hr. assert (Ip : In (p, c) (PM.src_own src ++ PM.vs_own (PM.VShort n0) ++ OB ++ LBX)) by (rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity).
        destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (tb, 24)); [unfold PGSSRA1.W0; apply in_or_app; right; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
    assert (SO1 : st_ok M1 model1 src (PM.VShort 0) tg sm cr LK Aw).
    { split; [split; [|split]|].
      - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
      - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
      - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
      - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| assumption])|].
        split; [exact PA1|]. split; [exact IA1|].
        split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]|].
        split; [exact TB1|].
        split; [exact HH1|]. split; [exact AM1|].
        split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
        split; [exact ILK|]. split; [exact IAW|].
        unfold PM.pot_text in *. cbn [PM.vs_cap] in *. split; [exact CRL| exact CRK]. }
    apply (at_srd fx1 R1 M1 model1 src (PM.VShort 0) tg sm cr LK Aw); try assumption.
    all: first [ rewrite (KS1 2%nat) by inl; exact A2 | rewrite (KS1 8%nat) by inl; exact A8 | rewrite (KS1 9%nat) by inl; exact A9
               | rewrite (KS1 18%nat) by inl; exact A18 | rewrite (KS1 21%nat) by inl; exact A21 | rewrite (KS1 22%nat) by inl; exact A22
               | (intros x Hx; rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx)
               | reflexivity ].
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn0 & Hc0 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c0 + 1) ltac:(lia) W0') as BY0. pose proof (PMF.odd_byte c0 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c0 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)); lia).
    assert (TIN : In (q0, c0) (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    pose proof (PGTKA.tbd_vis L ar C HI LY HIok _ FF LK cr Aw M model q0 c0 HH TIN ltac:(lia) CQ) as ((D1 & D2 & D16 & DBIG) & DZ & DW & DAV & DCE).
    pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q0 c0 HH TIN) as QIMG.
    assert (TFA := BLKAP _ _ TIN).
    pose proof LAY as (_ & _ & LI1 & LI2 & LT1 & LT2 & _ & _ & _ & _ & _ & _ & _ & _ & LTI).
    (* [comment removed for export] *)
    assert (KQT : q0 + 1 <= tb \/ tb + 24 <= q0) by (destruct TFA; [left|right]; lia).
    assert (KQO : q0 + 1 <= os \/ os + 296 <= q0) by (destruct TFA; [left|right]; lia).
    assert (KQS : 2147446784 + 17592186048512 <= q0 \/ q0 + 1 <= 2147446784) by (destruct DBIG; [left|right]; lia).
    assert (KQF : S - 80 + 80 <= q0 \/ q0 + 1 <= S - 80) by (right; lia).
    assert (QNI : ~ (65536 <= q0 < 6905856)) by (destruct QIMG; lia). clear QIMG.
    LeanFeed.pfeed PP (PMARSPP.arpSL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => (c0 + 1) mod 256
         | 40%nat => n0 | 41%nat => q0 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
        | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
        | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
        | |- PMARSPP.aligned q0 8 => unfold PMARSPP.aligned; apply PMKA.mod16_8'; exact D16
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & E19 & C0 & C1).
    set (P := fun a => (q0 + 0 <= a < q0 + 0 + 1) \/ (tb + 8 <= a < tb + 8 + 8)).
    unfold PMSPA.cfg, PMSP.cfg.
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb4e9c R1 0xb50e0 M1v P K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha Wa. unfold P in Wa. destruct Wa as [Wa|Wa].
      - split; [unfold aclientw, aclient_g; left; exists (q0, c0); split; [exact TIN| cbn [fst snd]; lia]| intros X; apply QNI; lia].
      - split; [| clear - Wa T1; lia]. unfold aclientw, aclient_g. right; right; right; left. destruct AT as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= q0 \/ q0 + 1 <= a) -> (a + n <= tb + 8 \/ tb + 16 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X Y i Hi. apply FR1; [lia| unfold P; clear - X Y Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn x Hx. destruct (NOTSH a n Ha Hn x Hx) as (X1 & X2). apply FR1; [lia| unfold P; clear - X2 TBIG KQS; destruct TBIG; destruct KQS; lia]. }
    assert (OTH : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX) -> q <> q0 -> PMFA.agA M M1 q m).
    { intros q m Hq NE. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1.
      pose proof (PMASK.blk_apart L ar C HI HIok _ FF LK cr Aw M _ q m q0 c0 HH Hq TIN NE) as AP. pose proof (BLKAP q m Hq) as BF.
      split; [apply AG; clear - X0 X1 AP BF Hc0 LT1 LT2; lia| apply AGSH; clear - X0 X1; lia]. }
    assert (NEQ : PM.sr_qc src <> q0).
    { intros E. apply (PMARS1.fst_neq_app (PM.src_own src) (PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX) (PM.sr_qc src) PM.CHUNK q0 c0);
        [exact NDL| left; reflexivity| apply in_or_app; left; left; reflexivity| exact E]. }
    assert (BK64 : forall a v, tb <= a -> a + 8 <= tb + 24 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply TAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    (* [comment removed for export] *)
    assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) src).
    { apply (PGSKA.src_fields_keepG M M1 os ois (ois + 16) src SRC); [lia| lia| destruct TFA as [TF|TF]; (split; [apply AG; lia| apply AGSH; lia])| |].
      - destruct (OTH _ _ QIN NEQ) as [_ SH]. exact SH.
      - apply (L5.defined_grows M M1 _ _ MGM1). exact DC. }
    assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 tb (PM.VLong c0 0 q0)).
    { split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
      split; [apply (PMFA.accA_agree M M1 tb 24); [apply AGSH; lia| exact VC]|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [destruct TFA as [TF|TF]; apply AG; lia| lia| lia| exact W0']|].
      split; [apply BK64; [lia| lia| exact C0]|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [destruct TFA as [TF|TF]; apply AG; lia| lia| lia| exact W16]|].
      split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MGM1; apply DQ; exact Hi|].
      apply (PMFA.accA_agree M M1 q0 c0); [apply AGSH; lia| exact CQ]. }
    assert (TB1 : PM.tb_ok (PM.VLong c0 0 q0) tg) by (unfold PM.tb_ok in *; cbn [PM.vs_cap] in *; exact TBOK).
    assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 (W0 ++ [(q0, 1)]) M M1).
    { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 (W0 ++ [(q0, 1)]) M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X].
      - apply (OWx (q0, 1)); [apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      - apply (OWx (tb, 24)); [apply in_or_app; left; unfold PGSSRA1.W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    destruct (tw_side M src (PM.VLong c0 n0 q0) LK cr Aw (vml_of model) HH) as (_ & FB').
    assert (PA1 : PGS.tw_at T M1 src (PM.VLong c0 0 q0) tg OB).
    { apply (tw_xferA M M1 src src (PM.VLong c0 n0 q0) (PM.VLong c0 0 q0) tg tg LK cr Aw (vml_of model) S 24576 [(q0, 1)] PA HH); [| | exact SF1| reflexivity| exact VS1| exact TB1].
      - rewrite app_assoc. apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M1); [exact EKo| apply (L5.defined_grows M M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1].
      - constructor; [| constructor]. cbn [fst snd]. split; [clear - TFA Hc0; destruct TFA; [left| right]; lia|]. split.
        + intros B m HB. destruct (proj2 (FB' (B, m) HB) q0 c0 ltac:(left; reflexivity)) as [Y|Y]; cbn [fst snd] in Y; [right| left]; clear - Y Hc0; lia.
        + unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - D1 D2 KQS Hc0. destruct KQS; lia. }
    set (Wp := [(q0, 1); (tb + 8, 8)]).
    assert (EK1 : L5SAR.ek L ar (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X]; [apply (OWx (q0, 1))| apply (OWx (tb + 8, 8))]; try (unfold Wp; cbn; auto); unfold L5.in_rng; cbn [fst snd]; lia. }
    assert (WAPPp : PMKA.wapp Wp).
    { unfold Wp. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct DBIG; [right| left]; lia|].
      apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]. }
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
    { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [clear - Hi TFA Hc0 LI1 LI2; lia| clear - Hi LTI; lia].
      - intros c n p E i Hi r0 Hr. assert (Ip : In (p, c) (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX)) by (rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity).
        assert (NE : p <> q0).
        { intros Ep. subst p. apply (PMARS1.fst_neq_app (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB) LBX q0 c0 q0 c);
            [rewrite <- !app_assoc; exact NDL| apply in_or_app; right; apply in_or_app; left; left; reflexivity| apply INCS; rewrite E; left; reflexivity| reflexivity]. }
        pose proof (BLKAP _ _ Ip) as X. pose proof (PMASK.blk_apart L ar C HI HIok _ FF LK cr Aw M _ p c q0 c0 HH Ip TIN NE) as Y.
        unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [clear - Hi Y Hc0; lia| clear - Hi X LT1 LT2; lia]. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X].
      - apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB) LBX FF LK cr Aw M _ q0 c0 a S 24576 ltac:(rewrite <- !app_assoc; exact HH));
          [apply in_or_app; right; apply in_or_app; left; left; reflexivity| lia| exact CA].
      - apply (OWx (tb, 24)); [unfold PGSSRA1.W0; apply in_or_app; right; left; reflexivity|].
        unfold L5.in_rng; cbn [fst snd]. lia. }
    assert (SO1 : st_ok M1 model1 src (PM.VLong c0 0 q0) tg sm cr LK Aw).
    { split; [split; [|split]|].
      - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
      - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
      - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
      - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| assumption])|].
        split; [exact PA1|]. split; [exact IA1|].
        split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]|].
        split; [exact TB1|].
        split; [exact HH1|]. split; [exact AM1|].
        split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
        split; [exact ILK|]. split; [exact IAW|].
        unfold PM.pot_text in *. cbn [PM.vs_cap] in *. split; [exact CRL| exact CRK]. }
    apply (at_srd fx1 R1 M1 model1 src (PM.VLong c0 0 q0) tg sm cr LK Aw); try assumption.
    all: first [ rewrite (KS1 2%nat) by inl; exact A2 | rewrite (KS1 8%nat) by inl; exact A8 | rewrite (KS1 9%nat) by inl; exact A9
               | rewrite (KS1 18%nat) by inl; exact A18 | rewrite (KS1 21%nat) by inl; exact A21 | rewrite (KS1 22%nat) by inl; exact A22
               | (intros x Hx; rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx)
               | reflexivity ].
Qed.

End Call.
End WithHeap.
End PGSRSA2b.
