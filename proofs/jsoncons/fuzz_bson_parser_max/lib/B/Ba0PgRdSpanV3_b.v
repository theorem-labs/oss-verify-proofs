(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnARdSpanVP_b Ba0PgRdSpanV1_b Ba0PgRdSpanV2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnSpecsAX_b PnSpecsAXC_b Ba0PgSrd1_b Ba0PgVw1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRVA3.
Abbreviation v8_atA := (PGV8.v8_at AsanUbsan.M.loaded_segments PMSPA.accA PGV8A.annA).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSRVA1.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGV8.vowner) (OB : list (Z * Z)) (src0 : PM.srcst) (x0 : PGV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGVWA1.os T).   (* [comment removed for export] *)
#[local] Abbreviation ois := (PGVWA1.ois T).   (* [comment removed for export] *)
#[local] Abbreviation tb := (PGVWA1.tb T).   (* [comment removed for export] *)
#[local] Abbreviation lo := (PGVWA1.lo T).   (* [comment removed for export] *)
#[local] Abbreviation hi := (PGVWA1.hi T).   (* [comment removed for export] *)
Hypothesis TOK : PGV8A.vowner_ok RSEGS AD L ar HI T.
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
Hypothesis SRDS : PGV8A.srd_read_v_specG RSEGS AD L ar HI PNRA.FCB (PNL.pn_srd_read_v PMA.AN).
#[local] Abbreviation W0 := (PGVWA1.W0 T).   (* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (x' : PGV8.v8) (g' : Z) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  PMSP.consumed src0 src' sm0 sm' = n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PGV8.v8_own x' ++ OB) ptr n) ->
  L5.defined M' ptr n -> PMSPA.accA M' ptr n ->
  (n = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at T M' src' x' g' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar x0 g0) (pot L ar x' g') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGVWA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGVWA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGVWA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation frame_app := (PGVWA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGVWA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGVWA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGVWA1.stw_ok L ar C HI LY HIok T TOK).
#[local] Abbreviation own2 := PGVWA1.own2.
#[local] Abbreviation unread_nn := (PGSRVA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation centry := (PGSRVA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation U := (PGSRVA1.U R0).
#[local] Abbreviation saves9 := (PGSRVA1.saves9 R0 S).
#[local] Abbreviation kept_rs := (PGSRVA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSRVA1.memrel L ar M0 LBX FF S T).
#[local] Abbreviation fields_eq := (PGSRVA1.fields_eq).
#[local] Abbreviation st_ok := (PGSRVA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S T OB x0 g0 str).
#[local] Abbreviation bregs := (PGSRVA1.bregs R0 S len T).
#[local] Abbreviation finish_rs := (PGSRVA1.finish_rs L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PGSRVA1.call_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation vpack := (PGSRVA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PGVWA1.outside_W0 L ar HI T TOK).

#[local] Abbreviation fast := (PGSRVA2.fast L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation centryM := (PGSRVA1.centryM L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation callee_mem := (PGSRVA1.callee_mem L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation perm_v8 := (PGVWA1.perm_v8 L ar C HI HIok).
#[local] Abbreviation perm_v8_back := (PGVWA1.perm_v8_back L ar C HI HIok).
#[local] Abbreviation call_fill := (PGSRVA1.call_fill L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation src_step_trans := PGSRVA2.src_step_trans.
(* [comment removed for export] *)
Hypothesis CLV : PNSAXC.clear_v8_spec RSEGS AD L ar HI 0xabb00.
#[local] Abbreviation at_srd := (PGSRVA2.at_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slow (fx : FPState) R M model src x g sm cr LK Aw :
  bregs R -> 1 <= len -> st_ok M model src x g sm cr LK Aw -> fields_eq src x g -> PMSP.src_step src0 src sm0 sm ->
  PM.unread src sm = PM.unread src0 sm0 -> PGV8.v8_room x (PM.unread src sm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3cd8 M model) K.
Proof using All.
  intros BR0 Hl SO FE STEP CONS0 RMx. pose proof BR0 as (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & _).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (tsrc M src x g PA) as (SRC & PNI & PD & VS & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  (* [comment removed for export] *)
  assert (AOF : PMSPA.aobjA FF lo (hi - lo)) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| lia| lia]).
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> q + m <= lo \/ hi <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m lo (hi - lo) HH Hq AOF) as [X|X]; [left| right]; lia. }
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (NOTSH : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> forall xs, a <= xs < a + m -> 0 <= HeapIfaceA.S xs < 2 ^ 64 /\ 2147446784 <= HeapIfaceA.S xs < 17594333495296).
  { intros a m Ha Hm xs Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= xs / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). lia. }
  destruct VS as (VD & VC & VR).
  (* [comment removed for export] *)
  assert (HW : exists b n, L5.u64_at RSEGS M tb b /\ L5.u64_at RSEGS M (tb + 8) (b + n) /\ 0 <= b <= 2 ^ 47 /\ 0 <= n <= 2 ^ 27
                           /\ PGV8.v8_data x = b /\ PGV8.v8_size x = n /\ n <= PGV8.v8_cap x).
  { destruct x as [|b n c]; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap].
    - destruct VR as (U0 & U8 & _). exists 0, 0. split; [exact U0|]. split; [exact U8|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity| lia].
    - destruct VR as (U0 & U8 & _ & Hn & Hc & Hb & _).
      assert (BIN : In (b, c) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b n c) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (BRB _ BIN) as (X0 & X1). cbn [fst snd] in X0, X1.
      exists b, n. split; [exact U0|]. split; [exact U8|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity| lia]. }
  destruct HW as (b & n & U0 & U8 & Hb & Hn & XB & XN & XC).
  LeanFeed.pfeed PP (PMARSVP.arvS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => b | 40%nat => n | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ tb _ => unfold MV; vis64 TAV
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E19 & E20 & E21 & C8).
  set (P := fun a => tb + 8 <= a < tb + 8 + 8).
  unfold PMSPA.cfg, PMSP.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3cd8 R1 0xabb00 M1v P K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. destruct AT as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
    - clear - Wa T1. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  (* [comment removed for export] *)
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= tb + 8 \/ tb + 16 <= a) -> L5C.agree_on M M1 a m).
  { intros a m Ha Hm X i Hi. apply FR1; [lia| unfold P; lia]. }
  assert (AGSH : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M1 a m).
  { intros a m Ha Hm xs Hx. destruct (NOTSH a m Ha Hm xs Hx) as (X1 & X2). apply FR1; [lia| unfold P; destruct TBIG; lia]. }
  assert (BK1 : forall a v, tb <= a -> a + 8 <= tb + 24 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb' X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply TAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
  assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) src).
  { apply (PGSKA.src_fields_keepG M M1 os ois (ois + 16) src SRC); [lia| lia| split; [apply AG; lia| apply AGSH; lia]| apply AGSH; lia|].
    apply (L5.defined_grows M M1 _ _ MGM1). exact DC. }
  set (Wp := [(tb + 8, 8)]).
  assert (EK1 : L5SAR.ek L ar (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF S 24576 Wp M M1).
  { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (tb + 8, 8)); [left; reflexivity|]. unfold L5.in_rng, P in *; cbn [fst snd]. lia. }
  assert (WAPPp : PMKA.wapp Wp) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]).
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros xr Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| | |exact IA].
    - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
    - intros c1 n1 p1 E i Hi r0 Hr. assert (Ip : In (p1, c1) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity).
      destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
  assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (tb, 24)); [unfold PGVWA1.W0; apply in_or_app; right; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (tb, 24)); [unfold PGVWA1.W0; apply in_or_app; right; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (MR1 : memrel M1).
  { split; [|split].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1). }
  assert (SV1 : saves9 M1).
  { repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| assumption]). }
  assert (BASE1 : PMSTA.base_okA RSEGS AD M1).
  { apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]. }
  assert (OWNc : PGV8.v8_own (PGV8.v8_clear x) = PGV8.v8_own x) by (destruct x; reflexivity).
  assert (POTc : pot L ar (PGV8.v8_clear x) g = pot L ar x g) by (destruct x; reflexivity).
  assert (TBc : PGV8.v8_ok (PGV8.v8_clear x) g) by (destruct x; exact TBOK).
  assert (KP1 : kept_rs R1).
  { intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
  assert (B2 : getr R1 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS1 2%nat) by inl; exact A2).
  destruct (centryM R1 M1 _ LK cr Aw (vml_of model1) 736480 0 E1 ltac:(split; [lia| reflexivity]) B2 KP1 MR1 HH1 ILK ltac:(lia)) as (ENT & _ & FRS').
  pose proof (perm_v8 src x OB LBX FF LK cr Aw M1 (vml_of model1) HH1) as HHp.
  (* [comment removed for export] *)
  pose proof CLV as CV. unfold PNSAXC.clear_v8_spec in CV.
  apply (CV fx1 R1 M1 model1 K (PM.src_own src ++ OB ++ LBX) FF LK Aw cr tb x (S - 80) 736480 HHp AM1 K0 ENT FRS').
  { rewrite L5K.rl10. exact E10. }
  { exact AT. }
  { exact T8. }
  { apply (PMFA.accA_agree M M1 tb 24); [apply AGSH; lia| exact VC]. }
  { (* [comment removed for export] *)
    split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
    split; [apply (PMFA.accA_agree M M1 tb 24); [apply AGSH; lia| exact VC]|].
    pose proof (BK1 (tb + 8) (b + n) ltac:(lia) ltac:(lia) C8) as C8'.
    destruct x as [|b0 n0 c0]; cbn [PGV8.v8_data PGV8.v8_size PGV8.v8_cap] in *.
    - destruct VR as (W0' & _ & W16). subst b n. rewrite Z.add_0_r in C8'.
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W0']|].
      split; [exact C8'|].
      apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W16].
    - destruct VR as (W0' & _ & W16 & Hn0 & Hc0 & Hb0 & Hb16 & BD & BA & BN). subst b n.
      assert (BIN : In (b0, c0) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b0 n0 c0) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (BRB _ BIN) as (X0 & X1). cbn [fst snd] in X0, X1.
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W0']|].
      split; [exact C8'|].
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W16]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hb16|].
      split; [intros i Hi; apply MGM1; apply BD; exact Hi|].
      split.
      + apply (PMFA.accA_agree M M1 b0 n0); [apply AGSH; lia| exact BA].
      + apply (PGV8KA.annA_agree M M1 b0 n0 c0); [lia| apply PMKA.mod16_8'; exact Hb16| apply AGSH; lia| exact BN]. }
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 VS2 PAY2 HP2 MRT2 ILK2 IAW2 AM2 HH2. rewrite <- OWNc in HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.
  (* [comment removed for export] *)
  assert (HP2' : L5CA.ahpres L ar ((PM.src_own src ++ OB) ++ LBX) FF (S - 80) 12288 [(tb + 8, 8)] M1 M2) by (rewrite <- app_assoc; exact HP2).
  destruct (callee_mem M1 M2 (PM.src_own src ++ OB) 12288 [(tb + 8, 8)] MR1 SV1 ltac:(lia) ltac:(lia) TOP HP2') as (MR2 & SV2 & EKn2).
  { intros a _ O r0 Hr Hin. destruct Hr as [<-|[]]. apply (O (tb, 24)); [unfold PGVWA1.W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  { intros a Ha r0 Hr Hin. destruct Hr as [<-|[]]. unfold L5.in_rng in Hin; cbn [fst snd] in Hin. lia. }
  assert (BRBc : forall q, In q (PM.src_own src ++ OB ++ LBX) -> 0 <= fst q /\ fst q + snd q <= 2 ^ 47).
  { intros q Hq. apply BRB. rewrite !in_app_iff in Hq. rewrite !in_app_iff. tauto. }
  assert (EKc : L5SAR.ek L ar (PM.src_own src ++ OB ++ LBX) FF S 24576 Wp M1 M2).
  { apply (L5SAR.ek_callee L ar (PM.src_own src ++ OB ++ LBX) [] FF [] S 24576 (S - 80) 12288 Wp Wp M1 M2 HP2); [lia| lia| intros a _ O; exact O]. }
  assert (QINc : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  pose proof MR2 as (EK2 & DK2 & STK2).
  assert (AGQ : PMFA.agA M1 M2 (PM.sr_qc src) PM.CHUNK).
  { apply (PMKA.agA_blk L ar _ FF S 24576 Wp M1 M2 EKc WAPPp BRBc (PM.sr_qc src) PM.CHUNK QINc). intros i Hi r0 Hr. unfold Wp in Hr. destruct Hr as [<-|[]]. unfold L5.in_rng; cbn [fst snd]. destruct (BLKAP _ _ QIN) as [X|X]; lia. }
  destruct AGQ as [AGQ1 AGQ2].
  assert (SF2 : PM.src_fields_at RSEGS PMSPA.accA M2 os ois (ois + 16) src).
  { apply (PGSKA.src_fields_keepG M1 M2 os ois (ois + 16) src SF1); [lia| lia| | |].
    - apply (PMKA.agA_obj L ar _ FF S 24576 Wp M1 M2 EKc WAPPp FRB os 296 AO_). intros i Hi r0 Hr. unfold Wp in Hr. destruct Hr as [<-|[]]. unfold L5.in_rng; cbn [fst snd]. lia.
    - exact AGQ2.
    - apply (L5C.defined_agree M1 M2 _ _ AGQ1). apply (L5.defined_grows M M1 _ _ MGM1). exact DC. }
  assert (IA2 : PM.iss_at RSEGS AD PMSPA.accA M2 ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M1 M2 EKc WAPPp FRB BRBc _ _ _ AOI); [intros xr Hx; rewrite !in_app_iff; right; right; apply INCS; exact Hx| | | exact IA1].
    - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
    - intros c1 n1 p1 E i Hi r0 Hr. assert (Ip : In (p1, c1) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity).
      destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
  assert (BASE2 : PMSTA.base_okA RSEGS AD M2).
  { apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M1 M2 EKn2); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE1]. }
  assert (PA2 : PGV8.vw_at T M2 src (PGV8.v8_clear x) g OB).
  { apply (tw_xferA M M2 src src x (PGV8.v8_clear x) g g LK cr Aw (vml_of model) S 24576 [] PA HH); [| constructor| exact SF2| reflexivity| exact VS2| exact TBc].
    apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M2).
    - apply (L5SAR.ek_trans L ar (OB ++ LBX) FF S 24576 W0 M M1 M2 EKo).
      apply (L5SAR.ek_callee L ar (OB ++ LBX) (PM.src_own src) FF [] S 24576 (S - 80) 12288 W0 [(tb + 8, 8)] M1 M2 HP2); [lia| lia| intros a _ O r0 Hr Hin; destruct Hr as [<-|[]]; apply (O (tb, 24)); [unfold PGVWA1.W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]].
    - destruct STK2 as (_ & _ & _ & _ & D & _). exact D.
    - apply (L5SAR.dk_trans L ar (OB ++ LBX) FF S 24576 M M1 M2); [apply L5SAR.dk_grows; exact MGM1|].
      apply (L5SAR.dk_callee L ar (OB ++ LBX) (PM.src_own src) FF [] S 24576 (S - 80) 12288 [(tb + 8, 8)] M1 M2 HP2); lia. }
  assert (HH2' : ri_inv HI (PM.src_own src ++ PGV8.v8_own (PGV8.v8_clear x) ++ OB ++ LBX) FF LK2 cr Aw2 M2 (vml_of model2)) by exact (perm_v8_back src (PGV8.v8_clear x) OB LBX FF LK2 cr Aw2 M2 (vml_of model2) HH2).
  assert (SO2 : st_ok M2 model2 src (PGV8.v8_clear x) g sm cr LK2 Aw2).
  { split; [exact MR2|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|]. split; [exact TBc|].
    split; [exact HH2'|]. split; [exact AM2|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT| eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]]|].
    split; [intros xr Hx; apply ILK; apply ILK2; exact Hx|]. split; [intros xr Hx; apply IAW2; apply IAW; exact Hx|].
    rewrite POTc. split; [exact CRL| exact CRK]. }
  (* [comment removed for export] *)
  pose proof (vpack M2 model2 src (PGV8.v8_clear x) g sm cr LK2 Aw2 SO2) as (Y0 & Y1 & Y2 & (YR1 & Y16 & Y3) & YVV & (P1 & P8 & PBIG) & PZ & PW & PAV & (Q1 & Q8 & QBIG) & QZ & QW & QAV & _ & _ & _ & _).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R1 R2 8%nat RP2) by inl; rewrite (KS1 8%nat) by inl; exact A8).
  assert (B9 : getr R2 (reg 9) = Z_to_bv 64 os) by (rewrite (L5SAR.cs_of_preserved R1 R2 9%nat RP2) by inl; rewrite (KS1 9%nat) by inl; exact A9).
  assert (B18 : getr R2 (reg 18) = Z_to_bv 64 tb) by (rewrite (L5SAR.cs_of_preserved R1 R2 18%nat RP2) by inl; rewrite (KS1 18%nat) by inl; exact A18).
  assert (B19 : getr R2 (reg 19) = Z_to_bv 64 (os + 288)) by (rewrite (L5SAR.cs_of_preserved R1 R2 19%nat RP2) by inl; exact E19).
  assert (B21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 21%nat RP2) by inl; exact E21).
  assert (B22 : getr R2 (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl; rewrite (KS1 22%nat) by inl; exact A22).
  assert (C2 : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2%nat RP2) by inl; exact B2).
  assert (KP2 : kept_rs R2).
  { intros xr Hx. rewrite (L5SAR.cs_of_preserved R1 R2 xr RP2) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP1. exact Hx. }
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  LeanFeed.pfeed PP (PMARSVP.arvC_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & G1 & G10 & G11 & G12).
  unfold PMSPA.cfg, PMSP.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb3ce0 R3 0xb5500 M3v K HH2' AM2 MS3 MG3 FRZ3).
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (SO3 : st_ok M2 model3 src (PGV8.v8_clear x) g sm cr LK2 Aw2).
  { pose proof SO2 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
    exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH3 (conj AM3 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT3) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
  apply (at_srd fx3 R3 M2 model3 src (PGV8.v8_clear x) g sm cr LK2 Aw2); try assumption.
  all: first [ rewrite (KS3 2%nat) by inl; exact C2 | rewrite (KS3 8%nat) by inl; exact B8 | rewrite (KS3 9%nat) by inl; exact B9
             | rewrite (KS3 18%nat) by inl; exact B18 | rewrite (KS3 19%nat) by inl; exact B19
             | rewrite (KS3 21%nat) by inl; exact B21 | rewrite (KS3 22%nat) by inl; exact B22
             | (intros xr Hx; rewrite (KS3 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP2; exact Hx)
             | (destruct x; reflexivity)
             | (apply PGV8.v8_room_clear; exact RMx) ].
Qed.

(* [comment removed for export] *)
Lemma src_eta (src : PM.srcst) : PM.SRC (PM.sr_qc src) (PM.sr_de src) (PM.sr_rem src) = src.
Proof. destruct src; reflexivity. Qed.

(* [comment removed for export] *)
Lemma after_fill (fx : FPState) R M model src x g sm sm1 cr LK Aw (c : Z) :
  bregs R -> getr R (reg 20) = Z_to_bv 64 (os + 264) -> getr R (reg 23) = Z_to_bv 64 ((os + 264) / 8 + 2147450880) ->
  getr R (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> 1 <= len ->
  st_ok M model src x g sm1 cr LK Aw -> fields_eq src x g -> PMSP.src_step src0 src sm0 sm ->
  PM.unread src sm = PM.unread src0 sm0 -> PGV8.v8_room x (PM.unread src0 sm0) ->
  PMSP.src_step src src sm sm1 -> PM.sr_rem src = 0 -> PM.sm_g sm1 = PM.sm_g sm + c ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3c98 M model) K.
Proof using All.
  intros BR0 A20 A23 A10 Hc Hl SO FE STEP CONS0 RMx STEP1 RZ G1. pose proof BR0 as (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP).
  pose proof (vpack M model src x g sm1 cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (tsrc M src x g PA) as (SRC & PNI & PD & VS & _).
  pose proof SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & Q1 & Q2 & Q3 & Q4 & DC & CC & C240).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (qc := PM.sr_qc src) in *.
  unfold PM.CHUNK in *.
  assert (QIN : In (qc, 16384) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMARSVP.arvB_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => qc | 36%nat => os | 37%nat => tb | 38%nat => len | 43%nat => c | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  assert (CCs : L5.u64_at RSEGS M1v (os + 280) qc /\ L5.u64_at RSEGS M1v (os + 288) c).
  { destruct EX as [(_ & _ & _ & _ & _ & _ & C1 & C2) | (_ & _ & _ & _ & _ & _ & C1 & C2)]; split; assumption. }
  destruct CCs as (C1 & C2).
  set (P := fun a => os + 280 <= a < os + 280 + 16).
  set (s2 := PM.SRC qc qc c).
  (* [comment removed for export] *)
  assert (POST : forall M1 model1, ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 ->
                   mrestrict (ahid Aw model) M1 = M1v -> mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
                   st_ok M1 model1 s2 x g sm1 cr LK Aw).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1.
    assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; clear - X Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn xr Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
      assert (X8 : 0 <= xr / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      apply FR1; [lia|]. unfold P. clear - X8 OBIG. destruct OBIG; lia. }
    assert (AGB : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> PMFA.agA M M1 q m).
    { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
    assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) s2).
    { apply (PGSKA.src_fields_updG M M1 os ois (ois + 16) qc (PM.sr_de src) (PM.sr_rem src) qc c ltac:(rewrite <- (src_eta src) in SRC; exact SRC)); unfold PM.CHUNK; [lia| lia| | | | | | | | | | lia| lia| lia].
      - split; [apply AGO; lia| apply AGSH; lia].
      - apply AGSH; lia.
      - apply (L5.defined_grows M M1 _ _ MGM1). exact F256.
      - apply AGSH; lia.
      - apply (L5.defined_grows M M1 _ _ MGM1). exact DC.
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F264].
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F272].
      - apply BK1; [lia| lia| exact C1].
      - apply BK1; [lia| lia| exact C2]. }
    assert (VS1 : v8_atA M1 tb x).
    { apply (PGV8KA.v8_keepA M M1 tb x); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact VS].
      intros b0 n0 c0 E. apply AGB. apply in_or_app; right; apply in_or_app; left. rewrite E. left; reflexivity. }
    assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGVWA1.W0, PGS.W_srcfG; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
    assert (PA1 : PGV8.vw_at T M1 s2 x g OB).
    { apply (tw_xferA M M1 src s2 x x g g LK cr Aw (vml_of model) S 24576 [] PA HH); [| constructor| exact SF1| reflexivity| exact VS1| exact TBOK].
      apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M1); [exact EKo| apply (L5.defined_grows M M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1]. }
    set (Wp := [(os + 280, 16)]).
    assert (EK1 : L5SAR.ek L ar (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 280, 16)); [left; reflexivity|]. unfold L5.in_rng, P in *; cbn [fst snd]. lia. }
    assert (WAPPp : PMKA.wapp Wp) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKA.wapp_nil]).
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm1).
    { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros xr Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
      - intros c1 n1 p1 E i Hi r0 Hr. assert (Ip : In (p1, c1) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity).
        destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGVWA1.W0, PGS.W_srcfG; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
    split; [split; [|split]|].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
    - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
      split; [exact PA1|]. split; [exact IA1|].
      split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
      split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK]. }
  assert (STEP2 : PMSP.src_step src0 s2 sm0 sm1).
  { apply (src_step_trans _ _ _ _ _ _ STEP). unfold s2. unfold PMSP.src_step, PM.unread in *. cbn [PM.sr_qc PM.sr_rem] in *.
    destruct STEP1 as (E1 & E2 & L1 & S1 & U1). split; [reflexivity|]. split; [exact E2|]. split; [exact L1|]. split; [exact S1| lia]. }
  assert (FE2 : fields_eq s2 x g) by exact I.
  assert (CONS2 : PM.unread s2 sm1 = PM.unread src0 sm0).
  { rewrite <- CONS0. destruct STEP1 as (_ & E2 & _). unfold s2, PM.unread. cbn [PM.sr_rem]. lia. }
  assert (RM2 : PGV8.v8_room x (PM.unread s2 sm1)) by (rewrite CONS2; exact RMx).
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x696000)).
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
    - clear - Wa O1. lia. }
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  unfold PMSPA.cfg, PMSP.cfg.
  destruct EX as [(MS & KS1 & E10 & E11 & E12 & Hlt & _) | (MS & KS1 & E10 & E11 & E12 & Hge & _)].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3c98 R1 0xb3cd8 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1) as SO1.
    apply (slow fx1 R1 M1 model1 s2 x g sm1 cr LK Aw); try assumption.
    unfold PGSRVA1.bregs.
    split; [rewrite (KS1 2%nat) by inl; exact A2|]. split; [rewrite (KS1 8%nat) by inl; exact A8|].
    split; [rewrite (KS1 9%nat) by inl; exact A9|]. split; [rewrite (KS1 18%nat) by inl; exact A18|].
    split; [rewrite (KS1 19%nat) by inl; exact A19|]. split; [rewrite (KS1 21%nat) by inl; exact A21|].
    split; [rewrite (KS1 22%nat) by inl; exact A22|].
    intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3c98 R1 0xb3d24 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1) as SO1.
    assert (BR1 : bregs R1).
    { unfold PGSRVA1.bregs.
      split; [rewrite (KS1 2%nat) by inl; exact A2|]. split; [rewrite (KS1 8%nat) by inl; exact A8|].
      split; [rewrite (KS1 9%nat) by inl; exact A9|]. split; [rewrite (KS1 18%nat) by inl; exact A18|].
      split; [rewrite (KS1 19%nat) by inl; exact A19|]. split; [rewrite (KS1 21%nat) by inl; exact A21|].
      split; [rewrite (KS1 22%nat) by inl; exact A22|].
      intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
    apply (fast fx1 R1 M1 model1 s2 x g sm1 cr LK Aw); try assumption.
    all: unfold s2; cbn [PM.sr_rem]; first [exact E12 | lia].
Qed.

Lemma src_step_refl a sa : PMSP.src_step a a sa sa.
Proof. unfold PMSP.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry (fx : FPState) :
  ri_inv HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0) -> L5CA.amodel_ok Aw0 model0 -> L5CA.astk ar M0 S 24576 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 len -> getr R0 (reg 12) = Z_to_bv 64 tb ->
  PGV8.vw_at T M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD PMSPA.accA M0 ois str sm0 -> PMSTA.base_okA RSEGS AD M0 ->
  PGV8.v8_ok x0 g0 -> PGV8.v8_room x0 (PM.unread src0 sm0) -> PMSPA.credit_le (pot L ar x0 g0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0xb3bfc M0 model0) K.
Proof using All.
  intros HH AM STK A10 A11 A12 PA IA BASE TBOK ROOM0 CRL.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 24576 80 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (tsrc M0 src0 x0 g0 PA) as (SRC & PNI & PD & VS & _).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 os _ _ src0 S 24576 HH AO_ ltac:(clear - LAY; lia) SRC PNI STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & Q1 & Q2 & Q3 & Q4 & DC & CC & C240).
  set (qc := PM.sr_qc src0) in *. set (rem := PM.sr_rem src0) in *.
  unfold PM.CHUNK in *.
  assert (QIN : In (qc, 16384) (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  set (MV := mrestrict (ahid Aw0 model0) M0) in *.
  LeanFeed.pfeed PP (PMARSVP.arvA_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => rem | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  set (P := fun a => S - 80 <= a < S - 80 + 80).
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x696000)).
  { intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
  (* [comment removed for export] *)
  assert (POST : forall M1 model1, ri_inv HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) -> L5CA.amodel_ok Aw0 model1 -> model_rt model0 model1 ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   saves9 M1v -> st_ok M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 SVv.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (_ & VIS & _).
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 80 \/ S <= a) -> L5C.agree_on M0 M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; clear - X Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M0 M1 a n).
    { intros a n Ha Hn xr Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
      assert (X8 : 0 <= xr / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      apply FR1; [lia|]. unfold P. lia. }
    assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M0 M1).
    { apply (PGVWA1.ek_drop L ar (PM.src_own src0 ++ PGV8.v8_own x0)). rewrite <- PGVWA1.own2.
      apply (L5SAR.ek_piece L ar _ FF S 24576 W0 M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 24576 a HH SPT CA) as [X|X]; lia. }
    pose proof (PGVWA1.ek_drop L ar OB LBX FF S 24576 W0 M0 M1 EKo) as EKn.
    pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
    assert (EKp : L5SAR.ek L ar (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF S 24576 [] M0 M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 [] M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 24576 a HH SPT CA) as [X|X]; lia. }
    split; [split; [|split]|].
    - exact EKn.
    - apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M0 M1 S 24576 STK MGM1).
    - split.
      { destruct SVv as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
        assert (BK : forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M1v (S - k) v -> L5.u64_at RSEGS M1 (S - k) v).
        { intros k v Hk X. apply (proj1 (L5A.u64_at_vis (ahid Aw0 model0) M1 (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
        repeat split; (apply BK; [lia| assumption]). }
      split.
      { apply (tw_xferA M0 M1 src0 src0 x0 x0 g0 g0 LK0 cr0 Aw0 (vml_of model0) S 24576 [] PA HH); [| constructor| | reflexivity| | exact TBOK].
        - apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M0 M1); [exact EKo| apply (L5.defined_grows M0 M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1].
        - apply (PGSKA.src_fields_keepG M0 M1 os ois (ois + 16) src0 SRC); [clear - O1; lia| clear - O1; lia| | |].
          + apply (PMKA.agA_obj L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil FRB os 296 AO_). intros i _ r0 [].
          + apply (PMASK.agsh_blk L ar _ FF S 24576 [] M0 M1 _ _ EKp PMKA.wapp_nil QIN); [clear - QB0; lia| clear - QB1; lia].
          + apply (L5.defined_grows M0 M1 _ _ MGM1). exact DC.
        - apply (PGV8KA.v8_keepA M0 M1 tb x0); [clear - LAY; lia| clear - LAY; lia| apply (PMKA.agA_obj L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil FRB tb 24 AT_); intros i _ r0 []| | exact VS].
          intros b0 n0 c0 E. apply (PMKA.agA_blk L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil BRB b0 c0); [apply in_or_app; right; apply in_or_app; left; rewrite E; left; reflexivity| intros i _ r0 []]. }
      split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil FRB BRB _ _ _ AOI); [intros xr Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
      split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M0 M1 EKn); [intros a Ha; apply outside_W0; pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH); clear - Ha FA1 H; lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [exact MRT1|].
      split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact CRL|].
      unfold PMSPA.credit_keep. lia. }
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as BU1. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as BU8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as BU9. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as BU18.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (FE0 : fields_eq src0 x0 g0) by exact I.
  unfold PMSPA.cfg, PMSP.cfg.
  destruct EX as [(MS & KS1 & E10 & E11 & Z0 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | [(MS & KS1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E21 & E22 & Hle & Hr1 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | [(MS & KS1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E21 & E22 & Hlt & Hr1 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | (MS & KS1 & E2 & E8 & E9 & E10 & E18 & E19 & E21 & E22 & Hr0 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)]]].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb3bfc R1 0xb3db4 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (L0 : len = 0) by (rewrite Z.sub_0_r, Z.mod_small in Z0 by lia; lia).
    apply (finish_rs fx1 R1 M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0 0 0); try assumption.
    all: first [ rewrite (KS1 1%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 2%nat) by inl; exact Rsp0
               | rewrite (KS1 8%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 9%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 18%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 19%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 20%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 21%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 22%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 23%nat) by inl; unfold PGSRVA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | (intros xr Hx; rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); reflexivity)
               | (intros _; exact ROOM0)
               | (unfold PMSP.consumed; lia)
               | lia
               | (left; split; reflexivity)
               | (intros i Hi; lia)
               | apply src_step_refl ].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb3bfc R1 0xb3d24 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (BR1 : bregs R1).
    { unfold PGSRVA1.bregs. do 7 (split; [assumption|]).
      intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
    apply (fast fx1 R1 M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0 BR1 E12); [rewrite Z.sub_0_r, Z.mod_small in Hr1, Hl1 by lia; lia| exact SO1| exact FE0| apply src_step_refl| reflexivity| exact ROOM0].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb3bfc R1 0xb3cd8 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (BR1 : bregs R1).
    { unfold PGSRVA1.bregs. do 7 (split; [assumption|]).
      intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
    apply (slow fx1 R1 M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0 BR1); [rewrite Z.sub_0_r, Z.mod_small in Hl1 by lia; lia| exact SO1| exact FE0| apply src_step_refl| reflexivity| exact ROOM0].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb3bfc R1 0xb3c5c M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (RZ : rem = 0) by (rewrite Z.sub_0_r, Z.mod_small in Hr0 by lia; lia).
    assert (LP : 1 <= len) by (rewrite Z.sub_0_r, Z.mod_small in Hl1 by lia; lia).
    pose proof (vpack M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0 SO1) as (W0v & W1v & W2v & (SR1 & S16 & W3v) & SVV & (P1 & P8 & PBIG) & PZ & PW & PAV & _ & _ & _ & _ & OSS & _ & _ & _).
    pose proof SO1 as (_ & _ & PA1 & _).
    pose proof (tsrc M1 src0 x0 g0 PA1) as (SRC1 & _).
    destruct SRC1 as (_ & _ & _ & G264 & G272 & _ & G288 & _). fold qc rem in G264, G288. rewrite RZ in G288.
    set (MV1 := mrestrict (ahid Aw0 model1) M1) in *.
    LeanFeed.pfeed PP (PMARSVP.arvR0_conc fx1 R1 MV1 (fun j => match j with 2%nat => S | 34%nat => qc | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV1; vis64 PAV
        | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & [(MS2 & KS2 & F10 & F11 & F12 & Hgt) | (MS2 & KS2 & F1 & F10 & F11 & F12 & F20 & F23 & Hle)]).
    + (* [comment removed for export] *)
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M1 model1 fx1 fx2 R1 0xb3c5c R2 0xb3cd8 M2v K HH1 AM1 MS2 MG2 FRZ2).
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
      assert (E2' : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
      assert (SO2 : st_ok M1 model2 src0 x0 g0 sm0 cr0 LK0 Aw0).
      { pose proof SO1 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT2) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (BR2 : bregs R2).
      { unfold PGSRVA1.bregs.
        split; [rewrite (KS2 2%nat) by inl; exact E2|]. split; [rewrite (KS2 8%nat) by inl; exact E8|].
        split; [rewrite (KS2 9%nat) by inl; exact E9|]. split; [rewrite (KS2 18%nat) by inl; exact E18|].
        split; [rewrite (KS2 19%nat) by inl; exact E19|]. split; [rewrite (KS2 21%nat) by inl; exact E21|].
        split; [rewrite (KS2 22%nat) by inl; exact E22|].
        intros xr Hx. rewrite (KS2 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
      apply (slow fx2 R2 M1 model2 src0 x0 g0 sm0 cr0 LK0 Aw0 BR2 LP SO2 FE0 (src_step_refl _ _) eq_refl ROOM0).
    + (* [comment removed for export] *)
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M1 model1 fx1 fx2 R1 0xb3c5c R2 0xb29f8 M2v K HH1 AM1 MS2 MG2 FRZ2).
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
      assert (E2' : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
      assert (SO2 : st_ok M1 model2 src0 x0 g0 sm0 cr0 LK0 Aw0).
      { pose proof SO1 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT2) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (KP2 : kept_rs R2).
      { intros xr Hx. rewrite (KS2 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
      assert (R2sp : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS2 2%nat) by inl; exact E2).
      apply (call_fill fx2 R2 M1 model2 src0 x0 g0 sm0 cr0 LK0 Aw0 736408 F1 ltac:(split; [lia| reflexivity]) R2sp KP2 F10 F11 F12 SO2).
      intros fx3 R3 M3 model3 LK3 Aw3 sm3 c RP3 Y10 Hc G1 ST0 ST2 STEP3 SO3.
      assert (BR3 : bregs R3).
      { unfold PGSRVA1.bregs.
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 2%nat RP3) by inl; exact R2sp|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 8%nat RP3) by inl; rewrite (KS2 8%nat) by inl; exact E8|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 9%nat RP3) by inl; rewrite (KS2 9%nat) by inl; exact E9|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 18%nat RP3) by inl; rewrite (KS2 18%nat) by inl; exact E18|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 19%nat RP3) by inl; rewrite (KS2 19%nat) by inl; exact E19|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 21%nat RP3) by inl; rewrite (KS2 21%nat) by inl; exact E21|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 22%nat RP3) by inl; rewrite (KS2 22%nat) by inl; exact E22|].
        intros xr Hx. rewrite (L5SAR.cs_of_preserved R2 R3 xr RP3) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx. }
      apply (after_fill fx3 R3 M3 model3 src0 x0 g0 sm0 sm3 cr0 LK3 Aw3 c BR3); try assumption.
      * rewrite (L5SAR.cs_of_preserved R2 R3 20%nat RP3) by inl. exact F20.
      * rewrite (L5SAR.cs_of_preserved R2 R3 23%nat RP3) by inl. exact F23.
      * apply src_step_refl.
      * reflexivity.
Qed.


End Call.
(* [comment removed for export] *)
Theorem read_span_v_okG : PGSA.fill_buffer_specG RSEGS AD L ar HI PNRA.FCB -> PGV8A.srd_read_v_specG RSEGS AD L ar HI PNRA.FCB (PNL.pn_srd_read_v PMA.AN) ->
  PNSAXC.clear_v8_spec RSEGS AD L ar HI 0xabb00 ->
  PGV8A.read_span_v_specG RSEGS AD L ar HI PNRA.FCB (PNL.pn_read_span_v PMA.AN).
Proof.
  intros FBS SRDS CLV T TOK. unfold PGV8A.read_span_v_specG.
  intros fx R M model K OB LBX FF LK Aw cr sp r len src x g str sm HH AM K0 ENT FRM FRS OFR A10 A11 A12 HLEN PA IA BASE INCS UN ROOM CRL KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12.
  cbn [PNL.pn_read_span_v PMA.AN NADDR_A].
  pose proof (PGV8A.vo_src _ _ _ _ _ _ TOK M src x g OB PA) as (_ & _ & _ & _ & TB).
  exact (entry R M model K LBX FF LK Aw cr sp r len T OB src x g str sm TOK Rra RAok Rsp Rgp Rtp K0 FRM FRS OFR HLEN INCS UN STKSH FBS SRDS KONT CLV fx
           HH AM ASTK A10 A11 A12 PA IA BASE TB ROOM CRL).
Qed.

End WithHeap.
End PGSRVA3.
