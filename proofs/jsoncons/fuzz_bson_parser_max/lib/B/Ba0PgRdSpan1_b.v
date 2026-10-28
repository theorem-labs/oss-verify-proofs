(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnARdSpanP_b Ba0_code_rb0310_b0314_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b Ba0PgSrd1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRSA1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSSRA1.pot.
#[local] Abbreviation own2 := PGSSRA1.own2.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
#[local] Abbreviation perm_tb := (PGSSRA1.perm_tb L ar C HI HIok).
#[local] Abbreviation perm_tb_back := (PGSSRA1.perm_tb_back L ar C HI HIok).
#[local] Abbreviation ek_drop := (PGSSRA1.ek_drop L ar).
#[local] Abbreviation dk_drop := (PGSSRA1.dk_drop L ar).

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tx0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
(* [comment removed for export] *)
#[local] Abbreviation os := (PGSSRA1.os T).
#[local] Abbreviation ois := (PGSSRA1.ois T).
#[local] Abbreviation tb := (PGSSRA1.tb T).
#[local] Abbreviation lo := (PGSSRA1.lo T).
#[local] Abbreviation hi := (PGSSRA1.hi T).
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
(* [comment removed for export] *)
#[local] Abbreviation W0 := (PGSSRA1.W0 T).
#[local] Abbreviation lay := (PGSSRA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGSSRA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGSSRA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation inW_W0 := (PGSSRA1.inW_W0 T).
#[local] Abbreviation outside_W0 := (PGSSRA1.outside_W0 L ar HI T TOK).
#[local] Abbreviation frame_app := (PGSSRA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGSSRA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGSSRA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGSSRA1.stw_ok L ar C HI LY HIok T TOK).
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

Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).
(* [comment removed for export] *)
Definition saves9 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
  /\ L5.u64_at RSEGS M (S - 72) (U 23).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition memrel (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LBX FF S 24576 W0 M0 M /\ L5SAR.dk L ar LBX FF S 24576 M0 M /\ L5CA.astk ar M S 24576.
(* [comment removed for export] *)
Definition fields_eq (src : PM.srcst) (tx : PM.vstr) (tg : Z) : Prop := True.
Definition st_ok (M : word -> option byte) (model : Model) (src : PM.srcst) (tx : PM.vstr) (tg : Z) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  memrel M /\ saves9 M /\ PGS.tw_at T M src tx tg OB /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
  /\ PMSTA.base_okA RSEGS AD M /\ PM.tb_ok tx tg
  /\ ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
  /\ incl LK LK0 /\ incl Aw0 Aw
  /\ PMSPA.credit_le (pot L ar tx tg) cr /\ PMSPA.credit_keep cr0 cr (pot L ar tx0 tg0) (pot L ar tx tg).
(* [comment removed for export] *)
Definition bregs (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 80) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 tb
  /\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 19) = Z_to_bv 64 (os + 288) /\ getr R (reg 21) = Z_to_bv 64 2147450880
  /\ getr R (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ kept_rs R.

Lemma unread_nn M model src tx tg sm cr LK Aw : st_ok M model src tx tg sm cr LK Aw ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using TOK.
  intros (_ & _ & PA & IA & _).
  destruct (tsrc M src tx tg PA) as ((_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish_rs (fx : FPState) R M model src tx tg sm cr LK Aw (ptr n : Z) :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  getr R (reg 8) = Z_to_bv 64 (U 8) -> getr R (reg 9) = Z_to_bv 64 (U 9) -> getr R (reg 18) = Z_to_bv 64 (U 18) ->
  getr R (reg 19) = Z_to_bv 64 (U 19) -> getr R (reg 20) = Z_to_bv 64 (U 20) -> getr R (reg 21) = Z_to_bv 64 (U 21) ->
  getr R (reg 22) = Z_to_bv 64 (U 22) -> getr R (reg 23) = Z_to_bv 64 (U 23) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 ptr -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src ++ PM.vs_own tx ++ OB) ptr n \/ (tb + 1 <= ptr /\ ptr + n <= tb + 24)) ->
  L5.defined M ptr n -> PMSPA.accA M ptr n -> st_ok M model src tx tg sm cr LK Aw -> fields_eq src tx tg -> PMSP.src_step src0 src sm0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb501c M model) K.
Proof using All.
  intros E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 KP E10 E11 Hn Hn2 LOC DEF ACC ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK)
         _ STEP.
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xb501c r W_b36ec HH AM F_b36ec eq_refl D_b36ec RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  apply (KONT fx R M model1 LK Aw src tx tg sm cr ptr n); try assumption.
  - apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx. cbn in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
    apply KP. destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; cbn; auto 12.
  - change (PMSPA.pm_scr 6) with 24576. apply (L5SAR.ahpres_of L ar LBX FF S 24576 _ M0 M EK); [destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma callee_mem M M' (BX : list (Z * Z)) scr' (W' : list L5.range) :
  memrel M -> saves9 M -> 0 <= scr' -> 80 + scr' <= 24576 -> ar_stack_top ar <= 2 ^ 47 ->
  L5CA.ahpres L ar (BX ++ LBX) FF (S - 80) scr' W' M M' ->
  (forall a, aclient L ar LBX FF S 24576 a -> L5.outside W0 a -> L5.outside W' a) -> (forall a, S - 80 <= a < S -> L5.outside W' a) ->
  memrel M' /\ saves9 M' /\ L5SAR.ek L ar LBX FF S 24576 W0 M M'.
Proof using All.
  intros (EK & DK & STK) SV Hs Hs2 TOP HP HW HWS.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M').
  { apply (L5SAR.ek_callee L ar LBX BX FF [] S 24576 (S - 80) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
  assert (DKn : L5SAR.dk L ar LBX FF S 24576 M M') by (apply (L5SAR.dk_callee L ar LBX BX FF [] S 24576 (S - 80) scr' W' M M' HP); lia).
  assert (KEEPS : forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
  { intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
    intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar (BX ++ LBX) FF (S - 80) scr' i); lia.
    - apply HWS. lia. }
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M' EK EKn).
  - exact (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M' DK DKn).
  - apply (PMKA.astk_after_ahpres L ar _ FF M M' S 24576 (S - 80) scr' W' STK HP); lia.
  - split; [|exact EKn]. destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
    repeat split; (apply KEEPS; [lia| assumption]).
Qed.

(* [comment removed for export] *)
Lemma centry (R : bvmap 5 word) M model src tx tg sm cr LK Aw (X h : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept_rs R -> st_ok M model src tx tg sm cr LK Aw -> 1 <= h <= 5 ->
  PMSPA.entryA AD L ar R M (S - 80) X h /\ PGSA.ffroomB PNRA.FCB h FF LK /\ PMSPA.ffrsA FF (S - 80).
Proof using All.
  intros A1 RAX A2 KP SO Hh.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  assert (STKr : L5CA.astk ar M (S - 80) (PMSPA.pm_scr h)).
  { apply (L5SAR.astk_sub ar M M S 24576 80 (PMSPA.pm_scr h) STK (fun _ Y => Y)); unfold PMSPA.pm_scr; [lia|lia|lia|].
    replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof (wapp_W0 _ _ _ _ _ _ HH) as WAPP0.
  assert (STKSH : shadow_zero M (S - 80 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8)).
  { assert (M8a : (S - 24576) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 24576) with (S + (-1536) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (S - 80 - PMSPA.pm_scr h) mod 8 = 0).
    { apply PMKA.mod16_8'. unfold PMSPA.pm_scr. replace (S - 80 - (12288 + 2048 * h)) with (S + (-(773 + 128 * h)) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    assert (G8 : PMSPA.pm_scr h / 8 = 1536 + 256 * h).
    { unfold PMSPA.pm_scr. replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite G8. unfold PMSPA.pm_scr in M8b |- *.
    apply (PMKA.shadow_zero_sub M (S - 24576) 3072); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKA.stksh_keepA L ar LBX FF S 24576 W0 M0 M EK WAPP0 (S - 24576) 3072); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
  assert (FRM : PGSA.ffroomB PNRA.FCB h FF LK) by (apply (PGTKA.ffroom_incl PNRA.FCB 6 h FF LK0 LK FRM0 ILK NDF); lia).
  split; [|split; [exact FRM| intros f Hf; specialize (FRS f Hf); lia]].
  unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
  split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
  split; [exact STKr| exact STKSH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_fill (fx : FPState) R M model src tx tg sm cr LK Aw (X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 (PM.sr_qc src) -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  st_ok M model src tx tg sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
     (PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
     PMSP.src_step src src sm sm' ->
     st_ok M' model' src tx tg sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb29f8 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 SO NEXT.
  destruct (centry R M model src tx tg sm cr LK Aw X 3 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (left; reflexivity).
  pose proof FBS as SR. unfold PGSA.fill_buffer_specG, PGSA.src_specG in SR. cbn [pa_fill_buffer AD PMA.AD ADDR_A] in SR.
  apply (SR (PGSA.src_of_tw T tx tg) (stw_ok tx tg) fx R M model K (PM.vs_own tx ++ OB) LBX FF LK Aw cr (S - 80) X src str sm []);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGSA.src_of_tw].
  { replace (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) with (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) by (rewrite <- !app_assoc; reflexivity). exact HH. }
  { exact AM. } { exact K0. } { exact ENT. } { exact FRM. } { exact FRS'. } { exact OFR. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGSA.fill_args. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11| exact A12]. }
  { reflexivity. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. } { exact BASE. } { exact INCS. }
  intros fx' R' M' model' LK' Aw' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSPA.pm_scr 3) with 18432 in HP. rewrite app_nil_r in HP.
  destruct RES as (-> & c & Y10 & Hc & G & ST0 & ST2).
  rewrite L5K.rl10 in Y10.
  apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G ST0 ST2 STEP).
  replace (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) with ((PM.src_own src ++ PM.vs_own tx ++ OB) ++ LBX) in HP by (rewrite <- !app_assoc; reflexivity).
  destruct (callee_mem M M' (PM.src_own src ++ PM.vs_own tx ++ OB) 18432 (PGS.W_srcG os ois src) MR SV ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & EKn).
  { intros a CA OW r0 Hr0 Hin. unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - apply (OW r0); [unfold PGSSRA1.W0; apply in_or_app; left; exact Hr0| exact Hin].
    - (* [comment removed for export] *)
      apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PM.vs_own tx ++ OB) LBX FF LK cr Aw M _ (PM.sr_qc src) PM.CHUNK a S 24576 ltac:(rewrite <- !app_assoc; exact HH));
        [left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA]. }
  { intros a Ha r0 Hr0 Hin. unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - exact (outside_W0 a ltac:(lia) r0 ltac:(unfold PGSSRA1.W0; apply in_or_app; left; exact Hr0) Hin).
    - destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|].
  split; [replace (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) with (PM.src_own src ++ (PM.vs_own tx ++ OB) ++ LBX) by (rewrite <- !app_assoc; reflexivity); exact HH'|].
  split; [exact AM'|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_srd (fx : FPState) R M model src tx tg sm cr LK Aw (X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 tb -> getr R (reg 12) = Z_to_bv 64 len ->
  st_ok M model src tx tg sm cr LK Aw -> PM.unread src sm < 2 ^ 26 -> PM.vs_size tx + PM.unread src sm < 2 ^ 26 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
          (src' : PM.srcst) (tx' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= len ->
     PMSP.consumed src src' sm sm' = d -> PM.vs_size tx' = PM.vs_size tx + d ->
     PMSP.src_step src src' sm sm' ->
     st_ok M' model' src' tx' tg' sm' cr' LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb50e0 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 SO UN UNS NEXT.
  destruct (centry R M model src tx tg sm cr LK Aw X 5 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  pose proof SRDS as SR. unfold PGSA.srd_read_specG in SR. cbn [pa_srd_read AD PMA.AD ADDR_A] in SR.
  apply (SR T TOK fx R M model K OB LBX FF LK Aw cr (S - 80) X len src tx tg str sm HH AM K0 ENT FRM FRS' OFR).
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5SAR.r11. exact A11. }
  { rewrite L5SAR.r12. exact A12. }
  { exact Hlen. }
  { exact PA. } { exact IA. } { exact BASE. } { exact INCS. } { exact UN. } { exact UNS. } { exact CRL. }
  intros fx' R' M' model' LK' Aw' src' tx' tg' sm' cr' d RP Y10 Hd CONS SZ PA' IA' STEP HP CK MRT' ILK' IAW' AM' HH'.
  change (PMSPA.pm_scr 5) with 22528 in HP.
  rewrite L5K.rl10 in Y10.
  apply (NEXT fx' R' M' model' LK' Aw' src' tx' tg' sm' cr' d RP Y10 Hd CONS SZ STEP).
  pose proof (tsrc M' src' tx' tg' PA') as (_ & _ & _ & _ & TB').
  destruct (callee_mem M M' [] 22528 W0 MR SV ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & EKn).
  { intros a _ O. exact O. }
  { intros a Ha. apply outside_W0. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TB'|]. split; [exact HH'|]. split; [exact AM'|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split.
  - unfold PMSPA.credit_keep, PMSPA.credit_le, PMSP.credit_keep, PMSP.credit_le in *. destruct CRL as (CL1 & CL2). destruct CK as (CK1 & CK2). split; lia.
  - unfold PMSPA.credit_keep, PMSPA.credit_le, PMSP.credit_keep, PMSP.credit_le in *. destruct CRK as (CR1 & CR2). destruct CK as (CK1 & CK2). split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vpack M model src tx tg sm cr LK Aw :
  st_ok M model src tx tg sm cr LK Aw ->
  let H := ahid Aw model in let MV := mrestrict H M in
  L5.img_clear MV 65536 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1
  /\ (140735332487248 <= S <= 2 ^ 47 /\ S mod 16 = 0 /\ L5.writable RSEGS MV (S - 80) 80)
  /\ (forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS MV (S - k) v)
  /\ (6905856 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis H a n)
  /\ (6905856 <= tb <= 140737488355304 /\ tb mod 8 = 0 /\ (2147446784 + 17592186048512 <= tb \/ tb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (tb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV tb 24 /\ (forall a n, tb <= a -> a + n <= tb + 24 -> L5A.avis H a n)
  /\ os + 296 <= S - 80 /\ tb + 24 <= S - 80 /\ PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF tb 24.
Proof using All.
  intros (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) H MV.
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  pose proof (tsrc M src tx tg PA) as (PSF & PNI & PD & VS & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 24576 80 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK cr Aw M model os _ _ src S 24576 HH AO ltac:(lia) PSF PNI STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGTKA.tb_visG L ar C HI LY HIok _ FF LK cr Aw M model tb tx HH AT ltac:(lia) VS)
    as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & _ & TFS1 & TFS2).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VIS & _).
  split; [exact V0|]. split; [exact V1|]. split; [exact V2|].
  split; [split; [lia| split; [exact A16| exact V3]]|].
  split.
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis H M (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  split; [split; [lia| split; [exact O8| exact OBIG]]|]. split; [exact OZ|]. split; [exact OW|]. split; [exact OAV|].
  split; [split; [lia| split; [exact T8| exact TBIG]]|]. split; [exact TZ|]. split; [exact TW|]. split; [exact TAV|].
  split; [lia|]. split; [lia|]. split; [exact AO| exact AT].
Qed.

End Call.
End WithHeap.
End PGSRSA1.
