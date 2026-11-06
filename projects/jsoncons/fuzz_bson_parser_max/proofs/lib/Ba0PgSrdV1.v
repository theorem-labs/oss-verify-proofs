(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs PmSpecsA PmSpecsAX PnSpecsAa
     PmModelFactsA PnStepA PmStep PmTxtKit2 PnASrcKit PnASrcRead1 PnAReset1 Ba0_code_b3dd8_b3ddc PgSrc PgSrcA PgSrcKitA PgTxtKitA PgV8 PgV8A PgV8KitA PnLayout PnRunA Ba0PgVw1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSVA1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGVWA1.pot.
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).
#[local] Abbreviation own2 := PGVWA1.own2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma room_cases a0 j c : 0 <= j -> c = a0 * 2 ^ j -> 1 <= a0 <= 2 ^ 14 -> 2 ^ 26 < c ->
  (8193 <= a0 /\ c = a0 * 8192) \/ 2 ^ 26 + 2 ^ 14 <= c.
Proof.
  intros Hj Hc Ha HC.
  destruct (Z_lt_le_dec j 13) as [Hlt|Hge].
  - exfalso. assert (P : 2 ^ j <= 2 ^ 12) by (apply Z.pow_le_mono_r; Lia.lia).
    assert (c <= 2 ^ 14 * 2 ^ 12) by (rewrite Hc; apply Z.mul_le_mono_nonneg; Lia.lia). change (2 ^ 14 * 2 ^ 12) with (2 ^ 26) in H. Lia.lia.
  - destruct (Z.eq_dec j 13) as [->|Hne].
    + left. change (2 ^ 13) with 8192 in Hc. split; [|exact Hc]. rewrite Hc in HC. Lia.lia.
    + right. assert (E : 2 ^ j = 2 ^ 14 * 2 ^ (j - 14)) by (rewrite <- Z.pow_add_r by Lia.lia; f_equal; Lia.lia).
      assert (T1 : 1 <= 2 ^ (j - 14)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; Lia.lia).
      set (t := 2 ^ (j - 14)) in *. rewrite E in Hc.
      assert (M1 : 4097 <= a0 * t) by Lia.nia. Lia.nia.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
#[local] Abbreviation perm_v8 := (PGVWA1.perm_v8 L ar C HI HIok).
#[local] Abbreviation perm_v8_back := (PGVWA1.perm_v8_back L ar C HI HIok).
#[local] Abbreviation ek_drop := (PGVWA1.ek_drop L ar).
#[local] Abbreviation dk_drop := (PGVWA1.dk_drop L ar).

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGV8.vowner) (OB : list (Z * Z)) (src0 : PM.srcst) (x0 : PGV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
(* [comment removed for export] *)
#[local] Abbreviation os := (PGVWA1.os T).
#[local] Abbreviation ois := (PGVWA1.ois T).
#[local] Abbreviation tb := (PGVWA1.tb T).
#[local] Abbreviation lo := (PGVWA1.lo T).
#[local] Abbreviation hi := (PGVWA1.hi T).
Hypothesis TOK : PGV8A.vowner_ok RSEGS AD L ar HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis SZ0 : PGV8.v8_size x0 = 0.
Hypothesis ROOM0 : PGV8.v8_room x0 (PM.unread src0 sm0).
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PGV8A.vu8_resize_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_resize PMA.AN).
Hypothesis SRD : PGSA.src_read_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis FBT : PGSA.fill_buffer_tb_specG RSEGS AD L ar HI PNRA.FCB.
(* [comment removed for export] *)
#[local] Abbreviation W0 := (PGVWA1.W0 T).
#[local] Abbreviation lay := (PGVWA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGVWA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGVWA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation inW_W0 := (PGVWA1.inW_W0 T).
#[local] Abbreviation outside_W0 := (PGVWA1.outside_W0 L ar HI T TOK).
#[local] Abbreviation frame_app := (PGVWA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGVWA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGVWA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGVWA1.stw_ok L ar C HI LY HIok T TOK).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (x' : PGV8.v8) (g' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PGV8.v8_size x' = d ->
  (d = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at T M' src' x' g' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar x0 g0) (pot L ar x' g') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).
(* [comment removed for export] *)
Definition saves13 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
  /\ L5.u64_at RSEGS M (S - 72) (U 23) /\ L5.u64_at RSEGS M (S - 80) (U 24) /\ L5.u64_at RSEGS M (S - 88) (U 25) /\ L5.u64_at RSEGS M (S - 96) (U 26)
  /\ L5.u64_at RSEGS M (S - 104) (U 27).
Definition locals (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 160) (tb + 8) /\ L5.u64_at RSEGS M (S - 152) len /\ L5.u64_at RSEGS M (S - 144) ((os + 256) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M (S - 136) (os + 256) /\ L5.u64_at RSEGS M (S - 128) ((os + 240) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M (S - 120) (os + 240) /\ L5.u64_at RSEGS M (S - 112) (os + 288).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4]%nat -> getr R (reg x) = getr R0 (reg x).
(* [comment removed for export] *)
Definition memrel (M : word -> option byte) : Prop :=
  L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M0 M /\ L5SAR.dk L ar (OB ++ LBX) FF S 22528 M0 M /\ L5CA.astk ar M S 22528.
(* [comment removed for export] *)
Definition fields_eq (src : PM.srcst) (x : PGV8.v8) (g : Z) : Prop := True.
(* [comment removed for export] *)
Definition vroom (x : PGV8.v8) : Prop :=
  match x with
  | PGV8.V8Null => True
  | PGV8.V8Blk _ _ c => exists a0 j, 0 <= j /\ c = a0 * 2 ^ j /\ 1 <= a0 <= 2 ^ 14
                        /\ (a0 + PM.unread src0 sm0 <= 2 ^ 26 \/ (a0 <= len /\ (a0 = 2 ^ 14 \/ a0 = len)))
  end.
(* [comment removed for export] *)
Definition acct (src : PM.srcst) (x : PGV8.v8) (g : Z) (sm : PM.strm) (w : Z) : Prop :=
  PMSP.consumed src0 src sm0 sm = len - w /\ PGV8.v8_size x = len - w /\ PMSP.src_step src0 src sm0 sm
  /\ vroom x /\ (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x).
Definition st_ok (M : word -> option byte) (model : Model) (src : PM.srcst) (x : PGV8.v8) (g : Z) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  memrel M /\ saves13 M /\ locals M /\ PGV8.vw_at T M src x g OB /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
  /\ PMSTA.base_okA RSEGS AD M /\ PGV8.v8_ok x g
  /\ ri_inv HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
  /\ incl LK LK0 /\ incl Aw0 Aw
  /\ PMSPA.credit_le (pot L ar x g) cr /\ PMSPA.credit_keep cr0 cr (pot L ar x0 g0) (pot L ar x g).
(* [comment removed for export] *)
Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 160) /\ getr R (reg 8) = Z_to_bv 64 2147450880 /\ getr R (reg 9) = Z_to_bv 64 tb
  /\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 19) = Z_to_bv 64 (os + 272) /\ getr R (reg 20) = Z_to_bv 64 ((tb + 8) / 8 + 2147450880)
  /\ getr R (reg 21) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ getr R (reg 23) = Z_to_bv 64 ((os + 272) / 8 + 2147450880)
  /\ getr R (reg 26) = Z_to_bv 64 (tb / 8 + 2147450880) /\ getr R (reg 27) = Z_to_bv 64 w /\ kept_rs R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish (fx : FPState) R M model src x g sm cr LK Aw (w : Z) :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall xq, In xq [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg xq) = Z_to_bv 64 (U xq)) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 (len - w) -> 0 <= w <= len ->
  st_ok M model src x g sm cr LK Aw -> acct src x g sm w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3e28 M model) K.
Proof using All.
  intros E1 E2 ES KP E10 Hw ((EK & DK & STK) & _ & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) (CONS & SZ & STEP & VR & _).
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSP.cfg.
  apply (PMASK.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xb3e28 r W_b3dd8 HH AM F_b3dd8 eq_refl D_b3dd8 RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  apply (KONT fx R M model1 LK Aw src x g sm cr (len - w)); try assumption; try lia.
  - apply L5SAR.preserved_by_index. intros xr Hx. unfold L5SAR.cs_all in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    rewrite (ES xr) by (cbn in Hx; cbn; tauto). unfold U. apply Z_to_bv_bv_unsigned.
  - (* [comment removed for export] *)
    intros Ed. assert (Hw0 : w = 0) by lia. subst w.
    pose proof STEP as (_ & _ & _ & _ & UNR). unfold PMSP.consumed in CONS.
    clear - CONS UNR VR UN0 Hlen. destruct x as [|b n c]; [exact I|]. cbn in VR |- *. destruct VR as (a0 & j & Hj & Hc & Ha0 & ALT).
    exists a0, j. split; [exact Hj|]. split; [exact Hc|]. split; [exact Ha0|]. destruct ALT as [X|[X _]]; Lia.lia.
  - change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M).
    + exact (ek_drop OB LBX FF S 22528 W0 M0 M EK).
    + destruct STK as (_ & _ & _ & _ & D & _); exact D.
    + exact (dk_drop OB LBX FF S 22528 M0 M DK).
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma callee_mem M M' (BX : list (Z * Z)) scr' (W' : list L5.range) :
  memrel M -> saves13 M -> locals M -> 0 <= scr' -> 160 + scr' <= 22528 -> ar_stack_top ar <= 2 ^ 47 ->
  L5CA.ahpres L ar (BX ++ (OB ++ LBX)) FF (S - 160) scr' W' M M' ->
  (forall a, aclient L ar (OB ++ LBX) FF S 22528 a -> L5.outside W0 a -> L5.outside W' a) -> (forall a, S - 160 <= a < S -> L5.outside W' a) ->
  memrel M' /\ saves13 M' /\ locals M' /\ L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M M'.
Proof using All.
  intros (EK & DK & STK) SV LC Hs Hs2 TOP HP HW HWS.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (EKn : L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M M').
  { apply (L5SAR.ek_callee L ar (OB ++ LBX) BX FF [] S 22528 (S - 160) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
  assert (DKn : L5SAR.dk L ar (OB ++ LBX) FF S 22528 M M') by (apply (L5SAR.dk_callee L ar (OB ++ LBX) BX FF [] S 22528 (S - 160) scr' W' M M' HP); lia).
  assert (KEEPS : forall k v, 8 <= k <= 160 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
  { intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
    intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar (BX ++ (OB ++ LBX)) FF (S - 160) scr' i); lia.
    - apply HWS. lia. }
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar (OB ++ LBX) FF S 22528 W0 M0 M M' EK EKn).
  - exact (L5SAR.dk_trans L ar (OB ++ LBX) FF S 22528 M0 M M' DK DKn).
  - apply (PMKA.astk_after_ahpres L ar _ FF M M' S 22528 (S - 160) scr' W' STK HP); lia.
  - split; [|split; [|exact EKn]].
    + destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
      repeat split; (apply KEEPS; [lia| assumption]).
    + destruct LC as (L1 & L2 & L3 & L4 & L5' & L6 & L7).
      repeat split; (apply KEEPS; [lia| assumption]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma centry (R : bvmap 5 word) M model src x g sm cr LK Aw (X h : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 160) -> kept_rs R -> st_ok M model src x g sm cr LK Aw -> 1 <= h <= 4 ->
  PMSPA.entryA AD L ar R M (S - 160) X h /\ PGSA.ffroomB PNRA.FCB h FF LK /\ PMSPA.ffrsA FF (S - 160).
Proof using All.
  intros A1 RAX A2 KP SO Hh.
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  assert (STKr : L5CA.astk ar M (S - 160) (PMSPA.pm_scr h)).
  { apply (L5SAR.astk_sub ar M M S 22528 160 (PMSPA.pm_scr h) STK (fun _ Y => Y)); unfold PMSPA.pm_scr; [lia|lia|lia|].
    replace (S - 160) with (S + (-10) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  pose proof (wapp_W0 _ _ _ _ _ _ HH) as WAPP0.
  assert (STKSH : shadow_zero M (S - 160 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8)).
  { assert (M8a : (S - 22528) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 22528) with (S + (-1408) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (S - 160 - PMSPA.pm_scr h) mod 8 = 0).
    { apply PMKA.mod16_8'. unfold PMSPA.pm_scr. replace (S - 160 - (12288 + 2048 * h)) with (S + (-(778 + 128 * h)) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    assert (G8 : PMSPA.pm_scr h / 8 = 1536 + 256 * h).
    { unfold PMSPA.pm_scr. replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite G8. unfold PMSPA.pm_scr in M8b |- *.
    apply (PMKA.shadow_zero_sub M (S - 22528) 2816); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKA.stksh_keepA L ar (OB ++ LBX) FF S 22528 W0 M0 M EK WAPP0 (S - 22528) 2816); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
  assert (FRM : PGSA.ffroomB PNRA.FCB h FF LK) by (apply (PGTKA.ffroom_incl PNRA.FCB 5 h FF LK0 LK FRM0 ILK NDF); lia).
  split; [|split; [exact FRM| intros f Hf; specialize (FRS f Hf); lia]].
  unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
  split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
  split; [exact STKr| exact STKSH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_ok_now src x g sm w nn M :
  PGV8.vw_at T M src x g OB -> vroom x -> (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x) -> len - w <= PGV8.v8_size x ->
  len - w <= PM.unread src0 sm0 - PM.unread src sm -> 0 <= w <= len -> 0 <= PM.unread src sm ->
  (nn <= PGV8.v8_cap x \/ nn = (len - w) + Z.min w PM.CHUNK) ->
  PGV8.v8_grow_ok x nn /\ nn <= 2 ^ 27.
Proof using TOK UN0 Hlen.
  intros AT VR MIN SZ CONS Hw HU Hnn.
  destruct (tsrc M src x g AT) as (_ & _ & _ & VS & _). unfold PGV8.v8_grow_ok.
  destruct x as [|b n c]; cbn in SZ, VR, MIN, Hnn |- *.
  - destruct Hnn as [H| ->]; [split; [left; exact H| Lia.lia]|]. unfold PM.CHUNK. split; [right; split; Lia.lia| Lia.lia].
  - destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _).
    destruct (Z_lt_le_dec c nn) as [GT|LE]; [|split; [left; exact LE| Lia.lia]].
    destruct Hnn as [H| ->]; [exfalso; Lia.lia|].
    assert (NB : len - w + Z.min w PM.CHUNK < 2 ^ 26 + 2 ^ 14 /\ len - w + Z.min w PM.CHUNK <= len) by (unfold PM.CHUNK; Lia.lia).
    split; [|Lia.lia]. right. split; [|Lia.lia].
    destruct (Z_lt_le_dec (2 ^ 26) c) as [BIG|OK]; [|exact OK]. exfalso.
    destruct VR as (a0 & j & Hj & Hc & Ha0 & ALT).
    destruct (room_cases a0 j c Hj Hc Ha0 BIG) as [(A1 & A2)|A3]; [|Lia.lia].
    destruct ALT as [X|(X1 & [X2|X2])].
    + assert (8193 * 8193 <= 8193 * a0) by Lia.nia. unfold PM.CHUNK in *. Lia.nia.
    + rewrite X2 in A2. change (2 ^ 14 * 8192) with (2 ^ 27) in A2. Lia.lia.
    + subst a0. Lia.nia.
Qed.

Lemma vroom_after src x g w nn M M' x' :
  PGV8.vw_at T M src x g OB -> vroom x -> (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x) -> len - w <= PGV8.v8_size x -> 0 <= w <= len ->
  (nn <= PGV8.v8_cap x \/ nn = (len - w) + Z.min w PM.CHUNK) ->
  v8_atA M' tb x' -> PGV8.v8_size x' = nn ->
  (PGV8.v8_cap x' = PGV8.v8_cap x \/ PGV8.v8_cap x' = Z.max (2 * PGV8.v8_cap x) nn) ->
  vroom x'.
Proof using TOK Hlen.
  intros AT VR MIN SZ Hw Hnn VS' SZ' CL.
  destruct (tsrc M src x g AT) as (_ & _ & _ & VS & _).
  destruct x' as [|b' n' c']; [exact I|]. cbn in SZ', CL |- *. subst n'.
  destruct VS' as (_ & _ & _ & _ & _ & G1 & G2 & _).
  destruct x as [|b n c]; cbn in SZ, VR, MIN, Hnn, CL.
  - (* [comment removed for export] *)
    assert (E : c' = nn) by Lia.lia.
    destruct Hnn as [H|H]; [Lia.lia|]. assert (Hw' : w = len) by Lia.lia. subst w. rewrite Z.sub_diag, Z.add_0_l in H.
    exists nn, 0. change (2 ^ 0) with 1. unfold PM.CHUNK in H. split; [Lia.lia|]. split; [Lia.lia|]. split; [Lia.lia|]. right. split; Lia.lia.
  - destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _). destruct VR as (a0 & j & Hj & Hc & Ha0 & ALT).
    destruct CL as [E|E]; [exists a0, j; subst c'; split; [Lia.lia|]; split; [Lia.lia|]; split; [Lia.lia| exact ALT]|].
    destruct (Z_lt_le_dec (2 * c) nn) as [EV|DB].
    + (* [comment removed for export] *)
      destruct Hnn as [H|H]; [Lia.lia|]. destruct MIN as [-> |MN]; [|Lia.lia].
      rewrite Z.sub_diag, Z.add_0_l in H. unfold PM.CHUNK in H.
      exists nn, 0. change (2 ^ 0) with 1. split; [Lia.lia|]. split; [Lia.lia|]. split; [Lia.lia|]. right. split; Lia.lia.
    + exists a0, (j + 1). rewrite Z.pow_add_r by Lia.lia. change (2 ^ 1) with 2. split; [Lia.lia|]. split; [Lia.lia|]. split; [Lia.lia|]. exact ALT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_resize (fx : FPState) R M model src x g sm cr LK Aw (nn X w : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 160) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 tb -> getr R (reg 11) = Z_to_bv 64 nn -> 0 <= nn ->
  (nn <= PGV8.v8_cap x \/ nn = (len - w) + Z.min w PM.CHUNK) ->
  vroom x -> (w = len \/ Z.min w PM.CHUNK <= PGV8.v8_cap x) -> len - w <= PGV8.v8_size x -> len - w <= PM.unread src0 sm0 - PM.unread src sm ->
  0 <= w <= len -> 0 <= PM.unread src sm ->
  st_ok M model src x g sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (x' : PGV8.v8) (g' : Z) (cr' : credit),
     regs_preserved R R' -> PGV8.v8_size x' = nn -> PGV8.v8_cap x <= PGV8.v8_cap x' -> vroom x' ->
     (nn <= PGV8.v8_cap x -> PGV8.v8_own x' = PGV8.v8_own x /\ g' = g) ->
     st_ok M' model' src x' g' sm cr' LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3e90 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 Hnn0 Hnn VR MIN SZW CONSW Hw HU SO NEXT.
  destruct (centry R M model src x g sm cr LK Aw X 1 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (tsrc M src x g PA) as (PSF & PNI & PD & VS & _).
  pose proof (PGV8KA.v8_visG L ar C HI LY HIok _ FF LK cr Aw M model tb x HH AT ltac:(lia) VS) as ((T1 & T8 & TBIG) & _ & _ & _ & _ & _ & TFS1 & TFS2).
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, TFS1, TFS2.
  destruct (grow_ok_now src x g sm w nn M PA VR MIN SZW CONSW Hw HU Hnn) as (GOK & N27).
  set (LB' := PM.src_own src ++ OB ++ LBX).
  pose proof (perm_v8 src x OB LBX FF LK cr Aw M _ HH) as HH'. fold LB' in HH'.
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) LB') by (unfold LB', PM.src_own; left; reflexivity).
  destruct (BRB _ ltac:(left; reflexivity)) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  pose proof RSZ as RS. unfold PGV8A.vu8_resize_spec, PGV8A.vu8_grow_spec in RS. cbn [PNL.pn_vu8_resize PMA.AN NADDR_A] in RS.
  apply (RS fx R M model K LB' FF LK Aw cr tb nn (S - 160) X g x HH' AM K0 ENT FRM FRS').
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5SAR.r11. exact A11. }
  { exact AT. } { exact T8. } { destruct VS as (_ & VC & _). exact VC. } { exact VS. } { exact TBOK. } { lia. } { exact GOK. } { exact CRL. }
  intros fx' R' M' model' LK' Aw' x' g' cr' RP VS' SZ TB' CAPLE OWN CL HP CK MRT' ILK' IAW' AM' HH2.
  change (PMSPA.pm_scr 1) with 14336 in HP.
  apply (NEXT fx' R' M' model' LK' Aw' x' g' cr' RP SZ CAPLE (vroom_after src x g w nn M M' x' PA VR MIN SZW Hw Hnn VS' SZ CL)).
  { intros LE. destruct (OWN ltac:(rewrite SZ; exact LE)) as (O1 & _ & O3). split; [exact O1| exact O3]. }
  assert (HPc : L5CA.ahpres L ar (PM.src_own src ++ (OB ++ LBX)) FF (S - 160) 14336 [(tb, 24)] M M') by exact HP.
  destruct (callee_mem M M' _ 14336 [(tb, 24)] MR SV LC ltac:(lia) ltac:(lia) TOP HPc) as (MR' & SV' & LC' & EKn).
  { intros a _ Oq r0 [<-|[]] Hin. apply (Oq (tb, 24)); [unfold PGVWA1.W0; apply in_or_app; right; left; reflexivity| exact Hin]. }
  { intros a Ha r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. }
  set (Wt := [(tb, 24)]).
  assert (WAPPt : PMKA.wapp Wt) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]).
  pose proof HP as (EKr & DSr & DKr).
  assert (EKt : L5SAR.ek L ar LB' FF (S - 160) 14336 Wt M M') by exact EKr.
  assert (BRB' : forall b, In b LB' -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47).
  { intros b Hb. apply BRB. unfold LB' in Hb. rewrite !in_app_iff in Hb. rewrite !in_app_iff. clear - Hb. tauto. }
  (* [comment removed for export] *)
  assert (SF' : PM.src_fields_at RSEGS PMSPA.accA M' os ois (ois + 16) src).
  { apply (PGSKA.src_fields_keepG M M' os ois (ois + 16) src PSF); [clear - LAY; lia| clear - LAY; lia| | |].
    - apply (PMKA.agA_obj L ar LB' FF (S - 160) 14336 Wt M M' EKt WAPPt FRB os 296 AO). intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hi Hin LAY. lia.
    - apply (PMASK.agsh_blk L ar LB' FF (S - 160) 14336 Wt M M' _ _ EKt WAPPt QIN); lia.
    - apply (PMASK.defined_dk L ar LB' FF (S - 160) 14336 M M' _ _ DKr); [intros i Hi; apply (L5SAR.block_client L ar LB' FF (S - 160) 14336 _ _ i QIN Hi)| lia| lia|].
      destruct PSF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DCH & _). exact DCH. }
  assert (HPw : L5CA.ahpres L ar (OB ++ LBX) FF (S - 160) 14336 (PGS.W_srcfG os ois ++ [(tb, 24)] ++ []) M M').
  { apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF (S - 160) 14336 _ M M').
    - apply (L5SAR.ek_callee L ar (OB ++ LBX) (PM.src_own src) FF [] (S - 160) 14336 (S - 160) 14336 _ _ M M' HPc); [lia| lia|].
      intros a _ Oq r0 [<-|[]] Hin. apply (Oq (tb, 24)); [apply in_or_app; right; left; reflexivity| exact Hin].
    - exact DSr.
    - apply (L5SAR.dk_callee L ar (OB ++ LBX) (PM.src_own src) FF [] (S - 160) 14336 (S - 160) 14336 _ M M' HPc); lia. }
  assert (PA' : PGV8.vw_at T M' src x' g' OB).
  { exact (tw_xferA M M' src src x x' g g' LK cr Aw (vml_of model) (S - 160) 14336 [] PA HH HPw ltac:(constructor) SF' eq_refl VS' TB'). }
  assert (IA' : PM.iss_at RSEGS AD PMSPA.accA M' ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar LB' FF (S - 160) 14336 Wt M M' EKt WAPPt FRB BRB' _ _ _ AOI); [| | |exact IA].
    - intros xr Hx. unfold LB'. rewrite !in_app_iff. right; right. apply INCS. exact Hx.
    - intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hi Hin LAY. lia.
    - intros c n p E i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ p c tb 24 HH ltac:(rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity) AT); lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. destruct (frame_app _ _ _ _ _ _ HH). lia. }
  split; [exact TB'|]. split; [apply perm_v8_back; exact HH2|]. split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros xr Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros xr Hx; apply IAW'; apply IAW; exact Hx|].
  unfold PMSPA.credit_keep, PMSPA.credit_le, PMSP.credit_keep, PMSP.credit_le in *. destruct CRL as (CL1 & CL2). destruct CK as (CK1 & CK2). destruct CRK as (CR1 & CR2). split; split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vdst (x : PGV8.v8) (p k : Z) : Prop := exists b n c, x = PGV8.V8Blk b n c /\ b <= p /\ p + k <= b + n.

(* [comment removed for export] *)
Lemma call_srcread (fx : FPState) R M model src x g sm cr LK Aw (p k X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 160) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  1 <= k <= PM.CHUNK -> vdst x p k -> st_ok M model src x g sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= k ->
     PMSP.consumed src src' sm sm' = d -> (1 <= PM.sr_rem src -> 1 <= d) ->
     (d = 0 -> PM.sr_rem src' = 0 /\ PM.sm_st sm' = 2) -> PMSP.src_step src src' sm sm' ->
     st_ok M' model' src' x g sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xadae0 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
  destruct (centry R M model src x g sm cr LK Aw X 4 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (left; reflexivity).
  assert (DSTB : 0 <= p /\ p + k <= 2 ^ 47 /\ forall a, p <= a < p + k -> (tb <= a < tb + 24) \/ exists B m, In (B, m) (PM.src_own src ++ PGV8.v8_own x) /\ B <= a < B + m).
  { destruct DST as (q & n & c & E & D1 & D2).
    pose proof (tsrc M src x g PA) as (_ & _ & _ & VSd & _). rewrite E in VSd. destruct VSd as (_ & _ & _ & _ & _ & Hnc & _).
    assert (IN : In (q, c) (PM.src_own src ++ PGV8.v8_own x)) by (rewrite E; apply in_or_app; right; left; reflexivity).
    destruct (BRB (q, c) ltac:(rewrite own2; apply in_or_app; left; exact IN)) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
    split; [lia|]. split; [lia|]. intros a Ha. right. exists q, c. split; [exact IN| lia]. }
  destruct DSTB as (Dp0 & Dp1 & DIN).
  pose proof SRD as SR. unfold PGSA.src_read_specG, PGSA.src_specG in SR. cbn [pa_src_read AD PMA.AD ADDR_A] in SR.
  apply (SR (PGV8A.src_of_vw T x g) (stw_ok x g) fx R M model K (PGV8.v8_own x ++ OB) LBX FF LK Aw cr (S - 160) X src str sm [(p, k)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGV8A.src_of_vw].
  { replace (PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) with (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) by (rewrite <- !app_assoc; reflexivity). exact HH. }
  { exact AM. } { exact K0. } { exact ENT. } { exact FRM. } { exact FRS'. } { exact OFR. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGSA.read_args. exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
    unfold PGSA.dst_okG. right. cbn [PGS.ow_win PGV8A.src_of_vw]. split; [lia| exact DST]. }
  { unfold PMPS.read_W. exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK in Hk; lia| reflexivity]. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. } { exact BASE. } { exact INCS. }
  intros fx' R' M' model' LK' Aw' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSPA.pm_scr 4) with 20480 in HP.
  unfold PMPS.read_res in RES. destruct RES as (p' & k' & d & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & _ & POS & ZERO).
  assert (pk : p' = p /\ k' = k).
  { rewrite L5SAR.r11 in Y11. rewrite L5SAR.r12 in Y12. rewrite A11 in Y11. rewrite A12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
    unfold PM.CHUNK in Hk, Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
  destruct pk as (-> & ->).
  assert (QC : PM.sr_qc src' = PM.sr_qc src) by (destruct STEP as (E & _); exact E).
  rewrite L5K.rl10 in Y10.
  apply (NEXT fx' R' M' model' LK' Aw' src' sm' d RP Y10 Hd CONS POS ZERO STEP).
  replace (PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) with ((PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LBX)) in HP by (rewrite <- !app_assoc; reflexivity).
  destruct (callee_mem M M' (PM.src_own src ++ PGV8.v8_own x) 20480 (PGS.W_srcG os ois src ++ [(p, k)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
  { intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + apply (OW r0); [unfold PGVWA1.W0; apply in_or_app; left; exact Hr0| exact Hin].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) FF LK cr Aw M _ (PM.sr_qc src) PM.CHUNK a S 22528 ltac:(rewrite <- own2; exact HH));
          [apply in_or_app; left; left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha)].
      + apply (OW (tb, 24)); [unfold PGVWA1.W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X0].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) FF LK cr Aw M _ B m a S 22528 ltac:(rewrite <- own2; exact HH) HB Ha CA). }
  { intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + exact (outside_W0 a ltac:(lia) r0 ltac:(unfold PGVWA1.W0; apply in_or_app; left; exact Hr0) Hin).
      + destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha')]; [lia|].
      destruct (WB (B, m) ltac:(rewrite own2; apply in_or_app; left; exact HB)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|].
  split; [unfold PM.src_own; rewrite QC; replace ([(PM.sr_qc src, PM.CHUNK)] ++ PGV8.v8_own x ++ OB ++ LBX) with (PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) by (unfold PM.src_own; rewrite <- !app_assoc; reflexivity); exact HH'|].
  split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros xr Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros xr Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma call_fillv (fx : FPState) R M model src x g sm cr LK Aw (p X q0 n0 c0 : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 160) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  x = PGV8.V8Blk q0 n0 c0 -> q0 <= p -> p + PM.CHUNK <= q0 + n0 -> st_ok M model src x g sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0)) ->
     (PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2) ->
     PMSP.src_step src src sm sm' ->
     st_ok M' model' src x g sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb150c M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO NEXT.
  destruct (centry R M model src x g sm cr LK Aw X 3 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (left; reflexivity).
  assert (IN : In (q0, c0) (PM.src_own src ++ PGV8.v8_own x)) by (rewrite ETB; apply in_or_app; right; left; reflexivity).
  destruct (WB (q0, c0) ltac:(rewrite own2; apply in_or_app; left; exact IN)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
  assert (Hnc : 0 <= n0 <= c0) by (pose proof (tsrc M src x g PA) as (_ & _ & _ & VSd & _); rewrite ETB in VSd; destruct VSd as (_ & _ & _ & _ & _ & XN & _); exact XN).
  pose proof FBT as SR. unfold PGSA.fill_buffer_tb_specG, PGSA.src_specG in SR. cbn [pa_fill_buffer AD PMA.AD ADDR_A] in SR.
  apply (SR (PGV8A.src_of_vw T x g) (stw_ok x g) fx R M model K (PGV8.v8_own x ++ OB) LBX FF LK Aw cr (S - 160) X src str sm [(p, PM.CHUNK)]);
    cbn [PGS.ow_at PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi PGS.ow_win PGV8A.src_of_vw].
  { replace (PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) with (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) by (rewrite <- !app_assoc; reflexivity). exact HH. }
  { exact AM. } { exact K0. } { exact ENT. } { exact FRM. } { exact FRS'. } { exact OFR. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PGSA.tbfill_args. exists p. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|].
    cbn [PGS.ow_win PGV8A.src_of_vw]. split; [unfold PM.CHUNK; lia|]. exists q0, n0, c0. split; [exact ETB| lia]. }
  { unfold PMTXS.tbfill_W. exists p. rewrite L5SAR.r11. split; [exact A11|]. split; [unfold PM.CHUNK in *; lia| reflexivity]. }
  { exists OB. split; [reflexivity| exact PA]. }
  { exact IA. } { exact BASE. } { exact INCS. }
  intros fx' R' M' model' LK' Aw' src' sm' RP (OB1 & EOB & PA') IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  apply app_inv_head in EOB. subst OB1.
  change (PMSPA.pm_scr 3) with 18432 in HP.
  destruct RES as ((-> & c & Y10 & Hc & G & ST0 & ST2) & _).
  rewrite L5K.rl10 in Y10.
  apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G ST0 ST2 STEP).
  replace (PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) with ((PM.src_own src ++ PGV8.v8_own x) ++ (OB ++ LBX)) in HP by (rewrite <- !app_assoc; reflexivity).
  destruct (callee_mem M M' (PM.src_own src ++ PGV8.v8_own x) 18432 (PGS.W_srcG os ois src ++ [(p, PM.CHUNK)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
  { intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + apply (OW r0); [unfold PGVWA1.W0; apply in_or_app; left; exact Hr0| exact Hin].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) FF LK cr Aw M _ (PM.sr_qc src) PM.CHUNK a S 22528 ltac:(rewrite <- own2; exact HH));
          [apply in_or_app; left; left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      apply (PMARS1.own_not_aclient L ar C HI HIok (PM.src_own src ++ PGV8.v8_own x) (OB ++ LBX) FF LK cr Aw M _ q0 c0 a S 22528 ltac:(rewrite <- own2; exact HH) IN ltac:(unfold PM.CHUNK in *; lia) CA). }
  { intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PGS.W_srcG in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + exact (outside_W0 a ltac:(lia) r0 ltac:(unfold PGVWA1.W0; apply in_or_app; left; exact Hr0) Hin).
      + destruct (WB _ QIN) as ((Q0' & _ & _ & _ & Q4' & _) & _). cbn [fst snd] in Q0', Q4'. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|].
  split; [replace (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) with (PM.src_own src ++ (PGV8.v8_own x ++ OB) ++ LBX) by (rewrite <- !app_assoc; reflexivity); exact HH'|].
  split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros xr Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros xr Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
Lemma unread_nn M model src x g sm cr LK Aw : st_ok M model src x g sm cr LK Aw ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using All.
  intros (_ & _ & _ & PA & IA & _).
  destruct (tsrc M src x g PA) as ((_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

(* [comment removed for export] *)
Lemma lregs_keep R R1 w : lregs R w -> (forall xq, In xq [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26; 27]%nat -> getr R1 (reg xq) = getr R (reg xq)) -> lregs R1 w.
Proof.
  intros (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & KP) E.
  unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
  intros xr Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.
Lemma lregs_pres R R' w : regs_preserved R R' -> lregs R w -> lregs R' w.
Proof. intros RP LR. apply (lregs_keep R R' w LR). intros xr Hx. apply (L5SAR.cs_of_preserved R R' xr RP). unfold L5SAR.cs_all. cbn in Hx |- *. tauto. Qed.

Lemma lregs_set R R1 w w' : lregs R w -> (forall xq, In xq [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 26]%nat -> getr R1 (reg xq) = getr R (reg xq)) ->
  getr R1 (reg 27) = Z_to_bv 64 w' -> lregs R1 w'.
Proof.
  intros (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & KP) E E25.
  unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
  intros xr Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ro_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) M model src x g sm cr LK Aw (M1v : word -> option byte) :
  st_ok M model src x g sm cr LK Aw ->
  msteps RSEGS (L5SAR.st fx R pc (mrestrict (ahid Aw model) M)) (L5SAR.st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall model1, st_ok M model1 src x g sm cr LK Aw -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros SO MS MG FRZ NEXT.
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  unfold PMSP.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v K HH AM MS MG FRZ).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  apply NEXT. split; [exact MR|]. split; [exact SV|]. split; [exact LC|]. split; [exact PA|]. split; [exact IA|]. split; [exact BASE|].
  split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vpack M model src x g sm cr LK Aw :
  st_ok M model src x g sm cr LK Aw ->
  let H := ahid Aw model in let MV := mrestrict H M in
  L5.img_clear MV 65536 1269760 /\ L5.u64_at RSEGS MV 1300408 2147450880 /\ L5.u32_at RSEGS MV 1300416 1
  /\ (140735332487328 <= S <= 2 ^ 47 /\ S mod 16 = 0 /\ L5.writable RSEGS MV (S - 160) 160)
  /\ (forall k v, 8 <= k <= 160 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS MV (S - k) v)
  /\ (6897664 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis H a n)
  /\ (6897664 <= tb <= 140737488355304 /\ tb mod 8 = 0 /\ (2147446784 + 17592186048512 <= tb \/ tb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (tb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV tb 24 /\ (forall a n, tb <= a -> a + n <= tb + 24 -> L5A.avis H a n)
  /\ os + 296 <= S - 160 /\ tb + 24 <= S - 160 /\ PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF tb 24.
Proof using All.
  intros (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK) H MV.
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO & AOI & AT). destruct (frame_app _ _ _ _ _ _ HH) as (F1 & F2 & F3 & F4 & F5).
  pose proof (tsrc M src x g PA) as (PSF & PNI & PD & VS & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 22528 160 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK cr Aw M model os _ _ src S 22528 HH AO ltac:(lia) PSF PNI STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGV8KA.v8_visG L ar C HI LY HIok _ FF LK cr Aw M model tb x HH AT ltac:(lia) VS)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (src : PM.srcst) (x : PGV8.v8) (g : Z) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) (w : Z) : Prop :=
  lregs R w /\ st_ok M model src x g sm cr LK Aw /\ acct src x g sm w /\ 1 <= w <= len.
Definition IHt (mu0 : Z) : Prop :=
  forall (fx : FPState) R M model src x g sm cr LK Aw w, PM.mu_src src sm < mu0 -> lstate R M model src x g sm cr LK Aw w ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3c5c M model) K.

End Call.
End WithHeap.
End PGSSVA1.
