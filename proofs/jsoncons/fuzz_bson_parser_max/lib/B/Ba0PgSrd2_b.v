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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnASrdP_b Ba0PgSrd1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSRA2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSSRA1.pot.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Lemma subw (x k : Z) : 0 <= x <= k -> k < 2 ^ 64 -> ((((k + ((18446744073709551615 * x) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) = k - x.
Proof.
  intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
  replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg (x : Z) : - 2 ^ 64 < x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 (x : Z) : - 2 ^ 64 < x <= 0 -> x mod 2 ^ 64 < 1 -> x = 0.
Proof. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.

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
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size tx0 + PM.unread src0 sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PMA.str_resize_spec L ar HI.
Hypothesis SRD : PGSA.src_read_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis FBT : PGSA.fill_buffer_tb_specG RSEGS AD L ar HI PNRA.FCB.
#[local] Abbreviation W0 := (PGSSRA1.W0 T).   (* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (tx' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PM.vs_size tx' = PM.vs_size tx0 + d ->
  PGS.tw_at T M' src' tx' tg' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar tx0 tg0) (pot L ar tx' tg') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PM.vs_own tx' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGSSRA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGSSRA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGSSRA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation frame_app := (PGSSRA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGSSRA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGSSRA1.stw_ok L ar C HI LY HIok T TOK).
#[local] Abbreviation U := (PGSSRA1.U R0).
#[local] Abbreviation saves13 := (PGSSRA1.saves13 R0 S).
#[local] Abbreviation locals := (PGSSRA1.locals S len T).
#[local] Abbreviation kept_rs := (PGSSRA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSSRA1.memrel L ar M0 LBX FF S T OB).
#[local] Abbreviation fields_eq := (PGSSRA1.fields_eq).
#[local] Abbreviation acct := (PGSSRA1.acct len src0 tx0 sm0).
#[local] Abbreviation st_ok := (PGSSRA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S len T OB tx0 tg0 str).
#[local] Abbreviation lregs := (PGSSRA1.lregs R0 S T).
#[local] Abbreviation tbdst := (PGSSRA1.tbdst T).
#[local] Abbreviation lstate := (PGSSRA1.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S len T OB src0 tx0 tg0 str sm0).
#[local] Abbreviation IHt := (PGSSRA1.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S len T OB src0 tx0 tg0 str sm0).
#[local] Abbreviation lregs_keep := (PGSSRA1.lregs_keep R0 S len T Hlen).
#[local] Abbreviation lregs_set := (PGSSRA1.lregs_set R0 S len T Hlen).
#[local] Abbreviation lregs_pres := (PGSSRA1.lregs_pres R0 S len T Hlen).
#[local] Abbreviation finish := (PGSSRA1.finish L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation callee_mem := (PGSSRA1.callee_mem L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation centry := (PGSSRA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PGSSRA1.call_resize L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PGSSRA1.call_srcread L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PGSSRA1.call_filltb L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PGSSRA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation vpack := (PGSSRA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation ro_step := (PGSSRA1.ro_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation outside_W0 := (PGSSRA1.outside_W0 L ar HI T TOK).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_shrink mu0 (IH : IHt mu0) (fx : FPState) R M model src tx tg sm cr LK Aw (w d : Z) :
  lregs R w -> getr R (reg 25) = Z_to_bv 64 d -> 0 <= d <= w -> d <= PM.CHUNK -> 1 <= w <= len ->
  st_ok M model src tx tg sm cr LK Aw -> acct src tx tg sm (w - d) -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb533c M model) K.
Proof using All.
  intros LR AD Hd HdC Hw SO AC MU. unfold PM.CHUNK in HdC.
  pose proof LR as (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP).
  pose proof (vpack M model src tx tg sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMASRDP.srdF_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 44%nat => d
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E8 & C0) | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0)]).
  - apply (ro_step fx fx1 R 0xb533c R1 0xb51a0 M model src tx tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    apply (IH fx1 R1 M model1 src tx tg sm cr LK Aw (w - d) MU).
    split; [|split; [exact SO1| split; [exact AC| lia]]].
    apply (lregs_set R R1 w (w - d) LR); [ks_tac KS1| exact E8].
  - apply (ro_step fx fx1 R 0xb533c R1 0xb53b8 M model src tx tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    apply (finish fx1 R1 M model1 src tx tg sm cr LK Aw 0); try assumption.
    + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace 0 with (w - d) by lia. exact AC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_read mu0 (IH : IHt mu0) (fx : FPState) R M model src tx tg sm cr LK Aw (w k d n : Z) :
  lregs R w -> getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  0 <= d <= k -> 1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  st_ok M model src tx tg sm cr LK Aw -> PM.vs_size tx = n + k -> 0 <= n -> n = PM.vs_size tx0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w + d ->
  PMSP.src_step src0 src sm0 sm -> fields_eq src tx tg -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb526c M model) K.
Proof using All.
  intros LR A10 A24 AN Hd Hk HkC Hw SO SZ Hn0 En CONS STEP FE MU. unfold PM.CHUNK in HkC.
  pose proof LR as (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP).
  pose proof (unread_nn M model src tx tg sm cr LK Aw SO) as (UN & _).
  assert (Hn : 0 <= n < 67108864) by (unfold PMSP.consumed in CONS; lia).
  pose proof (vpack M model src tx tg sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMASRDP.srdE_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 43%nat => k
       | 44%nat => d | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E25 & C0) | [(MS1 & KS1 & E8 & E25 & C0 & C1)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]]).
  - (* [comment removed for export] *)
    apply (ro_step fx fx1 R 0xb526c R1 0xd628c M model src tx tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    assert (DK' : d < k).
    { destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M model1 src tx tg sm cr LK Aw (d + n) 742204); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 LK2 Aw2 w d); try assumption.
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 25%nat RP2) by inl. exact E25.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * unfold PGSSRA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|].
        unfold PGSSRA1.fields_eq; exact I.
  - (* [comment removed for export] *)
    apply (ro_step fx fx1 R 0xb526c R1 0xb51a0 M model src tx tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (IH fx1 R1 M model1 src tx tg sm cr LK Aw (w - k) MU).
    split; [|split; [exact SO1| split; [|lia]]].
    + apply (lregs_set R R1 w (w - k) LR); [ks_tac KS1| exact E8].
    + unfold PGSSRA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
  - (* [comment removed for export] *)
    apply (ro_step fx fx1 R 0xb526c R1 0xb53b8 M model src tx tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (finish fx1 R1 M model1 src tx tg sm cr LK Aw 0); try assumption.
    + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PGSSRA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.

End Call.
End WithHeap.
End PGSSRA2.
