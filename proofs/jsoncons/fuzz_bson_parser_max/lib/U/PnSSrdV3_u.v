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
     PmTxtSpecs PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdVP_u Bs0_code_383d4_383d8_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSSrdV1_u PnSSrdV2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSSV3.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).

Lemma src_step_trans a b c sa sb sc : PMSP.src_step a b sa sb -> PMSP.src_step b c sb sc -> PMSP.src_step a c sa sc.
Proof.
  unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Lemma mu_dec src src' sm sm' : PMSP.src_step src src' sm sm' -> (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) -> (PM.sm_st sm' = 0 \/ PM.sm_st sm' = 2) ->
  (PM.unread src' sm' < PM.unread src sm \/ (PM.sm_st sm = 0 /\ PM.sm_st sm' = 2)) -> PM.mu_src src' sm' < PM.mu_src src sm.
Proof.
  unfold PM.mu_src. intros (_ & _ & _ & S2 & U) ST ST' H.
  destruct ST as [E|E]; destruct ST' as [E'|E']; rewrite ?E, ?E' in *; cbn [Z.eqb]; [lia|lia| specialize (S2 eq_refl); lia| lia].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

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
Hypothesis SZ0 : PGV8.v8_size x0 = 0.
Hypothesis ROOM0 : PGV8.v8_room x0 (PM.unread src0 sm0).
Hypothesis RSZ : PNRS.vu8_resize_spec L HI.
Hypothesis SRD : PGS.src_read_specG RSEGS AD L HI.
Hypothesis FBT : PGS.fill_buffer_tb_specG RSEGS AD L HI.
(* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : PGV8.v8) (g' : Z)
                         (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PGV8.v8_size x' = d ->
  (d = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at V M' src' x' g' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 5) (PNSSV1.W0 V) M0 M' ->
  PMSP.credit_keep cr0 cr' (PGV8.pot_v8 L x0 g0) (PGV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.


#[local] Abbreviation lay := (PNSSV1.lay L HI V VOK).
#[local] Abbreviation tsrc := (PNSSV1.tsrc L HI V OB VOK).
#[local] Abbreviation W0 := (PNSSV1.W0 V).
#[local] Abbreviation saves8 := (PNSSV1.saves8 R0 S).
#[local] Abbreviation kept7 := (PNSSV1.kept7 R0).
#[local] Abbreviation memrel := (PNSSV1.memrel L M0 LBX S V OB).
#[local] Abbreviation vroom := (PNSSV1.vroom len src0 sm0).
#[local] Abbreviation acct := (PNSSV1.acct len src0 sm0).
#[local] Abbreviation state_ok := (PNSSV1.state_ok L HI R0 M0 model0 LBX cr0 S V OB x0 g0 str).
#[local] Abbreviation lregs := (PNSSV1.lregs R0 S len V).
#[local] Abbreviation lstate := (PNSSV1.lstate L HI R0 M0 model0 LBX cr0 S len V OB src0 x0 g0 str sm0).
#[local] Abbreviation IHt := (PNSSV1.IHt L HI R0 M0 model0 K LBX cr0 S len V OB src0 x0 g0 str sm0).
#[local] Abbreviation finish := (PNSSV1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PNSSV1.call_resize L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PNSSV1.call_srcread L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation after_read := (PNSSV2.after_read L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PNSSV1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).

Ltac bvr1 R y := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg y))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.
Ltac kept_tac KS KP := intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); apply KP; exact Hy.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srcread mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w k n p : Z) :
  getr R (reg 1) = Z_to_bv 64 0x39608 -> getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 ov ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 k ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 n -> kept7 R ->
  1 <= k <= w -> k = Z.min w PM.CHUNK -> w <= len -> PNSSV1.vdst x p k ->
  state_ok M model src x g sm cr -> PGV8.v8_size x = n + k -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x370d0 M model) K.
Proof using All.
  intros A1 A2 A8 A9 A10 A11 A12 A18 A19 A21 A22 KP Hk HkC Hw DST SO SZ VR En CONS STEP PRG MU.
  assert (HkC' : k <= PM.CHUNK) by lia.
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  apply (call_srcread fx R M model src x g sm cr p k 0x39608 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 ltac:(lia) DST SO).
  intros fx2 R2 M2 src2 sm2 d RP2 Y10 Hd CONS2 POS ZERO STEP2 SO2.
  pose proof (unread_nn M2 model _ _ _ sm2 cr SO2) as (UN2 & ST2 & RM2 & GE2).
  apply (after_read mu0 IH fx2 R2 M2 model src2 x g sm2 cr w k d n); try assumption.
  - rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl. exact A2.
  - rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl. exact A8.
  - rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl. exact A9.
  - rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl. exact A18.
  - rewrite (PMK.cs_of_preserved R R2 19%nat RP2) by PMK.inl. exact A19.
  - rewrite (PMK.cs_of_preserved R R2 21%nat RP2) by PMK.inl. exact A21.
  - rewrite (PMK.cs_of_preserved R R2 22%nat RP2) by PMK.inl. exact A22.
  - intros y Hy. rewrite (PMK.cs_of_preserved R R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - unfold PMSP.consumed in *. lia.
  - exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  - enough (PM.mu_src src2 sm2 < PM.mu_src src sm) by lia.
    apply (mu_dec _ _ _ _ STEP2 ST ST2).
    unfold PMSP.consumed in CONS2. destruct (Z.eq_dec d 0) as [D0|D0]; [right| left; lia].
    destruct (ZERO D0) as (_ & E2). split; [|exact E2].
    destruct PRG as [P1|P1]; [specialize (POS P1); lia| exact P1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_resize1 mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w k n : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 ov ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 k ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 n -> kept7 R ->
  1 <= k <= w -> k = Z.min w PM.CHUNK -> w <= len ->
  state_ok M model src x g sm cr -> PGV8.v8_size x = n + k -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x395e8 M model) K.
Proof using All.
  intros A2 A8 A9 A18 A19 A21 A22 KP Hk HkC Hw SO SZ VR En CONS STEP PRG MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  assert (Hn : 0 <= n < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct x as [|b1 n1 c1]; cbn [PGV8.v8_size] in SZ; [lia|]. subst n1.
  destruct VS as (VD & _ & U0 & U8 & U16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
  assert (IN : In (b1, c1) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b1 (n + k) c1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
  destruct (BR b1 c1 IN) as (Q0 & _ & Q4).
  LeanFeed.pfeed PP (PNSSVP.tvQ_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
      | 39%nat => b1 | 42%nat => k | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x395e8 R1 0x370d0 M K Mh Ml MS).
  apply (at_srcread mu0 IH fx1 R1 M model src (PGV8.V8Blk b1 (n + k) c1) g sm cr w k n (b1 + n)); try assumption.
  + rewrite (KS 2%nat) by PMK.inl. exact A2.
  + rewrite (KS 8%nat) by PMK.inl. exact A8.
  + rewrite (KS 9%nat) by PMK.inl. exact A9.
  + rewrite (KS 18%nat) by PMK.inl. exact A18.
  + rewrite (KS 19%nat) by PMK.inl. exact A19.
  + rewrite (KS 21%nat) by PMK.inl. exact A21.
  + rewrite (KS 22%nat) by PMK.inl. exact A22.
  + kept_tac KS KP.
  + unfold PNSSV1.vdst. exists b1, (n + k), c1. split; [reflexivity| lia].
  + reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rpath mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w k : Z) :
  lregs R w -> getr R (reg 19) = Z_to_bv 64 k -> 1 <= k <= w -> k = Z.min w PM.CHUNK -> w <= len ->
  state_ok M model src x g sm cr -> acct src x sm w ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x395d0 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A21 & KP) A19 Hk HkC Hw SO AC PRG MU. pose proof AC as (CONS & SZ & STEP & VR & MIN).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; lia).
  assert (Hn : 0 <= len - w < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  (* [comment removed for export] *)
  assert (HDR : exists b, L5.u64_at RSEGS M ov b /\ L5.u64_at RSEGS M (ov + 8) (b + (len - w)) /\ 0 <= b <= 2 ^ 47).
  { destruct x as [|b1 n1 c1]; cbn [PGV8.v8_size] in SZ.
    - destruct VS as (_ & _ & U0 & U8 & _). exists 0. rewrite <- SZ, Z.add_0_l. split; [exact U0|]. split; [exact U8| lia].
    - destruct VS as (_ & _ & U0 & U8 & U16 & Hnc & Hc & Hb0 & _). subst n1. exists b1. split; [exact U0|]. split; [exact U8|].
      assert (IN : In (b1, c1) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b1 (len - w) c1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (BR b1 c1 IN) as (Q0 & _ & Q4). lia. }
  destruct HDR as (b & U0 & U8 & Hb).
  LeanFeed.pfeed PP (PNSSVP.tvR_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
      | 39%nat => b | 40%nat => len - w | 42%nat => k | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E22).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x395d0 R1 0x396ac M K Mh Ml MS).
  apply (call_resize fx1 R1 M model src x g sm cr ((len - w) + k) 0x395e8 w); try assumption.
  + split; [lia| reflexivity].
  + rewrite (KS 2%nat) by PMK.inl. exact A2.
  + kept_tac KS KP.
  + lia.
  + right. lia.
  + lia.
  + unfold PMSP.consumed in CONS. lia.
  + lia.
  + intros fx2 R2 M2 model2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 SO2.
    apply (after_resize1 mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 w k (len - w)); try assumption; try lia.
    * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
    * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
    * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
    * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
    * rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
    * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
    * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. exact E22.
    * intros y Hy. rewrite (PMK.cs_of_preserved R1 R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
      rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
Qed.

End Call.
End WithHeap.
End PNSSV3.
