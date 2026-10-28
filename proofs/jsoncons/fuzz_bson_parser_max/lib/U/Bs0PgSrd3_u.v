(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdP_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PgSrd1_u Bs0PgSrd2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSR3.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

Lemma subw (x k : Z) : 0 <= x <= k -> k < 2 ^ 64 -> ((((k + ((18446744073709551615 * x) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) = k - x.
Proof.
  intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
  replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg (x : Z) : - 2 ^ 64 < x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 (x : Z) : - 2 ^ 64 < x <= 0 -> x mod 2 ^ 64 < 1 -> x = 0.
Proof. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.

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
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tb0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGS.tw_os T).
#[local] Abbreviation ois := (PGS.tw_ois T).
#[local] Abbreviation otb := (PGS.tw_otb T).
#[local] Abbreviation lo := (PGS.tw_lo T).
#[local] Abbreviation hi := (PGS.tw_hi T).
Hypothesis TOK : PGS.towner_ok RSEGS AD L HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis K0 : K [].
Hypothesis SPLO : S <= lo.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size tb0 + PM.unread src0 sm0 < 2 ^ 26.
Hypothesis RSZ : PMS.str_resize_spec L HI.
Hypothesis SRD : PGS.src_read_specG RSEGS AD L HI.
Hypothesis FBT : PGS.fill_buffer_tb_specG RSEGS AD L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
                         (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PM.vs_size tb' = PM.vs_size tb0 + d ->
  PGS.tw_at T M' src' tb' tg' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 5) (PGSSR1.W0 T) M0 M' ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L tb0 tg0) (PM.pot_text L tb' tg') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGSSR1.lay L HI T TOK).
#[local] Abbreviation lay0 := (PGSSR1.lay0 L HI T TOK).
#[local] Abbreviation base_keep := (PGSSR1.base_keep L HI LY LBX S T OB TOK SPLO).
#[local] Abbreviation tw_xfer := (PGSSR1.tw_xfer L HI HIok LBX S T OB TOK SPLO).
#[local] Abbreviation tsrc := (PGSSR1.tsrc L HI T OB TOK).
#[local] Abbreviation W0 := (PGSSR1.W0 T).
#[local] Abbreviation saves9 := (PGSSR1.saves9 R0 S).
#[local] Abbreviation kept6 := (PGSSR1.kept6 R0).
#[local] Abbreviation memrel := (PGSSR1.memrel L M0 LBX S T OB).
#[local] Abbreviation acct := (PGSSR1.acct len src0 tb0 sm0).
#[local] Abbreviation state_ok := (PGSSR1.state_ok L HI R0 M0 model0 LBX cr0 S T OB tb0 tg0 str).
#[local] Abbreviation lregs := (PGSSR1.lregs R0 S len T).
#[local] Abbreviation tbdst := (PGSSR1.tbdst T).
#[local] Abbreviation lstate := (PGSSR1.lstate L HI R0 M0 model0 LBX cr0 S len T OB src0 tb0 tg0 str sm0).
#[local] Abbreviation IHt := (PGSSR1.IHt L HI R0 M0 model0 K LBX cr0 S len T OB src0 tb0 tg0 str sm0).
#[local] Abbreviation finish := (PGSSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PGSSR1.call_resize L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PGSSR1.call_srcread L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PGSSR1.call_filltb L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PGSSR1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation after_read := (PGSSR2.after_read L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srcread mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w k n p : Z) :
  getr R (reg 1) = Z_to_bv 64 234588 -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 otb ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 k ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 (otb + 1) -> getr R (reg 23) = Z_to_bv 64 n -> kept6 R ->
  1 <= k <= w -> k <= PM.CHUNK -> w <= len -> tbdst tb p k ->
  state_ok M model src tb tg sm cr -> PM.vs_size tb = n + k -> 0 <= n -> n = PM.vs_size tb0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x370d0 M model) K.
Proof using All.
  intros A1 A2 A8 A9 A10 A11 A12 A18 A19 A21 A22 A23 KP Hk HkC Hw DST SO SZ Hn0 En CONS STEP PRG MU.
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  apply (call_srcread fx R M model src tb tg sm cr p k 234588 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 ltac:(lia) DST SO).
  intros fx2 R2 M2 src2 sm2 d RP2 Y10 Hd CONS2 POS ZERO STEP2 SO2.
  pose proof (unread_nn M2 model _ _ _ sm2 cr SO2) as (UN2 & ST2 & RM2 & GE2).
  apply (after_read mu0 IH fx2 R2 M2 model src2 tb tg sm2 cr w k d n); try assumption.
  - rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl. exact A2.
  - rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl. exact A8.
  - rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl. exact A9.
  - rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl. exact A18.
  - rewrite (PMK.cs_of_preserved R R2 19%nat RP2) by PMK.inl. exact A19.
  - rewrite (PMK.cs_of_preserved R R2 21%nat RP2) by PMK.inl. exact A21.
  - rewrite (PMK.cs_of_preserved R R2 22%nat RP2) by PMK.inl. exact A22.
  - rewrite (PMK.cs_of_preserved R R2 23%nat RP2) by PMK.inl. exact A23.
  - intros x Hx. rewrite (PMK.cs_of_preserved R R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
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
Lemma after_resize1 mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w k n : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 otb ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 k ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 (otb + 1) -> getr R (reg 23) = Z_to_bv 64 n -> kept6 R ->
  1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  state_ok M model src tb tg sm cr -> PM.vs_size tb = n + k -> 0 <= n -> n = PM.vs_size tb0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3942c M model) K.
Proof using All.
  intros A2 A8 A9 A18 A19 A21 A22 A23 KP Hk HkC Hw SO SZ Hn0 En CONS STEP PRG MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  assert (Hn : n < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src tb tg PA) as (_ & _ & _ & VS & _).
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
  destruct VS as (VD & _ & VS). destruct tb as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & B0).
    pose proof (PMF.even_byte n1) as EV.
    LeanFeed.pfeed PP (PMSSRP.tsQS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => 2 * n1 | 42%nat => k | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3942c R1 0x370d0 M K Mh Ml MS).
    apply (at_srcread mu0 IH fx1 R1 M model src (PM.VShort n1) tg sm cr w k n (otb + n + 1)); try assumption.
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + rewrite (KS 8%nat) by PMK.inl. exact A8.
    + rewrite (KS 9%nat) by PMK.inl. exact A9.
    + rewrite (KS 18%nat) by PMK.inl. exact A18.
    + rewrite (KS 19%nat) by PMK.inl. exact A19.
    + rewrite (KS 21%nat) by PMK.inl. exact A21.
    + rewrite (KS 22%nat) by PMK.inl. exact A22.
    + rewrite (KS 23%nat) by PMK.inl. exact A23.
    + kept_tac KS KP.
    + unfold PGSSR1.tbdst. left. split; [exists n1; reflexivity|]. lia.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
    pose proof (PMF.u8_of_u64 RSEGS M otb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (IN : In (q1, c1) (PM.src_own src ++ PM.vs_own (PM.VLong c1 n1 q1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    destruct (BR q1 c1 IN) as (Q0 & _ & Q4).
    LeanFeed.pfeed PP (PMSSRP.tsQL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => (c1 + 1) mod 256 | 41%nat => q1 | 42%nat => k | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3942c R1 0x370d0 M K Mh Ml MS).
    apply (at_srcread mu0 IH fx1 R1 M model src (PM.VLong c1 n1 q1) tg sm cr w k n (q1 + n)); try assumption.
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + rewrite (KS 8%nat) by PMK.inl. exact A8.
    + rewrite (KS 9%nat) by PMK.inl. exact A9.
    + rewrite (KS 18%nat) by PMK.inl. exact A18.
    + rewrite (KS 19%nat) by PMK.inl. exact A19.
    + rewrite (KS 21%nat) by PMK.inl. exact A21.
    + rewrite (KS 22%nat) by PMK.inl. exact A22.
    + rewrite (KS 23%nat) by PMK.inl. exact A23.
    + kept_tac KS KP.
    + unfold PGSSR1.tbdst. right. exists c1, n1, q1. split; [reflexivity|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rpath mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w k : Z) :
  lregs R w -> getr R (reg 19) = Z_to_bv 64 k -> 1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  state_ok M model src tb tg sm cr -> acct src tb sm w ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39404 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A21 & A22 & KP) A19 Hk HkC Hw SO (CONS & SZ & STEP) PRG MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src tb tg PA) as (_ & _ & _ & VS & _).
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
  destruct VS as (VD & _ & VS). destruct tb as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & B0).
    pose proof (PMF.even_byte n1) as EV.
    LeanFeed.pfeed PP (PMSSRP.tsRS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => 2 * n1 | 42%nat => k | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E23).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39404 R1 0x59000 M K Mh Ml MS).
    assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + k)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    assert (E23' : getr R1 (reg 23) = Z_to_bv 64 n1) by (rewrite E23; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    apply (call_resize fx1 R1 M model src (PM.VShort n1) tg sm cr (n1 + k) 234540); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (after_resize1 mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 w k n1); try assumption; try lia.
      * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
      * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
      * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
      * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
      * rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
      * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
      * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
      * rewrite (PMK.cs_of_preserved R1 R2 23%nat RP2) by PMK.inl. exact E23'.
      * intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
        rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
    pose proof (PMF.u8_of_u64 RSEGS M otb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    LeanFeed.pfeed PP (PMSSRP.tsRL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => (c1 + 1) mod 256 | 40%nat => n1 | 42%nat => k | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E23).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39404 R1 0x59000 M K Mh Ml MS).
    apply (call_resize fx1 R1 M model src (PM.VLong c1 n1 q1) tg sm cr (n1 + k) 234540); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (after_resize1 mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 w k n1); try assumption; try lia.
      * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
      * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
      * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
      * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
      * rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
      * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
      * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
      * rewrite (PMK.cs_of_preserved R1 R2 23%nat RP2) by PMK.inl. exact E23.
      * intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
        rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
Qed.

End Call.
End WithHeap.
End PGSSR3.
