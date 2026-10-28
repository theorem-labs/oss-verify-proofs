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
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdP_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PgSrd1_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSR2.
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

Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_shrink mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w d : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 otb ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 20) = Z_to_bv 64 d -> getr R (reg 21) = Z_to_bv 64 w ->
  getr R (reg 22) = Z_to_bv 64 (otb + 1) -> kept6 R ->
  0 <= d <= w -> d <= PM.CHUNK -> 1 <= w <= len ->
  state_ok M model src tb tg sm cr -> acct src tb sm (w - d) -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x394ec M model) K.
Proof using All.
  intros A2 A8 A9 A18 A20 A21 A22 KP Hd HdC Hw SO AC MU. unfold PM.CHUNK in HdC.
  pose proof SO as ((EK & DK & STK) & SV & _ & _ & _ & _ & _ & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72). bvr.
  LeanFeed.pfeed PP (PMSSRP.tsF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w | 42%nat => d
     | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
     | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
     | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 54%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E21 & C0) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & C0)]).
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x394ec R1 0x393d8 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    apply (IH fx1 R1 M model src tb tg sm cr (w - d) MU).
    split; [|split; [exact SO| split; [exact AC| lia]]].
    unfold PGSSR1.lregs.
    split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
    split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
    split; [exact E21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
    intros x Hx. rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x394ec R1 0x39520 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    apply (finish fx1 R1 M model src tb tg sm cr 0); try assumption.
    + intros x Hx. rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace 0 with (w - d) by lia. exact AC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_read mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w k d n : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 otb ->
  getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 k ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 (otb + 1) -> getr R (reg 23) = Z_to_bv 64 n -> kept6 R ->
  0 <= d <= k -> 1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  state_ok M model src tb tg sm cr -> PM.vs_size tb = n + k -> 0 <= n -> n = PM.vs_size tb0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w + d ->
  PMSP.src_step src0 src sm0 sm -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3945c M model) K.
Proof using All.
  intros A2 A8 A9 A10 A18 A19 A21 A22 A23 KP Hd Hk HkC Hw SO SZ Hn0 En CONS STEP MU. unfold PM.CHUNK in HkC.
  pose proof SO as ((EK & DK & STK) & SV & _ & _ & _ & _ & _ & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & _).
  assert (Hn : 0 <= n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72). bvr.
  LeanFeed.pfeed PP (PMSSRP.tsE_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w | 42%nat => k
     | 43%nat => n | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
     | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
     | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 53%nat => d | 54%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E12 & E20 & C0)
                                               |[(MS & KS & E20 & E21 & C0 & C1) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & C0 & C1)]]).
  - (* [comment removed for export] *)
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3945c R1 0x59000 M K Mh Ml MS).
    assert (DK' : d < k).
    { destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M model src tb tg sm cr (n + d) 234732); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + intros x Hx. rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + unfold PM.CHUNK. lia.
    + unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 w d); try assumption.
      * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
      * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
      * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
      * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
      * rewrite (PMK.cs_of_preserved R1 R2 20%nat RP2) by PMK.inl. exact E20.
      * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
      * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
      * intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
        rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * unfold PGSSR1.acct. split; [lia|]. split; [lia|]. exact STEP.
  - (* [comment removed for export] *)
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3945c R1 0x393d8 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (IH fx1 R1 M model src tb tg sm cr (w - k) MU).
    split; [|split; [exact SO| split; [|lia]]].
    + unfold PGSSR1.lregs.
      split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
      split; [exact E21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
      intros x Hx. rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + unfold PGSSR1.acct. split; [lia|]. split; [lia|]. exact STEP.
  - (* [comment removed for export] *)
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3945c R1 0x39520 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (finish fx1 R1 M model src tb tg sm cr 0); try assumption.
    + intros x Hx. rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PGSSR1.acct. split; [lia|]. split; [lia|]. exact STEP.
Qed.

End Call.
End WithHeap.
End PGSSR2.
