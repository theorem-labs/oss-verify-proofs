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
     PmTxtSpecs PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdVP_u Bs0_code_383d4_383d8_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSSrdV1_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSSV2.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).

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
#[local] Abbreviation unread_nn := (PNSSV1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).

Ltac bvr1 R y := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg y))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_shrink mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w d : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 ov ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 20) = Z_to_bv 64 d -> getr R (reg 21) = Z_to_bv 64 w -> kept7 R ->
  0 <= d <= w -> d <= PM.CHUNK -> 1 <= w <= len ->
  state_ok M model src x g sm cr -> acct src x sm (w - d) -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39674 M model) K.
Proof using All.
  intros A2 A8 A9 A18 A20 A21 KP Hd HdC Hw SO AC MU. unfold PM.CHUNK in HdC.
  pose proof SO as ((EK & DK & STK) & SV & _ & _ & _ & _ & _ & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). bvr.
  LeanFeed.pfeed PP (PNSSVP.tvF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w | 42%nat => d
     | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
     | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
     | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E21 & C0) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & C0)]).
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39674 R1 0x395a4 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    apply (IH fx1 R1 M model src x g sm cr (w - d) MU).
    split; [|split; [exact SO| split; [exact AC| lia]]].
    unfold PNSSV1.lregs.
    split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
    split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
    split; [exact E21|].
    intros y Hy. rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39674 R1 0x396a4 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    apply (finish fx1 R1 M model src x g sm cr 0); try assumption.
    + intros y Hy. rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace 0 with (w - d) by lia. exact AC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_read mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w k d n : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 ov ->
  getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 k ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 n -> kept7 R ->
  0 <= d <= k -> 1 <= k <= w -> k = Z.min w PM.CHUNK -> w <= len ->
  state_ok M model src x g sm cr -> PGV8.v8_size x = n + k -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w + d ->
  PMSP.src_step src0 src sm0 sm -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39608 M model) K.
Proof using All.
  intros A2 A8 A9 A10 A18 A19 A21 A22 KP Hd Hk HkC Hw SO SZ VR En CONS STEP MU.
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; lia).
  pose proof SO as ((EK & DK & STK) & SV & PA & _ & _ & _ & _ & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & _).
  destruct (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  assert (CAP : n + k <= PGV8.v8_cap x /\ 0 <= n) by (destruct x as [|b' n' c']; cbn in SZ |- *; [lia| destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _); lia]).
  assert (Hn : 0 <= n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). bvr.
  LeanFeed.pfeed PP (PNSSVP.tvE_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w | 42%nat => k
     | 43%nat => n | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
     | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
     | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 53%nat => d | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E20 & C0)
                                               |[(MS & KS & E20 & E21 & C0 & C1) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & C0 & C1)]]).
  - (* [comment removed for export] *)
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39608 R1 0x396ac M K Mh Ml MS).
    assert (DK' : d < k).
    { destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M model src x g sm cr (n + d) 0x39674 w); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + intros y Hy. rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + lia.
    + left. lia.
    + right. lia.
    + lia.
    + unfold PMSP.consumed in CONS. lia.
    + lia.
    + intros fx2 R2 M2 model2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 w d); try assumption.
      * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
      * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
      * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
      * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
      * rewrite (PMK.cs_of_preserved R1 R2 20%nat RP2) by PMK.inl. exact E20.
      * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
      * intros y Hy. rewrite (PMK.cs_of_preserved R1 R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
        rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * unfold PNSSV1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR2|]. right. lia.
  - (* [comment removed for export] *)
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39608 R1 0x395a4 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (IH fx1 R1 M model src x g sm cr (w - k) MU).
    split; [|split; [exact SO| split; [|lia]]].
    + unfold PNSSV1.lregs.
      split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
      split; [exact E21|].
      intros y Hy. rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + unfold PNSSV1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. lia.
  - (* [comment removed for export] *)
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39608 R1 0x396a4 M K Mh Ml MS).
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (finish fx1 R1 M model src x g sm cr 0); try assumption.
    + intros y Hy. rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PNSSV1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. lia.
Qed.

End Call.
End WithHeap.
End PNSSV2.
