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
     PmTxtSpecs PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdVP_u Bs0_code_383d4_383d8_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSVu8Grow_u PnSSrdV1_u PnSSrdV2_u PnSSrdV3_u PnSSrdV4_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSSV5.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).

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
#[local] Abbreviation call_fillv := (PNSSV1.call_fillv L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation after_shrink := (PNSSV2.after_shrink L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation vw_xfer := (PNSSV1.vw_xfer L HI HIok LBX S V OB VOK SPLO).
#[local] Abbreviation base_keep := (PNSSV1.base_keep L HI LY LBX S V OB VOK SPLO).
#[local] Abbreviation rpath := (PNSSV3.rpath L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation dpath := (PNSSV4.dpath L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PNSSV1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).

Ltac bvr1 R y := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg y))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.
Ltac kept_tac KS KP := intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); apply KP; exact Hy.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma head mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w : Z) :
  lstate R M model src x g sm cr w -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x395a4 M model) K.
Proof using All.
  intros LS MU. pose proof LS as ((A2 & A8 & A9 & A18 & A21 & KP) & SO & AC & Hw).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct (tsrc M src x g PA) as ((F1 & _ & _ & _ & F5 & _ & F7 & _) & _).
  change PM.CHUNK with 16384 in F5, RM.
  destruct (Z.eq_dec (PM.sr_rem src) 0) as [RZ|RNZ].
  - (* [comment removed for export] *)
    rewrite RZ in F7.
    pose proof IA as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
    cbn [pa_vp_iss AD PnLayoutS_u.ADDR_S] in I0.
    destruct IOS as (_ & U32 & _).
    pose proof (PMTK2.u8_of_u32 RSEGS M (ois + 120 + 32) (PM.sm_st sm) ltac:(lia) U32) as B152.
    rewrite Z.mod_small in B152 by lia.
    pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). bvr.
    pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG.
    LeanFeed.pfeed PP (PNSSVP.tvH0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
       | 38%nat => ois | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
       | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
       | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => PM.sm_st sm | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E19 & C0 & C1) | [(MS & KS & E1 & E10 & E11 & E19 & C0 & C1)
                                                 | (MS & KS & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & C0)]]).
    + (* [comment removed for export] *)
      assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x395a4 R1 0x395d0 M K Mh Ml MS).
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (rpath mu0 IH fx1 R1 M model src x g sm cr w w); try assumption.
      * unfold PNSSV1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
        kept_tac KS KP.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * right. exact ST0.
    + (* [comment removed for export] *)
      assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x395a4 R1 0x3961c M K Mh Ml MS).
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (dpath mu0 IH fx1 R1 M model src x g sm cr w); try assumption.
      * unfold PNSSV1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
        kept_tac KS KP.
      * lia.
    + (* [comment removed for export] *)
      assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x395a4 R1 0x396a4 M K Mh Ml MS).
      apply (finish fx1 R1 M model src x g sm cr w); try assumption.
      * kept_tac KS KP.
      * lia.
  - (* [comment removed for export] *)
    LeanFeed.pfeed PP (PNSSVP.tvH1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
       | 37%nat => PM.sr_rem src | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E19 & C0) | (MS & KS & E1 & E10 & E11 & E19 & C0)]);
      (assert (EM : M1 = M) by (apply functional_extensionality; exact FRw)); subst M1;
      unfold PMSP.cfg; apply (PMK.spiece_ro RSEGS model fx fx1 R 0x395a4 R1 0x395d0 M K Mh Ml MS).
    + apply (rpath mu0 IH fx1 R1 M model src x g sm cr w w); try assumption.
      * unfold PNSSV1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
        kept_tac KS KP.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * left. lia.
    + apply (rpath mu0 IH fx1 R1 M model src x g sm cr w 16384); try assumption.
      * unfold PNSSV1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|].
        kept_tac KS KP.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * left. lia.
Qed.

(* [comment removed for export] *)
Lemma loop (n : nat) : forall (fx : FPState) R M model src x g sm cr w,
  (Z.to_nat (PM.mu_src src sm) < n)%nat -> lstate R M model src x g sm cr w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x395a4 M model) K.
Proof using All.
  induction n as [|n IHn]; intros fx R M model src x g sm cr w Hn LS; [lia|].
  assert (IHm : IHt (PM.mu_src src sm)).
  { intros fx' R' M' model' s' x' g' sm' cr' w' Hlt LS'. apply (IHn fx' R' M' model' s' x' g' sm' cr' w'); [|exact LS'].
    pose proof LS' as (_ & SO' & _). pose proof (unread_nn _ _ _ _ _ _ _ SO') as (UN' & _).
    assert (0 <= PM.mu_src s' sm') by (unfold PM.mu_src; destruct (Z.eqb _ _); lia). lia. }
  exact (head _ IHm fx R M model src x g sm cr w LS ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_ok (fx : FPState) :
  hi_heap HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) cr0 M0 (m_vmmaps model0) -> PMSP.model_ok model0 -> L5C.stk (hl_sptop L) M0 S 22528 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 ov -> getr R0 (reg 12) = Z_to_bv 64 len ->
  PGV8.vw_at V M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD T3 M0 ois str sm0 -> PMST.base_ok RSEGS AD M0 ->
  PGV8.v8_ok x0 g0 -> PMSP.credit_le (PGV8.pot_v8 L x0 g0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x3956c M0 model0) K.
Proof using All.
  intros HH MOK STK A10 A11 A12 PA IA BASE TBOK CRL.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof (L5C.stk_writable RSEGS _ M0 S 22528 STK) as WR.
  set (LBc := PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) in HH.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_refl).
  assert (INL : incl (OB ++ LBX) LBc) by (intros y Hy; unfold LBc; rewrite PNSSV1.own2; apply in_or_app; right; exact Hy).
  LeanFeed.pfeed PP (PNSSVP.tvA_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
  set (P := fun a => S - 64 <= a < S - 64 + 64).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= S - 64 \/ S <= a) -> L5C.agree_on M0 M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ; lia. }
  assert (AGH : forall B m, In (B, m) LBc -> L5C.agree_on M0 M1 B m).
  { intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4). unfold hl_ceil in Q4. apply AG; lia. }
  assert (EKw : forall scr, 64 <= scr <= 22528 -> PMK.ek L (OB ++ LBX) S scr W0 M0 M1).
  { intros scr Hs. apply (PMK.ek_piece_in RSEGS L KL (OB ++ LBX) S scr W0 M0 M1 P); [intros a Ha N; apply FRZ; [exact Ha| exact N]| | |].
    - apply (PMK.stk_call L M0 S 22528 S scr STK); [lia|lia|lia| exact A16].
    - exact (PMFR.brange_hi L (OB ++ LBX) (PMFR.brange_incl L (OB ++ LBX) _ BR INL)).
    - intros a Pa. left. unfold P in Pa. lia. }
  pose proof (EKw 22528 ltac:(lia)) as EKn.
  assert (SPC : forall pc1, msteps RSEGS (@mkst fx R0 (Z_to_bv 64 0x3956c) M0 (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
            (hi_heap HI LBc cr0 M1 (m_vmmaps model0) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model0) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x3956c M0 model0) K).
  { intros pc1 MS NEXT. unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LBc cr0 M0 model0 fx fx1 R0 0x3956c R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
    - intros a Ha N. apply FRZ; [exact Ha| exact N].
    - intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LBc M0 S 22528 a STK). lia.
    - intros a. unfold P. apply PMK.rng_dec.
    - exact NEXT. }
  assert (SO1 : forall (C1 : L5.u64_at RSEGS M1 (S - 64) (bv_unsigned (getr R0 (reg 22)))) (C2 : L5.u64_at RSEGS M1 (S - 56) (bv_unsigned (getr R0 (reg 21))))
                       (C3 : L5.u64_at RSEGS M1 (S - 48) (bv_unsigned (getr R0 (reg 20)))) (C4 : L5.u64_at RSEGS M1 (S - 40) (bv_unsigned (getr R0 (reg 19))))
                       (C5 : L5.u64_at RSEGS M1 (S - 32) (bv_unsigned (getr R0 (reg 18)))) (C6 : L5.u64_at RSEGS M1 (S - 24) (bv_unsigned (getr R0 (reg 9))))
                       (C7 : L5.u64_at RSEGS M1 (S - 16) (bv_unsigned (getr R0 (reg 8)))) (C8 : L5.u64_at RSEGS M1 (S - 8) (bv_unsigned (getr R0 (reg 1)))),
                hi_heap HI LBc cr0 M1 (m_vmmaps model0) -> state_ok M1 model0 src0 x0 g0 sm0 cr0).
  { intros C1 C2 C3 C4 C5 C6 C7 C8 HH1.
    destruct (tsrc M0 src0 x0 g0 PA) as (PSF & _ & _ & VS & _).
    assert (INC : In (PM.sr_qc src0, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; left; reflexivity).
    destruct (BR _ _ INC) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
    split; [split; [|split]|].
    - exact EKn.
    - apply PMK.dk_grows. exact MG.
    - exact (PMK.stk_grows L M0 M1 S 22528 MG STK).
    - split; [unfold PNSSV1.saves8; repeat split; assumption|].
      split.
      { apply (vw_xfer M0 M1 src0 src0 x0 x0 g0 g0 cr0 (m_vmmaps model0) 22528 S 64 [] PA HH STK ltac:(lia) ltac:(lia) ltac:(lia)); [| constructor| | reflexivity| | exact TBOK].
        - apply (PMK.hpres_of L (OB ++ LBX) S 64 _ M0 M1).
          + rewrite app_nil_r. exact (EKw 64 ltac:(lia)).
          + apply (L5.defined_grows M0 M1 _ _ MG). intros i Hi. replace (S - 64 + i) with (S - 22528 + (22528 - 64 + i)) by lia. apply SDEF. lia.
          + apply PMK.dk_grows. exact MG.
        - apply (PMF.src_fields_at_agree RSEGS M0 M1 os ois (ois + 16) src0); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AG; lia| exact (AGH _ _ INC)| exact PSF].
        - apply (PNSVG.v8_at_agree M0 M1 ov x0 P VS MG ltac:(lia) ltac:(lia) FRZ). intros a Ha. unfold P. lia. }
      split.
      { apply (PMF.iss_at_agree RSEGS AD M0 M1 ois str sm0); [lia|lia| apply AG; lia| |exact IA].
        intros c n p E. apply AGH. unfold LBc. apply PNSSV1.in4. apply INCS. rewrite E. left. reflexivity. }
      split; [exact (base_keep M0 M1 EKn STK BASE)|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|].
      split; [exact CRL| unfold PMSP.credit_keep; lia]. }
  pose proof (unread_nn M0 model0 src0 x0 g0 sm0 cr0) as UNX.
  assert (VR0 : vroom x0).
  { unfold PNSSV1.vroom. destruct x0 as [|b n c]; [exact I|]. cbn in ROOM0. destruct ROOM0 as (a0 & j & H1 & H2 & H3 & H4).
    exists a0, j. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. left. exact H4. }
  destruct EX as [(MS & KS & E2 & E8 & E9 & E18 & E21 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) | (MS & KS & E10 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8)];
    apply (SPC _ MS); intros HH1; pose proof (SO1 C1 C2 C3 C4 C5 C6 C7 C8 HH1) as SOk.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0 by lia.
    pose proof (unread_nn M1 model0 src0 x0 g0 sm0 cr0 SOk) as (UN & _).
    apply (loop (Nat.succ (Z.to_nat (PM.mu_src src0 sm0))) fx1 R1 M1 model0 src0 x0 g0 sm0 cr0 len); [apply Nat.lt_succ_diag_r|].
    split; [|split; [exact SOk| split; [|lia]]].
    + unfold PNSSV1.lregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E21|].
      intros y Hy. rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). reflexivity.
    + unfold PNSSV1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [lia|]. split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|].
      split; [exact VR0| left; lia].
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0 by lia. assert (L0 : len = 0) by lia.
    apply (finish fx1 R1 M1 model0 src0 x0 g0 sm0 cr0 0); try assumption.
    all: try (rewrite (KS 2%nat) by PMK.inl; exact Rsp0).
    all: try (rewrite (KS _) by PMK.inl; symmetry; apply Z_to_bv_bv_unsigned).
    + intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); reflexivity.
    + rewrite E10; f_equal; lia.
    + lia.
    + unfold PNSSV1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [lia|].
      split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|].
      split; [exact VR0| left; lia].
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem srd_read_v_okG : PNRS.vu8_resize_spec L HI -> PGS.src_read_specG RSEGS AD L HI -> PGS.fill_buffer_tb_specG RSEGS AD L HI ->
  PNRS.srd_read_v_spec L HI.
Proof.
  intros RSZ SRD FBT. unfold PNRS.srd_read_v_spec, PNR.srd_read_v_spec, PGV8.srd_read_v_specG.
  intros V VOK fx R M model K OB LBX cr sp r len src x g str sm HH MOK K0 EN SPLO A10 A11 A12 Hlen PA IA BASE INCS UN SZ ROOM CRL KONT.
  unfold PMSP.entry in EN. destruct EN as (E1 & RA & E2 & E3 & E4 & STK).
  change (PMSP.pm_scr 5) with 22528 in STK. cbn [PNL.pn_srd_read_v PnLayoutS_u.NADDR_S].
  pose proof (PGV8.vo_src _ _ _ _ _ VOK M src x g OB PA) as (_ & _ & _ & _ & TB).
  apply (entry_ok R M model K LBX cr sp r len V OB src x g str sm VOK E1 RA E2 E3 E4 K0 SPLO Hlen INCS UN SZ ROOM RSZ SRD FBT KONT fx HH MOK STK A10 A11 A12 PA IA BASE TB CRL).
Qed.

End WithHeap.
End PNSSV5.
