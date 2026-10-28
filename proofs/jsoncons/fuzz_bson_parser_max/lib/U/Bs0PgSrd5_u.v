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
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdP_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PgSrd1_u Bs0PgSrd2_u Bs0PgSrd3_u Bs0PgSrd4_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSR5.
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
#[local] Abbreviation own2 := PGSSR1.own2.
#[local] Abbreviation finish := (PGSSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PGSSR1.call_resize L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PGSSR1.call_srcread L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PGSSR1.call_filltb L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PGSSR1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation rpath := (PGSSR3.rpath L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
#[local] Abbreviation dpath := (PGSSR4.dpath L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma head mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w : Z) :
  lstate R M model src tb tg sm cr w -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x393d8 M model) K.
Proof using All.
  intros LS MU. pose proof LS as ((A2 & A8 & A9 & A18 & A21 & A22 & KP) & SO & AC & Hw).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct (tsrc M src tb tg PA) as ((F1 & _ & _ & _ & F5 & _ & F7 & _) & _).
  change PM.CHUNK with 16384 in F5, RM.
  destruct (Z.eq_dec (PM.sr_rem src) 0) as [RZ|RNZ].
  - (* [comment removed for export] *)
    rewrite RZ in F7.
    pose proof IA as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
    cbn [pa_vp_iss AD PnLayoutS_u.ADDR_S] in I0.
    destruct IOS as (_ & U32 & _).
    pose proof (PMTK2.u8_of_u32 RSEGS M (ois + 120 + 32) (PM.sm_st sm) ltac:(lia) U32) as B152.
    rewrite Z.mod_small in B152 by lia.
    pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72). bvr.
    pose proof BASE as (IMG & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG.
    LeanFeed.pfeed PP (PMSSRP.tsH0_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
       | 38%nat => ois | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
       | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
       | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 52%nat => PM.sm_st sm | 54%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E19 & C0 & C1) | [(MS & KS & E1 & E10 & E11 & E19 & C0 & C1)
                                                 | (MS & KS & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & C0)]]).
    + (* [comment removed for export] *)
      assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x393d8 R1 0x39404 M K Mh Ml MS).
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (rpath mu0 IH fx1 R1 M model src tb tg sm cr w w); try assumption.
      * unfold PGSSR1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
        kept_tac KS KP.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * right. exact ST0.
    + (* [comment removed for export] *)
      assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x393d8 R1 0x39470 M K Mh Ml MS).
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (dpath mu0 IH fx1 R1 M model src tb tg sm cr w); try assumption.
      * unfold PGSSR1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
        kept_tac KS KP.
      * lia.
    + (* [comment removed for export] *)
      assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
      unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x393d8 R1 0x39520 M K Mh Ml MS).
      apply (PGSSR1.finish L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT
               fx1 R1 M model src tb tg sm cr w); try assumption.
      * kept_tac KS KP.
      * lia.
  - (* [comment removed for export] *)
    LeanFeed.pfeed PP (PMSSRP.tsH1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
       | 37%nat => PM.sr_rem src | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & [(MS & KS & E1 & E10 & E11 & E19 & C0) | (MS & KS & E1 & E10 & E11 & E19 & C0)]);
      (assert (EM : M1 = M) by (apply functional_extensionality; exact FRw)); subst M1;
      unfold PMSP.cfg; apply (PMK.spiece_ro RSEGS model fx fx1 R 0x393d8 R1 0x39404 M K Mh Ml MS).
    + apply (rpath mu0 IH fx1 R1 M model src tb tg sm cr w w); try assumption.
      * unfold PGSSR1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
        kept_tac KS KP.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * left. lia.
    + apply (rpath mu0 IH fx1 R1 M model src tb tg sm cr w 16384); try assumption.
      * unfold PGSSR1.lregs.
        split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
        split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
        split; [rewrite (KS 21%nat) by PMK.inl; exact A21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
        kept_tac KS KP.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * left. lia.
Qed.

(* [comment removed for export] *)
Lemma loop (n : nat) : forall (fx : FPState) R M model src tb tg sm cr w,
  (Z.to_nat (PM.mu_src src sm) < n)%nat -> lstate R M model src tb tg sm cr w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x393d8 M model) K.
Proof using All.
  induction n as [|n IHn]; intros fx R M model src tb tg sm cr w Hn LS; [lia|].
  assert (IHm : IHt (PM.mu_src src sm)).
  { intros fx' R' M' model' s' tb' tg' sm' cr' w' Hlt LS'. apply (IHn fx' R' M' model' s' tb' tg' sm' cr' w'); [|exact LS'].
    pose proof LS' as (_ & SO' & _). pose proof (unread_nn _ _ _ _ _ _ _ SO') as (UN' & _).
    assert (0 <= PM.mu_src s' sm') by (unfold PM.mu_src; destruct (Z.eqb _ _); lia). lia. }
  exact (head _ IHm fx R M model src tb tg sm cr w LS ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_ok (fx : FPState) :
  hi_heap HI (PM.src_own src0 ++ PM.vs_own tb0 ++ OB ++ LBX) cr0 M0 (m_vmmaps model0) -> PMSP.model_ok model0 -> L5C.stk (hl_sptop L) M0 S 22528 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 otb -> getr R0 (reg 12) = Z_to_bv 64 len ->
  PGS.tw_at T M0 src0 tb0 tg0 OB -> PM.iss_at RSEGS AD T3 M0 ois str sm0 -> PMST.base_ok RSEGS AD M0 ->
  PM.tb_ok tb0 tg0 -> PMSP.credit_le (PM.pot_text L tb0 tg0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x39398 M0 model0) K.
Proof using All.
  intros HH MOK STK A10 A11 A12 PA IA BASE TBOK CRL.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof (L5C.stk_writable RSEGS _ M0 S 22528 STK) as WR.
  set (LBc := PM.src_own src0 ++ PM.vs_own tb0 ++ OB ++ LBX) in HH.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_refl).
  assert (INL : incl (OB ++ LBX) LBc) by (intros x Hx; unfold LBc; rewrite own2; apply in_or_app; right; exact Hx).
  LeanFeed.pfeed PP (PMSSRP.tsA_conc fx R0 M0 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
  set (P := fun a => S - 80 <= a < S - 80 + 80).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= S - 80 \/ S <= a) -> L5C.agree_on M0 M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ; lia. }
  assert (AGH : forall B m, In (B, m) LBc -> L5C.agree_on M0 M1 B m).
  { intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4). unfold hl_ceil in Q4. apply AG; lia. }
  assert (EKw : forall scr, 80 <= scr <= 22528 -> PMK.ek L (OB ++ LBX) S scr W0 M0 M1).
  { intros scr Hs. apply (PMK.ek_piece_in RSEGS L KL (OB ++ LBX) S scr W0 M0 M1 P); [intros a Ha N; apply FRZ; [exact Ha| exact N]| | |].
    - apply (PMK.stk_call L M0 S 22528 S scr STK); [lia|lia|lia| exact A16].
    - exact (PMFR.brange_hi L (OB ++ LBX) (PMFR.brange_incl L (OB ++ LBX) _ BR INL)).
    - intros a Pa. left. unfold P in Pa. lia. }
  pose proof (EKw 22528 ltac:(lia)) as EKn.
  assert (SPC : forall pc1, msteps RSEGS (@mkst fx R0 (Z_to_bv 64 0x39398) M0 (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
            (hi_heap HI LBc cr0 M1 (m_vmmaps model0) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model0) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x39398 M0 model0) K).
  { intros pc1 MS NEXT. unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok LBc cr0 M0 model0 fx fx1 R0 0x39398 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
    - intros a Ha N. apply FRZ; [exact Ha| exact N].
    - intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L LBc M0 S 22528 a STK). lia.
    - intros a. unfold P. apply PMK.rng_dec.
    - exact NEXT. }
  assert (SO1 : forall (C1 : L5.u64_at RSEGS M1 (S - 64) (bv_unsigned (getr R0 (reg 22)))) (C2 : L5.u64_at RSEGS M1 (S - 56) (bv_unsigned (getr R0 (reg 21))))
                       (C3 : L5.u64_at RSEGS M1 (S - 48) (bv_unsigned (getr R0 (reg 20)))) (C4 : L5.u64_at RSEGS M1 (S - 40) (bv_unsigned (getr R0 (reg 19))))
                       (C5 : L5.u64_at RSEGS M1 (S - 32) (bv_unsigned (getr R0 (reg 18)))) (C6 : L5.u64_at RSEGS M1 (S - 24) (bv_unsigned (getr R0 (reg 9))))
                       (C7 : L5.u64_at RSEGS M1 (S - 16) (bv_unsigned (getr R0 (reg 8)))) (C8 : L5.u64_at RSEGS M1 (S - 8) (bv_unsigned (getr R0 (reg 1))))
                       (C9 : L5.u64_at RSEGS M1 (S - 72) (bv_unsigned (getr R0 (reg 23)))),
               hi_heap HI LBc cr0 M1 (m_vmmaps model0) -> state_ok M1 model0 src0 tb0 tg0 sm0 cr0).
  { intros C1 C2 C3 C4 C5 C6 C7 C8 C9 HH1.
    destruct (tsrc M0 src0 tb0 tg0 PA) as (PSF & _ & _ & VS & _).
    assert (INC : In (PM.sr_qc src0, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; left; reflexivity).
    destruct (BR _ _ INC) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
    split; [split; [|split]|].
    - exact EKn.
    - apply PMK.dk_grows. exact MG.
    - exact (PMK.stk_grows L M0 M1 S 22528 MG STK).
    - split; [unfold PGSSR1.saves9; repeat split; assumption|].
      split.
      { apply (tw_xfer M0 M1 src0 src0 tb0 tb0 tg0 tg0 cr0 (m_vmmaps model0) 22528 S 80 [] PA HH STK ltac:(lia) ltac:(lia) ltac:(lia)); [| constructor| | reflexivity| | exact TBOK].
        - apply (PMK.hpres_of L (OB ++ LBX) S 80 _ M0 M1).
          + rewrite app_nil_r. exact (EKw 80 ltac:(lia)).
          + apply (L5.defined_grows M0 M1 _ _ MG). intros i Hi. replace (S - 80 + i) with (S - 22528 + (22528 - 80 + i)) by lia. apply SDEF. lia.
          + apply PMK.dk_grows. exact MG.
        - apply (PMF.src_fields_at_agree RSEGS M0 M1 os ois (ois + 16) src0); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AG; lia| exact (AGH _ _ INC)| exact PSF].
        - apply (PMF.vstr_at_agree RSEGS M0 M1 otb tb0); [lia|lia| apply AG; lia| |exact VS].
          intros c n p E. apply AGH. unfold LBc. rewrite E. apply in_or_app. right. left. reflexivity. }
      split.
      { apply (PMF.iss_at_agree RSEGS AD M0 M1 ois str sm0); [lia|lia| apply AG; lia| |exact IA].
        intros c n p E. apply AGH. unfold LBc. apply PGSSR1.in4. apply INCS. rewrite E. left. reflexivity. }
      split; [exact (base_keep M0 M1 EKn STK BASE)|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|].
      split; [exact CRL| unfold PMSP.credit_keep; lia]. }
  pose proof (unread_nn M0 model0 src0 tb0 tg0 sm0 cr0) as UNX.
  destruct EX as [(MS & KS & E2 & E8 & E9 & E18 & E21 & E22 & C0 & C9 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) | (MS & KS & E10 & C0 & C9 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8)];
    apply (SPC _ MS); intros HH1; pose proof (SO1 C1 C2 C3 C4 C5 C6 C7 C8 C9 HH1) as SOk.
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0 by lia.
    pose proof (unread_nn M1 model0 src0 tb0 tg0 sm0 cr0 SOk) as (UN & _).
    apply (loop (Nat.succ (Z.to_nat (PM.mu_src src0 sm0))) fx1 R1 M1 model0 src0 tb0 tg0 sm0 cr0 len); [apply Nat.lt_succ_diag_r|].
    split; [|split; [exact SOk| split; [|lia]]].
    + unfold PGSSR1.lregs. split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E21|]. split; [exact E22|].
      intros x Hx. rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). reflexivity.
    + unfold PGSSR1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [lia|]. split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia].
  - (* [comment removed for export] *)
    rewrite Z.sub_0_r, Z.mod_small in C0 by lia. assert (L0 : len = 0) by lia.
    apply (finish fx1 R1 M1 model0 src0 tb0 tg0 sm0 cr0 0); try assumption.
    all: try (rewrite (KS 2%nat) by PMK.inl; exact Rsp0).
    all: try (rewrite (KS _) by PMK.inl; symmetry; apply Z_to_bv_bv_unsigned).
    + intros x Hx; rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity); reflexivity.
    + rewrite E10; f_equal; lia.
    + lia.
    + unfold PGSSR1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [lia|].
      split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia].
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem srd_read_okG : PMS.str_resize_spec L HI -> PGS.src_read_specG RSEGS AD L HI -> PGS.fill_buffer_tb_specG RSEGS AD L HI ->
  PGS.srd_read_specG RSEGS AD L HI (pa_srd_read AD).
Proof.
  intros RSZ SRD FBT T TOK fx R M model K OB LBX cr sp r len src tb tg str sm HH MOK K0 EN SPLO A10 A11 A12 Hlen PA IA BASE INCS UN UNS CRL KONT.
  unfold PMSP.entry in EN. destruct EN as (E1 & RA & E2 & E3 & E4 & STK).
  change (PMSP.pm_scr 5) with 22528 in STK. cbn [pa_srd_read AD PnLayoutS_u.ADDR_S].
  pose proof (PGS.to_src _ _ _ _ _ TOK M src tb tg OB PA) as (_ & _ & _ & _ & TB).
  apply (entry_ok R M model K LBX cr sp r len T OB src tb tg str sm TOK E1 RA E2 E3 E4 K0 SPLO Hlen INCS UNS RSZ SRD FBT KONT fx HH MOK STK A10 A11 A12 PA IA BASE TB CRL).
Qed.

End WithHeap.
End PGSSR5.
