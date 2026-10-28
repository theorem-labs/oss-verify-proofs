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
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2 PgSrc PgSrcKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PgSrd1_u PnSRdSpanP_u Bs0_code_r36ef4_36ef8_u Bs0PgRdSpan1_u PnSReset_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRS2.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.

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
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis FBS : PGS.fill_buffer_specG RSEGS AD L HI.
Hypothesis SRDS : PGS.srd_read_specG RSEGS AD L HI (pa_srd_read AD).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z)
                         (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PM.vs_own tb' ++ OB) ptr n \/ (otb + 1 <= ptr /\ ptr + n <= otb + 24)) ->
  L5.defined M' ptr n ->
  PGS.tw_at T M' src' tb' tg' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 6) (PGS.W_srcfG os ois ++ [(otb, 24)]) M0 M' ->
  PMSP.credit_keep cr0 cr' (PM.pot_text L tb0 tg0) (PM.pot_text L tb' tg') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PM.vs_own tb' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGSSR1.lay L HI T TOK).
#[local] Abbreviation lay0 := (PGSSR1.lay0 L HI T TOK).
#[local] Abbreviation tsrc := (PGSSR1.tsrc L HI T OB TOK).
#[local] Abbreviation own2 := PGSSR1.own2.
#[local] Abbreviation base_keep := (PGSRS1.base_keep L HI LY LBX S T TOK SPLO).
#[local] Abbreviation st_piece := (PGSRS1.st_piece L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation src_keep_P := (PGSRS1.src_keep_P L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation vstr_keep_P := (PGSRS1.vstr_keep_P L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation W0 := (PGSSR1.W0 T).
#[local] Abbreviation saves4 := (PGSRS1.saves4 R0 S).
#[local] Abbreviation kept_rs := (PGSRS1.kept_rs R0).
#[local] Abbreviation memrel := (PGSRS1.memrel L M0 LBX S T).
#[local] Abbreviation st_ok := (PGSRS1.st_ok L HI R0 M0 model0 LBX cr0 S T OB tb0 tg0 str).
#[local] Abbreviation bregs := (PGSRS1.bregs R0 S len T).
#[local] Abbreviation finish_rs := (PGSRS1.finish_rs L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation call_fill := (PGSRS1.call_fill L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PGSRS1.call_srd L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
#[local] Abbreviation unread_nn := (PGSRS1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 FBS SRDS KONT).
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat.
Lemma zbv_mod (z : Z) : Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma src_step_trans a b c sa sb sc : PMSP.src_step a b sa sb -> PMSP.src_step b c sb sc -> PMSP.src_step a c sa sc.
Proof.
  unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fast (fx : FPState) R M model src tb tg sm cr :
  bregs R -> getr R (reg 11) = Z_to_bv 64 (PM.sr_rem src) -> 1 <= len <= PM.sr_rem src ->
  st_ok M model src tb tg sm cr -> PMSP.src_step src0 src sm0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x392c0 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & KP) A11 Hl SO STEP.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12). pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  destruct (tsrc M src tb tg PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _) & _ & PD & _).
  set (qc := PM.sr_qc src) in *. set (de := PM.sr_de src) in *. set (rem := PM.sr_rem src) in *.
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (QIN : In (qc, PM.CHUNK) (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  destruct (BR qc PM.CHUNK QIN) as (Q0 & _ & Q4).
  unfold PM.CHUNK in *.
  destruct (PMTK.u64_of_defined RSEGS M (os + 256) ltac:(lia) ltac:(destruct STOP; lia) F3) as (pos & Hpos & POS).
  assert (DE : 1 <= de <= 2 ^ 47) by (unfold hl_ceil in Q4; destruct STOP; lia).
  LeanFeed.pfeed PP (PMSRPP.rpF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => rem
       | 37%nat => de | 38%nat => pos | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & E10 & E12 & E13).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x392c0 R1 0x392d8 M K Mh Ml MS1).
  pose proof (Z.mod_pos_bound (len + pos) (2 ^ 64) ltac:(lia)) as HP49.
  pose proof SV as (S8 & S16 & S24 & S32). bvr.
  assert (WF : L5.writable RSEGS M (os + 256) 40).
  { apply (L5C.writable_of_defined RSEGS M _ 40); [| lia| destruct STOP; lia].
    apply (L5.defined_sub M os 296 (os + 256) 40 PD); lia. }
  LeanFeed.pfeed PP (PMSRPP.rpG_conc fx1 R1 M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 37%nat => de
       | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
       | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => rem | 49%nat => len + de | 50%nat => pos | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & E1 & E2 & E8 & E9 & E11' & E13' & E18 & C0u & C1 & C2).
  assert (C0 : L5.u64_at RSEGS M2 (os + 288) (-1 * len + rem)).
  { replace (-1 * len + rem) with ((((18446744073709551615 * len) mod 2 ^ 64) + rem) mod 2 ^ 64); [exact C0u|].
    rewrite Z.add_mod_idemp_l by lia. replace (18446744073709551615 * len + rem) with ((-1 * len + rem) + len * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  set (P := fun a => (os + 256 <= a < os + 256 + 8) \/ (os + 280 <= a < os + 280 + 16)).
  apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M model fx1 fx2 R1 0x392d8 R2 0x39384 M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2).
  { intros a Ha N. apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) M S 24576 a STK). lia. }
  { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH2.
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= os + 256 \/ os + 264 <= a) -> (a + m <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M2 a m).
  { intros a m Ha Hm X Y i Hi. apply FRZ2; lia. }
  set (src' := PM.SRC qc (len + de) (-1 * len + rem)).
  assert (SO2 : st_ok M2 model src' tb tg sm cr).
  { apply (st_piece M M2 model src src' tb tb tg sm cr P SO MG2);
      [intros a Ha N; apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]
      | intros a Pa; left; unfold P in Pa; lia | | reflexivity | | exact TBOK | reflexivity | reflexivity | exact HH2].
    - unfold src', PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F1]|].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F2]|].
      split; [apply (L5.defined_grows M M2 _ _ MG2); exact F3|].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F4]|].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F5]|].
      split; [exact C1|]. split; [exact C0|].
      split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact G4|].
      split; [apply (L5.defined_grows M M2 _ _ MG2); exact DC|]. split; exact I.
    - apply (vstr_keep_P M M2 model src tb tg sm cr P SO MG2); [intros a Ha N; apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]|].
      intros a Pa. unfold P in Pa. pose proof lay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DJ1 & DJ2 & DJ3). split; [lia|].
      intros c n q E. destruct (BR q c ltac:(rewrite E; apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (_ & _ & Z4). unfold hl_ceil in Z4. lia. }
  apply (finish_rs fx2 R2 M2 model src' tb tg sm cr de len); try assumption.
  - intros x Hx. rewrite (KS2 x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
    rewrite (KS1 x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
  - rewrite (KS2 10%nat) by PMK.inl. exact E10.
  - lia.
  - lia.
  - right. left. exists qc, 16384. split; [unfold src', PM.src_own; left; reflexivity| lia].
  - intros i Hi. apply MG2. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
  - unfold PMSP.src_step in *. cbn [PM.sr_qc PM.sr_rem] in *. unfold src'.
    apply (src_step_trans _ _ _ _ _ _ STEP). unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| unfold rem; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srd (fx : FPState) R M model src tb tg sm cr :
  getr R (reg 1) = Z_to_bv 64 234316 -> bregs R -> getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 otb ->
  getr R (reg 12) = Z_to_bv 64 len ->
  st_ok M model src tb tg sm cr -> PMSP.src_step src0 src sm0 sm -> PM.vs_size tb = 0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39398 M model) K.
Proof using All.
  intros A1 (A2 & A8 & A9 & A18 & KP) A10 A11 A12 SO STEP SZ0.
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  assert (UNs : PM.unread src sm < 2 ^ 26) by (destruct STEP as (_ & _ & _ & _ & U); lia).
  apply (call_srd fx R M model src tb tg sm cr 234316 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO UNs ltac:(lia)).
  intros fx2 R2 M2 model2 src2 tb2 tg2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 STEP2 SO2.
  pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & MOK2 & MB2 & CRL2 & CRK2).
  pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12). pose proof MOK2 as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M2 S 24576 STK2) as WR.
  pose proof (unread_nn M2 model2 src2 tb2 tg2 sm2 cr2 SO2) as (UN2 & _).
  assert (Hd2 : d < 2 ^ 26) by (unfold PMSP.consumed in CONS2; lia).
  pose proof (tsrc M2 src2 tb2 tg2 PA2) as (_ & _ & _ & VS & _).
  assert (STEP02 : PMSP.src_step src0 src2 sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  pose proof SV2 as (S8 & S16 & S24 & S32). bvr.
  destruct VS as (VD & _ & VS). destruct tb2 as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ2.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
    assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 32)) by (rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl; exact A2).
    assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl; exact A8).
    assert (B9 : getr R2 (reg 9) = Z_to_bv 64 os) by (rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl; exact A9).
    assert (B18 : getr R2 (reg 18) = Z_to_bv 64 otb) by (rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl; exact A18).
    LeanFeed.pfeed PP (PMSRPP.rpES_conc fx2 R2 M2 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 39%nat => 2 * n1
         | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
         | 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx3 & R3 & M3 & MG3 & FRw & _ & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRw). subst M3.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x3934c R3 0x39384 M2 K Mh Ml MS3).
    apply (finish_rs fx3 R3 M2 model2 src2 (PM.VShort n1) tg2 sm2 cr2 (otb + 1) n1); try assumption.
    + intros x Hx. rewrite (KS3 x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
      rewrite (PMK.cs_of_preserved R R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + rewrite <- (Z_to_bv_bv_unsigned _ (getr R3 (reg 11))), E11. f_equal. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
    + lia.
    + lia.
    + right. right. lia.
    + apply (L5.defined_sub M2 otb 24 (otb + 1) n1 VD); lia.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
    pose proof (PMF.u8_of_u64 RSEGS M2 otb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (BR : PMFR.brange L (PM.src_own src2 ++ PM.vs_own (PM.VLong c1 n1 q1) ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M2 _ HH2); apply incl_refl).
    assert (IN : In (q1, c1) (PM.src_own src2 ++ PM.vs_own (PM.VLong c1 n1 q1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    destruct (BR q1 c1 IN) as (Q0 & _ & Q4).
    assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 32)) by (rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl; exact A2).
    assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl; exact A8).
    assert (B9 : getr R2 (reg 9) = Z_to_bv 64 os) by (rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl; exact A9).
    assert (B18 : getr R2 (reg 18) = Z_to_bv 64 otb) by (rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl; exact A18).
    LeanFeed.pfeed PP (PMSRPP.rpEL_conc fx2 R2 M2 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 39%nat => (c1 + 1) mod 256
         | 40%nat => n1 | 41%nat => q1 | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
         | 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx3 & R3 & M3 & MG3 & FRw & _ & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRw). subst M3.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x3934c R3 0x39384 M2 K Mh Ml MS3).
    apply (finish_rs fx3 R3 M2 model2 src2 (PM.VLong c1 n1 q1) tg2 sm2 cr2 q1 n1); try assumption.
    + intros x Hx. rewrite (KS3 x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
      rewrite (PMK.cs_of_preserved R R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
    + lia.
    + lia.
    + right. left. exists q1, c1. split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| lia].
    + apply (L5.defined_sub M2 q1 c1 q1 n1 DQ); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slow (fx : FPState) R M model src tb tg sm cr :
  bregs R -> 1 <= len -> st_ok M model src tb tg sm cr -> PMSP.src_step src0 src sm0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39318 M model) K.
Proof using All.
  intros BR0 Hl SO STEP. pose proof BR0 as (A2 & A8 & A9 & A18 & KP).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12). pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (tsrc M src tb tg PA) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _) & _ & PD & VS & _).
  pose proof lay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DJ1 & DJ2 & DJ3).
  assert (INC : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply in_or_app; left; unfold PM.src_own; left; reflexivity).
  destruct (BR _ _ INC) as (C0' & _ & C4').
  pose proof (PMPK.heap_nodup L HI HIok _ _ _ _ HH) as NDL.
  destruct VS as (VD & _ & VS). destruct tb as [n0|c0 n0 q0].
  - (* [comment removed for export] *)
    destruct VS as (Hn0 & B0). pose proof (PMF.even_byte n0) as EV.
    assert (W2 : L5.writable RSEGS M otb 2) by (apply (L5C.writable_of_defined RSEGS M _ 2); [apply (L5.defined_sub M otb 24 _ 2 VD); lia| lia| destruct STOP; lia]).
    LeanFeed.pfeed PP (PMSRPP.rpSS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 39%nat => 2 * n0 | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & (C0 & C1)).
    set (P := fun a => otb + 0 <= a < otb + 0 + 2).
    apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PM.vs_own (PM.VShort n0) ++ OB ++ LBX) cr M model fx fx1 R 0x39318 R1 0x39398 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
    { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PM.vs_own (PM.VShort n0) ++ OB ++ LBX) M S 24576 a STK). lia. }
    { intros a. unfold P. apply PMK.rng_dec. }
    intros HH1.
    assert (SO1 : st_ok M1 model src (PM.VShort 0) tg sm cr).
    { apply (st_piece M M1 model src src (PM.VShort n0) (PM.VShort 0) tg sm cr P SO MG1);
        [intros a Ha N; apply FRZ1; [exact Ha| exact N] | intros a Pa; right; left; unfold P in Pa; lia | | reflexivity | | | reflexivity | reflexivity | exact HH1].
      - apply (src_keep_P M M1 model src (PM.VShort n0) tg sm cr P SO MG1); [intros a Ha N; apply FRZ1; [exact Ha| exact N]|]. intros a Pa. unfold P in Pa. lia.
      - split; [intros i Hi; apply MG1; apply VD; exact Hi|]. split; [exact I|]. split; [lia|]. replace (2 * 0) with 0 by lia. exact C0.
      - unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK. }
    apply (at_srd fx1 R1 M1 model src (PM.VShort 0) tg sm cr); try assumption.
    + unfold PGSRS1.bregs.
      split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
      kept_tac KS1 KP.
    + reflexivity.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn0 & Hc0 & Hce & DQ & _).
    pose proof (PMF.u8_of_u64 RSEGS M otb (c0 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c0 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c0 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c0 + 1) 256 ltac:(lia)); lia).
    assert (TIN : In (q0, c0) (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    destruct (BR q0 c0 TIN) as (T0 & T1 & T4).
    assert (Wq : L5.writable RSEGS M q0 1) by (apply (L5C.writable_of_defined RSEGS M _ 1); [apply (L5.defined_sub M q0 c0 _ 1 DQ); lia| lia| lia]).
    assert (W8' : L5.writable RSEGS M (otb + 8) 8) by (apply (L5C.writable_of_defined RSEGS M _ 8); [apply (L5.defined_sub M otb 24 _ 8 VD); lia| lia| destruct STOP; lia]).
    LeanFeed.pfeed PP (PMSRPP.rpSL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 39%nat => (c0 + 1) mod 256
         | 41%nat => q0 | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & C0 & C1).
    set (P := fun a => (q0 + 0 <= a < q0 + 0 + 1) \/ (otb + 8 <= a < otb + 8 + 8)).
    apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX) cr M model fx fx1 R 0x39318 R1 0x39398 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
    { intros a Pa. unfold P in Pa. destruct Pa as [X|X].
      - apply (PMK.cwr_block L (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX) q0 c0 a TIN). lia.
      - apply (PMK.cwr_stack L (PM.src_own src ++ PM.vs_own (PM.VLong c0 n0 q0) ++ OB ++ LBX) M S 24576 a STK). lia. }
    { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= q0 \/ q0 + 1 <= a) -> (a + m <= otb + 8 \/ otb + 16 <= a) -> L5C.agree_on M M1 a m).
    { intros a m Ha Hm X Y i Hi. apply FRZ1; lia. }
    assert (SO1 : st_ok M1 model src (PM.VLong c0 0 q0) tg sm cr).
    { apply (st_piece M M1 model src src (PM.VLong c0 n0 q0) (PM.VLong c0 0 q0) tg sm cr P SO MG1);
        [intros a Ha N; apply FRZ1; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]
        | intros a Pa; unfold P in Pa; destruct Pa as [X|X]; [right; right; exists c0, n0, q0; split; [reflexivity| lia]| right; left; lia] | | reflexivity | | | reflexivity | reflexivity | exact HH1].
      - apply (src_keep_P M M1 model src (PM.VLong c0 n0 q0) tg sm cr P SO MG1); [intros a Ha N; apply FRZ1; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]|].
        intros a Pa. unfold P in Pa. unfold hl_ceil in T4. lia.
      - split; [intros i Hi; apply MG1; apply VD; exact Hi|]. split; [exact I|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W0']|].
        split; [exact C0|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact W16]|].
        split; [lia|]. split; [lia|]. split; [exact Hce|]. split; [intros i Hi; apply MG1; apply DQ; exact Hi| exact I].
      - unfold PM.tb_ok in *. cbn [PM.vs_cap] in *. exact TBOK. }
    apply (at_srd fx1 R1 M1 model src (PM.VLong c0 0 q0) tg sm cr); try assumption.
    + unfold PGSRS1.bregs.
      split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
      kept_tac KS1 KP.
    + reflexivity.
Qed.

End Call.
End WithHeap.
End PGSRS2.
