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
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSRdSpanVP_u Bs0_code_37954_37958_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSVu8Grow_u PnSSrdV1_u PnSRdSpanV1_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSRSV2.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation v8_atP := (PGV8.v8_at RSEGS PMSP.T3 PMSP.T4).
Ltac kept_tac KS KP := intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); apply KP; exact Hy.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
#[local] Abbreviation own2 := PNSSV1.own2.

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
Hypothesis ROOM0 : PGV8.v8_room x0 (PM.unread src0 sm0).
Hypothesis FBS : PGS.fill_buffer_specG RSEGS AD L HI.
Hypothesis SRDS : PNRS.srd_read_v_spec L HI.
#[local] Abbreviation W0 := (PNSSV1.W0 V).
#[local] Abbreviation lay := (PNSSV1.lay L HI V VOK).
#[local] Abbreviation tsrc := (PNSSV1.tsrc L HI V OB VOK).
#[local] Abbreviation inW_W0' := (PNSSV1.inW_W0' L HI V VOK).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : PGV8.v8) (g' : Z)
                         (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  PMSP.consumed src0 src' sm0 sm' = n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PGV8.v8_own x' ++ OB) ptr n) ->
  L5.defined M' ptr n ->
  (n = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at V M' src' x' g' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 6) (PGS.W_srcfG os ois ++ [(ov, 24)]) M0 M' ->
  PMSP.credit_keep cr0 cr' (PGV8.pot_v8 L x0 g0) (PGV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.


#[local] Abbreviation own2 := PNSSV1.own2.
#[local] Abbreviation base_keep := (PNSRSV1.base_keep L HI LY LBX S V VOK SPLO).
#[local] Abbreviation st_piece := (PNSRSV1.st_piece L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation src_keep_P := (PNSRSV1.src_keep_P L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation v8_keep_P := (PNSRSV1.v8_keep_P L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation saves4 := (PNSRSV1.saves4 R0 S).
#[local] Abbreviation kept_rs := (PNSRSV1.kept_rs R0).
#[local] Abbreviation memrel := (PNSRSV1.memrel L M0 LBX S V).
#[local] Abbreviation st_ok := (PNSRSV1.st_ok L HI R0 M0 model0 LBX cr0 S V OB x0 g0 str).
#[local] Abbreviation bregs := (PNSRSV1.bregs R0 S len V).
#[local] Abbreviation finish_rs := (PNSRSV1.finish_rs L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation call_fill := (PNSRSV1.call_fill L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PNSRSV1.call_srd L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
#[local] Abbreviation unread_nn := (PNSRSV1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 ROOM0 FBS SRDS KONT).
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
Lemma fast (fx : FPState) R M model src x g sm cr :
  bregs R -> getr R (reg 11) = Z_to_bv 64 (PM.sr_rem src) -> 1 <= len <= PM.sr_rem src ->
  st_ok M model src x g sm cr -> PMSP.src_step src0 src sm0 sm -> PM.unread src sm = PM.unread src0 sm0 ->
  PGV8.v8_room x (PM.unread src sm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x389b4 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & KP) A11 Hl SO STEP CONS0 RM0.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & DJ1 & DJ2 & DJ3). pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  destruct (tsrc M src x g PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _) & _ & PD & VS & TB).
  set (qc := PM.sr_qc src) in *. set (de := PM.sr_de src) in *. set (rem := PM.sr_rem src) in *.
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (QIN : In (qc, PM.CHUNK) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  destruct (BR qc PM.CHUNK QIN) as (Q0 & _ & Q4).
  unfold PM.CHUNK in *.
  destruct (PMTK.u64_of_defined RSEGS M (os + 256) ltac:(lia) ltac:(destruct STOP; lia) F3) as (pos & Hpos & POS).
  assert (DE : 1 <= de <= 2 ^ 47) by (unfold hl_ceil in Q4; destruct STOP; lia).
  LeanFeed.pfeed PP (PNSRVP.rvF_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => rem
       | 54%nat => de | 55%nat => pos | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG1 & FRw & _ & MS1 & KS1 & E10 & E12 & E13).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x389b4 R1 0x389cc M K Mh Ml MS1).
  assert (E13' : getr R1 (reg 13) = Z_to_bv 64 ((len + pos) mod 2 ^ 64 - len)).
  { rewrite E13, (zbv_mod pos), (zbv_mod ((len + pos) mod 2 ^ 64 - len)), Zminus_mod_idemp_l. replace (len + pos - len) with pos by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (len + pos) (2 ^ 64) ltac:(lia)) as HP49.
  pose proof SV as (S8 & S16 & S24 & S32). bvr.
  assert (WF : L5.writable RSEGS M (os + 256) 40).
  { apply (L5C.writable_of_defined RSEGS M _ 40); [| lia| destruct STOP; lia].
    apply (L5.defined_sub M os 296 (os + 256) 40 PD); lia. }
  LeanFeed.pfeed PP (PNSRVP.rvG_conc fx1 R1 M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len
       | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
       | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => -1 * len + rem | 49%nat => (len + pos) mod 2 ^ 64 | 50%nat => len + de | 54%nat => de | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & E1 & E2 & E8 & E9 & E11' & _ & E18 & C0 & C1 & C2).
  set (P := fun a => (os + 256 <= a < os + 256 + 8) \/ (os + 280 <= a < os + 280 + 16)).
  apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M model fx1 fx2 R1 0x389cc R2 0x38a64 M2 P K HH Mh Ml ltac:(destruct STOP; lia) MS2 MG2).
  { intros a Ha N. apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]. }
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) M S 24576 a STK). lia. }
  { intros a. unfold P. apply PMK.or_dec; apply PMK.rng_dec. }
  intros HH2.
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= os + 256 \/ os + 264 <= a) -> (a + m <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M2 a m).
  { intros a m Ha Hm X Y i Hi. apply FRZ2; lia. }
  set (src' := PM.SRC qc (len + de) (-1 * len + rem)).
  assert (SO2 : st_ok M2 model src' x g sm cr).
  { apply (st_piece M M2 model src src' x x g sm cr P SO MG2);
      [intros a Ha N; apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]
      | intros a Pa; left; unfold P in Pa; lia | | reflexivity | | exact TB | reflexivity | reflexivity | exact HH2].
    - unfold src', PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F1]|].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F2]|].
      split; [apply (L5.defined_grows M M2 _ _ MG2); exact F3|].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F4]|].
      split; [apply (L5C.u64_at_agree RSEGS M M2); [apply AG; lia| lia| lia| exact F5]|].
      split; [exact C1|]. split; [exact C0|].
      split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact G4|].
      split; [apply (L5.defined_grows M M2 _ _ MG2); exact DC|]. split; exact I.
    - apply (v8_keep_P M M2 model src x g sm cr P SO MG2); [intros a Ha N; apply FRZ2; [exact Ha| intro X; apply N; left; exact X| intro X; apply N; right; exact X]|].
      intros a Pa. unfold P in Pa. lia. }
  apply (finish_rs fx2 R2 M2 model src' x g sm cr de len); try assumption.
  - intros y Hy. rewrite (KS2 y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
    rewrite (KS1 y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
  - rewrite (KS2 10%nat) by PMK.inl. exact E10.
  - lia.
  - lia.
  - right. exists qc, 16384. split; [unfold src', PM.src_own; left; reflexivity| lia].
  - intros i Hi. apply MG2. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
  - intros _. apply (PGV8.v8_room_mono x (PM.unread src sm)); [| exact RM0]. unfold src', PM.unread. cbn [PM.sr_rem]. unfold PM.unread in UN. unfold rem. lia.
  - unfold PMSP.src_step in *. cbn [PM.sr_qc PM.sr_rem] in *. unfold src'.
    apply (src_step_trans _ _ _ _ _ _ STEP). unfold PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| unfold rem; lia].
  - unfold PMSP.consumed. rewrite <- CONS0. unfold src', PM.unread. cbn [PM.sr_rem]. unfold rem. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srd (fx : FPState) R M model src x g sm cr :
  getr R (reg 1) = Z_to_bv 64 232000 -> bregs R -> getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 ov ->
  getr R (reg 12) = Z_to_bv 64 len ->
  st_ok M model src x g sm cr -> PMSP.src_step src0 src sm0 sm -> PM.unread src sm = PM.unread src0 sm0 -> PGV8.v8_size x = 0 ->
  PGV8.v8_room x (PM.unread src sm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3956c M model) K.
Proof using All.
  intros A1 (A2 & A8 & A9 & A18 & KP) A10 A11 A12 SO STEP CONS0 SZ0 RMx.
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  assert (UNs : PM.unread src sm < 2 ^ 26) by lia.
  apply (call_srd fx R M model src x g sm cr 232000 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO UNs SZ0 RMx).
  intros fx2 R2 M2 model2 src2 x2 g2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 RM2 STEP2 SO2.
  pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & MOK2 & MB2 & CRL2 & CRK2).
  pose proof STK2 as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _). pose proof MOK2 as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M2 S 24576 STK2) as WR.
  pose proof (unread_nn M2 model2 src2 x2 g2 sm2 cr2 SO2) as (UN2 & _).
  assert (Hd2 : d < 2 ^ 26) by (unfold PMSP.consumed in CONS2; lia).
  assert (CONS02 : PMSP.consumed src0 src2 sm0 sm2 = d) by (unfold PMSP.consumed in *; lia).
  pose proof (tsrc M2 src2 x2 g2 PA2) as (_ & _ & _ & VS & _).
  assert (STEP02 : PMSP.src_step src0 src2 sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  pose proof SV2 as (S8 & S16 & S24 & S32). bvr.
  assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 32)) by (rewrite (PMK.cs_of_preserved R R2 2%nat RP2) by PMK.inl; exact A2).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (PMK.cs_of_preserved R R2 8%nat RP2) by PMK.inl; exact A8).
  assert (B9 : getr R2 (reg 9) = Z_to_bv 64 os) by (rewrite (PMK.cs_of_preserved R R2 9%nat RP2) by PMK.inl; exact A9).
  assert (B18 : getr R2 (reg 18) = Z_to_bv 64 ov) by (rewrite (PMK.cs_of_preserved R R2 18%nat RP2) by PMK.inl; exact A18).
  destruct VS as (VD & _ & VS). destruct x2 as [|b2 n2 c2]; cbn [PGV8.v8_size] in SZ2.
  - (* [comment removed for export] *)
    destruct VS as (U0 & U8 & U16).
    assert (U8' : L5.u64_at RSEGS M2 (ov + 8) (0 + 0)) by exact U8.
    LeanFeed.pfeed PP (PNSRVP.rvE_conc fx2 R2 M2 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 39%nat => 0 | 40%nat => 0
         | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
         | 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx3 & R3 & M3 & MG3 & FRw & _ & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRw). subst M3.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x38a40 R3 0x38a64 M2 K Mh Ml MS3).
    apply (finish_rs fx3 R3 M2 model2 src2 PGV8.V8Null g2 sm2 cr2 0 d); try assumption.
    + intros y Hy. rewrite (KS3 y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
      rewrite (PMK.cs_of_preserved R R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + rewrite E11. f_equal. lia.
    + left. split; [reflexivity| lia].
    + intros i Hi. lia.
  - (* [comment removed for export] *)
    destruct VS as (U0 & U8 & U16 & Hn2 & Hc2 & Hb2 & Hb16 & DQ & _).
    subst n2.
    assert (BR : PMFR.brange L (PM.src_own src2 ++ PGV8.v8_own (PGV8.V8Blk b2 d c2) ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M2 _ HH2); apply incl_refl).
    assert (IN : In (b2, c2) (PM.src_own src2 ++ PGV8.v8_own (PGV8.V8Blk b2 d c2) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    destruct (BR b2 c2 IN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
    LeanFeed.pfeed PP (PNSRVP.rvE_conc fx2 R2 M2 (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 39%nat => b2 | 40%nat => d
         | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
         | 47%nat => bv_unsigned (getr R0 (reg 18)) | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx3 & R3 & M3 & MG3 & FRw & _ & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRw). subst M3.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 0x38a40 R3 0x38a64 M2 K Mh Ml MS3).
    apply (finish_rs fx3 R3 M2 model2 src2 (PGV8.V8Blk b2 d c2) g2 sm2 cr2 b2 d); try assumption.
    + intros y Hy. rewrite (KS3 y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
      rewrite (PMK.cs_of_preserved R R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    + right. exists b2, c2. split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| lia].
    + apply (L5.defined_sub M2 b2 c2 b2 d DQ); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slow (fx : FPState) R M model src x g sm cr :
  bregs R -> 1 <= len -> st_ok M model src x g sm cr -> PMSP.src_step src0 src sm0 sm -> PM.unread src sm = PM.unread src0 sm0 ->
  PGV8.v8_room x (PM.unread src sm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x38a0c M model) K.
Proof using All.
  intros BR0 Hl SO STEP CONS0 RMx. pose proof BR0 as (A2 & A8 & A9 & A18 & KP).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & DJ1 & DJ2 & DJ3). pose proof MOK as (Mh & Ml & Mm).
  pose proof (L5C.stk_writable RSEGS _ M S 24576 STK) as WR.
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (tsrc M src x g PA) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & _ & _) & _ & PD & VS & TB).
  pose proof VS as VS0. destruct VS as (VD & V4 & VS).
  assert (W8' : L5.writable RSEGS M (ov + 8) 8) by (apply (L5C.writable_of_defined RSEGS M _ 8); [apply (L5.defined_sub M ov 24 _ 8 VD); lia| lia| destruct STOP; lia]).
  (* [comment removed for export] *)
  assert (HB : exists b, L5.u64_at RSEGS M ov b /\ 0 <= b < 2 ^ 64 /\ PGV8.v8_data x = b).
  { destruct x as [|b n c]; cbn [PGV8.v8_data].
    - destruct VS as (U0 & _). exists 0. split; [exact U0| lia].
    - destruct VS as (U0 & _ & _ & Hn & Hc & Hb & _).
      assert (IN : In (b, c) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b n c) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (BR b c IN) as (_ & _ & Q4). unfold hl_ceil in Q4. exists b. split; [exact U0| lia]. }
  destruct HB as (b & U0 & Hb & XB).
  assert (PP : exists fx' R' M', mem_grows M M'
      /\ (forall a : word, ~ ((ov + 8) <= bv_unsigned a < (ov + 8) + 8) -> M' a = M a)
      /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((ov + 8) <= i < (ov + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ (msteps RSEGS (@mkst fx R (Z_to_bv 64 0x38a0c) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0x3956c) M' (seg_rom RSEGS))
          /\ (forall y, In y PMK.cs_all -> getr R' (reg y) = getr R (reg y))
          /\ getr R' (reg 1) = Z_to_bv 64 232000 /\ getr R' (reg 10) = Z_to_bv 64 os /\ getr R' (reg 11) = Z_to_bv 64 ov
          /\ getr R' (reg 12) = Z_to_bv 64 len /\ L5.u64_at RSEGS M' (ov + 8) b)).
  { destruct x as [|b0 n0 c0]; cbn [PGV8.v8_data] in XB.
    - destruct VS as (_ & U8 & _). subst b.
      LeanFeed.pfeed PP (PNSRVP.rvSz_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 39%nat => 0 | _ => 0 end)) ltac:(first [PMK.sc]).
      destruct PP as (fx1 & R1 & M1 & MG1 & FRw1 & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & C0).
      exists fx1, R1, M1. refine (conj MG1 (conj FRw1 (conj FRZ1 (conj MS1 (conj _ (conj E1 (conj E10 (conj E11 (conj E12 C0))))))))).
      intros y Hy. apply KS1. revert y Hy. apply PNSSV1.sub_in. vm_compute. reflexivity.
    - destruct VS as (_ & U8 & _ & Hn0 & Hc0 & Hb0 & _). subst b0.
      destruct (Z_le_gt_dec n0 0) as [N0|N0].
      + assert (n0 = 0) as -> by lia. rewrite Z.add_0_r in U8.
        LeanFeed.pfeed PP (PNSRVP.rvSz_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 39%nat => b | _ => 0 end)) ltac:(first [PMK.sc]).
        destruct PP as (fx1 & R1 & M1 & MG1 & FRw1 & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & C0).
        exists fx1, R1, M1. refine (conj MG1 (conj FRw1 (conj FRZ1 (conj MS1 (conj _ (conj E1 (conj E10 (conj E11 (conj E12 C0))))))))).
        intros y Hy. apply KS1. revert y Hy. apply PNSSV1.sub_in. vm_compute. reflexivity.
      + assert (IN : In (b, c0) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b n0 c0) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
        destruct (BR b c0 IN) as (_ & _ & Q4). unfold hl_ceil in Q4.
        assert (B47 : 1 <= b <= 2 ^ 47) by (destruct STOP; lia).
        remember (2 ^ 64 - n0) as v eqn:Hv.
        assert (V40 : 18446744073575333888 <= v <= 18446744073709551615) by lia.
        assert (EW : (b - v) mod 2 ^ 64 = b + n0).
        { replace (b - v) with (b + n0 + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
        assert (U8' : L5.u64_at RSEGS M (ov + 8) ((b - v) mod 2 ^ 64)) by (rewrite EW; exact U8).
        assert (C11 : 0 <= (if ((b - ((b - v) mod 2 ^ 64)) mod 2 ^ 64) <? 1 then 1 else 0) <= 0).
        { rewrite EW. replace (b - (b + n0)) with (2 ^ 64 - n0 + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia.
          destruct (Z.ltb_spec (2 ^ 64 - n0) 1); lia. }
        LeanFeed.pfeed PP (PNSRVP.rvS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 39%nat => b | 40%nat => v | _ => 0 end)) ltac:(first [PMK.sc]).
        destruct PP as (fx1 & R1 & M1 & MG1 & FRw1 & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & _ & C0).
        exists fx1, R1, M1. refine (conj MG1 (conj FRw1 (conj FRZ1 (conj MS1 (conj _ (conj E1 (conj E10 (conj E11 (conj E12 C0))))))))).
        intros y Hy. apply KS1. revert y Hy. apply PNSSV1.sub_in. vm_compute. reflexivity. }
  destruct PP as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E10 & E11 & E12 & C0).
  set (P := fun a => ov + 8 <= a < ov + 8 + 8).
  apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M model fx fx1 R 0x38a0c R1 0x3956c M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) M S 24576 a STK). lia. }
  { intros a. unfold P. apply PMK.rng_dec. }
  intros HH1.
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= ov + 8 \/ ov + 16 <= a) -> L5C.agree_on M M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ1; lia. }
  assert (OWNc : PGV8.v8_own (PGV8.v8_clear x) = PGV8.v8_own x) by (destruct x; reflexivity).
  assert (CAPc : PGV8.v8_cap (PGV8.v8_clear x) = PGV8.v8_cap x) by (destruct x; reflexivity).
  assert (TBc : PGV8.v8_ok (PGV8.v8_clear x) g) by (destruct x; exact TB).
  assert (SO1 : st_ok M1 model src (PGV8.v8_clear x) g sm cr).
  { apply (st_piece M M1 model src src x (PGV8.v8_clear x) g sm cr P SO MG1);
      [intros a Ha N; apply FRZ1; [exact Ha| exact N] | intros a Pa; right; unfold P in Pa; lia | | reflexivity | | exact TBc | exact OWNc | exact CAPc | rewrite OWNc; exact HH1].
    - apply (src_keep_P M M1 model src x g sm cr P SO MG1); [intros a Ha N; apply FRZ1; [exact Ha| exact N]|]. intros a Pa. unfold P in Pa. lia.
    - split; [intros i Hi; apply MG1; apply VD; exact Hi|]. split; [exact V4|].
      destruct x as [|b0 n0 c0]; cbn [PGV8.v8_clear PGV8.v8_data] in *.
      + destruct VS as (_ & _ & U16). subst b.
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U0]|].
        split; [exact C0|].
        apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U16].
      + destruct VS as (_ & _ & U16 & Hn0 & Hc0 & Hb0 & Hb16 & DQ & A4 & AN). subst b.
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U0]|].
        split; [replace (b0 + 0) with b0 by lia; exact C0|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U16]|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hb16|].
        split; [intros i Hi; apply MG1; apply DQ; exact Hi|]. split; [exact I| exact I]. }
  apply (at_srd fx1 R1 M1 model src (PGV8.v8_clear x) g sm cr); try assumption.
  + unfold PNSRSV1.bregs.
    split; [rewrite (KS1 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS1 8%nat) by PMK.inl; exact A8|].
    split; [rewrite (KS1 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS1 18%nat) by PMK.inl; exact A18|].
    kept_tac KS1 KP.
  + destruct x; reflexivity.
  + apply PGV8.v8_room_clear. exact RMx.
Qed.

End Call.
End WithHeap.
End PNSRSV2.
