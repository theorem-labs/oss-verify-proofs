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
     PmTxtSpecs PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdVP_u Bs0_code_383d4_383d8_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit PgV8 PgV8Kit PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnSVu8Grow_u PnSSrdV1_u PnSSrdV2_u PnSSrdV3_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSSV4.
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
#[local] Abbreviation unread_nn := (PNSSV1.unread_nn L HI LY HIok R0 M0 model0 K LBX cr0 S r len V OB src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UN0 SZ0 ROOM0 RSZ SRD FBT KONT).

Ltac bvr1 R y := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg y))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.
Ltac kept_tac KS KP := intros y Hy; rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity); apply KP; exact Hy.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_upd M M1 model src x g sm cr : state_ok M model src x g sm cr -> mem_grows M M1 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 256 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  hi_heap HI (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M1 (m_vmmaps model) -> state_ok M1 model src x g sm cr.
Proof using All.
  intros SO MG FRZ HH1.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & DJ1 & DJ2 & DJ3).
  set (LBc := PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) in HH.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= os + 256 \/ os + 264 <= a) -> L5C.agree_on M M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ; lia. }
  assert (AGH : forall B m, In (B, m) LBc -> L5C.agree_on M M1 B m).
  { intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4). unfold hl_ceil in Q4. apply AG; lia. }
  assert (EKw : forall LB sp scr, PMK.ek L LB sp scr W0 M M1).
  { intros LB sp scr. apply (PMK.ek_piece L LB sp scr W0 M M1 (fun a => os + 256 <= a < os + 256 + 8)); [intros a Ha N; apply FRZ; [exact Ha| exact N]|].
    intros a Ha CA NE OW Pa. apply (OW (os + 256, 40)); [unfold PNSSV1.W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng; cbn [fst snd]. lia. }
  split; [split; [|split]|].
  - exact (PMK.ek_trans L (OB ++ LBX) S 22528 W0 M0 M M1 EK (EKw _ _ _)).
  - apply (PMK.dk_trans L (OB ++ LBX) S 22528 M0 M M1 DK). apply PMK.dk_grows. exact MG.
  - exact (PMK.stk_grows L M M1 S 22528 MG STK).
  - split.
    { destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64).
      unfold PNSSV1.saves8. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption]). }
    split.
    { destruct (tsrc M src x g PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _) & _ & _ & VS & _).
      assert (INQ : In (PM.sr_qc src, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; left; reflexivity).
      destruct (BR _ _ INQ) as (C0 & _ & C4). unfold hl_ceil in C4.
      apply (vw_xfer M M1 src src x x g g cr (m_vmmaps model) 22528 S 0 [] PA HH STK ltac:(lia) ltac:(lia) ltac:(lia)); [| constructor| | reflexivity| | exact TBOK].
      - apply (PMK.hpres_of L (OB ++ LBX) S 0 _ M M1).
        + rewrite app_nil_r. exact (EKw (OB ++ LBX) S 0).
        + intros i Hi. lia.
        + apply PMK.dk_grows. exact MG.
      - unfold PM.src_fields_at. unfold PM.CHUNK in *.
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F1]|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F2]|].
        split; [apply (L5.defined_grows M M1 _ _ MG); exact F3|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F4]|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F5]|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F6]|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact F7]|].
        split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
        split; [apply (L5.defined_grows M M1 _ _ MG); exact DC|]. split; exact I.
      - apply (PNSVG.v8_at_agree M M1 ov x (fun a => os + 256 <= a < os + 256 + 8) VS MG ltac:(lia) ltac:(lia) FRZ). intros a Ha. lia. }
    split.
    { apply (PMF.iss_at_agree RSEGS AD M M1 ois str sm); [lia|lia| apply AG; lia| |exact IA].
      intros c n p E. apply AGH. unfold LBc. apply PNSSV1.in4. apply INCS. rewrite E. left. reflexivity. }
    split; [exact (base_keep M M1 (EKw _ _ _) STK BASE)|].
    split; [exact TBOK|]. split; [exact HH1|]. split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_after_fill mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w n c : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 ov ->
  getr R (reg 10) = Z_to_bv 64 c -> getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 16384 ->
  getr R (reg 22) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 w -> kept7 R ->
  0 <= c <= 16384 -> 16384 <= w <= len ->
  state_ok M model src x g sm cr -> PGV8.v8_size x = n + 16384 -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w + c ->
  PMSP.src_step src0 src sm0 sm -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39654 M model) K.
Proof using All.
  intros A2 A8 A9 A10 A18 A19 A22 A21 KP Hc Hw SO SZ VR En CONS STEP MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  assert (Hn : 0 <= n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct (tsrc M src x g PA) as ((_ & _ & D256 & _) & _ & _ & VS & _).
  assert (CAP : n + 16384 <= PGV8.v8_cap x) by (destruct x as [|b' n' c']; cbn in SZ |- *; [lia| destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _); lia]).
  assert (W256 : L5.writable RSEGS M (os + 256) 8) by (apply (L5C.writable_of_defined RSEGS M _ 8 D256); destruct STOP; lia).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64). bvr.
  LeanFeed.pfeed PP (PNSSVP.tvD3_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
     | 43%nat => n | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
     | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
     | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 53%nat => c | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
  set (P := fun a => os + 256 <= a < os + 256 + 8).
  assert (SPC : forall pc1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x39654) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
            (state_ok M1 model src x g sm cr -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39654 M model) K).
  { intros pc1 MS NEXT. unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) cr M model fx fx1 R 0x39654 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
    - intros a Ha N. apply FRZ; [exact Ha| exact N].
    - intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) M S 22528 a STK). lia.
    - intros a. unfold P. apply PMK.rng_dec.
    - intros HH1. apply NEXT. apply (pos_upd M M1 model src x g sm cr SO MG); [|exact HH1]. intros i Hi N. apply FRZ; [exact Hi| exact N]. }
  destruct EX as [(MS & KS & E1 & E10 & E11 & E20 & C0) | [(MS & KS & E20 & E21 & C0 & C1) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & C0 & C1)]];
    apply (SPC _ MS); intros SO1.
  - (* [comment removed for export] *)
    assert (DK' : c < 16384).
    { destruct (Z.eq_dec c 16384) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    pose proof (unread_nn M1 model src x g sm cr SO1) as (UN1 & _).
    apply (call_resize fx1 R1 M1 model src x g sm cr (n + c) 0x39674 w); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + lia.
    + left. lia.
    + right. unfold PM.CHUNK. lia.
    + lia.
    + unfold PMSP.consumed in CONS. lia.
    + lia.
    + intros fx2 R2 M2 model2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 w c); try assumption.
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
      * unfold PNSSV1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR2|]. right. unfold PM.CHUNK. lia.
  - (* [comment removed for export] *)
    assert (DK' : c = 16384) by (apply (PNSSV2.mod_lt1 (c - 16384)) in C1; lia). subst c.
    rewrite PNSSV2.subw in C0 by lia.
    apply (IH fx1 R1 M1 model src x g sm cr (w - 16384) MU).
    split; [|split; [exact SO1| split; [|lia]]].
    + unfold PNSSV1.lregs.
      split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
      split; [exact E21|].
      kept_tac KS KP.
    + unfold PNSSV1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. unfold PM.CHUNK. lia.
  - (* [comment removed for export] *)
    assert (DK' : c = 16384) by (apply (PNSSV2.mod_lt1 (c - 16384)) in C1; lia). subst c.
    rewrite PNSSV2.subw in C0 by lia.
    apply (finish fx1 R1 M1 model src x g sm cr 0); try assumption.
    + kept_tac KS KP.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PNSSV1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. unfold PM.CHUNK. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_after_resize mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w n : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 64) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 ov ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 16384 ->
  getr R (reg 22) = Z_to_bv 64 n -> getr R (reg 21) = Z_to_bv 64 w -> kept7 R ->
  16384 <= w <= len ->
  state_ok M model src x g sm cr -> PGV8.v8_size x = n + 16384 -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm -> PM.sm_st sm = 0 -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39634 M model) K.
Proof using All.
  intros A2 A8 A9 A18 A19 A22 A21 KP Hw SO SZ VR En CONS STEP ST0 MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  assert (Hn : 0 <= n < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct x as [|b1 n1 c1]; cbn [PGV8.v8_size] in SZ; [lia|]. subst n1.
  destruct VS as (VD & _ & U0 & U8 & U16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
  assert (IN : In (b1, c1) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b1 (n + 16384) c1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
  destruct (BR b1 c1 IN) as (Q0 & _ & Q4).
  LeanFeed.pfeed PP (PNSSVP.tvD2_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
      | 39%nat => b1 | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39634 R1 0x382d4 M K Mh Ml MS).
  apply (call_fillv fx1 R1 M model src (PGV8.V8Blk b1 (n + 16384) c1) g sm cr (b1 + n) 0x39654 b1 (n + 16384) c1); try assumption; try reflexivity.
  + split; [lia| reflexivity].
  + rewrite (KS 2%nat) by PMK.inl. exact A2.
  + kept_tac KS KP.
  + lia.
  + unfold PM.CHUNK. lia.
  + intros fx2 R2 M2 sm2 c RP2 Y10 Hcc G2 STF STEP2 SO2.
    destruct (STF ST0) as (Ec & ST2).
    pose proof (unread_nn M2 model src (PGV8.V8Blk b1 (n + 16384) c1) g sm2 cr SO2) as (UN2 & ST2' & RM2 & GE2).
    assert (CONS2 : PMSP.consumed src src sm sm2 = c).
    { unfold PMSP.consumed, PM.unread. destruct STEP2 as (_ & E2 & _). lia. }
    apply (d_after_fill mu0 IH fx2 R2 M2 model src (PGV8.V8Blk b1 (n + 16384) c1) g sm2 cr w n c); try assumption.
    * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
    * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
    * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
    * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
    * rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
    * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
    * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
    * intros y Hy. rewrite (PMK.cs_of_preserved R1 R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
      rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
    * reflexivity.
    * unfold PMSP.consumed in *. lia.
    * exact (PNSSV3.src_step_trans _ _ _ _ _ _ STEP STEP2).
    * enough (PM.mu_src src sm2 < PM.mu_src src sm) by lia.
      apply (PNSSV3.mu_dec _ _ _ _ STEP2 ST ST2').
      destruct (Z.ltb_spec c PM.CHUNK) as [LT|GE']; [right; split; [exact ST0| exact ST2]| left].
      unfold PMSP.consumed in CONS2. unfold PM.CHUNK in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dpath mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w : Z) :
  lregs R w -> getr R (reg 19) = Z_to_bv 64 16384 -> 16384 <= w <= len ->
  state_ok M model src x g sm cr -> acct src x sm w -> PM.sm_st sm = 0 -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3961c M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A21 & KP) A19 Hw SO AC ST0 MU. pose proof AC as (CONS & SZ & STEP & VR & MIN).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof lay as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12 & _).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src x g sm cr SO) as (UN & ST & RM & GE).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  assert (Hn : 0 <= len - w < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
  assert (BR : PMFR.brange L (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (HDR : exists b, L5.u64_at RSEGS M ov b /\ L5.u64_at RSEGS M (ov + 8) (b + (len - w)) /\ 0 <= b <= 2 ^ 47).
  { destruct x as [|b1 n1 c1]; cbn [PGV8.v8_size] in SZ.
    - destruct VS as (_ & _ & U0 & U8 & _). exists 0. rewrite <- SZ, Z.add_0_l. split; [exact U0|]. split; [exact U8| lia].
    - destruct VS as (_ & _ & U0 & U8 & U16 & Hnc & Hc & Hb0 & _). subst n1. exists b1. split; [exact U0|]. split; [exact U8|].
      assert (IN : In (b1, c1) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b1 (len - w) c1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (BR b1 c1 IN) as (Q0 & _ & Q4). lia. }
  destruct HDR as (b & U0 & U8 & Hb).
  LeanFeed.pfeed PP (PNSSVP.tvD_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => ov | 35%nat => len | 36%nat => w
      | 39%nat => b | 40%nat => len - w | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E22).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x3961c R1 0x396ac M K Mh Ml MS).
  apply (call_resize fx1 R1 M model src x g sm cr ((len - w) + 16384) 0x39634 w); try assumption.
  + split; [lia| reflexivity].
  + rewrite (KS 2%nat) by PMK.inl. exact A2.
  + kept_tac KS KP.
  + lia.
  + right. unfold PM.CHUNK. lia.
  + lia.
  + unfold PMSP.consumed in CONS. lia.
  + lia.
  + intros fx2 R2 M2 model2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 SO2.
    apply (d_after_resize mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 w (len - w)); try assumption; try lia.
    * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
    * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
    * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
    * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
    * rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
    * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. exact E22.
    * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
    * intros y Hy. rewrite (PMK.cs_of_preserved R1 R2 y RP2) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity).
      rewrite (KS y) by (revert y Hy; apply PNSSV1.sub_in; vm_compute; reflexivity). apply KP. exact Hy.
Qed.

End Call.
End WithHeap.
End PNSSV4.
