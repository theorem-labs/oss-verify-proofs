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
     PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTxtKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSSrdP_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgSrcKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PgSrd1_u Bs0PgSrd2_u Bs0PgSrd3_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSR4.
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
#[local] Abbreviation after_shrink := (PGSSR2.after_shrink L HI LY HIok R0 M0 model0 K LBX cr0 S r len T OB src0 tb0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 SPLO Hlen INCS UNS0 RSZ SRD FBT KONT).
Ltac kept_tac KS KP := intros x Hx; rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hx.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_upd M M1 model src tb tg sm cr : state_ok M model src tb tg sm cr -> mem_grows M M1 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 256 + 8) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  hi_heap HI (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M1 (m_vmmaps model) -> state_ok M1 model src tb tg sm cr.
Proof using All.
  intros SO MG FRZ HH1.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & MB & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof lay as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DJ1 & DJ2 & DJ3).
  set (LBc := PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) in HH.
  assert (BR : PMFR.brange L LBc) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  assert (AG : forall a m, 0 <= a -> a + m <= 2 ^ 64 -> (a + m <= os + 256 \/ os + 264 <= a) -> L5C.agree_on M M1 a m).
  { intros a m Ha Hm X i Hi. apply FRZ; lia. }
  assert (AGH : forall B m, In (B, m) LBc -> L5C.agree_on M M1 B m).
  { intros B m Hin. destruct (BR B m Hin) as (Q0 & _ & Q4). unfold hl_ceil in Q4. apply AG; lia. }
  assert (EKw : forall LB sp scr, PMK.ek L LB sp scr W0 M M1).
  { intros LB sp scr. apply (PMK.ek_piece L LB sp scr W0 M M1 (fun a => os + 256 <= a < os + 256 + 8)); [intros a Ha N; apply FRZ; [exact Ha| exact N]|].
    intros a Ha CA NE OW Pa. apply (OW (os + 256, 40)); [unfold W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng; cbn [fst snd]. lia. }
  split; [split; [|split]|].
  - exact (PMK.ek_trans L (OB ++ LBX) S 22528 W0 M0 M M1 EK (EKw _ _ _)).
  - apply (PMK.dk_trans L (OB ++ LBX) S 22528 M0 M M1 DK). apply PMK.dk_grows. exact MG.
  - exact (PMK.stk_grows L M M1 S 22528 MG STK).
  - split.
    { destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
      unfold saves9, PGSSR1.saves9. repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| eassumption]). }
    split.
    { destruct (tsrc M src tb tg PA) as ((F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _) & _ & _ & VS & _).
      assert (INQ : In (PM.sr_qc src, PM.CHUNK) LBc) by (unfold LBc, PM.src_own; left; reflexivity).
      destruct (BR _ _ INQ) as (C0 & _ & C4). unfold hl_ceil in C4.
      apply (tw_xfer M M1 src src tb tb tg tg cr (m_vmmaps model) 22528 S 0 [] PA HH STK ltac:(lia) ltac:(lia) ltac:(lia)); [| constructor| | reflexivity| | exact TBOK].
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
      - apply (PMF.vstr_at_agree RSEGS M M1 otb tb); [lia|lia| apply AG; lia| |exact VS].
        intros c n p E. apply AGH. unfold LBc. rewrite E. apply in_or_app. right. left. reflexivity. }
    split.
    { apply (PMF.iss_at_agree RSEGS AD M M1 ois str sm); [lia|lia| apply AG; lia| |exact IA].
      intros c n p E. apply AGH. unfold LBc. apply PGSSR1.in4. apply INCS. rewrite E. left. reflexivity. }
    split; [exact (base_keep M M1 (EKw _ _ _) STK BASE)|].
    split; [exact TBOK|]. split; [exact HH1|]. split; [exact MOK|]. split; [exact MB|]. split; [exact CRL| exact CRK].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_after_fill mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w n c : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 otb ->
  getr R (reg 10) = Z_to_bv 64 c -> getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 16384 ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 (otb + 1) -> getr R (reg 23) = Z_to_bv 64 n -> kept6 R ->
  0 <= c <= 16384 -> 16384 <= w <= len ->
  state_ok M model src tb tg sm cr -> PM.vs_size tb = n + 16384 -> 0 <= n -> n = PM.vs_size tb0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w + c ->
  PMSP.src_step src0 src sm0 sm -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x394c8 M model) K.
Proof using All.
  intros A2 A8 A9 A10 A18 A19 A21 A22 A23 KP Hc Hw SO SZ Hn0 En CONS STEP MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  assert (Hn : n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  destruct (tsrc M src tb tg PA) as ((_ & _ & D256 & _) & _).
  assert (W256 : L5.writable RSEGS M (os + 256) 8) by (apply (L5C.writable_of_defined RSEGS M _ 8 D256); destruct STOP; lia).
  pose proof SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72). bvr.
  LeanFeed.pfeed PP (PMSSRP.tsD3_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
     | 43%nat => n | 44%nat => bv_unsigned (getr R0 (reg 1)) | 45%nat => bv_unsigned (getr R0 (reg 8)) | 46%nat => bv_unsigned (getr R0 (reg 9))
     | 47%nat => bv_unsigned (getr R0 (reg 18)) | 48%nat => bv_unsigned (getr R0 (reg 19)) | 49%nat => bv_unsigned (getr R0 (reg 20))
     | 50%nat => bv_unsigned (getr R0 (reg 21)) | 51%nat => bv_unsigned (getr R0 (reg 22)) | 53%nat => c | 54%nat => bv_unsigned (getr R0 (reg 23)) | _ => 0 end)) ltac:(first [PMK.sc]).
  destruct PP as (fx1 & R1 & M1 & MG & _ & FRZ & EX).
  set (P := fun a => os + 256 <= a < os + 256 + 8).
  assert (SPC : forall pc1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x394c8) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) ->
            (state_ok M1 model src tb tg sm cr -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x394c8 M model) K).
  { intros pc1 MS NEXT. unfold PMSP.cfg.
    apply (PMK.spiece RSEGS L HI KL HIok (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) cr M model fx fx1 R 0x394c8 R1 pc1 M1 P K HH Mh Ml ltac:(destruct STOP; lia) MS MG).
    - intros a Ha N. apply FRZ; [exact Ha| exact N].
    - intros a Pa. unfold P in Pa. apply (PMK.cwr_stack L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX) M S 22528 a STK). lia.
    - intros a. unfold P. apply PMK.rng_dec.
    - intros HH1. apply NEXT. apply (pos_upd M M1 model src tb tg sm cr SO MG); [|exact HH1]. intros i Hi N. apply FRZ; [exact Hi| exact N]. }
  destruct EX as [(MS & KS & E1 & E10 & E11 & E12 & E20 & C0) | [(MS & KS & E20 & E21 & C0 & C1) | (MS & KS & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & C0 & C1)]];
    apply (SPC _ MS); intros SO1.
  - (* [comment removed for export] *)
    assert (DK' : c < 16384).
    { destruct (Z.eq_dec c 16384) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M1 model src tb tg sm cr (n + c) 234732); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + unfold PM.CHUNK. lia.
    + unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 w c); try assumption.
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
    assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
    rewrite subw in C0 by lia.
    apply (IH fx1 R1 M1 model src tb tg sm cr (w - 16384) MU).
    split; [|split; [exact SO1| split; [|lia]]].
    + unfold PGSSR1.lregs.
      split; [rewrite (KS 2%nat) by PMK.inl; exact A2|]. split; [rewrite (KS 8%nat) by PMK.inl; exact A8|].
      split; [rewrite (KS 9%nat) by PMK.inl; exact A9|]. split; [rewrite (KS 18%nat) by PMK.inl; exact A18|].
      split; [exact E21|]. split; [rewrite (KS 22%nat) by PMK.inl; exact A22|].
      kept_tac KS KP.
    + unfold PGSSR1.acct. split; [lia|]. split; [lia|]. exact STEP.
  - (* [comment removed for export] *)
    assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
    rewrite subw in C0 by lia.
    apply (finish fx1 R1 M1 model src tb tg sm cr 0); try assumption.
    + kept_tac KS KP.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PGSSR1.acct. split; [lia|]. split; [lia|]. exact STEP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_after_resize mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w n : Z) :
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 otb ->
  getr R (reg 18) = Z_to_bv 64 os -> getr R (reg 19) = Z_to_bv 64 16384 ->
  getr R (reg 21) = Z_to_bv 64 w -> getr R (reg 22) = Z_to_bv 64 (otb + 1) -> getr R (reg 23) = Z_to_bv 64 n -> kept6 R ->
  16384 <= w <= len ->
  state_ok M model src tb tg sm cr -> PM.vs_size tb = n + 16384 -> 0 <= n -> n = PM.vs_size tb0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm -> PM.sm_st sm = 0 -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39498 M model) K.
Proof using All.
  intros A2 A8 A9 A18 A19 A21 A22 A23 KP Hw SO SZ Hn0 En CONS STEP ST0 MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  assert (Hn : n < 2 ^ 26) by (unfold PMSP.consumed in CONS; lia).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src tb tg PA) as (_ & _ & _ & VS & _).
  assert (BR : PMFR.brange L (PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct VS as (VD & _ & VS). destruct tb as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ.
  - (* [comment removed for export] *)
    exfalso. destruct VS as (Hn1 & _). lia.
  - destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & _).
    pose proof (PMF.u8_of_u64 RSEGS M otb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (IN : In (q1, c1) (PM.src_own src ++ PM.vs_own (PM.VLong c1 n1 q1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    destruct (BR q1 c1 IN) as (Q0 & _ & Q4).
    LeanFeed.pfeed PP (PMSSRP.tsD2_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => (c1 + 1) mod 256 | 41%nat => q1 | 43%nat => n | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39498 R1 0x382d4 M K Mh Ml MS).
    apply (call_filltb fx1 R1 M model src (PM.VLong c1 n1 q1) tg sm cr (q1 + n) 234696 c1 n1 q1); try assumption; try reflexivity.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 sm2 c RP2 Y10 Hc G2 STF STEP2 SO2.
      destruct (STF ST0) as (Ec & ST2).
      pose proof (unread_nn M2 model src (PM.VLong c1 n1 q1) tg sm2 cr SO2) as (UN2 & ST2' & RM2 & GE2).
      assert (CONS2 : PMSP.consumed src src sm sm2 = c).
      { unfold PMSP.consumed, PM.unread. destruct STEP2 as (_ & E2 & _). lia. }
      apply (d_after_fill mu0 IH fx2 R2 M2 model src (PM.VLong c1 n1 q1) tg sm2 cr w n c); try assumption.
      * rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl. rewrite (KS 2%nat) by PMK.inl. exact A2.
      * rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl. rewrite (KS 8%nat) by PMK.inl. exact A8.
      * rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl. rewrite (KS 9%nat) by PMK.inl. exact A9.
      * rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl. rewrite (KS 18%nat) by PMK.inl. exact A18.
      * rewrite (PMK.cs_of_preserved R1 R2 19%nat RP2) by PMK.inl. rewrite (KS 19%nat) by PMK.inl. exact A19.
      * rewrite (PMK.cs_of_preserved R1 R2 21%nat RP2) by PMK.inl. rewrite (KS 21%nat) by PMK.inl. exact A21.
      * rewrite (PMK.cs_of_preserved R1 R2 22%nat RP2) by PMK.inl. rewrite (KS 22%nat) by PMK.inl. exact A22.
      * rewrite (PMK.cs_of_preserved R1 R2 23%nat RP2) by PMK.inl. rewrite (KS 23%nat) by PMK.inl. exact A23.
      * intros x Hx. rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity).
        rewrite (KS x) by (revert x Hx; apply PGSSR1.sub_in; vm_compute; reflexivity). apply KP. exact Hx.
      * unfold PMSP.consumed in *. lia.
      * exact (PGSSR3.src_step_trans _ _ _ _ _ _ STEP STEP2).
      * enough (PM.mu_src src sm2 < PM.mu_src src sm) by lia.
        apply (PGSSR3.mu_dec _ _ _ _ STEP2 ST ST2').
        destruct (Z.ltb_spec c PM.CHUNK) as [LT|GE']; [right; split; [exact ST0| exact ST2]| left].
        unfold PMSP.consumed in CONS2. unfold PM.CHUNK in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dpath mu0 (IH : IHt mu0) (fx : FPState) R M model src tb tg sm cr (w : Z) :
  lregs R w -> getr R (reg 19) = Z_to_bv 64 16384 -> 16384 <= w <= len ->
  state_ok M model src tb tg sm cr -> acct src tb sm w -> PM.sm_st sm = 0 -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39470 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A21 & A22 & KP) A19 Hw SO (CONS & SZ & STEP) ST0 MU.
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & MOK & _). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof lay0 as (LY1 & LY2 & LY3 & LY4 & LY5 & LY6 & LY7 & LY8 & LY9 & LY10 & LY11 & LY12).
  pose proof MOK as (Mh & Ml & Mm).
  pose proof (unread_nn M model src tb tg sm cr SO) as (UN & ST & RM & GE).
  pose proof (L5C.stk_writable RSEGS _ M S 22528 STK) as WR.
  pose proof (tsrc M src tb tg PA) as (_ & _ & _ & VS & _).
  destruct VS as (VD & _ & VS). destruct tb as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & B0).
    pose proof (PMF.even_byte n1) as EV.
    LeanFeed.pfeed PP (PMSSRP.tsDS_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => 2 * n1 | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E23).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39470 R1 0x59000 M K Mh Ml MS).
    assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + 16384)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    assert (E23' : getr R1 (reg 23) = Z_to_bv 64 n1) by (rewrite E23; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    apply (call_resize fx1 R1 M model src (PM.VShort n1) tg sm cr (n1 + 16384) 234648); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (d_after_resize mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 w n1); try assumption; try lia.
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
    LeanFeed.pfeed PP (PMSSRP.tsDL_conc fx R M (fun j => match j with 2%nat => S | 33%nat => os | 34%nat => otb | 35%nat => len | 36%nat => w
        | 39%nat => (c1 + 1) mod 256 | 40%nat => n1 | _ => 0 end)) ltac:(first [PMK.sc]).
    destruct PP as (fx1 & R1 & M1 & MG & FRw & _ & MS & KS & E1 & E10 & E11 & E12 & E23).
    assert (EM : M1 = M) by (apply functional_extensionality; exact FRw). subst M1.
    unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39470 R1 0x59000 M K Mh Ml MS).
    apply (call_resize fx1 R1 M model src (PM.VLong c1 n1 q1) tg sm cr (n1 + 16384) 234648); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS 2%nat) by PMK.inl. exact A2.
    + kept_tac KS KP.
    + cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PMSP.consumed in CONS. unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      apply (d_after_resize mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 w n1); try assumption; try lia.
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
End PGSSR4.
