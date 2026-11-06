(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParSpecs PmParKit PgSrc PgV8
     PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnBrObj PnBrKit.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBK3.

Lemma in_blk_incl l l' p k : incl l l' -> PGS.in_blk l p k -> PGS.in_blk l' p k.
Proof. intros I (B & m & Hin & H1 & H2). exists B, m. split; [apply I; exact Hin|]. split; [exact H1| exact H2]. Qed.

Lemma perm_tw {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (a ++ t ++ (b ++ c ++ n) ++ x).
Proof.
  rewrite <- !app_assoc. apply Permutation_app_head.
  rewrite !app_assoc. apply Permutation_app_tail. rewrite <- !app_assoc.
  change (b ++ c ++ n ++ t) with ((fun l => l) (b ++ c ++ n ++ t)). cbn beta.
  replace (b ++ c ++ n ++ t) with ((b ++ c ++ n) ++ t) by (rewrite <- !app_assoc; reflexivity).
  apply Permutation_app_comm.
Qed.
Lemma perm_vw {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (a ++ c ++ (b ++ n ++ t) ++ x).
Proof.
  rewrite <- !app_assoc. apply Permutation_app_head. rewrite !app_assoc. do 3 apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Abbreviation mem := (word -> option byte).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation scr := PMSP.pm_scr.
Abbreviation brel := (PNBK.brel segs A AN L HI).
Abbreviation BENT := PNBK.BENT.
Hypothesis KH : PNBK.khyps segs A AN L HI.
(* [comment removed for export] *)
Definition twok : Prop := forall fb s, hl_ceil L <= fb -> fb + 784 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> fb mod 16 = 0 ->
    PGS.towner_ok segs A L HI (PNM.txt_owner segs A T3 T4 (pa_vp_parser A) (fb + 40) (fb + 472) fb (fb + 784) s).
Definition vwok : Prop := forall fb s, hl_ceil L <= fb -> fb + 784 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> fb mod 16 = 0 ->
    PGV8.vowner_ok segs A L HI (PNM.vec_owner segs A T3 T4 (pa_vp_parser A) (fb + 40) (fb + 472) fb (fb + 784) s).
Let KL := PNBK.kh_KL _ _ _ _ _ KH.
Let HIok := PNBK.kh_HIok _ _ _ _ _ KH.
Let HFR := PNBK.kh_HFR _ _ _ _ _ KH.
Let HOP := PNBK.kh_HOP _ _ _ _ _ KH.
Let HOV := PNBK.kh_HOV _ _ _ _ _ KH.
Let HOIS := PNBK.kh_HOIS _ _ _ _ _ KH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_read_span h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' len : Z) K :
  twok -> PGS.read_span_specG segs A L HI (pa_read_span A) ->
  0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (PNBK.be_s E0)) (PNBK.be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 56) -> getr R1 (PMK.reg 11) = Z_to_bv 64 len -> getr R1 (PMK.reg 12) = Z_to_bv 64 (fb + 40 + 368) ->
  0 <= len < 2 ^ 64 ->
  sp' <= sp -> sp - scr h <= sp' - scr 6 -> sp' mod 16 = 0 ->
  PM.unread (PNM.b_src s1) sm1 < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 src2 tb2 tg2 sm2 cr2 ptr n,
      regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 ptr -> getr R2 (PMK.reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
      ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own (PNM.with_src_tb s1 src2 tb2 tg2)) ptr n \/ (fb + 40 + 368 + 1 <= ptr /\ ptr + n <= fb + 40 + 368 + 24)) ->
      L5.defined M2 ptr n ->
      PM.unread src2 sm2 <= PM.unread (PNM.b_src s1) sm1 ->
      brel h LBX sp fb str E0 (BENT M2 model2 cr2 (PNM.with_src_tb s1 src2 tb2 tg2) sm2 ax1) ->
      (forall a m, sp' <= a -> a + m <= fb + 48 -> L5C.agree_on M1 M2 a m) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (pa_read_span A) M1 model1) K.
Proof.
  intros TWOK RSP Hh K0 BR FOK INCS CRED0 X1 RA1 X2 X3 X4 X10 X11 X12 Hlen S1 S2 S3 UNR KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (PNBK.scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC6 : scr 6 = 24576) by reflexivity. rewrite SC6 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  destruct s1 as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  set (s1 := PNM.BPST mo dn src bb nb tb ng tg bg sb sk stk) in *.
  set (T := PNM.txt_owner segs A T3 T4 (pa_vp_parser A) (fb + 40) (fb + 472) fb (fb + 784) s1).
  assert (OK : PGS.towner_ok segs A L HI T) by (apply TWOK; [unfold hl_ceil in *; lia| lia| exact STOP| exact F3]).
  set (OB := PNM.txt_rest_own s1).
  set (LB1 := PM.src_own src ++ PM.vs_own tb ++ OB ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) LB1).
  { unfold LB1, OB, s1, PNM.bparser_own, PNM.brest_own, PNM.txt_rest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply perm_tw. }
  assert (HHp : hi_heap HI LB1 cr1 M1 (m_vmmaps model1)) by (apply (PNBK.hi_heap_perm _ _ _ _ _ KH _ _ _ _ _ HH PERM1)).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 24576) by (apply (PMK.stk_call L M1 sp sc sp' 24576 STK); [exact S1| exact S2| lia| exact S3]).
  destruct GR1 as (GNB & GTB & GBB). cbn [s1 PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in GNB, GTB, GBB.
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _).
  cbn [s1 PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in BB1, NB1, TB1, SV1.
  assert (CRL1 : PMSP.credit_le (pot s1) cr1) by (apply (PMPK.credit_le_keep _ _ _ _ CRED0 CK)).
  assert (CRX : PMSP.credit_le (PM.pot_text L tb tg) cr1).
  { pose proof (PNBK.pot_bstack_nonneg _ _ _ L _ KH sk ltac:(destruct SV1 as (_ & _ & _ & Hk & _); exact Hk)) as (Q1 & Q2).
    pose proof (PNBK.pot_text_nonneg segs A AN L HI KH _ _ _ _ NB1 GNB) as (Q3 & Q4). pose proof (PNBK.pot_v8_nonneg segs A AN L HI KH _ _ _ _ BB1 GBB) as (Q5 & Q6).
    pose proof (PNBK.pot_text_nonneg segs A AN L HI KH _ _ _ _ TB1 GTB) as (Q7 & Q8).
    revert CRL1. unfold PMSP.credit_le, PNR.pot_bparser, PM.credit_add, s1. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear - Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8. lia. }
  unfold PGS.read_span_specG in RSP.
  apply (RSP T OK fx1 R1 M1 model1 K OB LBX cr1 sp' r' len src tb tg str sm1 HHp MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { cbn [T PNM.txt_owner PGS.tw_lo]. lia. }
  { rewrite L5K.rl10. cbn [T PNM.txt_owner PGS.tw_os]. unfold PNM.OFF_SRC. replace (fb + 40 + 16) with (fb + 56) by lia. exact X10. }
  { rewrite L5K.rl11. exact X11. }
  { rewrite L5K.rl12. cbn [T PNM.txt_owner PGS.tw_otb]. unfold PNM.OFF_TB. exact X12. }
  { exact Hlen. }
  { cbn [T PNM.txt_owner PGS.tw_at]. split; [| split; [exact GTB| reflexivity]]. unfold s1. cbn [PNM.with_src_tb]. exact PA1. }
  { cbn [T PNM.txt_owner PGS.tw_ois]. exact IA1. }
  { exact BASE1. } { exact INCS. } { exact UNR. } { exact CRX. }
  intros fx2 R2 M2 model2 src2 tb2 tg2 sm2 cr2 ptr n RP2 Y10 Y11 Hn1 Hn2 WHERE DEF2 TW2 IA2 STEP2 HP2 CK2 MB2 HH2.
  cbn [T PNM.txt_owner PGS.tw_at PGS.tw_ois PGS.tw_os PGS.tw_otb] in TW2, IA2, HP2, WHERE. destruct TW2 as (PA2 & GTB2 & _).
  unfold PNM.OFF_SRC, PNM.OFF_TB in HP2, WHERE.
  assert (QC2 : PM.sr_qc src2 = PM.sr_qc src) by (destruct STEP2 as (E & _); exact E).
  set (s2 := PNM.with_src_tb s1 src2 tb2 tg2).
  set (LB2 := PM.src_own src2 ++ PM.vs_own tb2 ++ OB ++ LBX) in HH2.
  assert (PERM2 : Permutation LB2 (PNM.bparser_own s2 ++ LBX)).
  { unfold LB2, OB, s2, s1, PNM.bparser_own, PNM.brest_own, PNM.txt_rest_own. cbn [PNM.with_src_tb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
    apply Permutation_sym. apply perm_tw. }
  assert (HH2' : hi_heap HI (PNM.bparser_own s2 ++ LBX) cr2 M2 (m_vmmaps model2)) by (apply (PNBK.hi_heap_perm _ _ _ _ _ KH _ _ _ _ _ HH2 PERM2)).
  pose proof (PMFR.model_ok_but_vm model1 model2 MOK MB2) as MOK2.
  set (WE := PGS.W_srcfG (fb + 40 + 16) (fb + 472) ++ [(fb + 40 + 368, 24)]) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> (fb + 312 <= a < fb + 352) \/ (fb + 512 <= a < fb + 520) \/ (fb + 624 <= a < fb + 628) \/ (fb + 408 <= a < fb + 432)).
  { intros a (r0 & Hin & Hr). unfold WE, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
  assert (EKc : PMK.ek L LBX sp' 24576 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (AGH : forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ PMK.inW WE i) -> L5C.agree_on M1 M2 a m).
  { intros a m H1 H2 N. apply (PMPK.ag_hi segs L KL LBX sp' 24576 WE M1 M2 EKc STKc ltac:(lia) a m H1 H2 N). }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LBX M1 M2 sp sc sp' 24576 WE STK HP2); lia).
  destruct (PNBK.statics_keep segs A AN L HI KH LBX sp' 24576 WE M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCE in I. unfold hl_ceil in *. lia. }
  assert (OWN0 : PNBK.own_ok L [] LBX) by (intros B m Hin; destruct Hin).
  apply (KONT fx2 R2 M2 model2 src2 tb2 tg2 sm2 cr2 ptr n RP2 Y10 Y11 Hn1 Hn2).
  - destruct WHERE as [W0|[W1|W2]]; [left; exact W0| right; left| right; right; exact W2].
    revert W1. apply in_blk_incl.
    unfold OB, s2, s1, PNM.bparser_own, PNM.brest_own, PNM.txt_rest_own. cbn [PNM.with_src_tb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
    intros x Hx. rewrite !in_app_iff in Hx |- *. tauto.
  - exact DEF2.
  - destruct STEP2 as (_ & _ & _ & _ & LE). exact LE.
  - unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax]. fold s2.
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; [lia|lia| intros i Hi I; apply WCE in I; lia]|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; [lia|lia| intros i Hi I; apply WCE in I; lia]|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|].
      unfold PNM.bgrow_ok. cbn [s2 s1 PNM.with_src_tb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg]. split; [exact GNB|]. split; [exact GTB2| exact GBB]. }
    split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP); exact STEP2|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PNBK.ek_lbx_callee segs A AN L HI KH [] LBX sp sc sp' 24576 _ WE M1 M1 M2 HP2 S2 S1 OWN0); [|exact STK|].
        + apply (PNBK.brange_hi_x segs A AN L HI KH (PNM.bparser_own s1) LBX cr1 M1 (m_vmmaps model1)). exact HH.
        + intros a I. apply WCE in I. right. left. apply (PNBK.wrun_of_range segs A AN L HI KH). lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LBX sp sc sp' 24576 WE M1 M2 HP2); [apply incl_refl| exact S2| exact S1]. }
    split.
    { revert CK CK2. unfold PMSP.credit_keep, PNR.pot_bparser, PM.credit_add, s2, s1.
      cbn [PNM.with_src_tb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear. lia. }
    split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2'|]. split; [exact STK2| exact MOK2].
  - intros a m H1 H2. apply AGH; [exact H1| lia|]. intros i Hi I. apply WCE in I. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_read_span_v h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' len : Z) K :
  vwok -> PGV8.read_span_v_specG segs A L HI (PNL.pn_read_span_v AN) ->
  0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (PNBK.be_s E0)) (PNBK.be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 56) -> getr R1 (PMK.reg 11) = Z_to_bv 64 len -> getr R1 (PMK.reg 12) = Z_to_bv 64 (fb + 40 + 320) ->
  0 <= len < 2 ^ 64 ->
  sp' <= sp -> sp - scr h <= sp' - scr 6 -> sp' mod 16 = 0 ->
  PM.unread (PNM.b_src s1) sm1 < 2 ^ 26 -> PNR.bb_room s1 sm1 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 src2 x2 g2 sm2 cr2 ptr n,
      regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 ptr -> getr R2 (PMK.reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
      PM.unread src2 sm2 = PM.unread (PNM.b_src s1) sm1 - n ->
      ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own (PNM.with_src_bb s1 src2 x2 g2)) ptr n) ->
      L5.defined M2 ptr n ->
      (n = len -> PNR.bb_room (PNM.with_src_bb s1 src2 x2 g2) sm2) ->
      brel h LBX sp fb str E0 (BENT M2 model2 cr2 (PNM.with_src_bb s1 src2 x2 g2) sm2 ax1) ->
      (forall a m, sp' <= a -> a + m <= fb + 48 -> L5C.agree_on M1 M2 a m) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (PNL.pn_read_span_v AN) M1 model1) K.
Proof.
  intros VWOK RSP Hh K0 BR FOK INCS CRED0 X1 RA1 X2 X3 X4 X10 X11 X12 Hlen S1 S2 S3 UNR ROOM KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (PNBK.scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC6 : scr 6 = 24576) by reflexivity. rewrite SC6 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  unfold PNR.bb_room in ROOM.
  destruct s1 as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  set (s1 := PNM.BPST mo dn src bb nb tb ng tg bg sb sk stk) in *.
  set (V := PNM.vec_owner segs A T3 T4 (pa_vp_parser A) (fb + 40) (fb + 472) fb (fb + 784) s1).
  assert (OK : PGV8.vowner_ok segs A L HI V) by (apply VWOK; [unfold hl_ceil in *; lia| lia| exact STOP| exact F3]).
  set (OB := PNM.vec_rest_own s1).
  set (LB1 := PM.src_own src ++ PGV8.v8_own bb ++ OB ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) LB1).
  { unfold LB1, OB, s1, PNM.bparser_own, PNM.brest_own, PNM.vec_rest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply perm_vw. }
  assert (HHp : hi_heap HI LB1 cr1 M1 (m_vmmaps model1)) by (apply (PNBK.hi_heap_perm _ _ _ _ _ KH _ _ _ _ _ HH PERM1)).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 24576) by (apply (PMK.stk_call L M1 sp sc sp' 24576 STK); [exact S1| exact S2| lia| exact S3]).
  destruct GR1 as (GNB & GTB & GBB). cbn [s1 PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in GNB, GTB, GBB.
  pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB1 & NB1 & TB1 & SV1 & _).
  cbn [s1 PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in BB1, NB1, TB1, SV1.
  assert (CRL1 : PMSP.credit_le (pot s1) cr1) by (apply (PMPK.credit_le_keep _ _ _ _ CRED0 CK)).
  assert (CRX : PMSP.credit_le (PGV8.pot_v8 L bb bg) cr1).
  { pose proof (PNBK.pot_bstack_nonneg _ _ _ L _ KH sk ltac:(destruct SV1 as (_ & _ & _ & Hk & _); exact Hk)) as (Q1 & Q2).
    pose proof (PNBK.pot_text_nonneg segs A AN L HI KH _ _ _ _ NB1 GNB) as (Q3 & Q4). pose proof (PNBK.pot_v8_nonneg segs A AN L HI KH _ _ _ _ BB1 GBB) as (Q5 & Q6).
    pose proof (PNBK.pot_text_nonneg segs A AN L HI KH _ _ _ _ TB1 GTB) as (Q7 & Q8).
    revert CRL1. unfold PMSP.credit_le, PNR.pot_bparser, PM.credit_add, s1. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear - Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8. lia. }
  unfold PGV8.read_span_v_specG in RSP.
  apply (RSP V OK fx1 R1 M1 model1 K OB LBX cr1 sp' r' len src bb bg str sm1 HHp MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { cbn [V PNM.vec_owner PGV8.vw_lo]. lia. }
  { rewrite L5K.rl10. cbn [V PNM.vec_owner PGV8.vw_os]. unfold PNM.OFF_SRC. replace (fb + 40 + 16) with (fb + 56) by lia. exact X10. }
  { rewrite L5K.rl11. exact X11. }
  { rewrite L5K.rl12. cbn [V PNM.vec_owner PGV8.vw_ov]. unfold PNM.OFF_BB. exact X12. }
  { exact Hlen. }
  { cbn [V PNM.vec_owner PGV8.vw_at]. split; [| split; [exact GBB| reflexivity]]. unfold s1. cbn [PNM.with_src_bb]. exact PA1. }
  { cbn [V PNM.vec_owner PGV8.vw_ois]. exact IA1. }
  { exact BASE1. } { exact INCS. } { exact UNR. } { exact ROOM. } { exact CRX. }
  intros fx2 R2 M2 model2 src2 x2 g2 sm2 cr2 ptr n RP2 Y10 Y11 Hn1 Hn2 CONS WHERE DEF2 ROOM2 VW2 IA2 STEP2 HP2 CK2 MB2 HH2.
  cbn [V PNM.vec_owner PGV8.vw_at PGV8.vw_ois PGV8.vw_os PGV8.vw_ov] in VW2, IA2, HP2, WHERE. destruct VW2 as (PA2 & GBB2 & _).
  unfold PNM.OFF_SRC, PNM.OFF_BB in HP2.
  assert (QC2 : PM.sr_qc src2 = PM.sr_qc src) by (destruct STEP2 as (E & _); exact E).
  set (s2 := PNM.with_src_bb s1 src2 x2 g2).
  set (LB2 := PM.src_own src2 ++ PGV8.v8_own x2 ++ OB ++ LBX) in HH2.
  assert (PERM2 : Permutation LB2 (PNM.bparser_own s2 ++ LBX)).
  { unfold LB2, OB, s2, s1, PNM.bparser_own, PNM.brest_own, PNM.vec_rest_own. cbn [PNM.with_src_bb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
    apply Permutation_sym. apply perm_vw. }
  assert (HH2' : hi_heap HI (PNM.bparser_own s2 ++ LBX) cr2 M2 (m_vmmaps model2)) by (apply (PNBK.hi_heap_perm _ _ _ _ _ KH _ _ _ _ _ HH2 PERM2)).
  pose proof (PMFR.model_ok_but_vm model1 model2 MOK MB2) as MOK2.
  set (WE := PGS.W_srcfG (fb + 40 + 16) (fb + 472) ++ [(fb + 40 + 320, 24)]) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> (fb + 312 <= a < fb + 352) \/ (fb + 512 <= a < fb + 520) \/ (fb + 624 <= a < fb + 628) \/ (fb + 360 <= a < fb + 384)).
  { intros a (r0 & Hin & Hr). unfold WE, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
  assert (EKc : PMK.ek L LBX sp' 24576 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (AGH : forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (forall i, a <= i < a + m -> ~ PMK.inW WE i) -> L5C.agree_on M1 M2 a m).
  { intros a m H1 H2 N. apply (PMPK.ag_hi segs L KL LBX sp' 24576 WE M1 M2 EKc STKc ltac:(lia) a m H1 H2 N). }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LBX M1 M2 sp sc sp' 24576 WE STK HP2); lia).
  destruct (PNBK.statics_keep segs A AN L HI KH LBX sp' 24576 WE M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCE in I. unfold hl_ceil in *. lia. }
  assert (OWN0 : PNBK.own_ok L [] LBX) by (intros B m Hin; destruct Hin).
  apply (KONT fx2 R2 M2 model2 src2 x2 g2 sm2 cr2 ptr n RP2 Y10 Y11 Hn1 Hn2).
  - revert CONS. unfold PMSP.consumed, s1. cbn [PNM.b_src]. clear. intros CONS. lia.
  - destruct WHERE as [W0|W1]; [left; exact W0| right].
    revert W1. apply in_blk_incl.
    unfold OB, s2, s1, PNM.bparser_own, PNM.brest_own, PNM.vec_rest_own. cbn [PNM.with_src_bb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk].
    intros x Hx. rewrite !in_app_iff in Hx |- *. tauto.
  - exact DEF2.
  - intros Hn. unfold PNR.bb_room, s2, s1. cbn [PNM.with_src_bb PNM.b_bb PNM.b_src]. exact (ROOM2 Hn).
  - unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax]. fold s2.
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; [lia|lia| intros i Hi I; apply WCE in I; lia]|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; [lia|lia| intros i Hi I; apply WCE in I; lia]|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|].
      unfold PNM.bgrow_ok. cbn [s2 s1 PNM.with_src_bb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg]. split; [exact GNB|]. split; [exact GTB| exact GBB2]. }
    split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP); exact STEP2|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PNBK.ek_lbx_callee segs A AN L HI KH [] LBX sp sc sp' 24576 _ WE M1 M1 M2 HP2 S2 S1 OWN0); [|exact STK|].
        + apply (PNBK.brange_hi_x segs A AN L HI KH (PNM.bparser_own s1) LBX cr1 M1 (m_vmmaps model1)). exact HH.
        + intros a I. apply WCE in I. right. left. apply (PNBK.wrun_of_range segs A AN L HI KH). lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LBX sp sc sp' 24576 WE M1 M2 HP2); [apply incl_refl| exact S2| exact S1]. }
    split.
    { revert CK CK2. unfold PMSP.credit_keep, PNR.pot_bparser, PM.credit_add, s2, s1.
      cbn [PNM.with_src_bb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear. lia. }
    split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2'|]. split; [exact STK2| exact MOK2].
  - intros a m H1 H2. apply AGH; [exact H1| lia|]. intros i Hi I. apply WCE in I. lia.
Qed.

End Kit.
End PNBK3.
