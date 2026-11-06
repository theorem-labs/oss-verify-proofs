(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
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

Module PNBK4.

(* [comment removed for export] *)
Lemma defined_of_dk L LB sp sc (M1 M2 : word -> option byte) p n :
  PMK.dk L LB sp sc M1 M2 -> 0 <= p -> p + n <= 2 ^ 64 ->
  (forall i, p <= i < p + n -> client_addr L LB sp sc i /\ ~ in_errno L i) ->
  L5.defined M1 p n -> L5.defined M2 p n.
Proof.
  intros DK Hp Hn CL D i Hi. destruct (CL (p + i) ltac:(lia)) as (C & E). apply (DK (p + i) ltac:(lia) C E). apply D. exact Hi.
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
Let KL := PNBK.kh_KL _ _ _ _ _ KH.
Let HIok := PNBK.kh_HIok _ _ _ _ _ KH.
Let HFR := PNBK.kh_HFR _ _ _ _ _ KH.
Let HOP := PNBK.kh_HOP _ _ _ _ _ KH.
Let HOV := PNBK.kh_HOV _ _ _ _ _ KH.
Let HOIS := PNBK.kh_HOIS _ _ _ _ _ KH.
Let OWOK := PNBK.kh_OWOK _ _ _ _ _ KH.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_src_read_d h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' q kk : Z) K :
  PGS.src_read_specG segs A L HI ->
  0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 56) -> getr R1 (PMK.reg 11) = Z_to_bv 64 q -> getr R1 (PMK.reg 12) = Z_to_bv 64 kk ->
  sp' <= sp -> sp - scr h <= sp' - scr 4 -> sp' mod 16 = 0 ->
  sp' <= q -> q + kk <= sp -> 1 <= kk <= 16 ->
  (forall (fx2 : FPState) R2 (M2 : mem) src2 sm2 d,
      regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 d -> 0 <= d <= kk ->
      PM.unread src2 sm2 = PM.unread (PNM.b_src s1) sm1 - d -> L5.defined M2 q d ->
      brel h LBX sp fb str E0 (BENT M2 model1 cr1 (PNM.with_srcB s1 src2) sm2 ax1) ->
      (forall a n, sp' <= a -> a + n <= fb + 48 -> (a + n <= q \/ q + kk <= a) -> L5C.agree_on M1 M2 a n) ->
      (forall p n, 0 <= p -> p + n <= 2 ^ 64 -> (PGS.in_blk (PNM.bparser_own s1) p n \/ fb <= p) -> L5.defined M1 p n -> L5.defined M2 p n) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (pa_src_read A) M1 model1) K.
Proof.
  intros SRD Hh K0 BR FOK INCS X1 RA1 X2 X3 X4 X10 X11 X12 S1 S2 S3 Hq1 Hq2 Hkk KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (PNBK.scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC4 : scr 4 = 20480) by reflexivity. rewrite SC4 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1). pose proof (PMK.kl_errno segs L KL) as (ER0 & ER1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  set (O := PNM.src_owner segs A T3 T4 (pa_vp_parser A) (fb + 40) (fb + 472) fb (fb + 784) s1).
  assert (OK : PGS.owner_ok segs A L HI O) by (apply OWOK; [unfold hl_ceil in *; lia| lia| exact STOP| exact F3]).
  set (src1 := PNM.b_src s1) in *.
  set (LB1 := PM.src_own src1 ++ PNM.brest_own s1 ++ LBX).
  assert (ELB : PNM.bparser_own s1 ++ LBX = LB1) by (unfold LB1, PNM.bparser_own, src1; rewrite <- app_assoc; reflexivity).
  rewrite ELB in HH.
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 20480) by (apply (PMK.stk_call L M1 sp sc sp' 20480 STK); [exact S1| exact S2| lia| exact S3]).
  unfold PGS.src_read_specG, PGS.src_specG in SRD.
  apply (SRD O OK fx1 R1 M1 model1 K (PNM.brest_own s1) LBX cr1 sp' r' src1 str sm1 [(q, kk)] HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { cbn [O PNM.src_owner PGS.ow_lo]. lia. }
  { rewrite L5K.rl10. cbn [O PNM.src_owner PGS.ow_os]. unfold PNM.OFF_SRC. replace (fb + 40 + 16) with (fb + 56) by lia. exact X10. }
  { unfold PGS.read_args. exists q, kk. rewrite L5K.rl11, L5K.rl12. split; [exact X11|]. split; [exact X12|]. split; [unfold PM.CHUNK; lia|].
    unfold PGS.dst_okG. left. cbn [O PNM.src_owner PGS.ow_lo]. split; [exact Hq1|]. split; [lia|]. split; [lia|].
    apply (L5.defined_sub M1 (sp - sc) sc); [exact SDEF| lia| lia]. }
  { unfold PMPS.read_W. exists q, kk. rewrite L5K.rl11, L5K.rl12. split; [exact X11|]. split; [exact X12|]. split; [lia|]. split; [lia| reflexivity]. }
  { cbn [O PNM.src_owner PGS.ow_at]. split; [|reflexivity]. unfold src1. rewrite PNMF.with_srcB_id. exact PA1. }
  { cbn [O PNM.src_owner PGS.ow_ois]. exact IA1. }
  { exact BASE1. } { exact INCS. }
  intros fx2 R2 M2 src2 sm2 RP2 OW2 IA2 STEP2 RES2 HP2 HH2.
  cbn [O PNM.src_owner PGS.ow_at PGS.ow_ois PGS.ow_os] in OW2, IA2, HP2. destruct OW2 as (PA2 & _).
  unfold PNM.OFF_SRC in HP2.
  assert (QC2 : PM.sr_qc src2 = PM.sr_qc src1) by (destruct STEP2 as (E & _); exact E).
  unfold PMPS.read_res, PMSP.consumed in RES2. destruct RES2 as (p' & k' & d' & Y11 & Y12 & Hp' & Hk' & Y10 & Hd & CONS & DEF2 & _).
  assert (pk : p' = q /\ k' = kk).
  { change (getr R1 (PMK.reg 11) = Z_to_bv 64 p') in Y11. change (getr R1 (PMK.reg 12) = Z_to_bv 64 k') in Y12.
    rewrite X11 in Y11. rewrite X12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
    unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
  destruct pk as (-> & ->). change (getr R2 (PMK.reg 10) = Z_to_bv 64 d') in Y10.
  set (Wq := PGS.W_srcG (fb + 40 + 16) (fb + 472) src1 ++ [(q, kk)]) in HP2.
  assert (BRG : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH); apply incl_refl).
  assert (QIN : In (PM.sr_qc src1, PM.CHUNK) LB1) by (unfold LB1, PM.src_own; cbn; left; reflexivity).
  destruct (BRG _ _ QIN) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4.
  assert (WCq : forall a, PMK.inW Wq a -> (fb + 312 <= a < fb + 352) \/ (fb + 512 <= a < fb + 520) \/ (fb + 624 <= a < fb + 628)
                                           \/ (PM.sr_qc src1 <= a < PM.sr_qc src1 + PM.CHUNK) \/ (q <= a < q + kk)).
  { intros a (r0 & Hin & Hr). unfold Wq, PGS.W_srcG, PGS.W_srcfG in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin. }
  assert (EKc : PMK.ek L LB1 sp' 20480 Wq M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (DKc : PMK.dk L LB1 sp' 20480 M1 M2) by (apply (PMK.dk_callee L LB1 LB1 sp' 20480 sp' 20480 Wq M1 M2 HP2); [apply incl_refl| lia| lia]).
  assert (WHI : forall a, PMK.inW Wq a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L \/ (PM.sr_qc src1 <= a < PM.sr_qc src1 + PM.CHUNK)).
  { intros a I. apply WCq in I. destruct I as [I|[I|[I|[I|I]]]]; [left; lia| left; lia| left; lia| right; right; exact I| left; lia]. }
  assert (AGhi : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW Wq i) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 N. apply (PMPK.ag_hi segs L KL LB1 sp' 20480 Wq M1 M2 EKc STKc ltac:(lia) a n H1 H2 N). }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LB1 M1 M2 sp sc sp' 20480 Wq STK HP2); lia).
  assert (OWN1 : PNBK.own_ok L (PNM.bparser_own s1) LBX) by (apply (PNBK.own_ok_heap segs A AN L HI KH _ LBX cr1 M1 (m_vmmaps model1)); rewrite ELB; exact HH).
  destruct (PNBK.statics_keep segs A AN L HI KH LB1 sp' 20480 Wq M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCq in I. destruct I as [I|[I|[I|[I|I]]]]; unfold hl_ceil in *; lia. }
  apply (KONT fx2 R2 M2 src2 sm2 d' RP2 Y10 Hd).
  - clear - CONS. subst src1. Lia.lia.
  - exact DEF2.
  - unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax].
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGhi; [lia|lia| intros i Hi I; apply WCq in I; lia]|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGhi; [lia|lia| intros i Hi I; apply WCq in I; lia]|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|]. destruct s1; exact GR1. }
    split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP); destruct s1; exact STEP2|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        assert (HP2' : L5C.hpres L (PNM.bparser_own s1 ++ LBX) sp' 20480 Wq M1 M2) by (rewrite ELB; exact HP2).
        apply (PNBK.ek_lbx_callee segs A AN L HI KH (PNM.bparser_own s1) LBX sp sc sp' 20480 _ Wq M1 M1 M2 HP2' S2 S1 OWN1); [|exact STK|].
        + apply (PNBK.brange_hi_x segs A AN L HI KH (PNM.bparser_own s1) LBX cr1 M1 (m_vmmaps model1)). rewrite ELB. exact HH.
        + intros a I. apply WCq in I. destruct I as [I|[I|[I|[I|I]]]].
          * right. left. apply (PNBK.wrun_of_range segs A AN L HI KH). lia.
          * right. left. apply (PNBK.wrun_of_range segs A AN L HI KH). lia.
          * right. left. apply (PNBK.wrun_of_range segs A AN L HI KH). lia.
          * right. right. exists (PM.sr_qc src1, PM.CHUNK). split; [unfold PNM.bparser_own, PM.src_own; cbn; left; reflexivity| cbn [fst snd]; exact I].
          * left. lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LB1 sp sc sp' 20480 Wq M1 M2 HP2); [unfold LB1; apply incl_appr; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split; [destruct s1; exact CK|]. split; [exact MB|].
    split; [rewrite (PNBK.own_with_src s1 src2 QC2); rewrite ELB; exact HH2|]. split; [exact STK2| exact MOK].
  - intros a n H1 H2 H3. apply AGhi; [exact H1| lia|]. intros i Hi I. apply WCq in I. lia.
  - (* [comment removed for export] *)
    intros p n Hp Hn LOC D. apply (defined_of_dk L LB1 sp' 20480 M1 M2 p n DKc Hp Hn); [| exact D].
    intros i Hi. destruct LOC as [(B & m & Hin & HB1 & HB2)|HF].
    + assert (HinL : In (B, m) LB1) by (rewrite <- ELB; apply in_or_app; left; exact Hin).
      destruct (BRG B m HinL) as (Z0 & Z1 & Z4).
      split; [left; exists (B, m); split; [exact HinL| cbn [fst snd]; lia]|]. unfold in_errno. lia.
    + split; [right; left; unfold hl_ceil in *; lia|]. unfold in_errno. unfold hl_ceil in *. lia.
Qed.

End Kit.
End PNBK4.
