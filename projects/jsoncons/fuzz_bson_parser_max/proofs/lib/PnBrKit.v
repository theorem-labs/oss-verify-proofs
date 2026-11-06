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
     PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnBrObj.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBK.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
(* [comment removed for export] *)

Abbreviation mem := (word -> option byte).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation brun_pre := (PNR.brun_pre segs A AN).
Abbreviation berr_ok := (PNST.berr_ok segs A AN).
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation scr := PMSP.pm_scr.

(* [comment removed for export] *)
Definition bdom (a : Z) : Prop :=
  65536 <= a < pa_rw_lo A \/ pa_canary A <= a < pa_canary A + 8 \/ pa_need_locks A <= a < pa_need_locks A + 1
  \/ pa_locale_lock A <= a < pa_locale_lock A + 4.
(* [comment removed for export] *)
Record khyps : Prop := KHYPS {
  kh_KL : PMK.klayout segs L;
  kh_SF : PMKP.sfoot A L;
  kh_WF : PNST.addrs_wf A AN;
  kh_SFN : forall iv a, In iv (PNL.pn_d128_foot AN) -> fst iv <= a < snd iv -> PMKP.cstatic L a;
  kh_HIok : heap_iface_ok L SCFG HI;
  kh_HFR : pa_frame A = 784;
  kh_HOP : pa_off_p A = 40;
  kh_HOV : pa_off_v A = 464;
  kh_HOIS : pa_off_is A = 472;
  kh_HOEC : pa_off_ec A = 16;
  kh_BDI : forall a, bdom a -> hl_img_lo L <= a < hl_img_hi L;
  kh_EDI : forall a, PNKP.edep A AN a -> hl_img_lo L <= a < hl_img_hi L;
  kh_OWOK : forall fb s, hl_ceil L <= fb -> fb + 784 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> fb mod 16 = 0 ->
    PGS.owner_ok segs A L HI (PNM.src_owner segs A T3 T4 (pa_vp_parser A) (fb + 40) (fb + 472) fb (fb + 784) s);
  kh_EDB : forall a, PNKP.edep A AN a -> ~ bdom a;
  kh_KPM0 : 0 <= hl_k_per_malloc L;
  kh_BOV0 : 0 <= hl_b_overhead L
}.
Hypothesis KH : khyps.
Let KL := kh_KL KH.
Let SF := kh_SF KH.
Let WF := kh_WF KH.
Let SFN := kh_SFN KH.
Let HIok := kh_HIok KH.
Let HFR := kh_HFR KH.
Let HOP := kh_HOP KH.
Let HOV := kh_HOV KH.
Let HOIS := kh_HOIS KH.
Let HOEC := kh_HOEC KH.
Let BDI := kh_BDI KH.
Let EDI := kh_EDI KH.
Let OWOK := kh_OWOK KH.
Let EDB := kh_EDB KH.
Let KPM0 := kh_KPM0 KH.
Let BOV0 := kh_BOV0 KH.

Lemma statics_keep LB sp sc W (M M' : mem) ax :
  PMK.ek L LB sp sc W M M' -> (forall a, PMK.inW W a -> ~ (hl_img_lo L <= a < hl_img_hi L)) ->
  PMST.base_ok segs A M -> berr_ok M ax -> PMST.base_ok segs A M' /\ berr_ok M' ax.
Proof.
  intros E NI B ER. split.
  - apply (PMKP.base_ok_keep segs A L KL SF LB sp sc W M M' E); [| | | | exact B].
    all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; apply (NI a I); apply BDI; unfold bdom; tauto.
  - apply (PNKP.berr_ok_keep segs A AN L KL SF WF SFN LB sp sc W M M' ax E); [| exact ER].
    intros a Ha. apply PMFR.outside_of_not_inW. intros I. apply (NI a I). apply EDI. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pwr (fb a : Z) : Prop := (fb + 48 <= a < fb + 56) \/ (fb + 360 <= a < fb + 456).
Lemma wrun_where fb i : PMK.inW (PNR.W_brun A AN fb) i ->
  (fb + 48 <= i < fb + 56) \/ (fb + 312 <= i < fb + 352) \/ (fb + 512 <= i < fb + 520) \/ (fb + 624 <= i < fb + 628)
  \/ (fb + 360 <= i < fb + 456) \/ (fb + 16 <= i < fb + 32) \/ PMK.inW (PNST.berr_W A AN) i.
Proof.
  intros (r0 & Hin & Hr). unfold PNR.W_brun, PGS.W_srcfG, PNR.o_src, PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_ec, PNR.o_is, PNR.o_p,
    PMSP.o_p, PMSP.o_is, PMSP.o_ec, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in Hin.
  rewrite HOP, HOIS, HOEC in Hin. cbn [app] in Hin. unfold L5.in_rng in Hr.
  repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]).
  do 6 right. exists r0. split; [exact Hin| exact Hr].
Qed.
Lemma pwr_wrun fb a : pwr fb a -> PMK.inW (PNR.W_brun A AN fb) a.
Proof.
  unfold pwr, PNR.W_brun, PGS.W_srcfG, PNR.o_src, PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_ec, PNR.o_is, PNR.o_p,
    PMSP.o_p, PMSP.o_is, PMSP.o_ec, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
  rewrite HOP, HOIS, HOEC. cbn [app]. intros [H|H].
  - apply PMK.inW_here. lia.
  - destruct (Z_lt_ge_dec a (fb + 384)); [|destruct (Z_lt_ge_dec a (fb + 408)); [|destruct (Z_lt_ge_dec a (fb + 432))]].
    + do 4 apply PMK.inW_next. apply PMK.inW_here. lia.
    + do 5 apply PMK.inW_next. apply PMK.inW_here. lia.
    + do 6 apply PMK.inW_next. apply PMK.inW_here. lia.
    + do 7 apply PMK.inW_next. apply PMK.inW_here. lia.
Qed.

Lemma wrun_of_range fb a :
  (fb + 48 <= a < fb + 56) \/ (fb + 312 <= a < fb + 352) \/ (fb + 512 <= a < fb + 520) \/ (fb + 624 <= a < fb + 628)
  \/ (fb + 360 <= a < fb + 456) \/ (fb + 16 <= a < fb + 32) -> PMK.inW (PNR.W_brun A AN fb) a.
Proof.
  intros H. destruct H as [H|[H|[H|[H|[H|H]]]]]; [apply pwr_wrun; left; exact H| | | | apply pwr_wrun; right; exact H|].
  all: unfold PNR.W_brun, PGS.W_srcfG, PNR.o_src, PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_ec, PNR.o_is, PNR.o_p,
    PMSP.o_p, PMSP.o_is, PMSP.o_ec, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK; rewrite HOP, HOIS, HOEC; cbn [app].
  - do 1 apply PMK.inW_next. apply PMK.inW_here. lia.
  - do 2 apply PMK.inW_next. apply PMK.inW_here. lia.
  - do 3 apply PMK.inW_next. apply PMK.inW_here. lia.
  - do 8 apply PMK.inW_next. apply PMK.inW_here. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record bent : Type := BENT { be_M : mem; be_model : Model; be_cr : credit; be_s : PNM.bpst; be_sm : PM.strm; be_ax : PNST.bax }.

Definition brel (h : Z) (LBX : list (Z * Z)) (sp fb : Z) (str : PM.vstr) (E0 E1 : bent) : Prop :=
  brun_pre (be_M E1) fb (be_s E1) str (be_sm E1) (be_ax E1)
  /\ PMSP.src_step (PNM.b_src (be_s E0)) (PNM.b_src (be_s E1)) (be_sm E0) (be_sm E1)
  /\ PNST.bax_le (be_ax E0) (be_ax E1)
  /\ L5C.hpres L LBX sp (scr h) (PNR.W_brun A AN fb) (be_M E0) (be_M E1)
  /\ PMSP.credit_keep (be_cr E0) (be_cr E1) (pot (be_s E0)) (pot (be_s E1))
  /\ model_but_vm (be_model E0) (be_model E1)
  /\ hi_heap HI (PNM.bparser_own (be_s E1) ++ LBX) (be_cr E1) (be_M E1) (m_vmmaps (be_model E1))
  /\ L5C.stk (hl_sptop L) (be_M E1) sp (scr h)
  /\ PMSP.model_ok (be_model E1).

Lemma src_step_refl src sm : PMSP.src_step src src sm sm.
Proof. unfold PMSP.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.

Lemma credit_keep_refl cr p : PMSP.credit_keep cr cr p p.
Proof. unfold PMSP.credit_keep. lia. Qed.
Lemma credit_keep_trans c1 c2 c3 p1 p2 p3 : PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c2 c3 p2 p3 -> PMSP.credit_keep c1 c3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.

Lemma brel_init h LBX sp fb str M model cr s sm ax :
  0 <= h -> brun_pre M fb s str sm ax -> hi_heap HI (PNM.bparser_own s ++ LBX) cr M (m_vmmaps model) ->
  L5C.stk (hl_sptop L) M sp (scr h) -> PMSP.model_ok model ->
  brel h LBX sp fb str (BENT M model cr s sm ax) (BENT M model cr s sm ax).
Proof.
  intros Hh RP HH STK MOK. unfold brel. cbn [be_M be_model be_cr be_s be_sm be_ax].
  split; [exact RP|]. split; [apply src_step_refl|]. split; [apply PNST.bax_le_refl|].
  split.
  { apply (PMK.hpres_of L LBX sp (scr h) _ M M); [apply PMK.ek_refl| destruct STK as (_ & _ & _ & _ & D); exact D| apply PMK.dk_refl]. }
  split; [apply credit_keep_refl|]. split; [apply L5C.model_but_vm_refl|]. split; [exact HH|]. split; [exact STK| exact MOK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma statics_agree (M M' : mem) ax :
  (forall a, hl_img_lo L <= a < hl_img_hi L -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PMST.base_ok segs A M -> berr_ok M ax -> PMST.base_ok segs A M' /\ berr_ok M' ax.
Proof.
  intros AG (RO0 & (can & Hcan & CAN) & NL & LL) ER.
  pose proof (PMST.aw_canary A (PMKP.sf_wf A L SF)) as Hc.
  split.
  - split; [|split; [|split]].
    + intros i Hi. rewrite AG; [apply RO0; exact Hi| apply BDI; unfold bdom; tauto].
    + exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree segs M M'); [|lia|lia|exact CAN].
      intros i Hi. apply AG. apply BDI. unfold bdom. right. left. lia.
    + intros i Hi. rewrite AG; [apply NL; exact Hi| apply BDI; unfold bdom; tauto].
    + intros i Hi. rewrite AG; [apply LL; exact Hi| apply BDI; unfold bdom; tauto].
  - apply (PNKP.berr_agree segs A AN WF M M'); [|exact ER]. intros a Ha D. apply AG. apply EDI. exact D.
Qed.

(* [comment removed for export] *)
Lemma scr_nonneg h : 0 <= h -> 0 <= scr h.
Proof. unfold PMSP.pm_scr. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma brel_xfer h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (M2 : mem) (P : Z -> Prop) s2 :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ pwr fb a \/ in_block (PNM.bparser_own s1) a) ->
  bparser_at M2 (fb + 40) (fb + 472) s2 -> PNM.bparser_own s2 = PNM.bparser_own s1 -> PNM.b_src s2 = PNM.b_src s1 ->
  pot s2 = pot s1 -> PNM.bgrow_ok s2 ->
  hi_heap HI (PNM.bparser_own s1 ++ LBX) cr1 M2 (m_vmmaps model1) ->
  brel h LBX sp fb str E0 (BENT M2 model1 cr1 s2 sm1 ax1).
Proof.
  intros Hh BR FOK INCS MG FRZ PF PA2 OWN2 SRC2 POT2 GR2 HH2.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in *.
  destruct FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  set (LB := PNM.bparser_own s1 ++ LBX) in *.
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr1 M1 _ HH).
  (* [comment removed for export] *)
  assert (NPhi : forall i, fb + 456 <= i -> ~ P i).
  { intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| unfold pwr in X; lia|]. cbn [fst snd] in Hr.
    destruct (BRG B m ltac:(unfold LB; apply in_or_app; left; exact Hb)) as (_ & _ & Q4). unfold hl_ceil in Q4. lia. }
  assert (NPec : forall i, sp <= i < fb + 48 -> ~ P i).
  { intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| unfold pwr in X; lia|]. cbn [fst snd] in Hr.
    destruct (BRG B m ltac:(unfold LB; apply in_or_app; left; exact Hb)) as (_ & _ & Q4). unfold hl_ceil in Q4. lia. }
  assert (NPx : forall B m, In (B, m) LBX -> forall i, B <= i < B + m -> ~ P i).
  { intros B m Hin i Hi Pi. assert (HB : In (B, m) LB) by (unfold LB; apply in_or_app; right; exact Hin).
    destruct (BRG B m HB) as (_ & _ & Q4). unfold hl_ceil in Q4.
    destruct (PF i Pi) as [X|[X|((B', m') & Hb & Hr)]]; [lia| unfold pwr in X; lia|]. cbn [fst snd] in Hr.
    assert (HB' : In (B', m') LB) by (unfold LB; apply in_or_app; left; exact Hb).
    assert (NE : B' <> B) by (apply (PMPK.fst_neq_app (PNM.bparser_own s1) LBX B' m' B m NDL Hb Hin)).
    destruct (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ B' m' B m HH HB' HB NE); lia. }
  assert (NPimg : forall i, hl_img_lo L <= i < hl_img_hi L -> ~ P i).
  { intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & Hr)]]; [lia| unfold pwr in X; lia|]. cbn [fst snd] in Hr.
    destruct (BRG B m ltac:(unfold LB; apply in_or_app; left; exact Hb)) as (_ & Q1 & _). lia. }
  assert (AGP : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 N i Hi. apply FRZ; [lia| apply N; exact Hi]. }
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  destruct (statics_agree M1 M2 ax1) as (BASE2 & ERR2); [intros a Ha; apply FRZ; [lia| apply NPimg; exact Ha]| exact BASE1| exact ERR1|].
  unfold brel. cbn [be_M be_model be_cr be_s be_sm be_ax].
  split.
  { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
    split; [exact PA2|].
    split.
    { apply (PMF.iss_at_agree segs A M1 M2 (fb + 472) str sm1); [lia|lia| apply AGP; [lia|lia| intros i Hi; apply NPhi; lia]| | exact IA1].
      intros c n p ->. assert (Hin : In (p, c) LBX) by (apply INCS; cbn; auto).
      destruct (BRG p c ltac:(unfold LB; apply in_or_app; right; exact Hin)) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply AGP; [lia|lia| exact (NPx p c Hin)]. }
    split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGP; [lia|lia| intros i Hi; apply NPhi; lia]|lia|lia| exact VIS1]|].
    split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGP; [lia|lia| intros i Hi; apply NPhi; lia]|lia|lia| exact VREF1]|].
    split; [exact BASE2|]. split; [exact ERR2| exact GR2]. }
  split; [rewrite SRC2; exact STEP|]. split; [exact AXL|].
  split.
  { apply (PMK.hpres_of L LBX sp sc _ (be_M E0) M2).
    - apply (PMK.ek_trans L LBX sp sc _ (be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
      apply (PMK.ek_piece L LBX sp sc _ M1 M2 P FRZ). intros a Ha Hc He Ho Pa.
      destruct (PF a Pa) as [X|[X|((B, m) & Hb & Hr)]].
      + destruct Hc as [((B', m') & Hb' & Hr')|[(S1 & S2)|(I1 & I2)]]; [|lia|lia]. cbn [fst snd] in Hr'.
        destruct (BRG B' m' ltac:(unfold LB; apply in_or_app; right; exact Hb')) as (_ & _ & Q4). unfold hl_ceil in Q4. lia.
      + exact (PMK.inW_not_outside _ a (pwr_wrun fb a X) Ho).
      + cbn [fst snd] in Hr. assert (HB : In (B, m) LB) by (unfold LB; apply in_or_app; left; exact Hb).
        destruct (BRG B m HB) as (_ & Q1 & Q4). unfold hl_ceil in Q4.
        destruct Hc as [((B', m') & Hb' & Hr')|[(S1 & S2)|(I1 & I2)]]; [|lia|lia]. cbn [fst snd] in Hr'.
        exact (NPx B' m' Hb' a Hr' Pa).
    - destruct (PMK.stk_grows L M1 M2 sp sc MG STK) as (_ & _ & _ & _ & D). exact D.
    - apply (PMK.dk_trans L LBX sp sc (be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)). apply (PMK.dk_grows L LBX sp sc M1 M2 MG). }
  split; [rewrite POT2; exact CK|]. split; [exact MB|]. split; [rewrite OWN2; exact HH2|].
  split; [apply (PMK.stk_grows L M1 M2 sp sc MG STK)| exact MOK].
Qed.


(* [comment removed for export] *)
Lemma brel_piece h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) s2 K :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ pwr fb a \/ in_block (PNM.bparser_own s1) a) ->
  bparser_at M2 (fb + 40) (fb + 472) s2 -> PNM.bparser_own s2 = PNM.bparser_own s1 -> PNM.b_src s2 = PNM.b_src s1 ->
  pot s2 = pot s1 -> PNM.bgrow_ok s2 ->
  (brel h LBX sp fb str E0 (BENT M2 model1 cr1 s2 sm1 ax1) -> srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh BR FOK INCS MS MG FRZ DEC PF PA2 OWN2 SRC2 POT2 GR2 KONT.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in HH, STK, MOK.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
  set (LB := PNM.bparser_own s1 ++ LBX) in *.
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  apply (PMK.spiece segs L HI KL HIok LB cr1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2 P K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Pa. destruct (PF a Pa) as [X|[X|X]].
    - apply (PMK.cwr_stack L LB M1 sp (scr h) a STK). lia.
    - apply (PMK.cwr_stack L LB M1 sp (scr h) a STK). unfold pwr in X. lia.
    - destruct X as ((B, m) & Hb & Hr). cbn [fst snd] in Hr. apply (PMK.cwr_block L LB B m a); [unfold LB; apply in_or_app; left; exact Hb| exact Hr]. }
  { exact DEC. }
  intros HH2. apply KONT.
  exact (brel_xfer h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 M2 P s2 Hh BR FOK INCS MG FRZ PF PA2 OWN2 SRC2 POT2 GR2 HH2).
Qed.

(* [comment removed for export] *)
Lemma brel_stack_only h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (M2 : mem) (P : Z -> Prop) :
  0 <= h ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> sp - scr h <= a < sp) ->
  brel h LBX sp fb str E0 (BENT M2 model1 cr1 s1 sm1 ax1).
Proof.
  intros Hh BR FOK INCS MG FRZ DEC PF.
  pose proof BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in HH, STK, MOK, RP.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  set (LB := PNM.bparser_own s1 ++ LBX) in *.
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  destruct RP as (PA1 & _ & _ & _ & _ & _ & GR1).
  unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is in PA1. rewrite HOP, HOIS in PA1.
  assert (HH2 : hi_heap HI LB cr1 M2 (m_vmmaps model1)).
  { apply (PMK.hi_heap_stretch segs L HI KL HIok LB cr1 M1 M2 _ HH ltac:(lia)); [| exact MG].
    intros a Ha. destruct (DEC a) as [Y|N]; [right; apply (PMK.cwr_stack L LB M1 sp (scr h) a STK); pose proof (PF a Y); lia| left; apply FRZ; assumption]. }
  apply (brel_xfer h LBX sp fb str E0 M1 model1 cr1 s1 sm1 ax1 M2 P s1 Hh BR FOK INCS MG FRZ); [intros a Pa; left; exact (PF a Pa)| | reflexivity| reflexivity| reflexivity| exact GR1| exact HH2].
  apply (PNMF.bparser_at_agree segs A (pa_vp_parser A) M1 M2 (fb + 40) (fb + 472) s1); unfold PNM.PSIZE; [lia|lia| | | exact PA1].
  - intros i Hi. apply FRZ; [lia|]. intros Pi. pose proof (PF i Pi). lia.
  - intros B m Hin. destruct (BRG B m ltac:(unfold LB; apply in_or_app; left; exact Hin)) as (Q0 & _ & Q4). unfold hl_ceil in Q4. split; [lia|]. split; [lia|].
    intros i Hi. apply FRZ; [lia|]. intros Pi. pose proof (PF i Pi). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition own_ok (OWN LBX : list (Z * Z)) : Prop :=
  forall B m, In (B, m) OWN -> B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B)
                               /\ forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B.
Lemma own_ok_heap OWN LBX cr (M : mem) VM : hi_heap HI (OWN ++ LBX) cr M VM -> own_ok OWN LBX.
Proof.
  intros HH B m Hin. set (LB := OWN ++ LBX) in *.
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr M _ HH).
  assert (HB : In (B, m) LB) by (unfold LB; apply in_or_app; left; exact Hin). destruct (BRG B m HB) as (Z0 & Z1 & Z4).
  split; [exact Z4|]. split; [exact Z1|]. intros B' m' Hin'.
  assert (HB' : In (B', m') LB) by (unfold LB; apply in_or_app; right; exact Hin').
  assert (NE : B <> B') by (apply (PMPK.fst_neq_app OWN LBX B m B' m' NDL Hin Hin')).
  exact (PMPK.blocks_apart_heap L HI HIok LB cr M _ B m B' m' HH HB HB' NE).
Qed.

Lemma ek_lbx_callee OWN LBX sp sc sp' sc' W W' (M0 M M' : mem) :
  L5C.hpres L (OWN ++ LBX) sp' sc' W' M M' -> sp - sc <= sp' - sc' -> sp' <= sp ->
  own_ok OWN LBX -> (forall b, In b LBX -> fst b + snd b <= hl_ceil L) -> L5C.stk (hl_sptop L) M0 sp sc ->
  (forall a, PMK.inW W' a -> (sp - sc <= a < sp) \/ PMK.inW W a \/ in_block OWN a) ->
  PMK.ek L LBX sp sc W M M'.
Proof.
  intros HP H1 H2 HOWN HX STK HW. pose proof STK as (_ & SLO & SHI & STOP & _). pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  apply (PMK.ek_callee L LBX (OWN ++ LBX) sp sc sp' sc' W W' M M' HP); [apply incl_appr; apply incl_refl| exact H1| exact H2|].
  intros a Hc Ho r Hr Hin. destruct (HW a (ex_intro _ r (conj Hr Hin))) as [X|[X|((B, m) & Hb & Hrr)]].
  - destruct Hc as [((B', m') & Hb' & Hr')|[(S1 & S2)|(I1 & I2)]]; [|lia|unfold hl_ceil in *; lia].
    cbn [fst snd] in Hr'. pose proof (HX _ Hb') as Q. cbn [fst snd] in Q. unfold hl_ceil in *. lia.
  - exact (PMK.inW_not_outside _ a X Ho).
  - cbn [fst snd] in Hrr. destruct (HOWN B m Hb) as (Z1 & Z2 & Z3).
    destruct Hc as [((B', m') & Hb' & Hr')|[(S1 & S2)|(I1 & I2)]]; [|unfold hl_ceil in *; lia|lia].
    cbn [fst snd] in Hr'. destruct (Z3 B' m' Hb'); lia.
Qed.

Lemma brange_hi_x OWN LBX cr (M : mem) VM : hi_heap HI (OWN ++ LBX) cr M VM -> forall b, In b LBX -> fst b + snd b <= hl_ceil L.
Proof.
  intros HH. apply (PMFR.brange_hi L LBX). apply (PMFR.brange_of_heap L HI HIok (OWN ++ LBX) LBX cr M _ HH). apply incl_appr. apply incl_refl.
Qed.

(* [comment removed for export] *)
Lemma own_with_src s src' : PM.sr_qc src' = PM.sr_qc (PNM.b_src s) -> PNM.bparser_own (PNM.with_srcB s src') = PNM.bparser_own s.
Proof. intros E. destruct s. unfold PNM.bparser_own, PNM.brest_own, PM.src_own. cbn. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brel_src_read h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' q kk : Z) K :
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
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (pa_src_read A) M1 model1) K.
Proof.
  intros SRD Hh K0 BR FOK INCS X1 RA1 X2 X3 X4 X10 X11 X12 S1 S2 S3 Hq1 Hq2 Hkk KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC4 : scr 4 = 20480) by reflexivity. rewrite SC4 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
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
  assert (WHI : forall a, PMK.inW Wq a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L \/ (PM.sr_qc src1 <= a < PM.sr_qc src1 + PM.CHUNK)).
  { intros a I. apply WCq in I. destruct I as [I|[I|[I|[I|I]]]]; [left; lia| left; lia| left; lia| right; right; exact I| left; lia]. }
  assert (AGhi : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW Wq i) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 N. apply (PMPK.ag_hi segs L KL LB1 sp' 20480 Wq M1 M2 EKc STKc ltac:(lia) a n H1 H2 N). }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LB1 M1 M2 sp sc sp' 20480 Wq STK HP2); lia).
  assert (OWN1 : own_ok (PNM.bparser_own s1) LBX) by (apply (own_ok_heap _ LBX cr1 M1 (m_vmmaps model1)); rewrite ELB; exact HH).
  destruct (statics_keep LB1 sp' 20480 Wq M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCq in I. destruct I as [I|[I|[I|[I|I]]]]; unfold hl_ceil in *; lia. }
  apply (KONT fx2 R2 M2 src2 sm2 d' RP2 Y10 Hd).
  - clear - CONS. subst src1. Lia.lia.
  - exact DEF2.
  - unfold brel. cbn [be_M be_model be_cr be_s be_sm be_ax].
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGhi; [lia|lia| intros i Hi I; apply WCq in I; lia]|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGhi; [lia|lia| intros i Hi I; apply WCq in I; lia]|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|]. destruct s1; exact GR1. }
    split; [apply (PMPK.src_step_trans _ _ _ _ _ _ STEP); destruct s1; exact STEP2|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        assert (HP2' : L5C.hpres L (PNM.bparser_own s1 ++ LBX) sp' 20480 Wq M1 M2) by (rewrite ELB; exact HP2).
        apply (ek_lbx_callee (PNM.bparser_own s1) LBX sp sc sp' 20480 _ Wq M1 M1 M2 HP2' S2 S1 OWN1); [|exact STK|].
        + apply (brange_hi_x (PNM.bparser_own s1) LBX cr1 M1 (m_vmmaps model1)). rewrite ELB. exact HH.
        + intros a I. apply WCq in I. destruct I as [I|[I|[I|[I|I]]]].
          * right. left. apply wrun_of_range. lia.
          * right. left. apply wrun_of_range. lia.
          * right. left. apply wrun_of_range. lia.
          * right. right. exists (PM.sr_qc src1, PM.CHUNK). split; [unfold PNM.bparser_own, PM.src_own; cbn; left; reflexivity| cbn [fst snd]; exact I].
          * left. lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LB1 sp sc sp' 20480 Wq M1 M2 HP2); [unfold LB1; apply incl_appr; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split; [destruct s1; exact CK|]. split; [exact MB|].
    split; [rewrite (own_with_src s1 src2 QC2); rewrite ELB; exact HH2|]. split; [exact STK2| exact MOK].
  - intros a n H1 H2 H3. apply AGhi; [exact H1| lia|]. intros i Hi I. apply WCq in I. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma objs_keep LB sp' sc' W' (M1 M2 : mem) fb s str sm :
  PMK.ek L LB sp' sc' W' M1 M2 -> L5C.stk (hl_sptop L) M1 sp' sc' -> 0 <= sc' -> PMFR.brange L LB ->
  incl (PNM.bparser_own s) LB -> incl (PM.vs_own str) LB -> sp' <= fb -> fb + 784 <= hl_sptop L ->
  (forall a, PMK.inW W' a -> (sp' <= a < fb + 40) \/ (hl_img_lo L <= a < hl_img_hi L)) ->
  bparser_at M1 (fb + 40) (fb + 472) s -> iss_at M1 (fb + 472) str sm -> L5.u64_at segs M1 (fb + 464) (pa_vp_visitor A) ->
  L5.u64_at segs M1 (fb + 40 + 416) (fb + 464) ->
  bparser_at M2 (fb + 40) (fb + 472) s /\ iss_at M2 (fb + 472) str sm /\ L5.u64_at segs M2 (fb + 464) (pa_vp_visitor A)
  /\ L5.u64_at segs M2 (fb + 40 + 416) (fb + 464).
Proof.
  intros E STKc SC0 BRG INC INCS F1 F2 WHI PA IA VIS VREF.
  pose proof STKc as (_ & SLO & SHI & STOP & _). pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  assert (WHI' : forall a, PMK.inW W' a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (WHI a I); [left; lia| right; assumption]).
  assert (NW : forall i, fb + 40 <= i -> ~ PMK.inW W' i) by (intros i Hi I; destruct (WHI i I); lia).
  assert (AGH : forall a n, fb + 40 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2. apply (PMFR.ag_hi segs L KL LB sp' sc' W' M1 M2 E STKc SC0 a n); [lia| exact H2|]. intros i Hi. apply NW. lia. }
  split.
  { apply (PNMF.bparser_at_agree segs A (pa_vp_parser A) M1 M2 (fb + 40) (fb + 472) s); unfold PNM.PSIZE; [lia|lia| apply AGH; lia| | exact PA].
    intros B m Hin. apply INC in Hin. destruct (BRG _ _ Hin) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4. split; [lia|]. split; [lia|].
    apply (PMFR.ag_block segs L KL LB sp' sc' W' M1 M2 E STKc SC0 BRG WHI' B m Hin). }
  split.
  { apply (PMFR.iss_keep segs A L KL LB sp' sc' W' M1 M2 E STKc SC0 BRG WHI' (fb + 472) str sm); [lia|lia| intros i Hi; apply NW; lia| exact INCS| exact IA]. }
  split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VIS]|].
  apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VREF].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma catW_edep a : PMK.inW (PNST.cat_W A) a -> PNKP.edep A AN a.
Proof.
  intros (r0 & Hin & Hr). unfold PNST.cat_W in Hin. unfold L5.in_rng in Hr. unfold PNKP.edep.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; [left; lia| right; left; lia].
Qed.

Lemma brel_make_ec h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' v : Z) K :
  PNR.make_ec_spec segs A AN L HI ->
  0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 16) -> getr R1 (PMK.reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  sp' <= sp -> sp - scr h <= sp' - scr 1 -> sp' mod 16 = 0 -> L5.defined M1 (fb + 16) 16 ->
  (forall (fx2 : FPState) R2 (M2 : mem),
      regs_preserved R1 R2 -> PMSP.ec_at segs M2 (fb + 16) v (pa_errcat_obj A) ->
      brel h LBX sp fb str E0 (BENT M2 model1 cr1 s1 sm1 (PNST.bax_add_cat ax1)) ->
      (forall a n, sp' <= a -> a + n <= fb + 16 -> L5C.agree_on M1 M2 a n) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (pa_make_ec A) M1 model1) K.
Proof.
  intros MKE Hh K0 BR FOK INCS X1 RA1 X2 X3 X4 X10 X11 Hv S1 S2 S3 ED1 KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC1 : scr 1 = 14336) by reflexivity. rewrite SC1 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  set (LB1 := PNM.bparser_own s1 ++ LBX) in *.
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 14336) by (apply (PMK.stk_call L M1 sp sc sp' 14336 STK); [exact S1| exact S2| lia| exact S3]).
  assert (AL : (fb + 16) mod 8 = 0) by (replace (fb + 16) with (fb + 8 * 2) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  unfold PNR.make_ec_spec in MKE.
  apply (MKE fx1 R1 M1 model1 K LB1 cr1 (fb + 16) v sp' r' ax1 HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hv. } { lia. } { lia. } { exact AL. } { exact ED1. }
  { exact BASE1. } { exact ERR1. }
  intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
  set (WE := (fb + 16, 16) :: (if PNST.bax_cat ax1 then [] else PNST.cat_W A)) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> (fb + 16 <= a < fb + 32) \/ PMK.inW (PNST.cat_W A) a).
  { intros a (r0 & Hin & Hr). unfold WE in Hin. destruct Hin as [<-|Hin]; [left; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
    destruct (PNST.bax_cat ax1); [destruct Hin| right; exists r0; split; [exact Hin| exact Hr]]. }
  assert (EKc : PMK.ek L LB1 sp' 14336 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (BRG : PMFR.brange L LB1) by (apply (PMFR.brange_of_heap L HI HIok LB1 LB1 cr1 M1 _ HH); apply incl_refl).
  assert (WHI : forall a, PMK.inW WE a -> (sp' <= a < fb + 40) \/ (hl_img_lo L <= a < hl_img_hi L)).
  { intros a I. destruct (WCE a I) as [X|X]; [left; lia| right; apply EDI; apply catW_edep; exact X]. }
  destruct (objs_keep LB1 sp' 14336 WE M1 M2 fb s1 str sm1 EKc STKc ltac:(lia) BRG) as (PA2 & IA2 & VIS2 & VREF2);
    [unfold LB1; apply incl_appl; apply incl_refl| unfold LB1; apply incl_appr; exact INCS| lia| lia| exact WHI| exact PA1| exact IA1| exact VIS1| exact VREF1|].
  assert (BASE2 : PMST.base_ok segs A M2).
  { apply (PMKP.base_ok_keep segs A L KL SF LB1 sp' 14336 WE M1 M2 EKc); [| | | | exact BASE1].
    all: intros a Ha; apply PMFR.outside_of_not_inW; intros I; destruct (WCE a I) as [X|X];
      [assert (Hi : hl_img_lo L <= a < hl_img_hi L) by (apply BDI; unfold bdom; tauto); lia
      | apply (EDB a (catW_edep a X)); unfold bdom; tauto]. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LB1 M1 M2 sp sc sp' 14336 WE STK HP2); lia).
  assert (OWN1 : own_ok (PNM.bparser_own s1) LBX) by (apply (own_ok_heap _ LBX cr1 M1 (m_vmmaps model1)); exact HH).
  apply (KONT fx2 R2 M2 RP2 EC2).
  - unfold brel. cbn [be_M be_model be_cr be_s be_sm be_ax].
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|]. split; [exact VIS2|]. split; [exact VREF2|]. split; [exact BASE2|]. split; [exact ERR2| exact GR1]. }
    split; [exact STEP|]. split; [apply (PNST.bax_le_trans _ _ _ AXL); apply PNST.bax_le_cat|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (ek_lbx_callee (PNM.bparser_own s1) LBX sp sc sp' 14336 _ WE M1 M1 M2 HP2 S2 S1 OWN1); [|exact STK|].
        + apply (brange_hi_x (PNM.bparser_own s1) LBX cr1 M1 (m_vmmaps model1)). exact HH.
        + intros a I. right. left. destruct (WCE a I) as [X|X]; [apply wrun_of_range; lia|].
          unfold PNR.W_brun. rewrite !app_assoc. apply PMK.inW_app_r. unfold PNST.berr_W. apply PMK.inW_app_l. exact X.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LB1 sp sc sp' 14336 WE M1 M2 HP2); [unfold LB1; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split; [exact CK|]. split; [exact MB|]. split; [exact HH2|]. split; [exact STK2| exact MOK].
  - intros a n H1 H2. apply (PMFR.ag_hi segs L KL LB1 sp' 14336 WE M1 M2 EKc STKc ltac:(lia) a n H1); [lia|].
    intros i Hi I. destruct (WCE i I) as [X|X]; [lia|]. pose proof (EDI i (catW_edep i X)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hi_heap_perm LB LB' cr (M : mem) VM : hi_heap HI LB cr M VM -> Permutation LB LB' -> hi_heap HI LB' cr M VM.
Proof.
  intros HH P. apply (hio_perm L SCFG HI HIok LB LB' cr M VM HH).
  - intros b. split; [apply Permutation_in; exact P| apply Permutation_in; apply Permutation_sym; exact P].
  - apply base.NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst P)). apply base.NoDup_ListNoDup. exact (PMPK.heap_nodup L HI HIok LB cr M VM HH).
Qed.
Lemma perm4 {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (n ++ (a ++ b ++ c ++ t) ++ x).
Proof.
  apply (Permutation_trans (l' := (a ++ b ++ c) ++ n ++ t ++ x)); [rewrite <- !app_assoc; apply Permutation_refl|].
  apply (Permutation_trans (Permutation_app_swap_app (a ++ b ++ c) n (t ++ x))). rewrite <- !app_assoc. apply Permutation_refl.
Qed.
Lemma perm5 {T} (a b c n t x : list T) : Permutation ((a ++ b ++ c ++ n ++ t) ++ x) (t ++ (a ++ b ++ c ++ n) ++ x).
Proof.
  apply (Permutation_trans (l' := (a ++ b ++ c ++ n) ++ t ++ x)); [rewrite <- !app_assoc; apply Permutation_refl|].
  apply (Permutation_app_swap_app (a ++ b ++ c ++ n) t x).
Qed.

Lemma incl_own_r {T} (a b c n t : list T) (w : bool) : incl (a ++ b ++ c ++ (if w then t else n)) (a ++ b ++ c ++ n ++ t).
Proof.
  apply incl_app; [apply incl_appl; apply incl_refl|]. apply incl_appr. apply incl_app; [apply incl_appl; apply incl_refl|]. apply incl_appr.
  apply incl_app; [apply incl_appl; apply incl_refl|]. apply incl_appr. destruct w; [apply incl_appr| apply incl_appl]; apply incl_refl.
Qed.

Lemma pot_bstack_nonneg k : 0 <= k <= 11 -> 0 <= fst (PNR.pot_bstack L k) /\ 0 <= snd (PNR.pot_bstack L k).
Proof.
  intros Hk. unfold PNR.pot_bstack, PNM.BSZ. cbn [fst snd].
  assert (P : 2 ^ (k + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  split; [apply Z.mul_nonneg_nonneg; lia|]. assert (0 <= (11 - k) * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma pot_text_nonneg (M : mem) o x g : PM.vstr_at segs T3 M o x -> PM.tb_ok x g -> 0 <= fst (PM.pot_text L x g) /\ 0 <= snd (PM.pot_text L x g).
Proof.
  intros (_ & _ & VS) (Hg & _ & _). unfold PM.pot_text. cbn [fst snd].
  assert (C : PM.vs_cap x <= 2 ^ 27) by (destruct x as [n|c n p]; cbn [PM.vs_cap]; [lia| destruct VS as (_ & _ & _ & _ & Hc & _); lia]).
  split; [apply Z.mul_nonneg_nonneg; lia|]. assert (0 <= (23 - g) * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma pot_v8_nonneg (M : mem) v x g : PGV8.v8_at segs T3 T4 M v x -> PGV8.v8_ok x g -> 0 <= fst (PGV8.pot_v8 L x g) /\ 0 <= snd (PGV8.pot_v8 L x g).
Proof.
  intros (_ & _ & VS) OK. pose proof (PGV8.v8_ok_cap x g OK) as (Hg & _). unfold PGV8.pot_v8. cbn [fst snd].
  assert (C : PGV8.v8_cap x <= 2 ^ 27) by (destruct x as [|b n c]; cbn [PGV8.v8_cap]; [lia| destruct VS as (_ & _ & _ & _ & Hc & _); lia]).
  split; [apply Z.mul_nonneg_nonneg; lia|]. assert (0 <= (28 - g) * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.

Lemma brel_push_back_nb h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' c : Z) K :
  PNR.str_push_back_spec segs A AN L HI ->
  0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (be_s E0)) (be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 344) -> getr R1 (PMK.reg 11) = Z_to_bv 64 c -> 0 <= c < 256 ->
  sp' <= sp -> sp - scr h <= sp' - scr 1 -> sp' mod 16 = 0 -> PM.vs_size (PNM.b_nb s1) < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 x' g' cr2,
      regs_preserved R1 R2 -> PM.vs_size x' = PM.vs_size (PNM.b_nb s1) + 1 ->
      brel h LBX sp fb str E0 (BENT M2 model2 cr2 (PNBO.set_nb s1 x' g') sm1 ax1) ->
      (forall a n, sp' <= a -> a + n <= fb + 40 -> L5C.agree_on M1 M2 a n) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (PNL.pn_str_push_back AN) M1 model1) K.
Proof.
  intros PB Hh K0 BR FOK INCS CRED0 X1 RA1 X2 X3 X4 X10 X11 Hc S1 S2 S3 SZ KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC1 : scr 1 = 14336) by reflexivity. rewrite SC1 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1). pose proof (PMK.kl_errno segs L KL) as (ERN0 & ERN1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  destruct s1 as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  set (s1 := PNM.BPST mo dn src bb nb tb ng tg bg sb sk stk) in *.
  set (OWNr := PM.src_own src ++ PNM.bvec_own sb sk ++ PGV8.v8_own bb ++ PM.vs_own tb).
  set (LBr := OWNr ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) (PM.vs_own nb ++ LBr)).
  { unfold LBr, OWNr, s1, PNM.bparser_own, PNM.brest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply perm4. }
  assert (HHp : hi_heap HI (PM.vs_own nb ++ LBr) cr1 M1 (m_vmmaps model1)) by (apply (hi_heap_perm _ _ _ _ _ HH PERM1)).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 14336) by (apply (PMK.stk_call L M1 sp sc sp' 14336 STK); [exact S1| exact S2| lia| exact S3]).
  assert (AL : (fb + 40 + 344) mod 8 = 0) by (replace (fb + 40 + 344) with (fb + 8 * 48) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof PA1 as (_ & PDEF & _ & H8 & H9 & _ & _ & _ & SRC1 & _ & _ & BB1 & NB1 & TB1 & SV1 & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  cbn [s1 PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in H8, H9, SRC1, BB1, NB1, TB1, SV1, M01, D01.
  destruct GR1 as (GNB & GTB & GBB). cbn [s1 PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in GNB, GTB, GBB.
  assert (CRL1 : PMSP.credit_le (pot s1) cr1) by (apply (PMPK.credit_le_keep _ _ _ _ CRED0 CK)).
  assert (CRX : PMSP.credit_le (PM.pot_text L nb ng) cr1).
  { pose proof (pot_bstack_nonneg sk ltac:(destruct SV1 as (_ & _ & _ & Hk & _); exact Hk)) as (Q1 & Q2).
    pose proof (pot_text_nonneg _ _ _ _ TB1 GTB) as (Q3 & Q4). pose proof (pot_v8_nonneg _ _ _ _ BB1 GBB) as (Q5 & Q6).
    pose proof (pot_text_nonneg _ _ _ _ NB1 GNB) as (Q7 & Q8).
    revert CRL1. unfold PMSP.credit_le, PNR.pot_bparser, PM.credit_add, s1. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear - Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8. lia. }
  unfold PNR.str_push_back_spec in PB.
  apply (PB fx1 R1 M1 model1 K LBr cr1 (fb + 40 + 344) c sp' r' ng nb HHp MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hc. } { lia. } { lia. } { exact AL. }
  { exact NB1. } { exact GNB. } { exact SZ. } { exact CRX. }
  intros fx2 R2 M2 model2 x' g' cr2 RP2 VS2 SZ2 TBK2 _ HP2 CK2 MB2 HH2.
  set (s2 := PNBO.set_nb s1 x' g').
  assert (PERM2 : Permutation (PM.vs_own x' ++ LBr) (PNM.bparser_own s2 ++ LBX)).
  { unfold LBr, OWNr, s2, s1, PNM.bparser_own, PNM.brest_own. cbn [PNBO.set_nb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply Permutation_sym. apply perm4. }
  assert (HH2' : hi_heap HI (PNM.bparser_own s2 ++ LBX) cr2 M2 (m_vmmaps model2)) by (apply (hi_heap_perm _ _ _ _ _ HH2 PERM2)).
  pose proof (PMFR.model_ok_but_vm model1 model2 MOK MB2) as MOK2.
  set (WE := [(fb + 40 + 344, 24)] : list L5.range) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> fb + 40 + 344 <= a < fb + 40 + 344 + 24) by (intros a I; apply PMFR.inW_inv1 in I; exact I).
  assert (EKc : PMK.ek L LBr sp' 14336 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (BRr : PMFR.brange L LBr).
  { apply (PMFR.brange_of_heap L HI HIok _ LBr cr1 M1 _ HHp). apply incl_appr. apply incl_refl. }
  assert (WHI : forall a, PMK.inW WE a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WCE in I; left; lia).
  assert (AGH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 40 + 344 \/ fb + 40 + 344 + 24 <= a) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 H3. apply (PMFR.ag_hi segs L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) a n H1 H2). intros i Hi I. apply WCE in I. lia. }
  assert (AGB : forall B m, In (B, m) LBr -> L5C.agree_on M1 M2 B m) by (intros B m Hin; apply (PMFR.ag_block segs L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) BRr WHI B m Hin)).
  assert (DKH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M1 M2 a n) by (intros a n H1 H2; apply (PMPK.dkr_hpres_hi segs L KL LBr sp' 14336 WE M1 M2 a n HP2 STKc ltac:(lia) H1 H2)).
  assert (DKB : forall B m, In (B, m) LBr -> PMPK.dkr M1 M2 B m) by (intros B m Hin; apply (PMPK.dkr_hpres_blk segs L KL LBr sp' 14336 WE M1 M2 B m HP2 Hin BRr); lia).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) LBr) by (unfold LBr, OWNr, PM.src_own; cbn; left; reflexivity).
  assert (SIN : In (sb, PNM.BSZ * 2 ^ sk) LBr) by (unfold LBr, OWNr, PNM.bvec_own; cbn; right; left; reflexivity).
  assert (PA2 : bparser_at M2 (fb + 40) (fb + 472) s2).
  { unfold PNM.bparser_at, PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    cbn [s2 s1 PNBO.set_nb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
    destruct PA1 as (H0 & _ & _ & _ & _ & H10 & H12 & NI & _ & H312 & _).
    split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H0]|].
    split; [apply (PMPK.defined_dkr M1 M2 (fb + 40) 416); [apply DKH; lia| exact PDEF]|]. split; [exact I|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H8]|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H9]|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H10]|].
    split; [apply (PMF.u32_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H12]|].
    split; [apply (PMF.nullis_at_agree segs A M1 M2); [lia|lia| apply AGH; lia| exact NI]|].
    split.
    { destruct (BRr _ _ QIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PMF.src_fields_at_agree segs M1 M2); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AGH; lia| apply AGB; exact QIN| exact SRC1]. }
    split; [apply (PMF.u32_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H312]|]. split; [exact I|].
    split.
    { apply (PNMF.v8_at_keep segs M1 M2); [lia|lia| apply AGH; lia| | exact BB1].
      intros b n c0 E. apply DKB. unfold LBr, OWNr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      rewrite E. cbn. auto. }
    split; [exact VS2|].
    split.
    { apply (PNMF.vstr_at_keep segs M1 M2 (fb + 40 + 368) tb); [lia|lia| destruct tb; cbn [PNMF.vs_cells fst snd]; apply AGH; lia| apply DKH; lia| | exact TB1].
      intros c0 n p E. apply DKB. unfold LBr, OWNr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      rewrite E. cbn. auto. }
    split.
    { destruct (BRr _ _ SIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PNMF.bvec_at_agree segs M1 M2); [lia|lia|lia|lia| apply AGH; lia| apply AGB; exact SIN| exact SV1]. }
    split; [exact M01| exact D01]. }
  assert (INCSr : incl (PM.vs_own str) LBr) by (unfold LBr; apply incl_appr; exact INCS).
  assert (IA2 : iss_at M2 (fb + 472) str sm1).
  { apply (PMFR.iss_keep segs A L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) BRr WHI (fb + 472) str sm1); [lia|lia| intros i Hi I; apply WCE in I; lia| exact INCSr| exact IA1]. }
  destruct (statics_keep LBr sp' 14336 WE M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCE in I. lia. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LBr M1 M2 sp sc sp' 14336 WE STK HP2); lia).
  assert (OWN1 : own_ok (PNM.bparser_own s1) LBX) by (apply (own_ok_heap _ LBX cr1 M1 (m_vmmaps model1)); exact HH).
  assert (OWNR : own_ok OWNr LBX).
  { intros B m Hin. apply OWN1. revert Hin. apply (incl_own_r (PM.src_own src) (PNM.bvec_own sb sk) (PGV8.v8_own bb) (PM.vs_own nb) (PM.vs_own tb) true). }
  apply (KONT fx2 R2 M2 model2 x' g' cr2 RP2 SZ2).
  - unfold brel. cbn [be_M be_model be_cr be_s be_sm be_ax]. fold s2.
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|].
      unfold PNM.bgrow_ok. cbn [s2 s1 PNBO.set_nb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg]. split; [exact TBK2|]. split; [exact GTB| exact GBB]. }
    split; [exact STEP|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (ek_lbx_callee OWNr LBX sp sc sp' 14336 _ WE M1 M1 M2 HP2 S2 S1 OWNR); [|exact STK|].
        + apply (PMFR.brange_hi L LBX). apply (PMFR.brange_incl L LBX LBr BRr). unfold LBr. apply incl_appr. apply incl_refl.
        + intros a I. right. left. apply WCE in I. apply wrun_of_range. lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LBr sp sc sp' 14336 WE M1 M2 HP2); [unfold LBr; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split.
    { revert CK CK2. unfold PMSP.credit_keep, PNR.pot_bparser, PM.credit_add, s2, s1.
      cbn [PNBO.set_nb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear. lia. }
    split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2'|]. split; [exact STK2| exact MOK2].
  - intros a n H1 H2. apply AGH; [exact H1| lia| lia].
Qed.

Lemma brel_push_back_tb h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 (fx1 : FPState) R1 (sp' r' c : Z) K :
  PNR.str_push_back_spec segs A AN L HI ->
  0 <= h -> K [] ->
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX -> PMSP.credit_le (pot (be_s E0)) (be_cr E0) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 3) = Z_to_bv 64 (pa_gp A) -> getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 40 + 368) -> getr R1 (PMK.reg 11) = Z_to_bv 64 c -> 0 <= c < 256 ->
  sp' <= sp -> sp - scr h <= sp' - scr 1 -> sp' mod 16 = 0 -> PM.vs_size (PNM.b_tb s1) < 2 ^ 26 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 x' g' cr2,
      regs_preserved R1 R2 -> PM.vs_size x' = PM.vs_size (PNM.b_tb s1) + 1 ->
      brel h LBX sp fb str E0 (BENT M2 model2 cr2 (PNBO.set_tb s1 x' g') sm1 ax1) ->
      (forall a n, sp' <= a -> a + n <= fb + 40 -> L5C.agree_on M1 M2 a n) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (PNL.pn_str_push_back AN) M1 model1) K.
Proof.
  intros PB Hh K0 BR FOK INCS CRED0 X1 RA1 X2 X3 X4 X10 X11 Hc S1 S2 S3 SZ KONT.
  destruct BR as (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [be_M be_model be_cr be_s be_sm be_ax] in *.
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  assert (SC1 : scr 1 = 14336) by reflexivity. rewrite SC1 in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1). pose proof (PMK.kl_errno segs L KL) as (ERN0 & ERN1).
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  destruct s1 as [mo dn src bb nb tb ng tg bg sb sk stk].
  cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_ng PNM.b_tg PNM.b_bg PNM.b_sb PNM.b_sk PNM.b_stk] in *.
  set (s1 := PNM.BPST mo dn src bb nb tb ng tg bg sb sk stk) in *.
  set (OWNr := PM.src_own src ++ PNM.bvec_own sb sk ++ PGV8.v8_own bb ++ PM.vs_own nb).
  set (LBr := OWNr ++ LBX).
  assert (PERM1 : Permutation (PNM.bparser_own s1 ++ LBX) (PM.vs_own tb ++ LBr)).
  { unfold LBr, OWNr, s1, PNM.bparser_own, PNM.brest_own. cbn [PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply perm5. }
  assert (HHp : hi_heap HI (PM.vs_own tb ++ LBr) cr1 M1 (m_vmmaps model1)) by (apply (hi_heap_perm _ _ _ _ _ HH PERM1)).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 14336) by (apply (PMK.stk_call L M1 sp sc sp' 14336 STK); [exact S1| exact S2| lia| exact S3]).
  assert (AL : (fb + 40 + 368) mod 8 = 0) by (replace (fb + 40 + 368) with (fb + 8 * 51) by lia; apply PMPK.m8_add; apply PMPK.m16_8; exact F3).
  pose proof PA1 as (_ & PDEF & _ & H8 & H9 & _ & _ & _ & SRC1 & _ & _ & BB1 & NB1 & TB1 & SV1 & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  cbn [s1 PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in H8, H9, SRC1, BB1, NB1, TB1, SV1, M01, D01.
  destruct GR1 as (GNB & GTB & GBB). cbn [s1 PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg] in GNB, GTB, GBB.
  assert (CRL1 : PMSP.credit_le (pot s1) cr1) by (apply (PMPK.credit_le_keep _ _ _ _ CRED0 CK)).
  assert (CRX : PMSP.credit_le (PM.pot_text L tb tg) cr1).
  { pose proof (pot_bstack_nonneg sk ltac:(destruct SV1 as (_ & _ & _ & Hk & _); exact Hk)) as (Q1 & Q2).
    pose proof (pot_text_nonneg _ _ _ _ NB1 GNB) as (Q3 & Q4). pose proof (pot_v8_nonneg _ _ _ _ BB1 GBB) as (Q5 & Q6).
    pose proof (pot_text_nonneg _ _ _ _ TB1 GTB) as (Q7 & Q8).
    revert CRL1. unfold PMSP.credit_le, PNR.pot_bparser, PM.credit_add, s1. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear - Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8. lia. }
  unfold PNR.str_push_back_spec in PB.
  apply (PB fx1 R1 M1 model1 K LBr cr1 (fb + 40 + 368) c sp' r' tg tb HHp MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA1|]. split; [exact X2|].
    split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hc. } { lia. } { lia. } { exact AL. }
  { exact TB1. } { exact GTB. } { exact SZ. } { exact CRX. }
  intros fx2 R2 M2 model2 x' g' cr2 RP2 VS2 SZ2 TBK2 _ HP2 CK2 MB2 HH2.
  set (s2 := PNBO.set_tb s1 x' g').
  assert (PERM2 : Permutation (PM.vs_own x' ++ LBr) (PNM.bparser_own s2 ++ LBX)).
  { unfold LBr, OWNr, s2, s1, PNM.bparser_own, PNM.brest_own. cbn [PNBO.set_tb PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk]. apply Permutation_sym. apply perm5. }
  assert (HH2' : hi_heap HI (PNM.bparser_own s2 ++ LBX) cr2 M2 (m_vmmaps model2)) by (apply (hi_heap_perm _ _ _ _ _ HH2 PERM2)).
  pose proof (PMFR.model_ok_but_vm model1 model2 MOK MB2) as MOK2.
  set (WE := [(fb + 40 + 368, 24)] : list L5.range) in HP2.
  assert (WCE : forall a, PMK.inW WE a -> fb + 40 + 368 <= a < fb + 40 + 368 + 24) by (intros a I; apply PMFR.inW_inv1 in I; exact I).
  assert (EKc : PMK.ek L LBr sp' 14336 WE M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  assert (BRr : PMFR.brange L LBr).
  { apply (PMFR.brange_of_heap L HI HIok _ LBr cr1 M1 _ HHp). apply incl_appr. apply incl_refl. }
  assert (WHI : forall a, PMK.inW WE a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WCE in I; left; lia).
  assert (AGH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> (a + n <= fb + 40 + 368 \/ fb + 40 + 368 + 24 <= a) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 H3. apply (PMFR.ag_hi segs L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) a n H1 H2). intros i Hi I. apply WCE in I. lia. }
  assert (AGB : forall B m, In (B, m) LBr -> L5C.agree_on M1 M2 B m) by (intros B m Hin; apply (PMFR.ag_block segs L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) BRr WHI B m Hin)).
  assert (DKH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> PMPK.dkr M1 M2 a n) by (intros a n H1 H2; apply (PMPK.dkr_hpres_hi segs L KL LBr sp' 14336 WE M1 M2 a n HP2 STKc ltac:(lia) H1 H2)).
  assert (DKB : forall B m, In (B, m) LBr -> PMPK.dkr M1 M2 B m) by (intros B m Hin; apply (PMPK.dkr_hpres_blk segs L KL LBr sp' 14336 WE M1 M2 B m HP2 Hin BRr); lia).
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) LBr) by (unfold LBr, OWNr, PM.src_own; cbn; left; reflexivity).
  assert (SIN : In (sb, PNM.BSZ * 2 ^ sk) LBr) by (unfold LBr, OWNr, PNM.bvec_own; cbn; right; left; reflexivity).
  assert (PA2 : bparser_at M2 (fb + 40) (fb + 472) s2).
  { unfold PNM.bparser_at, PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    cbn [s2 s1 PNBO.set_tb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
    destruct PA1 as (H0 & _ & _ & _ & _ & H10 & H12 & NI & _ & H312 & _).
    split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H0]|].
    split; [apply (PMPK.defined_dkr M1 M2 (fb + 40) 416); [apply DKH; lia| exact PDEF]|]. split; [exact I|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H8]|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H9]|].
    split; [apply (L5C.u8_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H10]|].
    split; [apply (PMF.u32_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H12]|].
    split; [apply (PMF.nullis_at_agree segs A M1 M2); [lia|lia| apply AGH; lia| exact NI]|].
    split.
    { destruct (BRr _ _ QIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PMF.src_fields_at_agree segs M1 M2); [lia|lia|lia|unfold PM.CHUNK in *; lia| apply AGH; lia| apply AGB; exact QIN| exact SRC1]. }
    split; [apply (PMF.u32_at_agree segs M1 M2); [apply AGH; lia|lia|lia|exact H312]|]. split; [exact I|].
    split.
    { apply (PNMF.v8_at_keep segs M1 M2); [lia|lia| apply AGH; lia| | exact BB1].
      intros b n c0 E. apply DKB. unfold LBr, OWNr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      rewrite E. cbn. auto. }
    split.
    { apply (PNMF.vstr_at_keep segs M1 M2 (fb + 40 + 344) nb); [lia|lia| destruct nb; cbn [PNMF.vs_cells fst snd]; apply AGH; lia| apply DKH; lia| | exact NB1].
      intros c0 n p E. apply DKB. unfold LBr, OWNr. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      rewrite E. cbn. auto. }
    split; [exact VS2|].
    split.
    { destruct (BRr _ _ SIN) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
      apply (PNMF.bvec_at_agree segs M1 M2); [lia|lia|lia|lia| apply AGH; lia| apply AGB; exact SIN| exact SV1]. }
    split; [exact M01| exact D01]. }
  assert (INCSr : incl (PM.vs_own str) LBr) by (unfold LBr; apply incl_appr; exact INCS).
  assert (IA2 : iss_at M2 (fb + 472) str sm1).
  { apply (PMFR.iss_keep segs A L KL LBr sp' 14336 WE M1 M2 EKc STKc ltac:(lia) BRr WHI (fb + 472) str sm1); [lia|lia| intros i Hi I; apply WCE in I; lia| exact INCSr| exact IA1]. }
  destruct (statics_keep LBr sp' 14336 WE M1 M2 ax1 EKc) as (BASE2 & ERR2); [|exact BASE1| exact ERR1|].
  { intros a I Him. apply WCE in I. lia. }
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LBr M1 M2 sp sc sp' 14336 WE STK HP2); lia).
  assert (OWN1 : own_ok (PNM.bparser_own s1) LBX) by (apply (own_ok_heap _ LBX cr1 M1 (m_vmmaps model1)); exact HH).
  assert (OWNR : own_ok OWNr LBX).
  { intros B m Hin. apply OWN1. revert Hin. apply (incl_own_r (PM.src_own src) (PNM.bvec_own sb sk) (PGV8.v8_own bb) (PM.vs_own nb) (PM.vs_own tb) false). }
  apply (KONT fx2 R2 M2 model2 x' g' cr2 RP2 SZ2).
  - unfold brel. cbn [be_M be_model be_cr be_s be_sm be_ax]. fold s2.
    split.
    { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite ?HOP, ?HOIS, ?HOV.
      split; [exact PA2|]. split; [exact IA2|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VIS1]|].
      split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VREF1]|].
      split; [exact BASE2|]. split; [exact ERR2|].
      unfold PNM.bgrow_ok. cbn [s2 s1 PNBO.set_tb PNM.b_nb PNM.b_tb PNM.b_bb PNM.b_ng PNM.b_tg PNM.b_bg]. split; [exact GNB|]. split; [exact TBK2| exact GBB]. }
    split; [exact STEP|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (ek_lbx_callee OWNr LBX sp sc sp' 14336 _ WE M1 M1 M2 HP2 S2 S1 OWNR); [|exact STK|].
        + apply (PMFR.brange_hi L LBX). apply (PMFR.brange_incl L LBX LBr BRr). unfold LBr. apply incl_appr. apply incl_refl.
        + intros a I. right. left. apply WCE in I. apply wrun_of_range. lia.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.dk_callee L LBX LBr sp sc sp' 14336 WE M1 M2 HP2); [unfold LBr; apply incl_appr; apply incl_refl| exact S2| exact S1]. }
    split.
    { revert CK CK2. unfold PMSP.credit_keep, PNR.pot_bparser, PM.credit_add, s2, s1.
      cbn [PNBO.set_tb PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg fst snd]. clear. lia. }
    split; [apply (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2'|]. split; [exact STK2| exact MOK2].
  - intros a n H1 H2. apply AGH; [exact H1| lia| lia].
Qed.

End Kit.
End PNBK.
