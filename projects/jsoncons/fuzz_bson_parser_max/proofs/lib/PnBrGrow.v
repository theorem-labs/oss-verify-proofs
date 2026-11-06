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
     PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnBrObj PnBrKit PnBrKit2.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNBG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_remove_mid B n l1 l2 : (forall b, In b l1 -> fst b <> B) -> lb_remove B (l1 ++ (B, n) :: l2) = l1 ++ l2.
Proof.
  induction l1 as [|[c m] l1 IH]; intros H; cbn.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec c B) as [E|NE].
    + exfalso. apply (H (c, m)); [left; reflexivity| exact E].
    + rewrite IH; [reflexivity|]. intros b Hb. apply H. right. exact Hb.
Qed.
Lemma incl_lb_remove_keep B l LBX : incl LBX l -> (forall b, In b LBX -> fst b <> B) -> incl LBX (lb_remove B l).
Proof. intros I NB b Hb. destruct b as [c n]. apply L5C.in_lb_remove_neq; [apply I; exact Hb| exact (NB _ Hb)]. Qed.
(* [comment removed for export] *)
Lemma nodup_in_fst (LB : list (Z * Z)) B m m' : NoDup (map fst LB) -> In (B, m) LB -> In (B, m') LB -> m = m'.
Proof.
  induction LB as [|a LB IH]; intros ND H1 H2; [destruct H1|]. cbn [map] in ND. inversion ND as [|x l NI ND']. subst x l.
  destruct H1 as [->|H1]; destruct H2 as [H2|H2].
  - injection H2 as E. exact E.
  - exfalso. apply NI. apply PMPK.elem_of_In. cbn [fst]. apply (in_map fst LB (B, m') H2).
  - subst a. exfalso. apply NI. apply PMPK.elem_of_In. cbn [fst]. apply (in_map fst LB (B, m) H1).
  - exact (IH ND' H1 H2).
Qed.

(* [comment removed for export] *)
Lemma pot_grow L s b' k stk' : PNM.b_sk s = k -> 0 <= k ->
  PNR.pot_bparser L (PNM.BPST (PNM.b_more s) (PNM.b_done s) (PNM.b_src s) (PNM.b_bb s) (PNM.b_nb s) (PNM.b_tb s) (PNM.b_ng s) (PNM.b_tg s) (PNM.b_bg s) b' (k + 1) stk')
  = (fst (PNR.pot_bparser L s) - hl_k_per_malloc L, snd (PNR.pot_bparser L s) - (PNM.BSZ * 2 ^ (k + 1) + hl_b_overhead L)).
Proof.
  intros Hk Hk0. unfold PNR.pot_bparser, PNR.pot_bstack, PM.credit_add. cbn [fst snd PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg]. rewrite Hk.
  rewrite (Z.pow_add_r 2 (k + 1) 1), (Z.pow_add_r 2 k 1) by lia. change (2 ^ 1) with 2. f_equal; nia.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AN : PNL.pn_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KH : PNBK.khyps segs A AN L HI.
Let KL := PNBK.kh_KL _ _ _ _ _ KH.
Let SF := PNBK.kh_SF _ _ _ _ _ KH.
Let WF := PNBK.kh_WF _ _ _ _ _ KH.
Let HIok := PNBK.kh_HIok _ _ _ _ _ KH.
Let HFR := PNBK.kh_HFR _ _ _ _ _ KH.
Let HOP := PNBK.kh_HOP _ _ _ _ _ KH.
Let HOV := PNBK.kh_HOV _ _ _ _ _ KH.
Let HOIS := PNBK.kh_HOIS _ _ _ _ _ KH.
Let HOEC := PNBK.kh_HOEC _ _ _ _ _ KH.
Let BDI := PNBK.kh_BDI _ _ _ _ _ KH.
Let EDI := PNBK.kh_EDI _ _ _ _ _ KH.

Abbreviation mem := (word -> option byte).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation bparser_at := (PNM.bparser_at segs A T3 T4 (pa_vp_parser A)).
Abbreviation iss_at := (PM.iss_at segs A T3).
Abbreviation berr_ok := (PNST.berr_ok segs A AN).
Abbreviation brel := (PNBK.brel segs A AN L HI).
Abbreviation BENT := PNBK.BENT.
Abbreviation scr := PMSP.pm_scr.
Abbreviation pot := (PNR.pot_bparser L).
Abbreviation pwr := PNBK.pwr.

(* [comment removed for export] *)
Definition gw (h : Z) (LBX : list (Z * Z)) (sp fb : Z) (str : PM.vstr) (E0 : PNBK.bent) (LB : list (Z * Z))
           (M : mem) (model : Model) (cr : credit) (src : PM.srcst) (sm : PM.strm) (ax : PNST.bax) : Prop :=
  iss_at M (fb + 472) str sm /\ L5.u64_at segs M (fb + 464) (pa_vp_visitor A) /\ L5.u64_at segs M (fb + 456) (fb + 464)
  /\ PMST.base_ok segs A M /\ berr_ok M ax
  /\ PMSP.src_step (PNM.b_src (PNBK.be_s E0)) src (PNBK.be_sm E0) sm /\ PNST.bax_le (PNBK.be_ax E0) ax
  /\ L5C.hpres L LBX sp (scr h) (PNR.W_brun A AN fb) (PNBK.be_M E0) M
  /\ model_but_vm (PNBK.be_model E0) model /\ hi_heap HI LB cr M (m_vmmaps model)
  /\ L5C.stk (hl_sptop L) M sp (scr h) /\ PMSP.model_ok model /\ incl LBX LB.

Lemma gw_of_brel h LBX sp fb str E0 (M1 : mem) model1 cr1 s1 sm1 ax1 :
  brel h LBX sp fb str E0 (BENT M1 model1 cr1 s1 sm1 ax1) ->
  gw h LBX sp fb str E0 (PNM.bparser_own s1 ++ LBX) M1 model1 cr1 (PNM.b_src s1) sm1 ax1
  /\ bparser_at M1 (fb + 40) (fb + 472) s1 /\ PNM.bgrow_ok s1
  /\ PMSP.credit_keep (PNBK.be_cr E0) cr1 (pot (PNBK.be_s E0)) (pot s1).
Proof.
  intros (RP & STEP & AXL & HP & CK & MB & HH & STK & MOK). cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax] in *.
  destruct RP as (PA1 & IA1 & VIS1 & VREF1 & BASE1 & ERR1 & GR1).
  unfold PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE in PA1, IA1, VIS1, VREF1.
  rewrite HOP, HOIS in PA1. rewrite HOIS in IA1. rewrite HOV in VIS1. rewrite HOP, HOV in VREF1.
  split; [| split; [exact PA1| split; [exact GR1| exact CK]]].
  split; [exact IA1|]. split; [exact VIS1|]. split; [replace (fb + 456) with (fb + 40 + 416) by lia; exact VREF1|]. split; [exact BASE1|]. split; [exact ERR1|].
  split; [exact STEP|]. split; [exact AXL|]. split; [exact HP|]. split; [exact MB|]. split; [exact HH|]. split; [exact STK|]. split; [exact MOK|].
  apply incl_appr. apply incl_refl.
Qed.

Lemma brel_of_gw h LBX sp fb str E0 LB (M : mem) model cr src sm ax s' :
  gw h LBX sp fb str E0 LB M model cr src sm ax -> Permutation LB (PNM.bparser_own s' ++ LBX) ->
  bparser_at M (fb + 40) (fb + 472) s' -> PNM.b_src s' = src -> PNM.bgrow_ok s' ->
  PMSP.credit_keep (PNBK.be_cr E0) cr (pot (PNBK.be_s E0)) (pot s') ->
  brel h LBX sp fb str E0 (BENT M model cr s' sm ax).
Proof.
  intros (IA & VIS & VREF & BASE & ERR & STEP & AXL & HP & MB & HH & STK & MOK & INC) PERM PA SRC GR CK.
  unfold PNBK.brel. cbn [PNBK.be_M PNBK.be_model PNBK.be_cr PNBK.be_s PNBK.be_sm PNBK.be_ax].
  split.
  { unfold PNR.brun_pre, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PMSP.visitor_at, PNM.PSIZE. rewrite HOP, HOIS, HOV.
    split; [exact PA|]. split; [exact IA|]. split; [exact VIS|]. split; [replace (fb + 40 + 416) with (fb + 456) by lia; exact VREF|].
    split; [exact BASE|]. split; [exact ERR| exact GR]. }
  split; [rewrite SRC; exact STEP|]. split; [exact AXL|]. split; [exact HP|]. split; [exact CK|]. split; [exact MB|].
  split; [exact (PNBK.hi_heap_perm segs A AN L HI KH _ _ cr M _ HH PERM)|]. split; [exact STK| exact MOK].
Qed.

(* [comment removed for export] *)
Lemma gw_piece h LBX sp fb str E0 LB (M1 : mem) model1 cr1 src1 sm1 ax1 (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2 : mem) (P : Z -> Prop) K :
  0 <= h ->
  gw h LBX sp fb str E0 LB M1 model1 cr1 src1 sm1 ax1 ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  msteps segs (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom segs)) (@mkst fx2 R2 (Z_to_bv 64 pc2) M2 (seg_rom segs)) -> mem_grows M1 M2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, {P a} + {~ P a}) ->
  (forall a, P a -> (sp - scr h <= a < sp) \/ pwr fb a \/ (exists b, In b LB /\ ~ In b LBX /\ fst b <= a < fst b + snd b)) ->
  (gw h LBX sp fb str E0 LB M2 model1 cr1 src1 sm1 ax1 -> srealizes segs SCFG (@PMSP.cfg segs fx2 R2 pc2 M2 model1) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc1 M1 model1) K.
Proof.
  intros Hh GW FOK INCS MS MG FRZ DEC PF KONT.
  destruct GW as (IA1 & VIS1 & VREF1 & BASE1 & ERR1 & STEP & AXL & HP & MB & HH & STK & MOK & INC).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (PNBK.scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
  pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  assert (NDL : NoDup (map fst LB)) by exact (PMPK.heap_nodup L HI HIok LB cr1 M1 _ HH).
  apply (PMK.spiece segs L HI KL HIok LB cr1 M1 model1 fx1 fx2 R1 pc1 R2 pc2 M2 P K HH Mh Ml ltac:(lia) MS MG FRZ).
  { intros a Pa. destruct (PF a Pa) as [X|[X|(b & Hb & _ & Hr)]].
    - apply (PMK.cwr_stack L LB M1 sp sc a STK). lia.
    - apply (PMK.cwr_stack L LB M1 sp sc a STK). unfold PNBK.pwr in X. lia.
    - destruct b as (B, m). cbn [fst snd] in Hr. apply (PMK.cwr_block L LB B m a); [exact Hb| exact Hr]. }
  { exact DEC. }
  intros HH2. apply KONT.
  (* [comment removed for export] *)
  assert (NPhi : forall i, fb + 456 <= i -> ~ P i).
  { intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & _ & Hr)]]; [lia| unfold PNBK.pwr in X; lia|]. cbn [fst snd] in Hr.
    destruct (BRG B m Hb) as (_ & _ & Q4). unfold hl_ceil in Q4. lia. }
  assert (NPx : forall B m, In (B, m) LBX -> forall i, B <= i < B + m -> ~ P i).
  { intros B m Hin i Hi Pi. assert (HB : In (B, m) LB) by (apply INC; exact Hin).
    destruct (BRG B m HB) as (_ & _ & Q4). unfold hl_ceil in Q4.
    destruct (PF i Pi) as [X|[X|((B', m') & Hb & NIN & Hr)]]; [lia| unfold PNBK.pwr in X; lia|]. cbn [fst snd] in Hr.
    assert (NE : B' <> B).
    { intros E. subst B'. apply NIN. rewrite (nodup_in_fst LB B m' m NDL Hb HB). exact Hin. }
    destruct (PMPK.blocks_apart_heap L HI HIok LB cr1 M1 _ B' m' B m HH Hb HB NE); lia. }
  assert (NPimg : forall i, hl_img_lo L <= i < hl_img_hi L -> ~ P i).
  { intros i Hi Pi. destruct (PF i Pi) as [X|[X|((B, m) & Hb & _ & Hr)]]; [lia| unfold PNBK.pwr in X; lia|]. cbn [fst snd] in Hr.
    destruct (BRG B m Hb) as (_ & Q1 & _). lia. }
  assert (AGP : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2 N i Hi. apply FRZ; [lia| apply N; exact Hi]. }
  destruct (PNBK.statics_agree segs A AN L HI KH M1 M2 ax1) as (BASE2 & ERR2); [intros a Ha; apply FRZ; [lia| apply NPimg; exact Ha]| exact BASE1| exact ERR1|].
  unfold gw.
  split.
  { apply (PMF.iss_at_agree segs A M1 M2 (fb + 472) str sm1); [lia|lia| apply AGP; [lia|lia| intros i Hi; apply NPhi; lia]| | exact IA1].
    intros c n p ->. assert (Hin : In (p, c) LBX) by (apply INCS; cbn; auto).
    destruct (BRG p c (INC _ Hin)) as (Q0 & _ & Q4). unfold hl_ceil in Q4.
    apply AGP; [lia|lia| exact (NPx p c Hin)]. }
  split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGP; [lia|lia| intros i Hi; apply NPhi; lia]|lia|lia| exact VIS1]|].
  split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGP; [lia|lia| intros i Hi; apply NPhi; lia]|lia|lia| exact VREF1]|].
  split; [exact BASE2|]. split; [exact ERR2|]. split; [exact STEP|]. split; [exact AXL|].
  split.
  { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
    - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
      apply (PMK.ek_piece L LBX sp sc _ M1 M2 P FRZ). intros a Ha Hc He Ho Pa.
      destruct (PF a Pa) as [X|[X|((B, m) & Hb & NIN & Hr)]].
      + destruct Hc as [((B', m') & Hb' & Hr')|[(S1 & S2)|(I1 & I2)]]; [|lia|lia]. cbn [fst snd] in Hr'.
        destruct (BRG B' m' (INC _ Hb')) as (_ & _ & Q4). unfold hl_ceil in Q4. lia.
      + exact (PMK.inW_not_outside _ a (PNBK.pwr_wrun segs A AN L HI KH fb a X) Ho).
      + cbn [fst snd] in Hr. destruct (BRG B m Hb) as (_ & Q1 & Q4). unfold hl_ceil in Q4.
        destruct Hc as [((B', m') & Hb' & Hr')|[(S1 & S2)|(I1 & I2)]]; [|lia|lia]. cbn [fst snd] in Hr'.
        exact (NPx B' m' Hb' a Hr' Pa).
    - destruct (PMK.stk_grows L M1 M2 sp sc MG STK) as (_ & _ & _ & _ & D). exact D.
    - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)). apply (PMK.dk_grows L LBX sp sc M1 M2 MG). }
  split; [exact MB|]. split; [exact HH2|]. split; [apply (PMK.stk_grows L M1 M2 sp sc MG STK)|]. split; [exact MOK| exact INC].
Qed.


(* [comment removed for export] *)
Lemma gw_objs_keep LB sp' sc' (M1 M2 : mem) fb str sm ax :
  PMK.ek L LB sp' sc' [] M1 M2 -> L5C.stk (hl_sptop L) M1 sp' sc' -> 0 <= sc' -> PMFR.brange L LB ->
  incl (PM.vs_own str) LB -> sp' <= fb -> fb + 784 <= hl_sptop L ->
  iss_at M1 (fb + 472) str sm -> L5.u64_at segs M1 (fb + 464) (pa_vp_visitor A) -> L5.u64_at segs M1 (fb + 456) (fb + 464) ->
  PMST.base_ok segs A M1 -> berr_ok M1 ax ->
  iss_at M2 (fb + 472) str sm /\ L5.u64_at segs M2 (fb + 464) (pa_vp_visitor A) /\ L5.u64_at segs M2 (fb + 456) (fb + 464)
  /\ PMST.base_ok segs A M2 /\ berr_ok M2 ax
  /\ (forall a n, sp' <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M1 M2 a n).
Proof.
  intros E STKc SC0 BRG INCS F1 F2 IA VIS VREF BASE ERR.
  pose proof STKc as (_ & SLO & SHI & STOP & _). pose proof (PMK.kl_img segs L KL) as (IMG0 & IMG1).
  assert (WHI' : forall a, PMK.inW [] a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
  assert (AGH : forall a n, sp' <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M1 M2 a n).
  { intros a n H1 H2. apply (PMFR.ag_hi segs L KL LB sp' sc' [] M1 M2 E STKc SC0 a n); [lia| exact H2|]. intros i Hi I. destruct (PMFR.inW_nil i I). }
  split; [apply (PMFR.iss_keep segs A L KL LB sp' sc' [] M1 M2 E STKc SC0 BRG WHI' (fb + 472) str sm); [lia|lia| intros i Hi; apply PMFR.inW_nil| exact INCS| exact IA]|].
  split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VIS]|].
  split; [apply (L5C.u64_at_agree segs M1 M2); [apply AGH; lia|lia|lia| exact VREF]|].
  split; [apply (PMKP.base_ok_keep segs A L KL SF LB sp' sc' [] M1 M2 E); first [exact BASE | intros a _; apply L5C.outside_nil]|].
  split; [apply (PNKP.berr_ok_keep segs A AN L KL SF WF (PNBK.kh_SFN _ _ _ _ _ KH) LB sp' sc' [] M1 M2 ax E); first [exact ERR | intros a _; apply L5C.outside_nil]|].
  exact AGH.
Qed.

(* [comment removed for export] *)
Lemma gw_opnew h LBX sp fb str E0 LB (M1 : mem) model1 cr1 src1 sm1 ax1 (fx1 : FPState) R1 (sp' r' n : Z) K :
  PMSP.opnew_spec segs A L HI ->
  0 <= h -> K [] ->
  gw h LBX sp fb str E0 LB M1 model1 cr1 src1 sm1 ax1 ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) -> getr R1 (PMK.reg 10) = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 -> credit_ok L cr1 n ->
  sp' <= sp -> sp - scr h <= sp' - PMSP.OPNEW_SCR -> sp' mod 16 = 0 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2 Bn,
      regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 Bn -> L5C.fresh_block L LB M2 Bn n ->
      gw h LBX sp fb str E0 ((Bn, n) :: LB) M2 model2 (debit L cr1 n) src1 sm1 ax1 ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M1 M2 a m) ->
      (forall b, In b LB -> L5C.agree_on M1 M2 (fst b) (snd b)) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 (pa_opnew A) M1 model1) K.
Proof.
  intros OPN Hh K0 GW FOK INCS X1 RA1 X2 X4 X10 Hn CROK S1 S2 S3 KONT.
  destruct GW as (IA1 & VIS1 & VREF1 & BASE1 & ERR1 & STEP & AXL & HP & MB & HH & STK & MOK & INC).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (PNBK.scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  change PMSP.OPNEW_SCR with 8240 in S2.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 8240) by (apply (PMK.stk_call L M1 sp sc sp' 8240 STK); [exact S1| exact S2| lia| exact S3]).
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  unfold PMSP.opnew_spec in OPN.
  apply (OPN fx1 R1 M1 model1 K LB cr1 n sp' r' HH MOK K0); [rewrite L5K.rl10; exact X10| exact Hn| exact CROK| rewrite L5K.rl1; exact X1| exact RA1| rewrite L5K.rl2; exact X2| rewrite L5K.rl4; exact X4| exact STKc|].
  intros fx2 R2 M2 model2 Bn Y10 RP2 FR HP2 MB2 HH2. rewrite L5K.rl10 in Y10.
  assert (EKc : PMK.ek L LB sp' 8240 [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  destruct (gw_objs_keep LB sp' 8240 M1 M2 fb str sm1 ax1 EKc STKc ltac:(lia) BRG ltac:(intros b Hb; apply INC; apply INCS; exact Hb) ltac:(lia) F2 IA1 VIS1 VREF1 BASE1 ERR1)
    as (IA2 & VIS2 & VREF2 & BASE2 & ERR2 & AGH).
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LB M1 M2 sp sc sp' 8240 [] STK HP2); lia).
  apply (KONT fx2 R2 M2 model2 Bn RP2 Y10 FR); [| exact AGH| intros b Hb; destruct b as (B', m'); cbn [fst snd]; apply (PMFR.ag_block segs L KL LB sp' 8240 [] M1 M2 EKc STKc ltac:(lia) BRG); [intros a I; destruct (PMFR.inW_nil a I)| exact Hb]].
  unfold gw. split; [exact IA2|]. split; [exact VIS2|]. split; [exact VREF2|]. split; [exact BASE2|]. split; [exact ERR2|].
  split; [exact STEP|]. split; [exact AXL|].
  split.
  { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
    - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
      apply (PMK.ek_callee L LBX LB sp sc sp' 8240 _ [] M1 M2 HP2 INC S2 S1). intros a _ _. apply L5C.outside_nil.
    - destruct STK2 as (_ & _ & _ & _ & D). exact D.
    - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)). apply (PMK.dk_callee L LBX LB sp sc sp' 8240 [] M1 M2 HP2 INC S2 S1). }
  split; [exact (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2|]. split; [exact STK2|]. split; [exact (PMFR.model_ok_but_vm model1 model2 MOK MB2)|].
  intros b Hb. right. apply INC. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma gw_opdel pc h LBX sp fb str E0 LB (M1 : mem) model1 cr1 src1 sm1 ax1 (fx1 : FPState) R1 (sp' r' B n : Z) K :
  PMSP.opdel_spec_at segs A L HI pc ->
  0 <= h -> K [] ->
  gw h LBX sp fb str E0 LB M1 model1 cr1 src1 sm1 ax1 ->
  PMSP.frame_ok A L sp fb -> incl (PM.vs_own str) LBX ->
  In (B, n) LB -> (forall b, In b LBX -> fst b <> B) ->
  getr R1 (PMK.reg 1) = Z_to_bv 64 r' -> L5.ra_ok r' -> getr R1 (PMK.reg 2) = Z_to_bv 64 sp' ->
  getr R1 (PMK.reg 4) = Z_to_bv 64 (pa_tp A) -> getr R1 (PMK.reg 10) = Z_to_bv 64 B ->
  sp' <= sp -> sp - scr h <= sp' - PMSP.OPDEL_SCR -> sp' mod 16 = 0 ->
  (forall (fx2 : FPState) R2 (M2 : mem) model2,
      regs_preserved R1 R2 ->
      gw h LBX sp fb str E0 (lb_remove B LB) M2 model2 cr1 src1 sm1 ax1 ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> L5C.agree_on M1 M2 a m) ->
      (forall b, In b (lb_remove B LB) -> L5C.agree_on M1 M2 (fst b) (snd b)) ->
      srealizes segs SCFG (@PMSP.cfg segs fx2 R2 r' M2 model2) K) ->
  srealizes segs SCFG (@PMSP.cfg segs fx1 R1 pc M1 model1) K.
Proof.
  intros OPD Hh K0 GW FOK INCS HIN NLBX X1 RA1 X2 X4 X10 S1 S2 S3 KONT.
  destruct GW as (IA1 & VIS1 & VREF1 & BASE1 & ERR1 & STEP & AXL & HP & MB & HH & STK & MOK & INC).
  pose proof FOK as (F1 & F2 & F3). rewrite HFR in F2.
  pose proof (PNBK.scr_nonneg h Hh) as SC0. set (sc := scr h) in *.
  change PMSP.OPDEL_SCR with 8224 in S2.
  pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof MOK as (Mh & Ml & Mm).
  assert (STKc : L5C.stk (hl_sptop L) M1 sp' 8224) by (apply (PMK.stk_call L M1 sp sc sp' 8224 STK); [exact S1| exact S2| lia| exact S3]).
  set (LB' := lb_remove B LB).
  assert (INC' : incl LBX LB') by (apply incl_lb_remove_keep; [exact INC| exact NLBX]).
  assert (SUB : incl LB' LB) by (intros b Hb; apply (L5C.in_lb_remove B); exact Hb).
  assert (BRG : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr1 M1 _ HH); apply incl_refl).
  assert (BRG' : PMFR.brange L LB') by (intros b m Hb; apply BRG; apply SUB; exact Hb).
  unfold PMSP.opdel_spec_at in OPD.
  apply (OPD fx1 R1 M1 model1 K LB cr1 B n sp' r' HH MOK K0 HIN); [rewrite L5K.rl10; exact X10| rewrite L5K.rl1; exact X1| exact RA1| rewrite L5K.rl2; exact X2| rewrite L5K.rl4; exact X4| exact STKc|].
  intros fx2 R2 M2 model2 RP2 HP2 MB2 HH2. fold LB' in HP2, HH2.
  assert (EKc : PMK.ek L LB' sp' 8224 [] M1 M2) by (apply (PMK.ek_of_hpres L); exact HP2).
  destruct (gw_objs_keep LB' sp' 8224 M1 M2 fb str sm1 ax1 EKc STKc ltac:(lia) BRG' ltac:(intros b Hb; apply INC'; apply INCS; exact Hb) ltac:(lia) F2 IA1 VIS1 VREF1 BASE1 ERR1)
    as (IA2 & VIS2 & VREF2 & BASE2 & ERR2 & AGH).
  assert (STK2 : L5C.stk (hl_sptop L) M2 sp sc) by (apply (PMK.stk_after segs L KL LB' M1 M2 sp sc sp' 8224 [] STK HP2); lia).
  apply (KONT fx2 R2 M2 model2 RP2); [| exact AGH|].
  - unfold gw. split; [exact IA2|]. split; [exact VIS2|]. split; [exact VREF2|]. split; [exact BASE2|]. split; [exact ERR2|].
    split; [exact STEP|]. split; [exact AXL|].
    split.
    { apply (PMK.hpres_of L LBX sp sc _ (PNBK.be_M E0) M2).
      - apply (PMK.ek_trans L LBX sp sc _ (PNBK.be_M E0) M1 M2 (PMK.ek_of_hpres L LBX sp sc _ _ M1 HP)).
        apply (PMK.ek_callee L LBX LB' sp sc sp' 8224 _ [] M1 M2 HP2 INC' S2 S1). intros a _ _. apply L5C.outside_nil.
      - destruct STK2 as (_ & _ & _ & _ & D). exact D.
      - apply (PMK.dk_trans L LBX sp sc (PNBK.be_M E0) M1 M2 (PMK.dk_of_hpres L LBX sp sc _ _ M1 HP)). apply (PMK.dk_callee L LBX LB' sp sc sp' 8224 [] M1 M2 HP2 INC' S2 S1). }
    split; [exact (L5C.model_but_vm_trans _ _ _ MB MB2)|]. split; [exact HH2|]. split; [exact STK2|]. split; [exact (PMFR.model_ok_but_vm model1 model2 MOK MB2)| exact INC'].
  - intros b Hb. destruct b as (B', m'). cbn [fst snd]. apply (PMFR.ag_block segs L KL LB' sp' 8224 [] M1 M2 EKc STKc ltac:(lia) BRG'); [| exact Hb].
    intros a I. destruct (PMFR.inW_nil a I).
Qed.

End Kit.
End PNBG.
