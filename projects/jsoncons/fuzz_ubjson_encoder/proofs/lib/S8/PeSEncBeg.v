(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmSpecs PeSpecsS PmStep PmKeep PmFrame PmParKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCStatics PeCSpecs PeCSpecsS PeCFrame PeCKitS PeCKeep PeEncKit PeCpyKit AsanPlanSoundSums Es0Sums PeSEncBegP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Es0_code_36160_36164 Es0_code_35d2c_35d30.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PESENCB.
Import PMS.
Abbreviation CAD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Lemma e_begin_indef_err kd X : MAX_DEPTH < s_edepth X + 1 ->
  e_begin_indef kd X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X + 1) (s_lo X) (s_hi X) (s_bad X).
Proof. intros H. unfold e_begin_indef. cbv zeta. cbn [s_edepth w_edepth]. replace (MAX_DEPTH <? s_edepth X + 1) with true by (symmetry; apply Z.ltb_lt; exact H). destruct X; reflexivity. Qed.
Lemma e_begin_indef_ok kd X : s_edepth X + 1 <= MAX_DEPTH ->
  e_begin_indef kd X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) (s_ec X) (EI kd 0 0 :: s_estk X) (s_edepth X + 1) (s_lo X + 1) (s_hi X + 1) (s_bad X).
Proof. intros H. unfold e_begin_indef. cbv zeta. cbn [s_edepth w_edepth]. replace (MAX_DEPTH <? s_edepth X + 1) with false by (symmetry; apply Z.ltb_ge; lia). destruct X; reflexivity. Qed.

Definition CSL : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.
Local Ltac post_of P := destruct P as (fxpq & Rpq & Mpq & HPpq); exists fxpq, Rpq, Mpq; decompose [and] HPpq; repeat (split; [assumption|]); assumption.
Local Ltac post_of_v P v := destruct P as (fxpq & Rpq & Mpq & HPpq); exists fxpq, Rpq, Mpq, v; decompose [and] HPpq; repeat (split; [first [assumption | (clear; Lia.lia)]|]); assumption.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis PO : PESK.sink_policy_ok P.
Let KL := PECKS.klayout_S L LY.
Let SF := PECKS.sfoot_S L LY.
Abbreviation enc_at := (PEC.enc_at RSEGS EE L PMSP.T3 PMSP.T4).

Theorem v_begin_arr_ok :
  PESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P -> PECSS.make_ec_spec L HI -> PECSS.evec_alloc_spec L HI -> PECSS.evec_sbdtor_spec L HI ->
  PECSS.v_begin_arr_spec L HI P.
Proof.
  intros PB MKEC EVA EVD. unfold PECSS.v_begin_arr_spec, PECS.v_begin_arr_spec, PECS.eslot_spec.
  intros SPM [] fx R M model K LBX cr sp r fb cat p X s str sm en k e HH MOK K0 ENT FOK A10 A13 CPRE INCS POK MP NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame CAD PeCLayoutS.CADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  unfold PECS.args_t3 in A13.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI).
  destruct MP as ((LOHI & XBAD & FA & EDR) & LENLE).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl13 in A13.
  unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v, PESK.o_sink in *.
  cbn [pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S] in *.
  change (PMSP.pm_scr 4) with 20480 in *.
  assert (SC0 : 0 <= 20480) by lia.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
  assert (PINC : incl (PM.parser_own s) LB) by (unfold LB, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (KINC : incl (PESK.sink_own k) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }

  destruct en as [eb ek estk edepth].
  pose proof EA as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & _ & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EK, ELEN, EDEP, EKB, EBLK, EITEMS.

  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  set (n := Z.of_nat (length estk)).
  assert (HLENX : Z.of_nat (length (s_estk X)) = n) by (unfold n; rewrite Lestk, length_rev; reflexivity).
  rewrite HLENX in LENLE.
  pose proof (PEC.ecap_nonneg ek) as CN.
  assert (ECAPB : PEC.ecap ek <= 2048).
  { clear - EK. unfold PEC.ecap. destruct (ek =? 0); [Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. }
  assert (ALov : (fb + 440) mod 8 = 0) by (apply (PEEK.m8_of16 fb); [exact F3| reflexivity]).
  assert (ALsk : (fb + 496) mod 8 = 0) by (apply (PEEK.m8_of16 fb); [exact F3| reflexivity]).
  assert (ALec : (fb + 16) mod 8 = 0) by (apply (PEEK.m8_of16 fb); [exact F3| reflexivity]).
  assert (HO : bv_unsigned (getr R (PMK.reg 10)) = fb + 440) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HEC : bv_unsigned (getr R (PMK.reg 13)) = fb + 16) by (rewrite A13; apply L5.unsigned_lit; lia).
  unfold PEC.ESZ in EV32, EV40, ELEN. fold n in EV32.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as RB1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as RB8.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as RB9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as RB18.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as RB19. change (bv_modulus 64) with (2 ^ 64) in RB1, RB8, RB9, RB18, RB19.
  unfold PMSP.cfg. cbn [pe_begin_arr EE PeCLayoutS.EADDR_S].
  pose proof (ly_img_lo L LY) as IMLO. pose proof (ly_img_hi L LY) as IMHI.

  set (LBc0 := PM.parser_own s ++ LBX).
  assert (BRc0 : PMFR.brange L LBc0) by (apply (PMFR.brange_incl L LBc0 LB BR); unfold LBc0, LB, PEC.owned; insub).
  assert (PINC0 : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC0 : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  set (WEC := fun a : Z => (fb + 440 <= a < fb + 520) \/ (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
  assert (KEEPF : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WEC a) ->
            PM.parser_at RSEGS CAD PMSP.T3 PMSP.T4 M' (fb + 48) (fb + 520) s /\ PM.iss_at RSEGS CAD PMSP.T3 M' (fb + 520) str sm
            /\ L5.u64_at RSEGS M' (fb + 48 + 384) (fb + 440) /\ PMST.base_ok RSEGS CAD M' /\ PEC.content_ok RSEGS CAD M' fb p (PM.p_src s) str sm).
  { intros W M' EKW WC.
    assert (WHI : forall a, PMK.inW W a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC in I; unfold WEC in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
    assert (NW : forall i, ~ WEC i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PMFR.parser_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact PINC0| exact PA]|].
    split; [apply (PMFR.iss_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact IA]|].
    split; [apply (PMFR.u64_keep RSEGS L KL LBc0 sp 20480 W M M' EKW STK SC0); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact VREF]|].
    split; [apply (PMKP.base_ok_keep RSEGS CAD L KL SF LBc0 sp 20480 W M M' EKW); [| | | | exact BASE];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WEC;
            cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1; lia|].
    apply (PECF.content_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI fb p s str sm (fb + 48));
      unfold PMSP.o_is; cbn [pa_off_is CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact PINC0| exact IA| exact PA| exact CONT]. }
  set (WOB := fun a : Z => (fb + 440 <= a < fb + 520)).
  assert (KEEPE : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WOB a) ->
            PEST.err_ok RSEGS CAD EE M' e /\ PEC.ec_state RSEGS CAD M' fb (s_ec X) cat).
  { intros W M' EKW WC.
    assert (NW : forall i, ~ WOB i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PECKP.err_ok_keep RSEGS CAD EE L KL SF LBc0 sp 20480 W M M' EKW); [| | exact ERR];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WOB;
            cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1 IMLO IMHI; lia|].
    apply (PECF.ec_state_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 fb (s_ec X) cat);
      unfold PMSP.o_ec; cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WOB; lia| exact ECS]. }
  assert (WCE : forall a, PMK.inW (PEC.W_enc CAD EE fb) a -> WEC a).
  { intros a (r0 & Hin & Hr). unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink in Hin.
    cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in Hin.
    unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }

  assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
  assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
  assert (PEN : forall kk, 0 <= kk <= 12 -> 0 <= fst (PEC.pot_estack L kk) /\ 0 <= snd (PEC.pot_estack L kk)).
  { intros kk Hk. clear - KPM0 BOV0 Hk. unfold PEC.pot_estack, PEC.ESZ. cbn [fst snd]. assert (P2 : 2 ^ kk <= 2 ^ 12) by (apply Z.pow_le_mono_r; Lia.lia). split; Lia.nia. }
  assert (CREDk : PMSP.credit_le (PESK.sink_pot P (PESK.sk_c k)) cr).
  { pose proof (PEN ek EK) as PE. unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRED |- *. cbn [fst snd PEC.en_k] in CRED |- *. lia. }
  unfold MAX_DEPTH, MAX_ITEMS in EDR, EDEP, LENLE.
  assert (WRov : L5.writable RSEGS M (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF|lia|lia]).
  pose proof SKA as (_ & _ & _ & _ & _ & KZ & KCAP & KC0 & KBLK).
  set (en := PEC.ENC eb ek estk edepth) in *.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; insub).
  assert (BINk : 0 < ek -> In (eb, PEC.ESZ * PEC.ecap ek) (PEC.enc_own en)).
  { intros EKP. unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  assert (EBND : 0 < ek -> 4096 <= eb /\ eb + 24 * PEC.ecap ek <= hl_sptop L - 2 ^ 23 /\ (eb + 24 * PEC.ecap ek <= hl_img_lo L \/ hl_img_hi L <= eb)).
  { intros EKP. destruct (BR _ _ (EINC _ (BINk EKP))) as (B0 & B1 & B4). unfold hl_ceil in B4. unfold PEC.ESZ in B1, B4. split; [exact B0|]. split; [exact B4| exact B1]. }
  rewrite <- Ledepth in EDR.
  destruct (Z_lt_le_dec edepth 1024) as [DOK|DERR].
  2: {
    assert (ED : edepth = 1024) by lia.
    rewrite (e_begin_indef_err 3 X ltac:(unfold MAX_DEPTH; lia)) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB.
    pose proof (PESENBP.encBAe_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
    rewrite ED in EV48.
    PMK.feed P1 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov]) | PMK.sc | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
    assert (POSTC : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36058) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x36f18) M1 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBAe -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
      /\ getr R1 (PMK.reg 1) = Z_to_bv 64 221640
      /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 80)
      /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
      /\ getr R1 (PMK.reg 10) = getr R (PMK.reg 13)
      /\ getr R1 (PMK.reg 11) = Z_to_bv 64 11
      /\ L5.u32_at RSEGS M1 (fb + 440 + 48) 1025
      /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
      /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
      /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
      /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by post_of P1.
    clear P1.
    PMK.pvz_hg ltac:(idtac; destruct POSTC as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & C48 & S40 & S32 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1. rewrite A13 in X10_1.
    set (P1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36058 R1 0x36f18 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
    assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
    assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 80) 14336).
    { apply (PMK.stk_call L M1 sp 20480 (sp - 80) 14336 STK1); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (EKT1 : PMK.ek L LBc0 sp 20480 W1 M M1) by (apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx| intros a O; exact O]).
    destruct (KEEPF W1 M1 EKT1) as (_ & _ & _ & BASE1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
    destruct (KEEPE W1 M1 EKT1) as (ERR1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WOB. lia. }
    assert (ECD : L5.defined M (fb + 16) 16).
    { unfold PEC.ec_state, PMSP.o_ec in ECS. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S] in ECS.
      destruct (s_ec X); [destruct ECS as (v0 & _ & (_ & _ & D0)); exact D0| destruct ECS as (_ & _ & D0); exact D0]. }
    assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i' Hi'; apply NW1; lia| exact KINC| exact SKA]. }
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PEEK.enc_depth RSEGS EE L M M1 (fb + 440) fb eb ek _ edepth (edepth + 1) EA); [lia|lia| intros EKP; destruct (EBND EKP) as (B0 & B4 & _); unfold PEC.ESZ; clear - B0 B4 STOP; Lia.lia| | | exact MG1| replace (edepth + 1) with 1025 by lia; exact C48| unfold MAX_DEPTH; lia].
      - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
      - intros EKP i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1. unfold PEC.ESZ in Ri. destruct (EBND EKP) as (B0 & B4 & _). clear - Ri B4 SLO F1 SHI STOP. Lia.lia. }

    pose proof MKEC as MKX. unfold PECSS.make_ec_spec, PECS.make_ec_spec in MKX. cbn [pa_make_ec PECSS.AD PeCLayoutS.CADDR_S] in MKX.
    apply (MKX fx1 R1 M1 model K LB cr (fb + 16) 11 (sp - 80) 221640 e HH1 MOK K0); clear MKX.
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1_1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact X2_1|].
      split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
    { rewrite L5K.rl10. exact X10_1. }
    { rewrite L5K.rl11. exact X11_1. }
    { clear; Lia.lia. } { lia. } { lia. } { exact ALec. }
    { exact (L5.defined_grows M M1 _ _ MG1 ECD). }
    { exact BASE1. }
    { exact ERR1. }
    intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
    change (PMSP.pm_scr 1) with 14336 in HP2.
    set (W2 := (fb + 16, 16) :: (if e then [] else PMSP.err_W CAD)) in HP2.
    assert (WC2 : forall a, PMK.inW W2 a -> (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
    { intros a (r0 & Hin & Hr). unfold W2 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|].
      destruct e; [destruct Hin|]. unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Hin.
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    pose proof (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 80) 14336 _ STK1 HP2 ltac:(lia) ltac:(lia) ltac:(lia)) as STK2.
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    pose proof (PMK.ek_of_hpres L LB (sp - 80) 14336 W2 M1 M2 HP2) as EK2.
    assert (SC2 : 0 <= 14336) by lia.
    assert (WHI2 : forall a, PMK.inW W2 a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC2 in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
    assert (NW2 : forall i, (sp - 80 <= i < fb + 16 \/ fb + 16 + 16 <= i <= 2 ^ 64) -> ~ PMK.inW W2 i) by (intros i Hi I; apply WC2 in I; clear - Hi I IMLO IMHI F1 F2 STOP SLO; Lia.lia).
    assert (SV : forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
    { intros a v Ha Ha' U. apply (PMFR.u64_keep RSEGS L KL LB (sp - 80) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact U]. }
    pose proof (SV (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S40) as S40b. pose proof (SV (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S32) as S32b.
    pose proof (SV (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S24) as S24b. pose proof (SV (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S16) as S16b.
    pose proof (SV (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S8) as S8b.
    pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.

    pose proof (PESENBP.encBAr_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440
        | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
        | 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19))
        | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
    PMK.feed P3 ltac:(first [(unfold PESENBP.aligned; exact A16) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                           | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
    destruct P3 as (fx3 & R3 & M3 & _ & FRW3 & _ & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRW3). subst M3.
    apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 221640 R3 0x361b8 M2 K Mh Ml MS3).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M2 0x361b8 W_36160 r F_36160 eq_refl D_36160); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

    assert (EKT : PMK.ek L LBc0 sp 20480 (PEC.W_enc CAD EE fb) M M2).
    { apply (PMK.ek_trans L LBc0 sp 20480 _ M M1 M2).
      { apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 _ W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
        unfold PEC.W_enc, PMSP.o_v in O. cbn [pa_off_v CAD PeCLayoutS.CADDR_S app] in O.
        apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (PMK.ek_callee_in' RSEGS L KL LBc0 LB sp 20480 (sp - 80) 14336 _ W2 M1 M2 HP2 INC0);
        [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
      intros a I. apply WC2 in I. right. unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink.
      cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app].
      destruct I as [I|[I|I]]; [do 2 apply PMK.inW_next; apply PMK.inW_here; lia| do 3 apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia]. }
    destruct (KEEPF _ M2 EKT WCE) as (PA2 & IA2 & VREF2 & BASE2 & CONT2).
    assert (SKA2 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M2 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB (sp - 80) 14336 W2 M1 M2 EK2 STKc SC2 (PMFR.brange_incl L LB LB BR ltac:(apply incl_refl)) WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact KINC| exact SKA1]. }
    assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LB (sp - 80) 14336 W2 M1 M2 EK2 STKc SC2 BR WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact EINC| exact EA1]. }
    apply (KONT fx3 R3 M2 model (PEC.ENC eb ek estk (edepth + 1)) k true cr).
    - apply PMK.preserved_by_index. intros k0 Hk0.
      destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
      destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 18) as [->|N18]; [rewrite Y18; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 19) as [->|N19]; [rewrite Y19; apply PMPK.word_id|].
      assert (IN3 : In k0 PESENBP.KS_encBAr /\ In k0 PESENBP.KS_encBAe) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
      destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved R1 R2 k0 RP2 Hk0), (KS1 k0 I1). reflexivity.
    - unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
      split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|].
      split; [exact BASE2|]. split; [exact ERR2|]. split; [exact TBOK|]. split; [exact CONT2|].
      split.
      { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [exact Lestk|]. split; [lia|]. split; [exact Lz| exact Lbad]. }
      split; [| intros _; reflexivity].
      unfold PEC.ec_state, PMSP.o_ec. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]. exists 11. split; [clear; Lia.lia| exact EC2].
    - intros _; reflexivity.
    - apply (PMK.hpres_of L LBc0 sp 20480 _ M M2); [exact EKT| destruct STK2 as (_ & _ & _ & _ & D2); exact D2|].
      apply (PMK.dk_trans L LBc0 sp 20480 M M1 M2 (PMK.dk_grows L LBc0 sp 20480 M M1 MG1)).
      apply (PMK.dk_callee L LBc0 LB sp 20480 (sp - 80) 14336 _ M1 M2 HP2 INC0); lia.
    - unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k]. clear. Lia.lia.
    - apply L5C.model_but_vm_refl.
    - change (PEC.enc_own (PEC.ENC eb ek estk (edepth + 1))) with (PEC.enc_own en). exact HH2. }

  rewrite (e_begin_indef_ok 3 X ltac:(unfold MAX_DEPTH; lia)) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB.

  set (Ws := [(fb + 440, 56); (fb + 496, 24)] : list L5.range).
  assert (TAIL : forall (fxq : FPState) (Rq : bvmap 5 word) (Mq : word -> option byte) (modelq : Model) (crq : credit) (eb' ek' : Z),
    let en' := PEC.ENC eb' ek' (estk ++ [EI 3 0 0]) (edepth + 1) in
    getr Rq (PMK.reg 1) = Z_to_bv 64 221596 -> getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 80) ->
    getr Rq (PMK.reg 8) = Z_to_bv 64 (fb + 440) -> getr Rq (PMK.reg 10) = Z_to_bv 64 (fb + 496) -> getr Rq (PMK.reg 11) = Z_to_bv 64 (sp - 80) ->
    (forall x, In x CSL -> getr Rq (PMK.reg x) = getr R (PMK.reg x)) ->
    L5C.stk (hl_sptop L) Mq sp 20480 ->
    L5.u64_at RSEGS Mq (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) -> L5.u64_at RSEGS Mq (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
    L5.u64_at RSEGS Mq (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS Mq (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
    L5.u64_at RSEGS Mq (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) ->
    enc_at Mq (fb + 440) fb en' -> PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P Mq (fb + 496) k ->
    PMK.ek L LBc0 sp 20480 Ws M Mq -> PMK.dk L LBc0 sp 20480 M Mq ->
    PMSP.model_ok modelq -> model_but_vm model modelq ->
    hi_heap HI (PEC.owned s en' k ++ LBX) crq Mq (m_vmmaps modelq) ->
    PMSP.credit_le (PEC.pot_enc L P en' k) crq -> PMSP.credit_keep cr crq (PEC.pot_enc L P en k) (PEC.pot_enc L P en' k) ->
    srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x372d8 Mq modelq) K).
  { intros fxq Rq Mq modelq crq eb' ek' en' Q1 Q2 Q8 Q10 Q11 QCS STKq T40 T32 T24 T16 T8 EAq SKAq EKq DKq MOKq MBq HHq CRq CKq.
    pose proof MOKq as (Mhq & Mlq & Mmq).
    pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & _). cbn [PEC.en_k] in EKq'.
    set (LBq := PEC.owned s en' k ++ LBX) in HHq.
    set (LBYq := PM.parser_own s ++ PEC.enc_own en' ++ LBX).
    assert (PERMq : Permutation LBq (PESK.sink_own k ++ LBYq)) by (unfold LBq, LBYq, PEC.owned; rewrite <- !app_assoc; apply PEEK.perm4).
    assert (XINCq : incl LBc0 LBYq) by (unfold LBc0, LBYq; insub).
    assert (EINCq : incl (PEC.enc_own en') LBYq) by (unfold LBYq; insub).
    assert (STKcq : L5C.stk (hl_sptop L) Mq (sp - 80) 12288).
    { apply (PMK.stk_call L Mq sp 20480 (sp - 80) 12288 STKq); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    pose proof PB as PBX. unfold PESK.push_back_spec in PBX. cbn [pe_push_back EE PeCLayoutS.EADDR_S] in PBX.
    apply (PBX SPM fxq Rq Mq modelq K LBYq crq (fb + 496) (sp - 80) (sp - 80) 221596 k); clear PBX.
    { apply (PEEK.heap_perm L HI HIok LBq); [exact PERMq| exact HHq]. }
    { exact MOKq. }
    { exact K0. }
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact Q1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact Q2|].
      split; [rewrite (QCS 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (QCS 4%nat) by PMK.inl; exact Rtp|]. exact STKcq. }
    { rewrite L5K.rl10. exact Q10. }
    { rewrite L5K.rl11. exact Q11. }
    { exact SKAq. }
    { lia. } { lia. } { exact ALsk. } { lia. } { lia. } { left; lia. }
    { destruct STKq as (_ & _ & _ & _ & D1). apply (L5.defined_sub Mq (sp - 20480) 20480 (sp - 80) 1 D1); lia. }
    { intros ZC. apply (PESK.spo_next P PO (PESK.sk_c k) (s_hi X + 1) KCAP); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLK Hc))))))| exact HB| lia]. }
    { pose proof (PEN ek' EKq') as PE. unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRq |- *. unfold en' in CRq. cbn [fst snd PEC.en_k] in CRq |- *. clear - CRq PE. Lia.lia. }
    intros fx2 R2 M2 model2 cr2 b2 RP2 SKA2 HP2 CK2 MB2 HH2.
    change (PMSP.pm_scr 0) with 12288 in HP2. set (k2 := PESK.sk_push k b2) in *.
    pose proof (PMFR.model_ok_but_vm modelq model2 MOKq MB2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LBYq Mq M2 sp 20480 (sp - 80) 12288 _ STKq HP2); lia).
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    pose proof (PMK.ek_of_hpres L LBYq (sp - 80) 12288 [(fb + 496, 24)] Mq M2 HP2) as EK2.
    assert (BRY2 : PMFR.brange L (PESK.sink_own k2 ++ LBYq)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr2 M2 _ HH2); apply incl_refl).
    assert (BRYq : PMFR.brange L LBYq) by (apply (PMFR.brange_incl L LBYq _ BRY2); apply incl_appr; apply incl_refl).
    assert (WHI2 : forall a, PMK.inW [(fb + 496, 24)] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (SC2 : 0 <= 12288) by lia.
    assert (SV : forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Mq a v -> L5.u64_at RSEGS M2 a v).
    { intros a v Ha Ha' U. apply (PMFR.u64_keep RSEGS L KL LBYq (sp - 80) 12288 _ Mq M2 EK2 STKcq SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact U]. }
    pose proof (SV (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T40) as T40b. pose proof (SV (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T32) as T32b.
    pose proof (SV (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T24) as T24b. pose proof (SV (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T16) as T16b.
    pose proof (SV (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T8) as T8b.
    pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.

    pose proof (PESENBP.encBAu_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440
        | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
        | 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19))
        | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
    PMK.feed P3 ltac:(first [(unfold PESENBP.aligned; exact A16) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                           | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
    destruct P3 as (fx3 & R3 & M3 & _ & FRW3 & _ & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRW3). subst M3.
    apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 221596 R3 0x361b8 M2 K Mh2 Ml2 MS3).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh2| exact Ml2| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M2 0x361b8 W_36160 r F_36160 eq_refl D_36160); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

    assert (EKT : PMK.ek L LBc0 sp 20480 Ws M M2).
    { apply (PMK.ek_trans L LBc0 sp 20480 Ws M Mq M2 EKq).
      apply (PMK.ek_callee_in' RSEGS L KL LBc0 LBYq sp 20480 (sp - 80) 12288 Ws [(fb + 496, 24)] Mq M2 HP2 XINCq);
        [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
      intros a I. apply PMFR.inW_inv1 in I. right. apply PMK.inW_next. apply PMK.inW_here. lia. }
    destruct (KEEPF Ws M2 EKT) as (PA2 & IA2 & VREF2 & BASE2 & CONT2).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    destruct (KEEPE Ws M2 EKT) as (ERR2 & ECS2).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WOB. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (EA2 : enc_at M2 (fb + 440) fb en').
    { apply (PECF.enc_keep RSEGS EE L KL LBYq (sp - 80) 12288 [(fb + 496, 24)] Mq M2 EK2 STKcq SC2 BRYq WHI2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact EINCq| exact EAq]. }
    apply (KONT fx3 R3 M2 model2 en' k2 e cr2).
    - apply PMK.preserved_by_index. intros k0 Hk0.
      destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
      destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 18) as [->|N18]; [rewrite Y18; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 19) as [->|N19]; [rewrite Y19; apply PMPK.word_id|].
      assert (IN3 : In k0 PESENBP.KS_encBAu /\ In k0 CSL) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
      destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved Rq R2 k0 RP2 Hk0), (QCS k0 I1). reflexivity.
    - unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
      split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|].
      split; [exact BASE2|]. split; [exact ERR2|]. split; [exact TBOK|]. split; [exact CONT2|].
      split.
      { unfold PEC.clink, en'. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [rewrite Lestk; reflexivity|]. split; [lia|]. split; [|exact Lbad].
        unfold k2, PESK.sk_push. destruct (PESK.sk_z k <? PESK.sk_c k); cbn [PESK.sk_z]; lia. }
      split; [exact ECS2| exact ECI].
    - intros X'; exact X'.
    - apply (PMK.hpres_of L LBc0 sp 20480 _ M M2).
      + apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 _ Ws M M2 EKT); [apply incl_refl| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold PEC.W_enc, PMSP.o_v, PMSP.o_ec, PESK.o_sink in O.
        cbn [pa_off_v pa_off_ec pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in O.
        unfold Ws in Hr0. destruct Hr0 as [<-|[<-|[]]]; [apply (O (fb + 440, 56)); [left; reflexivity| exact Hin] | apply (O (fb + 496, 24)); [right; left; reflexivity| exact Hin]].
      + destruct STK2 as (_ & _ & _ & _ & D2). exact D2.
      + apply (PMK.dk_trans L LBc0 sp 20480 M Mq M2 DKq).
        apply (PMK.dk_callee L LBc0 LBYq sp 20480 (sp - 80) 12288 _ Mq M2 HP2 XINCq); lia.
    - unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add in CKq, CK2 |- *. unfold en' in CKq |- *. change (PEC.en_k en) with ek in CKq |- *.
      cbn [fst snd PEC.en_k] in CKq, CK2 |- *. clear - CKq CK2. Lia.lia.
    - exact (L5C.model_but_vm_trans _ _ _ MBq MB2).
    - refine (PEEK.heap_perm L HI HIok _ _ cr2 M2 _ _ HH2). unfold PEC.owned, LBYq. rewrite <- !app_assoc. apply Permutation_sym. apply PEEK.perm4. }
  unfold MAX_DEPTH in EV16.
  destruct (Z_lt_le_dec n (PEC.ecap ek)) as [ROOM|FULL].
  -
    assert (EKP : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in ROOM. rewrite Z0 in ROOM. cbn in ROOM. unfold n in ROOM. lia. }
    destruct (EBND EKP) as (B0 & B4 & B1). destruct (EBLK EKP) as (EBAL & EBDEF & EBR & _ & _). unfold PEC.ESZ in EBDEF.
    pose proof (EINC _ (BINk EKP)) as BIN.
    assert (ALend : (eb + 24 * n) mod 8 = 0) by (apply PEEK.al8_item; exact EBAL).
    assert (WRit : L5.writable RSEGS M (eb + 24 * n) 24).
    { apply (L5.writable_sub _ M eb (24 * PEC.ecap ek)); [apply (L5C.writable_of_defined RSEGS); [exact EBDEF|lia|lia]| unfold n; lia| lia]. }
    pose proof (PESENBP.encBAf_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => eb + 24 * n | 35%nat => eb + 24 * PEC.ecap ek | 36%nat => edepth | 41%nat => fb + 496 | _ => 0 end)) as P1.
    cbn beta iota in P1. rewrite !HO in P1.
    PMK.feed P1 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact ALsk | exact ALend]) | PMK.sc
                           | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ROOM CN ECAPB EDR; unfold hl_ceil, n in *; lia) ]).
    assert (POSTF : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
            ~ (eb + 24 * n + 0 <= i < eb + 24 * n + 0 + 24) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36058) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x372d8) M1 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBAf -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
      /\ getr R1 (PMK.reg 1) = Z_to_bv 64 221596
      /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 80)
      /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
      /\ getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 496)
      /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 80)
      /\ L5.u64_at RSEGS M1 (fb + 440 + 32) (eb + 24 * n + 24)
      /\ L5.u64_at RSEGS M1 (eb + 24 * n + 16) 0
      /\ L5.u64_at RSEGS M1 (eb + 24 * n + 8) 0
      /\ L5.u32_at RSEGS M1 (eb + 24 * n) 3
      /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth + 1)
      /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
      /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
      /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
      /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by post_of P1.
    clear P1.
    PMK.pvz_hg ltac:(idtac; destruct POSTF as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & C32 & I16 & I8 & I0 & C48 & S40 & S32 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1.
    set (P1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4) \/ (fb + 440 + 32 <= a < fb + 440 + 32 + 8) \/ (eb + 24 * n + 0 <= a < eb + 24 * n + 0 + 24)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| | | |]; intros X'; apply N; unfold P1; [left| right; left| right; right; left| right; right; right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36058 R1 0x372d8 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a [Pa|[Pa|[Pa|Pa]]]; [apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia
        | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia |].
      apply (PMK.cwr_block L _ eb (PEC.ESZ * PEC.ecap ek) a BIN). unfold PEC.ESZ. unfold n in ROOM. clear - Pa ROOM CN. Lia.lia. }
    { intros a. unfold P1. repeat (apply PMK.or_dec; [apply PMK.rng_dec|]). apply PMK.rng_dec. }
    intros HH1.
    set (LBcE := PESK.sink_own k ++ PM.parser_own s ++ LBX).
    assert (PERME : Permutation LB (PEC.enc_own en ++ LBcE)) by (unfold LB, LBcE, PEC.owned; rewrite <- !app_assoc; apply Permutation_sym; apply PEEK.perm4).
    pose proof (PEEK.heap_perm L HI HIok _ _ cr M1 _ PERME HH1) as HH1e.
    assert (BRE : PMFR.brange L LBcE) by (apply (PMFR.brange_of_heap L HI HIok _ LBcE cr M1 _ HH1e); apply incl_appr; apply incl_refl).
    set (WsE := [(fb + 440, 56)] : list L5.range).
    assert (EK1 : PMK.ek L LBcE sp 20480 WsE M M1).
    { apply (PEEK.ek_piece_own RSEGS L HI KL HIok (PEC.enc_own en) LBcE cr M1 _ sp 20480 WsE M M1 P1 eb (PEC.ESZ * PEC.ecap ek) HH1e (BINk EKP) FRZ1' ltac:(unfold hl_ceil; lia) ltac:(lia)).
      intros a [Pa|[Pa|[Pa|Pa]]]; [left; lia| right; left; apply PMK.inW_here; lia| right; left; apply PMK.inW_here; lia|].
      right. right. unfold PEC.ESZ. unfold n in ROOM. clear - Pa ROOM CN. Lia.lia. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LBcE sp 20480 WsE M M1 EK1 STK SC0 BRE); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| unfold LBcE; insub| exact SKA]. }
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (estk ++ [EI 3 0 0]) (edepth + 1))).
    { apply (PEEK.enc_push RSEGS EE L M M1 (fb + 440) fb eb ek estk edepth (edepth + 1) (EI 3 0 0) EA); [lia|lia| intros _; unfold PEC.ESZ; clear - B0 B4 STOP; Lia.lia| | | exact MG1| | exact C48| unfold MAX_DEPTH; lia| fold n; lia|].
      + intros i Hi Ri N1 N2. apply FRZ1'; [exact Hi|]. unfold P1. intros [X'|[X'|[X'|X']]]; [clear - X' Ri F1; Lia.lia| apply N2; clear - X'; Lia.lia| apply N1; clear - X'; Lia.lia|].
        unfold n in ROOM. clear - X' Ri B4 ROOM CN SLO F1. Lia.lia.
      + intros _ i Hi Ri. unfold PEC.ESZ in Ri. fold n in Ri. apply FRZ1'; [exact Hi|]. unfold P1. intros [X'|[X'|[X'|X']]]; [clear - X' Ri B4 ROOM CN SLO| clear - X' Ri B4 ROOM CN SLO F1| clear - X' Ri B4 ROOM CN SLO F1| clear - X' Ri]; Lia.lia.
      + unfold PEC.ESZ. fold n. replace (eb + 24 * (n + 1)) with (eb + 24 * n + 24) by (clear; Lia.lia). exact C32.
      + unfold PEC.eitem_at, PEC.ESZ. fold n. cbn [ei_kind ei_len ei_cnt]. split; [exact I0|]. split; [exact I8| exact I16]. }
    apply (TAIL fx1 R1 M1 model cr eb ek X1_1 X2_1 X8_1 X10_1 X11_1).
    + intros x Hx. apply KS1. exact (PEEK.sub_in PESENBP.KS_encBAf CSL ltac:(vm_compute; reflexivity) x Hx).
    + exact STK1. + exact S40. + exact S32. + exact S24. + exact S16. + exact S8. + exact EA1. + exact SKA1.
    + apply (PMK.ek_weaken L LBc0 LBcE sp 20480 sp 20480 Ws WsE M M1 EK1); [unfold LBc0, LBcE; insub| intros x Hx; exact Hx|].
      intros a O r0 Hr0 Hin. unfold WsE in Hr0. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin].
    + apply (PMK.dk_grows L LBc0 sp 20480 M M1 MG1).
    + exact MOK. + apply L5C.model_but_vm_refl.
    + change (PEC.enc_own (PEC.ENC eb ek (estk ++ [EI 3 0 0]) (edepth + 1))) with (PEC.enc_own en). exact HH1.
    + change (PEC.pot_enc L P (PEC.ENC eb ek (estk ++ [EI 3 0 0]) (edepth + 1)) k) with (PEC.pot_enc L P en k). exact CRED.
    + change (PEC.pot_enc L P (PEC.ENC eb ek (estk ++ [EI 3 0 0]) (edepth + 1)) k) with (PEC.pot_enc L P en k). unfold PMSP.credit_keep. clear. Lia.lia.
  -
    assert (FULLEQ : n = PEC.ecap ek) by lia.
    assert (EK10 : ek <= 11).
    { destruct (Z.eq_dec ek 12) as [E11|NE]; [exfalso| lia]. rewrite E11 in FULLEQ. cbn in FULLEQ. lia. }
    assert (NCE : PEC.ecap (ek + 1) = 2 ^ ek).
    { unfold PEC.ecap. replace (ek + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal. lia. }
    assert (NCB : 1 <= PEC.ecap (ek + 1) <= 2048).
    { rewrite NCE. clear - EK EK10. pose proof (Z.pow_pos_nonneg 2 ek ltac:(Lia.lia) ltac:(Lia.lia)). split; [Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. }
    assert (CAPGROW : PEC.ecap ek + 1 <= PEC.ecap (ek + 1)).
    { rewrite NCE. clear - EK. unfold PEC.ecap. destruct (Z.eqb_spec ek 0) as [->|NZ]; [cbn; Lia.lia|].
      replace (2 ^ ek) with (2 * 2 ^ (ek - 1)) by (rewrite <- Z.pow_succ_r by Lia.lia; f_equal; Lia.lia). pose proof (Z.pow_pos_nonneg 2 (ek - 1)). Lia.lia. }
    assert (POTSPLIT : fst (PEC.pot_estack L ek) = fst (PM.cost1 L (PEC.ESZ * PEC.ecap (ek + 1))) + fst (PEC.pot_estack L (ek + 1))
                    /\ snd (PEC.pot_estack L ek) = snd (PM.cost1 L (PEC.ESZ * PEC.ecap (ek + 1))) + snd (PEC.pot_estack L (ek + 1))).
    { rewrite NCE. unfold PEC.pot_estack, PM.cost1, PEC.ESZ. cbn [fst snd]. rewrite Z.pow_add_r, Z.pow_1_r by lia. clear. Lia.lia. }
    set (SZ := 24 * PEC.ecap ek). set (NC := PEC.ecap (ek + 1)) in *.
    rewrite FULLEQ in EV32. fold SZ in EV32.
    assert (EBB : 0 <= eb /\ eb + SZ <= hl_sptop L - 2 ^ 23).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [rewrite (EKB Z0); unfold SZ; rewrite Z0; cbn; clear - STOP; Lia.lia|]. destruct (EBND ltac:(lia)) as (B0 & B4 & _). unfold SZ. clear - B0 B4. Lia.lia. }

    pose proof (PESENBP.encBAn_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => eb + SZ | 36%nat => edepth | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
    fold SZ in EV40.
    PMK.feed P1 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov]) | assumption | PMK.rk | PMK.gmem | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 EDR EBB; Lia.lia) | PMK.sc ]).
    assert (POSTN : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x36058) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x360ac) M1 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBAn -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
      /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 80)
      /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
      /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (eb + SZ)
      /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (eb + SZ)
      /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth + 1)
      /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
      /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
      /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
      /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by post_of P1.
    clear P1.
    PMK.pvz_hg ltac:(idtac; destruct POSTN as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X2_1 & X8_1 & X11_1 & X18_1 & C48 & S40 & S32 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1.
    set (P1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36058 R1 0x360ac M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
    assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
    assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    pose proof (L5C.stk_writable RSEGS _ M1 sp 20480 STK1) as WR1.
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PEEK.enc_depth RSEGS EE L M M1 (fb + 440) fb eb ek _ edepth (edepth + 1) EA); [lia|lia| intros EKP; destruct (EBND EKP) as (B0 & B4 & _); unfold PEC.ESZ; clear - B0 B4 STOP; Lia.lia| | | exact MG1| exact C48| unfold MAX_DEPTH; lia].
      - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
      - intros EKP i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1. unfold PEC.ESZ in Ri. destruct (EBND EKP) as (B0 & B4 & _). clear - Ri B4 SLO F1 SHI STOP. Lia.lia. }
    pose proof EA1 as (_ & _ & _ & EV24a & _ & _ & _ & EDEF1 & _). cbn [PEC.en_b] in EV24a.
    assert (WRov1 : L5.writable RSEGS M1 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF1|lia|lia]).
    assert (EKT1 : PMK.ek L LBc0 sp 20480 W1 M M1) by (apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx| intros a O; exact O]).
    destruct (KEEPF W1 M1 EKT1) as (_ & _ & _ & BASE1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
    pose proof BASE1 as (IMG1 & _). cbn [pa_rw_lo CAD PeCLayoutS.CADDR_S] in IMG1.
    pose proof (bv_unsigned_in_range 64 (getr R1 (PMK.reg 10))) as RBj1. change (bv_modulus 64) with (2 ^ 64) in RBj1.

    assert (POSTG : exists fx2 R2 M2, mem_grows M1 M2
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 8) -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 0x360ac) M1 (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x37294) M2 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBAg0 -> getr R2 (PMK.reg x) = getr R1 (PMK.reg x))
      /\ getr R2 (PMK.reg 1) = Z_to_bv 64 221456
      /\ getr R2 (PMK.reg 9) = Z_to_bv 64 SZ
      /\ getr R2 (PMK.reg 10) = Z_to_bv 64 (fb + 440 + 24)
      /\ getr R2 (PMK.reg 11) = Z_to_bv 64 NC
      /\ L5.u64_at RSEGS M2 (sp - 48) (fb + 440 + 24)).
    { subst SZ NC.
      assert (EKC : ek = 0 \/ ek = 1 \/ ek = 2 \/ ek = 3 \/ ek = 4 \/ ek = 5 \/ ek = 6 \/ ek = 7 \/ ek = 8 \/ ek = 9 \/ ek = 10 \/ ek = 11) by lia.
      destruct EKC as [EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|EKv]]]]]]]]]]]; rewrite EKv in FULLEQ, X11_1, X18_1 |- *; cbn [PEC.ecap Z.eqb Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub Z.add Z.pos_sub Pos.add] in FULLEQ, X11_1, X18_1 |- *.
      - rewrite (EKB EKv) in X11_1, X18_1, EV24a. cbn [Z.add] in X11_1, X18_1.
        assert (EBAL8 : True) by exact I. assert (EB0 : True) by exact I. assert (EB4 : True) by exact I.
        pose proof (PESENBP.encBAg0_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg1_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg2_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg3_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg4_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg5_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg6_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg7_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg8_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg9_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg10_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBAg11_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2. }
    PMK.pvz_hg ltac:(idtac; destruct POSTG as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG2 & FRZ2 & MS2 & KS2 & G1 & G9 & G10 & G11 & C48s)); PMK.pvz_clrT.
    set (P2 := fun a => (sp - 48 <= a < sp - 48 + 8)).
    assert (FRZ2' : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ2; [exact Ha| exact N]).
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model fx1 fx2 R1 0x360ac R2 0x37294 M2 P2 K HH1 Mh Ml ltac:(lia) MS2 MG2 FRZ2').
    { intros a Pa. apply (PMK.cwr_stack L LB M1 sp 20480 a STK1). unfold P2 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P2. apply PMK.rng_dec. }
    intros HH2.
    assert (EK2 : PMK.ek L LB sp 20480 [] M1 M2).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [] M1 M2 P2 FRZ2' STK1 (PMFR.brange_hi L LB BR)). intros a Pa. left. unfold P2 in Pa. lia. }
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by exact (PMK.stk_grows L M1 M2 sp 20480 MG2 STK1).
    assert (STKc2 : L5C.stk (hl_sptop L) M2 (sp - 80) 14336).
    { apply (PMK.stk_call L M2 sp 20480 (sp - 80) 14336 STK2); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
    assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LB sp 20480 [] M1 M2 EK2 STK1 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact EINC| exact EA1]. }
    assert (EKT2 : PMK.ek L LBc0 sp 20480 W1 M M2).
    { apply (PMK.ek_trans L LBc0 sp 20480 W1 M M1 M2 EKT1). apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 [] M1 M2 EK2); [exact INC0| intros x Hx; exact Hx| intros a _ r0 Hr0; destruct Hr0]. }
    destruct (KEEPF W1 M2 EKT2) as (_ & _ & _ & BASE2 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
    assert (SV2 : forall a v, sp - 40 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
    { intros a v Ha Ha' U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2'; [lia| unfold P2; lia]|lia|lia| exact U]. }
    assert (ECAP10 : PEC.ecap ek <= 1024).
    { clear - EK EK10. unfold PEC.ecap. destruct (ek =? 0); [Lia.lia|]. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; Lia.lia. }
    assert (ALSZ : SZ mod 8 = 0) by (unfold SZ; replace (24 * PEC.ecap ek) with (3 * PEC.ecap ek * 8) by (clear; Lia.lia); apply Z.mod_mul; clear; Lia.lia).
    pose proof (PESK.sink_pot_nonneg RSEGS L PMSP.T3 PMSP.T4 P M (fb + 496) k PO SKA) as SPN. pose proof (PESK.sink_pot_fst PMSP.T3 PMSP.T4 P (PESK.sk_c k)) as SPF.

    pose proof EVA as EVX. unfold PECSS.evec_alloc_spec, PECS.evec_alloc_spec in EVX. cbn [pe_evec_alloc PECSS.EE PeCLayoutS.EADDR_S] in EVX.
    apply (EVX fx2 R2 M2 model K LB cr NC (sp - 80) 221456 HH2 MOK K0); clear EVX.
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact G1|]. split; [clear; unfold L5.ra_ok; Lia.lia|].
      split; [rewrite (KS2 2%nat) by PMK.inl; exact X2_1|].
      split; [rewrite (KS2 3%nat) by PMK.inl; rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS2 4%nat) by PMK.inl; rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc2. }
    { rewrite L5K.rl11. exact G11. }
    { clear - NCB. unfold NC in *. Lia.lia. }
    { exact BASE2. }
    { pose proof (PEN (ek + 1) ltac:(lia)) as PE1. unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRED |- *. change (PEC.en_k en) with ek in CRED.
      cbn [fst snd] in CRED |- *. clear - CRED POTSPLIT PE1 SPN SPF. Lia.lia. }
    intros fx3 R3 M3 model3 cr3 B RP3 R3_10 R3_11 FB HP3 CK3 MB3 HH3.
    rewrite L5K.rl10 in R3_10. rewrite L5K.rl11 in R3_11. change (PMSP.pm_scr 1) with 14336 in HP3.
    pose proof (L5C.fresh_block_bounds L LB M3 B _ FB) as (FB0 & FB1 & FB16 & FBn & FB4). unfold hl_ceil in FB4. unfold PEC.ESZ in FB1, FBn, FB4.
    destruct FB as (FBR & FBA & FBD). unfold PEC.ESZ in FBD.
    pose proof (PMFR.model_ok_but_vm model model3 MOK MB3) as MOK3. pose proof MOK3 as (Mh3 & Ml3 & Mm3).
    assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M2 M3 sp 20480 (sp - 80) 14336 _ STK2 HP3); lia).
    pose proof (L5C.stk_writable RSEGS _ M3 sp 20480 STK3) as WR3.
    pose proof (PMK.ek_of_hpres L LB (sp - 80) 14336 [] M2 M3 HP3) as EK3.
    assert (WHI3 : forall a, PMK.inW [] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
    assert (SC3 : 0 <= 14336) by lia.
    assert (EA3 : enc_at M3 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LB (sp - 80) 14336 [] M2 M3 EK3 STKc2 SC3 BR WHI3); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact EINC| exact EA2]. }
    assert (SKA3 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M3 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB (sp - 80) 14336 [] M2 M3 EK3 STKc2 SC3 BR WHI3); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 [] M1 M2 EK2 STK1 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i Hi; apply NW1; lia| exact KINC| exact SKA]. }
    assert (SV3 : forall a v, sp - 40 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Ha' U. apply (PMFR.u64_keep RSEGS L KL LB (sp - 80) 14336 [] M2 M3 EK3 STKc2 SC3); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)|]. exact (SV2 a v Ha Ha' U). }
    pose proof (SV3 (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S40) as S40c. pose proof (SV3 (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S32) as S32c.
    pose proof (SV3 (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S24) as S24c. pose proof (SV3 (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S16) as S16c.
    pose proof (SV3 (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S8) as S8c.
    pose proof EA3 as (_ & _ & _ & EV24c & EV32c & EV40c & EV48c & EDEF3 & _ & _ & _ & _ & _ & EBLK3 & EIT3).
    cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24c, EV32c, EV40c, EV48c, EBLK3, EIT3. unfold PEC.ESZ in EV32c, EV40c. fold n in EV32c. rewrite FULLEQ in EV32c. fold SZ in EV32c, EV40c.
    assert (WRov3 : L5.writable RSEGS M3 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF3|lia|lia]).
    assert (SZB : 0 <= SZ /\ SZ + 24 <= 24 * NC /\ SZ <= 24576) by (unfold SZ, NC; clear - CN CAPGROW ECAP10; Lia.lia).
    assert (WRBS : L5.writable RSEGS M3 (B + SZ) 24) by (apply (L5.writable_sub _ M3 B (24 * NC)); [apply (L5C.writable_of_defined RSEGS); [exact FBD|lia|lia]|lia|lia]).
    assert (ALB : B mod 8 = 0) by (apply PMPK.m16_8; exact FB16).

    pose proof (PESENBP.encBAh_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 37%nat => B | 38%nat => NC | 40%nat => SZ | _ => 0 end)) as P4. cbn beta iota in P4.
    PMK.feed P4 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact ALSZ | exact ALB]) | assumption | PMK.rk | PMK.gmem
                           | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 EBB FB0 FB4 SZB NCB; Lia.lia) | PMK.sc ]).
    assert (POSTH : exists fx4 R4 M4, mem_grows M3 M4
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (B + SZ + 0 <= i < B + SZ + 0 + 24) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 0x36110) M3 (seg_rom RSEGS)) (@mkst fx4 R4 (Z_to_bv 64 0xac48c) M4 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBAh -> getr R4 (PMK.reg x) = getr R3 (PMK.reg x))
      /\ getr R4 (PMK.reg 1) = Z_to_bv 64 221528
      /\ getr R4 (PMK.reg 9) = Z_to_bv 64 B
      /\ getr R4 (PMK.reg 11) = Z_to_bv 64 eb
      /\ getr R4 (PMK.reg 12) = Z_to_bv 64 SZ
      /\ getr R4 (PMK.reg 18) = Z_to_bv 64 (B + SZ + 24)
      /\ getr R4 (PMK.reg 19) = Z_to_bv 64 (B + 24 * NC)
      /\ L5.u64_at RSEGS M4 (B + SZ + 16) 0
      /\ L5.u64_at RSEGS M4 (B + SZ + 8) 0
      /\ L5.u32_at RSEGS M4 (B + SZ) 3) by post_of P4.
    clear P4.
    PMK.pvz_hg ltac:(idtac; destruct POSTH as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG4 & FRZ4 & MS4 & KS4 & H1 & H9 & H11 & H12 & H18 & H19 & I16 & I8 & I0)); PMK.pvz_clrT.
    set (P4 := fun a => (B + SZ + 0 <= a < B + SZ + 0 + 24)).
    assert (FRZ4' : forall a, 0 <= a < 2 ^ 64 -> ~ P4 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ4; [exact Ha| exact N]).
    assert (BINB : In (B, 24 * NC) ((B, PEC.ESZ * NC) :: LB)) by (left; reflexivity).
    apply (PMK.spiece RSEGS L HI KL HIok ((B, PEC.ESZ * NC) :: LB) cr3 M3 model3 fx3 fx4 R3 0x36110 R4 0xac48c M4 P4 K HH3 Mh3 Ml3 ltac:(lia) MS4 MG4 FRZ4').
    { intros a Pa. apply (PMK.cwr_block L _ B (24 * NC) a BINB). unfold P4 in Pa. clear - Pa SZB. Lia.lia. }
    { intros a. unfold P4. apply PMK.rng_dec. }
    intros HH4.
    assert (EK4 : PMK.ek L LB sp 20480 [] M3 M4).
    { apply (PEEK.ek_piece_own RSEGS L HI KL HIok [(B, PEC.ESZ * NC)] LB cr3 M4 _ sp 20480 [] M3 M4 P4 B (24 * NC) HH4 ltac:(left; reflexivity) FRZ4' ltac:(unfold hl_ceil; lia) ltac:(lia)).
      intros a Pa. right. right. unfold P4 in Pa. clear - Pa SZB. Lia.lia. }
    assert (STK4 : L5C.stk (hl_sptop L) M4 sp 20480) by exact (PMK.stk_grows L M3 M4 sp 20480 MG4 STK3).

    assert (APART : B + 24 * NC <= eb \/ eb + SZ <= B).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [right; rewrite (EKB Z0); unfold SZ; rewrite Z0; cbn; clear - FB0; Lia.lia|].
      destruct (FBA _ (EINC _ (BINk ltac:(lia)))) as [X'|X']; cbn [fst snd] in X'; unfold PEC.ESZ in X'; unfold SZ, NC; [left| right]; exact X'. }
    assert (DEFsrc : L5.defined M4 eb SZ).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [unfold SZ; rewrite Z0; cbn; intros i Hi; exfalso; clear - Hi; Lia.lia|].
      destruct (EBLK3 ltac:(lia)) as (_ & D3 & _). unfold PEC.ESZ in D3. fold SZ in D3. exact (L5.defined_grows M3 M4 _ _ MG4 D3). }
    destruct (PECPY.copy_run_eq0 RSEGS 0xac48c Es0Sums.src0_copy_spec_memcpy fx4 R4 M4 B eb SZ 221528
               ltac:(rewrite (KS4 10%nat) by PMK.inl; exact R3_10) H11 H12 H1 ltac:(clear; unfold L5.ra_ok; Lia.lia)
               ltac:(clear - SZB; Lia.lia) ltac:(clear - FB0; Lia.lia) ltac:(clear - FB4 SZB STOP; Lia.lia) ltac:(clear - EBB; Lia.lia) ltac:(clear - EBB STOP; Lia.lia)
               ltac:(clear - APART SZB; Lia.lia)
               ltac:(apply (L5.writable_sub _ M4 B (24 * NC)); [apply (L5C.writable_of_defined RSEGS); [exact (L5.defined_grows M3 M4 _ _ MG4 FBD)|lia|lia]|lia|lia])
               DEFsrc) as (R5 & M5 & MS5 & MG5 & FRZ5 & DEF5 & CPY5 & KS5 & A10_5).
    set (P5 := fun a => (B <= a < B + SZ)).
    assert (FRZ5' : forall a, 0 <= a < 2 ^ 64 -> ~ P5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ5; [exact Ha| exact N]).
    apply (PMK.spiece RSEGS L HI KL HIok ((B, PEC.ESZ * NC) :: LB) cr3 M4 model3 fx4 fx4 R4 0xac48c R5 221528 M5 P5 K HH4 Mh3 Ml3 ltac:(lia) MS5 MG5 FRZ5').
    { intros a Pa. apply (PMK.cwr_block L _ B (24 * NC) a BINB). unfold P5 in Pa. clear - Pa SZB. Lia.lia. }
    { intros a. unfold P5. apply PMK.rng_dec. }
    intros HH5.
    assert (EK5 : PMK.ek L LB sp 20480 [] M4 M5).
    { apply (PEEK.ek_piece_own RSEGS L HI KL HIok [(B, PEC.ESZ * NC)] LB cr3 M5 _ sp 20480 [] M4 M5 P5 B (24 * NC) HH5 ltac:(left; reflexivity) FRZ5' ltac:(unfold hl_ceil; lia) ltac:(lia)).
      intros a Pa. right. right. unfold P5 in Pa. clear - Pa SZB. Lia.lia. }
    assert (STK5 : L5C.stk (hl_sptop L) M5 sp 20480) by exact (PMK.stk_grows L M4 M5 sp 20480 MG5 STK4).
    pose proof (L5C.stk_writable RSEGS _ M5 sp 20480 STK5) as WR5.
    assert (AG35 : forall i, 0 <= i < 2 ^ 64 -> sp - 20480 <= i -> M5 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
    { intros i Hi Ri. rewrite (FRZ5' i Hi) by (unfold P5; clear - Ri FB4 SZB SLO; Lia.lia). apply (FRZ4' i Hi). unfold P4. clear - Ri FB4 SZB SLO. Lia.lia. }
    assert (EV24e : L5.u64_at RSEGS M5 (fb + 440 + 24) eb) by (apply (L5C.u64_at_agree RSEGS M3 M5); [intros i Hi; apply AG35; lia|lia|lia| exact EV24c]).
    assert (EV40e : L5.u64_at RSEGS M5 (fb + 440 + 40) (eb + SZ)) by (apply (L5C.u64_at_agree RSEGS M3 M5); [intros i Hi; apply AG35; lia|lia|lia| exact EV40c]).
    assert (WRov5 : L5.writable RSEGS M5 (fb + 440) 56) by (apply (L5.writable_grows _ M3 M5); [exact (StoreOk.mem_grows_trans _ _ _ MG4 MG5)| exact WRov3]).
    pose proof (bv_unsigned_in_range 64 (getr R5 (PMK.reg 10))) as RBj5. change (bv_modulus 64) with (2 ^ 64) in RBj5.

    pose proof (PESENBP.encBAi_conc fx4 R5 M5 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 37%nat => B | 40%nat => SZ | 42%nat => B + SZ + 24
        | 43%nat => B + 24 * NC | 55%nat => bv_unsigned (getr R5 (PMK.reg 10)) | _ => 0 end)) as P6. cbn beta iota in P6.
    PMK.feed P6 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov]) | (rewrite PMPK.word_id; reflexivity) | assumption | PMK.rk | PMK.gmem
                           | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 EBB FB0 FB4 SZB NCB; Lia.lia) | PMK.sc ]).
    assert (POSTI : exists fx6 R6 M6, mem_grows M5 M6
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 32) -> ~ (fb + 440 + 24 <= i < fb + 440 + 24 + 24) -> M6 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx4 R5 (Z_to_bv 64 0x36158) M5 (seg_rom RSEGS)) (@mkst fx6 R6 (Z_to_bv 64 0x37228) M6 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBAi -> getr R6 (PMK.reg x) = getr R5 (PMK.reg x))
      /\ getr R6 (PMK.reg 1) = Z_to_bv 64 221572
      /\ getr R6 (PMK.reg 10) = Z_to_bv 64 (sp - 80)
      /\ getr R6 (PMK.reg 11) = Z_to_bv 64 (eb + SZ)
      /\ L5.u64_at RSEGS M6 (sp - 56) (eb + SZ)
      /\ L5.u64_at RSEGS M6 (sp - 64) eb
      /\ L5.u64_at RSEGS M6 (sp - 72) eb
      /\ L5.u64_at RSEGS M6 (sp - 80) eb
      /\ L5.u64_at RSEGS M6 (fb + 440 + 40) (B + 24 * NC)
      /\ L5.u64_at RSEGS M6 (fb + 440 + 32) (B + SZ + 24)
      /\ L5.u64_at RSEGS M6 (fb + 440 + 24) B) by post_of P6.
    clear P6.
    PMK.pvz_hg ltac:(idtac; destruct POSTI as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG6 & FRZ6 & MS6 & KS6 & J1 & J10 & J11 & Q24 & Q16 & Q8 & Q0 & F40 & F32 & F24)); PMK.pvz_clrT.
    set (P6 := fun a => (sp - 80 <= a < sp - 80 + 32) \/ (fb + 440 + 24 <= a < fb + 440 + 24 + 24)).
    assert (FRZ6' : forall a, 0 <= a < 2 ^ 64 -> ~ P6 a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ6; [exact Ha| |]; intros X'; apply N; unfold P6; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok ((B, PEC.ESZ * NC) :: LB) cr3 M5 model3 fx4 fx6 R5 0x36158 R6 0x37228 M6 P6 K HH5 Mh3 Ml3 ltac:(lia) MS6 MG6 FRZ6').
    { intros a [Pa|Pa]; apply (PMK.cwr_stack L _ M5 sp 20480 a STK5); clear - Pa SLO SHI F1 F2; Lia.lia. }
    { intros a. unfold P6. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH6.
    assert (EK6 : PMK.ek L LB sp 20480 [(fb + 440, 56)] M5 M6).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(fb + 440, 56)] M5 M6 P6 FRZ6' STK5 (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK6 : L5C.stk (hl_sptop L) M6 sp 20480) by exact (PMK.stk_grows L M5 M6 sp 20480 MG6 STK5).
    pose proof (StoreOk.mem_grows_trans _ _ _ MG4 (StoreOk.mem_grows_trans _ _ _ MG5 MG6)) as MG36.
    assert (AG36 : forall i, 0 <= i < 2 ^ 64 -> sp - 48 <= i -> (i < fb + 440 + 24 \/ fb + 440 + 48 <= i) -> M6 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
    { intros i Hi Ri Oi. rewrite (FRZ6' i Hi) by (unfold P6; clear - Ri Oi; Lia.lia). apply (AG35 i Hi). clear - Ri; Lia.lia. }
    assert (SV6 : forall a v, sp - 48 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS M6 a v).
    { intros a v Ha Ha' U. apply (L5C.u64_at_agree RSEGS M3 M6); [intros i Hi; apply AG36; clear - Hi Ha Ha' F1 F2 SLO SHI STOP; Lia.lia|lia|lia| exact U]. }
    pose proof (SV6 (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S40c) as S40d. pose proof (SV6 (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S32c) as S32d.
    pose proof (SV6 (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S24c) as S24d. pose proof (SV6 (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S16c) as S16d.
    pose proof (SV6 (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S8c) as S8d.

    assert (COPY36 : forall j, 0 <= j < SZ -> M6 (Z_to_bv 64 (B + j)) = M3 (Z_to_bv 64 (eb + j))).
    { intros j Hj. rewrite (FRZ6' (B + j)) by (first [clear - Hj FB0 FB4 SZB STOP; Lia.lia | unfold P6; clear - Hj FB0 FB4 SZB SLO F1; Lia.lia]).
      rewrite (CPY5 j Hj). apply FRZ4'; [clear - Hj EBB STOP; Lia.lia|]. unfold P4. clear - Hj APART SZB. Lia.lia. }
    assert (EA6 : enc_at M6 (fb + 440) fb (PEC.ENC B (ek + 1) (estk ++ [EI 3 0 0]) (edepth + 1))).
    { apply (PEEK.enc_grow RSEGS EE L M3 M6 (fb + 440) fb eb ek estk (edepth + 1) (edepth + 1) (EI 3 0 0) B EA3); [lia|lia| | exact MG36| exact EK10| exact F24| | | | unfold MAX_DEPTH; lia| | exact ALB| | | |].
      + intros i Hi Ri. apply AG36; [exact Hi| clear - Ri F1; Lia.lia| clear - Ri; Lia.lia].
      + unfold PEC.ESZ. fold n. rewrite FULLEQ. fold SZ. replace (B + 24 * (PEC.ecap ek + 1)) with (B + SZ + 24) by (unfold SZ; clear; Lia.lia). exact F32.
      + unfold PEC.ESZ. fold NC. exact F40.
      + apply (PMF.u32_at_agree RSEGS M3 M6); [intros i Hi; apply AG36; clear - Hi F1 F2 SLO SHI STOP; Lia.lia|lia|lia| exact EV48c].
      + fold n. rewrite FULLEQ. fold NC. clear - CAPGROW. unfold NC. Lia.lia.
      + unfold PEC.ESZ. fold NC. exact (L5.defined_grows M3 M6 _ _ MG36 FBD).
      + exact FBR.
      + intros i Hi. pose proof (EIT3 i Hi) as (T0 & T8 & T16). unfold PEC.ESZ in T0, T8, T16 |- *.
        assert (Hi24 : 24 * Z.of_nat i + 24 <= SZ) by (unfold SZ; rewrite <- FULLEQ; unfold n; clear - Hi; Lia.lia).
        destruct (EBLK3 ltac:(destruct (Z.eq_dec ek 0) as [Z0|NZ]; [exfalso; unfold SZ in Hi24; rewrite Z0 in Hi24; cbn in Hi24; clear - Hi24; Lia.lia| lia])) as (_ & D3 & _).
        unfold PEC.ESZ in D3. assert (D3' : L5.defined M3 eb SZ) by (unfold SZ; exact D3).
        split; [|split].
        * apply (PECPY.u32_copy RSEGS M3 M6 (eb + 24 * Z.of_nat i) (B + 24 * Z.of_nat i));
            [clear - EBB Hi24 SZB; Lia.lia| clear - EBB Hi24 SZB STOP; Lia.lia| clear - FB0 Hi24; Lia.lia| clear - FB4 Hi24 SZB STOP; Lia.lia
            | apply (L5.defined_sub M3 eb SZ); [exact D3'| clear - Hi24; Lia.lia| clear - Hi24; Lia.lia]
            | intros j Hj; replace (B + 24 * Z.of_nat i + j) with (B + (24 * Z.of_nat i + j)) by (clear; Lia.lia); replace (eb + 24 * Z.of_nat i + j) with (eb + (24 * Z.of_nat i + j)) by (clear; Lia.lia); apply COPY36; clear - Hj Hi24; Lia.lia
            | exact T0].
        * apply (PECPY.u64_copy RSEGS M3 M6 (eb + 24 * Z.of_nat i + 8) (B + 24 * Z.of_nat i + 8));
            [clear - EBB Hi24 SZB; Lia.lia| clear - EBB Hi24 SZB STOP; Lia.lia| clear - FB0 Hi24; Lia.lia| clear - FB4 Hi24 SZB STOP; Lia.lia
            | apply (L5.defined_sub M3 eb SZ); [exact D3'| clear - Hi24; Lia.lia| clear - Hi24; Lia.lia]
            | intros j Hj; replace (B + 24 * Z.of_nat i + 8 + j) with (B + (24 * Z.of_nat i + 8 + j)) by (clear; Lia.lia); replace (eb + 24 * Z.of_nat i + 8 + j) with (eb + (24 * Z.of_nat i + 8 + j)) by (clear; Lia.lia); apply COPY36; clear - Hj Hi24; Lia.lia
            | exact T8].
        * apply (PECPY.u64_copy RSEGS M3 M6 (eb + 24 * Z.of_nat i + 16) (B + 24 * Z.of_nat i + 16));
            [clear - EBB Hi24 SZB; Lia.lia| clear - EBB Hi24 SZB STOP; Lia.lia| clear - FB0 Hi24; Lia.lia| clear - FB4 Hi24 SZB STOP; Lia.lia
            | apply (L5.defined_sub M3 eb SZ); [exact D3'| clear - Hi24; Lia.lia| clear - Hi24; Lia.lia]
            | intros j Hj; replace (B + 24 * Z.of_nat i + 16 + j) with (B + (24 * Z.of_nat i + 16 + j)) by (clear; Lia.lia); replace (eb + 24 * Z.of_nat i + 16 + j) with (eb + (24 * Z.of_nat i + 16 + j)) by (clear; Lia.lia); apply COPY36; clear - Hj Hi24; Lia.lia
            | exact T16].
      + unfold PEC.eitem_at, PEC.ESZ. fold n. rewrite FULLEQ. fold SZ. cbn [ei_kind ei_len ei_cnt].
        assert (AG46 : forall i, 0 <= i < 2 ^ 64 -> B + SZ <= i < B + SZ + 24 -> M6 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i)).
        { intros i Hi Ri. rewrite (FRZ6' i Hi) by (unfold P6; clear - Ri FB4 SZB SLO F1; Lia.lia). apply (FRZ5' i Hi). unfold P5. clear - Ri; Lia.lia. }
        split; [apply (PMF.u32_at_agree RSEGS M4 M6); [intros i Hi; apply AG46; [clear - Hi FB0 FB4 SZB STOP; Lia.lia| clear - Hi; Lia.lia]| clear - FB0 SZB; Lia.lia| clear - FB4 SZB STOP; Lia.lia| exact I0]|].
        split; [apply (L5C.u64_at_agree RSEGS M4 M6); [intros i Hi; apply AG46; [clear - Hi FB0 FB4 SZB STOP; Lia.lia| clear - Hi; Lia.lia]| clear - FB0 SZB; Lia.lia| clear - FB4 SZB STOP; Lia.lia| exact I8]|].
        apply (L5C.u64_at_agree RSEGS M4 M6); [intros i Hi; apply AG46; [clear - Hi FB0 FB4 SZB STOP; Lia.lia| clear - Hi; Lia.lia]| clear - FB0 SZB; Lia.lia| clear - FB4 SZB STOP; Lia.lia| exact I16]. }
    set (en' := PEC.ENC B (ek + 1) (estk ++ [EI 3 0 0]) (edepth + 1)) in EA6.
    assert (EOWN' : PEC.enc_own en' = [(B, PEC.ESZ * NC)]).
    { unfold PEC.enc_own, en'. cbn [PEC.en_k PEC.en_b]. replace (ek + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold NC. reflexivity. }
    assert (EKT6 : PMK.ek L LBc0 sp 20480 Ws M M6).
    { apply (PMK.ek_trans L LBc0 sp 20480 Ws M M2 M6).
      { apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 Ws W1 M M2 EKT2); [apply incl_refl| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M2 M3 M6).
      { apply (PMK.ek_callee_in' RSEGS L KL LBc0 LB sp 20480 (sp - 80) 14336 Ws [] M2 M3 HP3 INC0); [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)| intros a I; destruct (PMFR.inW_nil a I)]. }
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M3 M4 M6); [apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws [] M3 M4 EK4); [exact INC0| intros x Hx; exact Hx| intros a _ r0 Hr0; destruct Hr0]|].
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M4 M5 M6); [apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws [] M4 M5 EK5); [exact INC0| intros x Hx; exact Hx| intros a _ r0 Hr0; destruct Hr0]|].
      apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws [(fb + 440, 56)] M5 M6 EK6); [exact INC0| intros x Hx; exact Hx|].
      intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin]. }
    assert (DKT6 : PMK.dk L LBc0 sp 20480 M M6).
    { apply (PMK.dk_trans L LBc0 sp 20480 M M2 M6 (PMK.dk_grows L LBc0 sp 20480 M M2 (StoreOk.mem_grows_trans _ _ _ MG1 MG2))).
      apply (PMK.dk_trans L LBc0 sp 20480 M2 M3 M6); [apply (PMK.dk_callee L LBc0 LB sp 20480 (sp - 80) 14336 _ M2 M3 HP3 INC0); lia|].
      apply (PMK.dk_grows L LBc0 sp 20480 M3 M6 MG36). }
    destruct (KEEPF Ws M6 EKT6) as (_ & _ & _ & BASE6 & _).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (SKA6 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M6 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB sp 20480 [(fb + 440, 56)] M5 M6 EK6 STK5 SC0 BR); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 [] M4 M5 EK5 STK4 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 [] M3 M4 EK4 STK3 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC| exact SKA3]. }
    assert (CR36 : PMSP.credit_le (PEC.pot_enc L P en' k) cr3 /\ PMSP.credit_keep cr cr3 (PEC.pot_enc L P en k) (PEC.pot_enc L P en' k)).
    { unfold PMSP.credit_le, PMSP.credit_keep, PEC.pot_enc, PEC.credit_add in CRED, CK3 |- *. unfold en'. change (PEC.en_k en) with ek in CRED |- *. cbn [fst snd PEC.en_k] in CRED, CK3 |- *.
      fold NC in POTSPLIT. unfold PMSP.cr0 in CK3. cbn [fst snd] in CK3. clear - CRED CK3 POTSPLIT SPN SPF. Lia.lia. }
    destruct CR36 as (CR3e & CK3e).

    assert (AFTER7 : forall (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (cr7 : credit),
      getr R7 (PMK.reg 2) = Z_to_bv 64 (sp - 80) -> getr R7 (PMK.reg 8) = Z_to_bv 64 (fb + 440) -> getr R7 (PMK.reg 18) = Z_to_bv 64 (B + SZ + 24) ->
      (forall x, In x CSL -> getr R7 (PMK.reg x) = getr R (PMK.reg x)) ->
      L5C.stk (hl_sptop L) M7 sp 20480 ->
      L5.u64_at RSEGS M7 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) -> L5.u64_at RSEGS M7 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
      L5.u64_at RSEGS M7 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M7 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
      L5.u64_at RSEGS M7 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) ->
      enc_at M7 (fb + 440) fb en' -> PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M7 (fb + 496) k ->
      PMK.ek L LBc0 sp 20480 Ws M M7 -> PMK.dk L LBc0 sp 20480 M M7 ->
      PMSP.model_ok model7 -> model_but_vm model model7 ->
      hi_heap HI (PEC.owned s en' k ++ LBX) cr7 M7 (m_vmmaps model7) ->
      PMSP.credit_le (PEC.pot_enc L P en' k) cr7 -> PMSP.credit_keep cr cr7 (PEC.pot_enc L P en k) (PEC.pot_enc L P en' k) ->
      srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 0x36184 M7 model7) K).
    { intros fx7 R7 M7 model7 cr7 Z2 Z8 Z18 ZCS STK7 U40 U32 U24 U16 U8 EA7 SKA7 EK7 DK7 MOK7 MB7 HH7 CR7 CK7.
      pose proof MOK7 as (Mh7 & Ml7 & Mm7).
      pose proof EA7 as (_ & EV8g & _ & _ & _ & _ & EV48g & EDEF7 & _). cbn [PEC.en_depth] in EV48g. cbn [PESK.o_sink pe_off_sink EE PeCLayoutS.EADDR_S] in EV8g.
      assert (WRov7 : L5.writable RSEGS M7 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF7|lia|lia]).
      pose proof (L5C.stk_writable RSEGS _ M7 sp 20480 STK7) as WR7.
      set (LB7 := PEC.owned s en' k ++ LBX) in HH7.
      assert (BR7 : PMFR.brange L LB7) by (apply (PMFR.brange_of_heap L HI HIok LB7 LB7 cr7 M7 _ HH7); apply incl_refl).
      assert (INC07 : incl LBc0 LB7) by (unfold LBc0, LB7, PEC.owned; insub).
      assert (KINC7 : incl (PESK.sink_own k) LB7) by (unfold LB7, PEC.owned; insub).
      pose proof (bv_unsigned_in_range 64 (getr R7 (PMK.reg 10))) as RBj7. change (bv_modulus 64) with (2 ^ 64) in RBj7.
      pose proof (PESENBP.encBAt_conc fx7 R7 M7 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 41%nat => fb + 496 | 42%nat => B + SZ + 24 | 55%nat => bv_unsigned (getr R7 (PMK.reg 10)) | _ => 0 end)) as P8.
      cbn beta iota in P8.
      PMK.feed P8 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact ALsk]) | (rewrite PMPK.word_id; reflexivity) | assumption | PMK.rk | PMK.gmem
                             | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 FB0 FB4 SZB NCB; Lia.lia) | PMK.sc ]).
      assert (POSTT : exists fx8 R8 M8, mem_grows M7 M8
        /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 1) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> M8 (Z_to_bv 64 i) = M7 (Z_to_bv 64 i))
        /\ msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 0x36184) M7 (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0x372d8) M8 (seg_rom RSEGS))
        /\ (forall x, In x PESENBP.KS_encBAt -> getr R8 (PMK.reg x) = getr R7 (PMK.reg x))
        /\ getr R8 (PMK.reg 1) = Z_to_bv 64 221596
        /\ getr R8 (PMK.reg 10) = Z_to_bv 64 (fb + 496)
        /\ getr R8 (PMK.reg 11) = Z_to_bv 64 (sp - 80)
        /\ L5.u64_at RSEGS M8 (fb + 440 + 32) (B + SZ + 24)) by post_of P8.
      clear P8.
      PMK.pvz_hg ltac:(idtac; destruct POSTT as (fx8 & R8 & M8 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG8 & FRZ8 & MS8 & KS8 & T1 & T10 & T11 & C32t)); PMK.pvz_clrT.
      set (P8 := fun a => (sp - 80 <= a < sp - 80 + 1) \/ (fb + 440 + 32 <= a < fb + 440 + 32 + 8)).
      assert (FRZ8' : forall a, 0 <= a < 2 ^ 64 -> ~ P8 a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ8; [exact Ha| |]; intros X'; apply N; unfold P8; [left| right]; exact X'. }
      apply (PMK.spiece RSEGS L HI KL HIok LB7 cr7 M7 model7 fx7 fx8 R7 0x36184 R8 0x372d8 M8 P8 K HH7 Mh7 Ml7 ltac:(lia) MS8 MG8 FRZ8').
      { intros a [Pa|Pa]; apply (PMK.cwr_stack L LB7 M7 sp 20480 a STK7); clear - Pa SLO SHI F1 F2; Lia.lia. }
      { intros a. unfold P8. apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH8.
      assert (EK8 : PMK.ek L LB7 sp 20480 [(fb + 440, 56)] M7 M8).
      { apply (PMK.ek_piece_in RSEGS L KL LB7 sp 20480 [(fb + 440, 56)] M7 M8 P8 FRZ8' STK7 (PMFR.brange_hi L LB7 BR7)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
      assert (STK8 : L5C.stk (hl_sptop L) M8 sp 20480) by exact (PMK.stk_grows L M7 M8 sp 20480 MG8 STK7).
      assert (SV8 : forall a v, sp - 48 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M7 a v -> L5.u64_at RSEGS M8 a v).
      { intros a v Ha Ha' U. apply (L5C.u64_at_agree RSEGS M7 M8); [intros i Hi; apply FRZ8'; [clear - Hi Ha Ha' F1 SLO SHI STOP; Lia.lia| unfold P8; clear - Hi Ha Ha' F1; Lia.lia]|lia|lia| exact U]. }
      assert (EA8 : enc_at M8 (fb + 440) fb en').
      { unfold en'. apply (PEEK.enc_upd RSEGS EE L M7 M8 (fb + 440) fb B (ek + 1) _ (edepth + 1) (edepth + 1)); [exact EA7|lia|lia| intros _; unfold PEC.ESZ; fold NC; clear - FB0 FB4 STOP; Lia.lia| | | exact MG8| | | unfold MAX_DEPTH; lia].
        - intros i Hi Ri N1 N2. apply FRZ8'; [exact Hi|]. unfold P8. clear - Ri N1 F1. Lia.lia.
        - intros _ i Hi Ri. apply FRZ8'; [exact Hi|]. unfold P8. unfold PEC.ESZ in Ri. fold NC in Ri. clear - Ri FB4 SLO F1. Lia.lia.
        - rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. unfold PEC.ESZ. fold n. rewrite FULLEQ.
          match goal with |- L5.u64_at _ _ _ ?v => replace v with (B + SZ + 24) by (unfold SZ; clear; Lia.lia) end. exact C32t.
        - apply (PMF.u32_at_agree RSEGS M7 M8); [intros i Hi; apply FRZ8'; [clear - Hi F1 F2 SLO SHI STOP; Lia.lia| unfold P8; clear - Hi F1; Lia.lia]|lia|lia| exact EV48g]. }
      assert (SKA8 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M8 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LB7 sp 20480 [(fb + 440, 56)] M7 M8 EK8 STK7 SC0 BR7); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact KINC7| exact SKA7]. }
      apply (TAIL fx8 R8 M8 model7 cr7 B (ek + 1) T1).
      + rewrite (KS8 2%nat) by PMK.inl. exact Z2.
      + rewrite (KS8 8%nat) by PMK.inl. exact Z8.
      + exact T10. + exact T11.
      + intros x Hx. rewrite (KS8 x) by exact (PEEK.sub_in PESENBP.KS_encBAt CSL ltac:(vm_compute; reflexivity) x Hx). apply ZCS. exact Hx.
      + exact STK8.
      + exact (SV8 (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U40). + exact (SV8 (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U32).
      + exact (SV8 (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U24). + exact (SV8 (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U16).
      + exact (SV8 (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U8).
      + exact EA8. + exact SKA8.
      + apply (PMK.ek_trans L LBc0 sp 20480 Ws M M7 M8 EK7). apply (PMK.ek_weaken L LBc0 LB7 sp 20480 sp 20480 Ws [(fb + 440, 56)] M7 M8 EK8); [exact INC07| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin].
      + apply (PMK.dk_trans L LBc0 sp 20480 M M7 M8 DK7). apply (PMK.dk_grows L LBc0 sp 20480 M7 M8 MG8).
      + exact MOK7. + exact MB7. + exact HH8. + exact CR7. + exact CK7. }

    pose proof EVD as EVY. unfold PECSS.evec_sbdtor_spec, PECS.evec_sbdtor_spec in EVY. cbn [pe_evec_sbdtor PECSS.EE PeCLayoutS.EADDR_S] in EVY.
    assert (ENT6 : PMSP.entry CAD L R6 M6 (sp - 80) 221572 1).
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact J1|]. split; [clear; unfold L5.ra_ok; Lia.lia|].
      split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|].
      apply (PMK.stk_call L M6 sp 20480 (sp - 80) 14336 STK6); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (DQ6 : L5.defined M6 (sp - 80) 32) by (destruct STK6 as (_ & _ & _ & _ & D6); apply (L5.defined_sub M6 (sp - 20480) 20480 (sp - 80) 32 D6); lia).
    assert (ALq : (sp - 80) mod 8 = 0) by (apply PMPK.m16_8; replace (sp - 80) with (sp + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact A16).
    rewrite L5K.rl10 in EVY.
    destruct (Z.eq_dec ek 0) as [EK0|EKP].
    +
      pose proof (EKB EK0) as EB0.
      apply (EVY fx6 R6 M6 model3 K ((B, PEC.ESZ * NC) :: LB) cr3 (sp - 80) eb eb SZ (sp - 80) 221572 HH6 MOK3 K0 ENT6 J10 ltac:(lia) ltac:(lia) ALq DQ6 Q0 ltac:(replace (sp - 80 + 8) with (sp - 72) by (clear; Lia.lia); exact Q8) ltac:(replace (sp - 80 + 16) with (sp - 64) by (clear; Lia.lia); exact Q16) ltac:(replace (sp - 80 + 24) with (sp - 56) by (clear; Lia.lia); exact Q24) ltac:(left; exact EB0) BASE6); clear EVY.
      intros fx7 R7 M7 model7 cr7 RP7 HP7 CR7 MB7 HH7.
      rewrite EB0 in HP7, HH7. cbn [Z.eqb] in HP7, HH7. change (PMSP.pm_scr 1) with 14336 in HP7.
      pose proof (PMFR.model_ok_but_vm model3 model7 MOK3 MB7) as MOK7.
      assert (BRL : PMFR.brange L ((B, PEC.ESZ * NC) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr3 M6 _ HH6); apply incl_refl).
      pose proof (PMK.ek_of_hpres L _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 HP7) as EK7.
      assert (STKc6 : L5C.stk (hl_sptop L) M6 (sp - 80) 14336) by (destruct ENT6 as (_ & _ & _ & _ & _ & X'); exact X').
      assert (WHI7 : forall a, PMK.inW [(sp - 80, 32)] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (INCL6 : incl LB ((B, PEC.ESZ * NC) :: LB)) by (intros x Hx; right; exact Hx).
      apply (AFTER7 fx7 R7 M7 model7 cr7).
      * PMK.rk. * PMK.rk. * PMK.rk.
      * intros x Hx. assert (Hc : In x PMK.cs_all) by exact (PEEK.sub_in PMK.cs_all CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R6 R7 x RP7 Hc). rewrite (KS6 x) by exact (PEEK.sub_in PESENBP.KS_encBAi CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (KS5 x) by exact (PEEK.sub_in L5K.CS CSL ltac:(vm_compute; reflexivity) x Hx). rewrite (KS4 x) by exact (PEEK.sub_in PESENBP.KS_encBAh CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R2 R3 x RP3 Hc). rewrite (KS2 x) by exact (PEEK.sub_in PESENBP.KS_encBAg0 CSL ltac:(vm_compute; reflexivity) x Hx).
        apply KS1. exact (PEEK.sub_in PESENBP.KS_encBAn CSL ltac:(vm_compute; reflexivity) x Hx).
      * apply (PMK.stk_after RSEGS L KL _ M6 M7 sp 20480 (sp - 80) 14336 _ STK6 HP7); lia.
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S40d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S32d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S24d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S16d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S8d].
      * apply (PECF.enc_keep RSEGS EE L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| rewrite EOWN'; intros x [<-|[]]; left; reflexivity| exact EA6].
      * apply (PECF.sink_keep RSEGS L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| intros x Hx; right; exact (KINC x Hx)| exact SKA6].
      * apply (PMK.ek_trans L LBc0 sp 20480 Ws M M6 M7 EKT6).
        apply (PMK.ek_callee_in' RSEGS L KL LBc0 _ sp 20480 (sp - 80) 14336 Ws [(sp - 80, 32)] M6 M7 HP7); [intros x Hx; right; exact (INC0 x Hx)|lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)| intros a I; apply PMFR.inW_inv1 in I; left; lia].
      * apply (PMK.dk_trans L LBc0 sp 20480 M M6 M7 DKT6). apply (PMK.dk_callee L LBc0 _ sp 20480 (sp - 80) 14336 _ M6 M7 HP7); [intros x Hx; right; exact (INC0 x Hx)|lia|lia].
      * exact MOK7. * exact (L5C.model_but_vm_trans _ _ _ MB3 MB7).
      * refine (PEEK.heap_perm L HI HIok _ _ cr7 M7 _ _ HH7). unfold PEC.owned, LB. rewrite EOWN'. unfold PEC.owned.
        replace (PEC.enc_own en) with (@nil (Z * Z)) by (unfold PEC.enc_own, en; cbn [PEC.en_k]; rewrite EK0; reflexivity). cbn [app].
        rewrite <- !app_assoc. apply (Permutation_middle (PM.parser_own s) (PESK.sink_own k ++ LBX)).
      * unfold PMSP.credit_le in CR3e, CR7 |- *. clear - CR3e CR7. Lia.lia.
      * unfold PMSP.credit_keep, PMSP.credit_le in CK3e, CR7 |- *. clear - CK3e CR7. Lia.lia.
    +
      assert (EOWN : PEC.enc_own en = [(eb, PEC.ESZ * PEC.ecap ek)]).
      { unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      set (LBd := (eb, SZ) :: (B, PEC.ESZ * NC) :: PESK.sink_own k ++ PM.parser_own s ++ LBX).
      assert (PERMd : Permutation ((B, PEC.ESZ * NC) :: LB) LBd).
      { unfold LBd, LB, PEC.owned. rewrite EOWN. unfold PEC.ESZ at 2. fold SZ. rewrite <- !app_assoc. cbn [app].
        apply Permutation_sym. apply (Permutation_cons_app ((B, PEC.ESZ * NC) :: PM.parser_own s) (PESK.sink_own k ++ LBX)).
        cbn [app]. apply perm_skip. apply Permutation_app_swap_app. }
      pose proof (PEEK.heap_perm L HI HIok _ _ cr3 M6 _ PERMd HH6) as HH6d.
      destruct (EBND ltac:(lia)) as (B0 & B4 & _).
      apply (EVY fx6 R6 M6 model3 K LBd cr3 (sp - 80) eb eb SZ (sp - 80) 221572 HH6d MOK3 K0 ENT6 J10 ltac:(lia) ltac:(lia) ALq DQ6 Q0 ltac:(replace (sp - 80 + 8) with (sp - 72) by (clear; Lia.lia); exact Q8) ltac:(replace (sp - 80 + 16) with (sp - 64) by (clear; Lia.lia); exact Q16) ltac:(replace (sp - 80 + 24) with (sp - 56) by (clear; Lia.lia); exact Q24) ltac:(right; left; reflexivity) BASE6); clear EVY.
      intros fx7 R7 M7 model7 cr7 RP7 HP7 CR7 MB7 HH7.
      replace (eb =? 0) with false in HP7, HH7 by (symmetry; apply Z.eqb_neq; lia). unfold LBd in HP7, HH7. cbn [lb_remove fst] in HP7, HH7. rewrite Z.eqb_refl in HP7, HH7.
      change (PMSP.pm_scr 1) with 14336 in HP7.
      set (LB7 := (B, PEC.ESZ * NC) :: PESK.sink_own k ++ PM.parser_own s ++ LBX) in HP7, HH7.
      pose proof (PMFR.model_ok_but_vm model3 model7 MOK3 MB7) as MOK7.
      assert (BRL : PMFR.brange L LB7) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr7 M7 _ HH7); apply incl_refl).
      pose proof (PMK.ek_of_hpres L LB7 (sp - 80) 14336 [(sp - 80, 32)] M6 M7 HP7) as EK7.
      assert (STKc6 : L5C.stk (hl_sptop L) M6 (sp - 80) 14336) by (destruct ENT6 as (_ & _ & _ & _ & _ & X'); exact X').
      assert (WHI7 : forall a, PMK.inW [(sp - 80, 32)] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (INC7 : incl LBc0 LB7) by (unfold LBc0, LB7; intros x Hx; right; revert x Hx; insub).
      assert (KINC7 : incl (PESK.sink_own k) LB7) by (unfold LB7; intros x Hx; right; apply in_or_app; left; exact Hx).
      apply (AFTER7 fx7 R7 M7 model7 cr7).
      * PMK.rk. * PMK.rk. * PMK.rk.
      * intros x Hx. assert (Hc : In x PMK.cs_all) by exact (PEEK.sub_in PMK.cs_all CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R6 R7 x RP7 Hc). rewrite (KS6 x) by exact (PEEK.sub_in PESENBP.KS_encBAi CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (KS5 x) by exact (PEEK.sub_in L5K.CS CSL ltac:(vm_compute; reflexivity) x Hx). rewrite (KS4 x) by exact (PEEK.sub_in PESENBP.KS_encBAh CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R2 R3 x RP3 Hc). rewrite (KS2 x) by exact (PEEK.sub_in PESENBP.KS_encBAg0 CSL ltac:(vm_compute; reflexivity) x Hx).
        apply KS1. exact (PEEK.sub_in PESENBP.KS_encBAn CSL ltac:(vm_compute; reflexivity) x Hx).
      * apply (PMK.stk_after RSEGS L KL _ M6 M7 sp 20480 (sp - 80) 14336 _ STK6 HP7); lia.
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S40d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S32d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S24d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S16d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S8d].
      * apply (PECF.enc_keep RSEGS EE L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| rewrite EOWN'; intros x [<-|[]]; left; reflexivity| exact EA6].
      * apply (PECF.sink_keep RSEGS L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact KINC7| exact SKA6].
      * apply (PMK.ek_trans L LBc0 sp 20480 Ws M M6 M7 EKT6).
        apply (PMK.ek_callee_in' RSEGS L KL LBc0 _ sp 20480 (sp - 80) 14336 Ws [(sp - 80, 32)] M6 M7 HP7 INC7); [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)| intros a I; apply PMFR.inW_inv1 in I; left; lia].
      * apply (PMK.dk_trans L LBc0 sp 20480 M M6 M7 DKT6). apply (PMK.dk_callee L LBc0 _ sp 20480 (sp - 80) 14336 _ M6 M7 HP7 INC7); lia.
      * exact MOK7. * exact (L5C.model_but_vm_trans _ _ _ MB3 MB7).
      * refine (PEEK.heap_perm L HI HIok _ _ cr7 M7 _ _ HH7). unfold PEC.owned, LB7. rewrite EOWN'. rewrite <- !app_assoc. cbn [app].
        apply (Permutation_cons_app (PM.parser_own s) (PESK.sink_own k ++ LBX)). apply Permutation_app_swap_app.
      * unfold PMSP.credit_le in CR3e, CR7 |- *. clear - CR3e CR7. Lia.lia.
      * unfold PMSP.credit_keep, PMSP.credit_le in CK3e, CR7 |- *. clear - CK3e CR7. Lia.lia.
Qed.

Theorem v_begin_obj_ok :
  PESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P -> PECSS.make_ec_spec L HI -> PECSS.evec_alloc_spec L HI -> PECSS.evec_sbdtor_spec L HI ->
  PECSS.v_begin_obj_spec L HI P.
Proof.
  intros PB MKEC EVA EVD. unfold PECSS.v_begin_obj_spec, PECS.v_begin_obj_spec, PECS.eslot_spec.
  intros SPM [] fx R M model K LBX cr sp r fb cat p X s str sm en k e HH MOK K0 ENT FOK A10 A13 CPRE INCS POK MP NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK). destruct FOK as (F1 & F2 & F3). cbn [pa_frame CAD PeCLayoutS.CADDR_S] in F2.
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  unfold PECS.args_t3 in A13.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI).
  destruct MP as ((LOHI & XBAD & FA & EDR) & LENLE).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl13 in A13.
  unfold PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_ec, PMSP.o_v, PESK.o_sink in *.
  cbn [pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S] in *.
  change (PMSP.pm_scr 4) with 20480 in *.
  assert (SC0 : 0 <= 20480) by lia.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  pose proof (L5C.stk_writable RSEGS _ M sp 20480 STK) as WR.
  assert (PINC : incl (PM.parser_own s) LB) by (unfold LB, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (KINC : incl (PESK.sink_own k) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }

  destruct en as [eb ek estk edepth].
  pose proof EA as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & _ & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EK, ELEN, EDEP, EKB, EBLK, EITEMS.

  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [PEC.en_stk PEC.en_depth] in Lestk, Ledepth.
  set (n := Z.of_nat (length estk)).
  assert (HLENX : Z.of_nat (length (s_estk X)) = n) by (unfold n; rewrite Lestk, length_rev; reflexivity).
  rewrite HLENX in LENLE.
  pose proof (PEC.ecap_nonneg ek) as CN.
  assert (ECAPB : PEC.ecap ek <= 2048).
  { clear - EK. unfold PEC.ecap. destruct (ek =? 0); [Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. }
  assert (ALov : (fb + 440) mod 8 = 0) by (apply (PEEK.m8_of16 fb); [exact F3| reflexivity]).
  assert (ALsk : (fb + 496) mod 8 = 0) by (apply (PEEK.m8_of16 fb); [exact F3| reflexivity]).
  assert (ALec : (fb + 16) mod 8 = 0) by (apply (PEEK.m8_of16 fb); [exact F3| reflexivity]).
  assert (HO : bv_unsigned (getr R (PMK.reg 10)) = fb + 440) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HEC : bv_unsigned (getr R (PMK.reg 13)) = fb + 16) by (rewrite A13; apply L5.unsigned_lit; lia).
  unfold PEC.ESZ in EV32, EV40, ELEN. fold n in EV32.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as RB1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as RB8.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as RB9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as RB18.
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as RB19. change (bv_modulus 64) with (2 ^ 64) in RB1, RB8, RB9, RB18, RB19.
  unfold PMSP.cfg. cbn [pe_begin_obj EE PeCLayoutS.EADDR_S].
  pose proof (ly_img_lo L LY) as IMLO. pose proof (ly_img_hi L LY) as IMHI.

  set (LBc0 := PM.parser_own s ++ LBX).
  assert (BRc0 : PMFR.brange L LBc0) by (apply (PMFR.brange_incl L LBc0 LB BR); unfold LBc0, LB, PEC.owned; insub).
  assert (PINC0 : incl (PM.parser_own s) LBc0) by (unfold LBc0; apply incl_appl; apply incl_refl).
  assert (SINC0 : incl (PM.vs_own str) LBc0) by (unfold LBc0; apply incl_appr; exact INCS).
  set (WEC := fun a : Z => (fb + 440 <= a < fb + 520) \/ (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
  assert (KEEPF : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WEC a) ->
            PM.parser_at RSEGS CAD PMSP.T3 PMSP.T4 M' (fb + 48) (fb + 520) s /\ PM.iss_at RSEGS CAD PMSP.T3 M' (fb + 520) str sm
            /\ L5.u64_at RSEGS M' (fb + 48 + 384) (fb + 440) /\ PMST.base_ok RSEGS CAD M' /\ PEC.content_ok RSEGS CAD M' fb p (PM.p_src s) str sm).
  { intros W M' EKW WC.
    assert (WHI : forall a, PMK.inW W a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC in I; unfold WEC in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
    assert (NW : forall i, ~ WEC i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PMFR.parser_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact PINC0| exact PA]|].
    split; [apply (PMFR.iss_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact IA]|].
    split; [apply (PMFR.u64_keep RSEGS L KL LBc0 sp 20480 W M M' EKW STK SC0); [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact VREF]|].
    split; [apply (PMKP.base_ok_keep RSEGS CAD L KL SF LBc0 sp 20480 W M M' EKW); [| | | | exact BASE];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WEC;
            cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1; lia|].
    apply (PECF.content_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 BRc0 WHI fb p s str sm (fb + 48));
      unfold PMSP.o_is; cbn [pa_off_is CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WEC; lia| exact SINC0| exact PINC0| exact IA| exact PA| exact CONT]. }
  set (WOB := fun a : Z => (fb + 440 <= a < fb + 520)).
  assert (KEEPE : forall W M', PMK.ek L LBc0 sp 20480 W M M' -> (forall a, PMK.inW W a -> WOB a) ->
            PEST.err_ok RSEGS CAD EE M' e /\ PEC.ec_state RSEGS CAD M' fb (s_ec X) cat).
  { intros W M' EKW WC.
    assert (NW : forall i, ~ WOB i -> ~ PMK.inW W i) by (intros i Hi I; apply Hi; apply WC; exact I).
    split; [apply (PECKP.err_ok_keep RSEGS CAD EE L KL SF LBc0 sp 20480 W M M' EKW); [| | exact ERR];
            intros a Ha; apply PMFR.outside_of_not_inW; apply NW; unfold WOB;
            cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Ha; clear - Ha SLO STOP F1 IMLO IMHI; lia|].
    apply (PECF.ec_state_keep RSEGS CAD L KL LBc0 sp 20480 W M M' EKW STK SC0 fb (s_ec X) cat);
      unfold PMSP.o_ec; cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]; [lia|lia| intros i' Hi'; apply NW; unfold WOB; lia| exact ECS]. }
  assert (WCE : forall a, PMK.inW (PEC.W_enc CAD EE fb) a -> WEC a).
  { intros a (r0 & Hin & Hr). unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink in Hin.
    cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in Hin.
    unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; lia. }

  assert (KPM0 : 0 <= hl_k_per_malloc L) by (pose proof (ly_kpm L LY); lia).
  assert (BOV0 : 0 <= hl_b_overhead L) by (pose proof (ly_bov L LY); lia).
  assert (PEN : forall kk, 0 <= kk <= 12 -> 0 <= fst (PEC.pot_estack L kk) /\ 0 <= snd (PEC.pot_estack L kk)).
  { intros kk Hk. clear - KPM0 BOV0 Hk. unfold PEC.pot_estack, PEC.ESZ. cbn [fst snd]. assert (P2 : 2 ^ kk <= 2 ^ 12) by (apply Z.pow_le_mono_r; Lia.lia). split; Lia.nia. }
  assert (CREDk : PMSP.credit_le (PESK.sink_pot P (PESK.sk_c k)) cr).
  { pose proof (PEN ek EK) as PE. unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRED |- *. cbn [fst snd PEC.en_k] in CRED |- *. lia. }
  unfold MAX_DEPTH, MAX_ITEMS in EDR, EDEP, LENLE.
  assert (WRov : L5.writable RSEGS M (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF|lia|lia]).
  pose proof SKA as (_ & _ & _ & _ & _ & KZ & KCAP & KC0 & KBLK).
  set (en := PEC.ENC eb ek estk edepth) in *.
  assert (INC0 : incl LBc0 LB) by (unfold LBc0, LB, PEC.owned; insub).
  assert (BINk : 0 < ek -> In (eb, PEC.ESZ * PEC.ecap ek) (PEC.enc_own en)).
  { intros EKP. unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  assert (EBND : 0 < ek -> 4096 <= eb /\ eb + 24 * PEC.ecap ek <= hl_sptop L - 2 ^ 23 /\ (eb + 24 * PEC.ecap ek <= hl_img_lo L \/ hl_img_hi L <= eb)).
  { intros EKP. destruct (BR _ _ (EINC _ (BINk EKP))) as (B0 & B1 & B4). unfold hl_ceil in B4. unfold PEC.ESZ in B1, B4. split; [exact B0|]. split; [exact B4| exact B1]. }
  rewrite <- Ledepth in EDR.
  destruct (Z_lt_le_dec edepth 1024) as [DOK|DERR].
  2: {
    assert (ED : edepth = 1024) by lia.
    rewrite (e_begin_indef_err 1 X ltac:(unfold MAX_DEPTH; lia)) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB.
    pose proof (PESENBP.encBOe_conc fx R M (fun j => match j with 2%nat => sp | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
    rewrite ED in EV48.
    PMK.feed P1 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov]) | PMK.sc | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
    assert (POSTC : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35c24) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x36f18) M1 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBOe -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
      /\ getr R1 (PMK.reg 1) = Z_to_bv 64 220564
      /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 80)
      /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
      /\ getr R1 (PMK.reg 10) = getr R (PMK.reg 13)
      /\ getr R1 (PMK.reg 11) = Z_to_bv 64 11
      /\ L5.u32_at RSEGS M1 (fb + 440 + 48) 1025
      /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
      /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
      /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
      /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by post_of P1.
    clear P1.
    PMK.pvz_hg ltac:(idtac; destruct POSTC as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & C48 & S40 & S32 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1. rewrite A13 in X10_1.
    set (P1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35c24 R1 0x36f18 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
    assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
    assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    assert (STKc : L5C.stk (hl_sptop L) M1 (sp - 80) 14336).
    { apply (PMK.stk_call L M1 sp 20480 (sp - 80) 14336 STK1); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (EKT1 : PMK.ek L LBc0 sp 20480 W1 M M1) by (apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx| intros a O; exact O]).
    destruct (KEEPF W1 M1 EKT1) as (_ & _ & _ & BASE1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
    destruct (KEEPE W1 M1 EKT1) as (ERR1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WOB. lia. }
    assert (ECD : L5.defined M (fb + 16) 16).
    { unfold PEC.ec_state, PMSP.o_ec in ECS. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S] in ECS.
      destruct (s_ec X); [destruct ECS as (v0 & _ & (_ & _ & D0)); exact D0| destruct ECS as (_ & _ & D0); exact D0]. }
    assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i' Hi'; apply NW1; lia| exact KINC| exact SKA]. }
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PEEK.enc_depth RSEGS EE L M M1 (fb + 440) fb eb ek _ edepth (edepth + 1) EA); [lia|lia| intros EKP; destruct (EBND EKP) as (B0 & B4 & _); unfold PEC.ESZ; clear - B0 B4 STOP; Lia.lia| | | exact MG1| replace (edepth + 1) with 1025 by lia; exact C48| unfold MAX_DEPTH; lia].
      - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
      - intros EKP i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1. unfold PEC.ESZ in Ri. destruct (EBND EKP) as (B0 & B4 & _). clear - Ri B4 SLO F1 SHI STOP. Lia.lia. }

    pose proof MKEC as MKX. unfold PECSS.make_ec_spec, PECS.make_ec_spec in MKX. cbn [pa_make_ec PECSS.AD PeCLayoutS.CADDR_S] in MKX.
    apply (MKX fx1 R1 M1 model K LB cr (fb + 16) 11 (sp - 80) 220564 e HH1 MOK K0); clear MKX.
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1_1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact X2_1|].
      split; [rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc. }
    { rewrite L5K.rl10. exact X10_1. }
    { rewrite L5K.rl11. exact X11_1. }
    { clear; Lia.lia. } { lia. } { lia. } { exact ALec. }
    { exact (L5.defined_grows M M1 _ _ MG1 ECD). }
    { exact BASE1. }
    { exact ERR1. }
    intros fx2 R2 M2 RP2 EC2 ERR2 HP2 HH2.
    change (PMSP.pm_scr 1) with 14336 in HP2.
    set (W2 := (fb + 16, 16) :: (if e then [] else PMSP.err_W CAD)) in HP2.
    assert (WC2 : forall a, PMK.inW W2 a -> (fb + 16 <= a < fb + 16 + 16) \/ (0xc9640 <= a < 0xc9640 + 2) \/ (0xeb088 <= a < 0xeb088 + 544)).
    { intros a (r0 & Hin & Hr). unfold W2 in Hin. unfold L5.in_rng in Hr. destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|].
      destruct e; [destruct Hin|]. unfold PMSP.err_W in Hin. cbn [pa_errcat_guard pa_atexit CAD PeCLayoutS.CADDR_S] in Hin.
      destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    pose proof (PMK.stk_after RSEGS L KL LB M1 M2 sp 20480 (sp - 80) 14336 _ STK1 HP2 ltac:(lia) ltac:(lia) ltac:(lia)) as STK2.
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    pose proof (PMK.ek_of_hpres L LB (sp - 80) 14336 W2 M1 M2 HP2) as EK2.
    assert (SC2 : 0 <= 14336) by lia.
    assert (WHI2 : forall a, PMK.inW W2 a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply WC2 in I; rewrite IMLO, IMHI; clear - I F1; Lia.lia).
    assert (NW2 : forall i, (sp - 80 <= i < fb + 16 \/ fb + 16 + 16 <= i <= 2 ^ 64) -> ~ PMK.inW W2 i) by (intros i Hi I; apply WC2 in I; clear - Hi I IMLO IMHI F1 F2 STOP SLO; Lia.lia).
    assert (SV : forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
    { intros a v Ha Ha' U. apply (PMFR.u64_keep RSEGS L KL LB (sp - 80) 14336 _ M1 M2 EK2 STKc SC2); [lia|lia| intros i Hi; apply NW2; lia| exact U]. }
    pose proof (SV (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S40) as S40b. pose proof (SV (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S32) as S32b.
    pose proof (SV (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S24) as S24b. pose proof (SV (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S16) as S16b.
    pose proof (SV (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S8) as S8b.
    pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.

    pose proof (PESENBP.encBOr_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440
        | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
        | 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19))
        | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
    PMK.feed P3 ltac:(first [(unfold PESENBP.aligned; exact A16) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                           | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
    destruct P3 as (fx3 & R3 & M3 & _ & FRW3 & _ & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRW3). subst M3.
    apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 220564 R3 0x35d84 M2 K Mh Ml MS3).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M2 0x35d84 W_35d2c r F_35d2c eq_refl D_35d2c); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

    assert (EKT : PMK.ek L LBc0 sp 20480 (PEC.W_enc CAD EE fb) M M2).
    { apply (PMK.ek_trans L LBc0 sp 20480 _ M M1 M2).
      { apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 _ W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
        unfold PEC.W_enc, PMSP.o_v in O. cbn [pa_off_v CAD PeCLayoutS.CADDR_S app] in O.
        apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (PMK.ek_callee_in' RSEGS L KL LBc0 LB sp 20480 (sp - 80) 14336 _ W2 M1 M2 HP2 INC0);
        [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
      intros a I. apply WC2 in I. right. unfold PEC.W_enc, PMSP.err_W, PMSP.o_v, PMSP.o_ec, PESK.o_sink.
      cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app].
      destruct I as [I|[I|I]]; [do 2 apply PMK.inW_next; apply PMK.inW_here; lia| do 3 apply PMK.inW_next; apply PMK.inW_here; lia| do 4 apply PMK.inW_next; apply PMK.inW_here; lia]. }
    destruct (KEEPF _ M2 EKT WCE) as (PA2 & IA2 & VREF2 & BASE2 & CONT2).
    assert (SKA2 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M2 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB (sp - 80) 14336 W2 M1 M2 EK2 STKc SC2 (PMFR.brange_incl L LB LB BR ltac:(apply incl_refl)) WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact KINC| exact SKA1]. }
    assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LB (sp - 80) 14336 W2 M1 M2 EK2 STKc SC2 BR WHI2); [lia|lia| intros i Hi; apply NW2; lia| exact EINC| exact EA1]. }
    apply (KONT fx3 R3 M2 model (PEC.ENC eb ek estk (edepth + 1)) k true cr).
    - apply PMK.preserved_by_index. intros k0 Hk0.
      destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
      destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 18) as [->|N18]; [rewrite Y18; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 19) as [->|N19]; [rewrite Y19; apply PMPK.word_id|].
      assert (IN3 : In k0 PESENBP.KS_encBOr /\ In k0 PESENBP.KS_encBOe) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
      destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved R1 R2 k0 RP2 Hk0), (KS1 k0 I1). reflexivity.
    - unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
      split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|].
      split; [exact BASE2|]. split; [exact ERR2|]. split; [exact TBOK|]. split; [exact CONT2|].
      split.
      { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [exact Lestk|]. split; [lia|]. split; [exact Lz| exact Lbad]. }
      split; [| intros _; reflexivity].
      unfold PEC.ec_state, PMSP.o_ec. cbn [pa_off_ec CAD PeCLayoutS.CADDR_S]. exists 11. split; [clear; Lia.lia| exact EC2].
    - intros _; reflexivity.
    - apply (PMK.hpres_of L LBc0 sp 20480 _ M M2); [exact EKT| destruct STK2 as (_ & _ & _ & _ & D2); exact D2|].
      apply (PMK.dk_trans L LBc0 sp 20480 M M1 M2 (PMK.dk_grows L LBc0 sp 20480 M M1 MG1)).
      apply (PMK.dk_callee L LBc0 LB sp 20480 (sp - 80) 14336 _ M1 M2 HP2 INC0); lia.
    - unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add. change (PEC.en_k en) with ek. cbn [fst snd PEC.en_k]. clear. Lia.lia.
    - apply L5C.model_but_vm_refl.
    - change (PEC.enc_own (PEC.ENC eb ek estk (edepth + 1))) with (PEC.enc_own en). exact HH2. }

  rewrite (e_begin_indef_ok 1 X ltac:(unfold MAX_DEPTH; lia)) in NB, HB, KONT. cbn [s_bad s_hi] in NB, HB.

  set (Ws := [(fb + 440, 56); (fb + 496, 24)] : list L5.range).
  assert (TAIL : forall (fxq : FPState) (Rq : bvmap 5 word) (Mq : word -> option byte) (modelq : Model) (crq : credit) (eb' ek' : Z),
    let en' := PEC.ENC eb' ek' (estk ++ [EI 1 0 0]) (edepth + 1) in
    getr Rq (PMK.reg 1) = Z_to_bv 64 220520 -> getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 80) ->
    getr Rq (PMK.reg 8) = Z_to_bv 64 (fb + 440) -> getr Rq (PMK.reg 10) = Z_to_bv 64 (fb + 496) -> getr Rq (PMK.reg 11) = Z_to_bv 64 (sp - 80) ->
    (forall x, In x CSL -> getr Rq (PMK.reg x) = getr R (PMK.reg x)) ->
    L5C.stk (hl_sptop L) Mq sp 20480 ->
    L5.u64_at RSEGS Mq (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) -> L5.u64_at RSEGS Mq (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
    L5.u64_at RSEGS Mq (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS Mq (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
    L5.u64_at RSEGS Mq (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) ->
    enc_at Mq (fb + 440) fb en' -> PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P Mq (fb + 496) k ->
    PMK.ek L LBc0 sp 20480 Ws M Mq -> PMK.dk L LBc0 sp 20480 M Mq ->
    PMSP.model_ok modelq -> model_but_vm model modelq ->
    hi_heap HI (PEC.owned s en' k ++ LBX) crq Mq (m_vmmaps modelq) ->
    PMSP.credit_le (PEC.pot_enc L P en' k) crq -> PMSP.credit_keep cr crq (PEC.pot_enc L P en k) (PEC.pot_enc L P en' k) ->
    srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x372d8 Mq modelq) K).
  { intros fxq Rq Mq modelq crq eb' ek' en' Q1 Q2 Q8 Q10 Q11 QCS STKq T40 T32 T24 T16 T8 EAq SKAq EKq DKq MOKq MBq HHq CRq CKq.
    pose proof MOKq as (Mhq & Mlq & Mmq).
    pose proof EAq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EKq' & _). cbn [PEC.en_k] in EKq'.
    set (LBq := PEC.owned s en' k ++ LBX) in HHq.
    set (LBYq := PM.parser_own s ++ PEC.enc_own en' ++ LBX).
    assert (PERMq : Permutation LBq (PESK.sink_own k ++ LBYq)) by (unfold LBq, LBYq, PEC.owned; rewrite <- !app_assoc; apply PEEK.perm4).
    assert (XINCq : incl LBc0 LBYq) by (unfold LBc0, LBYq; insub).
    assert (EINCq : incl (PEC.enc_own en') LBYq) by (unfold LBYq; insub).
    assert (STKcq : L5C.stk (hl_sptop L) Mq (sp - 80) 12288).
    { apply (PMK.stk_call L Mq sp 20480 (sp - 80) 12288 STKq); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    pose proof PB as PBX. unfold PESK.push_back_spec in PBX. cbn [pe_push_back EE PeCLayoutS.EADDR_S] in PBX.
    apply (PBX SPM fxq Rq Mq modelq K LBYq crq (fb + 496) (sp - 80) (sp - 80) 220520 k); clear PBX.
    { apply (PEEK.heap_perm L HI HIok LBq); [exact PERMq| exact HHq]. }
    { exact MOKq. }
    { exact K0. }
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact Q1|]. split; [clear; unfold L5.ra_ok; Lia.lia|]. split; [exact Q2|].
      split; [rewrite (QCS 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (QCS 4%nat) by PMK.inl; exact Rtp|]. exact STKcq. }
    { rewrite L5K.rl10. exact Q10. }
    { rewrite L5K.rl11. exact Q11. }
    { exact SKAq. }
    { lia. } { lia. } { exact ALsk. } { lia. } { lia. } { left; lia. }
    { destruct STKq as (_ & _ & _ & _ & D1). apply (L5.defined_sub Mq (sp - 20480) 20480 (sp - 80) 1 D1); lia. }
    { intros ZC. apply (PESK.spo_next P PO (PESK.sk_c k) (s_hi X + 1) KCAP); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLK Hc))))))| exact HB| lia]. }
    { pose proof (PEN ek' EKq') as PE. unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRq |- *. unfold en' in CRq. cbn [fst snd PEC.en_k] in CRq |- *. clear - CRq PE. Lia.lia. }
    intros fx2 R2 M2 model2 cr2 b2 RP2 SKA2 HP2 CK2 MB2 HH2.
    change (PMSP.pm_scr 0) with 12288 in HP2. set (k2 := PESK.sk_push k b2) in *.
    pose proof (PMFR.model_ok_but_vm modelq model2 MOKq MB2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & Mm2).
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by (apply (PMK.stk_after RSEGS L KL LBYq Mq M2 sp 20480 (sp - 80) 12288 _ STKq HP2); lia).
    pose proof (L5C.stk_writable RSEGS _ M2 sp 20480 STK2) as WR2.
    pose proof (PMK.ek_of_hpres L LBYq (sp - 80) 12288 [(fb + 496, 24)] Mq M2 HP2) as EK2.
    assert (BRY2 : PMFR.brange L (PESK.sink_own k2 ++ LBYq)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr2 M2 _ HH2); apply incl_refl).
    assert (BRYq : PMFR.brange L LBYq) by (apply (PMFR.brange_incl L LBYq _ BRY2); apply incl_appr; apply incl_refl).
    assert (WHI2 : forall a, PMK.inW [(fb + 496, 24)] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (SC2 : 0 <= 12288) by lia.
    assert (SV : forall a v, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Mq a v -> L5.u64_at RSEGS M2 a v).
    { intros a v Ha Ha' U. apply (PMFR.u64_keep RSEGS L KL LBYq (sp - 80) 12288 _ Mq M2 EK2 STKcq SC2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact U]. }
    pose proof (SV (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T40) as T40b. pose proof (SV (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T32) as T32b.
    pose proof (SV (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T24) as T24b. pose proof (SV (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T16) as T16b.
    pose proof (SV (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) T8) as T8b.
    pose proof (bv_unsigned_in_range 64 (getr R2 (PMK.reg 10))) as RBj. change (bv_modulus 64) with (2 ^ 64) in RBj.

    pose proof (PESENBP.encBOu_conc fx2 R2 M2 (fun j => match j with 2%nat => sp | 10%nat => fb + 440
        | 44%nat => bv_unsigned (getr R (PMK.reg 1)) | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
        | 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19))
        | 55%nat => bv_unsigned (getr R2 (PMK.reg 10)) | _ => 0 end)) as P3. cbn beta iota in P3.
    PMK.feed P3 ltac:(first [(unfold PESENBP.aligned; exact A16) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                           | (clear - SLO STOP SHI F1 F2; unfold hl_ceil in *; lia) ]).
    destruct P3 as (fx3 & R3 & M3 & _ & FRW3 & _ & MS3 & KS3 & Y1 & Y2 & Y8 & Y9 & Y10 & Y18 & Y19).
    assert (EM : M3 = M2) by (apply functional_extensionality; exact FRW3). subst M3.
    apply (PMK.spiece_ro RSEGS model2 fx2 fx3 R2 220520 R3 0x35d84 M2 K Mh2 Ml2 MS3).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh2| exact Ml2| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M2 0x35d84 W_35d2c r F_35d2c eq_refl D_35d2c); [rewrite Y1, PMPK.word_id; exact Rra| lia| exact Hr2]. }

    assert (EKT : PMK.ek L LBc0 sp 20480 Ws M M2).
    { apply (PMK.ek_trans L LBc0 sp 20480 Ws M Mq M2 EKq).
      apply (PMK.ek_callee_in' RSEGS L KL LBc0 LBYq sp 20480 (sp - 80) 12288 Ws [(fb + 496, 24)] Mq M2 HP2 XINCq);
        [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)|].
      intros a I. apply PMFR.inW_inv1 in I. right. apply PMK.inW_next. apply PMK.inW_here. lia. }
    destruct (KEEPF Ws M2 EKT) as (PA2 & IA2 & VREF2 & BASE2 & CONT2).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    destruct (KEEPE Ws M2 EKT) as (ERR2 & ECS2).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WOB. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (EA2 : enc_at M2 (fb + 440) fb en').
    { apply (PECF.enc_keep RSEGS EE L KL LBYq (sp - 80) 12288 [(fb + 496, 24)] Mq M2 EK2 STKcq SC2 BRYq WHI2); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact EINCq| exact EAq]. }
    apply (KONT fx3 R3 M2 model2 en' k2 e cr2).
    - apply PMK.preserved_by_index. intros k0 Hk0.
      destruct (Nat.eq_dec k0 2) as [->|N2]; [rewrite Y2; symmetry; exact Rsp|].
      destruct (Nat.eq_dec k0 8) as [->|N8]; [rewrite Y8; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 9) as [->|N9]; [rewrite Y9; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 18) as [->|N18]; [rewrite Y18; apply PMPK.word_id|].
      destruct (Nat.eq_dec k0 19) as [->|N19]; [rewrite Y19; apply PMPK.word_id|].
      assert (IN3 : In k0 PESENBP.KS_encBOu /\ In k0 CSL) by (cbn in Hk0; decompose [or] Hk0; subst; try (exfalso; congruence); (split; PMK.inl)).
      destruct IN3 as [I3 I1]. rewrite (KS3 k0 I3), (PMK.cs_of_preserved Rq R2 k0 RP2 Hk0), (QCS k0 I1). reflexivity.
    - unfold PEC.crun_pre. unfold PMSP.o_p, PMSP.o_is, PMSP.o_v, PESK.o_sink. cbn [pa_off_p pa_off_is pa_off_v pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S].
      split; [exact PA2|]. split; [exact IA2|]. split; [exact EA2|]. split; [exact VREF2|]. split; [exact SKA2|].
      split; [exact BASE2|]. split; [exact ERR2|]. split; [exact TBOK|]. split; [exact CONT2|].
      split.
      { unfold PEC.clink, en'. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PEC.en_stk PEC.en_depth rev].
        split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|].
        split; [rewrite Lestk; reflexivity|]. split; [lia|]. split; [|exact Lbad].
        unfold k2, PESK.sk_push. destruct (PESK.sk_z k <? PESK.sk_c k); cbn [PESK.sk_z]; lia. }
      split; [exact ECS2| exact ECI].
    - intros X'; exact X'.
    - apply (PMK.hpres_of L LBc0 sp 20480 _ M M2).
      + apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 _ Ws M M2 EKT); [apply incl_refl| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold PEC.W_enc, PMSP.o_v, PMSP.o_ec, PESK.o_sink in O.
        cbn [pa_off_v pa_off_ec pe_off_sink CAD EE PeCLayoutS.CADDR_S PeCLayoutS.EADDR_S app] in O.
        unfold Ws in Hr0. destruct Hr0 as [<-|[<-|[]]]; [apply (O (fb + 440, 56)); [left; reflexivity| exact Hin] | apply (O (fb + 496, 24)); [right; left; reflexivity| exact Hin]].
      + destruct STK2 as (_ & _ & _ & _ & D2). exact D2.
      + apply (PMK.dk_trans L LBc0 sp 20480 M Mq M2 DKq).
        apply (PMK.dk_callee L LBc0 LBYq sp 20480 (sp - 80) 12288 _ Mq M2 HP2 XINCq); lia.
    - unfold PMSP.credit_keep, PEC.pot_enc, PEC.credit_add in CKq, CK2 |- *. unfold en' in CKq |- *. change (PEC.en_k en) with ek in CKq |- *.
      cbn [fst snd PEC.en_k] in CKq, CK2 |- *. clear - CKq CK2. Lia.lia.
    - exact (L5C.model_but_vm_trans _ _ _ MBq MB2).
    - refine (PEEK.heap_perm L HI HIok _ _ cr2 M2 _ _ HH2). unfold PEC.owned, LBYq. rewrite <- !app_assoc. apply Permutation_sym. apply PEEK.perm4. }
  unfold MAX_DEPTH in EV16.
  destruct (Z_lt_le_dec n (PEC.ecap ek)) as [ROOM|FULL].
  -
    assert (EKP : 0 < ek).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [|lia]. exfalso. unfold PEC.ecap in ROOM. rewrite Z0 in ROOM. cbn in ROOM. unfold n in ROOM. lia. }
    destruct (EBND EKP) as (B0 & B4 & B1). destruct (EBLK EKP) as (EBAL & EBDEF & EBR & _ & _). unfold PEC.ESZ in EBDEF.
    pose proof (EINC _ (BINk EKP)) as BIN.
    assert (ALend : (eb + 24 * n) mod 8 = 0) by (apply PEEK.al8_item; exact EBAL).
    assert (WRit : L5.writable RSEGS M (eb + 24 * n) 24).
    { apply (L5.writable_sub _ M eb (24 * PEC.ecap ek)); [apply (L5C.writable_of_defined RSEGS); [exact EBDEF|lia|lia]| unfold n; lia| lia]. }
    pose proof (PESENBP.encBOf_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => eb + 24 * n | 35%nat => eb + 24 * PEC.ecap ek | 36%nat => edepth | 41%nat => fb + 496 | _ => 0 end)) as P1.
    cbn beta iota in P1. rewrite !HO in P1.
    PMK.feed P1 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact ALsk | exact ALend]) | PMK.sc
                           | (clear - B0 B4 SLO STOP SHI F1 F2 ELEN ROOM CN ECAPB EDR; unfold hl_ceil, n in *; lia) ]).
    assert (POSTF : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) ->
            ~ (eb + 24 * n + 0 <= i < eb + 24 * n + 0 + 24) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35c24) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x372d8) M1 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBOf -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
      /\ getr R1 (PMK.reg 1) = Z_to_bv 64 220520
      /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 80)
      /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
      /\ getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 496)
      /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 80)
      /\ L5.u64_at RSEGS M1 (fb + 440 + 32) (eb + 24 * n + 24)
      /\ L5.u64_at RSEGS M1 (eb + 24 * n + 16) 0
      /\ L5.u64_at RSEGS M1 (eb + 24 * n + 8) 0
      /\ L5.u32_at RSEGS M1 (eb + 24 * n) 1
      /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth + 1)
      /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
      /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
      /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
      /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by post_of P1.
    clear P1.
    PMK.pvz_hg ltac:(idtac; destruct POSTF as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X1_1 & X2_1 & X8_1 & X10_1 & X11_1 & C32 & I16 & I8 & I0 & C48 & S40 & S32 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1.
    set (P1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4) \/ (fb + 440 + 32 <= a < fb + 440 + 32 + 8) \/ (eb + 24 * n + 0 <= a < eb + 24 * n + 0 + 24)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| | | |]; intros X'; apply N; unfold P1; [left| right; left| right; right; left| right; right; right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35c24 R1 0x372d8 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a [Pa|[Pa|[Pa|Pa]]]; [apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia
        | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia | apply (PMK.cwr_stack L LB M sp 20480 a STK); clear - Pa SLO SHI F1 F2; Lia.lia |].
      apply (PMK.cwr_block L _ eb (PEC.ESZ * PEC.ecap ek) a BIN). unfold PEC.ESZ. unfold n in ROOM. clear - Pa ROOM CN. Lia.lia. }
    { intros a. unfold P1. repeat (apply PMK.or_dec; [apply PMK.rng_dec|]). apply PMK.rng_dec. }
    intros HH1.
    set (LBcE := PESK.sink_own k ++ PM.parser_own s ++ LBX).
    assert (PERME : Permutation LB (PEC.enc_own en ++ LBcE)) by (unfold LB, LBcE, PEC.owned; rewrite <- !app_assoc; apply Permutation_sym; apply PEEK.perm4).
    pose proof (PEEK.heap_perm L HI HIok _ _ cr M1 _ PERME HH1) as HH1e.
    assert (BRE : PMFR.brange L LBcE) by (apply (PMFR.brange_of_heap L HI HIok _ LBcE cr M1 _ HH1e); apply incl_appr; apply incl_refl).
    set (WsE := [(fb + 440, 56)] : list L5.range).
    assert (EK1 : PMK.ek L LBcE sp 20480 WsE M M1).
    { apply (PEEK.ek_piece_own RSEGS L HI KL HIok (PEC.enc_own en) LBcE cr M1 _ sp 20480 WsE M M1 P1 eb (PEC.ESZ * PEC.ecap ek) HH1e (BINk EKP) FRZ1' ltac:(unfold hl_ceil; lia) ltac:(lia)).
      intros a [Pa|[Pa|[Pa|Pa]]]; [left; lia| right; left; apply PMK.inW_here; lia| right; left; apply PMK.inW_here; lia|].
      right. right. unfold PEC.ESZ. unfold n in ROOM. clear - Pa ROOM CN. Lia.lia. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    assert (SKA1 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M1 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LBcE sp 20480 WsE M M1 EK1 STK SC0 BRE); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| unfold LBcE; insub| exact SKA]. }
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek (estk ++ [EI 1 0 0]) (edepth + 1))).
    { apply (PEEK.enc_push RSEGS EE L M M1 (fb + 440) fb eb ek estk edepth (edepth + 1) (EI 1 0 0) EA); [lia|lia| intros _; unfold PEC.ESZ; clear - B0 B4 STOP; Lia.lia| | | exact MG1| | exact C48| unfold MAX_DEPTH; lia| fold n; lia|].
      + intros i Hi Ri N1 N2. apply FRZ1'; [exact Hi|]. unfold P1. intros [X'|[X'|[X'|X']]]; [clear - X' Ri F1; Lia.lia| apply N2; clear - X'; Lia.lia| apply N1; clear - X'; Lia.lia|].
        unfold n in ROOM. clear - X' Ri B4 ROOM CN SLO F1. Lia.lia.
      + intros _ i Hi Ri. unfold PEC.ESZ in Ri. fold n in Ri. apply FRZ1'; [exact Hi|]. unfold P1. intros [X'|[X'|[X'|X']]]; [clear - X' Ri B4 ROOM CN SLO| clear - X' Ri B4 ROOM CN SLO F1| clear - X' Ri B4 ROOM CN SLO F1| clear - X' Ri]; Lia.lia.
      + unfold PEC.ESZ. fold n. replace (eb + 24 * (n + 1)) with (eb + 24 * n + 24) by (clear; Lia.lia). exact C32.
      + unfold PEC.eitem_at, PEC.ESZ. fold n. cbn [ei_kind ei_len ei_cnt]. split; [exact I0|]. split; [exact I8| exact I16]. }
    apply (TAIL fx1 R1 M1 model cr eb ek X1_1 X2_1 X8_1 X10_1 X11_1).
    + intros x Hx. apply KS1. exact (PEEK.sub_in PESENBP.KS_encBOf CSL ltac:(vm_compute; reflexivity) x Hx).
    + exact STK1. + exact S40. + exact S32. + exact S24. + exact S16. + exact S8. + exact EA1. + exact SKA1.
    + apply (PMK.ek_weaken L LBc0 LBcE sp 20480 sp 20480 Ws WsE M M1 EK1); [unfold LBc0, LBcE; insub| intros x Hx; exact Hx|].
      intros a O r0 Hr0 Hin. unfold WsE in Hr0. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin].
    + apply (PMK.dk_grows L LBc0 sp 20480 M M1 MG1).
    + exact MOK. + apply L5C.model_but_vm_refl.
    + change (PEC.enc_own (PEC.ENC eb ek (estk ++ [EI 1 0 0]) (edepth + 1))) with (PEC.enc_own en). exact HH1.
    + change (PEC.pot_enc L P (PEC.ENC eb ek (estk ++ [EI 1 0 0]) (edepth + 1)) k) with (PEC.pot_enc L P en k). exact CRED.
    + change (PEC.pot_enc L P (PEC.ENC eb ek (estk ++ [EI 1 0 0]) (edepth + 1)) k) with (PEC.pot_enc L P en k). unfold PMSP.credit_keep. clear. Lia.lia.
  -
    assert (FULLEQ : n = PEC.ecap ek) by lia.
    assert (EK10 : ek <= 11).
    { destruct (Z.eq_dec ek 12) as [E11|NE]; [exfalso| lia]. rewrite E11 in FULLEQ. cbn in FULLEQ. lia. }
    assert (NCE : PEC.ecap (ek + 1) = 2 ^ ek).
    { unfold PEC.ecap. replace (ek + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal. lia. }
    assert (NCB : 1 <= PEC.ecap (ek + 1) <= 2048).
    { rewrite NCE. clear - EK EK10. pose proof (Z.pow_pos_nonneg 2 ek ltac:(Lia.lia) ltac:(Lia.lia)). split; [Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. }
    assert (CAPGROW : PEC.ecap ek + 1 <= PEC.ecap (ek + 1)).
    { rewrite NCE. clear - EK. unfold PEC.ecap. destruct (Z.eqb_spec ek 0) as [->|NZ]; [cbn; Lia.lia|].
      replace (2 ^ ek) with (2 * 2 ^ (ek - 1)) by (rewrite <- Z.pow_succ_r by Lia.lia; f_equal; Lia.lia). pose proof (Z.pow_pos_nonneg 2 (ek - 1)). Lia.lia. }
    assert (POTSPLIT : fst (PEC.pot_estack L ek) = fst (PM.cost1 L (PEC.ESZ * PEC.ecap (ek + 1))) + fst (PEC.pot_estack L (ek + 1))
                    /\ snd (PEC.pot_estack L ek) = snd (PM.cost1 L (PEC.ESZ * PEC.ecap (ek + 1))) + snd (PEC.pot_estack L (ek + 1))).
    { rewrite NCE. unfold PEC.pot_estack, PM.cost1, PEC.ESZ. cbn [fst snd]. rewrite Z.pow_add_r, Z.pow_1_r by lia. clear. Lia.lia. }
    set (SZ := 24 * PEC.ecap ek). set (NC := PEC.ecap (ek + 1)) in *.
    rewrite FULLEQ in EV32. fold SZ in EV32.
    assert (EBB : 0 <= eb /\ eb + SZ <= hl_sptop L - 2 ^ 23).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [rewrite (EKB Z0); unfold SZ; rewrite Z0; cbn; clear - STOP; Lia.lia|]. destruct (EBND ltac:(lia)) as (B0 & B4 & _). unfold SZ. clear - B0 B4. Lia.lia. }

    pose proof (PESENBP.encBOn_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => eb + SZ | 36%nat => edepth | _ => 0 end)) as P1. cbn beta iota in P1. rewrite !HO in P1.
    fold SZ in EV40.
    PMK.feed P1 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov]) | assumption | PMK.rk | PMK.gmem | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 EDR EBB; Lia.lia) | PMK.sc ]).
    assert (POSTN : exists fx1 R1 M1, mem_grows M M1
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (fb + 440 + 48 <= i < fb + 440 + 48 + 4) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 0x35c24) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0x35c78) M1 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBOn -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
      /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 80)
      /\ getr R1 (PMK.reg 8) = getr R (PMK.reg 10)
      /\ getr R1 (PMK.reg 11) = Z_to_bv 64 (eb + SZ)
      /\ getr R1 (PMK.reg 18) = Z_to_bv 64 (eb + SZ)
      /\ L5.u32_at RSEGS M1 (fb + 440 + 48) (edepth + 1)
      /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
      /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
      /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
      /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
      /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))) by post_of P1.
    clear P1.
    PMK.pvz_hg ltac:(idtac; destruct POSTN as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG1 & FRZ1 & MS1 & KS1 & X2_1 & X8_1 & X11_1 & X18_1 & C48 & S40 & S32 & S24 & S16 & S8)); PMK.pvz_clrT.
    rewrite A10 in X8_1.
    set (P1 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (fb + 440 + 48 <= a < fb + 440 + 48 + 4)).
    assert (FRZ1' : forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ1; [exact Ha| |]; intros X'; apply N; unfold P1; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x35c24 R1 0x35c78 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 20480 a STK). unfold P1 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P1. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    set (W1 := [(fb + 440 + 48, 4)] : list L5.range).
    assert (WHI1 : forall a, PMK.inW W1 a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
    assert (NW1 : forall i, ~ (fb + 440 + 48 <= i < fb + 440 + 52) -> ~ PMK.inW W1 i) by (intros i Hi I; apply PMFR.inW_inv1 in I; lia).
    assert (EK1 : PMK.ek L LB sp 20480 W1 M M1).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 W1 M M1 P1 FRZ1' STK (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 20480) by exact (PMK.stk_grows L M M1 sp 20480 MG1 STK).
    pose proof (L5C.stk_writable RSEGS _ M1 sp 20480 STK1) as WR1.
    assert (EA1 : enc_at M1 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PEEK.enc_depth RSEGS EE L M M1 (fb + 440) fb eb ek _ edepth (edepth + 1) EA); [lia|lia| intros EKP; destruct (EBND EKP) as (B0 & B4 & _); unfold PEC.ESZ; clear - B0 B4 STOP; Lia.lia| | | exact MG1| exact C48| unfold MAX_DEPTH; lia].
      - intros i Hi Ri Ni. apply FRZ1'; [exact Hi|]. unfold P1. clear - Ri Ni F1. Lia.lia.
      - intros EKP i Hi Ri. apply FRZ1'; [exact Hi|]. unfold P1. unfold PEC.ESZ in Ri. destruct (EBND EKP) as (B0 & B4 & _). clear - Ri B4 SLO F1 SHI STOP. Lia.lia. }
    pose proof EA1 as (_ & _ & _ & EV24a & _ & _ & _ & EDEF1 & _). cbn [PEC.en_b] in EV24a.
    assert (WRov1 : L5.writable RSEGS M1 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF1|lia|lia]).
    assert (EKT1 : PMK.ek L LBc0 sp 20480 W1 M M1) by (apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 W1 M M1 EK1); [exact INC0| intros x Hx; exact Hx| intros a O; exact O]).
    destruct (KEEPF W1 M1 EKT1) as (_ & _ & _ & BASE1 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
    pose proof BASE1 as (IMG1 & _). cbn [pa_rw_lo CAD PeCLayoutS.CADDR_S] in IMG1.
    pose proof (bv_unsigned_in_range 64 (getr R1 (PMK.reg 10))) as RBj1. change (bv_modulus 64) with (2 ^ 64) in RBj1.

    assert (POSTG : exists fx2 R2 M2, mem_grows M1 M2
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 8) -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx1 R1 (Z_to_bv 64 0x35c78) M1 (seg_rom RSEGS)) (@mkst fx2 R2 (Z_to_bv 64 0x37294) M2 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBOg0 -> getr R2 (PMK.reg x) = getr R1 (PMK.reg x))
      /\ getr R2 (PMK.reg 1) = Z_to_bv 64 220380
      /\ getr R2 (PMK.reg 9) = Z_to_bv 64 SZ
      /\ getr R2 (PMK.reg 10) = Z_to_bv 64 (fb + 440 + 24)
      /\ getr R2 (PMK.reg 11) = Z_to_bv 64 NC
      /\ L5.u64_at RSEGS M2 (sp - 48) (fb + 440 + 24)).
    { subst SZ NC.
      assert (EKC : ek = 0 \/ ek = 1 \/ ek = 2 \/ ek = 3 \/ ek = 4 \/ ek = 5 \/ ek = 6 \/ ek = 7 \/ ek = 8 \/ ek = 9 \/ ek = 10 \/ ek = 11) by lia.
      destruct EKC as [EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|[EKv|EKv]]]]]]]]]]]; rewrite EKv in FULLEQ, X11_1, X18_1 |- *; cbn [PEC.ecap Z.eqb Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub Z.add Z.pos_sub Pos.add] in FULLEQ, X11_1, X18_1 |- *.
      - rewrite (EKB EKv) in X11_1, X18_1, EV24a. cbn [Z.add] in X11_1, X18_1.
        assert (EBAL8 : True) by exact I. assert (EB0 : True) by exact I. assert (EB4 : True) by exact I.
        pose proof (PESENBP.encBOg0_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg1_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg2_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg3_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg4_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg5_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg6_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg7_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg8_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg9_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg10_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2.
      - destruct (EBND ltac:(lia)) as (EB0 & EB4 & _). pose proof (proj1 (EBLK ltac:(lia))) as EBAL8.
        pose proof (PESENBP.encBOg11_conc fx1 R1 M1 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 55%nat => bv_unsigned (getr R1 (PMK.reg 10)) | _ => 0 end)) as P2. cbn beta iota in P2.
        PMK.feed P2 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact EBAL8]) | (rewrite PMPK.word_id; reflexivity) | PMK.sc
                               | (clear - SLO STOP SHI F1 F2 EB0 EB4; unfold hl_ceil in *; lia) ]). post_of P2. }
    PMK.pvz_hg ltac:(idtac; destruct POSTG as (fx2 & R2 & M2 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG2 & FRZ2 & MS2 & KS2 & G1 & G9 & G10 & G11 & C48s)); PMK.pvz_clrT.
    set (P2 := fun a => (sp - 48 <= a < sp - 48 + 8)).
    assert (FRZ2' : forall a, 0 <= a < 2 ^ 64 -> ~ P2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ2; [exact Ha| exact N]).
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model fx1 fx2 R1 0x35c78 R2 0x37294 M2 P2 K HH1 Mh Ml ltac:(lia) MS2 MG2 FRZ2').
    { intros a Pa. apply (PMK.cwr_stack L LB M1 sp 20480 a STK1). unfold P2 in Pa. clear - Pa SLO SHI F1 F2. Lia.lia. }
    { intros a. unfold P2. apply PMK.rng_dec. }
    intros HH2.
    assert (EK2 : PMK.ek L LB sp 20480 [] M1 M2).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [] M1 M2 P2 FRZ2' STK1 (PMFR.brange_hi L LB BR)). intros a Pa. left. unfold P2 in Pa. lia. }
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 20480) by exact (PMK.stk_grows L M1 M2 sp 20480 MG2 STK1).
    assert (STKc2 : L5C.stk (hl_sptop L) M2 (sp - 80) 14336).
    { apply (PMK.stk_call L M2 sp 20480 (sp - 80) 14336 STK2); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
    assert (EA2 : enc_at M2 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LB sp 20480 [] M1 M2 EK2 STK1 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact EINC| exact EA1]. }
    assert (EKT2 : PMK.ek L LBc0 sp 20480 W1 M M2).
    { apply (PMK.ek_trans L LBc0 sp 20480 W1 M M1 M2 EKT1). apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 W1 [] M1 M2 EK2); [exact INC0| intros x Hx; exact Hx| intros a _ r0 Hr0; destruct Hr0]. }
    destruct (KEEPF W1 M2 EKT2) as (_ & _ & _ & BASE2 & _). { intros a I. apply PMFR.inW_inv1 in I. unfold WEC. lia. }
    assert (SV2 : forall a v, sp - 40 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v).
    { intros a v Ha Ha' U. apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2'; [lia| unfold P2; lia]|lia|lia| exact U]. }
    assert (ECAP10 : PEC.ecap ek <= 1024).
    { clear - EK EK10. unfold PEC.ecap. destruct (ek =? 0); [Lia.lia|]. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; Lia.lia. }
    assert (ALSZ : SZ mod 8 = 0) by (unfold SZ; replace (24 * PEC.ecap ek) with (3 * PEC.ecap ek * 8) by (clear; Lia.lia); apply Z.mod_mul; clear; Lia.lia).
    pose proof (PESK.sink_pot_nonneg RSEGS L PMSP.T3 PMSP.T4 P M (fb + 496) k PO SKA) as SPN. pose proof (PESK.sink_pot_fst PMSP.T3 PMSP.T4 P (PESK.sk_c k)) as SPF.

    pose proof EVA as EVX. unfold PECSS.evec_alloc_spec, PECS.evec_alloc_spec in EVX. cbn [pe_evec_alloc PECSS.EE PeCLayoutS.EADDR_S] in EVX.
    apply (EVX fx2 R2 M2 model K LB cr NC (sp - 80) 220380 HH2 MOK K0); clear EVX.
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact G1|]. split; [clear; unfold L5.ra_ok; Lia.lia|].
      split; [rewrite (KS2 2%nat) by PMK.inl; exact X2_1|].
      split; [rewrite (KS2 3%nat) by PMK.inl; rewrite (KS1 3%nat) by PMK.inl; exact Rgp|]. split; [rewrite (KS2 4%nat) by PMK.inl; rewrite (KS1 4%nat) by PMK.inl; exact Rtp|]. exact STKc2. }
    { rewrite L5K.rl11. exact G11. }
    { clear - NCB. unfold NC in *. Lia.lia. }
    { exact BASE2. }
    { pose proof (PEN (ek + 1) ltac:(lia)) as PE1. unfold PMSP.credit_le, PEC.pot_enc, PEC.credit_add in CRED |- *. change (PEC.en_k en) with ek in CRED.
      cbn [fst snd] in CRED |- *. clear - CRED POTSPLIT PE1 SPN SPF. Lia.lia. }
    intros fx3 R3 M3 model3 cr3 B RP3 R3_10 R3_11 FB HP3 CK3 MB3 HH3.
    rewrite L5K.rl10 in R3_10. rewrite L5K.rl11 in R3_11. change (PMSP.pm_scr 1) with 14336 in HP3.
    pose proof (L5C.fresh_block_bounds L LB M3 B _ FB) as (FB0 & FB1 & FB16 & FBn & FB4). unfold hl_ceil in FB4. unfold PEC.ESZ in FB1, FBn, FB4.
    destruct FB as (FBR & FBA & FBD). unfold PEC.ESZ in FBD.
    pose proof (PMFR.model_ok_but_vm model model3 MOK MB3) as MOK3. pose proof MOK3 as (Mh3 & Ml3 & Mm3).
    assert (STK3 : L5C.stk (hl_sptop L) M3 sp 20480) by (apply (PMK.stk_after RSEGS L KL LB M2 M3 sp 20480 (sp - 80) 14336 _ STK2 HP3); lia).
    pose proof (L5C.stk_writable RSEGS _ M3 sp 20480 STK3) as WR3.
    pose proof (PMK.ek_of_hpres L LB (sp - 80) 14336 [] M2 M3 HP3) as EK3.
    assert (WHI3 : forall a, PMK.inW [] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
    assert (SC3 : 0 <= 14336) by lia.
    assert (EA3 : enc_at M3 (fb + 440) fb (PEC.ENC eb ek estk (edepth + 1))).
    { apply (PECF.enc_keep RSEGS EE L KL LB (sp - 80) 14336 [] M2 M3 EK3 STKc2 SC3 BR WHI3); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact EINC| exact EA2]. }
    assert (SKA3 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M3 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB (sp - 80) 14336 [] M2 M3 EK3 STKc2 SC3 BR WHI3); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 [] M1 M2 EK2 STK1 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 W1 M M1 EK1 STK SC0 BR WHI1); [lia|lia| intros i Hi; apply NW1; lia| exact KINC| exact SKA]. }
    assert (SV3 : forall a v, sp - 40 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Ha Ha' U. apply (PMFR.u64_keep RSEGS L KL LB (sp - 80) 14336 [] M2 M3 EK3 STKc2 SC3); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)|]. exact (SV2 a v Ha Ha' U). }
    pose proof (SV3 (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S40) as S40c. pose proof (SV3 (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S32) as S32c.
    pose proof (SV3 (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S24) as S24c. pose proof (SV3 (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S16) as S16c.
    pose proof (SV3 (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S8) as S8c.
    pose proof EA3 as (_ & _ & _ & EV24c & EV32c & EV40c & EV48c & EDEF3 & _ & _ & _ & _ & _ & EBLK3 & EIT3).
    cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24c, EV32c, EV40c, EV48c, EBLK3, EIT3. unfold PEC.ESZ in EV32c, EV40c. fold n in EV32c. rewrite FULLEQ in EV32c. fold SZ in EV32c, EV40c.
    assert (WRov3 : L5.writable RSEGS M3 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF3|lia|lia]).
    assert (SZB : 0 <= SZ /\ SZ + 24 <= 24 * NC /\ SZ <= 24576) by (unfold SZ, NC; clear - CN CAPGROW ECAP10; Lia.lia).
    assert (WRBS : L5.writable RSEGS M3 (B + SZ) 24) by (apply (L5.writable_sub _ M3 B (24 * NC)); [apply (L5C.writable_of_defined RSEGS); [exact FBD|lia|lia]|lia|lia]).
    assert (ALB : B mod 8 = 0) by (apply PMPK.m16_8; exact FB16).

    pose proof (PESENBP.encBOh_conc fx3 R3 M3 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 37%nat => B | 38%nat => NC | 40%nat => SZ | _ => 0 end)) as P4. cbn beta iota in P4.
    PMK.feed P4 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact ALSZ | exact ALB]) | assumption | PMK.rk | PMK.gmem
                           | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 EBB FB0 FB4 SZB NCB; Lia.lia) | PMK.sc ]).
    assert (POSTH : exists fx4 R4 M4, mem_grows M3 M4
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (B + SZ + 0 <= i < B + SZ + 0 + 24) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx3 R3 (Z_to_bv 64 0x35cdc) M3 (seg_rom RSEGS)) (@mkst fx4 R4 (Z_to_bv 64 0xac48c) M4 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBOh -> getr R4 (PMK.reg x) = getr R3 (PMK.reg x))
      /\ getr R4 (PMK.reg 1) = Z_to_bv 64 220452
      /\ getr R4 (PMK.reg 9) = Z_to_bv 64 B
      /\ getr R4 (PMK.reg 11) = Z_to_bv 64 eb
      /\ getr R4 (PMK.reg 12) = Z_to_bv 64 SZ
      /\ getr R4 (PMK.reg 18) = Z_to_bv 64 (B + SZ + 24)
      /\ getr R4 (PMK.reg 19) = Z_to_bv 64 (B + 24 * NC)
      /\ L5.u64_at RSEGS M4 (B + SZ + 16) 0
      /\ L5.u64_at RSEGS M4 (B + SZ + 8) 0
      /\ L5.u32_at RSEGS M4 (B + SZ) 1) by post_of P4.
    clear P4.
    PMK.pvz_hg ltac:(idtac; destruct POSTH as (fx4 & R4 & M4 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG4 & FRZ4 & MS4 & KS4 & H1 & H9 & H11 & H12 & H18 & H19 & I16 & I8 & I0)); PMK.pvz_clrT.
    set (P4 := fun a => (B + SZ + 0 <= a < B + SZ + 0 + 24)).
    assert (FRZ4' : forall a, 0 <= a < 2 ^ 64 -> ~ P4 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ4; [exact Ha| exact N]).
    assert (BINB : In (B, 24 * NC) ((B, PEC.ESZ * NC) :: LB)) by (left; reflexivity).
    apply (PMK.spiece RSEGS L HI KL HIok ((B, PEC.ESZ * NC) :: LB) cr3 M3 model3 fx3 fx4 R3 0x35cdc R4 0xac48c M4 P4 K HH3 Mh3 Ml3 ltac:(lia) MS4 MG4 FRZ4').
    { intros a Pa. apply (PMK.cwr_block L _ B (24 * NC) a BINB). unfold P4 in Pa. clear - Pa SZB. Lia.lia. }
    { intros a. unfold P4. apply PMK.rng_dec. }
    intros HH4.
    assert (EK4 : PMK.ek L LB sp 20480 [] M3 M4).
    { apply (PEEK.ek_piece_own RSEGS L HI KL HIok [(B, PEC.ESZ * NC)] LB cr3 M4 _ sp 20480 [] M3 M4 P4 B (24 * NC) HH4 ltac:(left; reflexivity) FRZ4' ltac:(unfold hl_ceil; lia) ltac:(lia)).
      intros a Pa. right. right. unfold P4 in Pa. clear - Pa SZB. Lia.lia. }
    assert (STK4 : L5C.stk (hl_sptop L) M4 sp 20480) by exact (PMK.stk_grows L M3 M4 sp 20480 MG4 STK3).

    assert (APART : B + 24 * NC <= eb \/ eb + SZ <= B).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [right; rewrite (EKB Z0); unfold SZ; rewrite Z0; cbn; clear - FB0; Lia.lia|].
      destruct (FBA _ (EINC _ (BINk ltac:(lia)))) as [X'|X']; cbn [fst snd] in X'; unfold PEC.ESZ in X'; unfold SZ, NC; [left| right]; exact X'. }
    assert (DEFsrc : L5.defined M4 eb SZ).
    { destruct (Z.eq_dec ek 0) as [Z0|NZ]; [unfold SZ; rewrite Z0; cbn; intros i Hi; exfalso; clear - Hi; Lia.lia|].
      destruct (EBLK3 ltac:(lia)) as (_ & D3 & _). unfold PEC.ESZ in D3. fold SZ in D3. exact (L5.defined_grows M3 M4 _ _ MG4 D3). }
    destruct (PECPY.copy_run_eq0 RSEGS 0xac48c Es0Sums.src0_copy_spec_memcpy fx4 R4 M4 B eb SZ 220452
               ltac:(rewrite (KS4 10%nat) by PMK.inl; exact R3_10) H11 H12 H1 ltac:(clear; unfold L5.ra_ok; Lia.lia)
               ltac:(clear - SZB; Lia.lia) ltac:(clear - FB0; Lia.lia) ltac:(clear - FB4 SZB STOP; Lia.lia) ltac:(clear - EBB; Lia.lia) ltac:(clear - EBB STOP; Lia.lia)
               ltac:(clear - APART SZB; Lia.lia)
               ltac:(apply (L5.writable_sub _ M4 B (24 * NC)); [apply (L5C.writable_of_defined RSEGS); [exact (L5.defined_grows M3 M4 _ _ MG4 FBD)|lia|lia]|lia|lia])
               DEFsrc) as (R5 & M5 & MS5 & MG5 & FRZ5 & DEF5 & CPY5 & KS5 & A10_5).
    set (P5 := fun a => (B <= a < B + SZ)).
    assert (FRZ5' : forall a, 0 <= a < 2 ^ 64 -> ~ P5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ5; [exact Ha| exact N]).
    apply (PMK.spiece RSEGS L HI KL HIok ((B, PEC.ESZ * NC) :: LB) cr3 M4 model3 fx4 fx4 R4 0xac48c R5 220452 M5 P5 K HH4 Mh3 Ml3 ltac:(lia) MS5 MG5 FRZ5').
    { intros a Pa. apply (PMK.cwr_block L _ B (24 * NC) a BINB). unfold P5 in Pa. clear - Pa SZB. Lia.lia. }
    { intros a. unfold P5. apply PMK.rng_dec. }
    intros HH5.
    assert (EK5 : PMK.ek L LB sp 20480 [] M4 M5).
    { apply (PEEK.ek_piece_own RSEGS L HI KL HIok [(B, PEC.ESZ * NC)] LB cr3 M5 _ sp 20480 [] M4 M5 P5 B (24 * NC) HH5 ltac:(left; reflexivity) FRZ5' ltac:(unfold hl_ceil; lia) ltac:(lia)).
      intros a Pa. right. right. unfold P5 in Pa. clear - Pa SZB. Lia.lia. }
    assert (STK5 : L5C.stk (hl_sptop L) M5 sp 20480) by exact (PMK.stk_grows L M4 M5 sp 20480 MG5 STK4).
    pose proof (L5C.stk_writable RSEGS _ M5 sp 20480 STK5) as WR5.
    assert (AG35 : forall i, 0 <= i < 2 ^ 64 -> sp - 20480 <= i -> M5 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
    { intros i Hi Ri. rewrite (FRZ5' i Hi) by (unfold P5; clear - Ri FB4 SZB SLO; Lia.lia). apply (FRZ4' i Hi). unfold P4. clear - Ri FB4 SZB SLO. Lia.lia. }
    assert (EV24e : L5.u64_at RSEGS M5 (fb + 440 + 24) eb) by (apply (L5C.u64_at_agree RSEGS M3 M5); [intros i Hi; apply AG35; lia|lia|lia| exact EV24c]).
    assert (EV40e : L5.u64_at RSEGS M5 (fb + 440 + 40) (eb + SZ)) by (apply (L5C.u64_at_agree RSEGS M3 M5); [intros i Hi; apply AG35; lia|lia|lia| exact EV40c]).
    assert (WRov5 : L5.writable RSEGS M5 (fb + 440) 56) by (apply (L5.writable_grows _ M3 M5); [exact (StoreOk.mem_grows_trans _ _ _ MG4 MG5)| exact WRov3]).
    pose proof (bv_unsigned_in_range 64 (getr R5 (PMK.reg 10))) as RBj5. change (bv_modulus 64) with (2 ^ 64) in RBj5.

    pose proof (PESENBP.encBOi_conc fx4 R5 M5 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 33%nat => eb | 37%nat => B | 40%nat => SZ | 42%nat => B + SZ + 24
        | 43%nat => B + 24 * NC | 55%nat => bv_unsigned (getr R5 (PMK.reg 10)) | _ => 0 end)) as P6. cbn beta iota in P6.
    PMK.feed P6 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov]) | (rewrite PMPK.word_id; reflexivity) | assumption | PMK.rk | PMK.gmem
                           | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 EBB FB0 FB4 SZB NCB; Lia.lia) | PMK.sc ]).
    assert (POSTI : exists fx6 R6 M6, mem_grows M5 M6
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 32) -> ~ (fb + 440 + 24 <= i < fb + 440 + 24 + 24) -> M6 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fx4 R5 (Z_to_bv 64 0x35d24) M5 (seg_rom RSEGS)) (@mkst fx6 R6 (Z_to_bv 64 0x37228) M6 (seg_rom RSEGS))
      /\ (forall x, In x PESENBP.KS_encBOi -> getr R6 (PMK.reg x) = getr R5 (PMK.reg x))
      /\ getr R6 (PMK.reg 1) = Z_to_bv 64 220496
      /\ getr R6 (PMK.reg 10) = Z_to_bv 64 (sp - 80)
      /\ getr R6 (PMK.reg 11) = Z_to_bv 64 (eb + SZ)
      /\ L5.u64_at RSEGS M6 (sp - 56) (eb + SZ)
      /\ L5.u64_at RSEGS M6 (sp - 64) eb
      /\ L5.u64_at RSEGS M6 (sp - 72) eb
      /\ L5.u64_at RSEGS M6 (sp - 80) eb
      /\ L5.u64_at RSEGS M6 (fb + 440 + 40) (B + 24 * NC)
      /\ L5.u64_at RSEGS M6 (fb + 440 + 32) (B + SZ + 24)
      /\ L5.u64_at RSEGS M6 (fb + 440 + 24) B) by post_of P6.
    clear P6.
    PMK.pvz_hg ltac:(idtac; destruct POSTI as (fx6 & R6 & M6 & pvzP); PMK.pvz_lin pvzP;
                     destruct pvzP as (MG6 & FRZ6 & MS6 & KS6 & J1 & J10 & J11 & Q24 & Q16 & Q8 & Q0 & F40 & F32 & F24)); PMK.pvz_clrT.
    set (P6 := fun a => (sp - 80 <= a < sp - 80 + 32) \/ (fb + 440 + 24 <= a < fb + 440 + 24 + 24)).
    assert (FRZ6' : forall a, 0 <= a < 2 ^ 64 -> ~ P6 a -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ6; [exact Ha| |]; intros X'; apply N; unfold P6; [left| right]; exact X'. }
    apply (PMK.spiece RSEGS L HI KL HIok ((B, PEC.ESZ * NC) :: LB) cr3 M5 model3 fx4 fx6 R5 0x35d24 R6 0x37228 M6 P6 K HH5 Mh3 Ml3 ltac:(lia) MS6 MG6 FRZ6').
    { intros a [Pa|Pa]; apply (PMK.cwr_stack L _ M5 sp 20480 a STK5); clear - Pa SLO SHI F1 F2; Lia.lia. }
    { intros a. unfold P6. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH6.
    assert (EK6 : PMK.ek L LB sp 20480 [(fb + 440, 56)] M5 M6).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 20480 [(fb + 440, 56)] M5 M6 P6 FRZ6' STK5 (PMFR.brange_hi L LB BR)).
      intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
    assert (STK6 : L5C.stk (hl_sptop L) M6 sp 20480) by exact (PMK.stk_grows L M5 M6 sp 20480 MG6 STK5).
    pose proof (StoreOk.mem_grows_trans _ _ _ MG4 (StoreOk.mem_grows_trans _ _ _ MG5 MG6)) as MG36.
    assert (AG36 : forall i, 0 <= i < 2 ^ 64 -> sp - 48 <= i -> (i < fb + 440 + 24 \/ fb + 440 + 48 <= i) -> M6 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
    { intros i Hi Ri Oi. rewrite (FRZ6' i Hi) by (unfold P6; clear - Ri Oi; Lia.lia). apply (AG35 i Hi). clear - Ri; Lia.lia. }
    assert (SV6 : forall a v, sp - 48 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3 a v -> L5.u64_at RSEGS M6 a v).
    { intros a v Ha Ha' U. apply (L5C.u64_at_agree RSEGS M3 M6); [intros i Hi; apply AG36; clear - Hi Ha Ha' F1 F2 SLO SHI STOP; Lia.lia|lia|lia| exact U]. }
    pose proof (SV6 (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S40c) as S40d. pose proof (SV6 (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S32c) as S32d.
    pose proof (SV6 (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S24c) as S24d. pose proof (SV6 (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S16c) as S16d.
    pose proof (SV6 (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) S8c) as S8d.

    assert (COPY36 : forall j, 0 <= j < SZ -> M6 (Z_to_bv 64 (B + j)) = M3 (Z_to_bv 64 (eb + j))).
    { intros j Hj. rewrite (FRZ6' (B + j)) by (first [clear - Hj FB0 FB4 SZB STOP; Lia.lia | unfold P6; clear - Hj FB0 FB4 SZB SLO F1; Lia.lia]).
      rewrite (CPY5 j Hj). apply FRZ4'; [clear - Hj EBB STOP; Lia.lia|]. unfold P4. clear - Hj APART SZB. Lia.lia. }
    assert (EA6 : enc_at M6 (fb + 440) fb (PEC.ENC B (ek + 1) (estk ++ [EI 1 0 0]) (edepth + 1))).
    { apply (PEEK.enc_grow RSEGS EE L M3 M6 (fb + 440) fb eb ek estk (edepth + 1) (edepth + 1) (EI 1 0 0) B EA3); [lia|lia| | exact MG36| exact EK10| exact F24| | | | unfold MAX_DEPTH; lia| | exact ALB| | | |].
      + intros i Hi Ri. apply AG36; [exact Hi| clear - Ri F1; Lia.lia| clear - Ri; Lia.lia].
      + unfold PEC.ESZ. fold n. rewrite FULLEQ. fold SZ. replace (B + 24 * (PEC.ecap ek + 1)) with (B + SZ + 24) by (unfold SZ; clear; Lia.lia). exact F32.
      + unfold PEC.ESZ. fold NC. exact F40.
      + apply (PMF.u32_at_agree RSEGS M3 M6); [intros i Hi; apply AG36; clear - Hi F1 F2 SLO SHI STOP; Lia.lia|lia|lia| exact EV48c].
      + fold n. rewrite FULLEQ. fold NC. clear - CAPGROW. unfold NC. Lia.lia.
      + unfold PEC.ESZ. fold NC. exact (L5.defined_grows M3 M6 _ _ MG36 FBD).
      + exact FBR.
      + intros i Hi. pose proof (EIT3 i Hi) as (T0 & T8 & T16). unfold PEC.ESZ in T0, T8, T16 |- *.
        assert (Hi24 : 24 * Z.of_nat i + 24 <= SZ) by (unfold SZ; rewrite <- FULLEQ; unfold n; clear - Hi; Lia.lia).
        destruct (EBLK3 ltac:(destruct (Z.eq_dec ek 0) as [Z0|NZ]; [exfalso; unfold SZ in Hi24; rewrite Z0 in Hi24; cbn in Hi24; clear - Hi24; Lia.lia| lia])) as (_ & D3 & _).
        unfold PEC.ESZ in D3. assert (D3' : L5.defined M3 eb SZ) by (unfold SZ; exact D3).
        split; [|split].
        * apply (PECPY.u32_copy RSEGS M3 M6 (eb + 24 * Z.of_nat i) (B + 24 * Z.of_nat i));
            [clear - EBB Hi24 SZB; Lia.lia| clear - EBB Hi24 SZB STOP; Lia.lia| clear - FB0 Hi24; Lia.lia| clear - FB4 Hi24 SZB STOP; Lia.lia
            | apply (L5.defined_sub M3 eb SZ); [exact D3'| clear - Hi24; Lia.lia| clear - Hi24; Lia.lia]
            | intros j Hj; replace (B + 24 * Z.of_nat i + j) with (B + (24 * Z.of_nat i + j)) by (clear; Lia.lia); replace (eb + 24 * Z.of_nat i + j) with (eb + (24 * Z.of_nat i + j)) by (clear; Lia.lia); apply COPY36; clear - Hj Hi24; Lia.lia
            | exact T0].
        * apply (PECPY.u64_copy RSEGS M3 M6 (eb + 24 * Z.of_nat i + 8) (B + 24 * Z.of_nat i + 8));
            [clear - EBB Hi24 SZB; Lia.lia| clear - EBB Hi24 SZB STOP; Lia.lia| clear - FB0 Hi24; Lia.lia| clear - FB4 Hi24 SZB STOP; Lia.lia
            | apply (L5.defined_sub M3 eb SZ); [exact D3'| clear - Hi24; Lia.lia| clear - Hi24; Lia.lia]
            | intros j Hj; replace (B + 24 * Z.of_nat i + 8 + j) with (B + (24 * Z.of_nat i + 8 + j)) by (clear; Lia.lia); replace (eb + 24 * Z.of_nat i + 8 + j) with (eb + (24 * Z.of_nat i + 8 + j)) by (clear; Lia.lia); apply COPY36; clear - Hj Hi24; Lia.lia
            | exact T8].
        * apply (PECPY.u64_copy RSEGS M3 M6 (eb + 24 * Z.of_nat i + 16) (B + 24 * Z.of_nat i + 16));
            [clear - EBB Hi24 SZB; Lia.lia| clear - EBB Hi24 SZB STOP; Lia.lia| clear - FB0 Hi24; Lia.lia| clear - FB4 Hi24 SZB STOP; Lia.lia
            | apply (L5.defined_sub M3 eb SZ); [exact D3'| clear - Hi24; Lia.lia| clear - Hi24; Lia.lia]
            | intros j Hj; replace (B + 24 * Z.of_nat i + 16 + j) with (B + (24 * Z.of_nat i + 16 + j)) by (clear; Lia.lia); replace (eb + 24 * Z.of_nat i + 16 + j) with (eb + (24 * Z.of_nat i + 16 + j)) by (clear; Lia.lia); apply COPY36; clear - Hj Hi24; Lia.lia
            | exact T16].
      + unfold PEC.eitem_at, PEC.ESZ. fold n. rewrite FULLEQ. fold SZ. cbn [ei_kind ei_len ei_cnt].
        assert (AG46 : forall i, 0 <= i < 2 ^ 64 -> B + SZ <= i < B + SZ + 24 -> M6 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i)).
        { intros i Hi Ri. rewrite (FRZ6' i Hi) by (unfold P6; clear - Ri FB4 SZB SLO F1; Lia.lia). apply (FRZ5' i Hi). unfold P5. clear - Ri; Lia.lia. }
        split; [apply (PMF.u32_at_agree RSEGS M4 M6); [intros i Hi; apply AG46; [clear - Hi FB0 FB4 SZB STOP; Lia.lia| clear - Hi; Lia.lia]| clear - FB0 SZB; Lia.lia| clear - FB4 SZB STOP; Lia.lia| exact I0]|].
        split; [apply (L5C.u64_at_agree RSEGS M4 M6); [intros i Hi; apply AG46; [clear - Hi FB0 FB4 SZB STOP; Lia.lia| clear - Hi; Lia.lia]| clear - FB0 SZB; Lia.lia| clear - FB4 SZB STOP; Lia.lia| exact I8]|].
        apply (L5C.u64_at_agree RSEGS M4 M6); [intros i Hi; apply AG46; [clear - Hi FB0 FB4 SZB STOP; Lia.lia| clear - Hi; Lia.lia]| clear - FB0 SZB; Lia.lia| clear - FB4 SZB STOP; Lia.lia| exact I16]. }
    set (en' := PEC.ENC B (ek + 1) (estk ++ [EI 1 0 0]) (edepth + 1)) in EA6.
    assert (EOWN' : PEC.enc_own en' = [(B, PEC.ESZ * NC)]).
    { unfold PEC.enc_own, en'. cbn [PEC.en_k PEC.en_b]. replace (ek + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold NC. reflexivity. }
    assert (EKT6 : PMK.ek L LBc0 sp 20480 Ws M M6).
    { apply (PMK.ek_trans L LBc0 sp 20480 Ws M M2 M6).
      { apply (PMK.ek_weaken L LBc0 LBc0 sp 20480 sp 20480 Ws W1 M M2 EKT2); [apply incl_refl| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. unfold W1 in Hr0. destruct Hr0 as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply (O (fb + 440, 56)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M2 M3 M6).
      { apply (PMK.ek_callee_in' RSEGS L KL LBc0 LB sp 20480 (sp - 80) 14336 Ws [] M2 M3 HP3 INC0); [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)| intros a I; destruct (PMFR.inW_nil a I)]. }
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M3 M4 M6); [apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws [] M3 M4 EK4); [exact INC0| intros x Hx; exact Hx| intros a _ r0 Hr0; destruct Hr0]|].
      apply (PMK.ek_trans L LBc0 sp 20480 Ws M4 M5 M6); [apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws [] M4 M5 EK5); [exact INC0| intros x Hx; exact Hx| intros a _ r0 Hr0; destruct Hr0]|].
      apply (PMK.ek_weaken L LBc0 LB sp 20480 sp 20480 Ws [(fb + 440, 56)] M5 M6 EK6); [exact INC0| intros x Hx; exact Hx|].
      intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin]. }
    assert (DKT6 : PMK.dk L LBc0 sp 20480 M M6).
    { apply (PMK.dk_trans L LBc0 sp 20480 M M2 M6 (PMK.dk_grows L LBc0 sp 20480 M M2 (StoreOk.mem_grows_trans _ _ _ MG1 MG2))).
      apply (PMK.dk_trans L LBc0 sp 20480 M2 M3 M6); [apply (PMK.dk_callee L LBc0 LB sp 20480 (sp - 80) 14336 _ M2 M3 HP3 INC0); lia|].
      apply (PMK.dk_grows L LBc0 sp 20480 M3 M6 MG36). }
    destruct (KEEPF Ws M6 EKT6) as (_ & _ & _ & BASE6 & _).
    { intros a (r0 & Hin & Hr). unfold Ws in Hin. unfold L5.in_rng in Hr. unfold WEC. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia. }
    assert (SKA6 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M6 (fb + 496) k).
    { apply (PECF.sink_keep RSEGS L KL LB sp 20480 [(fb + 440, 56)] M5 M6 EK6 STK5 SC0 BR); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 [] M4 M5 EK5 STK4 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC|].
      apply (PECF.sink_keep RSEGS L KL LB sp 20480 [] M3 M4 EK4 STK3 SC0 BR WHI0); [lia|lia| intros i Hi I; destruct (PMFR.inW_nil i I)| exact KINC| exact SKA3]. }
    assert (CR36 : PMSP.credit_le (PEC.pot_enc L P en' k) cr3 /\ PMSP.credit_keep cr cr3 (PEC.pot_enc L P en k) (PEC.pot_enc L P en' k)).
    { unfold PMSP.credit_le, PMSP.credit_keep, PEC.pot_enc, PEC.credit_add in CRED, CK3 |- *. unfold en'. change (PEC.en_k en) with ek in CRED |- *. cbn [fst snd PEC.en_k] in CRED, CK3 |- *.
      fold NC in POTSPLIT. unfold PMSP.cr0 in CK3. cbn [fst snd] in CK3. clear - CRED CK3 POTSPLIT SPN SPF. Lia.lia. }
    destruct CR36 as (CR3e & CK3e).

    assert (AFTER7 : forall (fx7 : FPState) (R7 : bvmap 5 word) (M7 : word -> option byte) (model7 : Model) (cr7 : credit),
      getr R7 (PMK.reg 2) = Z_to_bv 64 (sp - 80) -> getr R7 (PMK.reg 8) = Z_to_bv 64 (fb + 440) -> getr R7 (PMK.reg 18) = Z_to_bv 64 (B + SZ + 24) ->
      (forall x, In x CSL -> getr R7 (PMK.reg x) = getr R (PMK.reg x)) ->
      L5C.stk (hl_sptop L) M7 sp 20480 ->
      L5.u64_at RSEGS M7 (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) -> L5.u64_at RSEGS M7 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) ->
      L5.u64_at RSEGS M7 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) -> L5.u64_at RSEGS M7 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) ->
      L5.u64_at RSEGS M7 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) ->
      enc_at M7 (fb + 440) fb en' -> PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M7 (fb + 496) k ->
      PMK.ek L LBc0 sp 20480 Ws M M7 -> PMK.dk L LBc0 sp 20480 M M7 ->
      PMSP.model_ok model7 -> model_but_vm model model7 ->
      hi_heap HI (PEC.owned s en' k ++ LBX) cr7 M7 (m_vmmaps model7) ->
      PMSP.credit_le (PEC.pot_enc L P en' k) cr7 -> PMSP.credit_keep cr cr7 (PEC.pot_enc L P en k) (PEC.pot_enc L P en' k) ->
      srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 0x35d50 M7 model7) K).
    { intros fx7 R7 M7 model7 cr7 Z2 Z8 Z18 ZCS STK7 U40 U32 U24 U16 U8 EA7 SKA7 EK7 DK7 MOK7 MB7 HH7 CR7 CK7.
      pose proof MOK7 as (Mh7 & Ml7 & Mm7).
      pose proof EA7 as (_ & EV8g & _ & _ & _ & _ & EV48g & EDEF7 & _). cbn [PEC.en_depth] in EV48g. cbn [PESK.o_sink pe_off_sink EE PeCLayoutS.EADDR_S] in EV8g.
      assert (WRov7 : L5.writable RSEGS M7 (fb + 440) 56) by (apply (L5C.writable_of_defined RSEGS); [exact EDEF7|lia|lia]).
      pose proof (L5C.stk_writable RSEGS _ M7 sp 20480 STK7) as WR7.
      set (LB7 := PEC.owned s en' k ++ LBX) in HH7.
      assert (BR7 : PMFR.brange L LB7) by (apply (PMFR.brange_of_heap L HI HIok LB7 LB7 cr7 M7 _ HH7); apply incl_refl).
      assert (INC07 : incl LBc0 LB7) by (unfold LBc0, LB7, PEC.owned; insub).
      assert (KINC7 : incl (PESK.sink_own k) LB7) by (unfold LB7, PEC.owned; insub).
      pose proof (bv_unsigned_in_range 64 (getr R7 (PMK.reg 10))) as RBj7. change (bv_modulus 64) with (2 ^ 64) in RBj7.
      pose proof (PESENBP.encBOt_conc fx7 R7 M7 (fun j => match j with 2%nat => sp | 10%nat => fb + 440 | 41%nat => fb + 496 | 42%nat => B + SZ + 24 | 55%nat => bv_unsigned (getr R7 (PMK.reg 10)) | _ => 0 end)) as P8.
      cbn beta iota in P8.
      PMK.feed P8 ltac:(first [(unfold PESENBP.aligned; first [exact A16 | exact ALov | exact ALsk]) | (rewrite PMPK.word_id; reflexivity) | assumption | PMK.rk | PMK.gmem
                             | (PMK.arith_goal; clear - SLO STOP SHI F1 F2 FB0 FB4 SZB NCB; Lia.lia) | PMK.sc ]).
      assert (POSTT : exists fx8 R8 M8, mem_grows M7 M8
        /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 1) -> ~ (fb + 440 + 32 <= i < fb + 440 + 32 + 8) -> M8 (Z_to_bv 64 i) = M7 (Z_to_bv 64 i))
        /\ msteps RSEGS (@mkst fx7 R7 (Z_to_bv 64 0x35d50) M7 (seg_rom RSEGS)) (@mkst fx8 R8 (Z_to_bv 64 0x372d8) M8 (seg_rom RSEGS))
        /\ (forall x, In x PESENBP.KS_encBOt -> getr R8 (PMK.reg x) = getr R7 (PMK.reg x))
        /\ getr R8 (PMK.reg 1) = Z_to_bv 64 220520
        /\ getr R8 (PMK.reg 10) = Z_to_bv 64 (fb + 496)
        /\ getr R8 (PMK.reg 11) = Z_to_bv 64 (sp - 80)
        /\ L5.u64_at RSEGS M8 (fb + 440 + 32) (B + SZ + 24)) by post_of P8.
      clear P8.
      PMK.pvz_hg ltac:(idtac; destruct POSTT as (fx8 & R8 & M8 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG8 & FRZ8 & MS8 & KS8 & T1 & T10 & T11 & C32t)); PMK.pvz_clrT.
      set (P8 := fun a => (sp - 80 <= a < sp - 80 + 1) \/ (fb + 440 + 32 <= a < fb + 440 + 32 + 8)).
      assert (FRZ8' : forall a, 0 <= a < 2 ^ 64 -> ~ P8 a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
      { intros a Ha N. apply FRZ8; [exact Ha| |]; intros X'; apply N; unfold P8; [left| right]; exact X'. }
      apply (PMK.spiece RSEGS L HI KL HIok LB7 cr7 M7 model7 fx7 fx8 R7 0x35d50 R8 0x372d8 M8 P8 K HH7 Mh7 Ml7 ltac:(lia) MS8 MG8 FRZ8').
      { intros a [Pa|Pa]; apply (PMK.cwr_stack L LB7 M7 sp 20480 a STK7); clear - Pa SLO SHI F1 F2; Lia.lia. }
      { intros a. unfold P8. apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH8.
      assert (EK8 : PMK.ek L LB7 sp 20480 [(fb + 440, 56)] M7 M8).
      { apply (PMK.ek_piece_in RSEGS L KL LB7 sp 20480 [(fb + 440, 56)] M7 M8 P8 FRZ8' STK7 (PMFR.brange_hi L LB7 BR7)). intros a [Pa|Pa]; [left; lia| right; apply PMK.inW_here; lia]. }
      assert (STK8 : L5C.stk (hl_sptop L) M8 sp 20480) by exact (PMK.stk_grows L M7 M8 sp 20480 MG8 STK7).
      assert (SV8 : forall a v, sp - 48 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M7 a v -> L5.u64_at RSEGS M8 a v).
      { intros a v Ha Ha' U. apply (L5C.u64_at_agree RSEGS M7 M8); [intros i Hi; apply FRZ8'; [clear - Hi Ha Ha' F1 SLO SHI STOP; Lia.lia| unfold P8; clear - Hi Ha Ha' F1; Lia.lia]|lia|lia| exact U]. }
      assert (EA8 : enc_at M8 (fb + 440) fb en').
      { unfold en'. apply (PEEK.enc_upd RSEGS EE L M7 M8 (fb + 440) fb B (ek + 1) _ (edepth + 1) (edepth + 1)); [exact EA7|lia|lia| intros _; unfold PEC.ESZ; fold NC; clear - FB0 FB4 STOP; Lia.lia| | | exact MG8| | | unfold MAX_DEPTH; lia].
        - intros i Hi Ri N1 N2. apply FRZ8'; [exact Hi|]. unfold P8. clear - Ri N1 F1. Lia.lia.
        - intros _ i Hi Ri. apply FRZ8'; [exact Hi|]. unfold P8. unfold PEC.ESZ in Ri. fold NC in Ri. clear - Ri FB4 SLO F1. Lia.lia.
        - rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. unfold PEC.ESZ. fold n. rewrite FULLEQ.
          match goal with |- L5.u64_at _ _ _ ?v => replace v with (B + SZ + 24) by (unfold SZ; clear; Lia.lia) end. exact C32t.
        - apply (PMF.u32_at_agree RSEGS M7 M8); [intros i Hi; apply FRZ8'; [clear - Hi F1 F2 SLO SHI STOP; Lia.lia| unfold P8; clear - Hi F1; Lia.lia]|lia|lia| exact EV48g]. }
      assert (SKA8 : PESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P M8 (fb + 496) k).
      { apply (PECF.sink_keep RSEGS L KL LB7 sp 20480 [(fb + 440, 56)] M7 M8 EK8 STK7 SC0 BR7); [intros a I; apply PMFR.inW_inv1 in I; left; lia|lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact KINC7| exact SKA7]. }
      apply (TAIL fx8 R8 M8 model7 cr7 B (ek + 1) T1).
      + rewrite (KS8 2%nat) by PMK.inl. exact Z2.
      + rewrite (KS8 8%nat) by PMK.inl. exact Z8.
      + exact T10. + exact T11.
      + intros x Hx. rewrite (KS8 x) by exact (PEEK.sub_in PESENBP.KS_encBOt CSL ltac:(vm_compute; reflexivity) x Hx). apply ZCS. exact Hx.
      + exact STK8.
      + exact (SV8 (sp - 40) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U40). + exact (SV8 (sp - 32) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U32).
      + exact (SV8 (sp - 24) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U24). + exact (SV8 (sp - 16) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U16).
      + exact (SV8 (sp - 8) _ ltac:(clear; Lia.lia) ltac:(clear; Lia.lia) U8).
      + exact EA8. + exact SKA8.
      + apply (PMK.ek_trans L LBc0 sp 20480 Ws M M7 M8 EK7). apply (PMK.ek_weaken L LBc0 LB7 sp 20480 sp 20480 Ws [(fb + 440, 56)] M7 M8 EK8); [exact INC07| intros x Hx; exact Hx|].
        intros a O r0 Hr0 Hin. destruct Hr0 as [<-|[]]. apply (O (fb + 440, 56)); [left; reflexivity| exact Hin].
      + apply (PMK.dk_trans L LBc0 sp 20480 M M7 M8 DK7). apply (PMK.dk_grows L LBc0 sp 20480 M7 M8 MG8).
      + exact MOK7. + exact MB7. + exact HH8. + exact CR7. + exact CK7. }

    pose proof EVD as EVY. unfold PECSS.evec_sbdtor_spec, PECS.evec_sbdtor_spec in EVY. cbn [pe_evec_sbdtor PECSS.EE PeCLayoutS.EADDR_S] in EVY.
    assert (ENT6 : PMSP.entry CAD L R6 M6 (sp - 80) 220496 1).
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact J1|]. split; [clear; unfold L5.ra_ok; Lia.lia|].
      split; [PMK.rk|]. split; [PMK.rk|]. split; [PMK.rk|].
      apply (PMK.stk_call L M6 sp 20480 (sp - 80) 14336 STK6); [lia|lia|lia|]. replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    assert (DQ6 : L5.defined M6 (sp - 80) 32) by (destruct STK6 as (_ & _ & _ & _ & D6); apply (L5.defined_sub M6 (sp - 20480) 20480 (sp - 80) 32 D6); lia).
    assert (ALq : (sp - 80) mod 8 = 0) by (apply PMPK.m16_8; replace (sp - 80) with (sp + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact A16).
    rewrite L5K.rl10 in EVY.
    destruct (Z.eq_dec ek 0) as [EK0|EKP].
    +
      pose proof (EKB EK0) as EB0.
      apply (EVY fx6 R6 M6 model3 K ((B, PEC.ESZ * NC) :: LB) cr3 (sp - 80) eb eb SZ (sp - 80) 220496 HH6 MOK3 K0 ENT6 J10 ltac:(lia) ltac:(lia) ALq DQ6 Q0 ltac:(replace (sp - 80 + 8) with (sp - 72) by (clear; Lia.lia); exact Q8) ltac:(replace (sp - 80 + 16) with (sp - 64) by (clear; Lia.lia); exact Q16) ltac:(replace (sp - 80 + 24) with (sp - 56) by (clear; Lia.lia); exact Q24) ltac:(left; exact EB0) BASE6); clear EVY.
      intros fx7 R7 M7 model7 cr7 RP7 HP7 CR7 MB7 HH7.
      rewrite EB0 in HP7, HH7. cbn [Z.eqb] in HP7, HH7. change (PMSP.pm_scr 1) with 14336 in HP7.
      pose proof (PMFR.model_ok_but_vm model3 model7 MOK3 MB7) as MOK7.
      assert (BRL : PMFR.brange L ((B, PEC.ESZ * NC) :: LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr3 M6 _ HH6); apply incl_refl).
      pose proof (PMK.ek_of_hpres L _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 HP7) as EK7.
      assert (STKc6 : L5C.stk (hl_sptop L) M6 (sp - 80) 14336) by (destruct ENT6 as (_ & _ & _ & _ & _ & X'); exact X').
      assert (WHI7 : forall a, PMK.inW [(sp - 80, 32)] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (INCL6 : incl LB ((B, PEC.ESZ * NC) :: LB)) by (intros x Hx; right; exact Hx).
      apply (AFTER7 fx7 R7 M7 model7 cr7).
      * PMK.rk. * PMK.rk. * PMK.rk.
      * intros x Hx. assert (Hc : In x PMK.cs_all) by exact (PEEK.sub_in PMK.cs_all CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R6 R7 x RP7 Hc). rewrite (KS6 x) by exact (PEEK.sub_in PESENBP.KS_encBOi CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (KS5 x) by exact (PEEK.sub_in L5K.CS CSL ltac:(vm_compute; reflexivity) x Hx). rewrite (KS4 x) by exact (PEEK.sub_in PESENBP.KS_encBOh CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R2 R3 x RP3 Hc). rewrite (KS2 x) by exact (PEEK.sub_in PESENBP.KS_encBOg0 CSL ltac:(vm_compute; reflexivity) x Hx).
        apply KS1. exact (PEEK.sub_in PESENBP.KS_encBOn CSL ltac:(vm_compute; reflexivity) x Hx).
      * apply (PMK.stk_after RSEGS L KL _ M6 M7 sp 20480 (sp - 80) 14336 _ STK6 HP7); lia.
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S40d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S32d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S24d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S16d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S8d].
      * apply (PECF.enc_keep RSEGS EE L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| rewrite EOWN'; intros x [<-|[]]; left; reflexivity| exact EA6].
      * apply (PECF.sink_keep RSEGS L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| intros x Hx; right; exact (KINC x Hx)| exact SKA6].
      * apply (PMK.ek_trans L LBc0 sp 20480 Ws M M6 M7 EKT6).
        apply (PMK.ek_callee_in' RSEGS L KL LBc0 _ sp 20480 (sp - 80) 14336 Ws [(sp - 80, 32)] M6 M7 HP7); [intros x Hx; right; exact (INC0 x Hx)|lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)| intros a I; apply PMFR.inW_inv1 in I; left; lia].
      * apply (PMK.dk_trans L LBc0 sp 20480 M M6 M7 DKT6). apply (PMK.dk_callee L LBc0 _ sp 20480 (sp - 80) 14336 _ M6 M7 HP7); [intros x Hx; right; exact (INC0 x Hx)|lia|lia].
      * exact MOK7. * exact (L5C.model_but_vm_trans _ _ _ MB3 MB7).
      * refine (PEEK.heap_perm L HI HIok _ _ cr7 M7 _ _ HH7). unfold PEC.owned, LB. rewrite EOWN'. unfold PEC.owned.
        replace (PEC.enc_own en) with (@nil (Z * Z)) by (unfold PEC.enc_own, en; cbn [PEC.en_k]; rewrite EK0; reflexivity). cbn [app].
        rewrite <- !app_assoc. apply (Permutation_middle (PM.parser_own s) (PESK.sink_own k ++ LBX)).
      * unfold PMSP.credit_le in CR3e, CR7 |- *. clear - CR3e CR7. Lia.lia.
      * unfold PMSP.credit_keep, PMSP.credit_le in CK3e, CR7 |- *. clear - CK3e CR7. Lia.lia.
    +
      assert (EOWN : PEC.enc_own en = [(eb, PEC.ESZ * PEC.ecap ek)]).
      { unfold PEC.enc_own, en. cbn [PEC.en_k PEC.en_b]. replace (ek =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      set (LBd := (eb, SZ) :: (B, PEC.ESZ * NC) :: PESK.sink_own k ++ PM.parser_own s ++ LBX).
      assert (PERMd : Permutation ((B, PEC.ESZ * NC) :: LB) LBd).
      { unfold LBd, LB, PEC.owned. rewrite EOWN. unfold PEC.ESZ at 2. fold SZ. rewrite <- !app_assoc. cbn [app].
        apply Permutation_sym. apply (Permutation_cons_app ((B, PEC.ESZ * NC) :: PM.parser_own s) (PESK.sink_own k ++ LBX)).
        cbn [app]. apply perm_skip. apply Permutation_app_swap_app. }
      pose proof (PEEK.heap_perm L HI HIok _ _ cr3 M6 _ PERMd HH6) as HH6d.
      destruct (EBND ltac:(lia)) as (B0 & B4 & _).
      apply (EVY fx6 R6 M6 model3 K LBd cr3 (sp - 80) eb eb SZ (sp - 80) 220496 HH6d MOK3 K0 ENT6 J10 ltac:(lia) ltac:(lia) ALq DQ6 Q0 ltac:(replace (sp - 80 + 8) with (sp - 72) by (clear; Lia.lia); exact Q8) ltac:(replace (sp - 80 + 16) with (sp - 64) by (clear; Lia.lia); exact Q16) ltac:(replace (sp - 80 + 24) with (sp - 56) by (clear; Lia.lia); exact Q24) ltac:(right; left; reflexivity) BASE6); clear EVY.
      intros fx7 R7 M7 model7 cr7 RP7 HP7 CR7 MB7 HH7.
      replace (eb =? 0) with false in HP7, HH7 by (symmetry; apply Z.eqb_neq; lia). unfold LBd in HP7, HH7. cbn [lb_remove fst] in HP7, HH7. rewrite Z.eqb_refl in HP7, HH7.
      change (PMSP.pm_scr 1) with 14336 in HP7.
      set (LB7 := (B, PEC.ESZ * NC) :: PESK.sink_own k ++ PM.parser_own s ++ LBX) in HP7, HH7.
      pose proof (PMFR.model_ok_but_vm model3 model7 MOK3 MB7) as MOK7.
      assert (BRL : PMFR.brange L LB7) by (apply (PMFR.brange_of_heap L HI HIok _ _ cr7 M7 _ HH7); apply incl_refl).
      pose proof (PMK.ek_of_hpres L LB7 (sp - 80) 14336 [(sp - 80, 32)] M6 M7 HP7) as EK7.
      assert (STKc6 : L5C.stk (hl_sptop L) M6 (sp - 80) 14336) by (destruct ENT6 as (_ & _ & _ & _ & _ & X'); exact X').
      assert (WHI7 : forall a, PMK.inW [(sp - 80, 32)] a -> sp - 80 <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; apply PMFR.inW_inv1 in I; left; lia).
      assert (INC7 : incl LBc0 LB7) by (unfold LBc0, LB7; intros x Hx; right; revert x Hx; insub).
      assert (KINC7 : incl (PESK.sink_own k) LB7) by (unfold LB7; intros x Hx; right; apply in_or_app; left; exact Hx).
      apply (AFTER7 fx7 R7 M7 model7 cr7).
      * PMK.rk. * PMK.rk. * PMK.rk.
      * intros x Hx. assert (Hc : In x PMK.cs_all) by exact (PEEK.sub_in PMK.cs_all CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R6 R7 x RP7 Hc). rewrite (KS6 x) by exact (PEEK.sub_in PESENBP.KS_encBOi CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (KS5 x) by exact (PEEK.sub_in L5K.CS CSL ltac:(vm_compute; reflexivity) x Hx). rewrite (KS4 x) by exact (PEEK.sub_in PESENBP.KS_encBOh CSL ltac:(vm_compute; reflexivity) x Hx).
        rewrite (PMK.cs_of_preserved R2 R3 x RP3 Hc). rewrite (KS2 x) by exact (PEEK.sub_in PESENBP.KS_encBOg0 CSL ltac:(vm_compute; reflexivity) x Hx).
        apply KS1. exact (PEEK.sub_in PESENBP.KS_encBOn CSL ltac:(vm_compute; reflexivity) x Hx).
      * apply (PMK.stk_after RSEGS L KL _ M6 M7 sp 20480 (sp - 80) 14336 _ STK6 HP7); lia.
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S40d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S32d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S24d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S16d].
      * apply (PMFR.u64_keep RSEGS L KL _ (sp - 80) 14336 _ M6 M7 EK7 STKc6 SC3); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact S8d].
      * apply (PECF.enc_keep RSEGS EE L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| rewrite EOWN'; intros x [<-|[]]; left; reflexivity| exact EA6].
      * apply (PECF.sink_keep RSEGS L KL _ (sp - 80) 14336 [(sp - 80, 32)] M6 M7 EK7 STKc6 SC3 BRL WHI7); [lia|lia| intros i Hi I; apply PMFR.inW_inv1 in I; lia| exact KINC7| exact SKA6].
      * apply (PMK.ek_trans L LBc0 sp 20480 Ws M M6 M7 EKT6).
        apply (PMK.ek_callee_in' RSEGS L KL LBc0 _ sp 20480 (sp - 80) 14336 Ws [(sp - 80, 32)] M6 M7 HP7 INC7); [lia|lia| unfold hl_ceil; lia| lia| exact (PMFR.brange_hi L LBc0 BRc0)| intros a I; apply PMFR.inW_inv1 in I; left; lia].
      * apply (PMK.dk_trans L LBc0 sp 20480 M M6 M7 DKT6). apply (PMK.dk_callee L LBc0 _ sp 20480 (sp - 80) 14336 _ M6 M7 HP7 INC7); lia.
      * exact MOK7. * exact (L5C.model_but_vm_trans _ _ _ MB3 MB7).
      * refine (PEEK.heap_perm L HI HIok _ _ cr7 M7 _ _ HH7). unfold PEC.owned, LB7. rewrite EOWN'. rewrite <- !app_assoc. cbn [app].
        apply (Permutation_cons_app (PM.parser_own s) (PESK.sink_own k ++ LBX)). apply Permutation_app_swap_app.
      * unfold PMSP.credit_le in CR3e, CR7 |- *. clear - CR3e CR7. Lia.lia.
      * unfold PMSP.credit_keep, PMSP.credit_le in CK3e, CR7 |- *. clear - CK3e CR7. Lia.lia.
Qed.

End WithHeap.
End PESENCB.
