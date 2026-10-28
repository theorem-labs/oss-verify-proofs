(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BExec BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BStep BSegs BsShadow BsConst BsIface BsCXXHeap.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Bridge LbB_Call.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section SR.
  Context {HCEIL : HeapCeil}.

  Lemma aconst_ok_app : forall A n lo hi, aapp A n -> A <= lo -> hi <= A + n -> aconst_ok (lo, hi).
  Proof.
    intros A n lo hi Happ H1 H2. unfold aapp, aapp_lo, aapp_hi in Happ. acb.
    assert (Hb : (0x6e8000 <= lo /\ hi <= 0x7fff7000) \/ (0x10007fff8000 <= lo)).
    { unfold AIMG_TOP, ALOWSH_LO, AHI_LO in Happ. destruct Happ as [[X Y]|[X Y]]; [left | right]; lia. }
    clear Happ.
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL,
      AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL;
      replace (sh AIMG_LO) with 0x7fffa000 by reflexivity; replace (sh AIMG_TOP) with 0x800d5000 by reflexivity;
      destruct Hb as [[X Y]|X]; lia.
  Qed.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma sr_blk : forall (Q : config -> Prop) s msF mo R F pc fc m ro R1 pc1 M1,
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F pc fc None m ro -> rfull R ->
    CatSim.msteps asegs (MS R F pc fc None m ro) (MS R1 F pc1 fc None M1 ro) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       as_VIS H s msF' = MS (mkR (getr R1 1) (getr R1 2) (getr R1 3) (getr R1 4) (getr R1 5) (getr R1 6) (getr R1 7) (getr R1 8)
                                 (getr R1 9) (getr R1 10) (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16)
                                 (getr R1 17) (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24)
                                 (getr R1 25) (getr R1 26) (getr R1 27) (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                            F pc1 fc None M1 ro ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q s msF mo R F pc fc m ro R1 pc1 M1 KR VIS HF Hms K.
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    eapply (ahh_evt_then H HH (fun ms => ms = MS (mkR (getr R1 1) (getr R1 2) (getr R1 3) (getr R1 4) (getr R1 5) (getr R1 6) (getr R1 7) (getr R1 8)
                                 (getr R1 9) (getr R1 10) (getr R1 11) (getr R1 12) (getr R1 13) (getr R1 14) (getr R1 15) (getr R1 16)
                                 (getr R1 17) (getr R1 18) (getr R1 19) (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24)
                                 (getr R1 25) (getr R1 26) (getr R1 27) (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
                            F pc1 fc None M1 ro)); [exact KR | exact VIS | |].
    - eapply evt_of_msteps_done; [exact Hms|]. exact (MS_full_eq _ _ _ _ _ _ HF1).
    - intros msF' mo' KR' MP' HP. apply K; assumption.
  Qed.

  Lemma sr_evt : forall (Q : config -> Prop) (P : machine_state -> Prop) s msF mo R F pc fc m ro,
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F pc fc None m ro ->
    evt asegs P (MS R F pc fc None m ro) ->
    (forall msF' mo', as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' -> P (as_VIS H s msF') -> Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof. intros Q P s msF mo R F pc fc m ro KR VIS E K. eapply (ahh_evt H HH P); [exact KR | exact VIS | exact E | exact K]. Qed.

  Lemma apres_new_block : forall s LB p A n SP m m' W,
    as_RHEAP H s ((p, A, n) :: LB) m -> ~ In p (map blk_id LB) ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => A <= fst iv /\ snd iv <= A + n) W ->
    A + n <= SP ->
    apres H LB SP m m'.
  Proof.
    intros s LB p A n SP m m' W RH NI MU WM FW HSP a Ha Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    assert (OUTR : ~ (A <= a < A + n)).
    { intros K. unfold aclient_addr in Hc.
      destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
      - lia.
      - unfold aimg_client in Hc. unfold AIMG_TOP in RI. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; lia.
      - assert (Hb' : In b ((p, A, n) :: LB)) by (right; exact Hb).
        assert (Hid : blk_id b <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
        pose proof (ah_disj H HH _ _ _ (p, A, n) b RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
        unfold blk_addr, blk_size in D, Hr. cbn [fst snd] in D, Hr.
        destruct D as [D|D]; lia.
      - assert (Hb' : In b ((p, A, n) :: LB)) by (right; exact Hb).
        pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
        unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
        clear MU WM FW. Z.div_mod_to_equations.
        destruct RAPP as [RAPP|RAPP]; destruct QAPP as [QAPP|QAPP]; lia.
      - destruct RF as [RF|RF]; lia.
      - unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
        unfold sh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. clear MU WM FW. Z.div_mod_to_equations.
        destruct RAPP as [RAPP|RAPP]; destruct F4 as [F4|F4]; lia.
      - unfold aapp, aapp_lo, aapp_hi in RAPP. acb.
        unfold sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. clear MU WM FW. Z.div_mod_to_equations.
        destruct RAPP as [RAPP|RAPP]; lia. }
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as [H1 H2]. cbn in H1, H2.
      split; [lia | apply IH; apply (Forall_inv_tail FW)]. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.

  Lemma apres_fresh : forall s LB p A n SP m0 m m' W,
    as_RHEAP H s ((p, A, n) :: LB) m0 -> ~ In p (map blk_id LB) ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (A <= fst iv /\ snd iv <= A + n) \/ (sh A <= fst iv /\ snd iv <= sh A + nsh n)
                              \/ (aceil <= fst iv /\ snd iv <= SP)) W ->
    aceil <= SP ->
    apres H LB SP m m'.
  Proof.
    intros s LB p A n SP m0 m m' W RH NI MU WM FW HSP a Ha Hc.
    pose proof (ah_blocks H HH _ _ _ (p, A, n) RH (or_introl eq_refl)) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    acb.
    assert (CLS : SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n))).
    { unfold aclient_addr in Hc.
      destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
      - left. exact Hc.
      - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
      - right. assert (Hb' : In b ((p, A, n) :: LB)) by (right; exact Hb).
        assert (Hid : blk_id b <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
        pose proof (ah_disj H HH _ _ _ (p, A, n) b RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
        pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
        destruct b as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
        destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
      - right. assert (Hb' : In b ((p, A, n) :: LB)) by (right; exact Hb).
        assert (Hid : blk_id b <> p) by (intros E; apply NI; rewrite <- E; apply in_map; exact Hb).
        pose proof (ah_disj H HH _ _ _ (p, A, n) b RH (or_introl eq_refl) Hb' (fun E => Hid (eq_sym E))) as D.
        pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
        unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
        destruct b as [[pb Ab] nb]. cbn [fst snd] in *.
        unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
        unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
        clear MU WM FW. Z.div_mod_to_equations.
        destruct D as [D|D]; split; try lia; split; lia.
      - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
        destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
      - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
        unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *. clear MU WM FW.
        Z.div_mod_to_equations.
        destruct RF as [RF|RF]; split; try lia; split; lia.
      - right. assert (SA0 : 0x7fff8000 <= sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. destruct RAPP as [RP|RP]; split; try lia; split; lia. }
    assert (OUT : outside W a).
    { clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
      pose proof (Forall_inv FW) as H1. cbn in H1.
      split; [| apply IH; apply (Forall_inv_tail FW)].
      destruct CLS as [C|(C1 & C2 & C3)]; destruct H1 as [[H1 H2]|[[H1 H2]|[H1 H2]]]; lia. }
    split.
    - unfold wa. apply MU. rewrite unsigned_lit by lia. exact OUT.
    - intros Hw. apply WM. exact Hw.
  Qed.
End SR.
