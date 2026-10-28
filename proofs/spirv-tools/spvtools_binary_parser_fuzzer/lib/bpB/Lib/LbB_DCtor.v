(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SR LbB_Own LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section DCtor.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma inframe_facts : forall LF m O n, as_RFS H LF m -> obj_inframe LF O n -> 0 <= n -> AIMG_TOP <= O ->
    O + n + 64 <= AAPP_HI /\ shvis m O (O + n) /\ as_FSB H <= O /\ O + n <= as_FSB H + AFS_SIZE.
  Proof.
    intros LF m O n RF (f & Hf & H1 & H2) Hn HO.
    destruct (ah_RFS_range H HH LF m RF) as [FSB_OK FR]. pose proof (FR f Hf) as (K1 & K2 & K3 & K4 & K5).
    pose proof FSB_OK as (B1 & B2 & B3 & B4). pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    pose proof (ah_frm_shvis H HH LF m f RF Hf) as SV.
    unfold AFS_HDR, AFS_SIZE, AAPP_HI, AIMG_TOP in *.
    split; [lia|]. split; [eapply shvis_sub; [exact SV | lia | lia | lia | lia | lia]|]. lia.
  Qed.

  Lemma cw_laws : forall LB LF m (sp ds lo : Z), as_RFS H LF m -> obj_inframe LF ds DS_SIZE -> app_obj ds DS_SIZE ->
    aceil <= lo -> lo + 8192 <= sp -> sp <= AAPP_HI ->
    Forall (aclient_write_ok H LB) [(sp + -8192, sp + 0); (ds + 0, ds + DS_SIZE)]
    /\ Forall (afs_write_ok H LF) [(sp + -8192, sp + 0); (ds + 0, ds + DS_SIZE)]
    /\ Forall stack0_ok [(sp + -8192, sp + 0); (ds + 0, ds + DS_SIZE)].
  Proof.
    intros LB LF m sp ds lo RF IN AO CE LO SPH.
    pose proof AO as (O1 & O2 & O3).
    destruct (inframe_facts LF m ds DS_SIZE RF IN ltac:(unfold DS_SIZE; lia) O1) as (F1 & _ & F3 & F4).
    destruct (ah_RFS_range H HH LF m RF) as [(B1 & B2 & B3 & B4) _].
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    unfold DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO, AAPP_HI in *.
    split; [|split].
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE, DS_SIZE.
      + left. lia.
      + right; right; right; right; left. lia.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold afs_write_ok; cbn [fst snd]; unfold AFS_SIZE, DS_SIZE.
      + left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. lia.
      + right. destruct IN as (f & Hf & H1 & H2). exists f. unfold DS_SIZE in H2. split; [exact Hf|]. lia.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold stack0_ok; cbn [fst snd]; unfold DS_SIZE.
      + left. unfold AHI_LO. lia.
      + destruct O2 as [O2|O2]; [right | left]; unfold sh, AHI_LO, ASHADOW_BASE in *; try lia.
  Qed.

  Lemma cw_xpres : forall s LB m m' (sp ds lo : Z), as_RHEAP H s LB m ->
    munch [(sp + -8192, sp + 0); (ds + 0, ds + DS_SIZE)] m m' -> wmono asegs m m' ->
    aceil <= lo -> lo + 8192 <= sp ->
    xpres H LB sp ([(ds, ds + DS_SIZE)] ++ []) m m'.
  Proof.
    intros s LB m m' sp ds lo RH MU WM CE LO a Ha [Hc Hx].
    split; [| apply WM].
    apply MU. unfold wa. rewrite unsigned_lit by lia. cbn [outside]. split; [| split; [| exact I]].
    - intros [L L2].
      pose proof aceil_facts as ((A1 & A2) & A3 & A4). pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
      destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
      + lia.
      + unfold aimg_client in Hc. lia.
      + pose proof (ah_blocks H HH _ _ _ b RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). lia.
      + pose proof (ah_blocks H HH _ _ _ b RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
        unfold sh, nsh, ASHADOW_BASE in Hr. Z.div_mod_to_equations. lia.
      + unfold AFS_SIZE in *. lia.
      + unfold sh, AFS_SIZE, ASHADOW_BASE in *. Z.div_mod_to_equations. lia.
      + unfold AHI_LO in Hc. lia.
    - intros [L L2]. apply Hx. cbn [rin_ivs app fst snd]. left. lia.
  Qed.

  Theorem ds_ctor_okA : ds_ctor_stmtA H LINV_P5 ds_repA0.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF CH
           lo B shi errv ds ppos pcons pstr pstr2 err pos j1 j2
           PRE Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Herr DSob DSW DSin PPob PPC PPL PPin S1ob S1C S1in S2ob S2C S2in PCob PCC DISJ.
    destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERR & MI & TP & RA2 & LV
                     & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
    destruct DSob as (DSA & DS8 & DSfs & DS0 & DS47 & DSsp & DSO).
    destruct PPob as (PPA & PP8 & PPfs & PP0 & PP47 & PPsp & PPO).
    destruct S1ob as (S1A & S18 & S1fs & S10 & S147 & S1sp & S1O).
    destruct S2ob as (S2A & S28 & S2fs & S20 & S247 & S2sp & S2O).
    destruct PCob as (PCA & PC8 & PCfs & PC0 & PC47 & PCsp & PCO).
    destruct (inframe_facts LF m ds DS_SIZE RFS DSin ltac:(unfold DS_SIZE; lia) (proj1 DSO)) as (DSH & DSV & _ & _).
    destruct (inframe_facts LF m ppos 24 RFS PPin ltac:(lia) (proj1 PPO)) as (PPH & PPV & _ & _).
    destruct (inframe_facts LF m pstr 24 RFS S1in ltac:(lia) (proj1 S1O)) as (S1H & S1V & _ & _).
    destruct (inframe_facts LF m pstr2 24 RFS S2in ltac:(lia) (proj1 S2O)) as (S2H & S2V & _ & _).
    assert (SPHI : bv_unsigned sp <= AAPP_HI) by (pose proof (stack0_bounds m lo shi S0); lia).
    assert (SPOBJ : forall O n, O = ds /\ n = DS_SIZE \/ O = ppos /\ n = 24 \/ O = pstr /\ n = 24 \/ O = pstr2 /\ n = 24
                                \/ O = pcons /\ n = 48 -> O + n <= bv_unsigned sp - LbB_DCtorK.CT_STACK \/ bv_unsigned sp <= O).
    { unfold LbB_DCtorK.CT_STACK, ADS_STACK in *.
      intros O n HO. destruct HO as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]]; lia. }
    assert (LO' : lo <= bv_unsigned sp - LbB_DCtorK.CT_STACK) by (unfold LbB_DCtorK.CT_STACK, ADS_STACK in *; lia).
    assert (OHI : forall O n, O = ds /\ n = DS_SIZE \/ O = ppos /\ n = 24 \/ O = pstr /\ n = 24 \/ O = pstr2 /\ n = 24 ->
                              O + n + 64 <= AAPP_HI).
    { intros O n HO. destruct HO as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]; assumption. }
    eapply (sr_evt H HH _ (LbB_DCtorK.ctor_P ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ds ppos pcons pstr pstr2 err lo
                                             pos j1 j2) s msF mo _ F (Z_to_bv 64 ADS_CTOR) fc m (seg_rom asegs) KR VIS).
    { eapply LbB_DCtorR1.ctor_evt; eassumption. }
    intros msF' mo' KR' MP' HP.
    destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E' & MI' & PW & REP).
    destruct PW as (PC & MU & WM). unfold LbB_DCtorK.CW in MU.
    destruct PC as (AC' & LV' & DA' & DW' & DV' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST').
    destruct (cw_laws LB LF m (bv_unsigned sp) ds lo RFS DSin DSO CEIL ltac:(unfold ADS_STACK in LO; lia) SPHI) as (W1 & W2 & W3).
    pose proof aceil_facts as ((A1 & A2) & A3 & A4).
    unfold ds_post. cbn [cfg_ms cfg_model].
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv, s, LB, [], F, fc.
    split; [exact E'|]. split; [exact FZ|]. split; [intros d Hd; discriminate Hd|].
    split; [exact KR'|]. split; [exact MP'|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |].
      cbn [disjoint_from cells_size csize]. rewrite TP, unsigned_lit by (unfold ATP; lia).
      pose proof DSO as (O1 & _). unfold ATP, AIMG_TOP, ADS_STACK in *. lia. }
    split; [eapply (ah_rauxv_frame H HH); [exact RAUX | exact MU | exact WM | exact W1]|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact W1]|].
    split; [cbv beta; split; [apply Permutation_refl | split; [apply REP | exact DW']]|].
    split; [constructor|].
    split; [eapply cw_xpres; [exact RH | exact MU | exact WM | exact CEIL | unfold ADS_STACK in LO; lia]|].
    split; [eapply (ah_RFS_frame H HH); [exact RFS | exact MU | exact WM | exact W2]|].
    split; [exact AC'|]. split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W3]|].
    split; [exact LV'|]. lia.
  Qed.
End DCtor.
