(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sstate"; "ss_next"; "ss_lenient"; "agree_below"; "smatch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "wsteps"; "etriple"; "model_idle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "lf_state"; "step_out"; "stop_reason"; "sym_step"; "mkLeaf"; "@Corelib.Init.Datatypes"; "list"; "bool"; "false"; "pair"; "option"; "Some"; "nat"; "true"; "None"; "cons"; "nil"; "@Corelib.Init.Logic"; "and"; "ex"; "eq"; "True"; "False"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_svc_pending"; "MachineOk"; "machine_result"; "step"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_halted"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "jpred"; "stableJ"; "LQ"; "LQJ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.C"; "wreach"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundW SymSoundR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section C.
Variable segs : list Segment.

Lemma smatch_idle : ltac2:(tb__ "0|1|
S0S1S12S2bA1M0S25S2aS5Vsegs;R5R4S15G0S23R3S24R2R1A2A4A4SaR2A1F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm.
  pose proof Hsm as (_ & _ & _ & Hhalt & _). cbn [fst snd cfg_ms cfg_model] in Hhalt. exact Hhalt.
Qed.

Lemma smatch_halted_none : ltac2:(tb__ "0|2|
S0S1S12S2bA1M0S25S2aS5Vsegs;R5R4S15G0S23R3S24R2R1A2A4A4S1fS16S36Q40A1M1A1S2cR2A1S1aG1A1A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm. apply model_idle_halted. eapply smatch_idle; eauto.
Qed.

Lemma smatch_pending_none : ltac2:(tb__ "0|2|
S0S1S12S2bA1M0S25S2aS5Vsegs;R5R4S15G0S23R3S24R2R1A2A4A4S1fS16S36Q40A1M1A1S26R3A1S1aG1A1A3F_;Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md Hsm.
  pose proof Hsm as (_ & _ & Hpend & _). cbn [fst snd cfg_ms cfg_model] in Hpend. exact Hpend.
Qed.

Lemma wstep_det_machine : ltac2:(tb__ "0|2|
S12S2bA1M0S25S2aS25S6S6SaR4A1S1fS16S36Q40A1M1A1S26R6A1S1aG1A1A3S1fS28S25A1S29Vsegs;R7A2S27S25R5A2A3S7Vsegs;S15G0S23R9S24R8R7A2A4R5A3S7Vsegs;S15G0S23RaS24R9R8A2A4R5A3S1fS6R7R6A3F_;F_;F_;F_;F_;Fw2;Fw1;Fms';Fmd;Fms;Ftr;").
Proof using .
  intros tr ms md ms' w1 w2 Hh Hp Hs Hw1 Hw2.
  rewrite (wstep_step_inv segs tr ms md ms' w1 Hh Hp Hs Hw1).
  rewrite (wstep_step_inv segs tr ms md ms' w2 Hh Hp Hs Hw2). reflexivity.
Qed.

Lemma next_rel_wstep : ltac2:(tb__ "0|3|
S1S1S0S12S2bA1M0S25S2aS5Vsegs;R4R6S15G0S23R3S24R2R1A2A4A4S37Vsegs;R7R6R5R4R3R2A7S1eS25S25S1eS0S0S1dS7Vsegs;S15G0S23R7S24R6R5A2A4S15G0S23R7S24R2R5A2A4M1A3S1dS6S7Vsegs;S15G0S23R8S24R7R6A2A4R1A3S1fS6R2S15G0S23R9S24R4R7A2A4A3F_;Fw';S1dS4S2RaA1M2R8R1A3S1dS38G2S2R9A1A2S5Vsegs;R1R9G1A4A2A2A2A2Lrho';A2Lms';A2F_;F_;Fmd;Fms;Ftr;Frho;FS';FS;").
Proof using .
  intros S S' rho tr ms md Hsm (ms' & rho' & Hstep & Hag & Hle & Hsm').
  pose proof (smatch_idle rho S tr ms md Hsm) as Hh.
  pose proof (smatch_pending_none rho S tr ms md Hsm) as Hp.
  exists ms', rho'. split; [apply wstep_of_step; assumption|].
  split; [intros w' Hw'; eapply wstep_step_inv; eauto|].
  split; [exact Hag|]. split; [exact Hle | exact Hsm'].
Qed.

Lemma wstep_det_smatch : ltac2:(tb__ "0|1|
S1S0S12S2bA1M0S25S2aS6S6S1fS13S3R7A1S14A3S5Vsegs;R7R8S15G0S23R6S24R5R4A2A4A4SeOLx;S10Vsegs;R9A2S1S20LS';S1S1S20LS2;LS1;SfS21Lr;Xex3S7Vsegs;S15G0S23R8S24R7R6A2A4R5A3S7Vsegs;S15G0S23R9S24R8R7A2A4R5A3S1fS6R7R6A3F_;F_;F_;F_;F_;Fw2;Fw1;Fmd;Fms;Ftr;Frho;FS;").
Proof using .
  intros S rho tr ms md w1 w2 Hlen Hsm Hprog Hw1 Hw2.
  pose proof (sym_step_sound segs S rho tr ms md Hsm) as X.
  destruct (sym_step segs S) as [S'|S1 S2|r].
  - apply (step_rel_strict segs _ _ _ _ _ _ Hlen) in X.
    destruct (next_rel_wstep S S' rho tr ms md Hsm X) as (ms' & rho' & _ & Huniq & _).
    rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
  - destruct X as [X|X].
    + destruct (next_rel_wstep S S1 rho tr ms md Hsm X) as (ms' & rho' & _ & Huniq & _).
      rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
    + destruct (next_rel_wstep S S2 rho tr ms md Hsm X) as (ms' & rho' & _ & Huniq & _).
      rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
  - destruct Hprog.
Qed.

Definition wreach (first : bool) (w w' : world) : Prop := ltac2:(tb__ "0|0|
S13OLfirst;Vfirst;S1eS6S6S1dS7Vsegs;Vw;R1A3S8Vsegs;R1Vw';A3A2Lw1;A2S8Vsegs;Vw;Vw';A3X13x2").

Lemma wreach_wsteps : ltac2:(tb__ "0|0|
S13S6S6S35R3R2R1A3S8Vsegs;R3R2A3F_;Fw';Fw;Ffirst;").
Proof using .
  intros [|] w w' H; [|exact H].
  destruct H as (w1 & H1 & H2). eapply wsteps_step; eauto.
Qed.

Lemma wreach_refl_false : ltac2:(tb__ "0|0|
S6S35S14R1R1A3Fw;").
Proof using . intros w. apply wsteps_refl. Qed.

Lemma wreach_cons : ltac2:(tb__ "0|0|
S13S6S6S6S7Vsegs;R3R2A3S8Vsegs;R3R2A3S35R6R5R3A3F_;F_;Fw';Fw1;Fw;Ffirst;").
Proof using .
  intros [|] w w1 w' H1 H2.
  - exists w1. split; assumption.
  - eapply wsteps_step; eauto.
Qed.

Lemma complete_via_nextJ : ltac2:(tb__ "0|4|
S30S1S1S0S12S2bA1M0S25S2aS12SbA1M1G1S13S31S2R9A1RaA2RbR8R7R5A3S5Vsegs;R9RbS15G0S23R8S24R7R6A2A4A4S37Vsegs;RcRbRaR9R8R7A7S0S6S2fVsegs;R10ReR2R1A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RdA3S1dS35S14R5R1A3S1dS4S2R12A1M2R6R2A3S2fVsegs;R14SdR3A1M3R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;Fw1;Frho1;SbS34SbR1R9A3S34SbR2R9A3F_;FL;S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RbA3S1dS35RaS15G0S23RfS24ReRdA2A4R1A3S1dS4G2R10R2A3S2fVsegs;R13G3R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;F_;F_;Ffirst;Fleaves;Fleaves';Fmd;Fms;Ftr;Frho;FS';FS;FJ;").
Proof using .
  intros J S S' rho tr ms md leaves' leaves first Hst Hk Hsm Hnr IH Hsub.
  destruct (next_rel_wstep S S' rho tr ms md Hsm Hnr) as (ms' & rho1 & Hw & _ & Hag1 & Hle & Hsm1).
  assert (Hsp1 : SPJ segs J S' rho1 (tr, mkCfg ms' md)) by (split; [exact Hsm1 | eapply Hst; eauto]).
  destruct (IH rho1 (tr, mkCfg ms' md) Hsp1) as (L & rho' & w' & Hin & Hr & Hag2 & Hsp').
  exists L, rho', w'. split; [apply Hsub; exact Hin|].
  split; [eapply wreach_cons; [exact Hw | exact Hr]|].
  split; [|exact Hsp'].
  eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [exact Hle | exact Hag2].
Qed.

Lemma sym_run_complete_genJ : ltac2:(tb__ "0|1|
S18S12S2dA1S30S1S13S12SbA1M0S0S6S1fS13S3R5A1S14A3S31S2R6A1R7A2S1fS16G0A1ScVsegs;RaR9R7R6A5S17G0R5A2A3S2fVsegs;R9R8R5R4A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RaA3S1dS35RbR8R1A3S1dS4S2RcA1R9R2A3S2fVsegs;RdSdR3A1R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Frho;Fleaves;Ffirst;FS;FJ;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts J. induction fuel as [|fuel IH]; intros S first leaves rho w Hlen Hst Hrun Hsp.
  - cbn in Hrun. destruct first; [discriminate|].
    injection Hrun as Hl. subst leaves.
    exists (mkLeaf S RsFuel), rho, w. split; [left; reflexivity|].
    split; [apply wreach_refl_false|]. split; [apply agree_below_refl | exact Hsp].
  - cbn [sym_run] in Hrun.
    assert (Hleaf : forall r, leaves = [mkLeaf S r] -> first = false ->
              exists L rho' w', In L leaves /\ wreach first w w'
                /\ agree_below (ss_next S) rho rho' /\ SPJ segs J (lf_state L) rho' w').
    { intros r Hl Hf. subst leaves first.
      exists (mkLeaf S r), rho, w. split; [left; reflexivity|].
      split; [apply wreach_refl_false|]. split; [apply agree_below_refl | exact Hsp]. }
    destruct (negb first && memZ (ss_pc S) cuts)%bool eqn:Hcut.
    + destruct first; [discriminate|]. injection Hrun as Hl. eapply Hleaf; [symmetry; exact Hl | reflexivity].
    + destruct w as [tr [ms md]]. pose proof Hsp as [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
      pose proof (sym_step_sound segs S rho tr ms md Hsm) as X.
      pose proof (sym_step_lenient segs S) as HL0.
      pose proof (sym_step_next segs S) as HN0.
      destruct (sym_step segs S) as [S'|S1 S2|r] eqn:Hss.
      * apply (step_rel_strict segs _ _ _ _ _ _ Hlen) in X.
        eapply (complete_via_nextJ J S S' rho tr ms md leaves leaves first Hst Hk Hsm X); [|intros L HL; exact HL].
        intros rho1 w1 Hsp1. exact (IH S' false leaves rho1 w1 ltac:(rewrite HL0; exact Hlen) (stableJ_mono _ _ _ HN0 Hst) Hrun Hsp1).
      * destruct (sym_run segs fuel cuts S1 false) as [l1|] eqn:H1; [|discriminate].
        destruct (sym_run segs fuel cuts S2 false) as [l2|] eqn:H2; [|discriminate].
        injection Hrun as Hl. subst leaves. destruct HL0 as [HL1 HL2]. destruct HN0 as [HN1 HN2].
        destruct X as [X|X].
        -- eapply (complete_via_nextJ J S S1 rho tr ms md l1 (l1 ++ l2) first Hst Hk Hsm X).
           ++ intros rho1 w1 Hsp1. exact (IH S1 false l1 rho1 w1 ltac:(rewrite HL1; exact Hlen) (stableJ_mono _ _ _ HN1 Hst) H1 Hsp1).
           ++ intros L HL. apply in_or_app. left. exact HL.
        -- eapply (complete_via_nextJ J S S2 rho tr ms md l2 (l1 ++ l2) first Hst Hk Hsm X).
           ++ intros rho1 w1 Hsp1. exact (IH S2 false l2 rho1 w1 ltac:(rewrite HL2; exact Hlen) (stableJ_mono _ _ _ HN2 Hst) H2 Hsp1).
           ++ intros L HL. apply in_or_app. right. exact HL.
      * destruct first; [discriminate|]. injection Hrun as Hl. eapply Hleaf; [symmetry; exact Hl | reflexivity].
Qed.

Lemma sym_run_complete_gen : ltac2:(tb__ "0|1|
S18S12S2dA1S12S2bA1S2aOF_;F_;S1S13S12SbA1M0S0S6S1fS13S3R5A1S14A3S1fS16G0A1ScVsegs;R9R8R6R5A5S17G0R4A2A3S2eVsegs;R8R7R4R3A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3R9A3S1dS35RaR7R1A3S1dS4S2RbA1R8R2A3S2eVsegs;RcSdR3A1R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;Fw;Frho;Fleaves;Ffirst;FS;FK;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts K S first leaves rho w Hlen Hrun Hsp.
  exact (sym_run_complete_genJ fuel cuts (liftK K) S first leaves rho w Hlen (stableJ_liftK _ K) Hrun Hsp).
Qed.

Theorem sym_run_completeJ : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S30S0S6S1fS13S3R5A1S14A3S31S2R6A1R4A2S1fS16G0A1ScVsegs;R9R8R7S19A5S17G0R6A2A3S2fVsegs;R6R8R5R4A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RbA3S1dS8Vsegs;R8R1A3S1dS4S2RcA1R9R2A3S2fVsegs;RaSdR3A1R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Frho;FJ;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves J rho w Hlen Hst Hrun Hsp.
  destruct (sym_run_complete_genJ fuel cuts J S true leaves rho w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  exists L, rho', w'. split; [exact Hin|]. split; [eapply wreach_wsteps; exact Hr|]. split; assumption.
Qed.

Theorem sym_run_complete : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S12S2bA1S2aOF_;F_;S0S6S1fS13S3R5A1S14A3S1fS16G0A1ScVsegs;R8R7R6S19A5S17G0R5A2A3S2eVsegs;R5R7R4R3A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RaA3S1dS8Vsegs;R7R1A3S1dS4S2RbA1R8R2A3S2eVsegs;R9SdR3A1R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;Fw;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho w Hlen Hrun Hsp.
  exact (sym_run_completeJ fuel cuts S leaves (liftK K) rho w Hlen (stableJ_liftK _ K) Hrun Hsp).
Qed.

Theorem sym_run_complete_plus : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S12S2bA1S2aOF_;F_;S0S6S1fS13S3R5A1S14A3S1fS16G0A1ScVsegs;R8R7R6S19A5S17G0R5A2A3S2eVsegs;R5R7R4R3A5S1eSbSbS1eS0S0S1eS6S6S1eS6S6S1dS34SbR4RbA3S1dS7Vsegs;R8R2A3S1dS8Vsegs;R2R1A3S1dS4S2RcA1R9R3A3S2eVsegs;RaSdR4A1R3R1A5A2A2A2A2Lw';A2Lw1;A2Lrho';A2LL;A2F_;F_;F_;Fw;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho w Hlen Hrun Hsp.
  destruct (sym_run_complete_gen fuel cuts K S true leaves rho w Hlen Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  destruct Hr as (w1 & Hw1 & Hr). exists L, rho', w1, w'.
  split; [exact Hin|]. split; [exact Hw1|]. split; [exact Hr|]. split; [exact Hag | exact Hsp'].
Qed.

Theorem sym_run_complete_first_falseJ : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S30S0S6S1fS13S3R5A1S14A3S31S2R6A1R4A2S1fS16G0A1ScVsegs;R9R8R7S14A5S17G0R6A2A3S2fVsegs;R6R8R5R4A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RbA3S1dS8Vsegs;R8R1A3S1dS4S2RcA1R9R2A3S2fVsegs;RaSdR3A1R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Frho;FJ;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves J rho w Hlen Hst Hrun Hsp.
  destruct (sym_run_complete_genJ fuel cuts J S false leaves rho w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  exists L, rho', w'. split; [exact Hin|]. split; [exact Hr|]. split; assumption.
Qed.

Theorem sym_run_complete_first_false : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S12S2bA1S2aOF_;F_;S0S6S1fS13S3R5A1S14A3S1fS16G0A1ScVsegs;R8R7R6S14A5S17G0R5A2A3S2eVsegs;R5R7R4R3A5S1eSbSbS1eS0S0S1eS6S6S1dS34SbR3RaA3S1dS8Vsegs;R7R1A3S1dS4S2RbA1R8R2A3S2eVsegs;R9SdR3A1R2R1A5A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;Fw;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho w Hlen Hrun Hsp.
  exact (sym_run_complete_first_falseJ fuel cuts S leaves (liftK K) rho w Hlen (stableJ_liftK _ K) Hrun Hsp).
Qed.

Theorem sym_run_etripleJ : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S30S0S1fS13S3R4A1S14A3S31S2R5A1R3A2S1fS16G0A1ScVsegs;R8R7R6S19A5S17G0R5A2A3S9Vsegs;S2fVsegs;R5R7R4A4S33Vsegs;R5S2R7A1R4R6A5A3F_;F_;F_;Frho;FJ;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves J rho Hlen Hst Hrun w Hsp.
  destruct (sym_run_completeJ fuel cuts S leaves J rho w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & [Hsm' Hk']).
  exists w'. split; [exact Hr|]. exists L, rho'.
  split; [exact Hin|]. split; [exact Hag|]. split; [exact Hsm' | exact Hk'].
Qed.

Theorem sym_run_etriple : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S12S2bA1S2aOF_;F_;S0S1fS13S3R4A1S14A3S1fS16G0A1ScVsegs;R7R6R5S19A5S17G0R4A2A3S9Vsegs;S2eVsegs;R4R6R3A4S32Vsegs;R4S2R6A1R3R5A5A3F_;F_;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Hlen Hrun.
  exact (sym_run_etripleJ fuel cuts S leaves (liftK K) rho Hlen (stableJ_liftK _ K) Hrun).
Qed.

Theorem sym_run_etriple_first_falseJ : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S30S0S1fS13S3R4A1S14A3S31S2R5A1R3A2S1fS16G0A1ScVsegs;R8R7R6S14A5S17G0R5A2A3S9Vsegs;S2fVsegs;R5R7R4A4S33Vsegs;R5S2R7A1R4R6A5A3F_;F_;F_;Frho;FJ;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves J rho Hlen Hst Hrun w Hsp.
  destruct (sym_run_complete_first_falseJ fuel cuts S leaves J rho w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & [Hsm' Hk']).
  exists w'. split; [exact Hr|]. exists L, rho'.
  split; [exact Hin|]. split; [exact Hag|]. split; [exact Hsm' | exact Hk'].
Qed.

Theorem sym_run_etriple_first_false : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S12S2bA1S2aOF_;F_;S0S1fS13S3R4A1S14A3S1fS16G0A1ScVsegs;R7R6R5S14A5S17G0R4A2A3S9Vsegs;S2eVsegs;R4R6R3A4S32Vsegs;R4S2R6A1R3R5A5A3F_;F_;Frho;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K rho Hlen Hrun.
  exact (sym_run_etriple_first_falseJ fuel cuts S leaves (liftK K) rho Hlen (stableJ_liftK _ K) Hrun).
Qed.

Theorem sym_run_etriple_ex : ltac2:(tb__ "0|1|
S18S12S2dA1S1S12SbA1M0S12S2bA1S2aOF_;F_;S1fS13S3R3A1S14A3S1fS16G0A1ScVsegs;R6R5R4S19A5S17G0R3A2A3S9Vsegs;S6S1eS0S0S2eVsegs;R5R7R1R2A5Lrho;A2Lw;S6S1eS0S0S32Vsegs;R5S2R7A1R1R6R2A6Lrho;A2Lw;A3F_;F_;FK;Fleaves;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S leaves K Hlen Hrun. apply etriple_ex. intros rho.
  eapply etriple_conseq; [intros w Hw; exact Hw | | eapply sym_run_etriple; [exact Hlen | exact Hrun]].
  intros w Hq. exists rho. exact Hq.
Qed.

Corollary sym_run_complete_single : ltac2:(tb__ "0|1|
S18S12S2dA1S1S1SfS12S2bA1S2aOF_;F_;S0S6S1fS13S3R6A1S14A3S1fS16S12SbA1M0A1ScVsegs;R9R8R7S19A5S17G0S1bSbS11R6R5A2S1cSbA1A3A2A3S2eVsegs;R5R8R4R3A5S1eS0S0S1eS6S6S1dS8Vsegs;R6R1A3S1dS4S2RbA1R7R2A3S2eVsegs;R8RaR2R1A5A2A2Lw';A2Lrho';A2F_;F_;F_;Fw;Frho;FK;Fr;FS1;FS;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts S S1 r K rho w Hlen Hrun Hsp.
  destruct (sym_run_complete fuel cuts S [mkLeaf S1 r] K rho w Hlen Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  destruct Hin as [Hin | Hin]; [|destruct Hin]. subst L. cbn [lf_state] in Hsp'.
  exists rho', w'. split; [exact Hr|]. split; [exact Hag | exact Hsp'].
Qed.

Lemma sym_step_complete : ltac2:(tb__ "0|3|
S1S0S12S2bA1M0S25S2aS1fS13S3R5A1S14A3S5Vsegs;R5R6S15G0S23R4S24R3R2A2A4A4SeOLx;S10Vsegs;R7A2S1S1eS25S25S1eS0S0S1dS7Vsegs;S15G0S23R8S24R7R6A2A4S15G0S23R8S24R2R6A2A4M1A3S1dS4S2RaA1R9R1A3S5Vsegs;R1R3G1A4A2A2Lrho';A2Lms';A2LS';S1S1S1eS25S25S1eS0S0S1dS7Vsegs;S15G0S23R9S24R8R7A2A4S15G0S23R9S24R2R7A2A4M2A3S1dS4S2RbA1RaR1A3S22S5Vsegs;R1R4G2A4S5Vsegs;R1R3G2A4A2A2A2Lrho';A2Lms';A2LS2;LS1;SfS20Lr;Xex3F_;F_;Fmd;Fms;Ftr;Frho;FS;").
Proof using .
  intros S rho tr ms md Hlen Hsm.
  pose proof (sym_step_sound segs S rho tr ms md Hsm) as X.
  destruct (sym_step segs S) as [S'|S1 S2|r].
  - apply (step_rel_strict segs _ _ _ _ _ _ Hlen) in X.
    destruct (next_rel_wstep S S' rho tr ms md Hsm X) as (ms' & rho' & Hw & _ & Hag & _ & Hsm').
    exists ms', rho'. split; [exact Hw|]. split; [exact Hag | exact Hsm'].
  - destruct X as [X|X].
    + destruct (next_rel_wstep S S1 rho tr ms md Hsm X) as (ms' & rho' & Hw & _ & Hag & _ & Hsm').
      exists ms', rho'. split; [exact Hw|]. split; [exact Hag|]. left. exact Hsm'.
    + destruct (next_rel_wstep S S2 rho tr ms md Hsm X) as (ms' & rho' & Hw & _ & Hag & _ & Hsm').
      exists ms', rho'. split; [exact Hw|]. split; [exact Hag|]. right. exact Hsm'.
  - exact I.
Qed.

End C.
