(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "agree_below"; "ss_lenient"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "la_state"; "step_outA"; "sym_stepA"; "mkLeafA"; "sym_runA_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wsteps"; "wstep"; "etriple"; "@Corelib.Init.Datatypes"; "list"; "bool"; "false"; "pair"; "Some"; "nat"; "option"; "true"; "cons"; "nil"; "@Corelib.Init.Logic"; "and"; "ex"; "eq"; "True"; "False"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "smatchA"; "LQA"; "linpath"; "vnext_rel"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete"; "wreach"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "stop_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundW SymSoundR SymComplete SymFrame SymEntail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section C.
Variable segs : list Segment.

Lemma wstep_det_smatchA : ltac2:(tb__ "0|2|
S6S0S11S28Q40A1A1S11S2fA1M0S2dS2eSdSdS1dS12S3S5R8A1A1S13A3S24Vsegs;R8R7R9S14G0S29R6S2aR5R4A2A4A5S9OLx;SaVsegs;RaA2S6S1eLA';S6S6S1eLA2;LA1;M1G1S31S1fLr;X9x4SfVsegs;S14G0S29R8S2aR7R6A2A4R5A3SfVsegs;S14G0S29R9S2aR8R7A2A4R5A3S1dSdR7R6A3F_;F_;F_;F_;F_;Fw2;Fw1;Fmd;Fms;Ftr;Ftp;Frho;FA;").
Proof using .
  intros A rho tp tr ms md w1 w2 Hlen Hsm Hprog Hw1 Hw2.
  pose proof (sym_step_soundA segs A rho tp tr ms md Hlen Hsm) as X.
  destruct (sym_stepA segs A) as [A'|A1 A2|A1 A2|r].
  - destruct (vnext_rel_wstep segs A A' rho tp tr ms md Hsm X) as (ms' & md' & rho' & _ & Huniq & _).
    rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
  - destruct X as [X|X].
    + destruct (vnext_rel_wstep segs A A1 rho tp tr ms md Hsm X) as (ms' & md' & rho' & _ & Huniq & _).
      rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
    + destruct (vnext_rel_wstep segs A A2 rho tp tr ms md Hsm X) as (ms' & md' & rho' & _ & Huniq & _).
      rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
  - destruct X as [X|X].
    + destruct (vnext_rel_wstep segs A A1 rho tp tr ms md Hsm X) as (ms' & md' & rho' & _ & Huniq & _).
      rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
    + destruct (vnext_rel_wstep segs A A2 rho tp tr ms md Hsm X) as (ms' & md' & rho' & _ & Huniq & _).
      rewrite (Huniq w1 Hw1), (Huniq w2 Hw2). reflexivity.
  - destruct Hprog.
Qed.

Lemma complete_via_nextA : ltac2:(tb__ "0|4|
S22S6S6S0S11S28Q40A1A1S11S2fA1M0S2dS2eS11S4A1M1G1S12S23Vsegs;S1S5RaA1A1RbA3RcR9R8R7R5A4S24Vsegs;RaR9RcS14G0S29R8S2aR7R6A2A4A5S27Vsegs;RdRcRbRaR9R8R7A8S0SdS21Vsegs;R11RfR2RdR1A6S1cS4S4S1cS0S0S1cSdSdS1bS2bS4R3RdA3S1bS30Vsegs;S13R5R1A4S1bS2S1S5R13A1A1M2R6R2A3S21Vsegs;R15S8R3A1M3R2R11R1A6A2A2A2Lw';A2Lrho';A2LL;A2F_;Fw1;Frho1;S4S2bS4R1R9A3S2bS4R2R9A3F_;FL;S1cS4S4S1cS0S0S1cSdSdS1bS2bS4R3RbA3S1bS30Vsegs;RaS14G0S29RfS2aReRdA2A4R1A4S1bS2G2R11R2A3S21Vsegs;R14G3R2R10R1A6A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;F_;F_;Ffirst;Fleaves;Fleaves';Fmd;Fms;Ftr;Ftp;Frho;FA';FA;FJ;").
Proof using .
  intros J A A' rho tp tr ms md leaves' leaves first Hst Hk Hsm Hnr IH Hsub.
  destruct (vnext_rel_wstep segs A A' rho tp tr ms md Hsm Hnr) as (ms' & md' & rho1 & Hw & _ & Hag1 & Hle & Hsm1 & Hme).
  assert (Hsp1 : SPA segs J A' rho1 tp (tr, mkCfg ms' md')) by (split; [exact Hsm1 | eapply Hst; eauto]).
  destruct (IH rho1 (tr, mkCfg ms' md') Hsp1) as (L & rho' & w' & Hin & Hr & Hag2 & Hsp').
  exists L, rho', w'. split; [apply Hsub; exact Hin|].
  split; [eapply wreach_cons; [exact Hw | exact Hr]|].
  split; [|exact Hsp'].
  eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [exact Hle | exact Hag2].
Qed.

Lemma linpath_complete : ltac2:(tb__ "0|0|
S22S6S6S0S11S28Q40A1A1SdS26Vsegs;R5R4A3S1dS12S3S5R6A1A1S13A3S23Vsegs;S1S5R7A1A1R8A3S21Vsegs;R9R8R6R5R4A6S1cS0S0S1cSdSdS1bSeVsegs;R7R1A3S1bS2S1S5RbA1A1R9R2A3S21Vsegs;RcRaR2R8R1A6A2A2Lw';A2Lrho';A2F_;F_;F_;F_;Fw;Ftp;Frho;FB;FA;FJ;").
Proof using .
  intros J A B rho tp w Hl. revert rho w. induction Hl as [A | A A' B Hs Hl IH]; intros rho w Hlen Hst Hsp.
  - exists rho, w. split; [apply wsteps_refl|]. split; [apply agree_below_refl | exact Hsp].
  - pose proof (sym_stepA_kept segs A) as K. rewrite Hs in K. destruct K as (K1 & K2 & _).
    destruct w as [tr [ms md]]. destruct Hsp as [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
    pose proof (sym_step_soundA segs A rho tp tr ms md Hlen Hsm) as X. rewrite Hs in X.
    destruct (vnext_rel_wstep segs A A' rho tp tr ms md Hsm X) as (ms' & md' & rho1 & Hw & _ & Hag1 & Hle & Hsm1 & Hme).
    assert (Hsp1 : SPA segs J A' rho1 tp (tr, mkCfg ms' md')) by (split; [exact Hsm1 | eapply Hst; eauto]).
    destruct (IH rho1 (tr, mkCfg ms' md') ltac:(rewrite K2; exact Hlen) (stableA_mono _ _ _ _ K1 Hst) Hsp1) as (rho' & w' & Hws & Hag2 & Hsp').
    exists rho', w'. split; [eapply wsteps_step; [exact Hw | exact Hws]|]. split; [|exact Hsp'].
    eapply agree_below_trans; [exact Hag1|]. eapply agree_below_le; [exact K1 | exact Hag2].
Qed.

Lemma wreach_false_trans : ltac2:(tb__ "0|0|
S12SdSdSdS30Vsegs;R4R3R2A4SeVsegs;R3R2A3S30Vsegs;R6R5R3A4F_;F_;Fw';Fw1;Fw;Ffirst;").
Proof using .
  intros [|] w w1 w' H1 H2.
  - destruct H1 as (w0 & Hw0 & Hws). exists w0. split; [exact Hw0 | eapply wsteps_trans; eauto].
  - eapply wsteps_trans; eauto.
Qed.

Lemma sym_run_complete_genA_ref : ltac2:(tb__ "0|1|
S16S11S2cA1S22S6S12S11S4A1M0S0S11S28Q40A1A1SdS1dS12S3S5R6A1A1S13A3S23Vsegs;S1S5R7A1A1R8A3S1dS17G0A1ScVsegs;RbRaR8R7A5S15G0R6A2A3S21Vsegs;RaR9R6R5R4A6S1cS4S4S1cS0S0S1cSdSdS1bS2bS4R3RbA3S1bS30Vsegs;RcR8R1A4S1bS2S1S5RdA1A1RaR2A3S21Vsegs;ReS8R3A1R2R9R1A6A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Ftp;Frho;Fleaves;Ffirst;FA;FJ;Fcuts;Ffuel;").
Proof using .
  intros fuel. induction fuel as [|fuel IH]; intros cuts J A first leaves rho tp w Hlen Hst Hrun Hsp.
  - cbn in Hrun. destruct first; [discriminate|].
    injection Hrun as Hl. subst leaves.
    exists (mkLeafA A RsFuel), rho, w. split; [left; reflexivity|].
    split; [apply wreach_refl_false|]. split; [apply agree_below_refl | exact Hsp].
  - cbn [sym_runA_ref] in Hrun.
    assert (Hleaf : forall r, leaves = [mkLeafA A r] -> first = false ->
              exists L rho' w', In L leaves /\ wreach segs first w w'
                /\ agree_below (ss_next (ax_S A)) rho rho' /\ SPA segs J (la_state L) rho' tp w').
    { intros r Hl Hf. subst leaves first.
      exists (mkLeafA A r), rho, w. split; [left; reflexivity|].
      split; [apply wreach_refl_false|]. split; [apply agree_below_refl | exact Hsp]. }
    destruct (negb first && memZ (ss_pc (ax_S A)) cuts)%bool eqn:Hcut.
    + destruct first; [discriminate|]. injection Hrun as Hl. eapply Hleaf; [symmetry; exact Hl | reflexivity].
    + destruct w as [tr [ms md]]. pose proof Hsp as [Hsm Hk]. cbn [w_tr w_cfg fst snd cfg_model] in Hk.
      pose proof (sym_step_soundA segs A rho tp tr ms md Hlen Hsm) as X.
      pose proof (sym_stepA_kept segs A) as HK.
      assert (FORK : forall A1 A2,
                stepA_inv A A1 /\ stepA_inv A A2 ->
                (vnext_rel segs A A1 rho tp tr ms md \/ vnext_rel segs A A2 rho tp tr ms md) ->
                match sym_runA_ref segs fuel cuts A1 false, sym_runA_ref segs fuel cuts A2 false with
                | Some l1, Some l2 => Some (l1 ++ l2) | _, _ => None end = Some leaves ->
                exists L rho' w', In L leaves /\ wreach segs first (tr, mkCfg ms md) w'
                  /\ agree_below (ss_next (ax_S A)) rho rho' /\ SPA segs J (la_state L) rho' tp w').
      { intros A1 A2 [(HN1 & HL1 & _) (HN2 & HL2 & _)] XX Hr.
        destruct (sym_runA_ref segs fuel cuts A1 false) as [l1|] eqn:H1; [|discriminate].
        destruct (sym_runA_ref segs fuel cuts A2 false) as [l2|] eqn:H2; [|discriminate].
        injection Hr as Hl. subst leaves.
        destruct XX as [XX|XX].
        - eapply (complete_via_nextA J A A1 rho tp tr ms md l1 (l1 ++ l2) first Hst Hk Hsm XX).
          + intros rho1 w1 Hsp1. exact (IH cuts J A1 false l1 rho1 tp w1 ltac:(rewrite HL1; exact Hlen) (stableA_mono _ _ _ _ HN1 Hst) H1 Hsp1).
          + intros L HL. apply in_or_app. left. exact HL.
        - eapply (complete_via_nextA J A A2 rho tp tr ms md l2 (l1 ++ l2) first Hst Hk Hsm XX).
          + intros rho1 w1 Hsp1. exact (IH cuts J A2 false l2 rho1 tp w1 ltac:(rewrite HL2; exact Hlen) (stableA_mono _ _ _ _ HN2 Hst) H2 Hsp1).
          + intros L HL. apply in_or_app. right. exact HL. }
      destruct (sym_stepA segs A) as [A'|A1 A2|A1 A2|r] eqn:Hss.
      * destruct HK as (HN0 & HL0 & _).
        eapply (complete_via_nextA J A A' rho tp tr ms md leaves leaves first Hst Hk Hsm X); [|intros L HL; exact HL].
        intros rho1 w1 Hsp1. exact (IH cuts J A' false leaves rho1 tp w1 ltac:(rewrite HL0; exact Hlen) (stableA_mono _ _ _ _ HN0 Hst) Hrun Hsp1).
      * exact (FORK A1 A2 HK X Hrun).
      * destruct (try_join segs A A1 A2) as [M|] eqn:Htj; [|exact (FORK A1 A2 HK X Hrun)].
        destruct HK as [(Hle1 & Hl1 & _) (Hle2 & Hl2 & _)].
        destruct (try_join_spec segs A A1 A2 M Htj) as (B1 & B2 & HP1 & HP2 & HJ2).
        destruct (join2_spec _ _ _ _ _ HJ2) as (HXM & HbM & HlenM & HleM).
        assert (ARM : forall Ai Bi, vnext_rel segs A Ai rho tp tr ms md ->
                  (ss_next (ax_S A) <= ss_next (ax_S Ai))%positive -> ss_lenient (ax_S Ai) = ss_lenient (ax_S A) ->
                  linpath segs Ai Bi ->
                  (forall r w, SPA segs J Bi r tp w -> exists r', agree_below (ss_next (ax_S A)) r r' /\ SPA segs J M r' tp w) ->
                  exists L rho' w', In L leaves /\ wreach segs first (tr, mkCfg ms md) w'
                    /\ agree_below (ss_next (ax_S A)) rho rho' /\ SPA segs J (la_state L) rho' tp w').
        { intros Ai Bi XX HleI HlI HPI HBi.
          destruct (vnext_rel_wstep segs A Ai rho tp tr ms md Hsm XX) as (ms1 & md1 & rho1 & Hw1 & _ & Hag1 & _ & Hsm1 & Hme1).
          assert (Hsp1 : SPA segs J Ai rho1 tp (tr, mkCfg ms1 md1)) by (split; [exact Hsm1 | eapply Hst; eauto]).
          destruct (linpath_complete J Ai Bi rho1 tp _ HPI ltac:(rewrite HlI; exact Hlen) (stableA_mono _ _ _ _ HleI Hst) Hsp1)
            as (rho2 & w2 & Hws2 & Hag2 & Hsp2).
          destruct (HBi rho2 w2 Hsp2) as (rhoM & HagM & HspM).
          destruct (IH cuts J M false leaves rhoM tp w2 HlenM (stableA_mono _ _ _ _ HleM Hst) Hrun HspM)
            as (L & rho' & w' & HinL & Hr & Hag3 & Hsp').
          exists L, rho', w'. split; [exact HinL|]. split.
          { eapply wreach_false_trans; [eapply wreach_cons; [exact Hw1 | exact Hws2] | eapply wreach_wsteps; exact Hr]. }
          split; [|exact Hsp'].
          eapply agree_below_trans; [exact Hag1|].
          eapply agree_below_trans; [eapply agree_below_le; [exact HleI | exact Hag2]|].
          eapply agree_below_trans; [exact HagM | eapply agree_below_le; [exact HleM | exact Hag3]]. }
        destruct X as [X|X].
        -- apply (ARM A1 B1 X Hle1 Hl1 HP1). intros r w2 Hsp2. exact (join2_sound segs J _ A B1 B2 M r tp w2 HJ2 Hst (or_introl Hsp2)).
        -- apply (ARM A2 B2 X Hle2 Hl2 HP2). intros r w2 Hsp2. exact (join2_sound segs J _ A B1 B2 M r tp w2 HJ2 Hst (or_intror Hsp2)).
      * destruct first; [discriminate|]. injection Hrun as Hl. eapply Hleaf; [symmetry; exact Hl | reflexivity].
Qed.

Lemma sym_run_complete_genA : ltac2:(tb__ "0|1|
S16S11S2cA1S22S6S12S11S4A1M0S0S11S28Q40A1A1SdS1dS12S3S5R6A1A1S13A3S23Vsegs;S1S5R7A1A1R8A3S1dS17G0A1S7Vsegs;RbRaR8R7A5S15G0R6A2A3S21Vsegs;RaR9R6R5R4A6S1cS4S4S1cS0S0S1cSdSdS1bS2bS4R3RbA3S1bS30Vsegs;RcR8R1A4S1bS2S1S5RdA1A1RaR2A3S21Vsegs;ReS8R3A1R2R9R1A6A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Ftp;Frho;Fleaves;Ffirst;FA;FJ;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts J A first leaves rho tp w HL HS Hrun. rewrite sym_runA_ref_eq in Hrun.
  exact (sym_run_complete_genA_ref fuel cuts J A first leaves rho tp w HL HS Hrun).
Qed.

Theorem sym_run_completeA : ltac2:(tb__ "0|1|
S16S11S2cA1S6S11S4A1M0S22S0S11S28Q40A1A1SdS1dS12S3S5R6A1A1S13A3S23Vsegs;S1S5R7A1A1R5A3S1dS17G0A1S7Vsegs;RaR9R8S18A5S15G0R7A2A3S21Vsegs;R7R9R6R5R4A6S1cS4S4S1cS0S0S1cSdSdS1bS2bS4R3RcA3S1bSeVsegs;R8R1A3S1bS2S1S5RdA1A1RaR2A3S21Vsegs;RbS8R3A1R2R9R1A6A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp w Hlen Hst Hrun Hsp.
  destruct (sym_run_complete_genA fuel cuts J A true leaves rho tp w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  exists L, rho', w'. split; [exact Hin|]. split; [eapply wreach_wsteps; exact Hr|]. split; assumption.
Qed.

Theorem sym_run_complete_plusA : ltac2:(tb__ "0|1|
S16S11S2cA1S6S11S4A1M0S22S0S11S28Q40A1A1SdS1dS12S3S5R6A1A1S13A3S23Vsegs;S1S5R7A1A1R5A3S1dS17G0A1S7Vsegs;RaR9R8S18A5S15G0R7A2A3S21Vsegs;R7R9R6R5R4A6S1cS4S4S1cS0S0S1cSdSdS1cSdSdS1bS2bS4R4RdA3S1bSfVsegs;R9R2A3S1bSeVsegs;R2R1A3S1bS2S1S5ReA1A1RbR3A3S21Vsegs;RcS8R4A1R3RaR1A6A2A2A2A2Lw';A2Lw1;A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp w Hlen Hst Hrun Hsp.
  destruct (sym_run_complete_genA fuel cuts J A true leaves rho tp w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  destruct Hr as (w1 & Hw1 & Hr). exists L, rho', w1, w'.
  split; [exact Hin|]. split; [exact Hw1|]. split; [exact Hr|]. split; [exact Hag | exact Hsp'].
Qed.

Theorem sym_run_complete_first_falseA : ltac2:(tb__ "0|1|
S16S11S2cA1S6S11S4A1M0S22S0S11S28Q40A1A1SdS1dS12S3S5R6A1A1S13A3S23Vsegs;S1S5R7A1A1R5A3S1dS17G0A1S7Vsegs;RaR9R8S13A5S15G0R7A2A3S21Vsegs;R7R9R6R5R4A6S1cS4S4S1cS0S0S1cSdSdS1bS2bS4R3RcA3S1bSeVsegs;R8R1A3S1bS2S1S5RdA1A1RaR2A3S21Vsegs;RbS8R3A1R2R9R1A6A2A2A2Lw';A2Lrho';A2LL;A2F_;F_;F_;F_;Fw;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp w Hlen Hst Hrun Hsp.
  destruct (sym_run_complete_genA fuel cuts J A false leaves rho tp w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  exists L, rho', w'. split; [exact Hin|]. split; [exact Hr|]. split; assumption.
Qed.

Theorem sym_run_etripleA : ltac2:(tb__ "0|1|
S16S11S2cA1S6S11S4A1M0S22S0S11S28Q40A1A1S1dS12S3S5R5A1A1S13A3S23Vsegs;S1S5R6A1A1R4A3S1dS17G0A1S7Vsegs;R9R8R7S18A5S15G0R6A2A3S10Vsegs;S21Vsegs;R6R8R5R4A5S25Vsegs;R6S1S5R8A1A1R5R4R7A6A3F_;F_;F_;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp Hlen Hst Hrun w Hsp.
  destruct (sym_run_completeA fuel cuts A leaves J rho tp w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & [Hsm' Hk']).
  exists w'. split; [exact Hr|]. exists L, rho'.
  split; [exact Hin|]. split; [exact Hag|]. split; [exact Hsm' | exact Hk'].
Qed.

Theorem sym_run_etriple_first_falseA : ltac2:(tb__ "0|1|
S16S11S2cA1S6S11S4A1M0S22S0S11S28Q40A1A1S1dS12S3S5R5A1A1S13A3S23Vsegs;S1S5R6A1A1R4A3S1dS17G0A1S7Vsegs;R9R8R7S13A5S15G0R6A2A3S10Vsegs;S21Vsegs;R6R8R5R4A5S25Vsegs;R6S1S5R8A1A1R5R4R7A6A3F_;F_;F_;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp Hlen Hst Hrun w Hsp.
  destruct (sym_run_complete_first_falseA fuel cuts A leaves J rho tp w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & [Hsm' Hk']).
  exists w'. split; [exact Hr|]. exists L, rho'.
  split; [exact Hin|]. split; [exact Hag|]. split; [exact Hsm' | exact Hk'].
Qed.

Corollary sym_run_complete_singleA : ltac2:(tb__ "0|1|
S16S11S2cA1S6S6S31S22S0S11S28Q40A1A1SdS1dS12S3S5R7A1A1S13A3S23Vsegs;S1S5R8A1A1R5A3S1dS17S11S4A1M0A1S7Vsegs;RbRaR9S18A5S15G0S19S4SbR8R7A2S1aS4A1A3A2A3S21Vsegs;R7RaR6R5R4A6S1cS0S0S1cSdSdS1bSeVsegs;R7R1A3S1bS2S1S5RdA1A1R9R2A3S21Vsegs;RaRcR2R8R1A6A2A2Lw';A2Lrho';A2F_;F_;F_;F_;Fw;Ftp;Frho;FJ;Fr;FA1;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A A1 r J rho tp w Hlen Hst Hrun Hsp.
  destruct (sym_run_completeA fuel cuts A [mkLeafA A1 r] J rho tp w Hlen Hst Hrun Hsp) as (L & rho' & w' & Hin & Hr & Hag & Hsp').
  destruct Hin as [Hin | Hin]; [|destruct Hin]. subst L. cbn [la_state] in Hsp'.
  exists rho', w'. split; [exact Hr|]. split; [exact Hag | exact Hsp'].
Qed.

Lemma sym_step_completeA : ltac2:(tb__ "0|5|
S6S0S11S28Q40A1A1S11S2fA1M0S2dS2eS1dS12S3S5R6A1A1S13A3S24Vsegs;R6R5R7S14G0S29R4S2aR3R2A2M1A4A5S9OLx;SaVsegs;R8A2S6S1cS2dS2dS1cS2eS2eS1cS0S0S1bSfVsegs;S14G0S29R9S2aR8R7A2A4S14G0S29R9G1A4M2A3S1bS2S1S5RcA1A1RbR1A3S1bS24Vsegs;R1RaR4G2A5S32Vsegs;RaR7R2A4A2A2A2Lrho';A2Lmd';A2Lms';A2LA';S6S6S1cS2dS2dS1cS2eS2eS1cS0S0S1bSfVsegs;S14G0S29RaS2aR9R8A2A4S14G0S29RaG1A4M3A3S1bS2S1S5RdA1A1RcR1A3S1bS20S24Vsegs;R1RbR5G3A5S24Vsegs;R1RbR4G3A5A2S32Vsegs;RbR8R2A4A2A2A2Lrho';A2Lmd';A2Lms';A2LA2;LA1;M4G4S31S1eLr;X9x4F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FA;").
Proof using .
  intros A rho tp tr ms md Hlen Hsm.
  pose proof (sym_step_soundA segs A rho tp tr ms md Hlen Hsm) as X.
  destruct (sym_stepA segs A) as [A'|A1 A2|A1 A2|r].
  - destruct (vnext_rel_wstep segs A A' rho tp tr ms md Hsm X) as (ms' & md' & rho' & Hw & _ & Hag & _ & Hsm' & Hme).
    exists ms', md', rho'. split; [exact Hw|]. split; [exact Hag|]. split; [exact Hsm' | exact Hme].
  - destruct X as [X|X].
    + destruct (vnext_rel_wstep segs A A1 rho tp tr ms md Hsm X) as (ms' & md' & rho' & Hw & _ & Hag & _ & Hsm' & Hme).
      exists ms', md', rho'. split; [exact Hw|]. split; [exact Hag|]. split; [left; exact Hsm' | exact Hme].
    + destruct (vnext_rel_wstep segs A A2 rho tp tr ms md Hsm X) as (ms' & md' & rho' & Hw & _ & Hag & _ & Hsm' & Hme).
      exists ms', md', rho'. split; [exact Hw|]. split; [exact Hag|]. split; [right; exact Hsm' | exact Hme].
  - destruct X as [X|X].
    + destruct (vnext_rel_wstep segs A A1 rho tp tr ms md Hsm X) as (ms' & md' & rho' & Hw & _ & Hag & _ & Hsm' & Hme).
      exists ms', md', rho'. split; [exact Hw|]. split; [exact Hag|]. split; [left; exact Hsm' | exact Hme].
    + destruct (vnext_rel_wstep segs A A2 rho tp tr ms md Hsm X) as (ms' & md' & rho' & Hw & _ & Hag & _ & Hsm' & Hme).
      exists ms', md', rho'. split; [exact Hw|]. split; [exact Hag|]. split; [right; exact Hsm' | exact Hme].
  - exact I.
Qed.

End C.
