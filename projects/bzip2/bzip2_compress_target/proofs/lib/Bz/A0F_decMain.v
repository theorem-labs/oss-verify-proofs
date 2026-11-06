(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFA A0F_decV A0F_decRet A0F_decRet3 A0F_decCutsA A0F_decCuts4 A0F_decCuts5 A0F_decCuts6 A0F_decCuts7 A0F_decCutsM A0F_decCuts8 A0F_decCutsE A0F_decCuts12S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0F_dec_U13a A0F_dec_U2A A0F_dec_U2B A0F_dec_U3 A0F_dec_U4A A0F_dec_U4B A0F_dec_U4C A0F_dec_U5A A0F_dec_U5B A0F_dec_U5C A0F_dec_U6 A0F_dec_U7B A0F_dec_U7C A0F_dec_U7D A0F_dec_U7E A0F_dec_U8S A0F_dec_U9A A0F_dec_U9B A0F_dec_U10 A0F_dec_U11B A0F_dec_U12FB A0F_dec_U12SF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts12S.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Ltac use L := eapply L; try eassumption.

Section S.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETC : A0F_RETC A Q.

  (* [comment removed for export] *)
  Let HRET : A0F_RET A Q. Proof. use A0F_dec_U13a.A0F_ret_of_retc. Qed.
  Let HRETOK : A0F_RET_OK A Q. Proof. use A0F_dec_U13a.A0F_ret_ok_of_ret. Qed.
  Let HRETD : A0F_RET_DATA A Q. Proof. use A0F_dec_U13a.A0F_ret_data_of_ret. Qed.
  Let HRETD2 : A0F_RET_DATA2 A Q. Proof. use A0F_dec_U13a.A0F_ret_data2_of_retc. Qed.
  Let HRETP2 : A0F_RETP2 A Q. Proof. use A0F_dec_U13a.A0F_retp2_of_retc. Qed.
  Let HRETP3 : A0F_RETP3 A Q. Proof. use A0F_retp3_of_retc. Qed.

  (* [comment removed for export] *)
  Definition A0F_cuts1 (F : nat) : Prop := A0F_cut_H14 A Q F /\ A0F_cut_HEND A Q F /\ A0F_cut_HBCRC A Q F /\ A0F_cut_HMAP A Q F.
  Theorem A0F_seg1 : (forall F, A0F_call_MSI A Q F) -> forall F, A0F_cuts1 F.
  Proof.
    intros HMSI F. induction F as [F IH] using (well_founded_induction lt_wf).
    assert (PEND : forall F', (F' < F)%nat -> A0F_cut_HEND A Q F') by (intros F' H; exact (proj1 (proj2 (IH F' H)))).
    assert (PBCRC : forall F', (F' < F)%nat -> A0F_cut_HBCRC A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (IH F' H))))).
    assert (PMAP : forall F', (F' < F)%nat -> A0F_cut_HMAP A Q F') by (intros F' H; exact (proj2 (proj2 (proj2 (IH F' H))))).
    assert (PMSI : forall F', (F' < F)%nat -> A0F_call_MSI A Q F') by (intros F' _; apply HMSI).
    clear IH.
    assert (CMAP : A0F_cut_HMAP A Q F) by (apply (A0F_dec_U4A.A0F_dec_U4A A AOK ASH Q HRETOK F PMAP PMSI)).
    assert (CBCRC : A0F_cut_HBCRC A Q F) by (apply (A0F_dec_U2B.A0F_dec_U2B A AOK ASH Q HRETOK HRETP2 F PMAP)).
    assert (CEND : A0F_cut_HEND A Q F) by (apply (A0F_dec_U3.A0F_dec_U3 A AOK ASH Q HRETOK HRETD HRETD2 HRETC F)).
    assert (C14 : A0F_cut_H14 A Q F) by (apply (A0F_dec_U2A.A0F_dec_U2A A AOK ASH Q HRETOK HRETD HRETD2 F PEND PBCRC)).
    unfold A0F_cuts1. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition A0F_cuts2 (F : nat) : Prop :=
    A0F_cut_MSIR A Q F /\ A0F_cut_HMAP2I A Q F /\ A0F_cut_HMAP2 A Q F /\ A0F_cut_L5I A Q F /\ A0F_cut_L5O A Q F /\ A0F_cut_L6W A Q F /\
    A0F_cut_HCOD A Q F /\ A0F_cut_HHB A Q F /\ (forall t, A0F_cut_L7T A Q F t).
  Lemma A0F_L7T_all : (forall F t mn mx, A0F_call_HBC A Q F t mn mx) -> forall F t, A0F_cut_L7T A Q F t.
  Proof.
    intros HHBC F t. apply (A0F_dec_U7C.A0F_U7_T A AOK ASH Q F t). intros mn mx. apply (A0F_dec_U7B.A0F_U7_C1 A Q F t mn mx). apply HHBC.
  Qed.
  Theorem A0F_seg2 : (forall F t mn mx, A0F_call_HBC A Q F t mn mx) -> forall F, A0F_cuts2 F.
  Proof.
    intros HHBC F. induction F as [F IH] using (well_founded_induction lt_wf).
    assert (PMAP2I : forall F', (F' < F)%nat -> A0F_cut_HMAP2I A Q F') by (intros F' H; exact (proj1 (proj2 (IH F' H)))).
    assert (PMAP2 : forall F', (F' < F)%nat -> A0F_cut_HMAP2 A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (IH F' H))))).
    assert (PL5I : forall F', (F' < F)%nat -> A0F_cut_L5I A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (IH F' H)))))).
    assert (PL5O : forall F', (F' < F)%nat -> A0F_cut_L5O A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (IH F' H))))))).
    assert (PL6W : forall F', (F' < F)%nat -> A0F_cut_L6W A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (IH F' H)))))))).
    assert (PCOD : forall F', (F' < F)%nat -> A0F_cut_HCOD A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (IH F' H))))))))).
    clear IH.
    assert (CT : forall t, A0F_cut_L7T A Q F t) by (intros t; apply A0F_L7T_all; exact HHBC).
    assert (CHHB : A0F_cut_HHB A Q F) by (apply (A0F_dec_U7C.A0F_U7_pro A AOK ASH Q F); apply CT).
    assert (CCOD : A0F_cut_HCOD A Q F) by (apply (A0F_dec_U6.A0F_U6_T A AOK ASH Q HRETOK F PL6W CHHB)).
    assert (CL6W : A0F_cut_L6W A Q F) by (apply (A0F_dec_U6.A0F_U6_W A AOK ASH Q HRETOK HRETD F PL6W PCOD)).
    assert (CUND : A0F_cut_HUND A Q F) by (apply (A0F_dec_U5C.A0F_dec_U5C A AOK ASH Q F CCOD)).
    assert (CL5I : A0F_cut_L5I A Q F) by (apply (A0F_dec_U5B.A0F_U5_L5I A AOK ASH Q HRETOK HRETD2 F PL5I PL5O)).
    assert (CL5O : A0F_cut_L5O A Q F) by (apply (A0F_dec_U5B.A0F_U5_L5O A AOK ASH Q F CL5I CUND)).
    assert (CSEL : A0F_cut_HSEL A Q F) by (apply (A0F_dec_U5A.A0F_dec_U5A A AOK ASH Q HRETOK HRETD HRETP2 F PL5O)).
    assert (CMK : A0F_cut_HMK A Q F) by (apply (A0F_dec_U4C.A0F_dec_U4C A AOK ASH Q HRETD F CSEL)).
    assert (CMAP2I : A0F_cut_HMAP2I A Q F) by (apply (A0F_dec_U4B.A0F_U4_L2I A AOK ASH Q HRETOK F PMAP2I PMAP2)).
    assert (CMAP2 : A0F_cut_HMAP2 A Q F) by (apply (A0F_dec_U4B.A0F_dec_U4B A AOK ASH Q F CMAP2I CMK)).
    assert (CMSIR : A0F_cut_MSIR A Q F) by (apply (A0F_dec_U4A.A0F_dec_U4xm A Q F CMAP2)).
    unfold A0F_cuts2. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition A0F_cuts4 (F : nat) : Prop :=
    A0F_cut_MSUR A Q F /\ A0F_cut_SYM A Q F /\ A0F_cut_HRUN A Q F /\ A0F_cut_HRUNEND A Q F /\ A0F_cut_HMTF1 A Q F /\ A0F_cut_HEOB A Q F.
  Theorem A0F_seg4 :
    (forall F fa fb j5 sym unz ll16_0 ll4_0, A0F_call_IDXN A Q F fa fb j5 sym unz ll16_0 ll4_0) ->
    (forall F fa fb j5 sym unz ll16_0 ll4_0, A0F_call_IDXR A Q F fa fb j5 sym unz ll16_0 ll4_0) -> forall F, A0F_cuts4 F.
  Proof.
    intros HIN HIR F. induction F as [F IH] using (well_founded_induction lt_wf).
    assert (PSYM : forall F', (F' < F)%nat -> A0F_cut_SYM A Q F') by (intros F' H; exact (proj1 (proj2 (IH F' H)))).
    assert (PRUN : forall F', (F' < F)%nat -> A0F_cut_HRUN A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (IH F' H))))).
    assert (PEND2 : forall F', (F' < F)%nat -> A0F_cut_HRUNEND A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (IH F' H)))))).
    clear IH.
    assert (CSMALL : A0F_cut_HSMALL A Q F) by (apply (A0F_dec_U12SF.A0F_dec_U12S A AOK ASH Q F (HIN F) (HIR F))).
    assert (CFAST : A0F_cut_HFAST A Q F) by (apply (A0F_dec_U12FB.A0F_dec_U12F A AOK ASH Q HRETP3 F)).
    assert (CEOB : A0F_cut_HEOB A Q F) by (apply (A0F_dec_U11B.A0F_dec_U11 A AOK ASH Q HRETP3 F CFAST CSMALL)).
    destruct (A0F_dec_U8S.A0F_dec_U8 A AOK ASH Q HRETOK HRETP2 F PSYM PRUN PEND2 CEOB) as (CMTFC & CLIT & CMTFB & CRUN & CSYM & CRUNEND & CMTF1).
    { intros HC. apply (A0F_dec_U10.A0F_dec_U10 A AOK ASH Q HRETP2 F HC). }
    { intros HB. apply (A0F_dec_U9A.A0F_U9_HRUN A AOK ASH Q HRETP2 F HB). }
    { intros HS. apply (A0F_dec_U9B.A0F_U9_HRUNEND A AOK ASH Q HRETP2 F HS). }
    assert (CL7G : A0F_cut_L7G A Q F) by (apply (A0F_dec_U7E.A0F_U7_G A AOK ASH Q F CMTF1)).
    assert (CL7K : A0F_cut_L7K A Q F 15) by (apply (A0F_dec_U7D.A0F_U7_mtf A AOK ASH Q F CL7G)).
    assert (CMSUR : A0F_cut_MSUR A Q F) by (apply (A0F_dec_U7D.A0F_U7_M2 A AOK ASH Q F CL7K)).
    unfold A0F_cuts4. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem A0F_seg5N : forall F fa fb j5 sym unz ll16_0 ll4_0, A0F_cut_IDXNR A Q F fa fb j5 sym unz ll16_0 ll4_0.
  Proof. intros. apply (A0F_dec_U12SF.A0F_dec_U12S_retN A AOK ASH Q HRETP3). Qed.
  Theorem A0F_seg5R : forall F fa fb j5 sym unz ll16_0 ll4_0, A0F_cut_IDXRR A Q F fa fb j5 sym unz ll16_0 ll4_0.
  Proof. intros. apply (A0F_dec_U12SF.A0F_dec_U12S_retR A AOK ASH Q HRETP3). Qed.
End S.
End ACeilS1.
