(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK DecCutFB B0F_decV B0F_decRet B0F_decCutsA B0F_decCuts4 B0F_decCuts5 B0F_decCuts6 B0F_decCuts7 B0F_decCutsM B0F_decCuts8 B0F_decCutsE B0F_decCuts12S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require B0F_dec_U13a B0F_dec_U2A B0F_dec_U2B B0F_dec_U3 B0F_dec_U4A B0F_dec_U4B B0F_dec_U4C B0F_dec_U5A B0F_dec_U5B B0F_dec_U5C B0F_dec_U6 B0F_dec_U7B B0F_dec_U7C B0F_dec_U7D B0F_dec_U7E B0F_dec_U8S B0F_dec_U9A B0F_dec_U9B B0F_dec_U10 B0F_dec_U11B B0F_dec_U12FB B0F_dec_U12SF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts8 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decCuts12S.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Ltac use L := eapply L; try eassumption.

Section S.
  Variable A : act14.
  Hypothesis AOK : act_ok BIHI0 A.
  Hypothesis ASH : act_sh DI_B0 A.
  Variable Q : dres -> machine_state -> Prop.
  Hypothesis HRETC : B0F_RETC A Q.

  (* [comment removed for export] *)
  Let HRET : B0F_RET A Q. Proof. use B0F_dec_U13a.B0F_ret_of_retc. Qed.
  Let HRETOK : B0F_RET_OK A Q. Proof. use B0F_dec_U13a.B0F_ret_ok_of_ret. Qed.
  Let HRETD : B0F_RET_DATA A Q. Proof. use B0F_dec_U13a.B0F_ret_data_of_ret. Qed.

  (* [comment removed for export] *)
  Definition B0F_cuts1 (F : nat) : Prop :=
    B0F_cut_H14 A Q F /\ B0F_cut_HEND A Q F /\ B0F_cut_HBCRC A Q F /\ B0F_cut_HMAP A Q F /\ B0F_cut_HMAP2I A Q F /\ B0F_cut_HMAP2 A Q F.
  Theorem B0F_seg1 : (forall F, B0F_call_MM A Q F) -> forall F, B0F_cuts1 F.
  Proof.
    intros HMM F. induction F as [F IH] using (well_founded_induction lt_wf).
    assert (PEND : forall F', (F' < F)%nat -> B0F_cut_HEND A Q F') by (intros F' H; exact (proj1 (proj2 (IH F' H)))).
    assert (PBCRC : forall F', (F' < F)%nat -> B0F_cut_HBCRC A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (IH F' H))))).
    assert (PMAP : forall F', (F' < F)%nat -> B0F_cut_HMAP A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (IH F' H)))))).
    assert (PMAP2I : forall F', (F' < F)%nat -> B0F_cut_HMAP2I A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (IH F' H))))))).
    assert (PMAP2 : forall F', (F' < F)%nat -> B0F_cut_HMAP2 A Q F') by (intros F' H; exact (proj2 (proj2 (proj2 (proj2 (proj2 (IH F' H))))))).
    clear IH.
    assert (PLZ : forall F', (F' < F)%nat -> B0F_cut_LZ A Q F' 0) by (intros F' H; apply (B0F_dec_U4A.B0F_U4_LZ A AOK ASH Q F'); apply PMAP2; exact H).
    assert (CMK : B0F_cut_HMK A Q F) by (apply (B0F_dec_U4C.B0F_dec_U4Cc A Q F); apply HMM).
    assert (CMAP2I : B0F_cut_HMAP2I A Q F) by (apply (B0F_dec_U4B.B0F_U4_L2I A AOK ASH Q HRETOK F PMAP2I PMAP2)).
    assert (CMAP2 : B0F_cut_HMAP2 A Q F) by (apply (B0F_dec_U4B.B0F_dec_U4B A AOK ASH Q F CMAP2I CMK)).
    assert (CMAP : B0F_cut_HMAP A Q F) by (apply (B0F_dec_U4A.B0F_dec_U4A A AOK ASH Q HRETOK F PMAP PLZ)).
    assert (CBCRC : B0F_cut_HBCRC A Q F) by (apply (B0F_dec_U2B.B0F_dec_U2B A AOK ASH Q HRETOK HRETD F PMAP)).
    assert (CEND : B0F_cut_HEND A Q F) by (apply (B0F_dec_U3.B0F_dec_U3 A AOK ASH Q HRETOK HRETD HRETC F)).
    assert (C14 : B0F_cut_H14 A Q F) by (apply (B0F_dec_U2A.B0F_dec_U2A A AOK ASH Q HRETOK HRETD F PEND PBCRC)).
    unfold B0F_cuts1. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition B0F_cuts2 (F : nat) : Prop :=
    B0F_cut_MMR A Q F /\ B0F_cut_HSEL A Q F /\ B0F_cut_L5I A Q F /\ B0F_cut_L5O A Q F /\ B0F_cut_L6W A Q F /\
    B0F_cut_HCOD A Q F /\ B0F_cut_HHB A Q F /\ (forall t, B0F_cut_L7T A Q F t).
  Lemma B0F_L7T_all : (forall F t mn mx, B0F_call_HBC A Q F t mn mx) -> forall F t, B0F_cut_L7T A Q F t.
  Proof.
    intros HHBC F t. apply (B0F_dec_U7C.B0F_U7_T A AOK ASH Q F t). intros mn mx. apply (B0F_dec_U7B.B0F_U7_C1 A AOK Q F t mn mx). apply HHBC.
  Qed.
  Theorem B0F_seg2 : (forall F t mn mx, B0F_call_HBC A Q F t mn mx) -> forall F, B0F_cuts2 F.
  Proof.
    intros HHBC F. induction F as [F IH] using (well_founded_induction lt_wf).
    assert (PL5I : forall F', (F' < F)%nat -> B0F_cut_L5I A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (IH F' H))))).
    assert (PL5O : forall F', (F' < F)%nat -> B0F_cut_L5O A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (IH F' H)))))).
    assert (PL6W : forall F', (F' < F)%nat -> B0F_cut_L6W A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (IH F' H))))))).
    assert (PCOD : forall F', (F' < F)%nat -> B0F_cut_HCOD A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (IH F' H)))))))).
    clear IH.
    assert (CT : forall t, B0F_cut_L7T A Q F t) by (intros t; apply B0F_L7T_all; exact HHBC).
    assert (CHHB : B0F_cut_HHB A Q F) by (apply (B0F_dec_U7C.B0F_U7_pro A AOK ASH Q F); apply CT).
    assert (CCOD : B0F_cut_HCOD A Q F) by (apply (B0F_dec_U6.B0F_U6_T A AOK ASH Q HRETOK F PL6W CHHB)).
    assert (CL6W : B0F_cut_L6W A Q F) by (apply (B0F_dec_U6.B0F_U6_W A AOK ASH Q HRETOK HRETD F PL6W PCOD)).
    assert (CUND : B0F_cut_HUND A Q F) by (apply (B0F_dec_U5C.B0F_dec_U5C A AOK ASH Q F CCOD)).
    assert (CL5I : B0F_cut_L5I A Q F) by (apply (B0F_dec_U5B.B0F_U5_L5I A AOK ASH Q HRETOK HRET F PL5I PL5O)).
    assert (CL5O : B0F_cut_L5O A Q F) by (apply (B0F_dec_U5B.B0F_U5_L5O A AOK ASH Q F CL5I CUND)).
    assert (CSEL : B0F_cut_HSEL A Q F) by (apply (B0F_dec_U5A.B0F_dec_U5A A AOK ASH Q HRETOK HRETD F PL5O)).
    assert (CMMR : B0F_cut_MMR A Q F) by (apply (B0F_dec_U4C.B0F_dec_U4Cr A AOK ASH Q HRETD F CSEL)).
    unfold B0F_cuts2. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition B0F_cuts4 (F : nat) : Prop :=
    B0F_cut_H7M A Q F /\ B0F_cut_SYM A Q F /\ B0F_cut_HRUN A Q F /\ B0F_cut_HRUNEND A Q F /\ B0F_cut_HMTF1 A Q F /\ B0F_cut_HEOB A Q F.
  Theorem B0F_seg4 :
    (forall F fa fb j5 sym unz ll16_0 ll4_0, B0F_call_IDXN A Q F fa fb j5 sym unz ll16_0 ll4_0) ->
    (forall F fa fb j5 sym unz ll16_0 ll4_0, B0F_call_IDXR A Q F fa fb j5 sym unz ll16_0 ll4_0) -> forall F, B0F_cuts4 F.
  Proof.
    intros HIN HIR F. induction F as [F IH] using (well_founded_induction lt_wf).
    assert (PSYM : forall F', (F' < F)%nat -> B0F_cut_SYM A Q F') by (intros F' H; exact (proj1 (proj2 (IH F' H)))).
    assert (PRUN : forall F', (F' < F)%nat -> B0F_cut_HRUN A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (IH F' H))))).
    assert (PEND2 : forall F', (F' < F)%nat -> B0F_cut_HRUNEND A Q F') by (intros F' H; exact (proj1 (proj2 (proj2 (proj2 (IH F' H)))))).
    clear IH.
    assert (CSMALL : B0F_cut_HSMALL A Q F) by (apply (B0F_dec_U12SF.B0F_dec_U12S A AOK ASH Q F (HIN F) (HIR F))).
    assert (CFAST : B0F_cut_HFAST A Q F) by (apply (B0F_dec_U12FB.B0F_dec_U12F A AOK ASH Q HRET F)).
    assert (CEOB : B0F_cut_HEOB A Q F) by (apply (B0F_dec_U11B.B0F_dec_U11 A AOK ASH Q HRET F CFAST CSMALL)).
    destruct (B0F_dec_U8S.B0F_dec_U8 A AOK ASH Q HRETOK HRET F PSYM PRUN PEND2 CEOB) as (CMTFC & CLIT & CMTFB & CRUN & CSYM & CRUNEND & CMTF1).
    { intros HC. apply (B0F_dec_U10.B0F_dec_U10 A AOK ASH Q HRET F HC). }
    { intros HB. apply (B0F_dec_U9A.B0F_U9_HRUN A AOK ASH Q HRET F HB). }
    { intros HS. apply (B0F_dec_U9B.B0F_U9_HRUNEND A AOK ASH Q HRET F HS). }
    assert (CL7G : B0F_cut_L7G A Q F) by (apply (B0F_dec_U7E.B0F_U7_G A AOK ASH Q F CMTF1)).
    assert (CL7K : B0F_cut_L7K A Q F 15) by (apply (B0F_dec_U7D.B0F_U7_mtf A AOK ASH Q F CL7G)).
    assert (CLZU : B0F_cut_LZU A Q F 0) by (apply (B0F_dec_U7D.B0F_U7_LZU A AOK ASH Q F CL7K)).
    assert (CH7M : B0F_cut_H7M A Q F) by (apply (B0F_dec_U7D.B0F_U7_M1 A AOK ASH Q F CLZU)).
    unfold B0F_cuts4. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem B0F_seg5N : forall F fa fb j5 sym unz ll16_0 ll4_0, B0F_cut_IDXNR A Q F fa fb j5 sym unz ll16_0 ll4_0.
  Proof. intros. apply (B0F_dec_U12SF.B0F_dec_U12S_retN A AOK ASH Q HRET). Qed.
  Theorem B0F_seg5R : forall F fa fb j5 sym unz ll16_0 ll4_0, B0F_cut_IDXRR A Q F fa fb j5 sym unz ll16_0 ll4_0.
  Proof. intros. apply (B0F_dec_U12SF.B0F_dec_U12S_retR A AOK ASH Q HRET). Qed.
End S.
End ACeilS1.
