(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs BzContracts BzContracts0 DecCut S0_dec_U13.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF S0F_decRet S0F_decCuts S0F_decCutsA S0F_decCuts4 S0F_decCuts6 S0F_decCuts7 S0F_decCutsM S0F_decCutsE S0F_dec_U2A S0F_dec_U2B S0F_dec_U3 S0F_dec_U4A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_dec_U4A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_dec_U4C S0F_dec_U5A S0F_dec_U5B S0F_dec_U5C S0F_dec_U6 S0F_dec_U7E S0F_dec_U8S S0F_dec_U9A S0F_dec_U9B S0F_dec_U10 S0F_dec_U11B S0F_dec_U12FB S0F_dec_U12SF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts7 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U2A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U2B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U4A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U4A.S0F_dec_U4B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U4C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U5A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U5B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U5C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U6 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U7E OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U8S OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U9A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U9B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U10 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U11B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12FB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_dec_U12SF.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition S0F_allcuts (A : act14) (F : nat) : Prop :=
  S0F_cut_H14 A F /\ S0F_cut_HEND A F /\ S0F_cut_HBCRC A F /\ S0F_cut_HMAP A F /\
  S0F_cut_HMAP2I A F /\ S0F_cut_HMAP2 A F /\ S0F_cut_HMK A F /\ S0F_cut_HSEL A F /\
  S0F_cut_L5I A F /\ S0F_cut_L5O A F /\ S0F_cut_HUND A F /\ S0F_cut_HCOD A F /\
  S0F_cut_L6T A F /\ S0F_cut_L6W A F /\ S0F_cut_HHB A F /\ S0F_cut_HMTF1 A F /\
  S0F_cut_SYM A F /\ S0F_cut_HLIT A F /\ S0F_cut_HMTFC A F /\ S0F_cut_HRUN A F /\
  S0F_cut_HMTFB A F /\ S0F_cut_HRUNEND A F /\ S0F_cut_HEOB A F.

Theorem S0F_dec_all : forall A, act_ok 320 A -> forall F, S0F_allcuts A F.
Proof.
  intros A AOK F. induction F as [F IH] using (well_founded_induction lt_wf).
  (* [comment removed for export] *)
  assert (P14 : forall F', (F' < F)%nat -> S0F_cut_H14 A F') by (intros F' H; exact (proj1 (IH F' H))).
  assert (PEND : forall F', (F' < F)%nat -> S0F_cut_HEND A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PBCRC : forall F', (F' < F)%nat -> S0F_cut_HBCRC A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PMAP : forall F', (F' < F)%nat -> S0F_cut_HMAP A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PMAP2I : forall F', (F' < F)%nat -> S0F_cut_HMAP2I A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PMAP2 : forall F', (F' < F)%nat -> S0F_cut_HMAP2 A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PL5I : forall F', (F' < F)%nat -> S0F_cut_L5I A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PL5O : forall F', (F' < F)%nat -> S0F_cut_L5O A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PL6T : forall F', (F' < F)%nat -> S0F_cut_L6T A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PL6W : forall F', (F' < F)%nat -> S0F_cut_L6W A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PSYM : forall F', (F' < F)%nat -> S0F_cut_SYM A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PRUN : forall F', (F' < F)%nat -> S0F_cut_HRUN A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  assert (PEND2 : forall F', (F' < F)%nat -> S0F_cut_HRUNEND A F')
    by (intros F' H; pose proof (IH F' H) as X; unfold S0F_allcuts in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; apply proj2 in X; first [exact (proj1 X) | exact X]).
  clear IH.
  (* [comment removed for export] *)
  pose proof (S0F_dec_U11 A AOK F (S0F_dec_U12F A AOK F) (S0F_dec_U12S A AOK F)) as CEOB.
  cps_destruct (S0F_dec_U8 A AOK F PSYM PRUN PEND2 CEOB (S0F_dec_U10 A AOK F) (S0F_dec_U9a A AOK F) (S0F_dec_U9b A AOK F))
    as (CMTFC & CLIT & CMTFB & CRUN & CSYM & CRUNEND & CMTF1).
  pose proof (S0F_dec_U7 A AOK F CMTF1) as CHHB.
  pose proof (S0F_U6_T A AOK F PL6W CHHB) as CL6T.
  pose proof (S0F_U6_W A AOK F PL6W PL6T) as CL6W.
  pose proof (S0F_L6T_HCOD A F CL6T) as CCOD.
  pose proof (S0F_dec_U5C A AOK F CCOD) as CUND.
  pose proof (S0F_U5_L5I A AOK F PL5I PL5O) as CL5I.
  pose proof (S0F_U5_L5O A AOK F CL5I CUND) as CL5O.
  pose proof (S0F_dec_U5A A AOK F PL5O) as CSEL.
  pose proof (S0F_dec_U4C A AOK F CSEL) as CMK.
  pose proof (S0F_U4_L2I A AOK F PMAP2I PMAP2) as CMAP2I.
  pose proof (S0F_dec_U4B A AOK F CMAP2I CMK) as CMAP2.
  pose proof (S0F_dec_U4A A AOK F PMAP PMAP2) as CMAP.
  pose proof (S0F_dec_U2B A AOK F PMAP) as CBCRC.
  pose proof (S0F_dec_U3 A AOK F) as CEND.
  pose proof (S0F_dec_U2A A AOK F PEND PBCRC) as C14.
  unfold S0F_allcuts. repeat split; assumption.
Qed.

Corollary S0F_dec_H14 : forall A, act_ok 320 A -> forall F, S0F_cut_H14 A F.
Proof. intros A AOK F. exact (proj1 (S0F_dec_all A AOK F)). Qed.

End ACeilS1.
