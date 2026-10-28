(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Export X1nr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma lay_top_lo : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0x6e000 <= lo.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H0. Qed.
Lemma lay_top_ST : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0 < ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. exact (proj1 H1). Qed.
Lemma lay_top_OUT : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0x6e000 <= OUT.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H2. Qed.
Lemma lay_top_A : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0x6e000 <= A.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H3. Qed.
Lemma lay_top_D : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0 < D.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. exact (proj1 H4). Qed.

Lemma lay_win_ST : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= 0x10000 \/ 0x6e000 <= ST.
Proof. intros until usp. intros L. pose proof L as (H0 & H1 & _). unfold nb_win, NBSTATE_SIZEOF, NB_GLOBALS_TOP in H1. exact (proj2 H1). Qed.
Lemma lay_win_D : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> D + DSZ <= 0x10000 \/ 0x6e000 <= D.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 6%nat sfP_ as H0 H1 H2 H3 H4 _ | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & _) ]. unfold nb_win, NB_GLOBALS_TOP in H4. exact (proj2 H4). Qed.
Lemma lay_top_STEREO : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0x6e000 <= STEREO.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H5. Qed.
Lemma lay_top_ISV : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> 0x6e000 <= ISV.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H6. Qed.
Lemma lay_ST_stk : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= lo \/ lo + (usp - lo) <= ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H7. Qed.
Lemma lay_OUT_stk : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> OUT + 640 <= lo \/ lo + (usp - lo) <= OUT.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H8. Qed.
Lemma lay_ISV_stk : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ISV + 640 <= lo \/ lo + (usp - lo) <= ISV.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H9. Qed.
Lemma lay_A_stk : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> A + 48 <= lo \/ lo + (usp - lo) <= A.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H10. Qed.
Lemma lay_D_stk : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> D + DSZ <= lo \/ lo + (usp - lo) <= D.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H11. Qed.
Lemma lay_STEREO_stk : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> STEREO + 8 <= lo \/ lo + (usp - lo) <= STEREO.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H12. Qed.
Lemma lay_ST_OUT : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= OUT \/ OUT + 640 <= ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H13. Qed.
Lemma lay_ST_ISV : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= ISV \/ ISV + 640 <= ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H14. Qed.
Lemma lay_ST_A : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= A \/ A + 48 <= ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H15. Qed.
Lemma lay_ST_D : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= D \/ D + DSZ <= ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H16. Qed.
Lemma lay_ST_STEREO : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ST + 2968 <= STEREO \/ STEREO + 8 <= ST.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H17. Qed.
Lemma lay_OUT_ISV : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> OUT + 640 <= ISV \/ ISV + 640 <= OUT.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H18. Qed.
Lemma lay_OUT_A : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> OUT + 640 <= A \/ A + 48 <= OUT.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H19. Qed.
Lemma lay_OUT_D : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> OUT + 640 <= D \/ D + DSZ <= OUT.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H20. Qed.
Lemma lay_OUT_STEREO : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> OUT + 640 <= STEREO \/ STEREO + 8 <= OUT.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H21. Qed.
Lemma lay_ISV_A : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ISV + 640 <= A \/ A + 48 <= ISV.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H22. Qed.
Lemma lay_ISV_D : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ISV + 640 <= D \/ D + DSZ <= ISV.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H23. Qed.
Lemma lay_ISV_STEREO : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> ISV + 640 <= STEREO \/ STEREO + 8 <= ISV.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H24. Qed.
Lemma lay_A_STEREO : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> A + 48 <= STEREO \/ STEREO + 8 <= A.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H25. Qed.
Lemma lay_D_STEREO : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp -> D + DSZ <= STEREO \/ STEREO + 8 <= D.
Proof. intros until usp. intros L. pose proof L as sfP_; first [ sf_destruct 27%nat sfP_ as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 | sf_fb; destruct sfP_ as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) ]. unfold apart, NBSTATE_SIZEOF, BITS_SIZEOF, NB_GLOBALS_TOP in *. exact H26. Qed.

Lemma lay_tops : forall ST OUT A D DSZ STEREO ISV lo usp, nb_layout ST OUT A D DSZ STEREO ISV lo usp ->
0x6e000 <= lo /\ 0 < ST /\ 0x6e000 <= OUT /\ 0x6e000 <= A /\ 0 < D /\ 0x6e000 <= STEREO /\ 0x6e000 <= ISV.
Proof.
intros until usp. intros L. repeat split;
[eapply lay_top_lo | eapply lay_top_ST | eapply lay_top_OUT | eapply lay_top_A | eapply lay_top_D | eapply lay_top_STEREO | eapply lay_top_ISV]; exact L.
Qed.

Ltac nb_base e :=
lazymatch e with
| Z.add ?x _ => nb_base x
| Z.sub ?x _ => nb_base x
| _ => e
end.

Ltac nb_class st out a d ster isv b :=
match b with
| _ => let x := match goal with |- _ => constr_eq b st end in constr:(1%nat)
| _ => let x := match goal with |- _ => constr_eq b out end in constr:(2%nat)
| _ => let x := match goal with |- _ => constr_eq b isv end in constr:(3%nat)
| _ => let x := match goal with |- _ => constr_eq b a end in constr:(4%nat)
| _ => let x := match goal with |- _ => constr_eq b d end in constr:(5%nat)
| _ => let x := match goal with |- _ => constr_eq b ster end in constr:(6%nat)
| _ =>

let e := match goal with E : b = ?e |- _ => e end in
let b' := nb_base e in nb_class st out a d ster isv b'
| _ => constr:(0%nat)
end.
Ltac nb_pose_pair L c1 c2 :=
lazymatch c1 with
| 1%nat => lazymatch c2 with
| 0%nat => pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ L); pose proof (lay_win_ST _ _ _ _ _ _ _ _ _ L) | 2%nat => pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ L)
| 3%nat => pose proof (lay_ST_ISV _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_ST_A _ _ _ _ _ _ _ _ _ L)
| 5%nat => pose proof (lay_ST_D _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_ST_STEREO _ _ _ _ _ _ _ _ _ L) end
| 2%nat => lazymatch c2 with
| 0%nat => pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ L) | 1%nat => pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ L)
| 3%nat => pose proof (lay_OUT_ISV _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_OUT_A _ _ _ _ _ _ _ _ _ L)
| 5%nat => pose proof (lay_OUT_D _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_OUT_STEREO _ _ _ _ _ _ _ _ _ L) end
| 3%nat => lazymatch c2 with
| 0%nat => pose proof (lay_ISV_stk _ _ _ _ _ _ _ _ _ L) | 1%nat => pose proof (lay_ST_ISV _ _ _ _ _ _ _ _ _ L)
| 2%nat => pose proof (lay_OUT_ISV _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_ISV_A _ _ _ _ _ _ _ _ _ L)
| 5%nat => pose proof (lay_ISV_D _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_ISV_STEREO _ _ _ _ _ _ _ _ _ L) end
| 4%nat => lazymatch c2 with
| 0%nat => pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ L) | 1%nat => pose proof (lay_ST_A _ _ _ _ _ _ _ _ _ L)
| 2%nat => pose proof (lay_OUT_A _ _ _ _ _ _ _ _ _ L) | 3%nat => pose proof (lay_ISV_A _ _ _ _ _ _ _ _ _ L)
| 6%nat => pose proof (lay_A_STEREO _ _ _ _ _ _ _ _ _ L) end
| 5%nat => lazymatch c2 with
| 0%nat => pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ L); pose proof (lay_win_D _ _ _ _ _ _ _ _ _ L) | 1%nat => pose proof (lay_ST_D _ _ _ _ _ _ _ _ _ L)
| 2%nat => pose proof (lay_OUT_D _ _ _ _ _ _ _ _ _ L) | 3%nat => pose proof (lay_ISV_D _ _ _ _ _ _ _ _ _ L)
| 6%nat => pose proof (lay_D_STEREO _ _ _ _ _ _ _ _ _ L) end
| 6%nat => lazymatch c2 with
| 0%nat => pose proof (lay_STEREO_stk _ _ _ _ _ _ _ _ _ L) | 1%nat => pose proof (lay_ST_STEREO _ _ _ _ _ _ _ _ _ L)
| 2%nat => pose proof (lay_OUT_STEREO _ _ _ _ _ _ _ _ _ L) | 3%nat => pose proof (lay_ISV_STEREO _ _ _ _ _ _ _ _ _ L)
| 4%nat => pose proof (lay_A_STEREO _ _ _ _ _ _ _ _ _ L) | 5%nat => pose proof (lay_D_STEREO _ _ _ _ _ _ _ _ _ L) end
| 0%nat => lazymatch c2 with
| 1%nat => pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ L); pose proof (lay_win_ST _ _ _ _ _ _ _ _ _ L) | 2%nat => pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ L)
| 3%nat => pose proof (lay_ISV_stk _ _ _ _ _ _ _ _ _ L) | 4%nat => pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ L)
| 5%nat => pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ L); pose proof (lay_win_D _ _ _ _ _ _ _ _ _ L) | 6%nat => pose proof (lay_STEREO_stk _ _ _ _ _ _ _ _ _ L) end
end.

Ltac nb_apart :=
match goal with
| L : nb_layout ?st ?out ?a ?d ?dsz ?ster ?isv ?lo ?usp |- (?x <= ?y \/ _)%Z =>
let bx := nb_base x in let by_ := nb_base y in
let c1 := nb_class st out a d ster isv bx in
let c2 := nb_class st out a d ster isv by_ in
nb_pose_pair L c1 c2
end.

Definition jboxed (P : Prop) : Prop := P.
Ltac nb_is_arith T :=
lazymatch T with
| (_ <= _)%Z => idtac | (_ < _)%Z => idtac | (_ <= _ <= _)%Z => idtac | (_ <= _ < _)%Z => idtac | (_ < _ <= _)%Z => idtac | (_ < _ < _)%Z => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | (_ <= _)%nat => idtac | (_ < _)%nat => idtac
| ((_ <= _)%Z /\ _) => idtac | ((_ < _)%Z /\ _) => idtac | (@eq Z _ _ /\ _) => idtac
| ((_ <= _)%Z \/ _) => idtac | ((_ < _)%Z \/ _) => idtac | (@eq Z _ _ \/ _) => idtac | (_ <> _) => idtac
end.
Ltac nb_keeper_base T :=
match T with
| (_ <= bv_unsigned _)%Z => idtac
| context [sb_buf_size _] => idtac
| (_ + _ <= _ \/ _ + _ <= _)%Z => idtac
| (_ <= ?v < _)%Z => is_var v | (_ <= ?v <= _)%Z => is_var v | (_ < ?v <= _)%Z => is_var v | (_ < ?v < _)%Z => is_var v
| (?v < _)%Z => is_var v | (?v <= _)%Z => is_var v
| (_ <= ?v)%Z => is_var v | (_ < ?v)%Z => is_var v
| @eq Z ?v _ => is_var v | @eq Z _ ?v => is_var v
| (?v < _)%nat => is_var v | (?v <= _)%nat => is_var v | (_ <= ?v < _)%nat => is_var v
| @eq nat ?v _ => is_var v | @eq nat _ ?v => is_var v
end.

Ltac nb_is_keeper T := nb_keeper_base T.
Ltac nb_box_junk :=
repeat match goal with H : ?T |- _ => nb_is_arith T; tryif nb_is_keeper T then fail else change T with (jboxed T) in H end.
Ltac nb_unbox_junk :=
repeat match goal with H : jboxed ?T |- _ => unfold jboxed in H end.

Ltac nb_in_goal e :=
first [ lazymatch goal with |- context [e] => idtac end
| match goal with
| H : @eq Z ?v ?rhs |- _ => is_var v; lazymatch goal with |- context [v] => idtac end; lazymatch rhs with context [e] => idtac end
| H : @eq nat ?a ?b |- _ => first [ lazymatch a with context [e] => idtac end | lazymatch b with context [e] => idtac end ]
end ].
Ltac nb_anchor_in_goal T :=
match T with
| context [length ?l] => nb_in_goal (length l)
| (?a <= ?e)%Z => is_Zlit_zb a; nb_in_goal e
| @eq Z (bv_unsigned ?e) _ => nb_in_goal e
| @eq Z ?e _ => tryif is_Zlit_zb e then fail else nb_in_goal e
| @eq Z _ ?e => tryif is_Zlit_zb e then fail else nb_in_goal e
end.
Ltac nb_unbox_anchored :=
repeat match goal with H : jboxed ?T |- _ => nb_anchor_in_goal T; unfold jboxed in H end.
Ltac nb_lia :=
nb_unbox_anchored;
first [ nb_apart; lia
| lia
| nb_unbox_junk; cbv delta [BITS_SIZEOF NBSTATE_SIZEOF] in *; lia ].
Ltac nb_conj :=
lazymatch goal with
| |- True => exact I
| |- _ /\ _ => split; [ nb_conj | nb_conj ]
| |- _ => nb_lia
end.

Ltac slia ::= cbv delta [BITS_SIZEOF NBSTATE_SIZEOF]; nb_conj.

Lemma zb8_eq : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.of_N]. exact H.
Qed.
Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte,
le4 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)) = [b0; b1; b2; b3].
Proof.
intros b0 b1 b2 b3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Z.mod_small by (cbn; lia).
cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
set (u := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
f_equal; [apply zb8_eq; subst u; symmetry; rewrite <- (Z.mod_small (bv_unsigned b0) 256) at 1 by lia; apply Z.mod_unique with (q:= bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3); [left; lia| lia] |].
f_equal; [apply zb8_eq; replace (u / 256) with (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)) by (subst u; apply Z.div_unique with (r := bv_unsigned b0); [left; lia|lia]);
symmetry; apply Z.mod_unique with (q := bv_unsigned b2 + 256 * bv_unsigned b3); [left; lia|lia] |].
f_equal; [apply zb8_eq; replace (u / 256 / 256) with (bv_unsigned b2 + 256 * bv_unsigned b3) by (subst u; rewrite Zdiv.Zdiv_Zdiv by lia; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1); [left; lia|lia]);
symmetry; apply Z.mod_unique with (q := bv_unsigned b3); [left; lia|lia] |].
f_equal. apply zb8_eq. replace (u / 256 / 256 / 256) with (bv_unsigned b3) by (subst u; rewrite !Zdiv.Zdiv_Zdiv by lia; apply Z.div_unique with (r := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2); [left; lia|lia]).
apply Z.mod_small. lia.
Qed.

Lemma bytes_are_f32 : forall (n : nat) (bs : list byte), length bs = (4 * n)%nat ->
exists ws, length ws = n /\ cells_bytes (f32 ws) = bs.
Proof.
induction n as [|n IH]; intros bs L.
- exists []. destruct bs; [split; reflexivity| cbn in L; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 bs]]]]; cbn in L; try lia.
destruct (IH bs ltac:(lia)) as (ws & Lw & E).
exists (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) :: ws).
split; [cbn; lia|]. rewrite f32_cons. cbn [cells_bytes cbytes]. rewrite le4_of_bytes, E. reflexivity.
Qed.

Lemma rw_cells_recast : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb'. split; [split; [exact Hwf'| rewrite Hb'; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), Hb', (cells_bytes_length cs Hwf). exact Hw.
Qed.
Lemma cells_wf_f32 : forall ws, cells_wf (f32 ws).
Proof. induction ws; cbn; [exact I| split; [exact I| exact IHws]]. Qed.

Lemma rw_cells_CB_f32 : forall segs m A (n : nat) bs,
rw_cells segs m A [CB (4 * n) bs] -> exists ws, length ws = n /\ rw_cells segs m A (f32 ws).
Proof.
intros segs m A n bs H.
assert (L : length bs = (4 * n)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (bytes_are_f32 n bs L) as (ws & Lw & E). exists ws. split; [exact Lw|].
eapply rw_cells_recast; [exact H| apply cells_wf_f32|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact E.
Qed.

Lemma rw_cells_f32_CB : forall segs m A ws,
rw_cells segs m A (f32 ws) -> rw_cells segs m A [CB (4 * length ws) (cells_bytes (f32 ws))].
Proof.
intros segs m A ws H. eapply rw_cells_recast; [exact H| |].
- cbn. split; [|exact I]. rewrite cells_bytes_length by apply cells_wf_f32. apply cells_size_f32.
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma rw_cells_f32_mid : forall segs m A ws i k,
rw_cells segs m A (f32 ws) -> (i <= length ws)%nat ->
rw_cells segs m (A + 4 * Z.of_nat i)%Z (f32 (firstn k (skipn i ws))).
Proof.
intros segs m A ws i k H Hi.
rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H. apply rw_cells_app in H. destruct H as [_ H].
rewrite cells_size_f32, firstn_length_le in H by exact Hi.
replace (Z.of_nat (4 * i)) with (4 * Z.of_nat i)%Z in H by lia.
rewrite <- (firstn_skipn k (skipn i ws)) in H. rewrite f32_app in H. apply rw_cells_app in H. destruct H as [H _]. exact H.
Qed.

Lemma f32_split : forall segs m A ws (i : nat), (i <= length ws)%nat ->
rw_cells segs m A (f32 ws) ->
rw_cells segs m A (f32 (firstn i ws)) /\ rw_cells segs m (A + 4 * Z.of_nat i) (f32 (skipn i ws)).
Proof.
intros segs m A ws i Hi H. rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H.
apply rw_cells_app in H. rewrite cells_size_f32, firstn_length_le in H by exact Hi.
replace (Z.of_nat (4 * i)) with (4 * Z.of_nat i)%Z in H by lia. exact H.
Qed.
Lemma f32_join : forall segs m A ws1 ws2,
rw_cells segs m A (f32 ws1) -> rw_cells segs m (A + 4 * Z.of_nat (length ws1)) (f32 ws2) ->
rw_cells segs m A (f32 (ws1 ++ ws2)).
Proof.
intros segs m A ws1 ws2 H1 H2. rewrite f32_app. apply rw_cells_join; [exact H1|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length ws1)) with (4 * Z.of_nat (length ws1))%Z by lia. exact H2.
Qed.

Definition w8 (b0 b1 b2 b3 b4 b5 b6 b7 : byte) : Z :=
bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 + 256 * bv_unsigned b7)))))).
Lemma Z_to_le_bytes_S : forall n z, Z_to_le_bytes (S n) z = Z_to_bv 8 z :: Z_to_le_bytes n (Z.shiftr z 8).
Proof. reflexivity. Qed.
Lemma zle_step : forall (b : byte) r n, 0 <= r ->
Z_to_le_bytes (S n) (bv_unsigned b + 256 * r) = b :: Z_to_le_bytes n r.
Proof.
intros b r n Hr. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
rewrite Z_to_le_bytes_S. f_equal.
- apply zb8_eq. symmetry. apply Z.mod_unique with (q := r); [left; lia| lia].
- f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. symmetry. apply Z.div_unique with (r := bv_unsigned b); [left; lia| lia].
Qed.
Lemma le8_of_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7 : byte,
le8 (Z_to_bv 64 (w8 b0 b1 b2 b3 b4 b5 b6 b7)) = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
intros.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
pose proof (bv_unsigned_in_range 8 b4) as R4. pose proof (bv_unsigned_in_range 8 b5) as R5.
pose proof (bv_unsigned_in_range 8 b6) as R6. pose proof (bv_unsigned_in_range 8 b7) as R7.
unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
rewrite Z.mod_small by (unfold w8; change (2 ^ Z.of_N 64) with 18446744073709551616; lia).
unfold w8.
rewrite (zle_step b0) by lia. rewrite (zle_step b1) by lia. rewrite (zle_step b2) by lia. rewrite (zle_step b3) by lia.
rewrite (zle_step b4) by lia. rewrite (zle_step b5) by lia. rewrite (zle_step b6) by lia.
replace (bv_unsigned b7) with (bv_unsigned b7 + 256 * 0) by lia. rewrite (zle_step b7) by lia. reflexivity.
Qed.
Lemma bytes_are_C8s : forall (n : nat) (bs : list byte), length bs = (8 * n)%nat ->
exists ws, length ws = n /\ cells_bytes (map C8 ws) = bs.
Proof.
induction n as [|n IH]; intros bs L.
- exists []. destruct bs; [split; reflexivity| cbn in L; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs]]]]]]]]; cbn in L; try lia.
destruct (IH bs ltac:(lia)) as (ws & Lw & E).
exists (Z_to_bv 64 (w8 b0 b1 b2 b3 b4 b5 b6 b7) :: ws).
split; [cbn; lia|]. cbn [map cells_bytes cbytes]. rewrite le8_of_bytes, E. reflexivity.
Qed.

Lemma rw_cells_CB_C8s : forall segs m A (n : nat) bs,
rw_cells segs m A [CB (8 * n) bs] -> exists ws, length ws = n /\ rw_cells segs m A (map C8 ws).
Proof.
intros segs m A n bs H.
assert (L : length bs = (8 * n)%nat) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
destruct (bytes_are_C8s n bs L) as (ws & Lw & E). exists ws. split; [exact Lw|].
eapply rw_cells_recast; [exact H| |].
- clear. induction ws; cbn; [exact I| split; [exact I| exact IHws]].
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact E.
Qed.

Lemma u8ro_read64 : forall segs m A ws (i : Z) w a,
u8ro segs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
intros segs m A ws i w a Hb Hn Hi ->.
first [ pose proof (u64s_split _ _ _ Hn) as sfP_; sf_destruct 6%nat sfP_ as pre post E Hlen Eu Hlu | sf_fb; destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu) ].
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
unfold u8ro in Hb.
rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma rw_cells_splitk : forall segs m A cs k, rw_cells segs m A cs ->
rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. apply rw_cells_app in H. exact H. Qed.
Ltac norm_lit_addr_in H :=
repeat match type of H with
| context [Z.add (Z.add ?b ?c) ?d] =>
is_Z_lit c; is_Z_lit d; let v := eval vm_compute in (c + d)%Z in
replace (Z.add (Z.add b c) d) with (Z.add b v) in H by lia
end.
Tactic Notation "chunk_splitk" hyp(H) "at" constr(k) "as" ident(H1) :=
apply (rw_cells_splitk _ _ _ _ k) in H; destruct H as [H1 H];
cbn [firstn skipn cells_size csize Nat.add] in H1, H; fold_of_nat_lits_in H; norm_lit_addr_in H.

Record frame := FRM {
f_a0 : word; f_a1 : word; f_a2 : word; f_a3 : word; f_a4 : word; f_a5 : word;
f_v48 : word; f_v56 : word; f_p64 : word; f_v68 : word; f_v72 : word;
f_v80 : word; f_v88 : word; f_v96 : word; f_v104 : word; f_v112 : word; f_v120 : word; f_v128 : word;
f_iq : list word;
f_ak : list word;
f_e32 : list word;
f_inn : list word;
f_ql : list word;
f_g0 : word; f_g1 : word; f_g2 : word; f_pv : word }.
Definition frame_ok (fr : frame) : Prop :=
length (f_iq fr) = 10%nat /\ length (f_ak fr) = 40%nat /\ length (f_e32 fr) = 40%nat /\
length (f_inn fr) = 40%nat /\ length (f_ql fr) = 10%nat.
Definition fa_cells (fr : frame) : list cell :=
[C8 (f_a0 fr); C8 (f_a1 fr); C8 (f_a2 fr); C8 (f_a3 fr); C8 (f_a4 fr); C8 (f_a5 fr)].
Definition fl_cells (fr : frame) : list cell :=
[C8 (f_v48 fr); C8 (f_v56 fr); C4 (f_p64 fr); C4 (f_v68 fr); C8 (f_v72 fr);
C8 (f_v80 fr); C8 (f_v88 fr); C8 (f_v96 fr); C8 (f_v104 fr); C8 (f_v112 fr); C8 (f_v120 fr); C8 (f_v128 fr)].
Definition fp_cells (fr : frame) : list cell := [C4 (f_g0 fr); C4 (f_g1 fr); C4 (f_g2 fr); C4 (f_pv fr)].

Ltac chunk_cat H1 H2 :=
lazymatch type of H1 with rw_cells ?segs ?m ?A1 ?cs1 =>
lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
let H := fresh "CAT" in
assert (H : rw_cells segs m A1 (cs1 ++ cs2))
by (apply rw_cells_join; [exact H1 |
replace (A1 + Z.of_nat (cells_size cs1))%Z with A2
by (rewrite ?cells_size_app, ?cells_size_f32; autorewrite with chunk_sizes;
cbn [cells_size csize Nat.add Nat.mul length]; fold_of_nat_lits; lia);
exact H2]);
clear H1 H2; cbn [app] in H; rename H into H1
end end.

Definition serr_frame (P : mem -> Prop) : Prop :=
forall m m' W, P m -> munch W m m' -> wmono rsegs m m' -> disjoint_from W NB_RSTDERR 232 -> P m'.
Definition sspc_frame (P : mem -> word -> Prop) : Prop :=
forall m m' W c, P m c -> munch W m m' -> wmono rsegs m m' ->
disjoint_from W NB_GOT_SSP 8 -> disjoint_from W NB_SSP_GUARD 8 -> P m' c.

Lemma nb_smrecs_bounds : forall r, In r nb_smrecs ->
NB_TABLES_LO <= smr_ptr r /\ smr_ptr r + 88 <= NB_TABLES_HI /\
(smr_ltp_par r = 0 \/ NB_TABLES_LO <= smr_ltp_par r /\ smr_ltp_par r + 16 <= NB_TABLES_HI) /\
(smr_innov_par r = 0 \/ NB_TABLES_LO <= smr_innov_par r /\ smr_innov_par r + 24 <= NB_TABLES_HI).
Proof.
intros r Hr. unfold nb_smrecs in Hr. unfold NB_TABLES_LO, NB_TABLES_HI.
repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr.
Qed.

Lemma smr_ltp_par_top : forall r, In r nb_smrecs -> smr_ltp_par r + 16 <= NB_GLOBALS_TOP.
Proof. intros r Hr. pose proof (nb_smrecs_bounds r Hr) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ B _ | sf_fb; destruct sfP_ as (_ & _ & B & _) ]. unfold NB_TABLES_LO, NB_TABLES_HI, NB_GLOBALS_TOP in *. lia. Qed.
Lemma smr_innov_par_top : forall r, In r nb_smrecs -> smr_innov_par r + 24 <= NB_GLOBALS_TOP.
Proof. intros r Hr. pose proof (nb_smrecs_bounds r Hr) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ _ B | sf_fb; destruct sfP_ as (_ & _ & _ & B) ]. unfold NB_TABLES_LO, NB_TABLES_HI, NB_GLOBALS_TOP in *. lia. Qed.

Lemma smr_ltp_wf : forall r k, In r nb_smrecs -> sm_ltp_unquant (smr_sm r) = Some k ->
match k with LtpPitchUnquant3tap p => ltp_params_ok p | _ => True end.
Proof.
intros r k Hr Hk. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hk; injection Hk as <-; cbn; first [exact I | unfold ltp_params_ok; cbn; lia] |]). destruct Hr.
Qed.
Lemma smr_innov_wf : forall r k, In r nb_smrecs -> sm_innovation_unquant (smr_sm r) = Some k ->
match k with InnovSplitCbShapeSignUnquant p => scb_params_ok p | _ => True end.
Proof.
intros r k Hr Hk. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hk; injection Hk as <-; cbn; first [exact I | unfold scb_params_ok; cbn; lia] |]). destruct Hr.
Qed.

Lemma nb_tables_transport : forall m m' W,
nb_tables m -> munch W m m' -> disjoint_from W NB_TABLES_LO (NB_TABLES_HI - NB_TABLES_LO) -> nb_tables m'.
Proof.
intros m m' W sfH_; first [ sf_destruct 8%nat sfH_ as T1 T2 T3 T4 T5 T6 T7a T7b | sf_fb; destruct sfH_ as (T1 & T2 & T3 & T4 & T5 & T6 & T7a & T7b) ]; intros MU DJ.
assert (DJsub : forall a n, NB_TABLES_LO <= a -> a + n <= NB_TABLES_HI -> 0 <= n -> disjoint_from W a n).
{ intros a n Ha Hn Hn0. clear -DJ Ha Hn Hn0. induction W as [|[u v] W IH]; cbn in *; [exact I|].
destruct DJ as [D1 D2]. split; [lia| apply IH; exact D2]. }
unfold NB_TABLES_LO, NB_TABLES_HI, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB in *.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- eapply u8ro_transport; [exact T1| exact MU|]. rewrite u64s_length, length_map.
cbn [length nb_submode_ptrs nb_smrecs map app Nat.mul Nat.add]. fold_of_nat_lits. unfold NB_SUBMODES_PTR. apply DJsub; lia.
- intros r Hr. pose proof (nb_smrecs_bounds r Hr) as (B1 & B2 & _). unfold NB_TABLES_LO, NB_TABLES_HI in *.
eapply ro_cells_transport; [apply T2; exact Hr| exact MU|].
unfold smrec_cells. cbv zeta. cbn [cells_size csize Nat.add]. fold_of_nat_lits. apply DJsub; lia.
- intros r p Hr Hp. pose proof (nb_smrecs_bounds r Hr) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ B3 _ | sf_fb; destruct sfP_ as (_ & _ & B3 & _) ]. unfold NB_TABLES_LO, NB_TABLES_HI in *.
assert (NZ : smr_ltp_par r <> 0).
{ clear -Hr Hp. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hp |- *; first [discriminate | lia] |]). destruct Hr. }
eapply ro_cells_transport; [apply T3; [exact Hr| exact Hp]| exact MU|].
cbn [ltp_par_cells cells_size csize Nat.add]. fold_of_nat_lits. apply DJsub; lia.
- intros r p Hr Hp. pose proof (nb_smrecs_bounds r Hr) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ _ B4 | sf_fb; destruct sfP_ as (_ & _ & _ & B4) ]. unfold NB_TABLES_LO, NB_TABLES_HI in *.
assert (NZ : smr_innov_par r <> 0).
{ clear -Hr Hp. unfold nb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hp |- *; first [discriminate | lia] |]). destruct Hr. }
eapply ro_cells_transport; [apply T4; [exact Hr| exact Hp]| exact MU|].
cbn [scb_par_cells cells_size csize Nat.add]. fold_of_nat_lits. apply DJsub; lia.
- eapply ro_cells_transport; [exact T5| exact MU|]. cbn [cells_size csize Nat.add]. fold_of_nat_lits. unfold NB_GOT_STDERR. apply DJsub; lia.
- eapply ro_cells_transport; [exact T6| exact MU|]. cbn [cells_size csize Nat.add]. fold_of_nat_lits. unfold NB_STDERR_VAR. apply DJsub; lia.
- unfold lsp_cdbk_got, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB in *. split.
+ eapply ro_cells_transport; [exact T7a| exact MU|]. cbn [cells_size csize Nat.add]. fold_of_nat_lits. apply DJsub; lia.
+ eapply ro_cells_transport; [exact T7b| exact MU|]. cbn [cells_size csize Nat.add]. fold_of_nat_lits. apply DJsub; lia.
Qed.

Lemma munch_of_write : forall m a bs, (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
munch [(a, a + Z.of_nat (length bs))%Z] m (write_to_mem m (wa a) bs).
Proof. intros m a bs Ha Hl. apply munch_write; [apply munch_refl| exact Ha| exact Hl|]. cbn. left. lia. Qed.
Lemma wmono_of_write : forall segs m a bs, wmono segs m (write_to_mem m (wa a) bs).
Proof. intros. apply wmono_write. apply wmono_refl. Qed.

Ltac transport_chunks segs m a bs ::=
let Ha := fresh "Ha_" in let Hl := fresh "Hl_" in
assert (Ha : (0 <= a)%Z) by lia;
assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; lia);
nb_box_junk;
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | exact Ha | exact Hl | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : bits_rep segs m ?A2 ?D2 ?b2 |- _ =>
first [ apply (bits_rep_frame segs m (write_to_mem m (wa a) bs) A2 D2 b2 [(a, a + Z.of_nat (length bs))%Z]) in H;
[ | solve [eauto] | apply munch_of_write; [exact Ha | exact Hl] | apply wmono_of_write
| cbn [disjoint_from]; simpl_sizes; slia | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : nb_tables m |- _ =>
first [ let H2 := fresh "TAB" in
unshelve epose proof (nb_tables_transport m _ _ H (munch_of_write m a bs Ha Hl) _) as H2;
[ cbn [disjoint_from]; simpl_sizes; unfold NB_TABLES_LO, NB_TABLES_HI; slia | clear H; rename H2 into H ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| SF : serr_frame ?P, H : ?P m |- _ =>
first [ let H2 := fresh "SERR" in
unshelve epose proof (SF m _ _ H (munch_of_write m a bs Ha Hl) (wmono_of_write segs m a bs) _) as H2;
[ cbn [disjoint_from]; simpl_sizes; unfold NB_RSTDERR; slia | clear H; rename H2 into H ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| SF : sspc_frame ?P, H : ?P m ?c |- _ =>
first [ let H2 := fresh "SSPC" in
unshelve epose proof (SF m _ _ c H (munch_of_write m a bs Ha Hl) (wmono_of_write segs m a bs) _ _) as H2;
[ cbn [disjoint_from]; simpl_sizes; unfold NB_GOT_SSP; slia | cbn [disjoint_from]; simpl_sizes; unfold NB_SSP_GUARD; slia
| clear H; rename H2 into H ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end;
clear Ha Hl; nb_unbox_junk.

Ltac transport_after_call segs m m' MU WM ::=
nb_box_junk;
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : bits_rep segs m ?A2 ?D2 ?b2 |- _ =>
first [ apply (bits_rep_frame segs m m' A2 D2 b2 W) in H;
[ | solve [eauto] | exact MU | exact WM | cbn [disjoint_from]; slia | cbn [disjoint_from]; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : nb_tables m |- _ =>
first [ let H2 := fresh "TAB" in
unshelve epose proof (nb_tables_transport m m' W H MU _) as H2;
[ cbn [disjoint_from]; unfold NB_TABLES_LO, NB_TABLES_HI; slia | clear H; rename H2 into H ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| SF : serr_frame ?P, H : ?P m |- _ =>
first [ let H2 := fresh "SERR" in
unshelve epose proof (SF m m' W H MU WM _) as H2;
[ cbn [disjoint_from]; unfold NB_RSTDERR; slia | clear H; rename H2 into H ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| SF : sspc_frame ?P, H : ?P m ?c |- _ =>
first [ let H2 := fresh "SSPC" in
unshelve epose proof (SF m m' W c H MU WM _ _) as H2;
[ cbn [disjoint_from]; unfold NB_GOT_SSP; slia | cbn [disjoint_from]; unfold NB_SSP_GUARD; slia | clear H; rename H2 into H ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end;
nb_unbox_junk.

Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.

Definition sub_ptr (i : Z) : Z := nth (Z.to_nat i) nb_submode_ptrs 0.
Lemma sub_ptr_read : forall m i, nb_tables m -> 0 <= i <= 15 ->
ov_read_bytes rsegs m (wa (NB_SUBMODES_PTR + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (sub_ptr i))).
Proof.
intros m i (T1 & _) Hi.
eapply (u8ro_read64 rsegs m NB_SUBMODES_PTR _ i); [exact T1 | | lia | reflexivity].
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]]]]; reflexivity.
Qed.

Lemma smrec_cases : forall mo, 0 <= mo <= 8 ->
(mo = 0 /\ sub_ptr mo = 0 /\ smrec_at mo = None /\ submode_at nb_submodes mo = None)
\/ (exists r, smrec_at mo = Some r /\ In r nb_smrecs /\ sub_ptr mo = smr_ptr r /\ 0x3b6f8 <= smr_ptr r /\
submode_at nb_submodes mo = Some (smr_sm r) /\ lsp_order (sm_lsp_unquant (smr_sm r)) = 10).
Proof.
intros mo Hmo.
assert (C : mo = 0 \/ mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]];
[left; repeat split; reflexivity | right ..];
(eexists; split; [reflexivity|]; split; [cbn; tauto|]; cbn; repeat split; reflexivity || lia).
Qed.
Lemma smrec_at_in : forall mo r, smrec_at mo = Some r -> In r nb_smrecs /\ submode_at nb_submodes mo = Some (smr_sm r) /\ 1 <= mo <= 8.
Proof.
intros mo r E. unfold smrec_at in E. destruct (Z.ltb_spec mo 1); [discriminate|].
destruct (Z_le_gt_dec mo 8).
- assert (C : mo = 1 \/ mo = 2 \/ mo = 3 \/ mo = 4 \/ mo = 5 \/ mo = 6 \/ mo = 7 \/ mo = 8) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in E; injection E as <-; cbn; repeat split; auto 10; lia.
- exfalso. assert (L : (8 <= Z.to_nat (mo - 1))%nat) by lia.
pose proof (nth_error_None nb_smrecs (Z.to_nat (mo - 1))) as [_ NN]. rewrite NN in E; [discriminate|]. cbn. lia.
Qed.

Record nbinv {ptr : Type} := NBI {
x_serr : mem -> Prop;
x_sspc : mem -> word -> Prop;
x_st : Z; x_out : Z; x_A : Z; x_D : Z; x_stereo : Z; x_isv : Z; x_lo : Z;
x_canary : word;
x_st0 : nb_state ptr; x_b0 : bits_st ptr;
x_ra : word; x_sp : word; x_gp : word; x_tp : word;
x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word;
x_s6 : word; x_s7 : word; x_s8 : word; x_s9 : word; x_s10 : word; x_s11 : word;
x_F : bvmap 5 word; x_m0 : mem }.
Arguments nbinv ptr : clear implicits.

Section Cuts.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable X : nbinv ptr.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation NBP := (nb_pieces rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler).

Definition nbW : list (Z * Z) :=
[(lo, usp); (ST, ST + NBSTATE_SIZEOF); (OUT, OUT + 640); (ISV, ISV + 640); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)].

Definition fr_saves : list cell :=
let F0 := x_F X in
[C8 (reg_get F0 (Z_to_bv 5 27)); C8 (reg_get F0 (Z_to_bv 5 26)); C8 (reg_get F0 (Z_to_bv 5 25)); C8 (reg_get F0 (Z_to_bv 5 24));
C8 (reg_get F0 (Z_to_bv 5 23)); C8 (reg_get F0 (Z_to_bv 5 22)); C8 (reg_get F0 (Z_to_bv 5 21)); C8 (reg_get F0 (Z_to_bv 5 20));
C8 (reg_get F0 (Z_to_bv 5 19)); C8 (reg_get F0 (Z_to_bv 5 18)); C8 (reg_get F0 (Z_to_bv 5 9)); C8 (reg_get F0 (Z_to_bv 5 8));
C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X);
C8 (x_s3 X); C8 (x_s2 X); C8 (x_s1 X); C8 (x_s0 X); C8 (x_ra X)].

Definition frame_at (m : mem) (fr : frame) : Prop :=
rw_cells rsegs m (usp + -912) (fa_cells fr)
/\ rw_cells rsegs m (usp + -864) (fl_cells fr)
/\ rw_cells rsegs m (usp + -776) (f32 (f_iq fr))
/\ rw_cells rsegs m (usp + -736) (f32 (f_ak fr))
/\ rw_cells rsegs m (usp + -576) (f32 (f_e32 fr))
/\ rw_cells rsegs m (usp + -416) (f32 (f_inn fr))
/\ rw_cells rsegs m (usp + -256) (f32 (f_ql fr))
/\ rw_cells rsegs m (usp + -216) (fp_cells fr)
/\ rw_cells rsegs m (usp + -200) fr_saves.

Definition nbctx (m : mem) (st : nb_state ptr) (b : bits_st ptr) (j : nb_junk) (ows iws sws : list word) : Prop :=
munch nbW (x_m0 X) m /\ wmono rsegs (x_m0 X) m /\ mem_inv rsegs m /\ stk rsegs m lo (usp + -912)
/\ NBP m ST OUT STEREO st j /\ nb_junk_ok j /\ cbs_ok A_speex_std_stereo_request_handler STEREO (nb_stereo_cb st) (j_cbs j) /\ nb_inv st
/\ bits_rep rsegs m A D b /\ bits_ok b /\ sb_buf_size b = sb_buf_size (x_b0 X)
/\ rw_cells rsegs m OUT (f32 ows) /\ length ows = 160%nat
/\ rw_cells rsegs m ISV (f32 iws) /\ length iws = 160%nat
/\ rw_cells rsegs m STEREO (f32 sws) /\ length sws = 2%nat.

Definition nbctxX (m : mem) (st : nb_state ptr) (b : bits_st ptr) (j : nb_junk) (ows iws sws : list word) : Prop :=
munch (nb_W ST OUT A STEREO ISV lo usp) (x_m0 X) m /\ wmono rsegs (x_m0 X) m /\ mem_inv rsegs m /\ stk rsegs m lo (usp + -912)
/\ NBP m ST OUT STEREO st j /\ nb_junk_ok j /\ cbs_ok A_speex_std_stereo_request_handler STEREO (nb_stereo_cb st) (j_cbs j) /\ nb_inv st
/\ bits_rep rsegs m A D b /\ bits_ok b /\ sb_buf_size b = sb_buf_size (x_b0 X)
/\ rw_cells rsegs m OUT (f32 ows) /\ length ows = 160%nat
/\ rw_cells rsegs m ISV (f32 iws) /\ length iws = 160%nat
/\ rw_cells rsegs m STEREO (f32 sws) /\ length sws = 2%nat
/\ nb_tables m /\ x_serr X m /\ x_sspc X m (x_canary X).

Definition at_X (r : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs1 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) (x_gp X) (x_tp X) (c_t0 k) (c_t1 k) (c_t2 k) xs0 xs1 xa0 (c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 (Z_to_bv 64 r) xs6 xs7 xs8 xs9 xs10 xs11 (c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21f30) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctxX m st b j ows iws sws /\ frame_ok fr /\ frame_at m fr
/\ j_exc j = ST + 1368.

Definition at_B (mo : Z) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs1 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) (x_gp X) (x_tp X) (c_t0 k) (c_t1 k) (c_t2 k) xs0 xs1 xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 (Z_to_bv 64 (ST + 32)) xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x20d74) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx m (set_nb_submodeID (x_st0 X) mo) b j ows iws sws /\ frame_ok fr /\ frame_at m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ 0 <= mo <= 8 /\ j_exc j = ST + 1368.

Definition at_N (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) (x_gp X) (x_tp X) (c_t0 k) (c_t1 k) (c_t2 k) xs0 xs1 xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x20fb4) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx m (set_nb_submodeID (x_st0 X) 0) b j ows iws sws /\ frame_ok fr /\ frame_at m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0 /\ j_exc j = ST + 1368.

Definition at_C (r : smrec) (mo : Z) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) (x_gp X) (x_tp X) (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x20e14) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx m (set_nb_submodeID (x_st0 X) mo) b j ows iws sws /\ frame_ok fr /\ frame_at m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ smrec_at mo = Some r /\ j_exc j = ST + 1368.

Definition at_E (r : smrec) (mo olp bp sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs2 xs4 xs7 xs10 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) (x_gp X) (x_tp X) (c_t0 k) (c_t1 k) (c_t2 k) xs0 (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 (Z_to_bv 64 (usp + -416)) xs4 (Z_to_bv 64 bp) (Z_to_bv 64 160) xs7 (Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) xs10 (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x212d8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx m st b j ows iws sws /\ frame_ok fr /\ frame_at m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v72 fr = Z_to_bv 64 (ST + 2228)
/\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (40 * sub)
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ f_v128 fr = Z_to_bv 64 (olp + 1073741824)
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub <= 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Definition at_A (pc : Z) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) (x_gp X) (x_tp X) (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 5) (Z_to_bv 64 4) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 13) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 14) (Z_to_bv 64 (-1)) (Z_to_bv 64 (ST + 2256)) (Z_to_bv 64 7)
(Z_to_bv 64 A_wb_skip_table) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 18446744073709482831) (Z_to_bv 64 A)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 pc) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx m (x_st0 X) b j ows iws sws /\ frame_ok fr /\ frame_at m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368.

Definition QA (s : PState) : nb_search_res -> PState -> machine_state -> Prop :=
fun res s' ms => s' = s /\
match res with
| NbReturn r b => at_X r (x_st0 X) b ms
| NbMode mo b => at_B mo b ms
end.
End Cuts.

Record nb_hyps {ptr : Type} (notify : list Z -> X1qx.M PState unit) (STR_TOP : Z) (X : nbinv ptr) : Prop := NBH {
h_lay : nb_layout (x_st X) (x_out X) (x_A X) (x_D X) (sb_buf_size (x_b0 X)) (x_stereo X) (x_isv X) (x_lo X) (bv_unsigned (x_sp X));
h_lo : x_lo X + NB_DECODE_DEPTH <= bv_unsigned (x_sp X);
h_spx : bv_unsigned (x_sp X) < 2^63;
h_inv0 : nb_inv (x_st0 X);
h_isv : match nb_innov_save (x_st0 X) with None => True | Some k => x_isv X = x_out X + 4 * k end;
h_stal : x_st X mod 8 = 0;
h_sthi : x_st X + NBSTATE_SIZEOF < 2^63;
h_tab0 : nb_tables (x_m0 X);
h_serr0 : x_serr X (x_m0 X);
h_sspc0 : x_sspc X (x_m0 X) (x_canary X);
h_serrf : serr_frame (x_serr X);
h_sspcf : sspc_frame (x_sspc X);
h_notify : nb_notify_stmt notify (x_serr X) (x_sspc X) STR_TOP;
h_strtop : 0x104d0 <= STR_TOP;
h_inband : inband_handler_stmt (ptr:=ptr);
h_userh : user_handler_stmt (ptr:=ptr);
h_memmove : memmove_stmt;
h_exp : exp_stmt;
h_lsp : forall k, lsp_unquant_stmt (ptr:=ptr) k;
h_ltp : forall k, match k with LtpPitchUnquant3tap p => ltp_params_ok p | _ => True end -> ltp_unquant_stmt (ptr:=ptr) k;
h_innov : forall k, match k with InnovSplitCbShapeSignUnquant p => scb_params_ok p | _ => True end -> innov_unquant_stmt (ptr:=ptr) k;
h_multicomb : multicomb_stmt;
h_lspi : lsp_interpolate_stmt;
h_l2l : lsp_to_lpc_stmt;
h_bwlpc : bw_lpc_w_stmt;
h_rms : compute_rms16_w_stmt;
h_smul : signal_mul_w_stmt;
h_san : sanitize_values32_w_stmt;
h_iir : iir_mem16_w_stmt;
h_hp : highpass_w_stmt;
h_out4 : x_out X mod 4 = 0;
h_ster4 : x_stereo X mod 4 = 0;
h_sp16 : bv_unsigned (x_sp X) mod 16 = 0 }.
