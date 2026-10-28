(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AFake_iface AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Export AZ_globals.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition aro_client (RNG : footprint) (m : amem) : Prop :=
  (forall A n, In (A, n) ACLIENT_RO -> aro RNG m A n) /\ ahull RNG m ACLIENT_HLO (ACLIENT_HHI - ACLIENT_HLO).

(* [comment removed for export] *)
Lemma aro_client_transport_gen : forall RNG m m' W, wmono bsegs m m' -> aro_client RNG m -> munch W m m' ->
  (forall A n, In (A, n) ACLIENT_RO -> disjoint_from W (shad A) (shad (A + n - 1) + 1 - shad A)) -> aro_client RNG m'.
Proof.
  intros RNG m m' W WM [H HH] MU D. split.
  - intros A n HIn. destruct (H A n HIn) as (U & R1 & R2).
    split; [eapply unpoisoned_munch; [exact U | exact MU | exact (D A n HIn)] | split; [exact R1 | exact R2]].
  - destruct HH as (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R). exists RLO, RHI.
    do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R].
Qed.

Lemma aro_client_transport : forall RNG m m' W, aro_client RNG m -> munch W m m' -> wmono bsegs m m' -> aappW W -> aro_client RNG m'.
Proof.
  intros RNG m m' W H MU WM HW. apply (aro_client_transport_gen RNG m m' W WM H MU). intros A n HIn.
  destruct (aclient_bounds A n HIn) as (B1 & B2 & B3).
  apply aappW_shadow_disjoint; [exact HW | | | |]; rewrite ?shad_div; unfold ASHOFF, KEND; Z.div_mod_to_equations; lia.
Qed.

Lemma aro_client_transport_F : forall RNG m m' W L, aro_client RNG m -> munch (W ++ fake_area L) m m' -> wmono bsegs m m' ->
  aappW W -> ablk (al_fake L) (al_fake L + FAKESZ) -> aro_client RNG m'.
Proof.
  intros RNG m m' W L H MU WM HW AF. apply (aro_client_transport_gen RNG m m' _ WM H MU). intros A n HIn.
  destruct (aclient_bounds A n HIn) as (B1 & B2 & B3).
  apply disjoint_from_app2.
  - apply aappW_shadow_disjoint; [exact HW | | | |]; rewrite ?shad_div; unfold ASHOFF, KEND; Z.div_mod_to_equations; lia.
  - unfold fake_area, FAKESZ in *. cbn [disjoint_from]. unfold ablk, AIMG_HI, KLS in AF. rewrite !shad_div. unfold ASHOFF.
    split; [| split; [| exact I]]; Z.div_mod_to_equations; lia.
Qed.

Lemma aro_client_of_M : forall RNG m, aro_clientM m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc2a00 -> aro_client RNG m.
Proof.
  intros RNG m [U W] RI RS. split.
  - intros A n HIn. destruct (aclient_bounds A n HIn) as (B1 & B2 & B3). split; [exact (U A n HIn)|]. split.
    + eapply rng_sub; [exact RI | lia | lia].
    + eapply rng_sub; [exact RS | |]; unfold shspan; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  - exists ACLIENT_HLO, ACLIENT_HHI. repeat (split; [unfold KEND; lia|]). split; [exact W|].
    eapply rng_sub; [exact RS | |]; rewrite ?shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma aro_client_at : forall RNG m A n, aro_client RNG m -> In (A, n) ACLIENT_RO -> aro RNG m A n.
Proof. intros RNG m A n [H _] HIn. exact (H A n HIn). Qed.
Lemma aro_client_hull : forall RNG m A n, aro_client RNG m -> ACLIENT_HLO <= A -> 0 <= n -> A + n <= ACLIENT_HHI -> ahull RNG m A n.
Proof.
  intros RNG m A n [_ (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R)] HA Hn HB. exists RLO, RHI.
  repeat (split; [lia|]). split; [exact W0 | exact R].
Qed.
End CANSEC1.

Ltac aro_cl H := apply (aro_client_at _ _ _ _ H); cbn [ACLIENT_RO In]; repeat (first [left; reflexivity | right]).
