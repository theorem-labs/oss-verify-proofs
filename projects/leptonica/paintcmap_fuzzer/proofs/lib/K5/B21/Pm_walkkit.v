(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit.
Import ListNotations.
Open Scope Z_scope.

Section PmWalkKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma live_outside_walk1 : forall Σ (m : mem) fr usp slo q n a,
  ART RT Σ m -> In (fr, 1%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (q, n) (rt_live RT Σ) -> q <= a < q + n ->
  outside [(slo, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] a.
Proof using AF.
  intros Σ m fr usp slo q n a HA FIN SLO QIN Ha.
  pose proof (af_live_range RT AF Σ m q n HA QIN) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m fr 1%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 1%nat HA FIN) as (SA1 & _). specialize (SA1 q n QIN).
  change (fs_size 1) with 128 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.
Lemma keeps_live_walk1 : forall Σ (m m' : mem) fr usp slo,
  ART RT Σ m -> In (fr, 1%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  munch [(slo, usp); (fr, fr + 120); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 16)] m m' -> keeps_live (rt_live RT Σ) m m'.
Proof using AF.
  intros Σ m m' fr usp slo HA FIN SLO MU b k Hin a Ha. apply MU. exact (live_outside_walk1 Σ m fr usp slo b k _ HA FIN SLO Hin Ha).
Qed.
(* [comment removed for export] *)
Lemma live_outside_walk2 : forall Σ (m : mem) fr usp slo q n a,
  ART RT Σ m -> In (fr, 2%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (q, n) (rt_live RT Σ) -> q <= a < q + n ->
  outside [(slo, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] a.
Proof using AF.
  intros Σ m fr usp slo q n a HA FIN SLO QIN Ha.
  pose proof (af_live_range RT AF Σ m q n HA QIN) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m fr 2%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV q n QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 2%nat HA FIN) as (SA1 & _). specialize (SA1 q n QIN).
  change (fs_size 2) with 256 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.
Lemma keeps_live_walk2 : forall Σ (m m' : mem) fr usp slo,
  ART RT Σ m -> In (fr, 2%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  munch [(slo, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] m m' -> keeps_live (rt_live RT Σ) m m'.
Proof using AF.
  intros Σ m m' fr usp slo HA FIN SLO MU b k Hin a Ha. apply MU. exact (live_outside_walk2 Σ m fr usp slo b k _ HA FIN SLO Hin Ha).
Qed.
End PmWalkKit.
