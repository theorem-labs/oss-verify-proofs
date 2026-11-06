(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit D_iface D_defs Lept_iface LeptC_kit Lept_objkit Gm_iface Gm_kit Gm_livekit Gm_livekit2 Gm_drvkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FhDrvKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma new_chunk_apart_sub : forall Σ' (m : mem) p n (live0 : list (Z * Z)) frs usp a,
  ART RT Σ' m -> In (p, n) (rt_live RT Σ') ->
  (forall e, In e live0 -> In e (rt_live RT Σ') /\ fst e <> p) -> (forall e, In e frs -> In e (rt_frames RT Σ')) ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m p n live0 frs usp a HA INL SUB FSUB SPL Ha.
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB. pose proof (client_static_lo a H) as HL. lia.
  - destruct H as (p' & n' & Hin & Hp). destruct (SUB _ Hin) as [Hin' NE]. cbn [fst] in NE.
    pose proof (live_apart RT AF Σ' m p n p' n' HA INL Hin' ltac:(congruence)) as D. lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_frames_range RT AF Σ' m f k HA (FSUB _ Hin)) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf).
    pose proof (af_fshadow_apart RT AF Σ' m f k HA (FSUB _ Hin)) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma live_outside_frame0 : forall Σ (m : mem) fr usp slo b k x,
  ART RT Σ m -> In (fr, 0%nat) (rt_frames RT Σ) -> rt_sp0 RT Σ - STACK_WIN <= slo ->
  In (b, k) (rt_live RT Σ) -> b <= x < b + k ->
  outside [(slo, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] x.
Proof using AF.
  intros Σ m fr usp slo b k x HA FIN SLO QIN Hx.
  pose proof (af_live_range RT AF Σ m b k HA QIN) as (_ & R1 & _).
  pose proof (af_frames_range RT AF Σ m fr 0%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV b k QIN).
  pose proof (af_fshadow_apart RT AF Σ m fr 0%nat HA FIN) as (SA1 & _). specialize (SA1 b k QIN).
  change (fs_size 0) with 64 in *. unfold shad, SHB in SA1.
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.

End FhDrvKit.
