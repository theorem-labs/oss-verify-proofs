(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.A14 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface LeptC_deser2_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma client_traces_ra : forall f r x rest, In (f :: r :: x :: rest) CLIENT_TRACES -> 4096 <= x.
Proof.
  intros f r x rest Hin.
  assert (CK : forallb (fun t => match t with _ :: _ :: y :: _ => 4096 <=? y | _ => true end) CLIENT_TRACES = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in CK. specialize (CK _ Hin). cbv beta iota in CK. apply Z.leb_le. exact CK.
Qed.

Section CTX.
Variable RT : rt_sig.
Lemma deser_ctx_intro : forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp s0 : word) (lo : Z) (m : mem) (dp n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> 28 <= n < 2^26 -> 0 < dp -> dp mod 8 = 0 -> own_live (rt_live RT Σ) dp n ->
  uctx m sp s0 ras ->
  Forall (fun r => Forall (fun f => In (f :: r :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS) DESER_DESTROY_RAS ->
  lenv RT Σ m sp lo (LSTK 8) -> lres RT Σ 6 5 (RASTER_COST + 64) ->
  forall rdes, In rdes DESER_DESTROY_RAS -> deser_ctx RT Σ PMc ra s0 (bv_unsigned sp) lo m dp n ras rdes.
Proof.
  intros Σ PMc ra sp s0 lo m dp n ras FDO MST NR DP0 DP8 OWN UCTX TRS ENV RES rdes Hr.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB). destruct RES as (FRB & LVB & CRB & LVP).
  pose proof ST as (STa & _).
  pose proof (proj1 (Forall_forall _ _) TRS rdes Hr) as TR1.
  assert (RA : 4096 <= bv_unsigned ra).
  { pose proof (proj1 (Forall_forall _ _) TR1 0x9194c ltac:(unfold DESTROY_FREE_RAS; left; reflexivity)) as T. exact (client_traces_ra _ _ _ _ T). }
  unfold deser_ctx, LSTK, STACK_WIN, USTACK_TOP, RT_STACK, RASTER_COST, uctx in *.
  repeat split; first [assumption | lia].
Qed.
End CTX.
