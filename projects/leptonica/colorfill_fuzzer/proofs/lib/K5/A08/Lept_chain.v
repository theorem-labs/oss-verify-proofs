(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface D_kit.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma chain_ok_keep : forall ras (m m' : mem) lo f, chain_ok m lo f ras ->
  agree_on (fun a => lo <= a < USTACK_TOP) m m' -> chain_ok m' lo f ras.
Proof.
  induction ras as [|ra1 ras IH]; intros m m' lo f H AG; cbn [chain_ok] in *; [exact H|].
  destruct H as (H1 & H2 & H3 & H4 & fp1 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exists fp1. split; [exact H5|]. split.
  - apply (rw_cells_agree_nw asegs m m' _ _ H6). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
  - apply (IH m m' f fp1 H7). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma chain_ok_push : forall (m : mem) lo f ra1 fp1 ras,
  lo + 16 <= f -> f mod 8 = 0 -> f + 16 <= USTACK_TOP -> 4096 <= ra1 < 2^64 -> 0 <= fp1 < 2^64 ->
  rw_cells asegs m (f + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 ra1)] -> chain_ok m f fp1 ras ->
  chain_ok m lo f (ra1 :: ras).
Proof. intros m lo f ra1 fp1 ras H1 H2 H3 H4 H5 H6 H7. cbn [chain_ok]. repeat (split; [assumption|]). exists fp1. auto. Qed.
