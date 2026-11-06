(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit.
Import ListNotations.
Open Scope Z_scope.

Section B.
Context {HC : HasCeiling}.

#[using="Type"] Lemma stk_release_any : forall (m : mem) lo A cs,
  stk asegs m lo A -> rw_cells asegs m A cs -> stk asegs m lo (A + Z.of_nat (cells_size cs)).
Proof.
  intros m lo A cs Hs Hc. destruct (Z_le_gt_dec lo A) as [LE|GT]; [apply stk_release; assumption|].
  pose proof (stk_of_rw_cells asegs m A cs Hc) as S. destruct Hs as (L0 & _ & _). pose proof S as (_ & H1 & _).
  destruct (Z_le_gt_dec lo (A + Z.of_nat (cells_size cs))) as [LE2|GT2].
  - exact (proj2 (stk_split asegs m A lo _ S ltac:(lia))).
  - split; [exact L0|]. split; [exact H1|]. intros a Ha. lia.
Qed.
Ltac release_any FR ST hi :=
  pose proof (stk_release_any _ _ _ _ ST FR) as STR; cbn [cells_size csize Nat.add] in STR;
  lazymatch type of STR with stk ?segs ?m ?lo ?hi' => replace hi' with hi in STR by lia end.

#[using="Type"] Lemma ic_vprintf_back_proof : vprintf_back_stmt.
Proof.
  intros until junk. intros FRM ST CLO Q64 AE MI.
  pose proof alloc_ceiling_bounds as ACB.
  replace (q - 48) with (q + -48) in * by lia.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 5 zstep.
  release_any FRM ST q. finish.
Qed.

#[using="Type"] Lemma ic_vfprintf_back_proof : vfprintf_back_stmt.
Proof.
  intros until lo. intros FRM ST CLO Q64 AE MI.
  pose proof alloc_ceiling_bounds as ACB.
  replace (q - 48) with (q + -48) in * by lia.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 6 zstep.
  release_any FRM ST q. finish.
Qed.

#[using="Type"] Lemma fprintf_frame_shape : forall (m : mem) A cells (x2 x1 x0 xra : word),
  rw_cells asegs m A cells -> cells_size cells = 112%nat ->
  nth_error cells 4 = Some (C8 x2) -> nth_error cells 5 = Some (C8 x1) -> nth_error cells 6 = Some (C8 x0) -> nth_error cells 7 = Some (C8 xra) ->
  firstn 4 (map csize cells) = [8; 8; 8; 8]%nat ->
  exists j1 j2, rw_cells asegs m A [CB 32 j1; C8 x2; C8 x1; C8 x0; C8 xra; CB 48 j2].
Proof.
  intros m A cells x2 x1 x0 xra RW SZ N4 N5 N6 N7 F4.
  destruct cells as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 rest]]]]]]]]; cbn in N4, N5, N6, N7, F4; try discriminate.
  injection N4 as ->. injection N5 as ->. injection N6 as ->. injection N7 as ->.
  injection F4 as S0 S1 S2 S3.
  pose proof (rw_cells_merge asegs m A [] [c0; c1; c2; c3] (C8 x2 :: C8 x1 :: C8 x0 :: C8 xra :: rest) RW) as M1.
  cbn [app cells_size] in M1. rewrite S0, S1, S2, S3 in M1. cbn [Nat.add] in M1.
  pose proof (rw_cells_merge asegs m A [CB 32 (cells_bytes [c0; c1; c2; c3]); C8 x2; C8 x1; C8 x0; C8 xra] rest []) as M2.
  rewrite app_nil_r in M2. cbn [app] in M2. specialize (M2 M1).
  cbn [cells_size csize] in SZ. rewrite S0, S1, S2, S3 in SZ.
  replace (cells_size rest) with 48%nat in M2 by lia.
  eexists. eexists. exact M2.
Qed.

#[using="Type"] Lemma ic_fprintf_back_proof : fprintf_back_stmt.
Proof.
  intros until cells. intros FRM SZ N4 N5 N6 N7 F4 ST CLO Q64 AE MI.
  pose proof alloc_ceiling_bounds as ACB.
  replace (q - 112) with (q + -112) in * by lia.
  destruct (fprintf_frame_shape m (q + -112) cells s2 s1 s0 ra0 FRM SZ N4 N5 N6 N7 F4) as (j1 & j2 & FR).
  clear FRM.
  pose proof (munch_refl [(lo, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  do 6 zstep.
  release_any FR ST q. finish.
Qed.
End B.
