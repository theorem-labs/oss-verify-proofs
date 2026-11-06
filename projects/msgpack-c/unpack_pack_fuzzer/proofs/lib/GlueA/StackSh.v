(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St.
Open Scope Z_scope.
Unset Lia Cache.

Definition SSH_ID : int := 12%uint63.

Section SSH.
Context {rc : runConstT}.

Definition ssh_holds (m : amem) : Prop := forall a, shad ATOP <= a < Shadow.KHIGH -> wb asegs m a = true.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma shad_top : shad (2 ^ 47) = Shadow.KHIGH.
Proof. reflexivity. Qed.

Lemma ssh_wr_at : forall m RLO RHI, ssh_holds m -> ATOP <= RLO -> RLO <= RHI -> RHI <= 2 ^ 47 ->
  ALib.Mem.wr_at asegs m (shad RLO) (shad RHI - shad RLO).
Proof.
  intros m RLO RHI H L1 L2 L3. pose proof atop_range as ATR.
  pose proof (shad_mono _ _ L1) as S1. pose proof (shad_mono _ _ L2) as S2. pose proof (shad_mono _ _ L3) as S3. rewrite shad_top in S3.
  assert (S0 : 0 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.div_pos ATOP (2 ^ 3)); lia).
  split; [lia|]. split; [unfold Shadow.KHIGH in *; lia|].
  intros i Hi. apply (GlueA.wb_wviewA asegs). apply H. lia.
Qed.
End SSH.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St.
Open Scope Z_scope.
Unset Lia Cache.

Definition SSH_ID : int := 12%uint63.

Section SSH.
Context {rc : runConstT}.

Definition ssh_holds (m : amem) : Prop := forall a, shad ATOP <= a < Shadow.KHIGH -> wb bsegs m a = true.

Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma shad_top : shad (2 ^ 47) = Shadow.KHIGH.
Proof. reflexivity. Qed.

Lemma ssh_wr_at : forall m RLO RHI, ssh_holds m -> ATOP <= RLO -> RLO <= RHI -> RHI <= 2 ^ 47 ->
  ALib.Mem.wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
Proof.
  intros m RLO RHI H L1 L2 L3. pose proof atop_range as ATR.
  pose proof (shad_mono _ _ L1) as S1. pose proof (shad_mono _ _ L2) as S2. pose proof (shad_mono _ _ L3) as S3. rewrite shad_top in S3.
  assert (S0 : 0 <= shad ATOP) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.div_pos ATOP (2 ^ 3)); lia).
  split; [lia|]. split; [unfold Shadow.KHIGH in *; lia|].
  intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs). apply H. lia.
Qed.
End SSH.
End TwinB.
