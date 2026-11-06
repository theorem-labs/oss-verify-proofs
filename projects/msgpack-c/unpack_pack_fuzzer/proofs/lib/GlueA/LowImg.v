(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC MemsetPre RangePre LowImgRd.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Definition ZRO_LO : Z := 0x7fffa000.
Definition ZRO_HI : Z := 0x7fffc58c.

Definition zro_holds {rc : runConstT} (m : word -> option byte) : Prop :=
  forall s, ZRO_LO <= s < ZRO_HI -> m (ALib.Mem.wa s) = Some (Z_to_bv 8 0) /\ wb asegs m s = true.

Lemma zro_shadow_bytes {rc : runConstT} : forall m A n, zro_holds m -> 0x10040 <= A -> 0 <= n -> A + n + 64 <= 0x22c60 ->
  Shadow.shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0).
Proof.
  intros m A n Z HA Hn HB. unfold Shadow.shadow_bytes, shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros s Hs. apply (proj1 (Z s ltac:(unfold ZRO_LO, ZRO_HI; Z.div_mod_to_equations; lia))).
Qed.

Definition low_range_facts {rc : runConstT} (RNG : footprint) (m : amem) (A len : Z) : Prop :=
  0x10040 <= A /\ A + len + 64 <= 0x22c60
  /\ (exists bs, length bs = Z.to_nat len /\ AM.bytes_at asegs m A bs)
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma low_range_facts_ok {rc : runConstT} : forall (RNG : footprint) (m : amem) A len, zro_holds m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc4000 ->
  0x10040 <= A -> 0 <= len -> A + len + 64 <= 0x22c60 -> low_range_facts RNG m A len.
Proof.
  intros RNG m A len Z RI RS HA HN HH.
  split; [exact HA|]. split; [exact HH|].
  split.
  { destruct (mapped_bytes m (Z.to_nat len) A ltac:(lia) ltac:(lia)) as (bs & LEN & BY).
    - intros i Hi. apply low_readable. lia.
    - exists bs. split; assumption. }
  split; [split; [lia|]; left; unfold Shadow.KLOW; lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    apply (proj1 (Z (ASHOFF + G) ltac:(unfold ZRO_LO, ZRO_HI, ASHOFF; lia))). }
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].
  exists (A / 64 * 64), ((A + len + 63) / 64 * 64).
  assert (H1 : A / 64 * 64 <= A /\ 0x10040 <= A / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + len <= (A + len + 63) / 64 * 64 /\ (A + len + 63) / 64 * 64 <= 0x22c40) by (Z.div_mod_to_equations; lia).
  assert (S1 : shad (A / 64 * 64) <= shad ((A + len + 63) / 64 * 64) /\ ZRO_LO <= shad (A / 64 * 64) /\ shad ((A + len + 63) / 64 * 64) <= ZRO_HI).
  { unfold shad, ASHOFF, ZRO_LO, ZRO_HI. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  - split; [unfold ZRO_LO in S1; lia|]. split; [unfold ZRO_HI in S1; lia|]. intros i Hi. apply (GlueA.wb_wviewA asegs).
    apply (proj2 (Z (shad (A / 64 * 64) + i) ltac:(lia))).
  - apply (rng_sub _ _ _ _ _ RS); unfold ZRO_LO, ZRO_HI in S1; lia.
Qed.

Lemma lit_low_inv : forall st a len, RangeC.lit_low st a len = true -> to_Z len <= 4096 ->
  W64.wt a = false /\ 0x10040 <= to_Z (W64.wl a) /\ to_Z (W64.wl a) + to_Z len + 64 <= 0x22c60 /\ find_op RangeC.ZRO_ID (s_ops st) = Some [].
Proof.
  intros st a len H NR. unfold RangeC.lit_low in H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in H. apply Uint63.leb_spec in Q2, Q1, Q0. change (to_Z 65600%uint63) with 65600 in Q2. change (to_Z 142432%uint63) with 142432 in Q1, Q0.
  pose proof (to_Z_bounded len) as LB.
  rewrite !Uint63.add_spec in Q0. change (to_Z 64%uint63) with 64 in Q0.
  rewrite (Z.mod_small (to_Z len + 64)) in Q0 by (change wB with (2 ^ 63); lia). rewrite Z.mod_small in Q0 by (change wB with (2 ^ 63); lia).
  destruct (find_op RangeC.ZRO_ID (s_ops st)) as [[|? ?]|]; try discriminate Q.
  split; [exact H|]. split; [lia|]. split; [lia| reflexivity].
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import StackSh.TwinB RangeC.TwinB MemsetPre.TwinB RangePre.TwinB LowImgRd.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import St CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Definition ZRO_LO : Z := 0x7fffa000.
Definition ZRO_HI : Z := 0x7fffc5a0.

Definition zro_holds {rc : runConstT} (m : word -> option byte) : Prop :=
  forall s, ZRO_LO <= s < ZRO_HI -> m (ALib.Mem.wa s) = Some (Z_to_bv 8 0) /\ wb bsegs m s = true.

Lemma zro_shadow_bytes {rc : runConstT} : forall m A n, zro_holds m -> 0x10040 <= A -> 0 <= n -> A + n + 64 <= 0x22d00 ->
  Shadow.shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0).
Proof.
  intros m A n Z HA Hn HB. unfold Shadow.shadow_bytes, shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros s Hs. apply (proj1 (Z s ltac:(unfold ZRO_LO, ZRO_HI; Z.div_mod_to_equations; lia))).
Qed.

Definition low_range_facts {rc : runConstT} (RNG : footprint) (m : amem) (A len : Z) : Prop :=
  0x10040 <= A /\ A + len + 64 <= 0x22d00
  /\ (exists bs, length bs = Z.to_nat len /\ AM.bytes_at bsegs m A bs)
  /\ SH.app_blk A (A + len) /\ SH.unpoisoned m A (A + len) /\ rng RNG A len
  /\ exists RLO RHI, (RLO <= A /\ A + len <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= SH.KEND)
       /\ AM.wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Lemma low_range_facts_ok {rc : runConstT} : forall (RNG : footprint) (m : amem) A len, zro_holds m -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc5000 ->
  0x10040 <= A -> 0 <= len -> A + len + 64 <= 0x22d00 -> low_range_facts RNG m A len.
Proof.
  intros RNG m A len Z RI RS HA HN HH.
  split; [exact HA|]. split; [exact HH|].
  split.
  { destruct (mapped_bytes m (Z.to_nat len) A ltac:(lia) ltac:(lia)) as (bs & LEN & BY).
    - intros i Hi. apply low_readable. lia.
    - exists bs. split; assumption. }
  split; [split; [lia|]; left; unfold Shadow.KLOW; lia|].
  split.
  { split; [lia|]. split; [lia|]. intros G _ G1 G2. exists (Z_to_bv 8 0). split; [| left; reflexivity].
    apply (proj1 (Z (ASHOFF + G) ltac:(unfold ZRO_LO, ZRO_HI, ASHOFF; lia))). }
  split; [apply (rng_sub _ _ _ _ _ RI); lia|].
  exists (A / 64 * 64), ((A + len + 63) / 64 * 64).
  assert (H1 : A / 64 * 64 <= A /\ 0x10040 <= A / 64 * 64) by (Z.div_mod_to_equations; lia).
  assert (H2 : A + len <= (A + len + 63) / 64 * 64 /\ (A + len + 63) / 64 * 64 <= 0x22cc0) by (Z.div_mod_to_equations; lia).
  assert (S1 : shad (A / 64 * 64) <= shad ((A + len + 63) / 64 * 64) /\ ZRO_LO <= shad (A / 64 * 64) /\ shad ((A + len + 63) / 64 * 64) <= ZRO_HI).
  { unfold shad, ASHOFF, ZRO_LO, ZRO_HI. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  split; [repeat split; try lia; try (apply Z_mod_mult); unfold Shadow.KEND; lia|].
  split.
  - split; [unfold ZRO_LO in S1; lia|]. split; [unfold ZRO_HI in S1; lia|]. intros i Hi. apply (GlueA.TwinB.wb_wviewA bsegs).
    apply (proj2 (Z (shad (A / 64 * 64) + i) ltac:(lia))).
  - apply (rng_sub _ _ _ _ _ RS); unfold ZRO_LO, ZRO_HI in S1; lia.
Qed.

Lemma lit_low_inv : forall st a len, RangeC.TwinB.RangeC.lit_low st a len = true -> to_Z len <= 4096 ->
  W64.wt a = false /\ 0x10040 <= to_Z (W64.wl a) /\ to_Z (W64.wl a) + to_Z len + 64 <= 0x22d00 /\ find_op RangeC.TwinB.RangeC.ZRO_ID (s_ops st) = Some [].
Proof.
  intros st a len H NR. unfold RangeC.TwinB.RangeC.lit_low in H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "Q" in apply andb_prop in H as [H X] end.
  apply negb_true_iff in H. apply Uint63.leb_spec in Q2, Q1, Q0. change (to_Z 65600%uint63) with 65600 in Q2. change (to_Z 142592%uint63) with 142592 in Q1, Q0.
  pose proof (to_Z_bounded len) as LB.
  rewrite !Uint63.add_spec in Q0. change (to_Z 64%uint63) with 64 in Q0.
  rewrite (Z.mod_small (to_Z len + 64)) in Q0 by (change wB with (2 ^ 63); lia). rewrite Z.mod_small in Q0 by (change wB with (2 ^ 63); lia).
  destruct (find_op RangeC.TwinB.RangeC.ZRO_ID (s_ops st)) as [[|? ?]|]; try discriminate Q.
  split; [exact H|]. split; [lia|]. split; [lia| reflexivity].
Qed.
End TwinB.
