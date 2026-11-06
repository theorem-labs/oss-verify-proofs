(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare Frame RefMemcpyLib.
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition sbyte (b : byte) : Z := bv_signed b.

(* [comment removed for export] *)
Definition apart_win (usp frame a len : Z) : Prop :=
  a + len <= usp - frame \/ usp <= a.

(* [comment removed for export] *)
Definition shadow_ok (segs : list Segment) (M : word -> option byte) (usp frame sb a : Z) : Prop :=
  exists k : byte,
    rdn segs M (Z_to_bv 64 (sb + a / 8)) 1 = Some [k]
    /\ sb + a / 8 < 2 ^ 64
    /\ apart_win usp frame (sb + a / 8) 1
    /\ (sbyte k = 0 \/ a mod 8 < sbyte k).

(* [comment removed for export] *)
Definition asan_payload_ok (segs : list Segment) (M : word -> option byte)
           (usp frame got : Z) (buf : word) (n : Z) : Prop :=
  exists (g sbw : word) (bs : list byte),
    rdn segs M (Z_to_bv 64 got) 8 = Some (word_to_le_bytes 8 g)
    /\ apart_win usp frame got 8
    /\ rdn segs M g 8 = Some (word_to_le_bytes 8 sbw)
    /\ bv_unsigned g + 8 <= 2 ^ 64
    /\ apart_win usp frame (bv_unsigned g) 8
    /\ rdn segs M buf (Z.to_nat n) = Some bs
    /\ (forall i, 0 <= i < n ->
          shadow_ok segs M usp frame (bv_unsigned sbw) (bv_unsigned buf + i)).

Definition asan_utf8_stmt (segs : list Segment) (entry frame got : Z) : Prop :=
  forall (R : bvmap 5 word) (M rom : word -> option byte) (ret buf : word) (n : Z),
    ret_ok ret ->
    getr R 1%bv = ret ->
    getr R 10%bv = buf ->
    getr R 11%bv = Z_to_bv 64 n ->
    0 <= n < 2 ^ 31 ->
    bv_unsigned buf <> 0 ->
    bv_unsigned buf + n < 2 ^ 64 - 1 ->
    4096 + frame <= bv_unsigned (getr R 2%bv) ->
    store_ok segs M (Z_to_bv 64 (bv_unsigned (getr R 2%bv) - frame)) (Z.to_nat frame) = true ->
    (1 <= n <= 65536 -> asan_payload_ok segs M (bv_unsigned (getr R 2%bv)) frame got buf n) ->
    exists (R' : bvmap 5 word) (M' : word -> option byte),
      msteps segs (mkst R (Z_to_bv 64 entry) M rom) (mkst R' ret M' rom)
      /\ keeps_cs R R'
      /\ frame_mod M M' [(Z_to_bv 64 (bv_unsigned (getr R 2%bv) - frame), frame)].
End WithFP1.

