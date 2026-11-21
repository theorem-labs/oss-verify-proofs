(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec Mem InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AS Require Import HexScanFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section RwZero.
  Variable segs : list Segment.
  Variable seg : Segment.
  Variable s : PrimString.string.
  Variables lo hi : Z.
  Hypothesis SEGB : seg_bytes seg = [s].
  Hypothesis RD : seg_readable seg = true.
  Hypothesis WR : seg_writable seg = true.
  Hypothesis BASE : Z.of_N (seg_base seg) = lo.
  Hypothesis LEN : Z.of_N (Z.to_N (Uint63.to_Z (PrimString.length s) / 2)) = hi - lo.
  Hypothesis FS : forall z, lo <= z -> z + 1 <= hi -> find_segment segs z 1 = Some seg.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis HI64 : hi <= 2 ^ 64.

  Lemma rw_bytes_b_zero_pointwise : forall n A,
    lo <= A -> A + Z.of_nat n <= hi ->
    (forall i, 0 <= i < Z.of_nat n -> hex_byte_at s (Z.to_N (A - lo + i)) = Some (Z_to_bv 8 0)) ->
    rw_bytes_b segs A (repeat (Z_to_bv 8 0) n) = true.
  Proof.
    induction n as [|n IH]; intros A HA HB HP; [reflexivity|].
    cbn [repeat rw_bytes_b].
    assert (UA : bv_unsigned (wa A) = A) by (apply wa_unsigned; lia).
    assert (H0 : hex_byte_at s (Z.to_N (A - lo)) = Some (Z_to_bv 8 0)).
    { specialize (HP 0 ltac:(lia)). rewrite Z.add_0_r in HP. exact HP. }
    assert (SB : segment_byte_at [s] (Z.to_N (A - lo)) = Some (Z_to_bv 8 0)).
    { cbn [segment_byte_at]. replace (Z.to_N (A - lo) <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
      exact H0. }
    assert (ROM : seg_rom segs (wa A) = Some (Z_to_bv 8 0)).
    { unfold seg_rom, memory_read. rewrite UA. change (Z.of_N 1) with 1. rewrite (FS A) by lia. rewrite RD, BASE, SEGB.
      change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite SB. reflexivity. }
    assert (WV : wview segs (fun _ => None) (wa A) = Some (Z_to_bv 8 0)).
    { unfold wview. rewrite UA. rewrite (FS A) by lia. rewrite WR, BASE, SEGB. exact SB. }
    rewrite ROM, WV. replace (bv_eqb (Z_to_bv 8 0) (Z_to_bv 8 0)) with true by reflexivity. cbn [andb].
    apply IH; [lia | lia |]. intros i Hi. replace (A + 1 - lo + i) with (A - lo + (i + 1)) by lia. apply HP. lia.
  Qed.

  Lemma rw_bytes_b_zero_fast : forall A n,
    lo <= A -> 0 <= n -> A + n <= hi ->
    scanP (byte_zeroI s) 64 (Uint63.of_Z (A - lo)) (Uint63.of_Z n) = true ->
    rw_bytes_b segs A (repeat (Z_to_bv 8 0) (Z.to_nat n)) = true.
  Proof.
    intros A n HA Hn HB SC.
    assert (WB : Uint63.wB = 9223372036854775808) by reflexivity.
    assert (SZ : hi - lo < 4611686018427387904).
    { pose proof (Uint63.to_Z_bounded (PrimString.length s)) as B. rewrite WB in B. rewrite <- LEN.
      rewrite Z2N.id by (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; lia. }
    assert (Eb : Uint63.to_Z (Uint63.of_Z (A - lo)) = A - lo) by (rewrite Uint63.of_Z_spec, WB; apply Z.mod_small; lia).
    assert (En : Uint63.to_Z (Uint63.of_Z n) = n) by (rewrite Uint63.of_Z_spec, WB; apply Z.mod_small; lia).
    apply rw_bytes_b_zero_pointwise; [exact HA | rewrite Z2Nat.id by lia; exact HB |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    pose proof (scanP_sound (byte_zeroI s) 64 _ _ SC) as S. rewrite Eb, En, WB in S.
    specialize (S ltac:(lia) i Hi). apply byte_zeroI_sound in S.
    rewrite Uint63.of_Z_spec, WB, Z.mod_small in S by lia. exact S.
  Qed.
End RwZero.
