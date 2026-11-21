(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface Deflate ZApiInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Zlib_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wq := (Z_to_bv 64).
Local Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem compressBound_proof : compressBound_stmt.
Proof.
  unfold compressBound_stmt. intros until n. intros Hn -> MI. unfold Z_COMPRESSBOUND, MallocRep.wz.
  do 11 zstep.
  apply evt_done. unfold compressBound_post. do 15 eexists. split; [reflexivity|].
  intros Hb. cbn [z_bound the_zapi zinst]. unfold compressBound_m, MallocRep.wz.
  (* [1.4: compressBound saturates; below ZH_MAX the sum does not wrap, so the overflow mask is 0] *)
  assert (HX : n <= n + n ≫ 12 + (n ≫ 14 + n ≫ 25) + 13 < 18446744073709551616).
  { rewrite !Z.shiftr_div_pow2 by lia. unfold ZH_MAX in Hb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia. }
  replace (Z.land (n + n ≫ 12 + (n ≫ 14 + n ≫ 25) + 13) 18446744073709551615) with (n + n ≫ 12 + (n ≫ 14 + n ≫ 25) + 13).
  2:{ change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small.
      change (2^64) with 18446744073709551616. lia. }
  replace (n + n ≫ 12 + (n ≫ 14 + n ≫ 25) + 13 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z Z.opp Z.add Z.land]. rewrite Z.lor_0_l.
  rewrite wrap64_id; [f_equal; lia|].
  rewrite !Z.shiftr_div_pow2 by lia. unfold ZH_MAX in Hb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. lia.
Qed.
End WithCeiling0.
