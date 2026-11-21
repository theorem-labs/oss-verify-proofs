(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import InfBBase InfBTables InfB_w7tab InfB_w7tab16.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition dist_src (S : Z) (cf : Z -> Z) (TA nd XT NS : Z) (rd : Z -> Z) : Prop :=
  forall m : amem, f32arr bsegs m (S + 1384) 1444 cf -> mem_inv bsegs m ->
    shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
    shadow_bytes m 2147469900 2147469916 (fun _ => 0) ->
    dtab m TA nd rd /\ dtab16 m TA nd rd
    /\ shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0).

Lemma dist_src_dyn : forall S cf o nd, (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) -> 0 <= o -> 0 <= nd -> o + nd <= 1444 ->
  dist_src S cf (S + 1384 + 4 * o) nd S 897 (rdc cf (CDyn o)).
Proof.
  intros S cf o nd CFR Ho Hn Hon m CODES MI SHS SHDF.
  split; [apply dtab_dyn; [exact CODES| exact CFR| lia| lia| lia]|].
  split; [apply dtab16_dyn; [exact CODES| exact CFR| lia| lia| lia]| exact SHS].
Qed.
Lemma dist_src_fix : forall S cf, dist_src S cf 152160 32 152160 16 (rdc (fun _ => 0) CDistfix).
Proof.
  intros S cf m CODES MI SHS SHDF.
  split; [exact (dtab_distfix m MI)|]. split; [exact (dtab16_distfix m MI)| exact SHDF].
Qed.
End CANSEC1.
