(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AArr U2ABlob InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2cA_glue.
Definition st_u2_initL (osz ki vlen vofs vext vlb vdb vnc vnl vnd vsh : Z) : ist :=
  IST HEAD 0 (-1) ki 0 0 0 osz 0 vlen vofs vext (CDyn 0) (CDyn 0) vlb vdb vnc vnl vnd vsh 0 0 0.

Lemma ainv_u2_initL : forall S D n OB osz ki W0 (lf cf : Z -> Z) vlen vofs vext vlb vdb vnc vnl vnd vsh,
  0 <= ki <= n -> 0 <= osz <= 262144 ->
  (forall i, 0 <= lf i < 65536) -> (forall i, 0 <= cf i < 4294967296) ->
  0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
  0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
  ainv (icx_of S D n OB osz 0 ki 0 W0) (st_u2_initL osz ki vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf.
Proof.
  intros S D n OB osz ki W0 lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh Hn Hosz Hlf Hcf R1 R2 R3 R4 R5 R6 R7 R8 R9.
  unfold ainv, RNG, WIN, MODE, st_u2_initL, icx_of; icx_cbn. cbv [N_CODES N_LENS WIN_SIZE].
  split; [| split].
  - split_conj; first [assumption | lia_std | change (2 ^ 0) with 1; lia_std | intros i _; apply Hlf | intros i _; apply Hcf].
  - split; [intros _; split; reflexivity | intros C; exfalso; exact (C eq_refl)].
  - split_conj.
    + left. reflexivity.
    + intros _. split; [left; reflexivity | reflexivity].
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. unfold codes_liveP. cbv [LEN_ LIT HEAD]. lia_std.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros [E|E]; exfalso; revert E; cbv; discriminate.
Qed.


