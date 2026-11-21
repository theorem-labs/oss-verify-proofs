(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Common Require RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module F_syscalls.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Lib Require Import SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PlainS9 Require Import PImg.
Import ListNotations.
Open Scope bv_scope.

Definition sysret_entry := 0x1927c%Z.
Definition read_entry := 0x20b10%Z.
Definition close_entry := 0x20ab0%Z.
Definition open_entry := 0x19130%Z.


Definition sysret_post {RCa1 : RunCtx}  (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma sysret_spec {RCa1 : RunCtx}  : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (errv : word) (lo : Z),
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (errno_addr tp) [C4 errv] ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (sysret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 errv F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1927c) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  -
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.

End F_syscalls.

Module RunDraw.
From Stdlib Require Import ZArith. From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Common Require Export RunDraw.
Open Scope Z_scope.

Ltac atop_facts :=
  lazymatch goal with
  | _ : (0x7fff7f800000 <= @ATOP _ <= 0x7FFFFF800000)%Z |- _ => idtac
  | |- context [@ATOP _] => pose proof atop_range as ATOPR
  | _ : context [@ATOP _] |- _ => pose proof atop_range as ATOPR
  | _ => idtac
  end.
Ltac sec_facts :=
  lazymatch goal with
  | _ : (0 <= @SECRET _ < 2^64)%Z |- _ => idtac
  | _ => pose proof sec_range as SECR
  end.

Definition pstage_len_sig : { n : nat | Z.of_nat n = 65536 }.
Proof. exists (Z.to_nat 65536). apply Z2Nat.id. apply Z.leb_le. reflexivity. Qed.
Definition PSTAGE_LEN : nat := proj1_sig pstage_len_sig.
Lemma PSTAGE_LEN_Z : Z.of_nat PSTAGE_LEN = 65536.
Proof. exact (proj2_sig pstage_len_sig). Qed.
Ltac stage_facts :=
  lazymatch goal with
  | _ : Z.of_nat PSTAGE_LEN = 65536 |- _ => idtac
  | |- context [PSTAGE_LEN] => pose proof PSTAGE_LEN_Z as PSTAGER
  | _ : context [PSTAGE_LEN] |- _ => pose proof PSTAGE_LEN_Z as PSTAGER
  | _ => idtac
  end.
Ltac lia := atop_facts; stage_facts; Stdlib.micromega.Lia.lia.
Ltac nia := atop_facts; stage_facts; Stdlib.micromega.Lia.nia.
End RunDraw.
