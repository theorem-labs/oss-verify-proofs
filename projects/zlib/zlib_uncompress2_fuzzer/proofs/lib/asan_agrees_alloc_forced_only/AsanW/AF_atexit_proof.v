(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow ITreeA SysStepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg ABase RtCells F_syscalls.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StrwF SysStepF StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AF_atexit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac sort_lits :=
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.

Section CANSEC1. Context {rc : runConstT}.

Local Ltac lits_in H :=
  unfold atx_cells1, atx_cells2, atx_cellsR, AATX, AATX_N, AATX_CALL, ACOV_HOOK, AAEF_GUARD, AAEF_INCB, ALIBC, ACOV_FLAG in H;
  let x := eval cbv in AATX in
  repeat match type of H with context [(x + ?b)%Z] => let v := eval vm_compute in (x + b)%Z in change (x + b)%Z with v in H end.

Theorem atexit_guard_proofA : atexit_guard_specA_stmt.
Proof.
  red. intros until w2. intros ST AX F1 A1 LIBC MI -> LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  lits_in AX. lits_in F1. lits_in A1. unfold ALIBC in LIBC. unfold AAEF_GUARD, AATEXIT.
  destruct AX as (AX1 & AX2 & AX3 & AX4 & AX5 & AX6 & AX7).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + AATX_N)]%Z m) as MU. unfold AATX, AATX_N in MU.
  pose proof (wmono_refl asegs m) as WM.
  hstep. carve_frame 48%nat ST. do 5 hstep.
  do 6 hstep.
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false.
  astep. astep.
  hstep. nlit. astep. astep.
  do 9 hstep.
  hstep. hstep. hstep. astep. hstep.
  hstep. do 5 hstep. release_frame FR ST (bv_unsigned sp). hstep. hstep.
  unfold atexitA_post, atx_cells2, AATX, AATX_N, AATX_CALL, ACOV_HOOK, AAEF_GUARD. cbn [Z.add]. sys_finish.
Qed.

Theorem funcs_on_exit_proofA : funcs_on_exit_specA_stmt.
Proof.
  red. intros until tm1. intros ST AX LIBC COV MI LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  unfold ALIBC in LIBC. unfold ACOV_FLAG in COV. unfold AFUNCS_ON_EXIT.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (AATX, AATX + 24)]%Z m) as MU. unfold AATX in MU.
  pose proof (wmono_refl asegs m) as WM.
  destruct AX as [AX|[AX CB0]]; lits_in AX; [| lits_in CB0].
  -
    destruct AX as (AX1 & AX2 & AX3 & AX4 & AX5 & AX6 & AX7).
    hstep. carve_frame 48%nat ST. do 5 hstep.
    do 5 hstep. hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    astep. astep. hstep. nlit. hstep.
    hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. nlit. hstep. hstep.
    hstep. hstep. hstep. astep. hstep.
    do 7 hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    do 5 hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. do 5 hstep. release_frame FR ST (bv_unsigned sp). hstep. hstep.
    hstep. astep. hstep.
    unfold funcs_on_exitA_post, AATX. cbn [Z.add]. sys_finish.
  -
    destruct AX as (AX1 & AX2 & AX3 & AX4 & AX5 & AX6 & AX7 & AX8 & AX9).
    hstep. carve_frame 48%nat ST. do 5 hstep.
    do 5 hstep. hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    astep. astep. hstep. nlit. hstep.
    hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
    hstep. hstep. hstep. nlit. hstep. hstep.
    hstep. hstep. hstep. astep. hstep.
    do 6 hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
    do 5 hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. nlit. hstep. hstep.
    hstep. hstep. hstep. astep. hstep.
    do 7 hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    do 5 hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. do 5 hstep. release_frame FR ST (bv_unsigned sp). hstep. hstep.
    hstep. astep. hstep.
    unfold funcs_on_exitA_post, AATX. cbn [Z.add]. sys_finish.
Qed.
End CANSEC1.
