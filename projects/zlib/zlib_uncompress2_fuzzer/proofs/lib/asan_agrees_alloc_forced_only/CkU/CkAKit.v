(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.CkU Require Import CkAImg CkATables CkAShadow CkAIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.CkU Require Export CrcATac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac acc_hint_shrng :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
      match goal with H : shrng RNG ?lo ?hi |- _ => apply (shrng_acc RNG lo hi a H); lia end
  end.

Ltac pose_sp_range sp :=
  let R := fresh "RSP" in
  pose proof (bv_unsigned_in_range 64 sp) as R; unfold bv_modulus in R;
  change (2 ^ Z.of_N 64) with 18446744073709551616 in R.

Ltac ck_slow_steps :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; ck_slow_steps
  | _ => idtac
  end.

Ltac ck_branch U JOIN CK :=
  ck_join U JOIN;
  [ let K := fresh "K" in let K2 := fresh "K2" in
    if_cases K; zify_cond K;
    [ ck_slow_steps; if_cases K2;
      [ ck_done U
      | exfalso; zify_lts K2; clear - CK K K2; Z.div_mod_to_equations; lia ]
    | ck_done U ]
  | ].

Tactic Notation "leafcall" uconstr(SPEC) :=
  eapply evtF_cut;
  [ eapply SPEC
  | let ms' := fresh "ms'" in let PO := fresh "POST" in
    intros ms' PO; hnf in PO; destruct_exs PO; subst ms';
    try (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end) ].
