(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.CkU Require Import CrcAGlue.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac show_reg n := let w := getreg n in idtac "x" n "=" w.
Ltac show_pc := lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.

Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.

Ltac regs_with R n y :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
  eval cbv beta iota delta [tset mkR] in (tset p y R).

Ltac ck_join n okpc :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
      let H := fresh "CONT" in
      enough (H : forall y : word, evtF segs RNG Q (MS (tset p y R) F (Z_to_bv 64 okpc) fc rv m ro));
      [ | let y := fresh "y" in intros y;
          let g := lazymatch goal with |- ?g => g end in
          let g' := eval cbv beta iota delta [tset mkR] in g in change g' ]
  end.

Ltac ck_done n :=
  lazymatch goal with
  | CONT : forall y : word, evtF _ _ _ _ |- _ =>
      let v := reg_val n in exact (CONT v)
  end.

Lemma sx32_sxz : forall x, 0 <= x < 2^64 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 (sxz x).
Proof.
  intros x Hx. unfold sx32, sxz. rewrite unsigned_lit by lia. symmetry. apply Z_to_bv_mod64.
Qed.
