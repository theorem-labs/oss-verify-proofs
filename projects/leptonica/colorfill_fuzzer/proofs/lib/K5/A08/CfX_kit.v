(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Mem MState.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
Import ListNotations.
Open Scope Z_scope.

Lemma cfx_amo_aligned : forall a : Z, 0 <= a < 2^64 -> a mod 4 = 0 -> amo_aligned AW (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Ltac cfx_amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).
(* [comment removed for export] *)
Ltac cfx_amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_is_x0; simp_regs; cfx_amo_align AMO; exec_cbv; cfx_amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
Lemma amo_add1_bytes : forall rc, 0 <= rc -> rc + 1 < 2^32 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 rc)))) (Z_to_bv 32 1))) = le4 (Z_to_bv 64 (rc + 1)).
Proof.
  intros rc H0 H1. unfold amo_val. change (le4 (Z_to_bv 64 (rc + 1))) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (rc + 1)))). f_equal.
  rewrite bv_add_unsigned. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  rewrite !unsigned_lit by lia. change (2 ^ Z.of_N 32) with (2^32). rewrite !Z.mod_small by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small 1) by lia.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Ltac cfx_amo_add1 AMO rc side :=
  cfx_amo_step AMO;
  lazymatch goal with |- context [Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD ?o ?s))] =>
    replace (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD o s))) with (le4 (Z_to_bv 64 (rc + 1)))
      by (symmetry; apply amo_add1_bytes; side) end;
  mem_after_store.

(* [comment removed for export] *)
Lemma amo_sub1_bytes : forall rc, 1 <= rc < 2^31 ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 rc)))) (Z_to_bv 32 4294967295))) = le4 (Z_to_bv 64 (rc - 1)).
Proof.
  intros rc H. unfold amo_val. change (le4 (Z_to_bv 64 (rc - 1))) with (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (rc - 1)))). f_equal.
  rewrite bv_add_unsigned. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  rewrite !unsigned_lit by lia. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small rc) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). rewrite (Z.mod_small 4294967295) by lia.
  change (2^32) with 4294967296 in *. change (2^31) with 2147483648 in *. Z.div_mod_to_equations. lia.
Qed.
Ltac cfx_amo_sub1 AMO rc side :=
  cfx_amo_step AMO;
  lazymatch goal with |- context [Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD ?o ?s))] =>
    replace (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD o s))) with (le4 (Z_to_bv 64 (rc - 1)))
      by (symmetry; apply amo_sub1_bytes; side) end;
  mem_after_store.
