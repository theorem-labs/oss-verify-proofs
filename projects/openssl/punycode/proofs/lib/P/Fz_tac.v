(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.
Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.
Ltac ls := lstep; try sb_fix.

(* [comment removed for export] *)
Ltac fold_sx32 :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
        replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  end.

Ltac xs := ls; fold_sx32; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xs_to p := repeat (tryif at_pc p then fail else xs).

(* [comment removed for export] *)
Ltac show_reg R k := let v := eval hnf in (Sem.reg_get R k) in idtac k "=" v.
Ltac show_regs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
  idtac "pc" pc;
  show_reg R (1%bv : reg); show_reg R (2%bv : reg); show_reg R (5%bv : reg); show_reg R (6%bv : reg); show_reg R (7%bv : reg);
  show_reg R (8%bv : reg); show_reg R (9%bv : reg); show_reg R (10%bv : reg); show_reg R (11%bv : reg); show_reg R (12%bv : reg);
  show_reg R (13%bv : reg); show_reg R (14%bv : reg); show_reg R (15%bv : reg); show_reg R (16%bv : reg); show_reg R (17%bv : reg);
  show_reg R (18%bv : reg); show_reg R (19%bv : reg); show_reg R (20%bv : reg); show_reg R (21%bv : reg); show_reg R (22%bv : reg);
  show_reg R (23%bv : reg); show_reg R (24%bv : reg); show_reg R (25%bv : reg); show_reg R (26%bv : reg); show_reg R (27%bv : reg);
  show_reg R (28%bv : reg); show_reg R (29%bv : reg); show_reg R (30%bv : reg); show_reg R (31%bv : reg) end.
