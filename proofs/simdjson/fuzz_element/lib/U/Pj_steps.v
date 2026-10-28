(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Notation usegs := Image.usegs.

Lemma amoadd_d_site : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (v : Z) (Q : machine_state -> Prop),
  rw_cells usegs m 0xee0b8 [C8 (Z_to_bv 64 v)] -> mem_inv usegs m -> (0 <= v < 2^62)%Z ->
  (forall m', rw_cells usegs m' 0xee0b8 [C8 (Z_to_bv 64 (v + 1))] -> mem_inv usegs m' ->
     evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0xee0b8) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9e2ac) fc None m' (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0xee0b8) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x9e2a8) fc None m (seg_rom usegs)).
Proof.
  intros until Q. intros CELL MI RV K.
  amo_step.
  change (amo_val AMO_ADD (Z_to_bv 64 v) (Z_to_bv 64 1)) with (Z_to_bv 64 v + Z_to_bv 64 1 : word) in CELL.
  rewrite lit_add_lit in CELL.
  apply K; assumption.
Qed.

Lemma amo32_add_bytes_lit : forall a b, (0 <= a < 2^32)%Z -> (0 <= b < 2^32)%Z ->
  Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 a)))) (Z_to_bv 32 b)))
  = le4 (Z_to_bv 64 (a + b)).
Proof.
  intros a b Ha Hb. cbn [amo_val]. rewrite bv_add_unsigned.
  rewrite low32_unsigned, le_bytes_to_word_le4, !Z_to_bv_unsigned.
  unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !(Z.mod_small a (2^64)) by lia. rewrite !(Z.mod_small a (2^32)) by lia. rewrite !(Z.mod_small b (2^32)) by lia.
  rewrite (Z_to_le_bytes_mod 4 (a + b) 32) by lia. rewrite (Z_to_le_bytes_mod 4 (a + b) 64) by lia. reflexivity.
Qed.

Ltac amo32_fix_lit := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD
         (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 ?a)))) (Z_to_bv 32 ?b))))) _) =>
      rewrite (amo32_add_bytes_lit a b) by lia; mem_after_store
  end.

Lemma amoadd_w_site : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (k : Z) (idv : word) (Q : machine_state -> Prop),
  rw_cells usegs m 0xedf08 [C4 (Z_to_bv 64 k)] -> rw_cells usegs m 0xeddd0 [C4 idv] -> mem_inv usegs m -> (0 <= k < 30)%Z ->
  (forall m' a1', rw_cells usegs m' 0xedf08 [C4 (Z_to_bv 64 (k + 1))] -> rw_cells usegs m' 0xeddd0 [C4 (Z_to_bv 64 (k + 1))] -> mem_inv usegs m' ->
     evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xeddc8) a1' (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xb6e6c) fc None m' (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xeddc8) (Z_to_bv 64 0xedf08) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0xb6e60) fc None m (seg_rom usegs)).
Proof.
  intros until Q. intros NID IDC MI RK K.
  amo_step. amo32_fix_lit.
  replace (sx32 (Z_to_bv 64 k)) with (Z_to_bv 64 k)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep.
  apply K; assumption.
Qed.

