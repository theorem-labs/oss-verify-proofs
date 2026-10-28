(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sj_hkitB Atp_h_vkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma psigned_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia. replace (z <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma pshiftr_16_4 : forall c, 0 <= c -> Z.shiftr (16 * c) 4 = c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (c * 2^4) by lia. apply Z.div_mul. lia. Qed.
Lemma pshiftr_16_3 : forall c, 0 <= c -> Z.shiftr (16 * c) 3 = 2 * c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (2 * c * 2^3) by lia. apply Z.div_mul. lia. Qed.
Lemma pshiftr_small0 : forall x n, 0 <= x < 2^n -> 0 <= n -> Z.shiftr x n = 0.
Proof. intros x n Hx Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma rw_cells_of_bytes : forall (m : mem) a cs, cells_wf cs -> bytes_at asegs m a (cells_bytes cs) -> wr_at asegs m a (Z.of_nat (cells_size cs)) -> rw_cells asegs m a cs.
Proof. intros m a cs WF HB HW. split; [split; [exact WF| exact HB]| exact HW]. Qed.
