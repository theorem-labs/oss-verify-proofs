(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 Atp_defsA Atp_objcA Atp_objmA Atp_objgA Atp_walkA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem esc_okA_closed : forall RT, art_facts RT -> rt_contracts2 RT -> esc_okA RT.
Proof.
  intros RT AF RC2 E d PMc Σ Σ1 I OK HELEM FDO MST CTX. split.
  - exact (esc_sso RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX).
  - exact (esc_heap RT AF RC2 E OK d HELEM PMc FDO MST Σ Σ1 I CTX).
Qed.

Theorem atp_obj_topA_closed : forall RT, art_facts RT -> rt_contracts2 RT -> forall E, aenvA_ok E -> atp_obj_cpsA RT E (Nat.pred TAPE_MAX_DEPTH).
Proof. intros RT AF RC2 E OK. exact (atp_obj_topA RT AF RC2 (esc_okA_closed RT AF RC2) E OK). Qed.
Theorem atp_arr_topA_closed : forall RT, art_facts RT -> rt_contracts2 RT -> forall E, aenvA_ok E -> atp_arr_cpsA RT E (Nat.pred TAPE_MAX_DEPTH).
Proof. intros RT AF RC2 E OK. exact (atp_arr_topA RT AF RC2 (esc_okA_closed RT AF RC2) E OK). Qed.
