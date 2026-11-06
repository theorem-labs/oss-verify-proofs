(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Z45 Z5p Z68 Z5w Z77.
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
