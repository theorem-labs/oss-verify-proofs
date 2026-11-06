(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit Zpm Zpl Zq2 Sj_rtf Zqc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma num_lits_of_af : forall RT, art_facts RT -> num_lits_acc RT.
Proof.
  intros RT AF Σ m HA. pose proof (af_acc_lits RT AF Σ m HA) as F. rewrite Forall_forall in F.
  unfold NUM_LITS. repeat constructor; cbn [fst snd].
  - apply (F (0x285a0, 10416)). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
  - apply (F (0x2af20, 640)). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
Qed.
