(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma num_lits_of_af : forall RT, art_facts RT -> num_lits_acc RT.
Proof.
  intros RT AF Σ m HA. pose proof (af_acc_lits RT AF Σ m HA) as F. rewrite Forall_forall in F.
  unfold NUM_LITS. repeat constructor; cbn [fst snd].
  - apply (F (0x28700, 10416)). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
  - apply (F (0x2b080, 640)). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
Qed.
