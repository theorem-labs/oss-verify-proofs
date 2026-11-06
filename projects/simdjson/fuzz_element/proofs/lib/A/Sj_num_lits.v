(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma num_lits_of_af : forall RT, art_facts RT -> num_lits_acc RT.
Proof.
  intros RT AF Σ m HA. pose proof (af_acc_lits RT AF Σ m HA) as F. rewrite Forall_forall in F.
  unfold NUM_LITS. repeat constructor; cbn [fst snd].
  - apply (F (0x2a2e0, 10416)). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
  - apply (F (0x2cc60, 640)). unfold ACC_LITS. repeat (first [left; reflexivity | right]).
Qed.
