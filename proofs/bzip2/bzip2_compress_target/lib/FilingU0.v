(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW Spec04 ThmCompressAsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.ThmCompressAsan U.S0B2BCStmt U.S0B2BDStmt.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require S0H_Iface S0H_Cover.

Theorem join_std : forall timg, tgt_side04 timg ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false)
    ShippedBudgets.lim_source ShippedBudgets.lim_target S0img timg.
Proof.
  unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
  intros timg HT enS enT inp HeS HeT Hi _.
  destruct (s0_side04 enS inp HeS Hi) as [ES TS]. destruct (HT enT inp HeT Hi) as [ET TT].
  split; [exact ES|]. split; [exact ET|].
  intro tr. rewrite (TS tr). symmetry. exact (TT tr).
Qed.

Section Lib.

  Theorem tgt_ubsan : tgt_side04 U.ThmCompressAsan.U0img.
  Proof. exact U.ThmCompressAsan.s0_side04. Qed.

  Theorem compress_ubsan_std :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false)
      ShippedBudgets.lim_source ShippedBudgets.lim_target S0img U.ThmCompressAsan.U0img.
  Proof. exact (join_std U.ThmCompressAsan.U0img tgt_ubsan). Qed.
End Lib.
