(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ITree Nodes Decode RegsEquiv Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg Harness_iface PlainMain_asm RMalloc_iface RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_huf_iface RZ_seq_iface RZ_block_iface RZ_tbl RZ_hufinv RZ_dblock RZ_client.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import PState Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section LIB.
  (* [comment removed for export] *)
  Hypothesis H1X : huf_1x_stmt.
  Hypothesis H4X : huf_4x_stmt.
  Hypothesis H1W : huf_1x1_wksp_stmt.
  Hypothesis H4W : huf_4x_wksp_stmt.
  Hypothesis HSD : zd_seq_default_stmt.
  Hypothesis HSS : zd_seq_split_stmt.
  Hypothesis HSL : zd_seq_long_stmt.

  (* [comment removed for export] *)
  Lemma plain_fuzz_of_lib : forall rc : runConstT, @fuzz_one_stmt rc.
  Proof.
    intros rc.
    exact (@zd_fuzz_one_client rc (ptbl HUFINVw) ptblw_laws (zd_dblock_closed H1X H4X H1W H4W HSD HSS HSL) rmalloc_spec rfree_spec_proof).
  Qed.

  (* [comment removed for export] *)
  Theorem plain_closed_of_lib : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs u_init_pc u_phdrs) en inp ->
      valid_input_either inp ->
      impl usegs (at_node usegs) (Prog.prog usegs UREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
           (ms0 usegs u_init_pc u_phdrs en inp).
  Proof. exact (plain_impl plain_fuzz_of_lib). Qed.
End LIB.
