(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AMain_final AH_huf_final AMain_huf AH_huf_libc.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMain_hufc () := "C5ARocqVerifyHarness?AgentSubmission5BothW9AMain_huf@base_asan_of_libC4ARocqVerifyHarness?AgentSubmission8BothMainBplain_tree_ok_stmtC5ARocqVerifyHarness?AgentSubmission5BothW;AH_huf_libc?huf_lib_closedA".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_asan_hufc : plain_tree_ok_stmt ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_AMain_hufc ()) [] "h05PLAINp;2g0000j20Tg0015f0g0025'0W0o"). Qed.
