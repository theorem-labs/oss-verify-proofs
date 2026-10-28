(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AMain_final AH_huf_final.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMain_huf () := "C5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_final=huf_lib_stmtAC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_finalBfuzz_client_of_libC5ARocqVerifyHarness?AgentSubmission5BothW;AMain_finalCbase_asan_of_clientC4ARocqVerifyHarness?AgentSubmission8BothMainBplain_tree_ok_stmtI5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_asan_of_lib : plain_tree_ok_stmt -> (forall rc : runConstT, huf_lib_stmtA rc) ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_AMain_huf ()) [] "h03LIBh15PLAINh22rcp;1p;2g0000j12Tg0015j11Tg002?j20Tg003Ig004If0R0#2]2f1%10'0W0W1o"). Qed.
