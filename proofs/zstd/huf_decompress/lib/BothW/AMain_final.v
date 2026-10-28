(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMain_final () := "C5ARocqVerifyHarness?AgentSubmission5BothW8AFreeAll8AHI_freeC5ARocqVerifyHarness?AgentSubmission5BothW=AMain_closedIAasan_impl_of_freec5ARocqVerifyHarness?AgentSubmission5BothW;AMain_final;client_stmtI5ARocqVerifyHarness?AgentSubmission3Lib8RunConst9runConstT00".

(* [comment removed for export] *)
Definition client_stmt : Prop := forall rc : runConstT, fuzz_oneA_stmtB (AI_of (@AHI_free rc)) AFake_iface.afake_rng.

Theorem asan_impl_final : client_stmt -> asan_impl_stmt ASTAGE.
Proof.
ltac2:(KReplay.run1 (kr_t_AMain_final ()) [] "h06CLIENTh12rcp;1p;2g0000j11Tg000lj20Tg0026g0038f0R0#1W1/00W0o"). Qed.

(* [comment removed for export] *)
Theorem base_asan_of_client : plain_tree_ok_stmt -> client_stmt ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. intros PLAIN CLIENT. exact (base_asan ASTAGE PLAIN (asan_impl_final CLIENT)). Qed.

(* [comment removed for export] *)
