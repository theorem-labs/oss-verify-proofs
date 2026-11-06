(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AMain_final AH_huf_final AMain_huf AH_huf_libc.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMain_hufc () := "C59OSSVerify5KrLib5AsanW9AMain_huf@base_asan_of_libC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8AsanMainBplain_tree_ok_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AH_huf_libc?huf_lib_closedAC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_asan_hufc : plain_tree_ok_stmt ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage asegs a_init_pc a_phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_AMain_hufc ()) [] "h05PLAINp;2g0000j20Tg0015f0g0025'0W0o"). Qed.
