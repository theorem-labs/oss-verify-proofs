(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import AsanMain HaltsAsanB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import ProgExits.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ADriver_iface AMain_final AH_huf_final AH_huf_libc.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_HaltsAsanBClosed () := "C59OSSVerify5KrLib5AsanW<AH_huf_finalBfuzz_client_of_libC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AMain_final?asan_impl_finalC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:HaltsAsanBChalts_asanB_of_implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=ADriver_iface6ASTAGEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;AH_huf_libc?huf_lib_closedAC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?forced_only_cfg".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem halts_asanB : halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source EXITS02 (mkImage asegs a_init_pc a_phdrs).
Proof.
  exact (halts_asanB_of_impl ASTAGE (asan_impl_final (fuzz_client_of_lib huf_lib_closedA)) forced_only_cfg
           (forced_only_cfg_least ACFG)).
Qed.
