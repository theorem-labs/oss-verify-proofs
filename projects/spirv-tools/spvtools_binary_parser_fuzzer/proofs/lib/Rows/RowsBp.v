(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common Require Import ClassifierRows.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require BaseUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Final Require FinalS1 FinalU1.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Require OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_RowsBp () := "C59OSSVerify5KrLib3Drv9BaseUbsan?base_ubsan_scfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Final7FinalS1Elib_contract_S1_finalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Final7FinalU1Elib_contract_U1_finalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv9BaseUbsan@base_ubsan_abortC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceEimage_brk_satisfiableI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsdSrcO_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgXTgtO_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C59OSSVerify5KrLib6Common>ClassifierRows>ca_iff_of_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Rows6RowsBp3CFGC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsdSrcO_spirv_tools_spvtools_binary_parser_fuzzer_repro1M7init_pcC1@~~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsdSrcO_spirv_tools_spvtools_binary_parser_fuzzer_repro1M5phdrsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgXTgtO_spvtools_binary_parser_fuzzer_ubsan1M7init_pcC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgXTgtO_spvtools_binary_parser_fuzzer_ubsan1M5phdrsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgWCla_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgWCla_spvtools_binary_parser_fuzzer_ubsan1M7init_pcC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgWCla_spvtools_binary_parser_fuzzer_ubsan1M5phdrsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Rows6RowsBp7base_bpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Cls7ClsInstOcla_accepts_binary_parser_ubsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common>ClassifierRows>cb_iff_of_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgWClb_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgWClb_spvtools_binary_parser_fuzzer_ubsan1M7init_pcC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgWClb_spvtools_binary_parser_fuzzer_ubsan1M5phdrsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Cls7ClsInstOclb_accepts_binary_parser_ubsanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Rows6RowsBp7src_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Rows6RowsBp7tgt_brkC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition CFG : SpuriousCfg := Run.mkSpuriousCfg false true true true true true.

Notation SRC := (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs) (only parsing).
Notation TGT := (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.phdrs) (only parsing).

Theorem base_bp : strong_universal_error_free_T_scfg CFG SRC TGT.
Proof.
ltac2:(KReplay.run1 (kr_t_RowsBp ()) [] "p;2g0000j20Tg0012g002:'0o"). Qed.

Theorem base_bp_abort :
  strong_universal_error_free_T_scfg_budgets_abort CFG ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.M.phdrs)
    (mkImage OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.init_pc OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.M.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_RowsBp ()) [] "p;2g003Bj20Tg0012g002:'0o"). Qed.
