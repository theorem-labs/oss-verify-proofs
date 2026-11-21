(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; the model's channel reader as a premise of the writes; recorded proofs re-encoded or written as text where the change reaches them; the walk over the image's own segments lifted to the run's segment list (run_segments, with the vDSO pair)). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ScfgBase ShapeAlg SRealizes SRzAbort HaltsKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Rows Require Export HaltsBpDrvS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import LibContractDefs S1Spec S1MainInst U1MainInst BaseUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem halts_bp_ubsan_drv :
  lib_contract_U1 ->
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source CODES02
    (mkImage Ubsan.M.loaded_segments
             Ubsan.M.init_pc
             Ubsan.M.phdrs).
Proof.
  (* LPS 727298f3: text in place of the recorded proof, as the plain build's twin
     [halts_bp_plain_drv]; the start-up takes the launch facts and the reader clause. *)
  intros LIB2.
  apply (srealizes_halts_scfg_budgets forced_only_cfg); [apply cfg_le_forced_only_CFG|].
  intros sp brk mbase rnd inp Hen Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & Hbrk & _ & Hfit & Hlau).
  assert (Hvl : valid_launch inp) by (clear - Hvalid; red in Hvalid; tauto).
  assert (Hrd : in_channel_reader inp = true) by (clear - Hvalid; red in Hvalid; tauto).
  destruct Hvalid as (Hva & Hve & _).
  exists (spec (in_argv inp) (in_fs inp)). split; [| split].
  - exact (u1_main_run_lim ShippedBudgets.lim_source ltac:(apply Z.leb_le; vm_compute; reflexivity)
             sp brk mbase rnd inp LIB2 Hsp Hbrk Hva Hve Hfit Hvl Hlau Hrd).
  - apply spec_nokill.
  - apply spec_exits_02.
Qed.
