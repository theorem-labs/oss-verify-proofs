(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BakeStackRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RtB_SM0 RtB_SM2 RtB_SM3 RtB_SM6 RtB_SM8 RtB_SF6 RtB_SF8 RtB_SetShadow.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Ext.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Theorem rt_bp_ext_ok : asan_rt_hyps_bp_ext H.
Proof.
  unfold asan_rt_hyps_bp_ext.
  refine (conj _ (conj _ (conj _ (conj I (conj _ (conj _ (conj I (conj _ (conj _ (conj _ _)))))))))).
  - apply stack_malloc_0_ok; assumption.
  - apply stack_malloc_2_ok; assumption.
  - apply stack_malloc_3_ok; assumption.
  - apply stack_malloc_6_ok; assumption.
  - apply stack_malloc_8_ok; assumption.
  - apply stack_free_6_ok; assumption.
  - apply stack_free_8_ok; assumption.
  - apply set_shadow_00_ok.
  - apply set_shadow_f8_ok.
Qed.
End Ext.
