(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec SRealizes FPSteps AllocCeil RunRandom LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import DrvLibContract DrvMallocT S1Statics S1Cells S1RKn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1TargetConsts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Definition target_phase_stmt {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb}
    (MI : MallocIface SEGS L) (AINV0 : AS MI -> LibIface.mem -> Model -> Prop) (TIGHT FRESH44 : AS MI -> Prop) : Prop :=
  drv_mallocT MI AINV0 TIGHT FRESH44 ->
  lib_call_stmt SEGS L MI S1ST S1TargetConsts.LLVM_ENTRY S1TargetConsts.EMPTY_OBJ LIB_STACK lib_caps LIB_BIGCAP
                S1TargetConsts.TD_LOCALE S1TargetConsts.GLOBAL_LOCALE ->
  forall (sp0 tid p1 : Z) (path content : list byte) (fs0 : Fs) (p cap : Z),
    0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0 ->
    alloc_ceiling = sp0 - 8388608 ->
    0 < tid < 2 ^ 22 ->
    Z.of_nat (length content) < 2 ^ 26 ->
    forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : LibIface.mem) (mo : Model),
      tpre MI sp0 tid p1 path TIGHT content fs0 p cap A R M mo -> frm_zero (@fp_csr fx) ->
      srealizes SEGS (mkCfg (mkst R (Z_to_bv 64 0x658b8) M (seg_rom SEGS)) mo) (t_target content fs0).
