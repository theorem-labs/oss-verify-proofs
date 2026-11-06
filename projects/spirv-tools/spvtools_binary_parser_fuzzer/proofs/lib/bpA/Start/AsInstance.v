(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsIface AsDriverLaws RtA_Iface DvA_FuzzStmt AsDrvDefs AsMainPre.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_RtOwn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtA_Td.
Import HPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Section Instance.

  Variable P_main : word -> word -> word -> EntryDraw -> ProcInput -> config -> Prop.

  Variable P : fuzz_params.

  Definition as_instance_stmt : Prop :=
    forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config),
      P_main sp0 brk0 mbase rdraw inp c ->
      exists (HCEIL : HeapCeil) (H : asr) (s0 : as_St H) (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z),
        asan_rt_hyps_bp H /\ asan_driver_laws H /\ rt_own H /\ RtA_Td.td_law H
        /\ (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H)
        /\ AMpre H P sp0 (in_argv inp) s0 (cfg_ms c) (cfg_model c) regs mem B tid can
        /\ m_fs (cfg_model c) = in_fs inp.
End Instance.
