(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsIface BsDriverLaws RtB_Iface DvB_FuzzStmt BsDrvDefs BsMainPre.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RtOwn.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Section Instance.

  Variable P_main : word -> word -> word -> EntryDraw -> ProcInput -> config -> Prop.

  Variable P : fuzz_params.

  Definition as_instance_stmt : Prop :=
    forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config),
      P_main sp0 brk0 mbase rdraw inp c ->
      exists (HCEIL : HeapCeil) (H : asr) (s0 : as_St H) (regs : bvmap 5 word) (mem : word -> option byte) (B tid can : Z),
        asan_rt_hyps_bp H /\ asan_driver_laws H /\ rt_own H /\ RtB_Td.td_law H
        /\ (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H)
        /\ AMpre H P sp0 (in_argv inp) s0 (cfg_ms c) (cfg_model c) regs mem B tid can
        /\ m_fs (cfg_model c) = in_fs inp.
End Instance.
