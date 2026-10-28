(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BazyRestrict BazySR BShapeAlg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BExec BMState.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ADRV_LIVE : Z := 2^27 + 2^26 + 7 * 2^26.
Definition ADRV_CNT  : Z := 3 + 512.

Record asan_driver_laws (H : asr) : Prop := ADL {

  adl_sr : forall (Q : config -> Prop) c T,
      as_SR H Q c -> (forall c', Q c' -> BShapeAlg.realizes asegs c' T) -> BShapeAlg.realizes asegs c T;

  adl_lazy : forall s, exists L S Zr,
         (forall msF, as_VIS H s msF = restrict L S msF)
      /\ (forall c, as_AKREL H s c -> lzok asegs L S Zr c)
      /\ (forall ms mo ms' mo', as_AKREL H s (mkCfg ms mo) -> lzok asegs L S Zr (mkCfg ms' mo') ->
            m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> as_AKREL H s (mkCfg ms' mo'));

  adl_mpres : forall mo mo', as_MPRES H mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_halted mo' = m_halted mo;

  adl_sb : forall mo mo', same_but_materialized mo mo' -> as_MPRES H mo mo';

  adl_live : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H }.

End HCW.

