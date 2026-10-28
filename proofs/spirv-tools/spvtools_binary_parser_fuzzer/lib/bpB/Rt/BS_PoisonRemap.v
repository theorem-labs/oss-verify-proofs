(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BAllocSim BMmapSim BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BsDepotInv BllocWalkKit B_memset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_Leaves BW_PoisonShadow BW_SysconfPg BW_PoisonRemap1 BecLazy BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition prm_model (mo : Model) (pb pe : Z) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in let h' := m_vmmaps mo' in
     nonvm_same mo mo'
  /\ vm_maps h' = vm_maps h
  /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h
  /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h
  /\ vm_noaccess h' = maps_subtract (vm_noaccess h) pb pe
  /\ eager_used mo' <= eager_used mo.

Definition prm_L (L : list (word * word)) (pb pe : Z) : list (word * word) := (wz pb, wz (pe - pb)) :: maps_subtract L pb pe.

End HCW.
