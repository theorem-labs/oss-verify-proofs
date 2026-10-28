From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Ltac x41_ck :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 140512) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 140740) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 151752) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 151760) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 151864) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152080) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152296) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152512) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152524) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152536) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152548) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152564) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152580) _ _ _ _) => kx_trap_fast
  | |- evt _ _ (MS _ _ (Z_to_bv 64 152596) _ _ _ _) => kx_trap_fast
  | _ => idtac
  end.
