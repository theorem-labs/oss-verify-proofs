From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Ltac t2ck := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x2965c) _ _ _ _) => kx_trap_fast | _ => idtac end.
Ltac t2side := lazymatch goal with |- evt _ _ _ => idtac | |- _ => try solve [lia] end.
