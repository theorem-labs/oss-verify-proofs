From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
Open Scope Z_scope.

Ltac ub_at U := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 U) _ _ _ _) => kx_trap_fast | _ => idtac end.
Ltac ub_at_slow U := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 U) _ _ _ _) => kx_trap | _ => idtac end.
