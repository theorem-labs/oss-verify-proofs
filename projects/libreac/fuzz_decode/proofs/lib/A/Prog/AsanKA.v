From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0.
Open Scope Z_scope.

Definition off_stk (sp : word) (K a n : Z) : Prop := a + n <= bv_unsigned sp - K \/ bv_unsigned sp <= a.
