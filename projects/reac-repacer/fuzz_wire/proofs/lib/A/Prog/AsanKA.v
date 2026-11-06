(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_decode/lib/A/Prog/AsanKA.v (origin/ossv/recipes 88154566652a) for reac-repacer/fuzz_uci's image A, with its module paths changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0.
Open Scope Z_scope.

Definition off_stk (sp : word) (K a n : Z) : Prop := a + n <= bv_unsigned sp - K \/ bv_unsigned sp <= a.
