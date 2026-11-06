(* Modified by Theorem Labs: copied from this unit's lib/A/Prog/AsanKA.v (commit ba35beec1417; itself from proofs/libreac/fuzz_decode/lib/A/Prog/AsanKA.v at recipes commit 88154566652a) for reac-repacer/fuzz_uci's image B: Img0 is lib/B/Img0.v; nothing else changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0.
Open Scope Z_scope.

Definition off_stk (sp : word) (K a n : Z) : Prop := a + n <= bv_unsigned sp - K \/ bv_unsigned sp <= a.
