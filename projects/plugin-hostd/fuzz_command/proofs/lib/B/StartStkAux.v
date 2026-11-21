From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03 YA0j YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB12 YB1h StartStkAuxG.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YB01r.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
(* Every hand-off state of the start-up run at CONFIG_RSEQ flag r (B/YB01r.v, computed in the build) covers the
   auxv vector and the 16 AT_RANDOM bytes of the flag-r layout: the premise stk_aux_chk of StartStkAuxG's presence
   lemmas, by vm_compute over each flag's states. *)
Lemma tfib_holes_stkaux :
(forallb (stk_aux_chk 0) (YB01r.HS_tfib_list_r 0) && forallb (stk_aux_chk 1) (YB01r.HS_tfib_list_r 1))%bool = true.
Proof. vm_compute. reflexivity. Qed.
