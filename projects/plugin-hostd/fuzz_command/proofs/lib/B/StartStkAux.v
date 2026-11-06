From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03 YA0j YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB12 YB1h YB01 StartStkAuxG.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
(* Every hand-off state of the start-up certificate (B/YB01.v) reads the 20 auxv words and the 16 AT_RANDOM bytes:
   the premise stk_aux_chk of StartStkAuxG.stk_aux_present, by vm_compute over HS_tfib_list. *)
Lemma tfib_holes_stkaux : forallb stk_aux_chk HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
