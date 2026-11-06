(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec3 SymExec3Sound SymRun3 SymDrive3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA U1ExitKn U1ExitDefs S1KnCut3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope. Import SX2. Import SXA.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition SW_ENTRY : Z := 0xd70d4.
Definition SW_RET : Z := 0xd6d64.

Definition kn_tp_extra (w : Z) : list kentry :=
  [ KImg 0xeff08 0xf00e8;
    KWord (SA (ELit 0) 0xf00e8) 4 (ELit 5); KWord (SA (ELit 0) 0xf00f0) 8 (ELit 0); KWord (SA (ELit 0) 0xf00f8) 8 (ELit 0);
    KWord (SA (ELit 0) 0xf0108) 8 (ELit 0x123408); KWord (SA (ELit 0) 0xf0110) 8 (ELit w);
    KWord (SA (ELit 0) 0xf0120) 8 (ELit 0x123008); KWord (SA (ELit 0) 0xf0130) 8 (ELit 0xd70d4);
    KWord (SA (ELit 0) 0xf0170) 4 (ELit 0xffffffff); KWord (SA (ELit 0) 0xf0178) 4 (ELit 0xffffffff);
    KWord (SA (ELit 0) 0x122688) 8 (EVar 35);
    KImg 0xf00ec 0xf00f0; KImg 0xf0100 0xf0108; KImg 0xf0118 0xf0120; KImg 0xf0128 0xf0130;
    KImg 0xf0138 0xf0170; KImg 0xf0174 0xf0178; KImg 0xf017c 0xf01d8 ].
Definition kn_exit_tp (w : Z) : list kentry := kn_exit_common0 ++ kn_cxx_exit_t ++ kn_tp_extra w.

Definition exit_clear_tp : list (Z * Z) := exit_clear_t0.

Definition run_tp1 (w : Z) := sym_execA SEGS 3000 true [SW_ENTRY] (SCR [] [] []) (SS EXIT sr_exit [] (kn_exit_tp w) 40) [].
Definition carry_tp1 (w : Z) := carry (s_log (fst (fst (run_tp1 w)))) (kn_exit_tp w) [].

Definition ABS_TP : list (Z * Z) := [(0xf0108, 0xf0118); (0xf0120, 0xf0128)]%Z.
Definition KEPT_SW : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.
Definition kn_tp2_of (kn1 : list kentry) : list kentry :=
  kn_cut3 0 (-352) (-240) ABS_TP 0x124000 kn1
   ++ [KWord (SA (ELit 0) 0xf0108) 8 (ELit 0x123408); KWord (SA (ELit 0) 0xf0110) 8 (ELit 0x123008);
       KWord (SA (ELit 0) 0xf0120) 8 (ELit 0x123008)].
Definition sr_tp2_of (sr1 : list expr) : list expr := sr_after_call_j sr1 KEPT_SW 40.
Definition run_tp2 (sr2 : list expr) (kn2 : list kentry) := sym_execA SEGS 3000 true [] (SCR [] [] []) (SS SW_RET sr2 [] kn2 72) [].

Definition c1a := Eval vm_compute in run_tp1 0x12300a.
Definition c1b := Eval vm_compute in run_tp1 0x12300c.
Definition c1c := Eval vm_compute in run_tp1 0x12300e.
Definition k1a := Eval vm_compute in carry_tp1 0x12300a.
Definition k1b := Eval vm_compute in carry_tp1 0x12300c.
Definition k1c := Eval vm_compute in carry_tp1 0x12300e.
Definition sr2a := Eval vm_compute in sr_tp2_of (s_regs (fst (fst c1a))).
Definition sr2b := Eval vm_compute in sr_tp2_of (s_regs (fst (fst c1b))).
Definition sr2c := Eval vm_compute in sr_tp2_of (s_regs (fst (fst c1c))).
Definition kn2a := Eval vm_compute in kn_tp2_of (fst (fst k1a)).
Definition kn2b := Eval vm_compute in kn_tp2_of (fst (fst k1b)).
Definition kn2c := Eval vm_compute in kn_tp2_of (fst (fst k1c)).
Definition c2a := Eval vm_compute in run_tp2 sr2a kn2a.
Definition c2b := Eval vm_compute in run_tp2 sr2b kn2b.
Definition c2c := Eval vm_compute in run_tp2 sr2c kn2c.

Lemma c1a_pc : s_pc (fst (fst c1a)) = SW_ENTRY. Proof. reflexivity. Qed.
Lemma c1a_scs : snd (fst c1a) = []. Proof. reflexivity. Qed.
Lemma k1a_scs : snd (fst k1a) = []. Proof. reflexivity. Qed.
Lemma c2a_pc : s_pc (fst (fst c2a)) = EXIT_ECALL. Proof. reflexivity. Qed.
Lemma c2a_scs : snd (fst c2a) = []. Proof. reflexivity. Qed.
Lemma c2a_a7 : nth 17 (s_regs (fst (fst c2a))) (ELit 0) = ELit 94. Proof. reflexivity. Qed.
Lemma c2a_a0 : nth 10 (s_regs (fst (fst c2a))) (ELit 0) = EVar 2. Proof. reflexivity. Qed.
Lemma c1a_log : log_out3_b 0 0x123008 0x123408 (s_log (fst (fst c1a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma k1a_vars : kn_vars_lt 40 (fst (fst k1a)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1a_vars : sr_vars_lt 40 (s_regs (fst (fst c1a))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma kn2a_eq : kn2a = kn_tp2_of (fst (fst k1a)). Proof. vm_compute. reflexivity. Qed.
Lemma sr2a_eq : sr2a = sr_tp2_of (s_regs (fst (fst c1a))). Proof. vm_compute. reflexivity. Qed.
Lemma c1b_pc : s_pc (fst (fst c1b)) = SW_ENTRY. Proof. reflexivity. Qed.
Lemma c1b_scs : snd (fst c1b) = []. Proof. reflexivity. Qed.
Lemma k1b_scs : snd (fst k1b) = []. Proof. reflexivity. Qed.
Lemma c2b_pc : s_pc (fst (fst c2b)) = EXIT_ECALL. Proof. reflexivity. Qed.
Lemma c2b_scs : snd (fst c2b) = []. Proof. reflexivity. Qed.
Lemma c2b_a7 : nth 17 (s_regs (fst (fst c2b))) (ELit 0) = ELit 94. Proof. reflexivity. Qed.
Lemma c2b_a0 : nth 10 (s_regs (fst (fst c2b))) (ELit 0) = EVar 2. Proof. reflexivity. Qed.
Lemma c1b_log : log_out3_b 0 0x123008 0x123408 (s_log (fst (fst c1b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma k1b_vars : kn_vars_lt 40 (fst (fst k1b)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1b_vars : sr_vars_lt 40 (s_regs (fst (fst c1b))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma kn2b_eq : kn2b = kn_tp2_of (fst (fst k1b)). Proof. vm_compute. reflexivity. Qed.
Lemma sr2b_eq : sr2b = sr_tp2_of (s_regs (fst (fst c1b))). Proof. vm_compute. reflexivity. Qed.
Lemma c1c_pc : s_pc (fst (fst c1c)) = SW_ENTRY. Proof. reflexivity. Qed.
Lemma c1c_scs : snd (fst c1c) = []. Proof. reflexivity. Qed.
Lemma k1c_scs : snd (fst k1c) = []. Proof. reflexivity. Qed.
Lemma c2c_pc : s_pc (fst (fst c2c)) = EXIT_ECALL. Proof. reflexivity. Qed.
Lemma c2c_scs : snd (fst c2c) = []. Proof. reflexivity. Qed.
Lemma c2c_a7 : nth 17 (s_regs (fst (fst c2c))) (ELit 0) = ELit 94. Proof. reflexivity. Qed.
Lemma c2c_a0 : nth 10 (s_regs (fst (fst c2c))) (ELit 0) = EVar 2. Proof. reflexivity. Qed.
Lemma c1c_log : log_out3_b 0 0x123008 0x123408 (s_log (fst (fst c1c))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma k1c_vars : kn_vars_lt 40 (fst (fst k1c)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma c1c_vars : sr_vars_lt 40 (s_regs (fst (fst c1c))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma kn2c_eq : kn2c = kn_tp2_of (fst (fst k1c)). Proof. vm_compute. reflexivity. Qed.
Lemma sr2c_eq : sr2c = sr_tp2_of (s_regs (fst (fst c1c))). Proof. vm_compute. reflexivity. Qed.
