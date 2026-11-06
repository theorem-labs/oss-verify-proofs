(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 LibSym.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Rpl.
Ltac2 rplG () : ident list array := Array.of_list [[@Corelib; @Init; @Datatypes; @cons]; [@Corelib; @Init; @Datatypes; @prod]; [@Corelib; @Numbers; @BinNums; @Z]; [@Corelib; @Init; @Datatypes; @nat]; [@Corelib; @Init; @Datatypes; @pair]; [@Corelib; @Numbers; @BinNums; @Zpos]; [@Corelib; @Init; @Datatypes; @nil]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @PTNode]; [@LinuxProcessSemantics; @Riscv; @Instr; @instr]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @PTLeaf]; [@Corelib; @Init; @Datatypes; @None]; [@Corelib; @Init; @Datatypes; @Some]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_ADD]; [@stdpp; @bitvector; @definitions; @BV]; [@Corelib; @Numbers; @BinNums; @Npos]; [@stdpp; @bitvector; @definitions; @Z_to_bv_obligation_1]; [@Corelib; @Numbers; @BinNums; @Z0]; [@LinuxProcessSemantics; @Riscv; @Instr; @Auipc]; [@LinuxProcessSemantics; @Riscv; @Instr; @Load]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ8]; [@Corelib; @Init; @Datatypes; @true]; [@LinuxProcessSemantics; @Riscv; @Instr; @Store]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jal]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_OR]; [@LinuxProcessSemantics; @Riscv; @Instr; @Branch]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_EQ]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_NE]; [@LinuxProcessSemantics; @Riscv; @Instr; @OpImm32]; [@Corelib; @Numbers; @BinNums; @xH]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SRL]; [@LinuxProcessSemantics; @Riscv; @Instr; @Lui]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_AND]; [@LinuxProcessSemantics; @Riscv; @Instr; @ShiftImm]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ1]; [@Corelib; @Init; @Datatypes; @false]; [@LinuxProcessSemantics; @Riscv; @Instr; @Op32]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SUB]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_LT]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLL]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GE]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ4]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLTU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_SLT]; [@LinuxProcessSemantics; @Riscv; @Instr; @Jalr]; [@LinuxProcessSemantics; @Riscv; @Instr; @BC_GEU]; [@LinuxProcessSemantics; @Riscv; @Instr; @ALU_XOR]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul32]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MUL]; [@LinuxProcessSemantics; @Riscv; @Instr; @SZ2]; [@LinuxProcessSemantics; @Riscv; @Instr; @Mul]; [@LinuxProcessSemantics; @Riscv; @Instr; @M_MULHU]; [@Corelib; @Init; @Logic; @eq_refl]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @itab]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @seg; @Pm4SegItab_A_756a46; @IT]; [@Corelib; @Init; @Logic; @eq]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibSym; @itab_of]; [@OSSVerify; @jsoncons; @fuzz_json_encoder; @images; @Asan; @M; @loaded_segments]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @seg; @Pm4SegItab_A_756a46; @ITR]; [@Corelib; @Init; @Logic; @eq_ind_r]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @AxSymExec3; @AX2; @itab_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @LibSym; @itab_of_sound]; [@OSSVerify; @Proofs; @jsoncons; @fuzz_json_encoder; @lib; @seg; @Pm4SegItab_A_756a46; @IT_eq]].

Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(455988, 690%nat) ; (460892, 54%nat) ; (524860, 1%nat) ; (529468, 380%nat) ; (604684, 24%nat) ; (1350932, 21%nat) ; (1351016, 78%nat) ; (1352376, 108%nat) ; (1352808, 908%nat) ; (1356440, 16%nat) ; (1387168, 257%nat)].
Definition IT : itab := Eval vm_compute in itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S00vv!2,^:'^;'^<!3+^='^;'^<!2'^>'^?'^@").
Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. ltac2:(Rpl.RP.run_i (rplG ()) 0 "S01lg^;;g^Ad;!6'^A'^;!2'^>'^?'^@$i;R'^;!2'^B'^?#1!2'^C'^?'^@'^<'^D").
Qed.
