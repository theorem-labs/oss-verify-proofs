(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1735c : bv 32 := 0x00050593.
Lemma F_1735c : fetch_word Ubsan.M.loaded_segments (0x1735c : word) = Some W_1735c.
Proof. vm_refl. Qed.
Lemma D_1735c : decode_any W_1735c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17360 : bv 32 := 0x05e00893.
Lemma F_17360 : fetch_word Ubsan.M.loaded_segments (0x17360 : word) = Some W_17360.
Proof. vm_refl. Qed.
Lemma D_17360 : decode_any W_17360 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_17364 : bv 32 := 0x00000073.
Lemma F_17364 : fetch_word Ubsan.M.loaded_segments (0x17364 : word) = Some W_17364.
Proof. vm_refl. Qed.
Lemma D_17364 : decode_any W_17364 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_17364 : is_ecall W_17364 = true.
Proof. reflexivity. Qed.

Definition W_1750c : bv 32 := 0x00008067.
Lemma F_1750c : fetch_word Ubsan.M.loaded_segments (0x1750c : word) = Some W_1750c.
Proof. vm_refl. Qed.
Lemma D_1750c : decode_any W_1750c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17510 : bv 32 := 0xfe010113.
Lemma F_17510 : fetch_word Ubsan.M.loaded_segments (0x17510 : word) = Some W_17510.
Proof. vm_refl. Qed.
Lemma D_17510 : decode_any W_17510 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_17514 : bv 32 := 0x00113c23.
Lemma F_17514 : fetch_word Ubsan.M.loaded_segments (0x17514 : word) = Some W_17514.
Proof. vm_refl. Qed.
Lemma D_17514 : decode_any W_17514 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17518 : bv 32 := 0x00813823.
Lemma F_17518 : fetch_word Ubsan.M.loaded_segments (0x17518 : word) = Some W_17518.
Proof. vm_refl. Qed.
Lemma D_17518 : decode_any W_17518 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1751c : bv 32 := 0x00913423.
Lemma F_1751c : fetch_word Ubsan.M.loaded_segments (0x1751c : word) = Some W_1751c.
Proof. vm_refl. Qed.
Lemma D_1751c : decode_any W_1751c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17520 : bv 32 := 0x00009517.
Lemma F_17520 : fetch_word Ubsan.M.loaded_segments (0x17520 : word) = Some W_17520.
Proof. vm_refl. Qed.
Lemma D_17520 : decode_any W_17520 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17524 : bv 32 := 0x00009597.
Lemma F_17524 : fetch_word Ubsan.M.loaded_segments (0x17524 : word) = Some W_17524.
Proof. vm_refl. Qed.
Lemma D_17524 : decode_any W_17524 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_17528 : bv 32 := 0xc4053503.
Lemma F_17528 : fetch_word Ubsan.M.loaded_segments (0x17528 : word) = Some W_17528.
Proof. vm_refl. Qed.
Lemma D_17528 : decode_any W_17528 = Some (Load SZ8 true 10 10 3136, 4%Z).
Proof. vm_refl. Qed.

Definition W_1752c : bv 32 := 0xc445b403.
Lemma F_1752c : fetch_word Ubsan.M.loaded_segments (0x1752c : word) = Some W_1752c.
Proof. vm_refl. Qed.
Lemma D_1752c : decode_any W_1752c = Some (Load SZ8 true 8 11 3140, 4%Z).
Proof. vm_refl. Qed.

Definition W_17530 : bv 32 := 0x00a47c63.
Lemma F_17530 : fetch_word Ubsan.M.loaded_segments (0x17530 : word) = Some W_17530.
Proof. vm_refl. Qed.
Lemma D_17530 : decode_any W_17530 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17534 : bv 32 := 0xff853583.
Lemma F_17534 : fetch_word Ubsan.M.loaded_segments (0x17534 : word) = Some W_17534.
Proof. vm_refl. Qed.
Lemma D_17534 : decode_any W_17534 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_17538 : bv 32 := 0xff850493.
Lemma F_17538 : fetch_word Ubsan.M.loaded_segments (0x17538 : word) = Some W_17538.
Proof. vm_refl. Qed.
Lemma D_17538 : decode_any W_17538 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1753c : bv 32 := 0x000580e7.
Lemma F_1753c : fetch_word Ubsan.M.loaded_segments (0x1753c : word) = Some W_1753c.
Proof. vm_refl. Qed.
Lemma D_1753c : decode_any W_1753c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17540 : bv 32 := 0x00048513.
Lemma F_17540 : fetch_word Ubsan.M.loaded_segments (0x17540 : word) = Some W_17540.
Proof. vm_refl. Qed.
Lemma D_17540 : decode_any W_17540 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17544 : bv 32 := 0xfe9468e3.
Lemma F_17544 : fetch_word Ubsan.M.loaded_segments (0x17544 : word) = Some W_17544.
Proof. vm_refl. Qed.
Lemma D_17544 : decode_any W_17544 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_17548 : bv 32 := 0x01813083.
Lemma F_17548 : fetch_word Ubsan.M.loaded_segments (0x17548 : word) = Some W_17548.
Proof. vm_refl. Qed.
Lemma D_17548 : decode_any W_17548 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1754c : bv 32 := 0x01013403.
Lemma F_1754c : fetch_word Ubsan.M.loaded_segments (0x1754c : word) = Some W_1754c.
Proof. vm_refl. Qed.
Lemma D_1754c : decode_any W_1754c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17550 : bv 32 := 0x00813483.
Lemma F_17550 : fetch_word Ubsan.M.loaded_segments (0x17550 : word) = Some W_17550.
Proof. vm_refl. Qed.
Lemma D_17550 : decode_any W_17550 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17554 : bv 32 := 0x02010113.
Lemma F_17554 : fetch_word Ubsan.M.loaded_segments (0x17554 : word) = Some W_17554.
Proof. vm_refl. Qed.
Lemma D_17554 : decode_any W_17554 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17558 : bv 32 := 0xfb5ff06f.
Lemma F_17558 : fetch_word Ubsan.M.loaded_segments (0x17558 : word) = Some W_17558.
Proof. vm_refl. Qed.
Lemma D_17558 : decode_any W_17558 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1755c : bv 32 := 0xff010113.
Lemma F_1755c : fetch_word Ubsan.M.loaded_segments (0x1755c : word) = Some W_1755c.
Proof. vm_refl. Qed.
Lemma D_1755c : decode_any W_1755c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17560 : bv 32 := 0x00113423.
Lemma F_17560 : fetch_word Ubsan.M.loaded_segments (0x17560 : word) = Some W_17560.
Proof. vm_refl. Qed.
Lemma D_17560 : decode_any W_17560 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17564 : bv 32 := 0x00813023.
Lemma F_17564 : fetch_word Ubsan.M.loaded_segments (0x17564 : word) = Some W_17564.
Proof. vm_refl. Qed.
Lemma D_17564 : decode_any W_17564 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17568 : bv 32 := 0x00000593.
Lemma F_17568 : fetch_word Ubsan.M.loaded_segments (0x17568 : word) = Some W_17568.
Proof. vm_refl. Qed.
Lemma D_17568 : decode_any W_17568 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1756c : bv 32 := 0x00020613.
Lemma F_1756c : fetch_word Ubsan.M.loaded_segments (0x1756c : word) = Some W_1756c.
Proof. vm_refl. Qed.
Lemma D_1756c : decode_any W_1756c = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17570 : bv 32 := 0xf5862603.
Lemma F_17570 : fetch_word Ubsan.M.loaded_segments (0x17570 : word) = Some W_17570.
Proof. vm_refl. Qed.
Lemma D_17570 : decode_any W_17570 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_17574 : bv 32 := 0x0003a697.
Lemma F_17574 : fetch_word Ubsan.M.loaded_segments (0x17574 : word) = Some W_17574.
Proof. vm_refl. Qed.
Lemma D_17574 : decode_any W_17574 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17578 : bv 32 := 0x1cc68693.
Lemma F_17578 : fetch_word Ubsan.M.loaded_segments (0x17578 : word) = Some W_17578.
Proof. vm_refl. Qed.
Lemma D_17578 : decode_any W_17578 = Some (OpImm ALU_ADD 13 13 460, 4%Z).
Proof. vm_refl. Qed.

Definition W_1757c : bv 32 := 0x1606a72f.
Lemma F_1757c : fetch_word Ubsan.M.loaded_segments (0x1757c : word) = Some W_1757c.
Proof. vm_refl. Qed.
Lemma D_1757c : decode_any W_1757c = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17580 : bv 32 := 0x00b71663.
Lemma F_17580 : fetch_word Ubsan.M.loaded_segments (0x17580 : word) = Some W_17580.
Proof. vm_refl. Qed.
Lemma D_17580 : decode_any W_17580 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17584 : bv 32 := 0x1ec6a7af.
Lemma F_17584 : fetch_word Ubsan.M.loaded_segments (0x17584 : word) = Some W_17584.
Proof. vm_refl. Qed.
Lemma D_17584 : decode_any W_17584 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17588 : bv 32 := 0xfe079ae3.
Lemma F_17588 : fetch_word Ubsan.M.loaded_segments (0x17588 : word) = Some W_17588.
Proof. vm_refl. Qed.
Lemma D_17588 : decode_any W_17588 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1758c : bv 32 := 0x0007059b.
Lemma F_1758c : fetch_word Ubsan.M.loaded_segments (0x1758c : word) = Some W_1758c.
Proof. vm_refl. Qed.
Lemma D_1758c : decode_any W_1758c = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17590 : bv 32 := 0x02c58263.
Lemma F_17590 : fetch_word Ubsan.M.loaded_segments (0x17590 : word) = Some W_17590.
Proof. vm_refl. Qed.
Lemma D_17590 : decode_any W_17590 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_17594 : bv 32 := 0x02058263.
Lemma F_17594 : fetch_word Ubsan.M.loaded_segments (0x17594 : word) = Some W_17594.
Proof. vm_refl. Qed.
Lemma D_17594 : decode_any W_17594 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_175b8 : bv 32 := 0x00050413.
Lemma F_175b8 : fetch_word Ubsan.M.loaded_segments (0x175b8 : word) = Some W_175b8.
Proof. vm_refl. Qed.
Lemma D_175b8 : decode_any W_175b8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175bc : bv 32 := 0xdbdff0ef.
Lemma F_175bc : fetch_word Ubsan.M.loaded_segments (0x175bc : word) = Some W_175bc.
Proof. vm_refl. Qed.
Lemma D_175bc : decode_any W_175bc = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_175c0 : bv 32 := 0xf51ff0ef.
Lemma F_175c0 : fetch_word Ubsan.M.loaded_segments (0x175c0 : word) = Some W_175c0.
Proof. vm_refl. Qed.
Lemma D_175c0 : decode_any W_175c0 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_175c4 : bv 32 := 0x310020ef.
Lemma F_175c4 : fetch_word Ubsan.M.loaded_segments (0x175c4 : word) = Some W_175c4.
Proof. vm_refl. Qed.
Lemma D_175c4 : decode_any W_175c4 = Some (Jal 1 8976, 4%Z).
Proof. vm_refl. Qed.

Definition W_175c8 : bv 32 := 0x00040513.
Lemma F_175c8 : fetch_word Ubsan.M.loaded_segments (0x175c8 : word) = Some W_175c8.
Proof. vm_refl. Qed.
Lemma D_175c8 : decode_any W_175c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_175cc : bv 32 := 0xd91ff0ef.
Lemma F_175cc : fetch_word Ubsan.M.loaded_segments (0x175cc : word) = Some W_175cc.
Proof. vm_refl. Qed.
Lemma D_175cc : decode_any W_175cc = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b4 : bv 32 := 0xff010113.
Lemma F_176b4 : fetch_word Ubsan.M.loaded_segments (0x176b4 : word) = Some W_176b4.
Proof. vm_refl. Qed.
Lemma D_176b4 : decode_any W_176b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_176b8 : bv 32 := 0x00113423.
Lemma F_176b8 : fetch_word Ubsan.M.loaded_segments (0x176b8 : word) = Some W_176b8.
Proof. vm_refl. Qed.
Lemma D_176b8 : decode_any W_176b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_176bc : bv 32 := 0x00050e63.
Lemma F_176bc : fetch_word Ubsan.M.loaded_segments (0x176bc : word) = Some W_176bc.
Proof. vm_refl. Qed.
Lemma D_176bc : decode_any W_176bc = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c0 : bv 32 := 0x00050593.
Lemma F_176c0 : fetch_word Ubsan.M.loaded_segments (0x176c0 : word) = Some W_176c0.
Proof. vm_refl. Qed.
Lemma D_176c0 : decode_any W_176c0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c4 : bv 32 := 0x00009517.
Lemma F_176c4 : fetch_word Ubsan.M.loaded_segments (0x176c4 : word) = Some W_176c4.
Proof. vm_refl. Qed.
Lemma D_176c4 : decode_any W_176c4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_176c8 : bv 32 := 0xa9453503.
Lemma F_176c8 : fetch_word Ubsan.M.loaded_segments (0x176c8 : word) = Some W_176c8.
Proof. vm_refl. Qed.
Lemma D_176c8 : decode_any W_176c8 = Some (Load SZ8 true 10 10 2708, 4%Z).
Proof. vm_refl. Qed.

Definition W_176cc : bv 32 := 0x00800613.
Lemma F_176cc : fetch_word Ubsan.M.loaded_segments (0x176cc : word) = Some W_176cc.
Proof. vm_refl. Qed.
Lemma D_176cc : decode_any W_176cc = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d0 : bv 32 := 0x00c070ef.
Lemma F_176d0 : fetch_word Ubsan.M.loaded_segments (0x176d0 : word) = Some W_176d0.
Proof. vm_refl. Qed.
Lemma D_176d0 : decode_any W_176d0 = Some (Jal 1 28684, 4%Z).
Proof. vm_refl. Qed.

Definition W_176d4 : bv 32 := 0x01c0006f.
Lemma F_176d4 : fetch_word Ubsan.M.loaded_segments (0x176d4 : word) = Some W_176d4.
Proof. vm_refl. Qed.
Lemma D_176d4 : decode_any W_176d4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f0 : bv 32 := 0x00009517.
Lemma F_176f0 : fetch_word Ubsan.M.loaded_segments (0x176f0 : word) = Some W_176f0.
Proof. vm_refl. Qed.
Lemma D_176f0 : decode_any W_176f0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f4 : bv 32 := 0xa6853503.
Lemma F_176f4 : fetch_word Ubsan.M.loaded_segments (0x176f4 : word) = Some W_176f4.
Proof. vm_refl. Qed.
Lemma D_176f4 : decode_any W_176f4 = Some (Load SZ8 true 10 10 2664, 4%Z).
Proof. vm_refl. Qed.

Definition W_176f8 : bv 32 := 0x000500a3.
Lemma F_176f8 : fetch_word Ubsan.M.loaded_segments (0x176f8 : word) = Some W_176f8.
Proof. vm_refl. Qed.
Lemma D_176f8 : decode_any W_176f8 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_176fc : bv 32 := 0x00053503.
Lemma F_176fc : fetch_word Ubsan.M.loaded_segments (0x176fc : word) = Some W_176fc.
Proof. vm_refl. Qed.
Lemma D_176fc : decode_any W_176fc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17700 : bv 32 := 0x00020593.
Lemma F_17700 : fetch_word Ubsan.M.loaded_segments (0x17700 : word) = Some W_17700.
Proof. vm_refl. Qed.
Lemma D_17700 : decode_any W_17700 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17704 : bv 32 := 0xfea5b823.
Lemma F_17704 : fetch_word Ubsan.M.loaded_segments (0x17704 : word) = Some W_17704.
Proof. vm_refl. Qed.
Lemma D_17704 : decode_any W_17704 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17708 : bv 32 := 0x00813083.
Lemma F_17708 : fetch_word Ubsan.M.loaded_segments (0x17708 : word) = Some W_17708.
Proof. vm_refl. Qed.
Lemma D_17708 : decode_any W_17708 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1770c : bv 32 := 0x01010113.
Lemma F_1770c : fetch_word Ubsan.M.loaded_segments (0x1770c : word) = Some W_1770c.
Proof. vm_refl. Qed.
Lemma D_1770c : decode_any W_1770c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17710 : bv 32 := 0x00008067.
Lemma F_17710 : fetch_word Ubsan.M.loaded_segments (0x17710 : word) = Some W_17710.
Proof. vm_refl. Qed.
Lemma D_17710 : decode_any W_17710 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1771c : bv 32 := 0xfffff5b7.
Lemma F_1771c : fetch_word Ubsan.M.loaded_segments (0x1771c : word) = Some W_1771c.
Proof. vm_refl. Qed.
Lemma D_1771c : decode_any W_1771c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_17720 : bv 32 := 0x0015859b.
Lemma F_17720 : fetch_word Ubsan.M.loaded_segments (0x17720 : word) = Some W_17720.
Proof. vm_refl. Qed.
Lemma D_17720 : decode_any W_17720 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17724 : bv 32 := 0x02b56663.
Lemma F_17724 : fetch_word Ubsan.M.loaded_segments (0x17724 : word) = Some W_17724.
Proof. vm_refl. Qed.
Lemma D_17724 : decode_any W_17724 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_17728 : bv 32 := 0xff010113.
Lemma F_17728 : fetch_word Ubsan.M.loaded_segments (0x17728 : word) = Some W_17728.
Proof. vm_refl. Qed.
Lemma D_17728 : decode_any W_17728 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_1772c : bv 32 := 0x00113423.
Lemma F_1772c : fetch_word Ubsan.M.loaded_segments (0x1772c : word) = Some W_1772c.
Proof. vm_refl. Qed.
Lemma D_1772c : decode_any W_1772c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17730 : bv 32 := 0x00813023.
Lemma F_17730 : fetch_word Ubsan.M.loaded_segments (0x17730 : word) = Some W_17730.
Proof. vm_refl. Qed.
Lemma D_17730 : decode_any W_17730 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17734 : bv 32 := 0x40a0043b.
Lemma F_17734 : fetch_word Ubsan.M.loaded_segments (0x17734 : word) = Some W_17734.
Proof. vm_refl. Qed.
Lemma D_17734 : decode_any W_17734 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_17738 : bv 32 := 0x01c000ef.
Lemma F_17738 : fetch_word Ubsan.M.loaded_segments (0x17738 : word) = Some W_17738.
Proof. vm_refl. Qed.
Lemma D_17738 : decode_any W_17738 = Some (Jal 1 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1773c : bv 32 := 0x00852023.
Lemma F_1773c : fetch_word Ubsan.M.loaded_segments (0x1773c : word) = Some W_1773c.
Proof. vm_refl. Qed.
Lemma D_1773c : decode_any W_1773c = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17740 : bv 32 := 0xfff00513.
Lemma F_17740 : fetch_word Ubsan.M.loaded_segments (0x17740 : word) = Some W_17740.
Proof. vm_refl. Qed.
Lemma D_17740 : decode_any W_17740 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17744 : bv 32 := 0x00813083.
Lemma F_17744 : fetch_word Ubsan.M.loaded_segments (0x17744 : word) = Some W_17744.
Proof. vm_refl. Qed.
Lemma D_17744 : decode_any W_17744 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17748 : bv 32 := 0x00013403.
Lemma F_17748 : fetch_word Ubsan.M.loaded_segments (0x17748 : word) = Some W_17748.
Proof. vm_refl. Qed.
Lemma D_17748 : decode_any W_17748 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1774c : bv 32 := 0x01010113.
Lemma F_1774c : fetch_word Ubsan.M.loaded_segments (0x1774c : word) = Some W_1774c.
Proof. vm_refl. Qed.
Lemma D_1774c : decode_any W_1774c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17750 : bv 32 := 0x00008067.
Lemma F_17750 : fetch_word Ubsan.M.loaded_segments (0x17750 : word) = Some W_17750.
Proof. vm_refl. Qed.
Lemma D_17750 : decode_any W_17750 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17754 : bv 32 := 0x00020513.
Lemma F_17754 : fetch_word Ubsan.M.loaded_segments (0x17754 : word) = Some W_17754.
Proof. vm_refl. Qed.
Lemma D_17754 : decode_any W_17754 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17758 : bv 32 := 0xf5c50513.
Lemma F_17758 : fetch_word Ubsan.M.loaded_segments (0x17758 : word) = Some W_17758.
Proof. vm_refl. Qed.
Lemma D_17758 : decode_any W_17758 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_1775c : bv 32 := 0x00008067.
Lemma F_1775c : fetch_word Ubsan.M.loaded_segments (0x1775c : word) = Some W_1775c.
Proof. vm_refl. Qed.
Lemma D_1775c : decode_any W_1775c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178a4 : bv 32 := 0x1c050463.
Lemma F_178a4 : fetch_word Ubsan.M.loaded_segments (0x178a4 : word) = Some W_178a4.
Proof. vm_refl. Qed.
Lemma D_178a4 : decode_any W_178a4 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_178a8 : bv 32 := 0xfd010113.
Lemma F_178a8 : fetch_word Ubsan.M.loaded_segments (0x178a8 : word) = Some W_178a8.
Proof. vm_refl. Qed.
Lemma D_178a8 : decode_any W_178a8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_178ac : bv 32 := 0x02113423.
Lemma F_178ac : fetch_word Ubsan.M.loaded_segments (0x178ac : word) = Some W_178ac.
Proof. vm_refl. Qed.
Lemma D_178ac : decode_any W_178ac = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_178b0 : bv 32 := 0x02813023.
Lemma F_178b0 : fetch_word Ubsan.M.loaded_segments (0x178b0 : word) = Some W_178b0.
Proof. vm_refl. Qed.
Lemma D_178b0 : decode_any W_178b0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_178b4 : bv 32 := 0x00913c23.
Lemma F_178b4 : fetch_word Ubsan.M.loaded_segments (0x178b4 : word) = Some W_178b4.
Proof. vm_refl. Qed.
Lemma D_178b4 : decode_any W_178b4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_178b8 : bv 32 := 0x01213823.
Lemma F_178b8 : fetch_word Ubsan.M.loaded_segments (0x178b8 : word) = Some W_178b8.
Proof. vm_refl. Qed.
Lemma D_178b8 : decode_any W_178b8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_178bc : bv 32 := 0x01313423.
Lemma F_178bc : fetch_word Ubsan.M.loaded_segments (0x178bc : word) = Some W_178bc.
Proof. vm_refl. Qed.
Lemma D_178bc : decode_any W_178bc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_178c0 : bv 32 := 0x00050493.
Lemma F_178c0 : fetch_word Ubsan.M.loaded_segments (0x178c0 : word) = Some W_178c0.
Proof. vm_refl. Qed.
Lemma D_178c0 : decode_any W_178c0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_178c4 : bv 32 := 0x1ac000ef.
Lemma F_178c4 : fetch_word Ubsan.M.loaded_segments (0x178c4 : word) = Some W_178c4.
Proof. vm_refl. Qed.
Lemma D_178c4 : decode_any W_178c4 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_178c8 : bv 32 := 0x02053583.
Lemma F_178c8 : fetch_word Ubsan.M.loaded_segments (0x178c8 : word) = Some W_178c8.
Proof. vm_refl. Qed.
Lemma D_178c8 : decode_any W_178c8 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_178cc : bv 32 := 0xffd4c683.
Lemma F_178cc : fetch_word Ubsan.M.loaded_segments (0x178cc : word) = Some W_178cc.
Proof. vm_refl. Qed.
Lemma D_178cc : decode_any W_178cc = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_178d0 : bv 32 := 0x00c5d613.
Lemma F_178d0 : fetch_word Ubsan.M.loaded_segments (0x178d0 : word) = Some W_178d0.
Proof. vm_refl. Qed.
Lemma D_178d0 : decode_any W_178d0 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_178d4 : bv 32 := 0x01f6f413.
Lemma F_178d4 : fetch_word Ubsan.M.loaded_segments (0x178d4 : word) = Some W_178d4.
Proof. vm_refl. Qed.
Lemma D_178d4 : decode_any W_178d4 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_178d8 : bv 32 := 0x00060e63.
Lemma F_178d8 : fetch_word Ubsan.M.loaded_segments (0x178d8 : word) = Some W_178d8.
Proof. vm_refl. Qed.
Lemma D_178d8 : decode_any W_178d8 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_178dc : bv 32 := 0x01f5f613.
Lemma F_178dc : fetch_word Ubsan.M.loaded_segments (0x178dc : word) = Some W_178dc.
Proof. vm_refl. Qed.
Lemma D_178dc : decode_any W_178dc = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_178e0 : bv 32 := 0x00061a63.
Lemma F_178e0 : fetch_word Ubsan.M.loaded_segments (0x178e0 : word) = Some W_178e0.
Proof. vm_refl. Qed.
Lemma D_178e0 : decode_any W_178e0 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_178e4 : bv 32 := 0xfffff637.
Lemma F_178e4 : fetch_word Ubsan.M.loaded_segments (0x178e4 : word) = Some W_178e4.
Proof. vm_refl. Qed.
Lemma D_178e4 : decode_any W_178e4 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_178e8 : bv 32 := 0x00c5f633.
Lemma F_178e8 : fetch_word Ubsan.M.loaded_segments (0x178e8 : word) = Some W_178e8.
Proof. vm_refl. Qed.
Lemma D_178e8 : decode_any W_178e8 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_178ec : bv 32 := 0xff060613.
Lemma F_178ec : fetch_word Ubsan.M.loaded_segments (0x178ec : word) = Some W_178ec.
Proof. vm_refl. Qed.
Lemma D_178ec : decode_any W_178ec = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_178f0 : bv 32 := 0x0200006f.
Lemma F_178f0 : fetch_word Ubsan.M.loaded_segments (0x178f0 : word) = Some W_178f0.
Proof. vm_refl. Qed.
Lemma D_178f0 : decode_any W_178f0 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_178f4 : bv 32 := 0x0055d613.
Lemma F_178f4 : fetch_word Ubsan.M.loaded_segments (0x178f4 : word) = Some W_178f4.
Proof. vm_refl. Qed.
Lemma D_178f4 : decode_any W_178f4 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_178f8 : bv 32 := 0xffff9717.
Lemma F_178f8 : fetch_word Ubsan.M.loaded_segments (0x178f8 : word) = Some W_178f8.
Proof. vm_refl. Qed.
Lemma D_178f8 : decode_any W_178f8 = Some (Auipc 14 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_178fc : bv 32 := 0x07e67613.
Lemma F_178fc : fetch_word Ubsan.M.loaded_segments (0x178fc : word) = Some W_178fc.
Proof. vm_refl. Qed.
Lemma D_178fc : decode_any W_178fc = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_17900 : bv 32 := 0xc1470713.
Lemma F_17900 : fetch_word Ubsan.M.loaded_segments (0x17900 : word) = Some W_17900.
Proof. vm_refl. Qed.
Lemma D_17900 : decode_any W_17900 = Some (OpImm ALU_ADD 14 14 3092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17904 : bv 32 := 0x00c70633.
Lemma F_17904 : fetch_word Ubsan.M.loaded_segments (0x17904 : word) = Some W_17904.
Proof. vm_refl. Qed.
Lemma D_17904 : decode_any W_17904 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17908 : bv 32 := 0x00065603.
Lemma F_17908 : fetch_word Ubsan.M.loaded_segments (0x17908 : word) = Some W_17908.
Proof. vm_refl. Qed.
Lemma D_17908 : decode_any W_17908 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1790c : bv 32 := 0x00461613.
Lemma F_1790c : fetch_word Ubsan.M.loaded_segments (0x1790c : word) = Some W_1790c.
Proof. vm_refl. Qed.
Lemma D_1790c : decode_any W_1790c = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17910 : bv 32 := 0x01053703.
Lemma F_17910 : fetch_word Ubsan.M.loaded_segments (0x17910 : word) = Some W_17910.
Proof. vm_refl. Qed.
Lemma D_17910 : decode_any W_17910 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17914 : bv 32 := 0x028607b3.
Lemma F_17914 : fetch_word Ubsan.M.loaded_segments (0x17914 : word) = Some W_17914.
Proof. vm_refl. Qed.
Lemma D_17914 : decode_any W_17914 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17918 : bv 32 := 0x0a000813.
Lemma F_17918 : fetch_word Ubsan.M.loaded_segments (0x17918 : word) = Some W_17918.
Proof. vm_refl. Qed.
Lemma D_17918 : decode_any W_17918 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_1791c : bv 32 := 0x00c70633.
Lemma F_1791c : fetch_word Ubsan.M.loaded_segments (0x1791c : word) = Some W_1791c.
Proof. vm_refl. Qed.
Lemma D_1791c : decode_any W_1791c = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17920 : bv 32 := 0x00f607b3.
Lemma F_17920 : fetch_word Ubsan.M.loaded_segments (0x17920 : word) = Some W_17920.
Proof. vm_refl. Qed.
Lemma D_17920 : decode_any W_17920 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17924 : bv 32 := 0x00c78613.
Lemma F_17924 : fetch_word Ubsan.M.loaded_segments (0x17924 : word) = Some W_17924.
Proof. vm_refl. Qed.
Lemma D_17924 : decode_any W_17924 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17928 : bv 32 := 0x0056d713.
Lemma F_17928 : fetch_word Ubsan.M.loaded_segments (0x17928 : word) = Some W_17928.
Proof. vm_refl. Qed.
Lemma D_17928 : decode_any W_17928 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1792c : bv 32 := 0x0306e663.
Lemma F_1792c : fetch_word Ubsan.M.loaded_segments (0x1792c : word) = Some W_1792c.
Proof. vm_refl. Qed.
Lemma D_1792c : decode_any W_1792c = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_17930 : bv 32 := 0x00500693.
Lemma F_17930 : fetch_word Ubsan.M.loaded_segments (0x17930 : word) = Some W_17930.
Proof. vm_refl. Qed.
Lemma D_17930 : decode_any W_17930 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_17934 : bv 32 := 0x00d70463.
Lemma F_17934 : fetch_word Ubsan.M.loaded_segments (0x17934 : word) = Some W_17934.
Proof. vm_refl. Qed.
Lemma D_17934 : decode_any W_17934 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1793c : bv 32 := 0x0087e703.
Lemma F_1793c : fetch_word Ubsan.M.loaded_segments (0x1793c : word) = Some W_1793c.
Proof. vm_refl. Qed.
Lemma D_1793c : decode_any W_1793c = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17940 : bv 32 := 0x00400693.
Lemma F_17940 : fetch_word Ubsan.M.loaded_segments (0x17940 : word) = Some W_17940.
Proof. vm_refl. Qed.
Lemma D_17940 : decode_any W_17940 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17944 : bv 32 := 0x00e6e463.
Lemma F_17944 : fetch_word Ubsan.M.loaded_segments (0x17944 : word) = Some W_17944.
Proof. vm_refl. Qed.
Lemma D_17944 : decode_any W_17944 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1794c : bv 32 := 0x0077c683.
Lemma F_1794c : fetch_word Ubsan.M.loaded_segments (0x1794c : word) = Some W_1794c.
Proof. vm_refl. Qed.
Lemma D_1794c : decode_any W_1794c = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_17950 : bv 32 := 0x00068463.
Lemma F_17950 : fetch_word Ubsan.M.loaded_segments (0x17950 : word) = Some W_17950.
Proof. vm_refl. Qed.
Lemma D_17950 : decode_any W_17950 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17958 : bv 32 := 0x409606b3.
Lemma F_17958 : fetch_word Ubsan.M.loaded_segments (0x17958 : word) = Some W_17958.
Proof. vm_refl. Qed.
Lemma D_17958 : decode_any W_17958 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1795c : bv 32 := 0x00e6f463.
Lemma F_1795c : fetch_word Ubsan.M.loaded_segments (0x1795c : word) = Some W_1795c.
Proof. vm_refl. Qed.
Lemma D_1795c : decode_any W_1795c = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17964 : bv 32 := 0x40e606b3.
Lemma F_17964 : fetch_word Ubsan.M.loaded_segments (0x17964 : word) = Some W_17964.
Proof. vm_refl. Qed.
Lemma D_17964 : decode_any W_17964 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17968 : bv 32 := 0x0006c683.
Lemma F_17968 : fetch_word Ubsan.M.loaded_segments (0x17968 : word) = Some W_17968.
Proof. vm_refl. Qed.
Lemma D_17968 : decode_any W_17968 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1796c : bv 32 := 0x00068463.
Lemma F_1796c : fetch_word Ubsan.M.loaded_segments (0x1796c : word) = Some W_1796c.
Proof. vm_refl. Qed.
Lemma D_1796c : decode_any W_1796c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17974 : bv 32 := 0x00064603.
Lemma F_17974 : fetch_word Ubsan.M.loaded_segments (0x17974 : word) = Some W_17974.
Proof. vm_refl. Qed.
Lemma D_17974 : decode_any W_17974 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17978 : bv 32 := 0x00060463.
Lemma F_17978 : fetch_word Ubsan.M.loaded_segments (0x17978 : word) = Some W_17978.
Proof. vm_refl. Qed.
Lemma D_17978 : decode_any W_17978 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17a70 : bv 32 := 0x00f57593.
Lemma F_17a70 : fetch_word Ubsan.M.loaded_segments (0x17a70 : word) = Some W_17a70.
Proof. vm_refl. Qed.
Lemma D_17a70 : decode_any W_17a70 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_17a74 : bv 32 := 0x00058463.
Lemma F_17a74 : fetch_word Ubsan.M.loaded_segments (0x17a74 : word) = Some W_17a74.
Proof. vm_refl. Qed.
Lemma D_17a74 : decode_any W_17a74 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17a7c : bv 32 := 0xffc54603.
Lemma F_17a7c : fetch_word Ubsan.M.loaded_segments (0x17a7c : word) = Some W_17a7c.
Proof. vm_refl. Qed.
Lemma D_17a7c : decode_any W_17a7c = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_17a80 : bv 32 := 0xffd54683.
Lemma F_17a80 : fetch_word Ubsan.M.loaded_segments (0x17a80 : word) = Some W_17a80.
Proof. vm_refl. Qed.
Lemma D_17a80 : decode_any W_17a80 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_17a84 : bv 32 := 0xffe55583.
Lemma F_17a84 : fetch_word Ubsan.M.loaded_segments (0x17a84 : word) = Some W_17a84.
Proof. vm_refl. Qed.
Lemma D_17a84 : decode_any W_17a84 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_17a88 : bv 32 := 0x00060e63.
Lemma F_17a88 : fetch_word Ubsan.M.loaded_segments (0x17a88 : word) = Some W_17a88.
Proof. vm_refl. Qed.
Lemma D_17a88 : decode_any W_17a88 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_17aa4 : bv 32 := 0x00459613.
Lemma F_17aa4 : fetch_word Ubsan.M.loaded_segments (0x17aa4 : word) = Some W_17aa4.
Proof. vm_refl. Qed.
Lemma D_17aa4 : decode_any W_17aa4 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_17aa8 : bv 32 := 0x40c50633.
Lemma F_17aa8 : fetch_word Ubsan.M.loaded_segments (0x17aa8 : word) = Some W_17aa8.
Proof. vm_refl. Qed.
Lemma D_17aa8 : decode_any W_17aa8 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17aac : bv 32 := 0xff063503.
Lemma F_17aac : fetch_word Ubsan.M.loaded_segments (0x17aac : word) = Some W_17aac.
Proof. vm_refl. Qed.
Lemma D_17aac : decode_any W_17aac = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ab0 : bv 32 := 0x01053703.
Lemma F_17ab0 : fetch_word Ubsan.M.loaded_segments (0x17ab0 : word) = Some W_17ab0.
Proof. vm_refl. Qed.
Lemma D_17ab0 : decode_any W_17ab0 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ab4 : bv 32 := 0xff060613.
Lemma F_17ab4 : fetch_word Ubsan.M.loaded_segments (0x17ab4 : word) = Some W_17ab4.
Proof. vm_refl. Qed.
Lemma D_17ab4 : decode_any W_17ab4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ab8 : bv 32 := 0x01f6f693.
Lemma F_17ab8 : fetch_word Ubsan.M.loaded_segments (0x17ab8 : word) = Some W_17ab8.
Proof. vm_refl. Qed.
Lemma D_17ab8 : decode_any W_17ab8 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_17abc : bv 32 := 0x00c70463.
Lemma F_17abc : fetch_word Ubsan.M.loaded_segments (0x17abc : word) = Some W_17abc.
Proof. vm_refl. Qed.
Lemma D_17abc : decode_any W_17abc = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ac4 : bv 32 := 0x02053603.
Lemma F_17ac4 : fetch_word Ubsan.M.loaded_segments (0x17ac4 : word) = Some W_17ac4.
Proof. vm_refl. Qed.
Lemma D_17ac4 : decode_any W_17ac4 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ac8 : bv 32 := 0x01f67713.
Lemma F_17ac8 : fetch_word Ubsan.M.loaded_segments (0x17ac8 : word) = Some W_17ac8.
Proof. vm_refl. Qed.
Lemma D_17ac8 : decode_any W_17ac8 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_17acc : bv 32 := 0x00d77463.
Lemma F_17acc : fetch_word Ubsan.M.loaded_segments (0x17acc : word) = Some W_17acc.
Proof. vm_refl. Qed.
Lemma D_17acc : decode_any W_17acc = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ad4 : bv 32 := 0x01852783.
Lemma F_17ad4 : fetch_word Ubsan.M.loaded_segments (0x17ad4 : word) = Some W_17ad4.
Proof. vm_refl. Qed.
Lemma D_17ad4 : decode_any W_17ad4 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ad8 : bv 32 := 0x00100713.
Lemma F_17ad8 : fetch_word Ubsan.M.loaded_segments (0x17ad8 : word) = Some W_17ad8.
Proof. vm_refl. Qed.
Lemma D_17ad8 : decode_any W_17ad8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17adc : bv 32 := 0x00d7173b.
Lemma F_17adc : fetch_word Ubsan.M.loaded_segments (0x17adc : word) = Some W_17adc.
Proof. vm_refl. Qed.
Lemma D_17adc : decode_any W_17adc = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ae0 : bv 32 := 0x00e7f7b3.
Lemma F_17ae0 : fetch_word Ubsan.M.loaded_segments (0x17ae0 : word) = Some W_17ae0.
Proof. vm_refl. Qed.
Lemma D_17ae0 : decode_any W_17ae0 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17ae4 : bv 32 := 0x00078463.
Lemma F_17ae4 : fetch_word Ubsan.M.loaded_segments (0x17ae4 : word) = Some W_17ae4.
Proof. vm_refl. Qed.
Lemma D_17ae4 : decode_any W_17ae4 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17aec : bv 32 := 0x01c52783.
Lemma F_17aec : fetch_word Ubsan.M.loaded_segments (0x17aec : word) = Some W_17aec.
Proof. vm_refl. Qed.
Lemma D_17aec : decode_any W_17aec = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_17af0 : bv 32 := 0x00e7f733.
Lemma F_17af0 : fetch_word Ubsan.M.loaded_segments (0x17af0 : word) = Some W_17af0.
Proof. vm_refl. Qed.
Lemma D_17af0 : decode_any W_17af0 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17af4 : bv 32 := 0x00070463.
Lemma F_17af4 : fetch_word Ubsan.M.loaded_segments (0x17af4 : word) = Some W_17af4.
Proof. vm_refl. Qed.
Lemma D_17af4 : decode_any W_17af4 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17afc : bv 32 := 0xfffff737.
Lemma F_17afc : fetch_word Ubsan.M.loaded_segments (0x17afc : word) = Some W_17afc.
Proof. vm_refl. Qed.
Lemma D_17afc : decode_any W_17afc = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b00 : bv 32 := 0x0003a797.
Lemma F_17b00 : fetch_word Ubsan.M.loaded_segments (0x17b00 : word) = Some W_17b00.
Proof. vm_refl. Qed.
Lemma D_17b00 : decode_any W_17b00 = Some (Auipc 15 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b04 : bv 32 := 0x00e57733.
Lemma F_17b04 : fetch_word Ubsan.M.loaded_segments (0x17b04 : word) = Some W_17b04.
Proof. vm_refl. Qed.
Lemma D_17b04 : decode_any W_17b04 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b08 : bv 32 := 0x00073703.
Lemma F_17b08 : fetch_word Ubsan.M.loaded_segments (0x17b08 : word) = Some W_17b08.
Proof. vm_refl. Qed.
Lemma D_17b08 : decode_any W_17b08 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b0c : bv 32 := 0xce07b783.
Lemma F_17b0c : fetch_word Ubsan.M.loaded_segments (0x17b0c : word) = Some W_17b0c.
Proof. vm_refl. Qed.
Lemma D_17b0c : decode_any W_17b0c = Some (Load SZ8 true 15 15 3296, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b10 : bv 32 := 0x00f70463.
Lemma F_17b10 : fetch_word Ubsan.M.loaded_segments (0x17b10 : word) = Some W_17b10.
Proof. vm_refl. Qed.
Lemma D_17b10 : decode_any W_17b10 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b18 : bv 32 := 0x03461713.
Lemma F_17b18 : fetch_word Ubsan.M.loaded_segments (0x17b18 : word) = Some W_17b18.
Proof. vm_refl. Qed.
Lemma D_17b18 : decode_any W_17b18 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b1c : bv 32 := 0x03a75713.
Lemma F_17b1c : fetch_word Ubsan.M.loaded_segments (0x17b1c : word) = Some W_17b1c.
Proof. vm_refl. Qed.
Lemma D_17b1c : decode_any W_17b1c = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b20 : bv 32 := 0x02f00793.
Lemma F_17b20 : fetch_word Ubsan.M.loaded_segments (0x17b20 : word) = Some W_17b20.
Proof. vm_refl. Qed.
Lemma D_17b20 : decode_any W_17b20 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b24 : bv 32 := 0x02e7ea63.
Lemma F_17b24 : fetch_word Ubsan.M.loaded_segments (0x17b24 : word) = Some W_17b24.
Proof. vm_refl. Qed.
Lemma D_17b24 : decode_any W_17b24 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b28 : bv 32 := 0x00171713.
Lemma F_17b28 : fetch_word Ubsan.M.loaded_segments (0x17b28 : word) = Some W_17b28.
Proof. vm_refl. Qed.
Lemma D_17b28 : decode_any W_17b28 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b2c : bv 32 := 0xffff9797.
Lemma F_17b2c : fetch_word Ubsan.M.loaded_segments (0x17b2c : word) = Some W_17b2c.
Proof. vm_refl. Qed.
Lemma D_17b2c : decode_any W_17b2c = Some (Auipc 15 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b30 : bv 32 := 0x9e078793.
Lemma F_17b30 : fetch_word Ubsan.M.loaded_segments (0x17b30 : word) = Some W_17b30.
Proof. vm_refl. Qed.
Lemma D_17b30 : decode_any W_17b30 = Some (OpImm ALU_ADD 15 15 2528, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b34 : bv 32 := 0x00e78733.
Lemma F_17b34 : fetch_word Ubsan.M.loaded_segments (0x17b34 : word) = Some W_17b34.
Proof. vm_refl. Qed.
Lemma D_17b34 : decode_any W_17b34 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b38 : bv 32 := 0x00075703.
Lemma F_17b38 : fetch_word Ubsan.M.loaded_segments (0x17b38 : word) = Some W_17b38.
Proof. vm_refl. Qed.
Lemma D_17b38 : decode_any W_17b38 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b3c : bv 32 := 0x02d707b3.
Lemma F_17b3c : fetch_word Ubsan.M.loaded_segments (0x17b3c : word) = Some W_17b3c.
Proof. vm_refl. Qed.
Lemma D_17b3c : decode_any W_17b3c = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b40 : bv 32 := 0x00f5f463.
Lemma F_17b40 : fetch_word Ubsan.M.loaded_segments (0x17b40 : word) = Some W_17b40.
Proof. vm_refl. Qed.
Lemma D_17b40 : decode_any W_17b40 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b48 : bv 32 := 0x00168693.
Lemma F_17b48 : fetch_word Ubsan.M.loaded_segments (0x17b48 : word) = Some W_17b48.
Proof. vm_refl. Qed.
Lemma D_17b48 : decode_any W_17b48 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b4c : bv 32 := 0x02e686b3.
Lemma F_17b4c : fetch_word Ubsan.M.loaded_segments (0x17b4c : word) = Some W_17b4c.
Proof. vm_refl. Qed.
Lemma D_17b4c : decode_any W_17b4c = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b50 : bv 32 := 0x00d5f863.
Lemma F_17b50 : fetch_word Ubsan.M.loaded_segments (0x17b50 : word) = Some W_17b50.
Proof. vm_refl. Qed.
Lemma D_17b50 : decode_any W_17b50 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b54 : bv 32 := 0x0100006f.
Lemma F_17b54 : fetch_word Ubsan.M.loaded_segments (0x17b54 : word) = Some W_17b54.
Proof. vm_refl. Qed.
Lemma D_17b54 : decode_any W_17b54 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b58 : bv 32 := 0x03f00693.
Lemma F_17b58 : fetch_word Ubsan.M.loaded_segments (0x17b58 : word) = Some W_17b58.
Proof. vm_refl. Qed.
Lemma D_17b58 : decode_any W_17b58 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b5c : bv 32 := 0x00d70463.
Lemma F_17b5c : fetch_word Ubsan.M.loaded_segments (0x17b5c : word) = Some W_17b5c.
Proof. vm_refl. Qed.
Lemma D_17b5c : decode_any W_17b5c = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b64 : bv 32 := 0x00c65613.
Lemma F_17b64 : fetch_word Ubsan.M.loaded_segments (0x17b64 : word) = Some W_17b64.
Proof. vm_refl. Qed.
Lemma D_17b64 : decode_any W_17b64 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b68 : bv 32 := 0x00060a63.
Lemma F_17b68 : fetch_word Ubsan.M.loaded_segments (0x17b68 : word) = Some W_17b68.
Proof. vm_refl. Qed.
Lemma D_17b68 : decode_any W_17b68 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b6c : bv 32 := 0x00861613.
Lemma F_17b6c : fetch_word Ubsan.M.loaded_segments (0x17b6c : word) = Some W_17b6c.
Proof. vm_refl. Qed.
Lemma D_17b6c : decode_any W_17b6c = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b70 : bv 32 := 0xfff60613.
Lemma F_17b70 : fetch_word Ubsan.M.loaded_segments (0x17b70 : word) = Some W_17b70.
Proof. vm_refl. Qed.
Lemma D_17b70 : decode_any W_17b70 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b74 : bv 32 := 0x00b67463.
Lemma F_17b74 : fetch_word Ubsan.M.loaded_segments (0x17b74 : word) = Some W_17b74.
Proof. vm_refl. Qed.
Lemma D_17b74 : decode_any W_17b74 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_17b7c : bv 32 := 0x00008067.
Lemma F_17b7c : fetch_word Ubsan.M.loaded_segments (0x17b7c : word) = Some W_17b7c.
Proof. vm_refl. Qed.
Lemma D_17b7c : decode_any W_17b7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f00 : bv 32 := 0x00072503.
Lemma F_17f00 : fetch_word Ubsan.M.loaded_segments (0x17f00 : word) = Some W_17f00.
Proof. vm_refl. Qed.
Lemma D_17f00 : decode_any W_17f00 = Some (Load SZ4 true 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f04 : bv 32 := 0x00b56633.
Lemma F_17f04 : fetch_word Ubsan.M.loaded_segments (0x17f04 : word) = Some W_17f04.
Proof. vm_refl. Qed.
Lemma D_17f04 : decode_any W_17f04 = Some (Op ALU_OR 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f08 : bv 32 := 0x160726af.
Lemma F_17f08 : fetch_word Ubsan.M.loaded_segments (0x17f08 : word) = Some W_17f08.
Proof. vm_refl. Qed.
Lemma D_17f08 : decode_any W_17f08 = Some (Lr AW true true 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f0c : bv 32 := 0x00a69663.
Lemma F_17f0c : fetch_word Ubsan.M.loaded_segments (0x17f0c : word) = Some W_17f0c.
Proof. vm_refl. Qed.
Lemma D_17f0c : decode_any W_17f0c = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f10 : bv 32 := 0x1ec727af.
Lemma F_17f10 : fetch_word Ubsan.M.loaded_segments (0x17f10 : word) = Some W_17f10.
Proof. vm_refl. Qed.
Lemma D_17f10 : decode_any W_17f10 = Some (Sc AW true true 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f14 : bv 32 := 0xfe079ae3.
Lemma F_17f14 : fetch_word Ubsan.M.loaded_segments (0x17f14 : word) = Some W_17f14.
Proof. vm_refl. Qed.
Lemma D_17f14 : decode_any W_17f14 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f18 : bv 32 := 0x0006869b.
Lemma F_17f18 : fetch_word Ubsan.M.loaded_segments (0x17f18 : word) = Some W_17f18.
Proof. vm_refl. Qed.
Lemma D_17f18 : decode_any W_17f18 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_17f1c : bv 32 := 0xfea692e3.
Lemma F_17f1c : fetch_word Ubsan.M.loaded_segments (0x17f1c : word) = Some W_17f1c.
Proof. vm_refl. Qed.
Lemma D_17f1c : decode_any W_17f1c = Some (Branch BC_NE 13 10 8164, 4%Z).
Proof. vm_refl. Qed.
