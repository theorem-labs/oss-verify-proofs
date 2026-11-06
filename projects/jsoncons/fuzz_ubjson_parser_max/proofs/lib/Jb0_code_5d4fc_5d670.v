(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require CTabKB.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_5d4fc : bv 32 := 0xfe010113.
Lemma F_5d4fc : CTabKB.F 0x5d4fc W_5d4fc.
Proof. vm_refl. Qed.
Lemma D_5d4fc : CTabKB.D W_5d4fc (OpImm ALU_ADD 2 2 4064).
Proof. vm_refl. Qed.
Definition W_5d500 : bv 32 := 0x00113c23.
Lemma F_5d500 : CTabKB.F 0x5d500 W_5d500.
Proof. vm_refl. Qed.
Lemma D_5d500 : CTabKB.D W_5d500 (Store SZ8 2 1 24).
Proof. vm_refl. Qed.
Definition W_5d504 : bv 32 := 0x00813823.
Lemma F_5d504 : CTabKB.F 0x5d504 W_5d504.
Proof. vm_refl. Qed.
Lemma D_5d504 : CTabKB.D W_5d504 (Store SZ8 2 8 16).
Proof. vm_refl. Qed.
Definition W_5d508 : bv 32 := 0x00913423.
Lemma F_5d508 : CTabKB.F 0x5d508 W_5d508.
Proof. vm_refl. Qed.
Lemma D_5d508 : CTabKB.D W_5d508 (Store SZ8 2 9 8).
Proof. vm_refl. Qed.
Definition W_5d50c : bv 32 := 0x01213023.
Lemma F_5d50c : CTabKB.F 0x5d50c W_5d50c.
Proof. vm_refl. Qed.
Lemma D_5d50c : CTabKB.D W_5d50c (Store SZ8 2 18 0).
Proof. vm_refl. Qed.
Definition W_5d510 : bv 32 := 0x02010413.
Lemma F_5d510 : CTabKB.F 0x5d510 W_5d510.
Proof. vm_refl. Qed.
Lemma D_5d510 : CTabKB.D W_5d510 (OpImm ALU_ADD 8 2 32).
Proof. vm_refl. Qed.
Definition W_5d514 : bv 32 := 0x000d8517.
Lemma F_5d514 : CTabKB.F 0x5d514 W_5d514.
Proof. vm_refl. Qed.
Lemma D_5d514 : CTabKB.D W_5d514 (Auipc 10 216).
Proof. vm_refl. Qed.
Definition W_5d518 : bv 32 := 0xc8450513.
Lemma F_5d518 : CTabKB.F 0x5d518 W_5d518.
Proof. vm_refl. Qed.
Lemma D_5d518 : CTabKB.D W_5d518 (OpImm ALU_ADD 10 10 3204).
Proof. vm_refl. Qed.
Definition W_5d51c : bv 32 := 0x04d050ef.
Lemma F_5d51c : CTabKB.F 0x5d51c W_5d51c.
Proof. vm_refl. Qed.
Lemma D_5d51c : CTabKB.D W_5d51c (Jal 1 22604).
Proof. vm_refl. Qed.
Definition W_5d520 : bv 32 := 0x00053483.
Lemma F_5d520 : CTabKB.F 0x5d520 W_5d520.
Proof. vm_refl. Qed.
Lemma D_5d520 : CTabKB.D W_5d520 (Load SZ8 true 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d524 : bv 32 := 0x08048063.
Lemma F_5d524 : CTabKB.F 0x5d524 W_5d524.
Proof. vm_refl. Qed.
Lemma D_5d524 : CTabKB.D W_5d524 (Branch BC_EQ 9 0 128).
Proof. vm_refl. Qed.
Definition W_5d528 : bv 32 := 0x0604c503.
Lemma F_5d528 : CTabKB.F 0x5d528 W_5d528.
Proof. vm_refl. Qed.
Lemma D_5d528 : CTabKB.D W_5d528 (Load SZ1 false 10 9 96).
Proof. vm_refl. Qed.
Definition W_5d52c : bv 32 := 0x0584b903.
Lemma F_5d52c : CTabKB.F 0x5d52c W_5d52c.
Proof. vm_refl. Qed.
Lemma D_5d52c : CTabKB.D W_5d52c (Load SZ8 true 18 9 88).
Proof. vm_refl. Qed.
Definition W_5d530 : bv 32 := 0x00050863.
Lemma F_5d530 : CTabKB.F 0x5d530 W_5d530.
Proof. vm_refl. Qed.
Lemma D_5d530 : CTabKB.D W_5d530 (Branch BC_EQ 10 0 16).
Proof. vm_refl. Qed.
Definition W_5d534 : bv 32 := 0x00048513.
Lemma F_5d534 : CTabKB.F 0x5d534 W_5d534.
Proof. vm_refl. Qed.
Lemma D_5d534 : CTabKB.D W_5d534 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d538 : bv 32 := 0x00040593.
Lemma F_5d538 : CTabKB.F 0x5d538 W_5d538.
Proof. vm_refl. Qed.
Lemma D_5d538 : CTabKB.D W_5d538 (OpImm ALU_ADD 11 8 0).
Proof. vm_refl. Qed.
Definition W_5d53c : bv 32 := 0xb75ff0ef.
Lemma F_5d53c : CTabKB.F 0x5d53c W_5d53c.
Proof. vm_refl. Qed.
Lemma D_5d53c : CTabKB.D W_5d53c (Jal 1 2095988).
Proof. vm_refl. Qed.
Definition W_5d540 : bv 32 := 0xffa90593.
Lemma F_5d540 : CTabKB.F 0x5d540 W_5d540.
Proof. vm_refl. Qed.
Lemma D_5d540 : CTabKB.D W_5d540 (OpImm ALU_ADD 11 18 4090).
Proof. vm_refl. Qed.
Definition W_5d544 : bv 32 := 0x00100513.
Lemma F_5d544 : CTabKB.F 0x5d544 W_5d544.
Proof. vm_refl. Qed.
Lemma D_5d544 : CTabKB.D W_5d544 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d548 : bv 32 := 0x00b51533.
Lemma F_5d548 : CTabKB.F 0x5d548 W_5d548.
Proof. vm_refl. Qed.
Lemma D_5d548 : CTabKB.D W_5d548 (Op ALU_SLL 10 10 11).
Proof. vm_refl. Qed.
Definition W_5d54c : bv 32 := 0x0005061b.
Lemma F_5d54c : CTabKB.F 0x5d54c W_5d54c.
Proof. vm_refl. Qed.
Lemma D_5d54c : CTabKB.D W_5d54c (OpImm32 12 10 0).
Proof. vm_refl. Qed.
Definition W_5d550 : bv 32 := 0x06c05a63.
Lemma F_5d550 : CTabKB.F 0x5d550 W_5d550.
Proof. vm_refl. Qed.
Lemma D_5d550 : CTabKB.D W_5d550 (Branch BC_GE 0 12 116).
Proof. vm_refl. Qed.
Definition W_5d554 : bv 32 := 0x000016b7.
Lemma F_5d554 : CTabKB.F 0x5d554 W_5d554.
Proof. vm_refl. Qed.
Lemma D_5d554 : CTabKB.D W_5d554 (Lui 13 1).
Proof. vm_refl. Qed.
Definition W_5d558 : bv 32 := 0xfff00713.
Lemma F_5d558 : CTabKB.F 0x5d558 W_5d558.
Proof. vm_refl. Qed.
Lemma D_5d558 : CTabKB.D W_5d558 (OpImm ALU_ADD 14 0 4095).
Proof. vm_refl. Qed.
Definition W_5d55c : bv 32 := 0x0004b603.
Lemma F_5d55c : CTabKB.F 0x5d55c W_5d55c.
Proof. vm_refl. Qed.
Lemma D_5d55c : CTabKB.D W_5d55c (Load SZ8 true 12 9 0).
Proof. vm_refl. Qed.
Definition W_5d560 : bv 32 := 0x00b71733.
Lemma F_5d560 : CTabKB.F 0x5d560 W_5d560.
Proof. vm_refl. Qed.
Lemma D_5d560 : CTabKB.D W_5d560 (Op ALU_SLL 14 14 11).
Proof. vm_refl. Qed.
Definition W_5d564 : bv 32 := 0xfff50793.
Lemma F_5d564 : CTabKB.F 0x5d564 W_5d564.
Proof. vm_refl. Qed.
Lemma D_5d564 : CTabKB.D W_5d564 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_5d568 : bv 32 := 0x00d485b3.
Lemma F_5d568 : CTabKB.F 0x5d568 W_5d568.
Proof. vm_refl. Qed.
Lemma D_5d568 : CTabKB.D W_5d568 (Op ALU_ADD 11 9 13).
Proof. vm_refl. Qed.
Definition W_5d56c : bv 32 := 0xfff74693.
Lemma F_5d56c : CTabKB.F 0x5d56c W_5d56c.
Proof. vm_refl. Qed.
Lemma D_5d56c : CTabKB.D W_5d56c (OpImm ALU_XOR 13 14 4095).
Proof. vm_refl. Qed.
Definition W_5d570 : bv 32 := 0x02079793.
Lemma F_5d570 : CTabKB.F 0x5d570 W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : CTabKB.D W_5d570 (ShiftImm ALU_SLL 15 15 32).
Proof. vm_refl. Qed.
Definition W_5d574 : bv 32 := 0x0207d793.
Lemma F_5d574 : CTabKB.F 0x5d574 W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : CTabKB.D W_5d574 (ShiftImm ALU_SRL 15 15 32).
Proof. vm_refl. Qed.
Definition W_5d578 : bv 32 := 0x00f60733.
Lemma F_5d578 : CTabKB.F 0x5d578 W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : CTabKB.D W_5d578 (Op ALU_ADD 14 12 15).
Proof. vm_refl. Qed.
Definition W_5d57c : bv 32 := 0x00170713.
Lemma F_5d57c : CTabKB.F 0x5d57c W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : CTabKB.D W_5d57c (OpImm ALU_ADD 14 14 1).
Proof. vm_refl. Qed.
Definition W_5d580 : bv 32 := 0x00d67833.
Lemma F_5d580 : CTabKB.F 0x5d580 W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : CTabKB.D W_5d580 (Op ALU_AND 16 12 13).
Proof. vm_refl. Qed.
Definition W_5d584 : bv 32 := 0x010587b3.
Lemma F_5d584 : CTabKB.F 0x5d584 W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : CTabKB.D W_5d584 (Op ALU_ADD 15 11 16).
Proof. vm_refl. Qed.
Definition W_5d588 : bv 32 := 0x0007c883.
Lemma F_5d588 : CTabKB.F 0x5d588 W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : CTabKB.D W_5d588 (Load SZ1 false 17 15 0).
Proof. vm_refl. Qed.
Definition W_5d58c : bv 32 := 0x06088663.
Lemma F_5d58c : CTabKB.F 0x5d58c W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : CTabKB.D W_5d58c (Branch BC_EQ 17 0 108).
Proof. vm_refl. Qed.
Definition W_5d590 : bv 32 := 0xfff5051b.
Lemma F_5d590 : CTabKB.F 0x5d590 W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : CTabKB.D W_5d590 (OpImm32 10 10 4095).
Proof. vm_refl. Qed.
Definition W_5d594 : bv 32 := 0x00160613.
Lemma F_5d594 : CTabKB.F 0x5d594 W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : CTabKB.D W_5d594 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d598 : bv 32 := 0xfe0514e3.
Lemma F_5d598 : CTabKB.F 0x5d598 W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : CTabKB.D W_5d598 (Branch BC_NE 10 0 8168).
Proof. vm_refl. Qed.
Definition W_5d59c : bv 32 := 0x00e4b023.
Lemma F_5d59c : CTabKB.F 0x5d59c W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : CTabKB.D W_5d59c (Store SZ8 9 14 0).
Proof. vm_refl. Qed.
Definition W_5d5a0 : bv 32 := 0x0400006f.
Lemma F_5d5a0 : CTabKB.F 0x5d5a0 W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : CTabKB.D W_5d5a0 (Jal 0 64).
Proof. vm_refl. Qed.
Definition W_5d5a4 : bv 32 := 0x000d7517.
Lemma F_5d5a4 : CTabKB.F 0x5d5a4 W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : CTabKB.D W_5d5a4 (Auipc 10 215).
Proof. vm_refl. Qed.
Definition W_5d5a8 : bv 32 := 0xe5453503.
Lemma F_5d5a8 : CTabKB.F 0x5d5a8 W_5d5a8.
Proof. vm_refl. Qed.
Lemma D_5d5a8 : CTabKB.D W_5d5a8 (Load SZ8 true 10 10 3668).
Proof. vm_refl. Qed.
Definition W_5d5ac : bv 32 := 0x00052503.
Lemma F_5d5ac : CTabKB.F 0x5d5ac W_5d5ac.
Proof. vm_refl. Qed.
Lemma D_5d5ac : CTabKB.D W_5d5ac (Load SZ4 true 10 10 0).
Proof. vm_refl. Qed.
Definition W_5d5b0 : bv 32 := 0x02050863.
Lemma F_5d5b0 : CTabKB.F 0x5d5b0 W_5d5b0.
Proof. vm_refl. Qed.
Lemma D_5d5b0 : CTabKB.D W_5d5b0 (Branch BC_EQ 10 0 48).
Proof. vm_refl. Qed.
Definition W_5d5b4 : bv 32 := 0x4a9250ef.
Lemma F_5d5b4 : CTabKB.F 0x5d5b4 W_5d5b4.
Proof. vm_refl. Qed.
Lemma D_5d5b4 : CTabKB.D W_5d5b4 (Jal 1 154792).
Proof. vm_refl. Qed.
Definition W_5d5b8 : bv 32 := 0x02050463.
Lemma F_5d5b8 : CTabKB.F 0x5d5b8 W_5d5b8.
Proof. vm_refl. Qed.
Lemma D_5d5b8 : CTabKB.D W_5d5b8 (Branch BC_EQ 10 0 40).
Proof. vm_refl. Qed.
Definition W_5d5bc : bv 32 := 0x02850583.
Lemma F_5d5bc : CTabKB.F 0x5d5bc W_5d5bc.
Proof. vm_refl. Qed.
Lemma D_5d5bc : CTabKB.D W_5d5bc (Load SZ1 true 11 10 40).
Proof. vm_refl. Qed.
Definition W_5d5c0 : bv 32 := 0x08058a63.
Lemma F_5d5c0 : CTabKB.F 0x5d5c0 W_5d5c0.
Proof. vm_refl. Qed.
Lemma D_5d5c0 : CTabKB.D W_5d5c0 (Branch BC_EQ 11 0 148).
Proof. vm_refl. Qed.
Definition W_5d5c4 : bv 32 := 0x00000513.
Lemma F_5d5c4 : CTabKB.F 0x5d5c4 W_5d5c4.
Proof. vm_refl. Qed.
Lemma D_5d5c4 : CTabKB.D W_5d5c4 (OpImm ALU_ADD 10 0 0).
Proof. vm_refl. Qed.
Definition W_5d5c8 : bv 32 := 0x01813083.
Lemma F_5d5c8 : CTabKB.F 0x5d5c8 W_5d5c8.
Proof. vm_refl. Qed.
Lemma D_5d5c8 : CTabKB.D W_5d5c8 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d5cc : bv 32 := 0x01013403.
Lemma F_5d5cc : CTabKB.F 0x5d5cc W_5d5cc.
Proof. vm_refl. Qed.
Lemma D_5d5cc : CTabKB.D W_5d5cc (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d5d0 : bv 32 := 0x00813483.
Lemma F_5d5d0 : CTabKB.F 0x5d5d0 W_5d5d0.
Proof. vm_refl. Qed.
Lemma D_5d5d0 : CTabKB.D W_5d5d0 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d5d4 : bv 32 := 0x00013903.
Lemma F_5d5d4 : CTabKB.F 0x5d5d4 W_5d5d4.
Proof. vm_refl. Qed.
Lemma D_5d5d4 : CTabKB.D W_5d5d4 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d5d8 : bv 32 := 0x02010113.
Lemma F_5d5d8 : CTabKB.F 0x5d5d8 W_5d5d8.
Proof. vm_refl. Qed.
Lemma D_5d5d8 : CTabKB.D W_5d5d8 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d5dc : bv 32 := 0x00008067.
Lemma F_5d5dc : CTabKB.F 0x5d5dc W_5d5dc.
Proof. vm_refl. Qed.
Lemma D_5d5dc : CTabKB.D W_5d5dc (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d5e0 : bv 32 := 0x01813083.
Lemma F_5d5e0 : CTabKB.F 0x5d5e0 W_5d5e0.
Proof. vm_refl. Qed.
Lemma D_5d5e0 : CTabKB.D W_5d5e0 (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d5e4 : bv 32 := 0x01013403.
Lemma F_5d5e4 : CTabKB.F 0x5d5e4 W_5d5e4.
Proof. vm_refl. Qed.
Lemma D_5d5e4 : CTabKB.D W_5d5e4 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d5e8 : bv 32 := 0x00813483.
Lemma F_5d5e8 : CTabKB.F 0x5d5e8 W_5d5e8.
Proof. vm_refl. Qed.
Lemma D_5d5e8 : CTabKB.D W_5d5e8 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d5ec : bv 32 := 0x00013903.
Lemma F_5d5ec : CTabKB.F 0x5d5ec W_5d5ec.
Proof. vm_refl. Qed.
Lemma D_5d5ec : CTabKB.D W_5d5ec (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d5f0 : bv 32 := 0x02010113.
Lemma F_5d5f0 : CTabKB.F 0x5d5f0 W_5d5f0.
Proof. vm_refl. Qed.
Lemma D_5d5f0 : CTabKB.D W_5d5f0 (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d5f4 : bv 32 := 0x00008067.
Lemma F_5d5f4 : CTabKB.F 0x5d5f4 W_5d5f4.
Proof. vm_refl. Qed.
Lemma D_5d5f4 : CTabKB.D W_5d5f4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d5f8 : bv 32 := 0x00160613.
Lemma F_5d5f8 : CTabKB.F 0x5d5f8 W_5d5f8.
Proof. vm_refl. Qed.
Lemma D_5d5f8 : CTabKB.D W_5d5f8 (OpImm ALU_ADD 12 12 1).
Proof. vm_refl. Qed.
Definition W_5d5fc : bv 32 := 0x00100513.
Lemma F_5d5fc : CTabKB.F 0x5d5fc W_5d5fc.
Proof. vm_refl. Qed.
Lemma D_5d5fc : CTabKB.D W_5d5fc (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_5d600 : bv 32 := 0xffb90913.
Lemma F_5d600 : CTabKB.F 0x5d600 W_5d600.
Proof. vm_refl. Qed.
Lemma D_5d600 : CTabKB.D W_5d600 (OpImm ALU_ADD 18 18 4091).
Proof. vm_refl. Qed.
Definition W_5d604 : bv 32 := 0x00681813.
Lemma F_5d604 : CTabKB.F 0x5d604 W_5d604.
Proof. vm_refl. Qed.
Lemma D_5d604 : CTabKB.D W_5d604 (ShiftImm ALU_SLL 16 16 6).
Proof. vm_refl. Qed.
Definition W_5d608 : bv 32 := 0x00c4b023.
Lemma F_5d608 : CTabKB.F 0x5d608 W_5d608.
Proof. vm_refl. Qed.
Lemma D_5d608 : CTabKB.D W_5d608 (Store SZ8 9 12 0).
Proof. vm_refl. Qed.
Definition W_5d60c : bv 32 := 0x00a78023.
Lemma F_5d60c : CTabKB.F 0x5d60c W_5d60c.
Proof. vm_refl. Qed.
Lemma D_5d60c : CTabKB.D W_5d60c (Store SZ1 15 10 0).
Proof. vm_refl. Qed.
Definition W_5d610 : bv 32 := 0x01251533.
Lemma F_5d610 : CTabKB.F 0x5d610 W_5d610.
Proof. vm_refl. Qed.
Lemma D_5d610 : CTabKB.D W_5d610 (Op ALU_SLL 10 10 18).
Proof. vm_refl. Qed.
Definition W_5d614 : bv 32 := 0x00a58533.
Lemma F_5d614 : CTabKB.F 0x5d614 W_5d614.
Proof. vm_refl. Qed.
Lemma D_5d614 : CTabKB.D W_5d614 (Op ALU_ADD 10 11 10).
Proof. vm_refl. Qed.
Definition W_5d618 : bv 32 := 0x010504b3.
Lemma F_5d618 : CTabKB.F 0x5d618 W_5d618.
Proof. vm_refl. Qed.
Lemma D_5d618 : CTabKB.D W_5d618 (Op ALU_ADD 9 10 16).
Proof. vm_refl. Qed.
Definition W_5d61c : bv 32 := 0x0084bc23.
Lemma F_5d61c : CTabKB.F 0x5d61c W_5d61c.
Proof. vm_refl. Qed.
Lemma D_5d61c : CTabKB.D W_5d61c (Store SZ8 9 8 24).
Proof. vm_refl. Qed.
Definition W_5d620 : bv 32 := 0x02f4bc23.
Lemma F_5d620 : CTabKB.F 0x5d620 W_5d620.
Proof. vm_refl. Qed.
Lemma D_5d620 : CTabKB.D W_5d620 (Store SZ8 9 15 56).
Proof. vm_refl. Qed.
Definition W_5d624 : bv 32 := 0x00048513.
Lemma F_5d624 : CTabKB.F 0x5d624 W_5d624.
Proof. vm_refl. Qed.
Lemma D_5d624 : CTabKB.D W_5d624 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d628 : bv 32 := 0x6ec000ef.
Lemma F_5d628 : CTabKB.F 0x5d628 W_5d628.
Proof. vm_refl. Qed.
Lemma D_5d628 : CTabKB.D W_5d628 (Jal 1 1772).
Proof. vm_refl. Qed.
Definition W_5d62c : bv 32 := 0x00050593.
Lemma F_5d62c : CTabKB.F 0x5d62c W_5d62c.
Proof. vm_refl. Qed.
Lemma D_5d62c : CTabKB.D W_5d62c (OpImm ALU_ADD 11 10 0).
Proof. vm_refl. Qed.
Definition W_5d630 : bv 32 := 0x00048513.
Lemma F_5d630 : CTabKB.F 0x5d630 W_5d630.
Proof. vm_refl. Qed.
Lemma D_5d630 : CTabKB.D W_5d630 (OpImm ALU_ADD 10 9 0).
Proof. vm_refl. Qed.
Definition W_5d634 : bv 32 := 0x00000613.
Lemma F_5d634 : CTabKB.F 0x5d634 W_5d634.
Proof. vm_refl. Qed.
Lemma D_5d634 : CTabKB.D W_5d634 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5d638 : bv 32 := 0x0005b023.
Lemma F_5d638 : CTabKB.F 0x5d638 W_5d638.
Proof. vm_refl. Qed.
Lemma D_5d638 : CTabKB.D W_5d638 (Store SZ8 11 0 0).
Proof. vm_refl. Qed.
Definition W_5d63c : bv 32 := 0x01813083.
Lemma F_5d63c : CTabKB.F 0x5d63c W_5d63c.
Proof. vm_refl. Qed.
Lemma D_5d63c : CTabKB.D W_5d63c (Load SZ8 true 1 2 24).
Proof. vm_refl. Qed.
Definition W_5d640 : bv 32 := 0x01013403.
Lemma F_5d640 : CTabKB.F 0x5d640 W_5d640.
Proof. vm_refl. Qed.
Lemma D_5d640 : CTabKB.D W_5d640 (Load SZ8 true 8 2 16).
Proof. vm_refl. Qed.
Definition W_5d644 : bv 32 := 0x00813483.
Lemma F_5d644 : CTabKB.F 0x5d644 W_5d644.
Proof. vm_refl. Qed.
Lemma D_5d644 : CTabKB.D W_5d644 (Load SZ8 true 9 2 8).
Proof. vm_refl. Qed.
Definition W_5d648 : bv 32 := 0x00013903.
Lemma F_5d648 : CTabKB.F 0x5d648 W_5d648.
Proof. vm_refl. Qed.
Lemma D_5d648 : CTabKB.D W_5d648 (Load SZ8 true 18 2 0).
Proof. vm_refl. Qed.
Definition W_5d64c : bv 32 := 0x02010113.
Lemma F_5d64c : CTabKB.F 0x5d64c W_5d64c.
Proof. vm_refl. Qed.
Lemma D_5d64c : CTabKB.D W_5d64c (OpImm ALU_ADD 2 2 32).
Proof. vm_refl. Qed.
Definition W_5d650 : bv 32 := 0x00008067.
Lemma F_5d650 : CTabKB.F 0x5d650 W_5d650.
Proof. vm_refl. Qed.
Lemma D_5d650 : CTabKB.D W_5d650 (Jalr 0 1 0).
Proof. vm_refl. Qed.
Definition W_5d654 : bv 32 := 0x04853483.
Lemma F_5d654 : CTabKB.F 0x5d654 W_5d654.
Proof. vm_refl. Qed.
Lemma D_5d654 : CTabKB.D W_5d654 (Load SZ8 true 9 10 72).
Proof. vm_refl. Qed.
Definition W_5d658 : bv 32 := 0x00100593.
Lemma F_5d658 : CTabKB.F 0x5d658 W_5d658.
Proof. vm_refl. Qed.
Lemma D_5d658 : CTabKB.D W_5d658 (OpImm ALU_ADD 11 0 1).
Proof. vm_refl. Qed.
Definition W_5d65c : bv 32 := 0x0095e663.
Lemma F_5d65c : CTabKB.F 0x5d65c W_5d65c.
Proof. vm_refl. Qed.
Lemma D_5d65c : CTabKB.D W_5d65c (Branch BC_LTU 11 9 12).
Proof. vm_refl. Qed.
Definition W_5d660 : bv 32 := 0x671250ef.
Lemma F_5d660 : CTabKB.F 0x5d660 W_5d660.
Proof. vm_refl. Qed.
Lemma D_5d660 : CTabKB.D W_5d660 (Jal 1 155248).
Proof. vm_refl. Qed.
Definition W_5d664 : bv 32 := 0x00050493.
Lemma F_5d664 : CTabKB.F 0x5d664 W_5d664.
Proof. vm_refl. Qed.
Lemma D_5d664 : CTabKB.D W_5d664 (OpImm ALU_ADD 9 10 0).
Proof. vm_refl. Qed.
Definition W_5d668 : bv 32 := 0xec0490e3.
Lemma F_5d668 : CTabKB.F 0x5d668 W_5d668.
Proof. vm_refl. Qed.
Lemma D_5d668 : CTabKB.D W_5d668 (Branch BC_NE 9 0 7872).
Proof. vm_refl. Qed.
Definition W_5d66c : bv 32 := 0xf59ff06f.
Lemma F_5d66c : CTabKB.F 0x5d66c W_5d66c.
Proof. vm_refl. Qed.
Lemma D_5d66c : CTabKB.D W_5d66c (Jal 0 2096984).
Proof. vm_refl. Qed.
