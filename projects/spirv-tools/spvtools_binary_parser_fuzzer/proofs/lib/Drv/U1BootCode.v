(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec StreamSim StoreOk.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_656b0 : bv 32 := 0xfffab197.
Lemma D_656b0 : decode_any W_656b0 = Some (Auipc 3 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_656b4 : bv 32 := 0x11018193.
Lemma D_656b4 : decode_any W_656b4 = Some (OpImm ALU_ADD 3 3 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_656b8 : bv 32 := 0x00010513.
Lemma D_656b8 : decode_any W_656b8 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_656bc : bv 32 := 0xfff9b597.
Lemma D_656bc : decode_any W_656bc = Some (Auipc 11 1048475, 4%Z).
Proof. vm_refl. Qed.

Definition W_656c0 : bv 32 := 0x90458593.
Lemma D_656c0 : decode_any W_656c0 = Some (OpImm ALU_ADD 11 11 2308, 4%Z).
Proof. vm_refl. Qed.

Definition W_656c4 : bv 32 := 0xff017113.
Lemma D_656c4 : decode_any W_656c4 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_656c8 : bv 32 := 0x0040006f.
Lemma D_656c8 : decode_any W_656c8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_656cc : bv 32 := 0x00052583.
Lemma D_656cc : decode_any W_656cc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_656d0 : bv 32 := 0x00089617.
Lemma D_656d0 : decode_any W_656d0 = Some (Auipc 12 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_656d4 : bv 32 := 0x00089697.
Lemma D_656d4 : decode_any W_656d4 = Some (Auipc 13 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_656d8 : bv 32 := 0x00089717.
Lemma D_656d8 : decode_any W_656d8 = Some (Auipc 14 137, 4%Z).
Proof. vm_refl. Qed.

Definition W_656dc : bv 32 := 0x51863783.
Lemma D_656dc : decode_any W_656dc = Some (Load SZ8 true 15 12 1304, 4%Z).
Proof. vm_refl. Qed.

Definition W_656e0 : bv 32 := 0x51c6b683.
Lemma D_656e0 : decode_any W_656e0 = Some (Load SZ8 true 13 13 1308, 4%Z).
Proof. vm_refl. Qed.

Definition W_656e4 : bv 32 := 0x52073703.
Lemma D_656e4 : decode_any W_656e4 = Some (Load SZ8 true 14 14 1312, 4%Z).
Proof. vm_refl. Qed.

Definition W_656e8 : bv 32 := 0x00850613.
Lemma D_656e8 : decode_any W_656e8 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_656ec : bv 32 := 0x00078513.
Lemma D_656ec : decode_any W_656ec = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_656f0 : bv 32 := 0x00000793.
Lemma D_656f0 : decode_any W_656f0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_656f4 : bv 32 := 0x0306c06f.
Lemma D_656f4 : decode_any W_656f4 = Some (Jal 0 442416, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14a8 : bv 32 := 0x00008067.
Lemma D_d14a8 : decode_any W_d14a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14ac : bv 32 := 0xe8010113.
Lemma D_d14ac : decode_any W_d14ac = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14b0 : bv 32 := 0x16113c23.
Lemma D_d14b0 : decode_any W_d14b0 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14b4 : bv 32 := 0x16813823.
Lemma D_d14b4 : decode_any W_d14b4 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14b8 : bv 32 := 0x16913423.
Lemma D_d14b8 : decode_any W_d14b8 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14bc : bv 32 := 0x17213023.
Lemma D_d14bc : decode_any W_d14bc = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14c0 : bv 32 := 0x00058413.
Lemma D_d14c0 : decode_any W_d14c0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14c4 : bv 32 := 0x00050493.
Lemma D_d14c4 : decode_any W_d14c4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14c8 : bv 32 := 0x03010513.
Lemma D_d14c8 : decode_any W_d14c8 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14cc : bv 32 := 0x13000613.
Lemma D_d14cc : decode_any W_d14cc = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14d0 : bv 32 := 0x00000593.
Lemma D_d14d0 : decode_any W_d14d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14d4 : bv 32 := 0x409110ef.
Lemma D_d14d4 : decode_any W_d14d4 = Some (Jal 1 72712, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14d8 : bv 32 := 0x0001e517.
Lemma D_d14d8 : decode_any W_d14d8 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14dc : bv 32 := 0x8d053503.
Lemma D_d14dc : decode_any W_d14dc = Some (Load SZ8 true 10 10 2256, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14e0 : bv 32 := 0x00953023.
Lemma D_d14e0 : decode_any W_d14e0 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14e4 : bv 32 := 0x0004b503.
Lemma D_d14e4 : decode_any W_d14e4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14e8 : bv 32 := 0x00848493.
Lemma D_d14e8 : decode_any W_d14e8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14ec : bv 32 := 0xfe051ce3.
Lemma D_d14ec : decode_any W_d14ec = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14f0 : bv 32 := 0x00051517.
Lemma D_d14f0 : decode_any W_d14f0 = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14f4 : bv 32 := 0x17850913.
Lemma D_d14f4 : decode_any W_d14f4 = Some (OpImm ALU_ADD 18 10 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14f8 : bv 32 := 0x00993423.
Lemma D_d14f8 : decode_any W_d14f8 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d14fc : bv 32 := 0x0004b583.
Lemma D_d14fc : decode_any W_d14fc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1500 : bv 32 := 0x04058c63.
Lemma D_d1500 : decode_any W_d1500 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1504 : bv 32 := 0x01048493.
Lemma D_d1504 : decode_any W_d1504 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1508 : bv 32 := 0x02500513.
Lemma D_d1508 : decode_any W_d1508 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_d150c : bv 32 := 0x03010613.
Lemma D_d150c : decode_any W_d150c = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1510 : bv 32 := 0x0100006f.
Lemma D_d1510 : decode_any W_d1510 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1514 : bv 32 := 0x0004b583.
Lemma D_d1514 : decode_any W_d1514 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1518 : bv 32 := 0x01048493.
Lemma D_d1518 : decode_any W_d1518 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d151c : bv 32 := 0x00058e63.
Lemma D_d151c : decode_any W_d151c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1520 : bv 32 := 0xfeb56ae3.
Lemma D_d1520 : decode_any W_d1520 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1524 : bv 32 := 0xff84b683.
Lemma D_d1524 : decode_any W_d1524 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1528 : bv 32 := 0x00359593.
Lemma D_d1528 : decode_any W_d1528 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_d152c : bv 32 := 0x00b605b3.
Lemma D_d152c : decode_any W_d152c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1530 : bv 32 := 0x00d5b023.
Lemma D_d1530 : decode_any W_d1530 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1534 : bv 32 := 0xfe1ff06f.
Lemma D_d1534 : decode_any W_d1534 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1538 : bv 32 := 0x0b013583.
Lemma D_d1538 : decode_any W_d1538 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_d153c : bv 32 := 0x13013503.
Lemma D_d153c : decode_any W_d153c = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1540 : bv 32 := 0x00051617.
Lemma D_d1540 : decode_any W_d1540 = Some (Auipc 12 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1544 : bv 32 := 0x18b63823.
Lemma D_d1544 : decode_any W_d1544 = Some (Store SZ8 12 11 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1548 : bv 32 := 0x00050c63.
Lemma D_d1548 : decode_any W_d1548 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1560 : bv 32 := 0x06013503.
Lemma D_d1560 : decode_any W_d1560 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1564 : bv 32 := 0x02a93823.
Lemma D_d1564 : decode_any W_d1564 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1568 : bv 32 := 0x00041463.
Lemma D_d1568 : decode_any W_d1568 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1570 : bv 32 := 0x00041663.
Lemma D_d1570 : decode_any W_d1570 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d157c : bv 32 := 0x0001e517.
Lemma D_d157c : decode_any W_d157c = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1580 : bv 32 := 0x83453583.
Lemma D_d1580 : decode_any W_d1580 = Some (Load SZ8 true 11 10 2100, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1584 : bv 32 := 0x0001e517.
Lemma D_d1584 : decode_any W_d1584 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1588 : bv 32 := 0x83453503.
Lemma D_d1588 : decode_any W_d1588 = Some (Load SZ8 true 10 10 2100, 4%Z).
Proof. vm_refl. Qed.

Definition W_d158c : bv 32 := 0x0085b023.
Lemma D_d158c : decode_any W_d158c = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1590 : bv 32 := 0x00140593.
Lemma D_d1590 : decode_any W_d1590 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1594 : bv 32 := 0x00853023.
Lemma D_d1594 : decode_any W_d1594 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1598 : bv 32 := 0x02f00613.
Lemma D_d1598 : decode_any W_d1598 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_d159c : bv 32 := 0x00c0006f.
Lemma D_d159c : decode_any W_d159c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15a0 : bv 32 := 0x00b53023.
Lemma D_d15a0 : decode_any W_d15a0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15a4 : bv 32 := 0x00158593.
Lemma D_d15a4 : decode_any W_d15a4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15a8 : bv 32 := 0xfff5c683.
Lemma D_d15a8 : decode_any W_d15a8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15ac : bv 32 := 0xfec68ae3.
Lemma D_d15ac : decode_any W_d15ac = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15b0 : bv 32 := 0xfe069ae3.
Lemma D_d15b0 : decode_any W_d15b0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15b4 : bv 32 := 0x03010513.
Lemma D_d15b4 : decode_any W_d15b4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15b8 : bv 32 := 0x214000ef.
Lemma D_d15b8 : decode_any W_d15b8 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15bc : bv 32 := 0x0f813503.
Lemma D_d15bc : decode_any W_d15bc = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15c0 : bv 32 := 0x1ad000ef.
Lemma D_d15c0 : decode_any W_d15c0 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15c4 : bv 32 := 0x08813503.
Lemma D_d15c4 : decode_any W_d15c4 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15c8 : bv 32 := 0x09013583.
Lemma D_d15c8 : decode_any W_d15c8 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15cc : bv 32 := 0x00b51c63.
Lemma D_d15cc : decode_any W_d15cc = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15d0 : bv 32 := 0x09813503.
Lemma D_d15d0 : decode_any W_d15d0 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15d4 : bv 32 := 0x0a013583.
Lemma D_d15d4 : decode_any W_d15d4 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15d8 : bv 32 := 0x00b51663.
Lemma D_d15d8 : decode_any W_d15d8 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15dc : bv 32 := 0x0e813503.
Lemma D_d15dc : decode_any W_d15dc = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_d15e0 : bv 32 := 0x0e050063.
Lemma D_d15e0 : decode_any W_d15e0 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16c0 : bv 32 := 0x17813083.
Lemma D_d16c0 : decode_any W_d16c0 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16c4 : bv 32 := 0x17013403.
Lemma D_d16c4 : decode_any W_d16c4 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16c8 : bv 32 := 0x16813483.
Lemma D_d16c8 : decode_any W_d16c8 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16cc : bv 32 := 0x16013903.
Lemma D_d16cc : decode_any W_d16cc = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16d0 : bv 32 := 0x18010113.
Lemma D_d16d0 : decode_any W_d16d0 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16d4 : bv 32 := 0x00008067.
Lemma D_d16d4 : decode_any W_d16d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16d8 : bv 32 := 0xfe010113.
Lemma D_d16d8 : decode_any W_d16d8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16dc : bv 32 := 0x00113c23.
Lemma D_d16dc : decode_any W_d16dc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16e0 : bv 32 := 0x00813823.
Lemma D_d16e0 : decode_any W_d16e0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16e4 : bv 32 := 0x00913423.
Lemma D_d16e4 : decode_any W_d16e4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16e8 : bv 32 := 0xdc1ff0ef.
Lemma D_d16e8 : decode_any W_d16e8 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16ec : bv 32 := 0x0001d517.
Lemma D_d16ec : decode_any W_d16ec = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16f0 : bv 32 := 0x0001d597.
Lemma D_d16f0 : decode_any W_d16f0 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16f4 : bv 32 := 0x6d453403.
Lemma D_d16f4 : decode_any W_d16f4 = Some (Load SZ8 true 8 10 1748, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16f8 : bv 32 := 0x6d85b483.
Lemma D_d16f8 : decode_any W_d16f8 = Some (Load SZ8 true 9 11 1752, 4%Z).
Proof. vm_refl. Qed.

Definition W_d16fc : bv 32 := 0x0084fa63.
Lemma D_d16fc : decode_any W_d16fc = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1700 : bv 32 := 0x0004b503.
Lemma D_d1700 : decode_any W_d1700 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1704 : bv 32 := 0x000500e7.
Lemma D_d1704 : decode_any W_d1704 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1708 : bv 32 := 0x00848493.

Definition W_d170c : bv 32 := 0xfe84eae3.

Definition W_d1710 : bv 32 := 0x01813083.

Definition W_d1714 : bv 32 := 0x01013403.

Definition W_d1718 : bv 32 := 0x00813483.

Definition W_d171c : bv 32 := 0x02010113.

Definition W_d1720 : bv 32 := 0x00008067.

Definition W_d1724 : bv 32 := 0xfe010113.
Lemma D_d1724 : decode_any W_d1724 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1728 : bv 32 := 0x00113c23.
Lemma D_d1728 : decode_any W_d1728 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d172c : bv 32 := 0x00813823.
Lemma D_d172c : decode_any W_d172c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1730 : bv 32 := 0x00913423.
Lemma D_d1730 : decode_any W_d1730 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1734 : bv 32 := 0x01213023.
Lemma D_d1734 : decode_any W_d1734 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1738 : bv 32 := 0x00060413.
Lemma D_d1738 : decode_any W_d1738 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d173c : bv 32 := 0x00058493.
Lemma D_d173c : decode_any W_d173c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1740 : bv 32 := 0x00050913.
Lemma D_d1740 : decode_any W_d1740 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1744 : bv 32 := 0x00063583.
Lemma D_d1744 : decode_any W_d1744 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1748 : bv 32 := 0x00349513.
Lemma D_d1748 : decode_any W_d1748 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_d174c : bv 32 := 0x00a60533.
Lemma D_d174c : decode_any W_d174c = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1750 : bv 32 := 0x00850513.
Lemma D_d1750 : decode_any W_d1750 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1754 : bv 32 := 0xd59ff0ef.
Lemma D_d1754 : decode_any W_d1754 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1758 : bv 32 := 0x00000517.
Lemma D_d1758 : decode_any W_d1758 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d175c : bv 32 := 0x02c50313.
Lemma D_d175c : decode_any W_d175c = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1760 : bv 32 := 0x00090513.
Lemma D_d1760 : decode_any W_d1760 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1764 : bv 32 := 0x00048593.
Lemma D_d1764 : decode_any W_d1764 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1768 : bv 32 := 0x00040613.
Lemma D_d1768 : decode_any W_d1768 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d176c : bv 32 := 0x01813083.
Lemma D_d176c : decode_any W_d176c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1770 : bv 32 := 0x01013403.
Lemma D_d1770 : decode_any W_d1770 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1774 : bv 32 := 0x00813483.
Lemma D_d1774 : decode_any W_d1774 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1778 : bv 32 := 0x00013903.
Lemma D_d1778 : decode_any W_d1778 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d177c : bv 32 := 0x02010113.
Lemma D_d177c : decode_any W_d177c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1780 : bv 32 := 0x00030067.
Lemma D_d1780 : decode_any W_d1780 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1784 : bv 32 := 0xfd010113.
Lemma D_d1784 : decode_any W_d1784 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1788 : bv 32 := 0x02113423.
Lemma D_d1788 : decode_any W_d1788 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d178c : bv 32 := 0x02813023.
Lemma D_d178c : decode_any W_d178c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1790 : bv 32 := 0x00913c23.
Lemma D_d1790 : decode_any W_d1790 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1794 : bv 32 := 0x01213823.
Lemma D_d1794 : decode_any W_d1794 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1798 : bv 32 := 0x01313423.
Lemma D_d1798 : decode_any W_d1798 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d179c : bv 32 := 0x00060413.
Lemma D_d179c : decode_any W_d179c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17a0 : bv 32 := 0x00058493.
Lemma D_d17a0 : decode_any W_d17a0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17a4 : bv 32 := 0x00050913.
Lemma D_d17a4 : decode_any W_d17a4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17a8 : bv 32 := 0x00359513.
Lemma D_d17a8 : decode_any W_d17a8 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17ac : bv 32 := 0x00a60533.
Lemma D_d17ac : decode_any W_d17ac = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17b0 : bv 32 := 0x00850993.
Lemma D_d17b0 : decode_any W_d17b0 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17b4 : bv 32 := 0xf25ff0ef.
Lemma D_d17b4 : decode_any W_d17b4 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_d17b8 : bv 32 := 0x00048513.

Definition W_d17bc : bv 32 := 0x00040593.

Definition W_d17c0 : bv 32 := 0x00098613.

Definition W_d17c4 : bv 32 := 0x000900e7.

Definition W_d180c : bv 32 := 0xfc010113.
Lemma D_d180c : decode_any W_d180c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1810 : bv 32 := 0x02113c23.
Lemma D_d1810 : decode_any W_d1810 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1814 : bv 32 := 0x02813823.
Lemma D_d1814 : decode_any W_d1814 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1818 : bv 32 := 0x02913423.
Lemma D_d1818 : decode_any W_d1818 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d181c : bv 32 := 0x03213023.
Lemma D_d181c : decode_any W_d181c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1820 : bv 32 := 0x01313c23.
Lemma D_d1820 : decode_any W_d1820 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1824 : bv 32 := 0x01413823.
Lemma D_d1824 : decode_any W_d1824 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1828 : bv 32 := 0x01513423.
Lemma D_d1828 : decode_any W_d1828 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d182c : bv 32 := 0x02853683.
Lemma D_d182c : decode_any W_d182c = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1830 : bv 32 := 0x00051597.
Lemma D_d1830 : decode_any W_d1830 = Some (Auipc 11 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1834 : bv 32 := 0xbf058593.
Lemma D_d1834 : decode_any W_d1834 = Some (OpImm ALU_ADD 11 11 3056, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1838 : bv 32 := 0x00051617.
Lemma D_d1838 : decode_any W_d1838 = Some (Auipc 12 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_d183c : bv 32 := 0xe7060493.
Lemma D_d183c : decode_any W_d183c = Some (OpImm ALU_ADD 9 12 3696, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1840 : bv 32 := 0x0c068e63.
Lemma D_d1840 : decode_any W_d1840 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1844 : bv 32 := 0x00000613.
Lemma D_d1844 : decode_any W_d1844 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1848 : bv 32 := 0x00000893.
Lemma D_d1848 : decode_any W_d1848 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d184c : bv 32 := 0x0001f717.
Lemma D_d184c : decode_any W_d184c = Some (Auipc 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1850 : bv 32 := 0x01853783.
Lemma D_d1850 : decode_any W_d1850 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1854 : bv 32 := 0x02053503.
Lemma D_d1854 : decode_any W_d1854 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1858 : bv 32 := 0x00600813.
Lemma D_d1858 : decode_any W_d1858 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_d185c : bv 32 := 0x0001d297.
Lemma D_d185c : decode_any W_d185c = Some (Auipc 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1860 : bv 32 := 0x98c76f03.
Lemma D_d1860 : decode_any W_d1860 = Some (Load SZ4 false 30 14 2444, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1864 : bv 32 := 0x3c42b283.
Lemma D_d1864 : decode_any W_d1864 = Some (Load SZ8 true 5 5 964, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1868 : bv 32 := 0x00200313.
Lemma D_d1868 : decode_any W_d1868 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_d186c : bv 32 := 0x00700393.
Lemma D_d186c : decode_any W_d186c = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1870 : bv 32 := 0x6474ee37.
Lemma D_d1870 : decode_any W_d1870 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1874 : bv 32 := 0x551e0e1b.
Lemma D_d1874 : decode_any W_d1874 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1878 : bv 32 := 0x00078e93.
Lemma D_d1878 : decode_any W_d1878 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d187c : bv 32 := 0x0180006f.
Lemma D_d187c : decode_any W_d187c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1880 : bv 32 := 0x010eb603.
Lemma D_d1880 : decode_any W_d1880 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1884 : bv 32 := 0x40c78633.
Lemma D_d1884 : decode_any W_d1884 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1888 : bv 32 := 0xfff68693.
Lemma D_d1888 : decode_any W_d1888 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_d188c : bv 32 := 0x00ae8eb3.
Lemma D_d188c : decode_any W_d188c = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1890 : bv 32 := 0x04068a63.
Lemma D_d1890 : decode_any W_d1890 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1894 : bv 32 := 0x000ea403.
Lemma D_d1894 : decode_any W_d1894 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1898 : bv 32 := 0xff0404e3.
Lemma D_d1898 : decode_any W_d1898 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_d189c : bv 32 := 0x00028a63.
Lemma D_d189c : decode_any W_d189c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18b0 : bv 32 := 0x000e8f93.
Lemma D_d18b0 : decode_any W_d18b0 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18b4 : bv 32 := 0x00740463.
Lemma D_d18b4 : decode_any W_d18b4 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18b8 : bv 32 := 0x00088f93.
Lemma D_d18b8 : decode_any W_d18b8 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18bc : bv 32 := 0x03c41063.
Lemma D_d18bc : decode_any W_d18bc = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18c0 : bv 32 := 0x028eb883.
Lemma D_d18c0 : decode_any W_d18c0 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18c4 : bv 32 := 0x011f7c63.
Lemma D_d18c4 : decode_any W_d18c4 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18dc : bv 32 := 0x000f8893.
Lemma D_d18dc : decode_any W_d18dc = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18e0 : bv 32 := 0xfa9ff06f.
Lemma D_d18e0 : decode_any W_d18e0 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_d18e4 : bv 32 := 0x02088c63.
Lemma D_d18e4 : decode_any W_d18e4 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d191c : bv 32 := 0x0105b603.
Lemma D_d191c : decode_any W_d191c = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1920 : bv 32 := 0x0205b683.
Lemma D_d1920 : decode_any W_d1920 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1924 : bv 32 := 0x0285b503.
Lemma D_d1924 : decode_any W_d1924 = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1928 : bv 32 := 0x00c68733.
Lemma D_d1928 : decode_any W_d1928 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d192c : bv 32 := 0xfff50793.
Lemma D_d192c : decode_any W_d192c = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1930 : bv 32 := 0x40e00733.
Lemma D_d1930 : decode_any W_d1930 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1934 : bv 32 := 0x00c7f633.
Lemma D_d1934 : decode_any W_d1934 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1938 : bv 32 := 0x00e7f733.
Lemma D_d1938 : decode_any W_d1938 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d193c : bv 32 := 0x00700793.
Lemma D_d193c : decode_any W_d193c = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1940 : bv 32 := 0x00d706b3.
Lemma D_d1940 : decode_any W_d1940 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1944 : bv 32 := 0x02d5b023.
Lemma D_d1944 : decode_any W_d1944 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1948 : bv 32 := 0x02c5b823.
Lemma D_d1948 : decode_any W_d1948 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d194c : bv 32 := 0x00a7e663.
Lemma D_d194c : decode_any W_d194c = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1950 : bv 32 := 0x00800513.
Lemma D_d1950 : decode_any W_d1950 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1954 : bv 32 := 0x02a5b423.
Lemma D_d1954 : decode_any W_d1954 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1958 : bv 32 := 0x00d60633.
Lemma D_d1958 : decode_any W_d1958 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d195c : bv 32 := 0x000205b7.
Lemma D_d195c : decode_any W_d195c = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1960 : bv 32 := 0x00a60633.
Lemma D_d1960 : decode_any W_d1960 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1964 : bv 32 := 0x0d15869b.
Lemma D_d1964 : decode_any W_d1964 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1968 : bv 32 := 0x0df60593.
Lemma D_d1968 : decode_any W_d1968 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_d196c : bv 32 := 0xff85f593.
Lemma D_d196c : decode_any W_d196c = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1970 : bv 32 := 0x00b4bc23.
Lemma D_d1970 : decode_any W_d1970 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1974 : bv 32 := 0x02a4b023.
Lemma D_d1974 : decode_any W_d1974 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1978 : bv 32 := 0x02d5ea63.
Lemma D_d1978 : decode_any W_d1978 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19ac : bv 32 := 0x00031697.
Lemma D_d19ac : decode_any W_d19ac = Some (Auipc 13 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19b0 : bv 32 := 0x0104b983.
Lemma D_d19b0 : decode_any W_d19b0 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19b4 : bv 32 := 0x0284b603.
Lemma D_d19b4 : decode_any W_d19b4 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19b8 : bv 32 := 0xfff50713.
Lemma D_d19b8 : decode_any W_d19b8 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19bc : bv 32 := 0xf3800793.
Lemma D_d19bc : decode_any W_d19bc = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19c0 : bv 32 := 0x9a468513.
Lemma D_d19c0 : decode_any W_d19c0 = Some (OpImm ALU_ADD 10 13 2468, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19c4 : bv 32 := 0x40a787b3.
Lemma D_d19c4 : decode_any W_d19c4 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19c8 : bv 32 := 0x00f77733.
Lemma D_d19c8 : decode_any W_d19c8 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19cc : bv 32 := 0xfff64693.
Lemma D_d19cc : decode_any W_d19cc = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19d0 : bv 32 := 0x00e50933.
Lemma D_d19d0 : decode_any W_d19d0 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19d4 : bv 32 := 0x00369693.
Lemma D_d19d4 : decode_any W_d19d4 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19d8 : bv 32 := 0x00d506b3.
Lemma D_d19d8 : decode_any W_d19d8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19dc : bv 32 := 0x00b68a33.
Lemma D_d19dc : decode_any W_d19dc = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19e0 : bv 32 := 0x0c890413.
Lemma D_d19e0 : decode_any W_d19e0 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_d19e4 : bv 32 := 0x04098463.
Lemma D_d19e4 : decode_any W_d19e4 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a2c : bv 32 := 0x00ca3023.
Lemma D_d1a2c : decode_any W_d1a2c = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a30 : bv 32 := 0x0d493023.
Lemma D_d1a30 : decode_any W_d1a30 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a34 : bv 32 := 0x01293023.
Lemma D_d1a34 : decode_any W_d1a34 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a38 : bv 32 := 0x00040513.
Lemma D_d1a38 : decode_any W_d1a38 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a3c : bv 32 := 0x081130ef.
Lemma D_d1a3c : decode_any W_d1a3c = Some (Jal 1 80000, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a40 : bv 32 := 0x04054a63.
Lemma D_d1a40 : decode_any W_d1a40 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a44 : bv 32 := 0x00051663.
Lemma D_d1a44 : decode_any W_d1a44 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a48 : bv 32 := 0x00100513.
Lemma D_d1a48 : decode_any W_d1a48 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a4c : bv 32 := 0x00a48023.
Lemma D_d1a4c : decode_any W_d1a4c = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a50 : bv 32 := 0x00200513.
Lemma D_d1a50 : decode_any W_d1a50 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a54 : bv 32 := 0x00051597.
Lemma D_d1a54 : decode_any W_d1a54 = Some (Auipc 11 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a58 : bv 32 := 0x02a92423.
Lemma D_d1a58 : decode_any W_d1a58 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a5c : bv 32 := 0x06000893.
Lemma D_d1a5c : decode_any W_d1a5c = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a60 : bv 32 := 0x9cc58513.
Lemma D_d1a60 : decode_any W_d1a60 = Some (OpImm ALU_ADD 10 11 2508, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a64 : bv 32 := 0x03848593.
Lemma D_d1a64 : decode_any W_d1a64 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a68 : bv 32 := 0x00000073.

Lemma E_d1a68 : is_ecall W_d1a68 = true.
Proof. vm_refl. Qed.

Definition W_d1a6c : bv 32 := 0x07890613.
Lemma D_d1a6c : decode_any W_d1a6c = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a70 : bv 32 := 0x02a92023.
Lemma D_d1a70 : decode_any W_d1a70 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a74 : bv 32 := 0x08b93c23.
Lemma D_d1a74 : decode_any W_d1a74 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a78 : bv 32 := 0x06c93c23.
Lemma D_d1a78 : decode_any W_d1a78 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a7c : bv 32 := 0x00051517.
Lemma D_d1a7c : decode_any W_d1a7c = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a80 : bv 32 := 0xc1453503.
Lemma D_d1a80 : decode_any W_d1a80 = Some (Load SZ8 true 10 10 3092, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a84 : bv 32 := 0x01293423.
Lemma D_d1a84 : decode_any W_d1a84 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a88 : bv 32 := 0x01293823.
Lemma D_d1a88 : decode_any W_d1a88 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a8c : bv 32 := 0x00a93c23.
Lemma D_d1a8c : decode_any W_d1a8c = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a90 : bv 32 := 0x0080006f.
Lemma D_d1a90 : decode_any W_d1a90 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a98 : bv 32 := 0x03813083.
Lemma D_d1a98 : decode_any W_d1a98 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1a9c : bv 32 := 0x03013403.
Lemma D_d1a9c : decode_any W_d1a9c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1aa0 : bv 32 := 0x02813483.
Lemma D_d1aa0 : decode_any W_d1aa0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1aa4 : bv 32 := 0x02013903.
Lemma D_d1aa4 : decode_any W_d1aa4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1aa8 : bv 32 := 0x01813983.
Lemma D_d1aa8 : decode_any W_d1aa8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1aac : bv 32 := 0x01013a03.
Lemma D_d1aac : decode_any W_d1aac = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1ab0 : bv 32 := 0x00813a83.
Lemma D_d1ab0 : decode_any W_d1ab0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1ab4 : bv 32 := 0x04010113.
Lemma D_d1ab4 : decode_any W_d1ab4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1ab8 : bv 32 := 0x00008067.
Lemma D_d1ab8 : decode_any W_d1ab8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f78 : bv 32 := 0xff010113.
Lemma D_d1f78 : decode_any W_d1f78 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f7c : bv 32 := 0x00113423.
Lemma D_d1f7c : decode_any W_d1f7c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f80 : bv 32 := 0x00050e63.
Lemma D_d1f80 : decode_any W_d1f80 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f84 : bv 32 := 0x00050593.
Lemma D_d1f84 : decode_any W_d1f84 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f88 : bv 32 := 0x0001d517.
Lemma D_d1f88 : decode_any W_d1f88 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f8c : bv 32 := 0xe5453503.
Lemma D_d1f8c : decode_any W_d1f8c = Some (Load SZ8 true 10 10 3668, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f90 : bv 32 := 0x00800613.
Lemma D_d1f90 : decode_any W_d1f90 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f94 : bv 32 := 0x3d5100ef.
Lemma D_d1f94 : decode_any W_d1f94 = Some (Jal 1 68564, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1f98 : bv 32 := 0x01c0006f.
Lemma D_d1f98 : decode_any W_d1f98 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fb4 : bv 32 := 0x0001d517.
Lemma D_d1fb4 : decode_any W_d1fb4 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fb8 : bv 32 := 0xe2853503.
Lemma D_d1fb8 : decode_any W_d1fb8 = Some (Load SZ8 true 10 10 3624, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fbc : bv 32 := 0x000500a3.
Lemma D_d1fbc : decode_any W_d1fbc = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fc0 : bv 32 := 0x00053503.
Lemma D_d1fc0 : decode_any W_d1fc0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fc4 : bv 32 := 0x00020593.
Lemma D_d1fc4 : decode_any W_d1fc4 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fc8 : bv 32 := 0xfea5b823.
Lemma D_d1fc8 : decode_any W_d1fc8 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fcc : bv 32 := 0x00813083.
Lemma D_d1fcc : decode_any W_d1fcc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fd0 : bv 32 := 0x01010113.
Lemma D_d1fd0 : decode_any W_d1fd0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fd4 : bv 32 := 0x00008067.
Lemma D_d1fd4 : decode_any W_d1fd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b68 : bv 32 := 0x0035f693.
Lemma D_e2b68 : decode_any W_e2b68 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b6c : bv 32 := 0x10068863.
Lemma D_e2b6c : decode_any W_e2b6c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2c7c : bv 32 := 0x00050693.
Lemma D_e2c7c : decode_any W_e2c7c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2c80 : bv 32 := 0x00357793.
Lemma D_e2c80 : decode_any W_e2c80 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2c84 : bv 32 := 0xf2079ae3.
Lemma D_e2c84 : decode_any W_e2c84 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2c88 : bv 32 := 0x01000713.
Lemma D_e2c88 : decode_any W_e2c88 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2c8c : bv 32 := 0x02e66c63.
Lemma D_e2c8c : decode_any W_e2c8c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2cc4 : bv 32 := 0x00800713.
Lemma D_e2cc4 : decode_any W_e2cc4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2cc8 : bv 32 := 0x00e66e63.
Lemma D_e2cc8 : decode_any W_e2cc8 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ccc : bv 32 := 0x0005a703.
Lemma D_e2ccc : decode_any W_e2ccc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2cd0 : bv 32 := 0x0045a783.
Lemma D_e2cd0 : decode_any W_e2cd0 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2cd4 : bv 32 := 0x00e6a023.
Lemma D_e2cd4 : decode_any W_e2cd4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2cd8 : bv 32 := 0x00f6a223.
Lemma D_e2cd8 : decode_any W_e2cd8 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2cdc : bv 32 := 0x00868693.
Lemma D_e2cdc : decode_any W_e2cdc = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ce0 : bv 32 := 0x00858593.
Lemma D_e2ce0 : decode_any W_e2ce0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ce4 : bv 32 := 0x00467713.
Lemma D_e2ce4 : decode_any W_e2ce4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ce8 : bv 32 := 0x24070063.
Lemma D_e2ce8 : decode_any W_e2ce8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f28 : bv 32 := 0x00267713.
Lemma D_e2f28 : decode_any W_e2f28 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f2c : bv 32 := 0x00071863.
Lemma D_e2f2c : decode_any W_e2f2c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f30 : bv 32 := 0x00167613.
Lemma D_e2f30 : decode_any W_e2f30 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f34 : bv 32 := 0x02061663.
Lemma D_e2f34 : decode_any W_e2f34 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2f38 : bv 32 := 0x00008067.
Lemma D_e2f38 : decode_any W_e2f38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e30e8 : bv 32 := 0x0e060a63.
Lemma D_e30e8 : decode_any W_e30e8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_e30ec : bv 32 := 0x00b50023.
Lemma D_e30ec : decode_any W_e30ec = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e30f0 : bv 32 := 0x00c506b3.
Lemma D_e30f0 : decode_any W_e30f0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e30f4 : bv 32 := 0x00300713.
Lemma D_e30f4 : decode_any W_e30f4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e30f8 : bv 32 := 0xfeb68fa3.
Lemma D_e30f8 : decode_any W_e30f8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e30fc : bv 32 := 0x0ee66063.
Lemma D_e30fc : decode_any W_e30fc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3100 : bv 32 := 0x00b500a3.
Lemma D_e3100 : decode_any W_e3100 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3104 : bv 32 := 0x00b50123.
Lemma D_e3104 : decode_any W_e3104 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3108 : bv 32 := 0x00700713.
Lemma D_e3108 : decode_any W_e3108 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e310c : bv 32 := 0xfeb68ea3.
Lemma D_e310c : decode_any W_e310c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3110 : bv 32 := 0xfeb68f23.
Lemma D_e3110 : decode_any W_e3110 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3114 : bv 32 := 0x0ce66463.
Lemma D_e3114 : decode_any W_e3114 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3118 : bv 32 := 0x00b501a3.
Lemma D_e3118 : decode_any W_e3118 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e311c : bv 32 := 0x00900793.
Lemma D_e311c : decode_any W_e311c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3120 : bv 32 := 0xfeb68e23.
Lemma D_e3120 : decode_any W_e3120 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3124 : bv 32 := 0x0af66c63.
Lemma D_e3124 : decode_any W_e3124 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3128 : bv 32 := 0x40a006bb.
Lemma D_e3128 : decode_any W_e3128 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_e312c : bv 32 := 0x03859813.
Lemma D_e312c : decode_any W_e312c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3130 : bv 32 := 0x101015b7.
Lemma D_e3130 : decode_any W_e3130 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3134 : bv 32 := 0x0036f693.
Lemma D_e3134 : decode_any W_e3134 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3138 : bv 32 := 0x00459713.
Lemma D_e3138 : decode_any W_e3138 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e313c : bv 32 := 0x40d60633.
Lemma D_e313c : decode_any W_e313c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3140 : bv 32 := 0x00d505b3.
Lemma D_e3140 : decode_any W_e3140 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3144 : bv 32 := 0x10070693.
Lemma D_e3144 : decode_any W_e3144 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3148 : bv 32 := 0xffc67713.
Lemma D_e3148 : decode_any W_e3148 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_e314c : bv 32 := 0x02d83633.
Lemma D_e314c : decode_any W_e314c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3150 : bv 32 := 0x00c5a023.
Lemma D_e3150 : decode_any W_e3150 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3154 : bv 32 := 0x00e586b3.
Lemma D_e3154 : decode_any W_e3154 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3158 : bv 32 := 0xfec6ae23.
Lemma D_e3158 : decode_any W_e3158 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_e315c : bv 32 := 0x08f76063.
Lemma D_e315c : decode_any W_e315c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3160 : bv 32 := 0x00c5a223.
Lemma D_e3160 : decode_any W_e3160 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3164 : bv 32 := 0x00c5a423.
Lemma D_e3164 : decode_any W_e3164 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3168 : bv 32 := 0x01900793.
Lemma D_e3168 : decode_any W_e3168 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_e316c : bv 32 := 0xfec6aa23.
Lemma D_e316c : decode_any W_e316c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3170 : bv 32 := 0xfec6ac23.
Lemma D_e3170 : decode_any W_e3170 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3174 : bv 32 := 0x06f76463.
Lemma D_e3174 : decode_any W_e3174 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3178 : bv 32 := 0x00c5a623.
Lemma D_e3178 : decode_any W_e3178 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e317c : bv 32 := 0x00c5a823.
Lemma D_e317c : decode_any W_e317c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3180 : bv 32 := 0x00c5aa23.
Lemma D_e3180 : decode_any W_e3180 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3184 : bv 32 := 0x00c5ac23.
Lemma D_e3184 : decode_any W_e3184 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3188 : bv 32 := 0x0045f793.
Lemma D_e3188 : decode_any W_e3188 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e318c : bv 32 := 0x02000813.
Lemma D_e318c : decode_any W_e318c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3190 : bv 32 := 0x01878793.
Lemma D_e3190 : decode_any W_e3190 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3194 : bv 32 := 0x40f70733.
Lemma D_e3194 : decode_any W_e3194 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3198 : bv 32 := 0xfec6a223.
Lemma D_e3198 : decode_any W_e3198 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_e319c : bv 32 := 0xfec6a423.
Lemma D_e319c : decode_any W_e319c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31a0 : bv 32 := 0xfec6a623.
Lemma D_e31a0 : decode_any W_e31a0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31a4 : bv 32 := 0xfec6a823.
Lemma D_e31a4 : decode_any W_e31a4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31a8 : bv 32 := 0x03076a63.
Lemma D_e31a8 : decode_any W_e31a8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31ac : bv 32 := 0x02061613.
Lemma D_e31ac : decode_any W_e31ac = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31b0 : bv 32 := 0x00f585b3.
Lemma D_e31b0 : decode_any W_e31b0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31b4 : bv 32 := 0x02065693.
Lemma D_e31b4 : decode_any W_e31b4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31b8 : bv 32 := 0x00d66633.
Lemma D_e31b8 : decode_any W_e31b8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31bc : bv 32 := 0x01f00693.
Lemma D_e31bc : decode_any W_e31bc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31c0 : bv 32 := 0x00c5b023.
Lemma D_e31c0 : decode_any W_e31c0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31c4 : bv 32 := 0x00c5b423.
Lemma D_e31c4 : decode_any W_e31c4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31c8 : bv 32 := 0x00c5b823.
Lemma D_e31c8 : decode_any W_e31c8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31cc : bv 32 := 0x00c5bc23.
Lemma D_e31cc : decode_any W_e31cc = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31d0 : bv 32 := 0xfe070713.
Lemma D_e31d0 : decode_any W_e31d0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31d4 : bv 32 := 0x02058593.
Lemma D_e31d4 : decode_any W_e31d4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31d8 : bv 32 := 0xfee6e4e3.
Lemma D_e31d8 : decode_any W_e31d8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_e31dc : bv 32 := 0x00008067.
Lemma D_e31dc : decode_any W_e31dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5288 : bv 32 := 0x00050213.
Lemma D_e5288 : decode_any W_e5288 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e528c : bv 32 := 0x00000513.
Lemma D_e528c : decode_any W_e528c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5290 : bv 32 := 0x00008067.
Lemma D_e5290 : decode_any W_e5290 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition code_tbl : list (word * bv 32) := [
  (0x656f0, W_656b0);
  (0x656f4, W_656b4);
  (0x656f8, W_656b8);
  (0x656fc, W_656bc);
  (0x65700, W_656c0);
  (0x65704, W_656c4);
  (0x65708, W_656c8);
  (0x6570c, W_656cc);
  (0x65710, W_656d0);
  (0x65714, W_656d4);
  (0x65718, W_656d8);
  (0x6571c, W_656dc);
  (0x65720, W_656e0);
  (0x65724, W_656e4);
  (0x65728, W_656e8);
  (0x6572c, W_656ec);
  (0x65730, W_656f0);
  (0x65734, W_656f4);
  (0xd14e8, W_d14a8);
  (0xd14ec, W_d14ac);
  (0xd14f0, W_d14b0);
  (0xd14f4, W_d14b4);
  (0xd14f8, W_d14b8);
  (0xd14fc, W_d14bc);
  (0xd1500, W_d14c0);
  (0xd1504, W_d14c4);
  (0xd1508, W_d14c8);
  (0xd150c, W_d14cc);
  (0xd1510, W_d14d0);
  (0xd1514, W_d14d4);
  (0xd1518, W_d14d8);
  (0xd151c, W_d14dc);
  (0xd1520, W_d14e0);
  (0xd1524, W_d14e4);
  (0xd1528, W_d14e8);
  (0xd152c, W_d14ec);
  (0xd1530, W_d14f0);
  (0xd1534, W_d14f4);
  (0xd1538, W_d14f8);
  (0xd153c, W_d14fc);
  (0xd1540, W_d1500);
  (0xd1544, W_d1504);
  (0xd1548, W_d1508);
  (0xd154c, W_d150c);
  (0xd1550, W_d1510);
  (0xd1554, W_d1514);
  (0xd1558, W_d1518);
  (0xd155c, W_d151c);
  (0xd1560, W_d1520);
  (0xd1564, W_d1524);
  (0xd1568, W_d1528);
  (0xd156c, W_d152c);
  (0xd1570, W_d1530);
  (0xd1574, W_d1534);
  (0xd1578, W_d1538);
  (0xd157c, W_d153c);
  (0xd1580, W_d1540);
  (0xd1584, W_d1544);
  (0xd1588, W_d1548);
  (0xd15a0, W_d1560);
  (0xd15a4, W_d1564);
  (0xd15a8, W_d1568);
  (0xd15b0, W_d1570);
  (0xd15bc, W_d157c);
  (0xd15c0, W_d1580);
  (0xd15c4, W_d1584);
  (0xd15c8, W_d1588);
  (0xd15cc, W_d158c);
  (0xd15d0, W_d1590);
  (0xd15d4, W_d1594);
  (0xd15d8, W_d1598);
  (0xd15dc, W_d159c);
  (0xd15e0, W_d15a0);
  (0xd15e4, W_d15a4);
  (0xd15e8, W_d15a8);
  (0xd15ec, W_d15ac);
  (0xd15f0, W_d15b0);
  (0xd15f4, W_d15b4);
  (0xd15f8, W_d15b8);
  (0xd15fc, W_d15bc);
  (0xd1600, W_d15c0);
  (0xd1604, W_d15c4);
  (0xd1608, W_d15c8);
  (0xd160c, W_d15cc);
  (0xd1610, W_d15d0);
  (0xd1614, W_d15d4);
  (0xd1618, W_d15d8);
  (0xd161c, W_d15dc);
  (0xd1620, W_d15e0);
  (0xd1700, W_d16c0);
  (0xd1704, W_d16c4);
  (0xd1708, W_d16c8);
  (0xd170c, W_d16cc);
  (0xd1710, W_d16d0);
  (0xd1714, W_d16d4);
  (0xd1718, W_d16d8);
  (0xd171c, W_d16dc);
  (0xd1720, W_d16e0);
  (0xd1724, W_d16e4);
  (0xd1728, W_d16e8);
  (0xd172c, W_d16ec);
  (0xd1730, W_d16f0);
  (0xd1734, W_d16f4);
  (0xd1738, W_d16f8);
  (0xd173c, W_d16fc);
  (0xd1740, W_d1700);
  (0xd1744, W_d1704);
  (0xd1748, W_d1708);
  (0xd174c, W_d170c);
  (0xd1750, W_d1710);
  (0xd1754, W_d1714);
  (0xd1758, W_d1718);
  (0xd175c, W_d171c);
  (0xd1760, W_d1720);
  (0xd1764, W_d1724);
  (0xd1768, W_d1728);
  (0xd176c, W_d172c);
  (0xd1770, W_d1730);
  (0xd1774, W_d1734);
  (0xd1778, W_d1738);
  (0xd177c, W_d173c);
  (0xd1780, W_d1740);
  (0xd1784, W_d1744);
  (0xd1788, W_d1748);
  (0xd178c, W_d174c);
  (0xd1790, W_d1750);
  (0xd1794, W_d1754);
  (0xd1798, W_d1758);
  (0xd179c, W_d175c);
  (0xd17a0, W_d1760);
  (0xd17a4, W_d1764);
  (0xd17a8, W_d1768);
  (0xd17ac, W_d176c);
  (0xd17b0, W_d1770);
  (0xd17b4, W_d1774);
  (0xd17b8, W_d1778);
  (0xd17bc, W_d177c);
  (0xd17c0, W_d1780);
  (0xd17c4, W_d1784);
  (0xd17c8, W_d1788);
  (0xd17cc, W_d178c);
  (0xd17d0, W_d1790);
  (0xd17d4, W_d1794);
  (0xd17d8, W_d1798);
  (0xd17dc, W_d179c);
  (0xd17e0, W_d17a0);
  (0xd17e4, W_d17a4);
  (0xd17e8, W_d17a8);
  (0xd17ec, W_d17ac);
  (0xd17f0, W_d17b0);
  (0xd17f4, W_d17b4);
  (0xd17f8, W_d17b8);
  (0xd17fc, W_d17bc);
  (0xd1800, W_d17c0);
  (0xd1804, W_d17c4);
  (0xd180c, W_d180c);
  (0xd1810, W_d1810);
  (0xd1814, W_d1814);
  (0xd1818, W_d1818);
  (0xd181c, W_d181c);
  (0xd1820, W_d1820);
  (0xd1824, W_d1824);
  (0xd1828, W_d1828);
  (0xd182c, W_d182c);
  (0xd1830, W_d1830);
  (0xd1834, W_d1834);
  (0xd1838, W_d1838);
  (0xd183c, W_d183c);
  (0xd1840, W_d1840);
  (0xd1844, W_d1844);
  (0xd1848, W_d1848);
  (0xd184c, W_d184c);
  (0xd1850, W_d1850);
  (0xd1854, W_d1854);
  (0xd1858, W_d1858);
  (0xd185c, W_d185c);
  (0xd1860, W_d1860);
  (0xd1864, W_d1864);
  (0xd1868, W_d1868);
  (0xd186c, W_d186c);
  (0xd1870, W_d1870);
  (0xd1874, W_d1874);
  (0xd1878, W_d1878);
  (0xd187c, W_d187c);
  (0xd1880, W_d1880);
  (0xd1884, W_d1884);
  (0xd1888, W_d1888);
  (0xd188c, W_d188c);
  (0xd1890, W_d1890);
  (0xd1894, W_d1894);
  (0xd1898, W_d1898);
  (0xd189c, W_d189c);
  (0xd18b0, W_d18b0);
  (0xd18b4, W_d18b4);
  (0xd18b8, W_d18b8);
  (0xd18bc, W_d18bc);
  (0xd18c0, W_d18c0);
  (0xd18c4, W_d18c4);
  (0xd18dc, W_d18dc);
  (0xd18e0, W_d18e0);
  (0xd18e4, W_d18e4);
  (0xd191c, W_d191c);
  (0xd1920, W_d1920);
  (0xd1924, W_d1924);
  (0xd1928, W_d1928);
  (0xd192c, W_d192c);
  (0xd1930, W_d1930);
  (0xd1934, W_d1934);
  (0xd1938, W_d1938);
  (0xd193c, W_d193c);
  (0xd1940, W_d1940);
  (0xd1944, W_d1944);
  (0xd1948, W_d1948);
  (0xd194c, W_d194c);
  (0xd1950, W_d1950);
  (0xd1954, W_d1954);
  (0xd1958, W_d1958);
  (0xd195c, W_d195c);
  (0xd1960, W_d1960);
  (0xd1964, W_d1964);
  (0xd1968, W_d1968);
  (0xd196c, W_d196c);
  (0xd1970, W_d1970);
  (0xd1974, W_d1974);
  (0xd1978, W_d1978);
  (0xd19ac, W_d19ac);
  (0xd19b0, W_d19b0);
  (0xd19b4, W_d19b4);
  (0xd19b8, W_d19b8);
  (0xd19bc, W_d19bc);
  (0xd19c0, W_d19c0);
  (0xd19c4, W_d19c4);
  (0xd19c8, W_d19c8);
  (0xd19cc, W_d19cc);
  (0xd19d0, W_d19d0);
  (0xd19d4, W_d19d4);
  (0xd19d8, W_d19d8);
  (0xd19dc, W_d19dc);
  (0xd19e0, W_d19e0);
  (0xd19e4, W_d19e4);
  (0xd1a2c, W_d1a2c);
  (0xd1a30, W_d1a30);
  (0xd1a34, W_d1a34);
  (0xd1a38, W_d1a38);
  (0xd1a3c, W_d1a3c);
  (0xd1a40, W_d1a40);
  (0xd1a44, W_d1a44);
  (0xd1a48, W_d1a48);
  (0xd1a4c, W_d1a4c);
  (0xd1a50, W_d1a50);
  (0xd1a54, W_d1a54);
  (0xd1a58, W_d1a58);
  (0xd1a5c, W_d1a5c);
  (0xd1a60, W_d1a60);
  (0xd1a64, W_d1a64);
  (0xd1a68, W_d1a68);
  (0xd1a6c, W_d1a6c);
  (0xd1a70, W_d1a70);
  (0xd1a74, W_d1a74);
  (0xd1a78, W_d1a78);
  (0xd1a7c, W_d1a7c);
  (0xd1a80, W_d1a80);
  (0xd1a84, W_d1a84);
  (0xd1a88, W_d1a88);
  (0xd1a8c, W_d1a8c);
  (0xd1a90, W_d1a90);
  (0xd1a98, W_d1a98);
  (0xd1a9c, W_d1a9c);
  (0xd1aa0, W_d1aa0);
  (0xd1aa4, W_d1aa4);
  (0xd1aa8, W_d1aa8);
  (0xd1aac, W_d1aac);
  (0xd1ab0, W_d1ab0);
  (0xd1ab4, W_d1ab4);
  (0xd1ab8, W_d1ab8);
  (0xd1fac, W_d1f78);
  (0xd1fb0, W_d1f7c);
  (0xd1fb4, W_d1f80);
  (0xd1fb8, W_d1f84);
  (0xd1fbc, W_d1f88);
  (0xd1fc0, W_d1f8c);
  (0xd1fc4, W_d1f90);
  (0xd1fc8, W_d1f94);
  (0xd1fcc, W_d1f98);
  (0xd1fe8, W_d1fb4);
  (0xd1fec, W_d1fb8);
  (0xd1ff0, W_d1fbc);
  (0xd1ff4, W_d1fc0);
  (0xd1ff8, W_d1fc4);
  (0xd1ffc, W_d1fc8);
  (0xd2000, W_d1fcc);
  (0xd2004, W_d1fd0);
  (0xd2008, W_d1fd4);
  (0xe2b9c, W_e2b68);
  (0xe2ba0, W_e2b6c);
  (0xe2cb0, W_e2c7c);
  (0xe2cb4, W_e2c80);
  (0xe2cb8, W_e2c84);
  (0xe2cbc, W_e2c88);
  (0xe2cc0, W_e2c8c);
  (0xe2cf8, W_e2cc4);
  (0xe2cfc, W_e2cc8);
  (0xe2d00, W_e2ccc);
  (0xe2d04, W_e2cd0);
  (0xe2d08, W_e2cd4);
  (0xe2d0c, W_e2cd8);
  (0xe2d10, W_e2cdc);
  (0xe2d14, W_e2ce0);
  (0xe2d18, W_e2ce4);
  (0xe2d1c, W_e2ce8);
  (0xe2f5c, W_e2f28);
  (0xe2f60, W_e2f2c);
  (0xe2f64, W_e2f30);
  (0xe2f68, W_e2f34);
  (0xe2f6c, W_e2f38);
  (0xe311c, W_e30e8);
  (0xe3120, W_e30ec);
  (0xe3124, W_e30f0);
  (0xe3128, W_e30f4);
  (0xe312c, W_e30f8);
  (0xe3130, W_e30fc);
  (0xe3134, W_e3100);
  (0xe3138, W_e3104);
  (0xe313c, W_e3108);
  (0xe3140, W_e310c);
  (0xe3144, W_e3110);
  (0xe3148, W_e3114);
  (0xe314c, W_e3118);
  (0xe3150, W_e311c);
  (0xe3154, W_e3120);
  (0xe3158, W_e3124);
  (0xe315c, W_e3128);
  (0xe3160, W_e312c);
  (0xe3164, W_e3130);
  (0xe3168, W_e3134);
  (0xe316c, W_e3138);
  (0xe3170, W_e313c);
  (0xe3174, W_e3140);
  (0xe3178, W_e3144);
  (0xe317c, W_e3148);
  (0xe3180, W_e314c);
  (0xe3184, W_e3150);
  (0xe3188, W_e3154);
  (0xe318c, W_e3158);
  (0xe3190, W_e315c);
  (0xe3194, W_e3160);
  (0xe3198, W_e3164);
  (0xe319c, W_e3168);
  (0xe31a0, W_e316c);
  (0xe31a4, W_e3170);
  (0xe31a8, W_e3174);
  (0xe31ac, W_e3178);
  (0xe31b0, W_e317c);
  (0xe31b4, W_e3180);
  (0xe31b8, W_e3184);
  (0xe31bc, W_e3188);
  (0xe31c0, W_e318c);
  (0xe31c4, W_e3190);
  (0xe31c8, W_e3194);
  (0xe31cc, W_e3198);
  (0xe31d0, W_e319c);
  (0xe31d4, W_e31a0);
  (0xe31d8, W_e31a4);
  (0xe31dc, W_e31a8);
  (0xe31e0, W_e31ac);
  (0xe31e4, W_e31b0);
  (0xe31e8, W_e31b4);
  (0xe31ec, W_e31b8);
  (0xe31f0, W_e31bc);
  (0xe31f4, W_e31c0);
  (0xe31f8, W_e31c4);
  (0xe31fc, W_e31c8);
  (0xe3200, W_e31cc);
  (0xe3204, W_e31d0);
  (0xe3208, W_e31d4);
  (0xe320c, W_e31d8);
  (0xe3210, W_e31dc);
  (0xe52bc, W_e5288);
  (0xe52c0, W_e528c);
  (0xe52c4, W_e5290)
].

Definition img_tbl : list (word * nat * list byte) := [
  (Z_to_bv 64 65600, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 6));
  (Z_to_bv 64 65616, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 65600));
  (Z_to_bv 64 65656, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65712, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65768, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65824, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65880, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1685382482));
  (Z_to_bv 64 65936, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1685382480));
  (Z_to_bv 64 65992, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1685382481));
  (Z_to_bv 64 66032, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 66048, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 4));
  (Z_to_bv 64 66104, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1879048195));
  (Z_to_bv 64 977952, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 977960, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 415804));
  (Z_to_bv 64 977968, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 857320));
  (Z_to_bv 64 977976, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 859652));
  (Z_to_bv 64 978408, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1057608));
  (Z_to_bv 64 978416, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1189536));
  (Z_to_bv 64 978424, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1189528));
  (Z_to_bv 64 978432, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 953456));
  (Z_to_bv 64 978440, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 953440));
  (Z_to_bv 64 983512, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 131072));
  (Z_to_bv 64 1188912, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1188928, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1188936, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1189520, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1189560, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1189584, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 978448, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1189512));
  (Z_to_bv 64 953440, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 609812))
].

Definition fetch_is (segs : list Segment) (pc : word) (w : bv 32) : bool :=
  match fetch_word segs pc with Some w' => bv_eqb w' w | None => false end.

Definition code_ok (segs : list Segment) : bool :=
  forallb (fun e => fetch_is segs (fst e) (snd e)) code_tbl.

Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | b1 :: r1, b2 :: r2 => bv_eqb b1 b2 && bytes_eqb r1 r2
  | _, _ => false
  end.

Definition rdn_is (segs : list Segment) (a : word) (n : nat) (bs : list byte) : bool :=
  match rdn segs (fun _ => None) a n with Some bs' => bytes_eqb bs' bs | None => false end.

Definition img_ok (segs : list Segment) : bool :=
  forallb (fun e => match e with (a, n, bs) => rdn_is segs a n bs end) img_tbl.

Definition data_lo : Z := 0x1022b0.
Definition data_len : nat := 496%nat.

Definition data2_lo : Z := 0x122420.
Definition data2_len : nat := 784%nat.

Definition u1b_ok (segs : list Segment) : bool :=
  code_ok segs && img_ok segs && wseg_ok segs (Z_to_bv 64 data_lo) data_len
  && wseg_ok segs (Z_to_bv 64 data2_lo) data2_len.

Definition code_mem (pc : word) (w : bv 32) : bool :=
  existsb (fun e => bv_eqb (fst e) pc && bv_eqb (snd e) w) code_tbl.

Definition img_mem (a : word) (n : nat) (bs : list byte) : bool :=
  existsb (fun e => match e with (a', n', bs') => bv_eqb a' a && Nat.eqb n' n && bytes_eqb bs' bs end) img_tbl.

Lemma bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma bytes_eqb_eq : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|b1 r1 IH]; intros [|b2 r2] H; cbn [bytes_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. apply IH in H2. subst. reflexivity.
Qed.

Lemma code_sound : forall segs, u1b_ok segs = true ->
  forall pc w, code_mem pc w = true -> fetch_word segs pc = Some w.
Proof.
  intros segs H pc w Hm. unfold u1b_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  unfold code_ok in H. rewrite forallb_forall in H.
  unfold code_mem in Hm. apply existsb_exists in Hm as [[p x] [Hin Hx]].
  apply andb_prop in Hx as [Hp Hw]. apply bv_eqb_eq in Hp, Hw. cbn [fst snd] in *. subst p x.
  specialize (H _ Hin). cbn [fst snd] in H. unfold fetch_is in H.
  destruct (fetch_word segs pc) as [w'|]; [|discriminate]. apply bv_eqb_eq in H. subst. reflexivity.
Qed.

Lemma img_sound : forall segs, u1b_ok segs = true ->
  forall a n bs, img_mem a n bs = true -> rdn segs (fun _ => None) a n = Some bs.
Proof.
  intros segs H a n bs Hm. unfold u1b_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  unfold img_ok in H. rewrite forallb_forall in H.
  unfold img_mem in Hm. apply existsb_exists in Hm as [[[a' n'] bs'] [Hin Hx]].
  apply andb_prop in Hx as [Hx Hb]. apply andb_prop in Hx as [Ha Hn].
  apply bv_eqb_eq in Ha. apply Nat.eqb_eq in Hn. apply bytes_eqb_eq in Hb. subst a' n' bs'.
  specialize (H _ Hin). unfold rdn_is in H.
  destruct (rdn segs (fun _ => None) a n) as [bs'|]; [|discriminate]. apply bytes_eqb_eq in H. subst. reflexivity.
Qed.

Lemma wseg_data : forall segs, u1b_ok segs = true -> wseg_ok segs (Z_to_bv 64 data_lo) data_len = true.
Proof. intros segs H. unfold u1b_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma wseg_data2 : forall segs, u1b_ok segs = true -> wseg_ok segs (Z_to_bv 64 data2_lo) data2_len = true.
Proof. intros segs H. unfold u1b_ok in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma store_ok_data : forall segs m (a : Z) (n : nat), u1b_ok segs = true ->
  (0x1022b0 <= a)%Z -> (a + Z.of_nat n <= 0x1024a0)%Z ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros segs m a n H Hlo Hhi.
  assert (Ha : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    apply Z.mod_small. lia. }
  eapply (store_ok_window segs m (Z_to_bv 64 0x1022b0) (Z_to_bv 64 a) 496%nat n 0x1022b0 0x1024a0);
    [ reflexivity | reflexivity | lia | exact (wseg_data segs H) | rewrite Ha; lia | rewrite Ha; exact Hhi ].
Qed.

Lemma store_ok_data2 : forall segs m (a : Z) (n : nat), u1b_ok segs = true ->
  (0x122420 <= a)%Z -> (a + Z.of_nat n <= 0x122730)%Z ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros segs m a n H Hlo Hhi.
  assert (Ha : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    apply Z.mod_small. lia. }
  eapply (store_ok_window segs m (Z_to_bv 64 0x122420) (Z_to_bv 64 a) 784%nat n 0x122420 0x122730);
    [ reflexivity | reflexivity | lia | exact (wseg_data2 segs H) | rewrite Ha; lia | rewrite Ha; exact Hhi ].
Qed.

Ltac ok_dat HX := first [ apply (store_ok_data _ _ _ _ HX); lia | apply (store_ok_data2 _ _ _ _ HX); lia ].

Lemma F_656b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0x656f0 : word) = Some W_656b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0x656f4 : word) = Some W_656b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656b8 : forall segs, u1b_ok segs = true -> fetch_word segs (0x656f8 : word) = Some W_656b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656bc : forall segs, u1b_ok segs = true -> fetch_word segs (0x656fc : word) = Some W_656bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65700 : word) = Some W_656c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65704 : word) = Some W_656c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656c8 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65708 : word) = Some W_656c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656cc : forall segs, u1b_ok segs = true -> fetch_word segs (0x6570c : word) = Some W_656cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656d0 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65710 : word) = Some W_656d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656d4 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65714 : word) = Some W_656d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656d8 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65718 : word) = Some W_656d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656dc : forall segs, u1b_ok segs = true -> fetch_word segs (0x6571c : word) = Some W_656dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656e0 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65720 : word) = Some W_656e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656e4 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65724 : word) = Some W_656e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656e8 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65728 : word) = Some W_656e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656ec : forall segs, u1b_ok segs = true -> fetch_word segs (0x6572c : word) = Some W_656ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656f0 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65730 : word) = Some W_656f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_656f4 : forall segs, u1b_ok segs = true -> fetch_word segs (0x65734 : word) = Some W_656f4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14a8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd14e8 : word) = Some W_d14a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14ac : forall segs, u1b_ok segs = true -> fetch_word segs (0xd14ec : word) = Some W_d14ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd14f0 : word) = Some W_d14b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd14f4 : word) = Some W_d14b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14b8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd14f8 : word) = Some W_d14b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14bc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd14fc : word) = Some W_d14bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1500 : word) = Some W_d14c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1504 : word) = Some W_d14c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14c8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1508 : word) = Some W_d14c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14cc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd150c : word) = Some W_d14cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14d0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1510 : word) = Some W_d14d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14d4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1514 : word) = Some W_d14d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14d8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1518 : word) = Some W_d14d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14dc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd151c : word) = Some W_d14dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14e0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1520 : word) = Some W_d14e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14e4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1524 : word) = Some W_d14e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14e8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1528 : word) = Some W_d14e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14ec : forall segs, u1b_ok segs = true -> fetch_word segs (0xd152c : word) = Some W_d14ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14f0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1530 : word) = Some W_d14f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14f4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1534 : word) = Some W_d14f4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14f8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1538 : word) = Some W_d14f8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d14fc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd153c : word) = Some W_d14fc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1500 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1540 : word) = Some W_d1500.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1504 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1544 : word) = Some W_d1504.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1508 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1548 : word) = Some W_d1508.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d150c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd154c : word) = Some W_d150c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1510 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1550 : word) = Some W_d1510.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1514 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1554 : word) = Some W_d1514.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1518 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1558 : word) = Some W_d1518.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d151c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd155c : word) = Some W_d151c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1520 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1560 : word) = Some W_d1520.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1524 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1564 : word) = Some W_d1524.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1528 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1568 : word) = Some W_d1528.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d152c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd156c : word) = Some W_d152c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1530 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1570 : word) = Some W_d1530.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1534 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1574 : word) = Some W_d1534.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1538 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1578 : word) = Some W_d1538.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d153c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd157c : word) = Some W_d153c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1540 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1580 : word) = Some W_d1540.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1544 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1584 : word) = Some W_d1544.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1548 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1588 : word) = Some W_d1548.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1560 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15a0 : word) = Some W_d1560.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1564 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15a4 : word) = Some W_d1564.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1568 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15a8 : word) = Some W_d1568.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1570 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15b0 : word) = Some W_d1570.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d157c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15bc : word) = Some W_d157c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1580 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15c0 : word) = Some W_d1580.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1584 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15c4 : word) = Some W_d1584.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1588 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15c8 : word) = Some W_d1588.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d158c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15cc : word) = Some W_d158c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1590 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15d0 : word) = Some W_d1590.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1594 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15d4 : word) = Some W_d1594.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1598 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15d8 : word) = Some W_d1598.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d159c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15dc : word) = Some W_d159c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15a0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15e0 : word) = Some W_d15a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15a4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15e4 : word) = Some W_d15a4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15a8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15e8 : word) = Some W_d15a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15ac : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15ec : word) = Some W_d15ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15f0 : word) = Some W_d15b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15f4 : word) = Some W_d15b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15b8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15f8 : word) = Some W_d15b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15bc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd15fc : word) = Some W_d15bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1600 : word) = Some W_d15c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1604 : word) = Some W_d15c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15c8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1608 : word) = Some W_d15c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15cc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd160c : word) = Some W_d15cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15d0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1610 : word) = Some W_d15d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15d4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1614 : word) = Some W_d15d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15d8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1618 : word) = Some W_d15d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15dc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd161c : word) = Some W_d15dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d15e0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1620 : word) = Some W_d15e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1700 : word) = Some W_d16c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1704 : word) = Some W_d16c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16c8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1708 : word) = Some W_d16c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16cc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd170c : word) = Some W_d16cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16d0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1710 : word) = Some W_d16d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16d4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1714 : word) = Some W_d16d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16d8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1718 : word) = Some W_d16d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16dc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd171c : word) = Some W_d16dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16e0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1720 : word) = Some W_d16e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16e4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1724 : word) = Some W_d16e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16e8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1728 : word) = Some W_d16e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16ec : forall segs, u1b_ok segs = true -> fetch_word segs (0xd172c : word) = Some W_d16ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16f0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1730 : word) = Some W_d16f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16f4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1734 : word) = Some W_d16f4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16f8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1738 : word) = Some W_d16f8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d16fc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd173c : word) = Some W_d16fc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1700 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1740 : word) = Some W_d1700.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1704 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1744 : word) = Some W_d1704.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.

Lemma F_d1724 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1764 : word) = Some W_d1724.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1728 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1768 : word) = Some W_d1728.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d172c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd176c : word) = Some W_d172c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1730 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1770 : word) = Some W_d1730.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1734 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1774 : word) = Some W_d1734.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1738 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1778 : word) = Some W_d1738.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d173c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd177c : word) = Some W_d173c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1740 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1780 : word) = Some W_d1740.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1744 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1784 : word) = Some W_d1744.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1748 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1788 : word) = Some W_d1748.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d174c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd178c : word) = Some W_d174c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1750 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1790 : word) = Some W_d1750.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1754 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1794 : word) = Some W_d1754.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1758 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1798 : word) = Some W_d1758.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d175c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd179c : word) = Some W_d175c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1760 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17a0 : word) = Some W_d1760.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1764 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17a4 : word) = Some W_d1764.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1768 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17a8 : word) = Some W_d1768.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d176c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17ac : word) = Some W_d176c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1770 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17b0 : word) = Some W_d1770.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1774 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17b4 : word) = Some W_d1774.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1778 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17b8 : word) = Some W_d1778.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d177c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17bc : word) = Some W_d177c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1780 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17c0 : word) = Some W_d1780.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1784 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17c4 : word) = Some W_d1784.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1788 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17c8 : word) = Some W_d1788.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d178c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17cc : word) = Some W_d178c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1790 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17d0 : word) = Some W_d1790.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1794 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17d4 : word) = Some W_d1794.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1798 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17d8 : word) = Some W_d1798.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d179c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17dc : word) = Some W_d179c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d17a0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17e0 : word) = Some W_d17a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d17a4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17e4 : word) = Some W_d17a4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d17a8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17e8 : word) = Some W_d17a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d17ac : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17ec : word) = Some W_d17ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d17b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17f0 : word) = Some W_d17b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d17b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd17f4 : word) = Some W_d17b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.

Lemma F_d180c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd180c : word) = Some W_d180c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1810 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1810 : word) = Some W_d1810.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1814 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1814 : word) = Some W_d1814.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1818 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1818 : word) = Some W_d1818.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d181c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd181c : word) = Some W_d181c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1820 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1820 : word) = Some W_d1820.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1824 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1824 : word) = Some W_d1824.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1828 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1828 : word) = Some W_d1828.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d182c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd182c : word) = Some W_d182c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1830 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1830 : word) = Some W_d1830.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1834 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1834 : word) = Some W_d1834.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1838 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1838 : word) = Some W_d1838.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d183c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd183c : word) = Some W_d183c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1840 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1840 : word) = Some W_d1840.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1844 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1844 : word) = Some W_d1844.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1848 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1848 : word) = Some W_d1848.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d184c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd184c : word) = Some W_d184c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1850 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1850 : word) = Some W_d1850.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1854 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1854 : word) = Some W_d1854.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1858 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1858 : word) = Some W_d1858.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d185c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd185c : word) = Some W_d185c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1860 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1860 : word) = Some W_d1860.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1864 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1864 : word) = Some W_d1864.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1868 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1868 : word) = Some W_d1868.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d186c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd186c : word) = Some W_d186c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1870 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1870 : word) = Some W_d1870.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1874 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1874 : word) = Some W_d1874.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1878 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1878 : word) = Some W_d1878.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d187c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd187c : word) = Some W_d187c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1880 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1880 : word) = Some W_d1880.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1884 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1884 : word) = Some W_d1884.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1888 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1888 : word) = Some W_d1888.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d188c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd188c : word) = Some W_d188c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1890 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1890 : word) = Some W_d1890.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1894 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1894 : word) = Some W_d1894.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1898 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1898 : word) = Some W_d1898.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d189c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd189c : word) = Some W_d189c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18b0 : word) = Some W_d18b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18b4 : word) = Some W_d18b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18b8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18b8 : word) = Some W_d18b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18bc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18bc : word) = Some W_d18bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18c0 : word) = Some W_d18c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18c4 : word) = Some W_d18c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18dc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18dc : word) = Some W_d18dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18e0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18e0 : word) = Some W_d18e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d18e4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd18e4 : word) = Some W_d18e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d191c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd191c : word) = Some W_d191c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1920 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1920 : word) = Some W_d1920.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1924 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1924 : word) = Some W_d1924.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1928 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1928 : word) = Some W_d1928.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d192c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd192c : word) = Some W_d192c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1930 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1930 : word) = Some W_d1930.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1934 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1934 : word) = Some W_d1934.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1938 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1938 : word) = Some W_d1938.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d193c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd193c : word) = Some W_d193c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1940 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1940 : word) = Some W_d1940.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1944 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1944 : word) = Some W_d1944.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1948 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1948 : word) = Some W_d1948.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d194c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd194c : word) = Some W_d194c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1950 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1950 : word) = Some W_d1950.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1954 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1954 : word) = Some W_d1954.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1958 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1958 : word) = Some W_d1958.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d195c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd195c : word) = Some W_d195c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1960 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1960 : word) = Some W_d1960.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1964 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1964 : word) = Some W_d1964.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1968 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1968 : word) = Some W_d1968.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d196c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd196c : word) = Some W_d196c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1970 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1970 : word) = Some W_d1970.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1974 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1974 : word) = Some W_d1974.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1978 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1978 : word) = Some W_d1978.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19ac : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19ac : word) = Some W_d19ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19b0 : word) = Some W_d19b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19b4 : word) = Some W_d19b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19b8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19b8 : word) = Some W_d19b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19bc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19bc : word) = Some W_d19bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19c0 : word) = Some W_d19c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19c4 : word) = Some W_d19c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19c8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19c8 : word) = Some W_d19c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19cc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19cc : word) = Some W_d19cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19d0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19d0 : word) = Some W_d19d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19d4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19d4 : word) = Some W_d19d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19d8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19d8 : word) = Some W_d19d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19dc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19dc : word) = Some W_d19dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19e0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19e0 : word) = Some W_d19e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d19e4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd19e4 : word) = Some W_d19e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a2c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a2c : word) = Some W_d1a2c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a30 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a30 : word) = Some W_d1a30.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a34 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a34 : word) = Some W_d1a34.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a38 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a38 : word) = Some W_d1a38.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a3c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a3c : word) = Some W_d1a3c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a40 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a40 : word) = Some W_d1a40.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a44 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a44 : word) = Some W_d1a44.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a48 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a48 : word) = Some W_d1a48.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a4c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a4c : word) = Some W_d1a4c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a50 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a50 : word) = Some W_d1a50.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a54 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a54 : word) = Some W_d1a54.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a58 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a58 : word) = Some W_d1a58.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a5c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a5c : word) = Some W_d1a5c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a60 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a60 : word) = Some W_d1a60.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a64 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a64 : word) = Some W_d1a64.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a68 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a68 : word) = Some W_d1a68.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a6c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a6c : word) = Some W_d1a6c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a70 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a70 : word) = Some W_d1a70.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a74 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a74 : word) = Some W_d1a74.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a78 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a78 : word) = Some W_d1a78.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a7c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a7c : word) = Some W_d1a7c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a80 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a80 : word) = Some W_d1a80.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a84 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a84 : word) = Some W_d1a84.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a88 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a88 : word) = Some W_d1a88.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a8c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a8c : word) = Some W_d1a8c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a90 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a90 : word) = Some W_d1a90.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a98 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a98 : word) = Some W_d1a98.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1a9c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1a9c : word) = Some W_d1a9c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1aa0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1aa0 : word) = Some W_d1aa0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1aa4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1aa4 : word) = Some W_d1aa4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1aa8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1aa8 : word) = Some W_d1aa8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1aac : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1aac : word) = Some W_d1aac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1ab0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ab0 : word) = Some W_d1ab0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1ab4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ab4 : word) = Some W_d1ab4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1ab8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ab8 : word) = Some W_d1ab8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f78 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fac : word) = Some W_d1f78.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f7c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fb0 : word) = Some W_d1f7c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f80 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fb4 : word) = Some W_d1f80.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f84 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fb8 : word) = Some W_d1f84.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f88 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fbc : word) = Some W_d1f88.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f8c : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fc0 : word) = Some W_d1f8c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f90 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fc4 : word) = Some W_d1f90.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f94 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fc8 : word) = Some W_d1f94.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1f98 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fcc : word) = Some W_d1f98.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fb4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fe8 : word) = Some W_d1fb4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fb8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1fec : word) = Some W_d1fb8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fbc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ff0 : word) = Some W_d1fbc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fc0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ff4 : word) = Some W_d1fc0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fc4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ff8 : word) = Some W_d1fc4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fc8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd1ffc : word) = Some W_d1fc8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fcc : forall segs, u1b_ok segs = true -> fetch_word segs (0xd2000 : word) = Some W_d1fcc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fd0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd2004 : word) = Some W_d1fd0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d1fd4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xd2008 : word) = Some W_d1fd4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2b68 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2b9c : word) = Some W_e2b68.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2b6c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2ba0 : word) = Some W_e2b6c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2c7c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cb0 : word) = Some W_e2c7c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2c80 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cb4 : word) = Some W_e2c80.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2c84 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cb8 : word) = Some W_e2c84.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2c88 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cbc : word) = Some W_e2c88.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2c8c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cc0 : word) = Some W_e2c8c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2cc4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cf8 : word) = Some W_e2cc4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2cc8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2cfc : word) = Some W_e2cc8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2ccc : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d00 : word) = Some W_e2ccc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2cd0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d04 : word) = Some W_e2cd0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2cd4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d08 : word) = Some W_e2cd4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2cd8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d0c : word) = Some W_e2cd8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2cdc : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d10 : word) = Some W_e2cdc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2ce0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d14 : word) = Some W_e2ce0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2ce4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d18 : word) = Some W_e2ce4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2ce8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2d1c : word) = Some W_e2ce8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2f28 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2f5c : word) = Some W_e2f28.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2f2c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2f60 : word) = Some W_e2f2c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2f30 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2f64 : word) = Some W_e2f30.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2f34 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2f68 : word) = Some W_e2f34.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e2f38 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe2f6c : word) = Some W_e2f38.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e30e8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe311c : word) = Some W_e30e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e30ec : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3120 : word) = Some W_e30ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e30f0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3124 : word) = Some W_e30f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e30f4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3128 : word) = Some W_e30f4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e30f8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe312c : word) = Some W_e30f8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e30fc : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3130 : word) = Some W_e30fc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3100 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3134 : word) = Some W_e3100.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3104 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3138 : word) = Some W_e3104.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3108 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe313c : word) = Some W_e3108.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e310c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3140 : word) = Some W_e310c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3110 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3144 : word) = Some W_e3110.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3114 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3148 : word) = Some W_e3114.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3118 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe314c : word) = Some W_e3118.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e311c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3150 : word) = Some W_e311c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3120 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3154 : word) = Some W_e3120.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3124 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3158 : word) = Some W_e3124.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3128 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe315c : word) = Some W_e3128.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e312c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3160 : word) = Some W_e312c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3130 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3164 : word) = Some W_e3130.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3134 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3168 : word) = Some W_e3134.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3138 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe316c : word) = Some W_e3138.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e313c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3170 : word) = Some W_e313c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3140 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3174 : word) = Some W_e3140.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3144 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3178 : word) = Some W_e3144.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3148 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe317c : word) = Some W_e3148.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e314c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3180 : word) = Some W_e314c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3150 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3184 : word) = Some W_e3150.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3154 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3188 : word) = Some W_e3154.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3158 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe318c : word) = Some W_e3158.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e315c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3190 : word) = Some W_e315c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3160 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3194 : word) = Some W_e3160.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3164 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3198 : word) = Some W_e3164.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3168 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe319c : word) = Some W_e3168.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e316c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31a0 : word) = Some W_e316c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3170 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31a4 : word) = Some W_e3170.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3174 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31a8 : word) = Some W_e3174.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3178 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31ac : word) = Some W_e3178.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e317c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31b0 : word) = Some W_e317c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3180 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31b4 : word) = Some W_e3180.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3184 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31b8 : word) = Some W_e3184.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3188 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31bc : word) = Some W_e3188.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e318c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31c0 : word) = Some W_e318c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3190 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31c4 : word) = Some W_e3190.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3194 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31c8 : word) = Some W_e3194.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3198 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31cc : word) = Some W_e3198.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e319c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31d0 : word) = Some W_e319c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31a0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31d4 : word) = Some W_e31a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31a4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31d8 : word) = Some W_e31a4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31a8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31dc : word) = Some W_e31a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31ac : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31e0 : word) = Some W_e31ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31b0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31e4 : word) = Some W_e31b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31b4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31e8 : word) = Some W_e31b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31b8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31ec : word) = Some W_e31b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31bc : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31f0 : word) = Some W_e31bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31c0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31f4 : word) = Some W_e31c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31c4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31f8 : word) = Some W_e31c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31c8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe31fc : word) = Some W_e31c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31cc : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3200 : word) = Some W_e31cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31d0 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3204 : word) = Some W_e31d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31d4 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3208 : word) = Some W_e31d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31d8 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe320c : word) = Some W_e31d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e31dc : forall segs, u1b_ok segs = true -> fetch_word segs (0xe3210 : word) = Some W_e31dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e5288 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe52bc : word) = Some W_e5288.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e528c : forall segs, u1b_ok segs = true -> fetch_word segs (0xe52c0 : word) = Some W_e528c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e5290 : forall segs, u1b_ok segs = true -> fetch_word segs (0xe52c4 : word) = Some W_e5290.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.

Lemma img_10040_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10050_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10078_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_100b0_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_100e8_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10120_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10158_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10190_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_101c8_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_101f0_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10200_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10238_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eebf0_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 977952) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eebf8_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 977960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 415804)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eec00_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 977968) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 857320)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eec08_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 977976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 859652)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eedb8_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 978408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1057608)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eedc0_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 978416) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1189536)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eedc8_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 978424) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1189528)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eedd0_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 978432) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 953456)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eedd8_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 978440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 953440)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_f01a8_4 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 983512) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_102330_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1188912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_102340_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1188928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_102348_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1188936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_1026e0_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1189520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_102708_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1189560) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_102720_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1189584) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eede0_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 978448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1189512)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_e8c30_8 : forall segs, u1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 953440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 609812)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
