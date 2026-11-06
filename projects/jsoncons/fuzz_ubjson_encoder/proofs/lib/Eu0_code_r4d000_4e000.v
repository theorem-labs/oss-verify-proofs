(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a1498 : bv 32 := 0x00050593.
Lemma F_a1498 : fetch_word Ubsan.M.loaded_segments (0xa14e4 : word) = Some W_a1498.
Proof. vm_refl. Qed.
Lemma D_a1498 : decode_any W_a1498 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14b8 : bv 32 := 0x00060463.
Lemma F_a14b8 : fetch_word Ubsan.M.loaded_segments (0xa1504 : word) = Some W_a14b8.
Proof. vm_refl. Qed.
Lemma D_a14b8 : decode_any W_a14b8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14c8 : bv 32 := 0xffe55803.
Lemma F_a14c8 : fetch_word Ubsan.M.loaded_segments (0xa1514 : word) = Some W_a14c8.
Proof. vm_refl. Qed.
Lemma D_a14c8 : decode_any W_a14c8 = Some (Load SZ2 false 16 10 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14cc : bv 32 := 0x00060e63.
Lemma F_a14cc : fetch_word Ubsan.M.loaded_segments (0xa1518 : word) = Some W_a14cc.
Proof. vm_refl. Qed.
Lemma D_a14cc : decode_any W_a14cc = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a14f4 : bv 32 := 0x0104b603.
Lemma F_a14f4 : fetch_word Ubsan.M.loaded_segments (0xa1540 : word) = Some W_a14f4.
Proof. vm_refl. Qed.
Lemma D_a14f4 : decode_any W_a14f4 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1530 : bv 32 := 0x01c4a783.
Lemma F_a1530 : fetch_word Ubsan.M.loaded_segments (0xa157c : word) = Some W_a1530.
Proof. vm_refl. Qed.
Lemma D_a1530 : decode_any W_a1530 = Some (Load SZ4 true 15 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a153c : bv 32 := 0x00000023.
Lemma F_a153c : fetch_word Ubsan.M.loaded_segments (0xa1588 : word) = Some W_a153c.
Proof. vm_refl. Qed.
Lemma D_a153c : decode_any W_a153c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1540 : bv 32 := 0xfffff6b7.
Lemma F_a1540 : fetch_word Ubsan.M.loaded_segments (0xa158c : word) = Some W_a1540.
Proof. vm_refl. Qed.
Lemma D_a1540 : decode_any W_a1540 = Some (Lui 13 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1544 : bv 32 := 0x0004c797.
Lemma F_a1544 : fetch_word Ubsan.M.loaded_segments (0xa1590 : word) = Some W_a1544.
Proof. vm_refl. Qed.
Lemma D_a1544 : decode_any W_a1544 = Some (Auipc 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1548 : bv 32 := 0x00d4f6b3.
Lemma F_a1548 : fetch_word Ubsan.M.loaded_segments (0xa1594 : word) = Some W_a1548.
Proof. vm_refl. Qed.
Lemma D_a1548 : decode_any W_a1548 = Some (Op ALU_AND 13 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a154c : bv 32 := 0x0006b683.
Lemma F_a154c : fetch_word Ubsan.M.loaded_segments (0xa1598 : word) = Some W_a154c.
Proof. vm_refl. Qed.
Lemma D_a154c : decode_any W_a154c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1550 : bv 32 := 0xa407b783.
Lemma F_a1550 : fetch_word Ubsan.M.loaded_segments (0xa159c : word) = Some W_a1550.
Proof. vm_refl. Qed.
Lemma D_a1550 : decode_any W_a1550 = Some (Load SZ8 true 15 15 2624, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1554 : bv 32 := 0x00f68463.
Lemma F_a1554 : fetch_word Ubsan.M.loaded_segments (0xa15a0 : word) = Some W_a1554.
Proof. vm_refl. Qed.
Lemma D_a1554 : decode_any W_a1554 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1558 : bv 32 := 0x00000023.
Lemma F_a1558 : fetch_word Ubsan.M.loaded_segments (0xa15a4 : word) = Some W_a1558.
Proof. vm_refl. Qed.
Lemma D_a1558 : decode_any W_a1558 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a155c : bv 32 := 0x03471693.
Lemma F_a155c : fetch_word Ubsan.M.loaded_segments (0xa15a8 : word) = Some W_a155c.
Proof. vm_refl. Qed.
Lemma D_a155c : decode_any W_a155c = Some (ShiftImm ALU_SLL 13 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1560 : bv 32 := 0x02f00e13.
Lemma F_a1560 : fetch_word Ubsan.M.loaded_segments (0xa15ac : word) = Some W_a1560.
Proof. vm_refl. Qed.
Lemma D_a1560 : decode_any W_a1560 = Some (OpImm ALU_ADD 28 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1564 : bv 32 := 0xfff7a797.
Lemma F_a1564 : fetch_word Ubsan.M.loaded_segments (0xa15b0 : word) = Some W_a1564.
Proof. vm_refl. Qed.
Lemma D_a1564 : decode_any W_a1564 = Some (Auipc 15 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1568 : bv 32 := 0x03a6d693.
Lemma F_a1568 : fetch_word Ubsan.M.loaded_segments (0xa15b4 : word) = Some W_a1568.
Proof. vm_refl. Qed.
Lemma D_a1568 : decode_any W_a1568 = Some (ShiftImm ALU_SRL 13 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_a156c : bv 32 := 0x00169393.
Lemma F_a156c : fetch_word Ubsan.M.loaded_segments (0xa15b8 : word) = Some W_a156c.
Proof. vm_refl. Qed.
Lemma D_a156c : decode_any W_a156c = Some (ShiftImm ALU_SLL 7 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1570 : bv 32 := 0xa1078793.
Lemma F_a1570 : fetch_word Ubsan.M.loaded_segments (0xa15bc : word) = Some W_a1570.
Proof. vm_refl. Qed.
Lemma D_a1570 : decode_any W_a1570 = Some (OpImm ALU_ADD 15 15 2576, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1574 : bv 32 := 0x02de6463.
Lemma F_a1574 : fetch_word Ubsan.M.loaded_segments (0xa15c0 : word) = Some W_a1574.
Proof. vm_refl. Qed.
Lemma D_a1574 : decode_any W_a1574 = Some (Branch BC_LTU 28 13 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1578 : bv 32 := 0x00778e33.
Lemma F_a1578 : fetch_word Ubsan.M.loaded_segments (0xa15c4 : word) = Some W_a1578.
Proof. vm_refl. Qed.
Lemma D_a1578 : decode_any W_a1578 = Some (Op ALU_ADD 28 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a157c : bv 32 := 0x000e5e03.
Lemma F_a157c : fetch_word Ubsan.M.loaded_segments (0xa15c8 : word) = Some W_a157c.
Proof. vm_refl. Qed.
Lemma D_a157c : decode_any W_a157c = Some (Load SZ2 false 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1580 : bv 32 := 0x025e0eb3.
Lemma F_a1580 : fetch_word Ubsan.M.loaded_segments (0xa15cc : word) = Some W_a1580.
Proof. vm_refl. Qed.
Lemma D_a1580 : decode_any W_a1580 = Some (Mul M_MUL 29 28 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1584 : bv 32 := 0x01d87463.
Lemma F_a1584 : fetch_word Ubsan.M.loaded_segments (0xa15d0 : word) = Some W_a1584.
Proof. vm_refl. Qed.
Lemma D_a1584 : decode_any W_a1584 = Some (Branch BC_GEU 16 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1588 : bv 32 := 0x00000023.
Lemma F_a1588 : fetch_word Ubsan.M.loaded_segments (0xa15d4 : word) = Some W_a1588.
Proof. vm_refl. Qed.
Lemma D_a1588 : decode_any W_a1588 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a158c : bv 32 := 0x00128e93.
Lemma F_a158c : fetch_word Ubsan.M.loaded_segments (0xa15d8 : word) = Some W_a158c.
Proof. vm_refl. Qed.
Lemma D_a158c : decode_any W_a158c = Some (OpImm ALU_ADD 29 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1590 : bv 32 := 0x03ce8e33.
Lemma F_a1590 : fetch_word Ubsan.M.loaded_segments (0xa15dc : word) = Some W_a1590.
Proof. vm_refl. Qed.
Lemma D_a1590 : decode_any W_a1590 = Some (Mul M_MUL 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1594 : bv 32 := 0x01c87863.
Lemma F_a1594 : fetch_word Ubsan.M.loaded_segments (0xa15e0 : word) = Some W_a1594.
Proof. vm_refl. Qed.
Lemma D_a1594 : decode_any W_a1594 = Some (Branch BC_GEU 16 28 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1598 : bv 32 := 0x0100006f.
Lemma F_a1598 : fetch_word Ubsan.M.loaded_segments (0xa15e4 : word) = Some W_a1598.
Proof. vm_refl. Qed.
Lemma D_a1598 : decode_any W_a1598 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a159c : bv 32 := 0x03f00e13.
Lemma F_a159c : fetch_word Ubsan.M.loaded_segments (0xa15e8 : word) = Some W_a159c.
Proof. vm_refl. Qed.
Lemma D_a159c : decode_any W_a159c = Some (OpImm ALU_ADD 28 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15a0 : bv 32 := 0x01c68463.
Lemma F_a15a0 : fetch_word Ubsan.M.loaded_segments (0xa15ec : word) = Some W_a15a0.
Proof. vm_refl. Qed.
Lemma D_a15a0 : decode_any W_a15a0 = Some (Branch BC_EQ 13 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15a4 : bv 32 := 0x00000023.
Lemma F_a15a4 : fetch_word Ubsan.M.loaded_segments (0xa15f0 : word) = Some W_a15a4.
Proof. vm_refl. Qed.
Lemma D_a15a4 : decode_any W_a15a4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15a8 : bv 32 := 0x00c75e13.
Lemma F_a15a8 : fetch_word Ubsan.M.loaded_segments (0xa15f4 : word) = Some W_a15a8.
Proof. vm_refl. Qed.
Lemma D_a15a8 : decode_any W_a15a8 = Some (ShiftImm ALU_SRL 28 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15ac : bv 32 := 0x000e0c63.
Lemma F_a15ac : fetch_word Ubsan.M.loaded_segments (0xa15f8 : word) = Some W_a15ac.
Proof. vm_refl. Qed.
Lemma D_a15ac : decode_any W_a15ac = Some (Branch BC_EQ 28 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15b0 : bv 32 := 0x008e1e13.
Lemma F_a15b0 : fetch_word Ubsan.M.loaded_segments (0xa15fc : word) = Some W_a15b0.
Proof. vm_refl. Qed.
Lemma D_a15b0 : decode_any W_a15b0 = Some (ShiftImm ALU_SLL 28 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15b4 : bv 32 := 0xfffe0e13.
Lemma F_a15b4 : fetch_word Ubsan.M.loaded_segments (0xa1600 : word) = Some W_a15b4.
Proof. vm_refl. Qed.
Lemma D_a15b4 : decode_any W_a15b4 = Some (OpImm ALU_ADD 28 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15b8 : bv 32 := 0x010e7463.
Lemma F_a15b8 : fetch_word Ubsan.M.loaded_segments (0xa1604 : word) = Some W_a15b8.
Proof. vm_refl. Qed.
Lemma D_a15b8 : decode_any W_a15b8 = Some (Branch BC_GEU 28 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15bc : bv 32 := 0x00000023.
Lemma F_a15bc : fetch_word Ubsan.M.loaded_segments (0xa1608 : word) = Some W_a15bc.
Proof. vm_refl. Qed.
Lemma D_a15bc : decode_any W_a15bc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15c0 : bv 32 := 0x1e030663.
Lemma F_a15c0 : fetch_word Ubsan.M.loaded_segments (0xa160c : word) = Some W_a15c0.
Proof. vm_refl. Qed.
Lemma D_a15c0 : decode_any W_a15c0 = Some (Branch BC_EQ 6 0 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15c4 : bv 32 := 0x007783b3.
Lemma F_a15c4 : fetch_word Ubsan.M.loaded_segments (0xa1610 : word) = Some W_a15c4.
Proof. vm_refl. Qed.
Lemma D_a15c4 : decode_any W_a15c4 = Some (Op ALU_ADD 7 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15c8 : bv 32 := 0x0003d803.
Lemma F_a15c8 : fetch_word Ubsan.M.loaded_segments (0xa1614 : word) = Some W_a15c8.
Proof. vm_refl. Qed.
Lemma D_a15c8 : decode_any W_a15c8 = Some (Load SZ2 false 16 7 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15cc : bv 32 := 0x00481813.
Lemma F_a15cc : fetch_word Ubsan.M.loaded_segments (0xa1618 : word) = Some W_a15cc.
Proof. vm_refl. Qed.
Lemma D_a15cc : decode_any W_a15cc = Some (ShiftImm ALU_SLL 16 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15d0 : bv 32 := 0x025802b3.
Lemma F_a15d0 : fetch_word Ubsan.M.loaded_segments (0xa161c : word) = Some W_a15d0.
Proof. vm_refl. Qed.
Lemma D_a15d0 : decode_any W_a15d0 = Some (Mul M_MUL 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15d4 : bv 32 := 0x0a000e13.
Lemma F_a15d4 : fetch_word Ubsan.M.loaded_segments (0xa1620 : word) = Some W_a15d4.
Proof. vm_refl. Qed.
Lemma D_a15d4 : decode_any W_a15d4 = Some (OpImm ALU_ADD 28 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15d8 : bv 32 := 0x005602b3.
Lemma F_a15d8 : fetch_word Ubsan.M.loaded_segments (0xa1624 : word) = Some W_a15d8.
Proof. vm_refl. Qed.
Lemma D_a15d8 : decode_any W_a15d8 = Some (Op ALU_ADD 5 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15dc : bv 32 := 0x01028313.
Lemma F_a15dc : fetch_word Ubsan.M.loaded_segments (0xa1628 : word) = Some W_a15dc.
Proof. vm_refl. Qed.
Lemma D_a15dc : decode_any W_a15dc = Some (OpImm ALU_ADD 6 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e0 : bv 32 := 0x01030833.
Lemma F_a15e0 : fetch_word Ubsan.M.loaded_segments (0xa162c : word) = Some W_a15e0.
Proof. vm_refl. Qed.
Lemma D_a15e0 : decode_any W_a15e0 = Some (Op ALU_ADD 16 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e4 : bv 32 := 0xffc80293.
Lemma F_a15e4 : fetch_word Ubsan.M.loaded_segments (0xa1630 : word) = Some W_a15e4.
Proof. vm_refl. Qed.
Lemma D_a15e4 : decode_any W_a15e4 = Some (OpImm ALU_ADD 5 16 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15e8 : bv 32 := 0x0058d393.
Lemma F_a15e8 : fetch_word Ubsan.M.loaded_segments (0xa1634 : word) = Some W_a15e8.
Proof. vm_refl. Qed.
Lemma D_a15e8 : decode_any W_a15e8 = Some (ShiftImm ALU_SRL 7 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15ec : bv 32 := 0x03c8e663.
Lemma F_a15ec : fetch_word Ubsan.M.loaded_segments (0xa1638 : word) = Some W_a15ec.
Proof. vm_refl. Qed.
Lemma D_a15ec : decode_any W_a15ec = Some (Branch BC_LTU 17 28 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f0 : bv 32 := 0x00500893.
Lemma F_a15f0 : fetch_word Ubsan.M.loaded_segments (0xa163c : word) = Some W_a15f0.
Proof. vm_refl. Qed.
Lemma D_a15f0 : decode_any W_a15f0 = Some (OpImm ALU_ADD 17 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f4 : bv 32 := 0x01138463.
Lemma F_a15f4 : fetch_word Ubsan.M.loaded_segments (0xa1640 : word) = Some W_a15f4.
Proof. vm_refl. Qed.
Lemma D_a15f4 : decode_any W_a15f4 = Some (Branch BC_EQ 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15f8 : bv 32 := 0x00000023.
Lemma F_a15f8 : fetch_word Ubsan.M.loaded_segments (0xa1644 : word) = Some W_a15f8.
Proof. vm_refl. Qed.
Lemma D_a15f8 : decode_any W_a15f8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a15fc : bv 32 := 0xff886383.
Lemma F_a15fc : fetch_word Ubsan.M.loaded_segments (0xa1648 : word) = Some W_a15fc.
Proof. vm_refl. Qed.
Lemma D_a15fc : decode_any W_a15fc = Some (Load SZ4 false 7 16 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1600 : bv 32 := 0x00400893.
Lemma F_a1600 : fetch_word Ubsan.M.loaded_segments (0xa164c : word) = Some W_a1600.
Proof. vm_refl. Qed.
Lemma D_a1600 : decode_any W_a1600 = Some (OpImm ALU_ADD 17 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1604 : bv 32 := 0x0078e463.
Lemma F_a1604 : fetch_word Ubsan.M.loaded_segments (0xa1650 : word) = Some W_a1604.
Proof. vm_refl. Qed.
Lemma D_a1604 : decode_any W_a1604 = Some (Branch BC_LTU 17 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1608 : bv 32 := 0x00000023.
Lemma F_a1608 : fetch_word Ubsan.M.loaded_segments (0xa1654 : word) = Some W_a1608.
Proof. vm_refl. Qed.
Lemma D_a1608 : decode_any W_a1608 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a160c : bv 32 := 0xff784883.
Lemma F_a160c : fetch_word Ubsan.M.loaded_segments (0xa1658 : word) = Some W_a160c.
Proof. vm_refl. Qed.
Lemma D_a160c : decode_any W_a160c = Some (Load SZ1 false 17 16 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1610 : bv 32 := 0x00088463.
Lemma F_a1610 : fetch_word Ubsan.M.loaded_segments (0xa165c : word) = Some W_a1610.
Proof. vm_refl. Qed.
Lemma D_a1610 : decode_any W_a1610 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1614 : bv 32 := 0x00000023.
Lemma F_a1614 : fetch_word Ubsan.M.loaded_segments (0xa1660 : word) = Some W_a1614.
Proof. vm_refl. Qed.
Lemma D_a1614 : decode_any W_a1614 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1618 : bv 32 := 0x40a288b3.
Lemma F_a1618 : fetch_word Ubsan.M.loaded_segments (0xa1664 : word) = Some W_a1618.
Proof. vm_refl. Qed.
Lemma D_a1618 : decode_any W_a1618 = Some (Op ALU_SUB 17 5 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a161c : bv 32 := 0x0078f463.
Lemma F_a161c : fetch_word Ubsan.M.loaded_segments (0xa1668 : word) = Some W_a161c.
Proof. vm_refl. Qed.
Lemma D_a161c : decode_any W_a161c = Some (Branch BC_GEU 17 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16bc : bv 32 := 0x07c74713.
Lemma F_a16bc : fetch_word Ubsan.M.loaded_segments (0xa1708 : word) = Some W_a16bc.
Proof. vm_refl. Qed.
Lemma D_a16bc : decode_any W_a16bc = Some (OpImm ALU_XOR 14 14 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16c0 : bv 32 := 0x07900893.
Lemma F_a16c0 : fetch_word Ubsan.M.loaded_segments (0xa170c : word) = Some W_a16c0.
Proof. vm_refl. Qed.
Lemma D_a16c0 : decode_any W_a16c0 = Some (OpImm ALU_ADD 17 0 121, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16cc : bv 32 := 0x011788b3.
Lemma F_a16cc : fetch_word Ubsan.M.loaded_segments (0xa1718 : word) = Some W_a16cc.
Proof. vm_refl. Qed.
Lemma D_a16cc : decode_any W_a16cc = Some (Op ALU_ADD 17 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16d0 : bv 32 := 0x0008d883.
Lemma F_a16d0 : fetch_word Ubsan.M.loaded_segments (0xa171c : word) = Some W_a16d0.
Proof. vm_refl. Qed.
Lemma D_a16d0 : decode_any W_a16d0 = Some (Load SZ2 false 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16d4 : bv 32 := 0x0f166463.
Lemma F_a16d4 : fetch_word Ubsan.M.loaded_segments (0xa1720 : word) = Some W_a16d4.
Proof. vm_refl. Qed.
Lemma D_a16d4 : decode_any W_a16d4 = Some (Branch BC_LTU 12 17 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16d8 : bv 32 := 0x07a00893.
Lemma F_a16d8 : fetch_word Ubsan.M.loaded_segments (0xa1724 : word) = Some W_a16d8.
Proof. vm_refl. Qed.
Lemma D_a16d8 : decode_any W_a16d8 = Some (OpImm ALU_ADD 17 0 122, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16dc : bv 32 := 0x0e40006f.
Lemma F_a16dc : fetch_word Ubsan.M.loaded_segments (0xa1728 : word) = Some W_a16dc.
Proof. vm_refl. Qed.
Lemma D_a16dc : decode_any W_a16dc = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16e0 : bv 32 := 0xfec3839b.
Lemma F_a16e0 : fetch_word Ubsan.M.loaded_segments (0xa172c : word) = Some W_a16e0.
Proof. vm_refl. Qed.
Lemma D_a16e0 : decode_any W_a16e0 = Some (OpImm32 7 7 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16e4 : bv 32 := 0x1075e063.
Lemma F_a16e4 : fetch_word Ubsan.M.loaded_segments (0xa1730 : word) = Some W_a16e4.
Proof. vm_refl. Qed.
Lemma D_a16e4 : decode_any W_a16e4 = Some (Branch BC_LTU 11 7 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16e8 : bv 32 := 0x03000793.
Lemma F_a16e8 : fetch_word Ubsan.M.loaded_segments (0xa1734 : word) = Some W_a16e8.
Proof. vm_refl. Qed.
Lemma D_a16e8 : decode_any W_a16e8 = Some (OpImm ALU_ADD 15 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16ec : bv 32 := 0x0ef6ec63.
Lemma F_a16ec : fetch_word Ubsan.M.loaded_segments (0xa1738 : word) = Some W_a16ec.
Proof. vm_refl. Qed.
Lemma D_a16ec : decode_any W_a16ec = Some (Branch BC_LTU 13 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16f0 : bv 32 := 0x03f00793.
Lemma F_a16f0 : fetch_word Ubsan.M.loaded_segments (0xa173c : word) = Some W_a16f0.
Proof. vm_refl. Qed.
Lemma D_a16f0 : decode_any W_a16f0 = Some (OpImm ALU_ADD 15 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16f4 : bv 32 := 0x00f68463.
Lemma F_a16f4 : fetch_word Ubsan.M.loaded_segments (0xa1740 : word) = Some W_a16f4.
Proof. vm_refl. Qed.
Lemma D_a16f4 : decode_any W_a16f4 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16f8 : bv 32 := 0x00000023.
Lemma F_a16f8 : fetch_word Ubsan.M.loaded_segments (0xa1744 : word) = Some W_a16f8.
Proof. vm_refl. Qed.
Lemma D_a16f8 : decode_any W_a16f8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a16fc : bv 32 := 0x00001a37.
Lemma F_a16fc : fetch_word Ubsan.M.loaded_segments (0xa1748 : word) = Some W_a16fc.
Proof. vm_refl. Qed.
Lemma D_a16fc : decode_any W_a16fc = Some (Lui 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1700 : bv 32 := 0x406509b3.
Lemma F_a1700 : fetch_word Ubsan.M.loaded_segments (0xa174c : word) = Some W_a1700.
Proof. vm_refl. Qed.
Lemma D_a1700 : decode_any W_a1700 = Some (Op ALU_SUB 19 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1704 : bv 32 := 0xfffff6b7.
Lemma F_a1704 : fetch_word Ubsan.M.loaded_segments (0xa1750 : word) = Some W_a1704.
Proof. vm_refl. Qed.
Lemma D_a1704 : decode_any W_a1704 = Some (Lui 13 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1708 : bv 32 := 0xfffa0a1b.
Lemma F_a1708 : fetch_word Ubsan.M.loaded_segments (0xa1754 : word) = Some W_a1708.
Proof. vm_refl. Qed.
Lemma D_a1708 : decode_any W_a1708 = Some (OpImm32 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_a170c : bv 32 := 0x014587b3.
Lemma F_a170c : fetch_word Ubsan.M.loaded_segments (0xa1758 : word) = Some W_a170c.
Proof. vm_refl. Qed.
Lemma D_a170c : decode_any W_a170c = Some (Op ALU_ADD 15 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1710 : bv 32 := 0x013787b3.
Lemma F_a1710 : fetch_word Ubsan.M.loaded_segments (0xa175c : word) = Some W_a1710.
Proof. vm_refl. Qed.
Lemma D_a1710 : decode_any W_a1710 = Some (Op ALU_ADD 15 15 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_a17c8 : bv 32 := 0x011787b3.
Lemma F_a17c8 : fetch_word Ubsan.M.loaded_segments (0xa1814 : word) = Some W_a17c8.
Proof. vm_refl. Qed.
Lemma D_a17c8 : decode_any W_a17c8 = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_a17cc : bv 32 := 0x0007d783.
Lemma F_a17cc : fetch_word Ubsan.M.loaded_segments (0xa1818 : word) = Some W_a17cc.
Proof. vm_refl. Qed.
Lemma D_a17cc : decode_any W_a17cc = Some (Load SZ2 false 15 15 0, 4%Z).
Proof. vm_refl. Qed.
