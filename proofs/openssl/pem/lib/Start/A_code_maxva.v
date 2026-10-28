(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d1570 : bv 32 := 0xff010113.
Lemma F_1d1570 : fetch_word Asan.M.loaded_segments (0x1d6584 : word) = Some W_1d1570.
Proof. vm_refl. Qed.
Lemma D_1d1570 : decode_any W_1d1570 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1574 : bv 32 := 0x00113423.
Lemma F_1d1574 : fetch_word Asan.M.loaded_segments (0x1d6588 : word) = Some W_1d1574.
Proof. vm_refl. Qed.
Lemma D_1d1574 : decode_any W_1d1574 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1578 : bv 32 := 0x00813023.
Lemma F_1d1578 : fetch_word Asan.M.loaded_segments (0x1d658c : word) = Some W_1d1578.
Proof. vm_refl. Qed.
Lemma D_1d1578 : decode_any W_1d1578 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d157c : bv 32 := 0x01010413.
Lemma F_1d157c : fetch_word Asan.M.loaded_segments (0x1d6590 : word) = Some W_1d157c.
Proof. vm_refl. Qed.
Lemma D_1d157c : decode_any W_1d157c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1580 : bv 32 := 0x003ce517.
Lemma F_1d1580 : fetch_word Asan.M.loaded_segments (0x1d6594 : word) = Some W_1d1580.
Proof. vm_refl. Qed.
Lemma D_1d1580 : decode_any W_1d1580 = Some (Auipc 10 974, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1584 : bv 32 := 0x06453503.
Lemma F_1d1584 : fetch_word Asan.M.loaded_segments (0x1d6598 : word) = Some W_1d1584.
Proof. vm_refl. Qed.
Lemma D_1d1584 : decode_any W_1d1584 = Some (Load SZ8 true 10 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1588 : bv 32 := 0x00050a63.
Lemma F_1d1588 : fetch_word Asan.M.loaded_segments (0x1d659c : word) = Some W_1d1588.
Proof. vm_refl. Qed.
Lemma D_1d1588 : decode_any W_1d1588 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d158c : bv 32 := 0x003cf517.
Lemma F_1d158c : fetch_word Asan.M.loaded_segments (0x1d65a0 : word) = Some W_1d158c.
Proof. vm_refl. Qed.
Lemma D_1d158c : decode_any W_1d158c = Some (Auipc 10 975, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1590 : bv 32 := 0xbe853503.
Lemma F_1d1590 : fetch_word Asan.M.loaded_segments (0x1d65a4 : word) = Some W_1d1590.
Proof. vm_refl. Qed.
Lemma D_1d1590 : decode_any W_1d1590 = Some (Load SZ8 true 10 10 3048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1594 : bv 32 := 0x00053503.
Lemma F_1d1594 : fetch_word Asan.M.loaded_segments (0x1d65a8 : word) = Some W_1d1594.
Proof. vm_refl. Qed.
Lemma D_1d1594 : decode_any W_1d1594 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1598 : bv 32 := 0x00c0006f.
Lemma F_1d1598 : fetch_word Asan.M.loaded_segments (0x1d65ac : word) = Some W_1d1598.
Proof. vm_refl. Qed.
Lemma D_1d1598 : decode_any W_1d1598 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d159c : bv 32 := 0x0c040663.
Lemma F_1d159c : fetch_word Asan.M.loaded_segments (0x1d65b0 : word) = Some W_1d159c.
Proof. vm_refl. Qed.
Lemma D_1d159c : decode_any W_1d159c = Some (Branch BC_EQ 8 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15a0 : bv 32 := 0x00040513.
Lemma F_1d15a0 : fetch_word Asan.M.loaded_segments (0x1d65b4 : word) = Some W_1d15a0.
Proof. vm_refl. Qed.
Lemma D_1d15a0 : decode_any W_1d15a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15a4 : bv 32 := 0x00155593.
Lemma F_1d15a4 : fetch_word Asan.M.loaded_segments (0x1d65b8 : word) = Some W_1d15a4.
Proof. vm_refl. Qed.
Lemma D_1d15a4 : decode_any W_1d15a4 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15a8 : bv 32 := 0x55555637.
Lemma F_1d15a8 : fetch_word Asan.M.loaded_segments (0x1d65bc : word) = Some W_1d15a8.
Proof. vm_refl. Qed.
Lemma D_1d15a8 : decode_any W_1d15a8 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15ac : bv 32 := 0x333336b7.
Lemma F_1d15ac : fetch_word Asan.M.loaded_segments (0x1d65c0 : word) = Some W_1d15ac.
Proof. vm_refl. Qed.
Lemma D_1d15ac : decode_any W_1d15ac = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15b0 : bv 32 := 0x0f0f1737.
Lemma F_1d15b0 : fetch_word Asan.M.loaded_segments (0x1d65c4 : word) = Some W_1d15b0.
Proof. vm_refl. Qed.
Lemma D_1d15b0 : decode_any W_1d15b0 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15b4 : bv 32 := 0x010107b7.
Lemma F_1d15b4 : fetch_word Asan.M.loaded_segments (0x1d65c8 : word) = Some W_1d15b4.
Proof. vm_refl. Qed.
Lemma D_1d15b4 : decode_any W_1d15b4 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15b8 : bv 32 := 0x00b56533.
Lemma F_1d15b8 : fetch_word Asan.M.loaded_segments (0x1d65cc : word) = Some W_1d15b8.
Proof. vm_refl. Qed.
Lemma D_1d15b8 : decode_any W_1d15b8 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15bc : bv 32 := 0x5556059b.
Lemma F_1d15bc : fetch_word Asan.M.loaded_segments (0x1d65d0 : word) = Some W_1d15bc.
Proof. vm_refl. Qed.
Lemma D_1d15bc : decode_any W_1d15bc = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15c0 : bv 32 := 0x3336861b.
Lemma F_1d15c0 : fetch_word Asan.M.loaded_segments (0x1d65d4 : word) = Some W_1d15c0.
Proof. vm_refl. Qed.
Lemma D_1d15c0 : decode_any W_1d15c0 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15c4 : bv 32 := 0xf0f7069b.
Lemma F_1d15c4 : fetch_word Asan.M.loaded_segments (0x1d65d8 : word) = Some W_1d15c4.
Proof. vm_refl. Qed.
Lemma D_1d15c4 : decode_any W_1d15c4 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15c8 : bv 32 := 0x1017871b.
Lemma F_1d15c8 : fetch_word Asan.M.loaded_segments (0x1d65dc : word) = Some W_1d15c8.
Proof. vm_refl. Qed.
Lemma D_1d15c8 : decode_any W_1d15c8 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15cc : bv 32 := 0x00255793.
Lemma F_1d15cc : fetch_word Asan.M.loaded_segments (0x1d65e0 : word) = Some W_1d15cc.
Proof. vm_refl. Qed.
Lemma D_1d15cc : decode_any W_1d15cc = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15d0 : bv 32 := 0x00f56533.
Lemma F_1d15d0 : fetch_word Asan.M.loaded_segments (0x1d65e4 : word) = Some W_1d15d0.
Proof. vm_refl. Qed.
Lemma D_1d15d0 : decode_any W_1d15d0 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15d4 : bv 32 := 0x02059793.
Lemma F_1d15d4 : fetch_word Asan.M.loaded_segments (0x1d65e8 : word) = Some W_1d15d4.
Proof. vm_refl. Qed.
Lemma D_1d15d4 : decode_any W_1d15d4 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15d8 : bv 32 := 0x00f585b3.
Lemma F_1d15d8 : fetch_word Asan.M.loaded_segments (0x1d65ec : word) = Some W_1d15d8.
Proof. vm_refl. Qed.
Lemma D_1d15d8 : decode_any W_1d15d8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15dc : bv 32 := 0x02061793.
Lemma F_1d15dc : fetch_word Asan.M.loaded_segments (0x1d65f0 : word) = Some W_1d15dc.
Proof. vm_refl. Qed.
Lemma D_1d15dc : decode_any W_1d15dc = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15e0 : bv 32 := 0x00f60633.
Lemma F_1d15e0 : fetch_word Asan.M.loaded_segments (0x1d65f4 : word) = Some W_1d15e0.
Proof. vm_refl. Qed.
Lemma D_1d15e0 : decode_any W_1d15e0 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15e4 : bv 32 := 0x02069793.
Lemma F_1d15e4 : fetch_word Asan.M.loaded_segments (0x1d65f8 : word) = Some W_1d15e4.
Proof. vm_refl. Qed.
Lemma D_1d15e4 : decode_any W_1d15e4 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15e8 : bv 32 := 0x00f686b3.
Lemma F_1d15e8 : fetch_word Asan.M.loaded_segments (0x1d65fc : word) = Some W_1d15e8.
Proof. vm_refl. Qed.
Lemma D_1d15e8 : decode_any W_1d15e8 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15ec : bv 32 := 0x02071793.
Lemma F_1d15ec : fetch_word Asan.M.loaded_segments (0x1d6600 : word) = Some W_1d15ec.
Proof. vm_refl. Qed.
Lemma D_1d15ec : decode_any W_1d15ec = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15f0 : bv 32 := 0x00f70733.
Lemma F_1d15f0 : fetch_word Asan.M.loaded_segments (0x1d6604 : word) = Some W_1d15f0.
Proof. vm_refl. Qed.
Lemma D_1d15f0 : decode_any W_1d15f0 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15f4 : bv 32 := 0x00455793.
Lemma F_1d15f4 : fetch_word Asan.M.loaded_segments (0x1d6608 : word) = Some W_1d15f4.
Proof. vm_refl. Qed.
Lemma D_1d15f4 : decode_any W_1d15f4 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15f8 : bv 32 := 0x00f56533.
Lemma F_1d15f8 : fetch_word Asan.M.loaded_segments (0x1d660c : word) = Some W_1d15f8.
Proof. vm_refl. Qed.
Lemma D_1d15f8 : decode_any W_1d15f8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15fc : bv 32 := 0x00855793.
Lemma F_1d15fc : fetch_word Asan.M.loaded_segments (0x1d6610 : word) = Some W_1d15fc.
Proof. vm_refl. Qed.
Lemma D_1d15fc : decode_any W_1d15fc = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1600 : bv 32 := 0x00f56533.
Lemma F_1d1600 : fetch_word Asan.M.loaded_segments (0x1d6614 : word) = Some W_1d1600.
Proof. vm_refl. Qed.
Lemma D_1d1600 : decode_any W_1d1600 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1604 : bv 32 := 0x01055793.
Lemma F_1d1604 : fetch_word Asan.M.loaded_segments (0x1d6618 : word) = Some W_1d1604.
Proof. vm_refl. Qed.
Lemma D_1d1604 : decode_any W_1d1604 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1608 : bv 32 := 0x00f56533.
Lemma F_1d1608 : fetch_word Asan.M.loaded_segments (0x1d661c : word) = Some W_1d1608.
Proof. vm_refl. Qed.
Lemma D_1d1608 : decode_any W_1d1608 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d160c : bv 32 := 0x02055793.
Lemma F_1d160c : fetch_word Asan.M.loaded_segments (0x1d6620 : word) = Some W_1d160c.
Proof. vm_refl. Qed.
Lemma D_1d160c : decode_any W_1d160c = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1610 : bv 32 := 0x00f56533.
Lemma F_1d1610 : fetch_word Asan.M.loaded_segments (0x1d6624 : word) = Some W_1d1610.
Proof. vm_refl. Qed.
Lemma D_1d1610 : decode_any W_1d1610 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1614 : bv 32 := 0xfff54513.
Lemma F_1d1614 : fetch_word Asan.M.loaded_segments (0x1d6628 : word) = Some W_1d1614.
Proof. vm_refl. Qed.
Lemma D_1d1614 : decode_any W_1d1614 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1618 : bv 32 := 0x00155793.
Lemma F_1d1618 : fetch_word Asan.M.loaded_segments (0x1d662c : word) = Some W_1d1618.
Proof. vm_refl. Qed.
Lemma D_1d1618 : decode_any W_1d1618 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d161c : bv 32 := 0x00b7f5b3.
Lemma F_1d161c : fetch_word Asan.M.loaded_segments (0x1d6630 : word) = Some W_1d161c.
Proof. vm_refl. Qed.
Lemma D_1d161c : decode_any W_1d161c = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1620 : bv 32 := 0x40b50533.
Lemma F_1d1620 : fetch_word Asan.M.loaded_segments (0x1d6634 : word) = Some W_1d1620.
Proof. vm_refl. Qed.
Lemma D_1d1620 : decode_any W_1d1620 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1624 : bv 32 := 0x00c575b3.
Lemma F_1d1624 : fetch_word Asan.M.loaded_segments (0x1d6638 : word) = Some W_1d1624.
Proof. vm_refl. Qed.
Lemma D_1d1624 : decode_any W_1d1624 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1628 : bv 32 := 0x00255513.
Lemma F_1d1628 : fetch_word Asan.M.loaded_segments (0x1d663c : word) = Some W_1d1628.
Proof. vm_refl. Qed.
Lemma D_1d1628 : decode_any W_1d1628 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d162c : bv 32 := 0x00c57533.
Lemma F_1d162c : fetch_word Asan.M.loaded_segments (0x1d6640 : word) = Some W_1d162c.
Proof. vm_refl. Qed.
Lemma D_1d162c : decode_any W_1d162c = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1630 : bv 32 := 0x00a58533.
Lemma F_1d1630 : fetch_word Asan.M.loaded_segments (0x1d6644 : word) = Some W_1d1630.
Proof. vm_refl. Qed.
Lemma D_1d1630 : decode_any W_1d1630 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1634 : bv 32 := 0x00455593.
Lemma F_1d1634 : fetch_word Asan.M.loaded_segments (0x1d6648 : word) = Some W_1d1634.
Proof. vm_refl. Qed.
Lemma D_1d1634 : decode_any W_1d1634 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1638 : bv 32 := 0x00b50533.
Lemma F_1d1638 : fetch_word Asan.M.loaded_segments (0x1d664c : word) = Some W_1d1638.
Proof. vm_refl. Qed.
Lemma D_1d1638 : decode_any W_1d1638 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d163c : bv 32 := 0x00d57533.
Lemma F_1d163c : fetch_word Asan.M.loaded_segments (0x1d6650 : word) = Some W_1d163c.
Proof. vm_refl. Qed.
Lemma D_1d163c : decode_any W_1d163c = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1640 : bv 32 := 0x02e50533.
Lemma F_1d1640 : fetch_word Asan.M.loaded_segments (0x1d6654 : word) = Some W_1d1640.
Proof. vm_refl. Qed.
Lemma D_1d1640 : decode_any W_1d1640 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1644 : bv 32 := 0x03855513.
Lemma F_1d1644 : fetch_word Asan.M.loaded_segments (0x1d6658 : word) = Some W_1d1644.
Proof. vm_refl. Qed.
Lemma D_1d1644 : decode_any W_1d1644 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1648 : bv 32 := 0x40a0053b.
Lemma F_1d1648 : fetch_word Asan.M.loaded_segments (0x1d665c : word) = Some W_1d1648.
Proof. vm_refl. Qed.
Lemma D_1d1648 : decode_any W_1d1648 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d164c : bv 32 := 0xfff00593.
Lemma F_1d164c : fetch_word Asan.M.loaded_segments (0x1d6660 : word) = Some W_1d164c.
Proof. vm_refl. Qed.
Lemma D_1d164c : decode_any W_1d164c = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1650 : bv 32 := 0x00a59533.
Lemma F_1d1650 : fetch_word Asan.M.loaded_segments (0x1d6664 : word) = Some W_1d1650.
Proof. vm_refl. Qed.
Lemma D_1d1650 : decode_any W_1d1650 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1654 : bv 32 := 0xfff54513.
Lemma F_1d1654 : fetch_word Asan.M.loaded_segments (0x1d6668 : word) = Some W_1d1654.
Proof. vm_refl. Qed.
Lemma D_1d1654 : decode_any W_1d1654 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1658 : bv 32 := 0x00813083.
Lemma F_1d1658 : fetch_word Asan.M.loaded_segments (0x1d666c : word) = Some W_1d1658.
Proof. vm_refl. Qed.
Lemma D_1d1658 : decode_any W_1d1658 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d165c : bv 32 := 0x00013403.
Lemma F_1d165c : fetch_word Asan.M.loaded_segments (0x1d6670 : word) = Some W_1d165c.
Proof. vm_refl. Qed.
Lemma D_1d165c : decode_any W_1d165c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1660 : bv 32 := 0x01010113.
Lemma F_1d1660 : fetch_word Asan.M.loaded_segments (0x1d6674 : word) = Some W_1d1660.
Proof. vm_refl. Qed.
Lemma D_1d1660 : decode_any W_1d1660 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1664 : bv 32 := 0x00008067.
Lemma F_1d1664 : fetch_word Asan.M.loaded_segments (0x1d6678 : word) = Some W_1d1664.
Proof. vm_refl. Qed.
Lemma D_1d1664 : decode_any W_1d1664 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
