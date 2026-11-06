(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d1504 : bv 32 := 0xff010113.
Lemma F_1d1504 : fetch_word AsanUbsan.M.loaded_segments (0x1d14f0 : word) = Some W_1d1504.
Proof. vm_refl. Qed.
Lemma D_1d1504 : decode_any W_1d1504 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1508 : bv 32 := 0x00113423.
Lemma F_1d1508 : fetch_word AsanUbsan.M.loaded_segments (0x1d14f4 : word) = Some W_1d1508.
Proof. vm_refl. Qed.
Lemma D_1d1508 : decode_any W_1d1508 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d150c : bv 32 := 0x00813023.
Lemma F_1d150c : fetch_word AsanUbsan.M.loaded_segments (0x1d14f8 : word) = Some W_1d150c.
Proof. vm_refl. Qed.
Lemma D_1d150c : decode_any W_1d150c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1510 : bv 32 := 0x01010413.
Lemma F_1d1510 : fetch_word AsanUbsan.M.loaded_segments (0x1d14fc : word) = Some W_1d1510.
Proof. vm_refl. Qed.
Lemma D_1d1510 : decode_any W_1d1510 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1514 : bv 32 := 0x00410517.
Lemma F_1d1514 : fetch_word AsanUbsan.M.loaded_segments (0x1d1500 : word) = Some W_1d1514.
Proof. vm_refl. Qed.
Lemma D_1d1514 : decode_any W_1d1514 = Some (Auipc 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1518 : bv 32 := 0xa9853503.
Lemma F_1d1518 : fetch_word AsanUbsan.M.loaded_segments (0x1d1504 : word) = Some W_1d1518.
Proof. vm_refl. Qed.
Lemma D_1d1518 : decode_any W_1d1518 = Some (Load SZ8 true 10 10 2712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d151c : bv 32 := 0x00050a63.
Lemma F_1d151c : fetch_word AsanUbsan.M.loaded_segments (0x1d1508 : word) = Some W_1d151c.
Proof. vm_refl. Qed.
Lemma D_1d151c : decode_any W_1d151c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1520 : bv 32 := 0x00410517.
Lemma F_1d1520 : fetch_word AsanUbsan.M.loaded_segments (0x1d150c : word) = Some W_1d1520.
Proof. vm_refl. Qed.
Lemma D_1d1520 : decode_any W_1d1520 = Some (Auipc 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1524 : bv 32 := 0x61c53503.
Lemma F_1d1524 : fetch_word AsanUbsan.M.loaded_segments (0x1d1510 : word) = Some W_1d1524.
Proof. vm_refl. Qed.
Lemma D_1d1524 : decode_any W_1d1524 = Some (Load SZ8 true 10 10 1564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1528 : bv 32 := 0x00053503.
Lemma F_1d1528 : fetch_word AsanUbsan.M.loaded_segments (0x1d1514 : word) = Some W_1d1528.
Proof. vm_refl. Qed.
Lemma D_1d1528 : decode_any W_1d1528 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d152c : bv 32 := 0x00c0006f.
Lemma F_1d152c : fetch_word AsanUbsan.M.loaded_segments (0x1d1518 : word) = Some W_1d152c.
Proof. vm_refl. Qed.
Lemma D_1d152c : decode_any W_1d152c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1530 : bv 32 := 0x0c040663.
Lemma F_1d1530 : fetch_word AsanUbsan.M.loaded_segments (0x1d151c : word) = Some W_1d1530.
Proof. vm_refl. Qed.
Lemma D_1d1530 : decode_any W_1d1530 = Some (Branch BC_EQ 8 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1534 : bv 32 := 0x00040513.
Lemma F_1d1534 : fetch_word AsanUbsan.M.loaded_segments (0x1d1520 : word) = Some W_1d1534.
Proof. vm_refl. Qed.
Lemma D_1d1534 : decode_any W_1d1534 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1538 : bv 32 := 0x00155593.
Lemma F_1d1538 : fetch_word AsanUbsan.M.loaded_segments (0x1d1524 : word) = Some W_1d1538.
Proof. vm_refl. Qed.
Lemma D_1d1538 : decode_any W_1d1538 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d153c : bv 32 := 0x55555637.
Lemma F_1d153c : fetch_word AsanUbsan.M.loaded_segments (0x1d1528 : word) = Some W_1d153c.
Proof. vm_refl. Qed.
Lemma D_1d153c : decode_any W_1d153c = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1540 : bv 32 := 0x333336b7.
Lemma F_1d1540 : fetch_word AsanUbsan.M.loaded_segments (0x1d152c : word) = Some W_1d1540.
Proof. vm_refl. Qed.
Lemma D_1d1540 : decode_any W_1d1540 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1544 : bv 32 := 0x0f0f1737.
Lemma F_1d1544 : fetch_word AsanUbsan.M.loaded_segments (0x1d1530 : word) = Some W_1d1544.
Proof. vm_refl. Qed.
Lemma D_1d1544 : decode_any W_1d1544 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1548 : bv 32 := 0x010107b7.
Lemma F_1d1548 : fetch_word AsanUbsan.M.loaded_segments (0x1d1534 : word) = Some W_1d1548.
Proof. vm_refl. Qed.
Lemma D_1d1548 : decode_any W_1d1548 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d154c : bv 32 := 0x00b56533.
Lemma F_1d154c : fetch_word AsanUbsan.M.loaded_segments (0x1d1538 : word) = Some W_1d154c.
Proof. vm_refl. Qed.
Lemma D_1d154c : decode_any W_1d154c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1550 : bv 32 := 0x5556059b.
Lemma F_1d1550 : fetch_word AsanUbsan.M.loaded_segments (0x1d153c : word) = Some W_1d1550.
Proof. vm_refl. Qed.
Lemma D_1d1550 : decode_any W_1d1550 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1554 : bv 32 := 0x3336861b.
Lemma F_1d1554 : fetch_word AsanUbsan.M.loaded_segments (0x1d1540 : word) = Some W_1d1554.
Proof. vm_refl. Qed.
Lemma D_1d1554 : decode_any W_1d1554 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1558 : bv 32 := 0xf0f7069b.
Lemma F_1d1558 : fetch_word AsanUbsan.M.loaded_segments (0x1d1544 : word) = Some W_1d1558.
Proof. vm_refl. Qed.
Lemma D_1d1558 : decode_any W_1d1558 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d155c : bv 32 := 0x1017871b.
Lemma F_1d155c : fetch_word AsanUbsan.M.loaded_segments (0x1d1548 : word) = Some W_1d155c.
Proof. vm_refl. Qed.
Lemma D_1d155c : decode_any W_1d155c = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1560 : bv 32 := 0x00255793.
Lemma F_1d1560 : fetch_word AsanUbsan.M.loaded_segments (0x1d154c : word) = Some W_1d1560.
Proof. vm_refl. Qed.
Lemma D_1d1560 : decode_any W_1d1560 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1564 : bv 32 := 0x00f56533.
Lemma F_1d1564 : fetch_word AsanUbsan.M.loaded_segments (0x1d1550 : word) = Some W_1d1564.
Proof. vm_refl. Qed.
Lemma D_1d1564 : decode_any W_1d1564 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1568 : bv 32 := 0x02059793.
Lemma F_1d1568 : fetch_word AsanUbsan.M.loaded_segments (0x1d1554 : word) = Some W_1d1568.
Proof. vm_refl. Qed.
Lemma D_1d1568 : decode_any W_1d1568 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d156c : bv 32 := 0x00f585b3.
Lemma F_1d156c : fetch_word AsanUbsan.M.loaded_segments (0x1d1558 : word) = Some W_1d156c.
Proof. vm_refl. Qed.
Lemma D_1d156c : decode_any W_1d156c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1570 : bv 32 := 0x02061793.
Lemma F_1d1570 : fetch_word AsanUbsan.M.loaded_segments (0x1d155c : word) = Some W_1d1570.
Proof. vm_refl. Qed.
Lemma D_1d1570 : decode_any W_1d1570 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1574 : bv 32 := 0x00f60633.
Lemma F_1d1574 : fetch_word AsanUbsan.M.loaded_segments (0x1d1560 : word) = Some W_1d1574.
Proof. vm_refl. Qed.
Lemma D_1d1574 : decode_any W_1d1574 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1578 : bv 32 := 0x02069793.
Lemma F_1d1578 : fetch_word AsanUbsan.M.loaded_segments (0x1d1564 : word) = Some W_1d1578.
Proof. vm_refl. Qed.
Lemma D_1d1578 : decode_any W_1d1578 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d157c : bv 32 := 0x00f686b3.
Lemma F_1d157c : fetch_word AsanUbsan.M.loaded_segments (0x1d1568 : word) = Some W_1d157c.
Proof. vm_refl. Qed.
Lemma D_1d157c : decode_any W_1d157c = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1580 : bv 32 := 0x02071793.
Lemma F_1d1580 : fetch_word AsanUbsan.M.loaded_segments (0x1d156c : word) = Some W_1d1580.
Proof. vm_refl. Qed.
Lemma D_1d1580 : decode_any W_1d1580 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1584 : bv 32 := 0x00f70733.
Lemma F_1d1584 : fetch_word AsanUbsan.M.loaded_segments (0x1d1570 : word) = Some W_1d1584.
Proof. vm_refl. Qed.
Lemma D_1d1584 : decode_any W_1d1584 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1588 : bv 32 := 0x00455793.
Lemma F_1d1588 : fetch_word AsanUbsan.M.loaded_segments (0x1d1574 : word) = Some W_1d1588.
Proof. vm_refl. Qed.
Lemma D_1d1588 : decode_any W_1d1588 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d158c : bv 32 := 0x00f56533.
Lemma F_1d158c : fetch_word AsanUbsan.M.loaded_segments (0x1d1578 : word) = Some W_1d158c.
Proof. vm_refl. Qed.
Lemma D_1d158c : decode_any W_1d158c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1590 : bv 32 := 0x00855793.
Lemma F_1d1590 : fetch_word AsanUbsan.M.loaded_segments (0x1d157c : word) = Some W_1d1590.
Proof. vm_refl. Qed.
Lemma D_1d1590 : decode_any W_1d1590 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1594 : bv 32 := 0x00f56533.
Lemma F_1d1594 : fetch_word AsanUbsan.M.loaded_segments (0x1d1580 : word) = Some W_1d1594.
Proof. vm_refl. Qed.
Lemma D_1d1594 : decode_any W_1d1594 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d1598 : bv 32 := 0x01055793.
Lemma F_1d1598 : fetch_word AsanUbsan.M.loaded_segments (0x1d1584 : word) = Some W_1d1598.
Proof. vm_refl. Qed.
Lemma D_1d1598 : decode_any W_1d1598 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d159c : bv 32 := 0x00f56533.
Lemma F_1d159c : fetch_word AsanUbsan.M.loaded_segments (0x1d1588 : word) = Some W_1d159c.
Proof. vm_refl. Qed.
Lemma D_1d159c : decode_any W_1d159c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15a0 : bv 32 := 0x02055793.
Lemma F_1d15a0 : fetch_word AsanUbsan.M.loaded_segments (0x1d158c : word) = Some W_1d15a0.
Proof. vm_refl. Qed.
Lemma D_1d15a0 : decode_any W_1d15a0 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15a4 : bv 32 := 0x00f56533.
Lemma F_1d15a4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1590 : word) = Some W_1d15a4.
Proof. vm_refl. Qed.
Lemma D_1d15a4 : decode_any W_1d15a4 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15a8 : bv 32 := 0xfff54513.
Lemma F_1d15a8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1594 : word) = Some W_1d15a8.
Proof. vm_refl. Qed.
Lemma D_1d15a8 : decode_any W_1d15a8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15ac : bv 32 := 0x00155793.
Lemma F_1d15ac : fetch_word AsanUbsan.M.loaded_segments (0x1d1598 : word) = Some W_1d15ac.
Proof. vm_refl. Qed.
Lemma D_1d15ac : decode_any W_1d15ac = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15b0 : bv 32 := 0x00b7f5b3.
Lemma F_1d15b0 : fetch_word AsanUbsan.M.loaded_segments (0x1d159c : word) = Some W_1d15b0.
Proof. vm_refl. Qed.
Lemma D_1d15b0 : decode_any W_1d15b0 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15b4 : bv 32 := 0x40b50533.
Lemma F_1d15b4 : fetch_word AsanUbsan.M.loaded_segments (0x1d15a0 : word) = Some W_1d15b4.
Proof. vm_refl. Qed.
Lemma D_1d15b4 : decode_any W_1d15b4 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15b8 : bv 32 := 0x00c575b3.
Lemma F_1d15b8 : fetch_word AsanUbsan.M.loaded_segments (0x1d15a4 : word) = Some W_1d15b8.
Proof. vm_refl. Qed.
Lemma D_1d15b8 : decode_any W_1d15b8 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15bc : bv 32 := 0x00255513.
Lemma F_1d15bc : fetch_word AsanUbsan.M.loaded_segments (0x1d15a8 : word) = Some W_1d15bc.
Proof. vm_refl. Qed.
Lemma D_1d15bc : decode_any W_1d15bc = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15c0 : bv 32 := 0x00c57533.
Lemma F_1d15c0 : fetch_word AsanUbsan.M.loaded_segments (0x1d15ac : word) = Some W_1d15c0.
Proof. vm_refl. Qed.
Lemma D_1d15c0 : decode_any W_1d15c0 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15c4 : bv 32 := 0x00a58533.
Lemma F_1d15c4 : fetch_word AsanUbsan.M.loaded_segments (0x1d15b0 : word) = Some W_1d15c4.
Proof. vm_refl. Qed.
Lemma D_1d15c4 : decode_any W_1d15c4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15c8 : bv 32 := 0x00455593.
Lemma F_1d15c8 : fetch_word AsanUbsan.M.loaded_segments (0x1d15b4 : word) = Some W_1d15c8.
Proof. vm_refl. Qed.
Lemma D_1d15c8 : decode_any W_1d15c8 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15cc : bv 32 := 0x00b50533.
Lemma F_1d15cc : fetch_word AsanUbsan.M.loaded_segments (0x1d15b8 : word) = Some W_1d15cc.
Proof. vm_refl. Qed.
Lemma D_1d15cc : decode_any W_1d15cc = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15d0 : bv 32 := 0x00d57533.
Lemma F_1d15d0 : fetch_word AsanUbsan.M.loaded_segments (0x1d15bc : word) = Some W_1d15d0.
Proof. vm_refl. Qed.
Lemma D_1d15d0 : decode_any W_1d15d0 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15d4 : bv 32 := 0x02e50533.
Lemma F_1d15d4 : fetch_word AsanUbsan.M.loaded_segments (0x1d15c0 : word) = Some W_1d15d4.
Proof. vm_refl. Qed.
Lemma D_1d15d4 : decode_any W_1d15d4 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15d8 : bv 32 := 0x03855513.
Lemma F_1d15d8 : fetch_word AsanUbsan.M.loaded_segments (0x1d15c4 : word) = Some W_1d15d8.
Proof. vm_refl. Qed.
Lemma D_1d15d8 : decode_any W_1d15d8 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15dc : bv 32 := 0x40a0053b.
Lemma F_1d15dc : fetch_word AsanUbsan.M.loaded_segments (0x1d15c8 : word) = Some W_1d15dc.
Proof. vm_refl. Qed.
Lemma D_1d15dc : decode_any W_1d15dc = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15e0 : bv 32 := 0xfff00593.
Lemma F_1d15e0 : fetch_word AsanUbsan.M.loaded_segments (0x1d15cc : word) = Some W_1d15e0.
Proof. vm_refl. Qed.
Lemma D_1d15e0 : decode_any W_1d15e0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15e4 : bv 32 := 0x00a59533.
Lemma F_1d15e4 : fetch_word AsanUbsan.M.loaded_segments (0x1d15d0 : word) = Some W_1d15e4.
Proof. vm_refl. Qed.
Lemma D_1d15e4 : decode_any W_1d15e4 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15e8 : bv 32 := 0xfff54513.
Lemma F_1d15e8 : fetch_word AsanUbsan.M.loaded_segments (0x1d15d4 : word) = Some W_1d15e8.
Proof. vm_refl. Qed.
Lemma D_1d15e8 : decode_any W_1d15e8 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15ec : bv 32 := 0x00813083.
Lemma F_1d15ec : fetch_word AsanUbsan.M.loaded_segments (0x1d15d8 : word) = Some W_1d15ec.
Proof. vm_refl. Qed.
Lemma D_1d15ec : decode_any W_1d15ec = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15f0 : bv 32 := 0x00013403.
Lemma F_1d15f0 : fetch_word AsanUbsan.M.loaded_segments (0x1d15dc : word) = Some W_1d15f0.
Proof. vm_refl. Qed.
Lemma D_1d15f0 : decode_any W_1d15f0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15f4 : bv 32 := 0x01010113.
Lemma F_1d15f4 : fetch_word AsanUbsan.M.loaded_segments (0x1d15e0 : word) = Some W_1d15f4.
Proof. vm_refl. Qed.
Lemma D_1d15f4 : decode_any W_1d15f4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d15f8 : bv 32 := 0x00008067.
Lemma F_1d15f8 : fetch_word AsanUbsan.M.loaded_segments (0x1d15e4 : word) = Some W_1d15f8.
Proof. vm_refl. Qed.
Lemma D_1d15f8 : decode_any W_1d15f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
