(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_158508 : bv 32 := 0x0e060a63.
Lemma F_158508 : fetch_word Asan.M.loaded_segments (0x158858 : word) = Some W_158508.
Proof. vm_refl. Qed.
Lemma D_158508 : decode_any W_158508 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850c : bv 32 := 0x00b50023.
Lemma F_15850c : fetch_word Asan.M.loaded_segments (0x15885c : word) = Some W_15850c.
Proof. vm_refl. Qed.
Lemma D_15850c : decode_any W_15850c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158510 : bv 32 := 0x00c506b3.
Lemma F_158510 : fetch_word Asan.M.loaded_segments (0x158860 : word) = Some W_158510.
Proof. vm_refl. Qed.
Lemma D_158510 : decode_any W_158510 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158514 : bv 32 := 0x00300713.
Lemma F_158514 : fetch_word Asan.M.loaded_segments (0x158864 : word) = Some W_158514.
Proof. vm_refl. Qed.
Lemma D_158514 : decode_any W_158514 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158518 : bv 32 := 0xfeb68fa3.
Lemma F_158518 : fetch_word Asan.M.loaded_segments (0x158868 : word) = Some W_158518.
Proof. vm_refl. Qed.
Lemma D_158518 : decode_any W_158518 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15851c : bv 32 := 0x0ee66063.
Lemma F_15851c : fetch_word Asan.M.loaded_segments (0x15886c : word) = Some W_15851c.
Proof. vm_refl. Qed.
Lemma D_15851c : decode_any W_15851c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158520 : bv 32 := 0x00b500a3.
Lemma F_158520 : fetch_word Asan.M.loaded_segments (0x158870 : word) = Some W_158520.
Proof. vm_refl. Qed.
Lemma D_158520 : decode_any W_158520 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158524 : bv 32 := 0x00b50123.
Lemma F_158524 : fetch_word Asan.M.loaded_segments (0x158874 : word) = Some W_158524.
Proof. vm_refl. Qed.
Lemma D_158524 : decode_any W_158524 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158528 : bv 32 := 0x00700713.
Lemma F_158528 : fetch_word Asan.M.loaded_segments (0x158878 : word) = Some W_158528.
Proof. vm_refl. Qed.
Lemma D_158528 : decode_any W_158528 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15852c : bv 32 := 0xfeb68ea3.
Lemma F_15852c : fetch_word Asan.M.loaded_segments (0x15887c : word) = Some W_15852c.
Proof. vm_refl. Qed.
Lemma D_15852c : decode_any W_15852c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158530 : bv 32 := 0xfeb68f23.
Lemma F_158530 : fetch_word Asan.M.loaded_segments (0x158880 : word) = Some W_158530.
Proof. vm_refl. Qed.
Lemma D_158530 : decode_any W_158530 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158534 : bv 32 := 0x0ce66463.
Lemma F_158534 : fetch_word Asan.M.loaded_segments (0x158884 : word) = Some W_158534.
Proof. vm_refl. Qed.
Lemma D_158534 : decode_any W_158534 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158538 : bv 32 := 0x00b501a3.
Lemma F_158538 : fetch_word Asan.M.loaded_segments (0x158888 : word) = Some W_158538.
Proof. vm_refl. Qed.
Lemma D_158538 : decode_any W_158538 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15853c : bv 32 := 0x00900793.
Lemma F_15853c : fetch_word Asan.M.loaded_segments (0x15888c : word) = Some W_15853c.
Proof. vm_refl. Qed.
Lemma D_15853c : decode_any W_15853c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158540 : bv 32 := 0xfeb68e23.
Lemma F_158540 : fetch_word Asan.M.loaded_segments (0x158890 : word) = Some W_158540.
Proof. vm_refl. Qed.
Lemma D_158540 : decode_any W_158540 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158544 : bv 32 := 0x0af66c63.
Lemma F_158544 : fetch_word Asan.M.loaded_segments (0x158894 : word) = Some W_158544.
Proof. vm_refl. Qed.
Lemma D_158544 : decode_any W_158544 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158548 : bv 32 := 0x40a006bb.
Lemma F_158548 : fetch_word Asan.M.loaded_segments (0x158898 : word) = Some W_158548.
Proof. vm_refl. Qed.
Lemma D_158548 : decode_any W_158548 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854c : bv 32 := 0x03859813.
Lemma F_15854c : fetch_word Asan.M.loaded_segments (0x15889c : word) = Some W_15854c.
Proof. vm_refl. Qed.
Lemma D_15854c : decode_any W_15854c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158550 : bv 32 := 0x101015b7.
Lemma F_158550 : fetch_word Asan.M.loaded_segments (0x1588a0 : word) = Some W_158550.
Proof. vm_refl. Qed.
Lemma D_158550 : decode_any W_158550 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158554 : bv 32 := 0x0036f693.
Lemma F_158554 : fetch_word Asan.M.loaded_segments (0x1588a4 : word) = Some W_158554.
Proof. vm_refl. Qed.
Lemma D_158554 : decode_any W_158554 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158558 : bv 32 := 0x00459713.
Lemma F_158558 : fetch_word Asan.M.loaded_segments (0x1588a8 : word) = Some W_158558.
Proof. vm_refl. Qed.
Lemma D_158558 : decode_any W_158558 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15855c : bv 32 := 0x40d60633.
Lemma F_15855c : fetch_word Asan.M.loaded_segments (0x1588ac : word) = Some W_15855c.
Proof. vm_refl. Qed.
Lemma D_15855c : decode_any W_15855c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158560 : bv 32 := 0x00d505b3.
Lemma F_158560 : fetch_word Asan.M.loaded_segments (0x1588b0 : word) = Some W_158560.
Proof. vm_refl. Qed.
Lemma D_158560 : decode_any W_158560 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158564 : bv 32 := 0x10070693.
Lemma F_158564 : fetch_word Asan.M.loaded_segments (0x1588b4 : word) = Some W_158564.
Proof. vm_refl. Qed.
Lemma D_158564 : decode_any W_158564 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158568 : bv 32 := 0xffc67713.
Lemma F_158568 : fetch_word Asan.M.loaded_segments (0x1588b8 : word) = Some W_158568.
Proof. vm_refl. Qed.
Lemma D_158568 : decode_any W_158568 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15856c : bv 32 := 0x02d83633.
Lemma F_15856c : fetch_word Asan.M.loaded_segments (0x1588bc : word) = Some W_15856c.
Proof. vm_refl. Qed.
Lemma D_15856c : decode_any W_15856c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158570 : bv 32 := 0x00c5a023.
Lemma F_158570 : fetch_word Asan.M.loaded_segments (0x1588c0 : word) = Some W_158570.
Proof. vm_refl. Qed.
Lemma D_158570 : decode_any W_158570 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158574 : bv 32 := 0x00e586b3.
Lemma F_158574 : fetch_word Asan.M.loaded_segments (0x1588c4 : word) = Some W_158574.
Proof. vm_refl. Qed.
Lemma D_158574 : decode_any W_158574 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158578 : bv 32 := 0xfec6ae23.
Lemma F_158578 : fetch_word Asan.M.loaded_segments (0x1588c8 : word) = Some W_158578.
Proof. vm_refl. Qed.
Lemma D_158578 : decode_any W_158578 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15857c : bv 32 := 0x08f76063.
Lemma F_15857c : fetch_word Asan.M.loaded_segments (0x1588cc : word) = Some W_15857c.
Proof. vm_refl. Qed.
Lemma D_15857c : decode_any W_15857c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158580 : bv 32 := 0x00c5a223.
Lemma F_158580 : fetch_word Asan.M.loaded_segments (0x1588d0 : word) = Some W_158580.
Proof. vm_refl. Qed.
Lemma D_158580 : decode_any W_158580 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158584 : bv 32 := 0x00c5a423.
Lemma F_158584 : fetch_word Asan.M.loaded_segments (0x1588d4 : word) = Some W_158584.
Proof. vm_refl. Qed.
Lemma D_158584 : decode_any W_158584 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158588 : bv 32 := 0x01900793.
Lemma F_158588 : fetch_word Asan.M.loaded_segments (0x1588d8 : word) = Some W_158588.
Proof. vm_refl. Qed.
Lemma D_158588 : decode_any W_158588 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15858c : bv 32 := 0xfec6aa23.
Lemma F_15858c : fetch_word Asan.M.loaded_segments (0x1588dc : word) = Some W_15858c.
Proof. vm_refl. Qed.
Lemma D_15858c : decode_any W_15858c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158590 : bv 32 := 0xfec6ac23.
Lemma F_158590 : fetch_word Asan.M.loaded_segments (0x1588e0 : word) = Some W_158590.
Proof. vm_refl. Qed.
Lemma D_158590 : decode_any W_158590 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158594 : bv 32 := 0x06f76463.
Lemma F_158594 : fetch_word Asan.M.loaded_segments (0x1588e4 : word) = Some W_158594.
Proof. vm_refl. Qed.
Lemma D_158594 : decode_any W_158594 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_158598 : bv 32 := 0x00c5a623.
Lemma F_158598 : fetch_word Asan.M.loaded_segments (0x1588e8 : word) = Some W_158598.
Proof. vm_refl. Qed.
Lemma D_158598 : decode_any W_158598 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15859c : bv 32 := 0x00c5a823.
Lemma F_15859c : fetch_word Asan.M.loaded_segments (0x1588ec : word) = Some W_15859c.
Proof. vm_refl. Qed.
Lemma D_15859c : decode_any W_15859c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585a0 : bv 32 := 0x00c5aa23.
Lemma F_1585a0 : fetch_word Asan.M.loaded_segments (0x1588f0 : word) = Some W_1585a0.
Proof. vm_refl. Qed.
Lemma D_1585a0 : decode_any W_1585a0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585a4 : bv 32 := 0x00c5ac23.
Lemma F_1585a4 : fetch_word Asan.M.loaded_segments (0x1588f4 : word) = Some W_1585a4.
Proof. vm_refl. Qed.
Lemma D_1585a4 : decode_any W_1585a4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585a8 : bv 32 := 0x0045f793.
Lemma F_1585a8 : fetch_word Asan.M.loaded_segments (0x1588f8 : word) = Some W_1585a8.
Proof. vm_refl. Qed.
Lemma D_1585a8 : decode_any W_1585a8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585ac : bv 32 := 0x02000813.
Lemma F_1585ac : fetch_word Asan.M.loaded_segments (0x1588fc : word) = Some W_1585ac.
Proof. vm_refl. Qed.
Lemma D_1585ac : decode_any W_1585ac = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585b0 : bv 32 := 0x01878793.
Lemma F_1585b0 : fetch_word Asan.M.loaded_segments (0x158900 : word) = Some W_1585b0.
Proof. vm_refl. Qed.
Lemma D_1585b0 : decode_any W_1585b0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585b4 : bv 32 := 0x40f70733.
Lemma F_1585b4 : fetch_word Asan.M.loaded_segments (0x158904 : word) = Some W_1585b4.
Proof. vm_refl. Qed.
Lemma D_1585b4 : decode_any W_1585b4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585b8 : bv 32 := 0xfec6a223.
Lemma F_1585b8 : fetch_word Asan.M.loaded_segments (0x158908 : word) = Some W_1585b8.
Proof. vm_refl. Qed.
Lemma D_1585b8 : decode_any W_1585b8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585bc : bv 32 := 0xfec6a423.
Lemma F_1585bc : fetch_word Asan.M.loaded_segments (0x15890c : word) = Some W_1585bc.
Proof. vm_refl. Qed.
Lemma D_1585bc : decode_any W_1585bc = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c0 : bv 32 := 0xfec6a623.
Lemma F_1585c0 : fetch_word Asan.M.loaded_segments (0x158910 : word) = Some W_1585c0.
Proof. vm_refl. Qed.
Lemma D_1585c0 : decode_any W_1585c0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c4 : bv 32 := 0xfec6a823.
Lemma F_1585c4 : fetch_word Asan.M.loaded_segments (0x158914 : word) = Some W_1585c4.
Proof. vm_refl. Qed.
Lemma D_1585c4 : decode_any W_1585c4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c8 : bv 32 := 0x03076a63.
Lemma F_1585c8 : fetch_word Asan.M.loaded_segments (0x158918 : word) = Some W_1585c8.
Proof. vm_refl. Qed.
Lemma D_1585c8 : decode_any W_1585c8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585cc : bv 32 := 0x02061613.
Lemma F_1585cc : fetch_word Asan.M.loaded_segments (0x15891c : word) = Some W_1585cc.
Proof. vm_refl. Qed.
Lemma D_1585cc : decode_any W_1585cc = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585d0 : bv 32 := 0x00f585b3.
Lemma F_1585d0 : fetch_word Asan.M.loaded_segments (0x158920 : word) = Some W_1585d0.
Proof. vm_refl. Qed.
Lemma D_1585d0 : decode_any W_1585d0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585d4 : bv 32 := 0x02065693.
Lemma F_1585d4 : fetch_word Asan.M.loaded_segments (0x158924 : word) = Some W_1585d4.
Proof. vm_refl. Qed.
Lemma D_1585d4 : decode_any W_1585d4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585d8 : bv 32 := 0x00d66633.
Lemma F_1585d8 : fetch_word Asan.M.loaded_segments (0x158928 : word) = Some W_1585d8.
Proof. vm_refl. Qed.
Lemma D_1585d8 : decode_any W_1585d8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585dc : bv 32 := 0x01f00693.
Lemma F_1585dc : fetch_word Asan.M.loaded_segments (0x15892c : word) = Some W_1585dc.
Proof. vm_refl. Qed.
Lemma D_1585dc : decode_any W_1585dc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585e0 : bv 32 := 0x00c5b023.
Lemma F_1585e0 : fetch_word Asan.M.loaded_segments (0x158930 : word) = Some W_1585e0.
Proof. vm_refl. Qed.
Lemma D_1585e0 : decode_any W_1585e0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585e4 : bv 32 := 0x00c5b423.
Lemma F_1585e4 : fetch_word Asan.M.loaded_segments (0x158934 : word) = Some W_1585e4.
Proof. vm_refl. Qed.
Lemma D_1585e4 : decode_any W_1585e4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585e8 : bv 32 := 0x00c5b823.
Lemma F_1585e8 : fetch_word Asan.M.loaded_segments (0x158938 : word) = Some W_1585e8.
Proof. vm_refl. Qed.
Lemma D_1585e8 : decode_any W_1585e8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585ec : bv 32 := 0x00c5bc23.
Lemma F_1585ec : fetch_word Asan.M.loaded_segments (0x15893c : word) = Some W_1585ec.
Proof. vm_refl. Qed.
Lemma D_1585ec : decode_any W_1585ec = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585f0 : bv 32 := 0xfe070713.
Lemma F_1585f0 : fetch_word Asan.M.loaded_segments (0x158940 : word) = Some W_1585f0.
Proof. vm_refl. Qed.
Lemma D_1585f0 : decode_any W_1585f0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585f4 : bv 32 := 0x02058593.
Lemma F_1585f4 : fetch_word Asan.M.loaded_segments (0x158944 : word) = Some W_1585f4.
Proof. vm_refl. Qed.
Lemma D_1585f4 : decode_any W_1585f4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585f8 : bv 32 := 0xfee6e4e3.
Lemma F_1585f8 : fetch_word Asan.M.loaded_segments (0x158948 : word) = Some W_1585f8.
Proof. vm_refl. Qed.
Lemma D_1585f8 : decode_any W_1585f8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585fc : bv 32 := 0x00008067.
Lemma F_1585fc : fetch_word Asan.M.loaded_segments (0x15894c : word) = Some W_1585fc.
Proof. vm_refl. Qed.
Lemma D_1585fc : decode_any W_1585fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x158858%Z.
Definition Fo_000 := F_158508.
Definition Do_000 := D_158508.
Definition Fo_004 := F_15850c.
Definition Do_004 := D_15850c.
Definition Fo_008 := F_158510.
Definition Do_008 := D_158510.
Definition Fo_00c := F_158514.
Definition Do_00c := D_158514.
Definition Fo_010 := F_158518.
Definition Do_010 := D_158518.
Definition Fo_014 := F_15851c.
Definition Do_014 := D_15851c.
Definition Fo_018 := F_158520.
Definition Do_018 := D_158520.
Definition Fo_01c := F_158524.
Definition Do_01c := D_158524.
Definition Fo_020 := F_158528.
Definition Do_020 := D_158528.
Definition Fo_024 := F_15852c.
Definition Do_024 := D_15852c.
Definition Fo_028 := F_158530.
Definition Do_028 := D_158530.
Definition Fo_02c := F_158534.
Definition Do_02c := D_158534.
Definition Fo_030 := F_158538.
Definition Do_030 := D_158538.
Definition Fo_034 := F_15853c.
Definition Do_034 := D_15853c.
Definition Fo_038 := F_158540.
Definition Do_038 := D_158540.
Definition Fo_03c := F_158544.
Definition Do_03c := D_158544.
Definition Fo_040 := F_158548.
Definition Do_040 := D_158548.
Definition Fo_044 := F_15854c.
Definition Do_044 := D_15854c.
Definition Fo_048 := F_158550.
Definition Do_048 := D_158550.
Definition Fo_04c := F_158554.
Definition Do_04c := D_158554.
Definition Fo_050 := F_158558.
Definition Do_050 := D_158558.
Definition Fo_054 := F_15855c.
Definition Do_054 := D_15855c.
Definition Fo_058 := F_158560.
Definition Do_058 := D_158560.
Definition Fo_05c := F_158564.
Definition Do_05c := D_158564.
Definition Fo_060 := F_158568.
Definition Do_060 := D_158568.
Definition Fo_064 := F_15856c.
Definition Do_064 := D_15856c.
Definition Fo_068 := F_158570.
Definition Do_068 := D_158570.
Definition Fo_06c := F_158574.
Definition Do_06c := D_158574.
Definition Fo_070 := F_158578.
Definition Do_070 := D_158578.
Definition Fo_074 := F_15857c.
Definition Do_074 := D_15857c.
Definition Fo_078 := F_158580.
Definition Do_078 := D_158580.
Definition Fo_07c := F_158584.
Definition Do_07c := D_158584.
Definition Fo_080 := F_158588.
Definition Do_080 := D_158588.
Definition Fo_084 := F_15858c.
Definition Do_084 := D_15858c.
Definition Fo_088 := F_158590.
Definition Do_088 := D_158590.
Definition Fo_08c := F_158594.
Definition Do_08c := D_158594.
Definition Fo_090 := F_158598.
Definition Do_090 := D_158598.
Definition Fo_094 := F_15859c.
Definition Do_094 := D_15859c.
Definition Fo_098 := F_1585a0.
Definition Do_098 := D_1585a0.
Definition Fo_09c := F_1585a4.
Definition Do_09c := D_1585a4.
Definition Fo_0a0 := F_1585a8.
Definition Do_0a0 := D_1585a8.
Definition Fo_0a4 := F_1585ac.
Definition Do_0a4 := D_1585ac.
Definition Fo_0a8 := F_1585b0.
Definition Do_0a8 := D_1585b0.
Definition Fo_0ac := F_1585b4.
Definition Do_0ac := D_1585b4.
Definition Fo_0b0 := F_1585b8.
Definition Do_0b0 := D_1585b8.
Definition Fo_0b4 := F_1585bc.
Definition Do_0b4 := D_1585bc.
Definition Fo_0b8 := F_1585c0.
Definition Do_0b8 := D_1585c0.
Definition Fo_0bc := F_1585c4.
Definition Do_0bc := D_1585c4.
Definition Fo_0c0 := F_1585c8.
Definition Do_0c0 := D_1585c8.
Definition Fo_0c4 := F_1585cc.
Definition Do_0c4 := D_1585cc.
Definition Fo_0c8 := F_1585d0.
Definition Do_0c8 := D_1585d0.
Definition Fo_0cc := F_1585d4.
Definition Do_0cc := D_1585d4.
Definition Fo_0d0 := F_1585d8.
Definition Do_0d0 := D_1585d8.
Definition Fo_0d4 := F_1585dc.
Definition Do_0d4 := D_1585dc.
Definition Fo_0d8 := F_1585e0.
Definition Do_0d8 := D_1585e0.
Definition Fo_0dc := F_1585e4.
Definition Do_0dc := D_1585e4.
Definition Fo_0e0 := F_1585e8.
Definition Do_0e0 := D_1585e8.
Definition Fo_0e4 := F_1585ec.
Definition Do_0e4 := D_1585ec.
Definition Fo_0e8 := F_1585f0.
Definition Do_0e8 := D_1585f0.
Definition Fo_0ec := F_1585f4.
Definition Do_0ec := D_1585f4.
Definition Fo_0f0 := F_1585f8.
Definition Do_0f0 := D_1585f8.
Definition Fo_0f4 := F_1585fc.
Definition Do_0f4 := D_1585fc.
