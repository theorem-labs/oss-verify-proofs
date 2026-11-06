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
From OSSVerify.zstd.zstd_frame_info.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_92524 : bv 32 := 0x0e060a63.
Lemma F_92524 : fetch_word Asan.M.loaded_segments (0x92568 : word) = Some W_92524.
Proof. vm_refl. Qed.
Lemma D_92524 : decode_any W_92524 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92528 : bv 32 := 0x00b50023.
Lemma F_92528 : fetch_word Asan.M.loaded_segments (0x9256c : word) = Some W_92528.
Proof. vm_refl. Qed.
Lemma D_92528 : decode_any W_92528 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9252c : bv 32 := 0x00c506b3.
Lemma F_9252c : fetch_word Asan.M.loaded_segments (0x92570 : word) = Some W_9252c.
Proof. vm_refl. Qed.
Lemma D_9252c : decode_any W_9252c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92530 : bv 32 := 0x00300713.
Lemma F_92530 : fetch_word Asan.M.loaded_segments (0x92574 : word) = Some W_92530.
Proof. vm_refl. Qed.
Lemma D_92530 : decode_any W_92530 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92534 : bv 32 := 0xfeb68fa3.
Lemma F_92534 : fetch_word Asan.M.loaded_segments (0x92578 : word) = Some W_92534.
Proof. vm_refl. Qed.
Lemma D_92534 : decode_any W_92534 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92538 : bv 32 := 0x0ee66063.
Lemma F_92538 : fetch_word Asan.M.loaded_segments (0x9257c : word) = Some W_92538.
Proof. vm_refl. Qed.
Lemma D_92538 : decode_any W_92538 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9253c : bv 32 := 0x00b500a3.
Lemma F_9253c : fetch_word Asan.M.loaded_segments (0x92580 : word) = Some W_9253c.
Proof. vm_refl. Qed.
Lemma D_9253c : decode_any W_9253c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92540 : bv 32 := 0x00b50123.
Lemma F_92540 : fetch_word Asan.M.loaded_segments (0x92584 : word) = Some W_92540.
Proof. vm_refl. Qed.
Lemma D_92540 : decode_any W_92540 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92544 : bv 32 := 0x00700713.
Lemma F_92544 : fetch_word Asan.M.loaded_segments (0x92588 : word) = Some W_92544.
Proof. vm_refl. Qed.
Lemma D_92544 : decode_any W_92544 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92548 : bv 32 := 0xfeb68ea3.
Lemma F_92548 : fetch_word Asan.M.loaded_segments (0x9258c : word) = Some W_92548.
Proof. vm_refl. Qed.
Lemma D_92548 : decode_any W_92548 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9254c : bv 32 := 0xfeb68f23.
Lemma F_9254c : fetch_word Asan.M.loaded_segments (0x92590 : word) = Some W_9254c.
Proof. vm_refl. Qed.
Lemma D_9254c : decode_any W_9254c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92550 : bv 32 := 0x0ce66463.
Lemma F_92550 : fetch_word Asan.M.loaded_segments (0x92594 : word) = Some W_92550.
Proof. vm_refl. Qed.
Lemma D_92550 : decode_any W_92550 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92554 : bv 32 := 0x00b501a3.
Lemma F_92554 : fetch_word Asan.M.loaded_segments (0x92598 : word) = Some W_92554.
Proof. vm_refl. Qed.
Lemma D_92554 : decode_any W_92554 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92558 : bv 32 := 0x00900793.
Lemma F_92558 : fetch_word Asan.M.loaded_segments (0x9259c : word) = Some W_92558.
Proof. vm_refl. Qed.
Lemma D_92558 : decode_any W_92558 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9255c : bv 32 := 0xfeb68e23.
Lemma F_9255c : fetch_word Asan.M.loaded_segments (0x925a0 : word) = Some W_9255c.
Proof. vm_refl. Qed.
Lemma D_9255c : decode_any W_9255c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92560 : bv 32 := 0x0af66c63.
Lemma F_92560 : fetch_word Asan.M.loaded_segments (0x925a4 : word) = Some W_92560.
Proof. vm_refl. Qed.
Lemma D_92560 : decode_any W_92560 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92564 : bv 32 := 0x40a006bb.
Lemma F_92564 : fetch_word Asan.M.loaded_segments (0x925a8 : word) = Some W_92564.
Proof. vm_refl. Qed.
Lemma D_92564 : decode_any W_92564 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92568 : bv 32 := 0x03859813.
Lemma F_92568 : fetch_word Asan.M.loaded_segments (0x925ac : word) = Some W_92568.
Proof. vm_refl. Qed.
Lemma D_92568 : decode_any W_92568 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9256c : bv 32 := 0x101015b7.
Lemma F_9256c : fetch_word Asan.M.loaded_segments (0x925b0 : word) = Some W_9256c.
Proof. vm_refl. Qed.
Lemma D_9256c : decode_any W_9256c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92570 : bv 32 := 0x0036f693.
Lemma F_92570 : fetch_word Asan.M.loaded_segments (0x925b4 : word) = Some W_92570.
Proof. vm_refl. Qed.
Lemma D_92570 : decode_any W_92570 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92574 : bv 32 := 0x00459713.
Lemma F_92574 : fetch_word Asan.M.loaded_segments (0x925b8 : word) = Some W_92574.
Proof. vm_refl. Qed.
Lemma D_92574 : decode_any W_92574 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92578 : bv 32 := 0x40d60633.
Lemma F_92578 : fetch_word Asan.M.loaded_segments (0x925bc : word) = Some W_92578.
Proof. vm_refl. Qed.
Lemma D_92578 : decode_any W_92578 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9257c : bv 32 := 0x00d505b3.
Lemma F_9257c : fetch_word Asan.M.loaded_segments (0x925c0 : word) = Some W_9257c.
Proof. vm_refl. Qed.
Lemma D_9257c : decode_any W_9257c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92580 : bv 32 := 0x10070693.
Lemma F_92580 : fetch_word Asan.M.loaded_segments (0x925c4 : word) = Some W_92580.
Proof. vm_refl. Qed.
Lemma D_92580 : decode_any W_92580 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92584 : bv 32 := 0xffc67713.
Lemma F_92584 : fetch_word Asan.M.loaded_segments (0x925c8 : word) = Some W_92584.
Proof. vm_refl. Qed.
Lemma D_92584 : decode_any W_92584 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92588 : bv 32 := 0x02d83633.
Lemma F_92588 : fetch_word Asan.M.loaded_segments (0x925cc : word) = Some W_92588.
Proof. vm_refl. Qed.
Lemma D_92588 : decode_any W_92588 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9258c : bv 32 := 0x00c5a023.
Lemma F_9258c : fetch_word Asan.M.loaded_segments (0x925d0 : word) = Some W_9258c.
Proof. vm_refl. Qed.
Lemma D_9258c : decode_any W_9258c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92590 : bv 32 := 0x00e586b3.
Lemma F_92590 : fetch_word Asan.M.loaded_segments (0x925d4 : word) = Some W_92590.
Proof. vm_refl. Qed.
Lemma D_92590 : decode_any W_92590 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92594 : bv 32 := 0xfec6ae23.
Lemma F_92594 : fetch_word Asan.M.loaded_segments (0x925d8 : word) = Some W_92594.
Proof. vm_refl. Qed.
Lemma D_92594 : decode_any W_92594 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92598 : bv 32 := 0x08f76063.
Lemma F_92598 : fetch_word Asan.M.loaded_segments (0x925dc : word) = Some W_92598.
Proof. vm_refl. Qed.
Lemma D_92598 : decode_any W_92598 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9259c : bv 32 := 0x00c5a223.
Lemma F_9259c : fetch_word Asan.M.loaded_segments (0x925e0 : word) = Some W_9259c.
Proof. vm_refl. Qed.
Lemma D_9259c : decode_any W_9259c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925a0 : bv 32 := 0x00c5a423.
Lemma F_925a0 : fetch_word Asan.M.loaded_segments (0x925e4 : word) = Some W_925a0.
Proof. vm_refl. Qed.
Lemma D_925a0 : decode_any W_925a0 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925a4 : bv 32 := 0x01900793.
Lemma F_925a4 : fetch_word Asan.M.loaded_segments (0x925e8 : word) = Some W_925a4.
Proof. vm_refl. Qed.
Lemma D_925a4 : decode_any W_925a4 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925a8 : bv 32 := 0xfec6aa23.
Lemma F_925a8 : fetch_word Asan.M.loaded_segments (0x925ec : word) = Some W_925a8.
Proof. vm_refl. Qed.
Lemma D_925a8 : decode_any W_925a8 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925ac : bv 32 := 0xfec6ac23.
Lemma F_925ac : fetch_word Asan.M.loaded_segments (0x925f0 : word) = Some W_925ac.
Proof. vm_refl. Qed.
Lemma D_925ac : decode_any W_925ac = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925b0 : bv 32 := 0x06f76463.
Lemma F_925b0 : fetch_word Asan.M.loaded_segments (0x925f4 : word) = Some W_925b0.
Proof. vm_refl. Qed.
Lemma D_925b0 : decode_any W_925b0 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925b4 : bv 32 := 0x00c5a623.
Lemma F_925b4 : fetch_word Asan.M.loaded_segments (0x925f8 : word) = Some W_925b4.
Proof. vm_refl. Qed.
Lemma D_925b4 : decode_any W_925b4 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925b8 : bv 32 := 0x00c5a823.
Lemma F_925b8 : fetch_word Asan.M.loaded_segments (0x925fc : word) = Some W_925b8.
Proof. vm_refl. Qed.
Lemma D_925b8 : decode_any W_925b8 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925bc : bv 32 := 0x00c5aa23.
Lemma F_925bc : fetch_word Asan.M.loaded_segments (0x92600 : word) = Some W_925bc.
Proof. vm_refl. Qed.
Lemma D_925bc : decode_any W_925bc = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925c0 : bv 32 := 0x00c5ac23.
Lemma F_925c0 : fetch_word Asan.M.loaded_segments (0x92604 : word) = Some W_925c0.
Proof. vm_refl. Qed.
Lemma D_925c0 : decode_any W_925c0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925c4 : bv 32 := 0x0045f793.
Lemma F_925c4 : fetch_word Asan.M.loaded_segments (0x92608 : word) = Some W_925c4.
Proof. vm_refl. Qed.
Lemma D_925c4 : decode_any W_925c4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925c8 : bv 32 := 0x02000813.
Lemma F_925c8 : fetch_word Asan.M.loaded_segments (0x9260c : word) = Some W_925c8.
Proof. vm_refl. Qed.
Lemma D_925c8 : decode_any W_925c8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925cc : bv 32 := 0x01878793.
Lemma F_925cc : fetch_word Asan.M.loaded_segments (0x92610 : word) = Some W_925cc.
Proof. vm_refl. Qed.
Lemma D_925cc : decode_any W_925cc = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925d0 : bv 32 := 0x40f70733.
Lemma F_925d0 : fetch_word Asan.M.loaded_segments (0x92614 : word) = Some W_925d0.
Proof. vm_refl. Qed.
Lemma D_925d0 : decode_any W_925d0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925d4 : bv 32 := 0xfec6a223.
Lemma F_925d4 : fetch_word Asan.M.loaded_segments (0x92618 : word) = Some W_925d4.
Proof. vm_refl. Qed.
Lemma D_925d4 : decode_any W_925d4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925d8 : bv 32 := 0xfec6a423.
Lemma F_925d8 : fetch_word Asan.M.loaded_segments (0x9261c : word) = Some W_925d8.
Proof. vm_refl. Qed.
Lemma D_925d8 : decode_any W_925d8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925dc : bv 32 := 0xfec6a623.
Lemma F_925dc : fetch_word Asan.M.loaded_segments (0x92620 : word) = Some W_925dc.
Proof. vm_refl. Qed.
Lemma D_925dc : decode_any W_925dc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925e0 : bv 32 := 0xfec6a823.
Lemma F_925e0 : fetch_word Asan.M.loaded_segments (0x92624 : word) = Some W_925e0.
Proof. vm_refl. Qed.
Lemma D_925e0 : decode_any W_925e0 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925e4 : bv 32 := 0x03076a63.
Lemma F_925e4 : fetch_word Asan.M.loaded_segments (0x92628 : word) = Some W_925e4.
Proof. vm_refl. Qed.
Lemma D_925e4 : decode_any W_925e4 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925e8 : bv 32 := 0x02061613.
Lemma F_925e8 : fetch_word Asan.M.loaded_segments (0x9262c : word) = Some W_925e8.
Proof. vm_refl. Qed.
Lemma D_925e8 : decode_any W_925e8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925ec : bv 32 := 0x00f585b3.
Lemma F_925ec : fetch_word Asan.M.loaded_segments (0x92630 : word) = Some W_925ec.
Proof. vm_refl. Qed.
Lemma D_925ec : decode_any W_925ec = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925f0 : bv 32 := 0x02065693.
Lemma F_925f0 : fetch_word Asan.M.loaded_segments (0x92634 : word) = Some W_925f0.
Proof. vm_refl. Qed.
Lemma D_925f0 : decode_any W_925f0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925f4 : bv 32 := 0x00d66633.
Lemma F_925f4 : fetch_word Asan.M.loaded_segments (0x92638 : word) = Some W_925f4.
Proof. vm_refl. Qed.
Lemma D_925f4 : decode_any W_925f4 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925f8 : bv 32 := 0x01f00693.
Lemma F_925f8 : fetch_word Asan.M.loaded_segments (0x9263c : word) = Some W_925f8.
Proof. vm_refl. Qed.
Lemma D_925f8 : decode_any W_925f8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925fc : bv 32 := 0x00c5b023.
Lemma F_925fc : fetch_word Asan.M.loaded_segments (0x92640 : word) = Some W_925fc.
Proof. vm_refl. Qed.
Lemma D_925fc : decode_any W_925fc = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92600 : bv 32 := 0x00c5b423.
Lemma F_92600 : fetch_word Asan.M.loaded_segments (0x92644 : word) = Some W_92600.
Proof. vm_refl. Qed.
Lemma D_92600 : decode_any W_92600 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92604 : bv 32 := 0x00c5b823.
Lemma F_92604 : fetch_word Asan.M.loaded_segments (0x92648 : word) = Some W_92604.
Proof. vm_refl. Qed.
Lemma D_92604 : decode_any W_92604 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92608 : bv 32 := 0x00c5bc23.
Lemma F_92608 : fetch_word Asan.M.loaded_segments (0x9264c : word) = Some W_92608.
Proof. vm_refl. Qed.
Lemma D_92608 : decode_any W_92608 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9260c : bv 32 := 0xfe070713.
Lemma F_9260c : fetch_word Asan.M.loaded_segments (0x92650 : word) = Some W_9260c.
Proof. vm_refl. Qed.
Lemma D_9260c : decode_any W_9260c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92610 : bv 32 := 0x02058593.
Lemma F_92610 : fetch_word Asan.M.loaded_segments (0x92654 : word) = Some W_92610.
Proof. vm_refl. Qed.
Lemma D_92610 : decode_any W_92610 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92614 : bv 32 := 0xfee6e4e3.
Lemma F_92614 : fetch_word Asan.M.loaded_segments (0x92658 : word) = Some W_92614.
Proof. vm_refl. Qed.
Lemma D_92614 : decode_any W_92614 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92618 : bv 32 := 0x00008067.
Lemma F_92618 : fetch_word Asan.M.loaded_segments (0x9265c : word) = Some W_92618.
Proof. vm_refl. Qed.
Lemma D_92618 : decode_any W_92618 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x92568%Z.
Definition Fo_000 := F_92524.
Definition Do_000 := D_92524.
Definition Fo_004 := F_92528.
Definition Do_004 := D_92528.
Definition Fo_008 := F_9252c.
Definition Do_008 := D_9252c.
Definition Fo_00c := F_92530.
Definition Do_00c := D_92530.
Definition Fo_010 := F_92534.
Definition Do_010 := D_92534.
Definition Fo_014 := F_92538.
Definition Do_014 := D_92538.
Definition Fo_018 := F_9253c.
Definition Do_018 := D_9253c.
Definition Fo_01c := F_92540.
Definition Do_01c := D_92540.
Definition Fo_020 := F_92544.
Definition Do_020 := D_92544.
Definition Fo_024 := F_92548.
Definition Do_024 := D_92548.
Definition Fo_028 := F_9254c.
Definition Do_028 := D_9254c.
Definition Fo_02c := F_92550.
Definition Do_02c := D_92550.
Definition Fo_030 := F_92554.
Definition Do_030 := D_92554.
Definition Fo_034 := F_92558.
Definition Do_034 := D_92558.
Definition Fo_038 := F_9255c.
Definition Do_038 := D_9255c.
Definition Fo_03c := F_92560.
Definition Do_03c := D_92560.
Definition Fo_040 := F_92564.
Definition Do_040 := D_92564.
Definition Fo_044 := F_92568.
Definition Do_044 := D_92568.
Definition Fo_048 := F_9256c.
Definition Do_048 := D_9256c.
Definition Fo_04c := F_92570.
Definition Do_04c := D_92570.
Definition Fo_050 := F_92574.
Definition Do_050 := D_92574.
Definition Fo_054 := F_92578.
Definition Do_054 := D_92578.
Definition Fo_058 := F_9257c.
Definition Do_058 := D_9257c.
Definition Fo_05c := F_92580.
Definition Do_05c := D_92580.
Definition Fo_060 := F_92584.
Definition Do_060 := D_92584.
Definition Fo_064 := F_92588.
Definition Do_064 := D_92588.
Definition Fo_068 := F_9258c.
Definition Do_068 := D_9258c.
Definition Fo_06c := F_92590.
Definition Do_06c := D_92590.
Definition Fo_070 := F_92594.
Definition Do_070 := D_92594.
Definition Fo_074 := F_92598.
Definition Do_074 := D_92598.
Definition Fo_078 := F_9259c.
Definition Do_078 := D_9259c.
Definition Fo_07c := F_925a0.
Definition Do_07c := D_925a0.
Definition Fo_080 := F_925a4.
Definition Do_080 := D_925a4.
Definition Fo_084 := F_925a8.
Definition Do_084 := D_925a8.
Definition Fo_088 := F_925ac.
Definition Do_088 := D_925ac.
Definition Fo_08c := F_925b0.
Definition Do_08c := D_925b0.
Definition Fo_090 := F_925b4.
Definition Do_090 := D_925b4.
Definition Fo_094 := F_925b8.
Definition Do_094 := D_925b8.
Definition Fo_098 := F_925bc.
Definition Do_098 := D_925bc.
Definition Fo_09c := F_925c0.
Definition Do_09c := D_925c0.
Definition Fo_0a0 := F_925c4.
Definition Do_0a0 := D_925c4.
Definition Fo_0a4 := F_925c8.
Definition Do_0a4 := D_925c8.
Definition Fo_0a8 := F_925cc.
Definition Do_0a8 := D_925cc.
Definition Fo_0ac := F_925d0.
Definition Do_0ac := D_925d0.
Definition Fo_0b0 := F_925d4.
Definition Do_0b0 := D_925d4.
Definition Fo_0b4 := F_925d8.
Definition Do_0b4 := D_925d8.
Definition Fo_0b8 := F_925dc.
Definition Do_0b8 := D_925dc.
Definition Fo_0bc := F_925e0.
Definition Do_0bc := D_925e0.
Definition Fo_0c0 := F_925e4.
Definition Do_0c0 := D_925e4.
Definition Fo_0c4 := F_925e8.
Definition Do_0c4 := D_925e8.
Definition Fo_0c8 := F_925ec.
Definition Do_0c8 := D_925ec.
Definition Fo_0cc := F_925f0.
Definition Do_0cc := D_925f0.
Definition Fo_0d0 := F_925f4.
Definition Do_0d0 := D_925f4.
Definition Fo_0d4 := F_925f8.
Definition Do_0d4 := D_925f8.
Definition Fo_0d8 := F_925fc.
Definition Do_0d8 := D_925fc.
Definition Fo_0dc := F_92600.
Definition Do_0dc := D_92600.
Definition Fo_0e0 := F_92604.
Definition Do_0e0 := D_92604.
Definition Fo_0e4 := F_92608.
Definition Do_0e4 := D_92608.
Definition Fo_0e8 := F_9260c.
Definition Do_0e8 := D_9260c.
Definition Fo_0ec := F_92610.
Definition Do_0ec := D_92610.
Definition Fo_0f0 := F_92614.
Definition Do_0f0 := D_92614.
Definition Fo_0f4 := F_92618.
Definition Do_0f4 := D_92618.
