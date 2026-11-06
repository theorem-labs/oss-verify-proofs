(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cb62c : bv 32 := 0x0ff5f593.
Lemma F_cb62c : fetch_word Asan.M.loaded_segments (0xcb62c : word) = Some W_cb62c.
Proof. vm_refl. Qed.
Lemma D_cb62c : decode_any W_cb62c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb630 : bv 32 := 0x00757693.
Lemma F_cb630 : fetch_word Asan.M.loaded_segments (0xcb630 : word) = Some W_cb630.
Proof. vm_refl. Qed.
Lemma D_cb630 : decode_any W_cb630 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb634 : bv 32 := 0x00c03733.
Lemma F_cb634 : fetch_word Asan.M.loaded_segments (0xcb634 : word) = Some W_cb634.
Proof. vm_refl. Qed.
Lemma D_cb634 : decode_any W_cb634 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb638 : bv 32 := 0x02068c63.
Lemma F_cb638 : fetch_word Asan.M.loaded_segments (0xcb638 : word) = Some W_cb638.
Proof. vm_refl. Qed.
Lemma D_cb638 : decode_any W_cb638 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb63c : bv 32 := 0x02060a63.
Lemma F_cb63c : fetch_word Asan.M.loaded_segments (0xcb63c : word) = Some W_cb63c.
Proof. vm_refl. Qed.
Lemma D_cb63c : decode_any W_cb63c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb640 : bv 32 := 0x00150793.
Lemma F_cb640 : fetch_word Asan.M.loaded_segments (0xcb640 : word) = Some W_cb640.
Proof. vm_refl. Qed.
Lemma D_cb640 : decode_any W_cb640 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb644 : bv 32 := 0x00100813.
Lemma F_cb644 : fetch_word Asan.M.loaded_segments (0xcb644 : word) = Some W_cb644.
Proof. vm_refl. Qed.
Lemma D_cb644 : decode_any W_cb644 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb648 : bv 32 := 0x00054703.
Lemma F_cb648 : fetch_word Asan.M.loaded_segments (0xcb648 : word) = Some W_cb648.
Proof. vm_refl. Qed.
Lemma D_cb648 : decode_any W_cb648 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb64c : bv 32 := 0x00060693.
Lemma F_cb64c : fetch_word Asan.M.loaded_segments (0xcb64c : word) = Some W_cb64c.
Proof. vm_refl. Qed.
Lemma D_cb64c : decode_any W_cb64c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb650 : bv 32 := 0x06b70e63.
Lemma F_cb650 : fetch_word Asan.M.loaded_segments (0xcb650 : word) = Some W_cb650.
Proof. vm_refl. Qed.
Lemma D_cb650 : decode_any W_cb650 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb654 : bv 32 := 0x00150513.
Lemma F_cb654 : fetch_word Asan.M.loaded_segments (0xcb654 : word) = Some W_cb654.
Proof. vm_refl. Qed.
Lemma D_cb654 : decode_any W_cb654 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb658 : bv 32 := 0xfff68613.
Lemma F_cb658 : fetch_word Asan.M.loaded_segments (0xcb658 : word) = Some W_cb658.
Proof. vm_refl. Qed.
Lemma D_cb658 : decode_any W_cb658 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb65c : bv 32 := 0x0077f893.
Lemma F_cb65c : fetch_word Asan.M.loaded_segments (0xcb65c : word) = Some W_cb65c.
Proof. vm_refl. Qed.
Lemma D_cb65c : decode_any W_cb65c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb660 : bv 32 := 0x00c03733.
Lemma F_cb660 : fetch_word Asan.M.loaded_segments (0xcb660 : word) = Some W_cb660.
Proof. vm_refl. Qed.
Lemma D_cb660 : decode_any W_cb660 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb664 : bv 32 := 0x00088663.
Lemma F_cb664 : fetch_word Asan.M.loaded_segments (0xcb664 : word) = Some W_cb664.
Proof. vm_refl. Qed.
Lemma D_cb664 : decode_any W_cb664 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb668 : bv 32 := 0x00178793.
Lemma F_cb668 : fetch_word Asan.M.loaded_segments (0xcb668 : word) = Some W_cb668.
Proof. vm_refl. Qed.
Lemma D_cb668 : decode_any W_cb668 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb66c : bv 32 := 0xfd069ee3.
Lemma F_cb66c : fetch_word Asan.M.loaded_segments (0xcb66c : word) = Some W_cb66c.
Proof. vm_refl. Qed.
Lemma D_cb66c : decode_any W_cb66c = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb670 : bv 32 := 0x06070863.
Lemma F_cb670 : fetch_word Asan.M.loaded_segments (0xcb670 : word) = Some W_cb670.
Proof. vm_refl. Qed.
Lemma D_cb670 : decode_any W_cb670 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb674 : bv 32 := 0x00054683.
Lemma F_cb674 : fetch_word Asan.M.loaded_segments (0xcb674 : word) = Some W_cb674.
Proof. vm_refl. Qed.
Lemma D_cb674 : decode_any W_cb674 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb678 : bv 32 := 0x04b68663.
Lemma F_cb678 : fetch_word Asan.M.loaded_segments (0xcb678 : word) = Some W_cb678.
Proof. vm_refl. Qed.
Lemma D_cb678 : decode_any W_cb678 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb67c : bv 32 := 0x00800693.
Lemma F_cb67c : fetch_word Asan.M.loaded_segments (0xcb67c : word) = Some W_cb67c.
Proof. vm_refl. Qed.
Lemma D_cb67c : decode_any W_cb67c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb680 : bv 32 := 0x04d66263.
Lemma F_cb680 : fetch_word Asan.M.loaded_segments (0xcb680 : word) = Some W_cb680.
Proof. vm_refl. Qed.
Lemma D_cb680 : decode_any W_cb680 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb684 : bv 32 := 0xfff45697.
Lemma F_cb684 : fetch_word Asan.M.loaded_segments (0xcb684 : word) = Some W_cb684.
Proof. vm_refl. Qed.
Lemma D_cb684 : decode_any W_cb684 = Some (Auipc 13 1048389, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb688 : bv 32 := 0xd046b683.
Lemma F_cb688 : fetch_word Asan.M.loaded_segments (0xcb688 : word) = Some W_cb688.
Proof. vm_refl. Qed.
Lemma D_cb688 : decode_any W_cb688 = Some (Load SZ8 true 13 13 3332, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb68c : bv 32 := 0xfff45717.
Lemma F_cb68c : fetch_word Asan.M.loaded_segments (0xcb68c : word) = Some W_cb68c.
Proof. vm_refl. Qed.
Lemma D_cb68c : decode_any W_cb68c = Some (Auipc 14 1048389, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb690 : bv 32 := 0xce473703.
Lemma F_cb690 : fetch_word Asan.M.loaded_segments (0xcb690 : word) = Some W_cb690.
Proof. vm_refl. Qed.
Lemma D_cb690 : decode_any W_cb690 = Some (Load SZ8 true 14 14 3300, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb694 : bv 32 := 0x00168793.
Lemma F_cb694 : fetch_word Asan.M.loaded_segments (0xcb694 : word) = Some W_cb694.
Proof. vm_refl. Qed.
Lemma D_cb694 : decode_any W_cb694 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb698 : bv 32 := 0x02f587b3.
Lemma F_cb698 : fetch_word Asan.M.loaded_segments (0xcb698 : word) = Some W_cb698.
Proof. vm_refl. Qed.
Lemma D_cb698 : decode_any W_cb698 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb69c : bv 32 := 0x00700813.
Lemma F_cb69c : fetch_word Asan.M.loaded_segments (0xcb69c : word) = Some W_cb69c.
Proof. vm_refl. Qed.
Lemma D_cb69c : decode_any W_cb69c = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6a0 : bv 32 := 0x00053883.
Lemma F_cb6a0 : fetch_word Asan.M.loaded_segments (0xcb6a0 : word) = Some W_cb6a0.
Proof. vm_refl. Qed.
Lemma D_cb6a0 : decode_any W_cb6a0 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6a4 : bv 32 := 0x00f8c8b3.
Lemma F_cb6a4 : fetch_word Asan.M.loaded_segments (0xcb6a4 : word) = Some W_cb6a4.
Proof. vm_refl. Qed.
Lemma D_cb6a4 : decode_any W_cb6a4 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6a8 : bv 32 := 0x411682b3.
Lemma F_cb6a8 : fetch_word Asan.M.loaded_segments (0xcb6a8 : word) = Some W_cb6a8.
Proof. vm_refl. Qed.
Lemma D_cb6a8 : decode_any W_cb6a8 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6ac : bv 32 := 0x0112e8b3.
Lemma F_cb6ac : fetch_word Asan.M.loaded_segments (0xcb6ac : word) = Some W_cb6ac.
Proof. vm_refl. Qed.
Lemma D_cb6ac : decode_any W_cb6ac = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6b0 : bv 32 := 0x00e8f8b3.
Lemma F_cb6b0 : fetch_word Asan.M.loaded_segments (0xcb6b0 : word) = Some W_cb6b0.
Proof. vm_refl. Qed.
Lemma D_cb6b0 : decode_any W_cb6b0 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6b4 : bv 32 := 0x02e89a63.
Lemma F_cb6b4 : fetch_word Asan.M.loaded_segments (0xcb6b4 : word) = Some W_cb6b4.
Proof. vm_refl. Qed.
Lemma D_cb6b4 : decode_any W_cb6b4 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6b8 : bv 32 := 0xff860613.
Lemma F_cb6b8 : fetch_word Asan.M.loaded_segments (0xcb6b8 : word) = Some W_cb6b8.
Proof. vm_refl. Qed.
Lemma D_cb6b8 : decode_any W_cb6b8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6bc : bv 32 := 0x00850513.
Lemma F_cb6bc : fetch_word Asan.M.loaded_segments (0xcb6bc : word) = Some W_cb6bc.
Proof. vm_refl. Qed.
Lemma D_cb6bc : decode_any W_cb6bc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6c0 : bv 32 := 0xfec860e3.
Lemma F_cb6c0 : fetch_word Asan.M.loaded_segments (0xcb6c0 : word) = Some W_cb6c0.
Proof. vm_refl. Qed.
Lemma D_cb6c0 : decode_any W_cb6c0 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6c4 : bv 32 := 0x00060693.
Lemma F_cb6c4 : fetch_word Asan.M.loaded_segments (0xcb6c4 : word) = Some W_cb6c4.
Proof. vm_refl. Qed.
Lemma D_cb6c4 : decode_any W_cb6c4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6c8 : bv 32 := 0x00060c63.
Lemma F_cb6c8 : fetch_word Asan.M.loaded_segments (0xcb6c8 : word) = Some W_cb6c8.
Proof. vm_refl. Qed.
Lemma D_cb6c8 : decode_any W_cb6c8 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6cc : bv 32 := 0x00054603.
Lemma F_cb6cc : fetch_word Asan.M.loaded_segments (0xcb6cc : word) = Some W_cb6cc.
Proof. vm_refl. Qed.
Lemma D_cb6cc : decode_any W_cb6cc = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6d0 : bv 32 := 0x00b60a63.
Lemma F_cb6d0 : fetch_word Asan.M.loaded_segments (0xcb6d0 : word) = Some W_cb6d0.
Proof. vm_refl. Qed.
Lemma D_cb6d0 : decode_any W_cb6d0 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6d4 : bv 32 := 0xfff68693.
Lemma F_cb6d4 : fetch_word Asan.M.loaded_segments (0xcb6d4 : word) = Some W_cb6d4.
Proof. vm_refl. Qed.
Lemma D_cb6d4 : decode_any W_cb6d4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6d8 : bv 32 := 0x00150513.
Lemma F_cb6d8 : fetch_word Asan.M.loaded_segments (0xcb6d8 : word) = Some W_cb6d8.
Proof. vm_refl. Qed.
Lemma D_cb6d8 : decode_any W_cb6d8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6dc : bv 32 := 0xfe0698e3.
Lemma F_cb6dc : fetch_word Asan.M.loaded_segments (0xcb6dc : word) = Some W_cb6dc.
Proof. vm_refl. Qed.
Lemma D_cb6dc : decode_any W_cb6dc = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6e0 : bv 32 := 0x00000513.
Lemma F_cb6e0 : fetch_word Asan.M.loaded_segments (0xcb6e0 : word) = Some W_cb6e0.
Proof. vm_refl. Qed.
Lemma D_cb6e0 : decode_any W_cb6e0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6e4 : bv 32 := 0x00008067.
Lemma F_cb6e4 : fetch_word Asan.M.loaded_segments (0xcb6e4 : word) = Some W_cb6e4.
Proof. vm_refl. Qed.
Lemma D_cb6e4 : decode_any W_cb6e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6e8 : bv 32 := 0x00060693.
Lemma F_cb6e8 : fetch_word Asan.M.loaded_segments (0xcb6e8 : word) = Some W_cb6e8.
Proof. vm_refl. Qed.
Lemma D_cb6e8 : decode_any W_cb6e8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6ec : bv 32 := 0x00054603.
Lemma F_cb6ec : fetch_word Asan.M.loaded_segments (0xcb6ec : word) = Some W_cb6ec.
Proof. vm_refl. Qed.
Lemma D_cb6ec : decode_any W_cb6ec = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6f0 : bv 32 := 0xfeb612e3.
Lemma F_cb6f0 : fetch_word Asan.M.loaded_segments (0xcb6f0 : word) = Some W_cb6f0.
Proof. vm_refl. Qed.
Lemma D_cb6f0 : decode_any W_cb6f0 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6f4 : bv 32 := 0xff1ff06f.
Lemma F_cb6f4 : fetch_word Asan.M.loaded_segments (0xcb6f4 : word) = Some W_cb6f4.
Proof. vm_refl. Qed.
Lemma D_cb6f4 : decode_any W_cb6f4 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6f8 : bv 32 := 0x02060063.
Lemma F_cb6f8 : fetch_word Asan.M.loaded_segments (0xcb6f8 : word) = Some W_cb6f8.
Proof. vm_refl. Qed.
Lemma D_cb6f8 : decode_any W_cb6f8 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb6fc : bv 32 := 0x00054683.
Lemma F_cb6fc : fetch_word Asan.M.loaded_segments (0xcb6fc : word) = Some W_cb6fc.
Proof. vm_refl. Qed.
Lemma D_cb6fc : decode_any W_cb6fc = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb700 : bv 32 := 0x0005c703.
Lemma F_cb700 : fetch_word Asan.M.loaded_segments (0xcb700 : word) = Some W_cb700.
Proof. vm_refl. Qed.
Lemma D_cb700 : decode_any W_cb700 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb704 : bv 32 := 0x00e69e63.
Lemma F_cb704 : fetch_word Asan.M.loaded_segments (0xcb704 : word) = Some W_cb704.
Proof. vm_refl. Qed.
Lemma D_cb704 : decode_any W_cb704 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb708 : bv 32 := 0xfff60613.
Lemma F_cb708 : fetch_word Asan.M.loaded_segments (0xcb708 : word) = Some W_cb708.
Proof. vm_refl. Qed.
Lemma D_cb708 : decode_any W_cb708 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb70c : bv 32 := 0x00150513.
Lemma F_cb70c : fetch_word Asan.M.loaded_segments (0xcb70c : word) = Some W_cb70c.
Proof. vm_refl. Qed.
Lemma D_cb70c : decode_any W_cb70c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb710 : bv 32 := 0x00158593.
Lemma F_cb710 : fetch_word Asan.M.loaded_segments (0xcb710 : word) = Some W_cb710.
Proof. vm_refl. Qed.
Lemma D_cb710 : decode_any W_cb710 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb714 : bv 32 := 0xfe0614e3.
Lemma F_cb714 : fetch_word Asan.M.loaded_segments (0xcb714 : word) = Some W_cb714.
Proof. vm_refl. Qed.
Lemma D_cb714 : decode_any W_cb714 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb718 : bv 32 := 0x00000513.
Lemma F_cb718 : fetch_word Asan.M.loaded_segments (0xcb718 : word) = Some W_cb718.
Proof. vm_refl. Qed.
Lemma D_cb718 : decode_any W_cb718 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb71c : bv 32 := 0x00008067.
Lemma F_cb71c : fetch_word Asan.M.loaded_segments (0xcb71c : word) = Some W_cb71c.
Proof. vm_refl. Qed.
Lemma D_cb71c : decode_any W_cb71c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb720 : bv 32 := 0x40e68533.
Lemma F_cb720 : fetch_word Asan.M.loaded_segments (0xcb720 : word) = Some W_cb720.
Proof. vm_refl. Qed.
Lemma D_cb720 : decode_any W_cb720 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb724 : bv 32 := 0x00008067.
Lemma F_cb724 : fetch_word Asan.M.loaded_segments (0xcb724 : word) = Some W_cb724.
Proof. vm_refl. Qed.
Lemma D_cb724 : decode_any W_cb724 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb728 : bv 32 := 0x0035f693.
Lemma F_cb728 : fetch_word Asan.M.loaded_segments (0xcb728 : word) = Some W_cb728.
Proof. vm_refl. Qed.
Lemma D_cb728 : decode_any W_cb728 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb72c : bv 32 := 0x10068863.
Lemma F_cb72c : fetch_word Asan.M.loaded_segments (0xcb72c : word) = Some W_cb72c.
Proof. vm_refl. Qed.
Lemma D_cb72c : decode_any W_cb72c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb730 : bv 32 := 0x02060e63.
Lemma F_cb730 : fetch_word Asan.M.loaded_segments (0xcb730 : word) = Some W_cb730.
Proof. vm_refl. Qed.
Lemma D_cb730 : decode_any W_cb730 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb734 : bv 32 := 0x00158713.
Lemma F_cb734 : fetch_word Asan.M.loaded_segments (0xcb734 : word) = Some W_cb734.
Proof. vm_refl. Qed.
Lemma D_cb734 : decode_any W_cb734 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb738 : bv 32 := 0x00100793.
Lemma F_cb738 : fetch_word Asan.M.loaded_segments (0xcb738 : word) = Some W_cb738.
Proof. vm_refl. Qed.
Lemma D_cb738 : decode_any W_cb738 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb73c : bv 32 := 0x00050693.
Lemma F_cb73c : fetch_word Asan.M.loaded_segments (0xcb73c : word) = Some W_cb73c.
Proof. vm_refl. Qed.
Lemma D_cb73c : decode_any W_cb73c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb740 : bv 32 := 0x0005c883.
Lemma F_cb740 : fetch_word Asan.M.loaded_segments (0xcb740 : word) = Some W_cb740.
Proof. vm_refl. Qed.
Lemma D_cb740 : decode_any W_cb740 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb744 : bv 32 := 0x00060813.
Lemma F_cb744 : fetch_word Asan.M.loaded_segments (0xcb744 : word) = Some W_cb744.
Proof. vm_refl. Qed.
Lemma D_cb744 : decode_any W_cb744 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb748 : bv 32 := 0x00158593.
Lemma F_cb748 : fetch_word Asan.M.loaded_segments (0xcb748 : word) = Some W_cb748.
Proof. vm_refl. Qed.
Lemma D_cb748 : decode_any W_cb748 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb74c : bv 32 := 0x00377293.
Lemma F_cb74c : fetch_word Asan.M.loaded_segments (0xcb74c : word) = Some W_cb74c.
Proof. vm_refl. Qed.
Lemma D_cb74c : decode_any W_cb74c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb750 : bv 32 := 0x01168023.
Lemma F_cb750 : fetch_word Asan.M.loaded_segments (0xcb750 : word) = Some W_cb750.
Proof. vm_refl. Qed.
Lemma D_cb750 : decode_any W_cb750 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb754 : bv 32 := 0x00168693.
Lemma F_cb754 : fetch_word Asan.M.loaded_segments (0xcb754 : word) = Some W_cb754.
Proof. vm_refl. Qed.
Lemma D_cb754 : decode_any W_cb754 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb758 : bv 32 := 0xfff60613.
Lemma F_cb758 : fetch_word Asan.M.loaded_segments (0xcb758 : word) = Some W_cb758.
Proof. vm_refl. Qed.
Lemma D_cb758 : decode_any W_cb758 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb75c : bv 32 := 0x00028a63.
Lemma F_cb75c : fetch_word Asan.M.loaded_segments (0xcb75c : word) = Some W_cb75c.
Proof. vm_refl. Qed.
Lemma D_cb75c : decode_any W_cb75c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb760 : bv 32 := 0x00170713.
Lemma F_cb760 : fetch_word Asan.M.loaded_segments (0xcb760 : word) = Some W_cb760.
Proof. vm_refl. Qed.
Lemma D_cb760 : decode_any W_cb760 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb764 : bv 32 := 0xfcf81ee3.
Lemma F_cb764 : fetch_word Asan.M.loaded_segments (0xcb764 : word) = Some W_cb764.
Proof. vm_refl. Qed.
Lemma D_cb764 : decode_any W_cb764 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb768 : bv 32 := 0x0080006f.
Lemma F_cb768 : fetch_word Asan.M.loaded_segments (0xcb768 : word) = Some W_cb768.
Proof. vm_refl. Qed.
Lemma D_cb768 : decode_any W_cb768 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb76c : bv 32 := 0x00050693.
Lemma F_cb76c : fetch_word Asan.M.loaded_segments (0xcb76c : word) = Some W_cb76c.
Proof. vm_refl. Qed.
Lemma D_cb76c : decode_any W_cb76c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb770 : bv 32 := 0x0036f793.
Lemma F_cb770 : fetch_word Asan.M.loaded_segments (0xcb770 : word) = Some W_cb770.
Proof. vm_refl. Qed.
Lemma D_cb770 : decode_any W_cb770 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb774 : bv 32 := 0x0c078a63.
Lemma F_cb774 : fetch_word Asan.M.loaded_segments (0xcb774 : word) = Some W_cb774.
Proof. vm_refl. Qed.
Lemma D_cb774 : decode_any W_cb774 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb778 : bv 32 := 0x02000713.
Lemma F_cb778 : fetch_word Asan.M.loaded_segments (0xcb778 : word) = Some W_cb778.
Proof. vm_refl. Qed.
Lemma D_cb778 : decode_any W_cb778 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb77c : bv 32 := 0x02e67063.
Lemma F_cb77c : fetch_word Asan.M.loaded_segments (0xcb77c : word) = Some W_cb77c.
Proof. vm_refl. Qed.
Lemma D_cb77c : decode_any W_cb77c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb780 : bv 32 := 0x01000713.
Lemma F_cb780 : fetch_word Asan.M.loaded_segments (0xcb780 : word) = Some W_cb780.
Proof. vm_refl. Qed.
Lemma D_cb780 : decode_any W_cb780 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb784 : bv 32 := 0x24e67863.
Lemma F_cb784 : fetch_word Asan.M.loaded_segments (0xcb784 : word) = Some W_cb784.
Proof. vm_refl. Qed.
Lemma D_cb784 : decode_any W_cb784 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb788 : bv 32 := 0x00867713.
Lemma F_cb788 : fetch_word Asan.M.loaded_segments (0xcb788 : word) = Some W_cb788.
Proof. vm_refl. Qed.
Lemma D_cb788 : decode_any W_cb788 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb78c : bv 32 := 0x2c071e63.
Lemma F_cb78c : fetch_word Asan.M.loaded_segments (0xcb78c : word) = Some W_cb78c.
Proof. vm_refl. Qed.
Lemma D_cb78c : decode_any W_cb78c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb790 : bv 32 := 0x00467713.
Lemma F_cb790 : fetch_word Asan.M.loaded_segments (0xcb790 : word) = Some W_cb790.
Proof. vm_refl. Qed.
Lemma D_cb790 : decode_any W_cb790 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb794 : bv 32 := 0x32071463.
Lemma F_cb794 : fetch_word Asan.M.loaded_segments (0xcb794 : word) = Some W_cb794.
Proof. vm_refl. Qed.
Lemma D_cb794 : decode_any W_cb794 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb798 : bv 32 := 0x3500006f.
Lemma F_cb798 : fetch_word Asan.M.loaded_segments (0xcb798 : word) = Some W_cb798.
Proof. vm_refl. Qed.
Lemma D_cb798 : decode_any W_cb798 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb79c : bv 32 := 0x0005a703.
Lemma F_cb79c : fetch_word Asan.M.loaded_segments (0xcb79c : word) = Some W_cb79c.
Proof. vm_refl. Qed.
Lemma D_cb79c : decode_any W_cb79c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7a0 : bv 32 := 0x00300813.
Lemma F_cb7a0 : fetch_word Asan.M.loaded_segments (0xcb7a0 : word) = Some W_cb7a0.
Proof. vm_refl. Qed.
Lemma D_cb7a0 : decode_any W_cb7a0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7a4 : bv 32 := 0x11078e63.
Lemma F_cb7a4 : fetch_word Asan.M.loaded_segments (0xcb7a4 : word) = Some W_cb7a4.
Proof. vm_refl. Qed.
Lemma D_cb7a4 : decode_any W_cb7a4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7a8 : bv 32 := 0x00200813.
Lemma F_cb7a8 : fetch_word Asan.M.loaded_segments (0xcb7a8 : word) = Some W_cb7a8.
Proof. vm_refl. Qed.
Lemma D_cb7a8 : decode_any W_cb7a8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7ac : bv 32 := 0x19079c63.
Lemma F_cb7ac : fetch_word Asan.M.loaded_segments (0xcb7ac : word) = Some W_cb7ac.
Proof. vm_refl. Qed.
Lemma D_cb7ac : decode_any W_cb7ac = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7b0 : bv 32 := 0x00875793.
Lemma F_cb7b0 : fetch_word Asan.M.loaded_segments (0xcb7b0 : word) = Some W_cb7b0.
Proof. vm_refl. Qed.
Lemma D_cb7b0 : decode_any W_cb7b0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7b4 : bv 32 := 0xffe60613.
Lemma F_cb7b4 : fetch_word Asan.M.loaded_segments (0xcb7b4 : word) = Some W_cb7b4.
Proof. vm_refl. Qed.
Lemma D_cb7b4 : decode_any W_cb7b4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7b8 : bv 32 := 0x00e68023.
Lemma F_cb7b8 : fetch_word Asan.M.loaded_segments (0xcb7b8 : word) = Some W_cb7b8.
Proof. vm_refl. Qed.
Lemma D_cb7b8 : decode_any W_cb7b8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7bc : bv 32 := 0x00f680a3.
Lemma F_cb7bc : fetch_word Asan.M.loaded_segments (0xcb7bc : word) = Some W_cb7bc.
Proof. vm_refl. Qed.
Lemma D_cb7bc : decode_any W_cb7bc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7c0 : bv 32 := 0x00268693.
Lemma F_cb7c0 : fetch_word Asan.M.loaded_segments (0xcb7c0 : word) = Some W_cb7c0.
Proof. vm_refl. Qed.
Lemma D_cb7c0 : decode_any W_cb7c0 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7c4 : bv 32 := 0x01058593.
Lemma F_cb7c4 : fetch_word Asan.M.loaded_segments (0xcb7c4 : word) = Some W_cb7c4.
Proof. vm_refl. Qed.
Lemma D_cb7c4 : decode_any W_cb7c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7c8 : bv 32 := 0x01100793.
Lemma F_cb7c8 : fetch_word Asan.M.loaded_segments (0xcb7c8 : word) = Some W_cb7c8.
Proof. vm_refl. Qed.
Lemma D_cb7c8 : decode_any W_cb7c8 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7cc : bv 32 := 0x0107581b.
Lemma F_cb7cc : fetch_word Asan.M.loaded_segments (0xcb7cc : word) = Some W_cb7cc.
Proof. vm_refl. Qed.
Lemma D_cb7cc : decode_any W_cb7cc = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7d0 : bv 32 := 0xff45a883.
Lemma F_cb7d0 : fetch_word Asan.M.loaded_segments (0xcb7d0 : word) = Some W_cb7d0.
Proof. vm_refl. Qed.
Lemma D_cb7d0 : decode_any W_cb7d0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7d4 : bv 32 := 0xff85a283.
Lemma F_cb7d4 : fetch_word Asan.M.loaded_segments (0xcb7d4 : word) = Some W_cb7d4.
Proof. vm_refl. Qed.
Lemma D_cb7d4 : decode_any W_cb7d4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7d8 : bv 32 := 0xffc5a303.
Lemma F_cb7d8 : fetch_word Asan.M.loaded_segments (0xcb7d8 : word) = Some W_cb7d8.
Proof. vm_refl. Qed.
Lemma D_cb7d8 : decode_any W_cb7d8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7dc : bv 32 := 0x0005a703.
Lemma F_cb7dc : fetch_word Asan.M.loaded_segments (0xcb7dc : word) = Some W_cb7dc.
Proof. vm_refl. Qed.
Lemma D_cb7dc : decode_any W_cb7dc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7e0 : bv 32 := 0x01089393.
Lemma F_cb7e0 : fetch_word Asan.M.loaded_segments (0xcb7e0 : word) = Some W_cb7e0.
Proof. vm_refl. Qed.
Lemma D_cb7e0 : decode_any W_cb7e0 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7e4 : bv 32 := 0x0108d89b.
Lemma F_cb7e4 : fetch_word Asan.M.loaded_segments (0xcb7e4 : word) = Some W_cb7e4.
Proof. vm_refl. Qed.
Lemma D_cb7e4 : decode_any W_cb7e4 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7e8 : bv 32 := 0x0103e833.
Lemma F_cb7e8 : fetch_word Asan.M.loaded_segments (0xcb7e8 : word) = Some W_cb7e8.
Proof. vm_refl. Qed.
Lemma D_cb7e8 : decode_any W_cb7e8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7ec : bv 32 := 0x01029393.
Lemma F_cb7ec : fetch_word Asan.M.loaded_segments (0xcb7ec : word) = Some W_cb7ec.
Proof. vm_refl. Qed.
Lemma D_cb7ec : decode_any W_cb7ec = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7f0 : bv 32 := 0x0102d29b.
Lemma F_cb7f0 : fetch_word Asan.M.loaded_segments (0xcb7f0 : word) = Some W_cb7f0.
Proof. vm_refl. Qed.
Lemma D_cb7f0 : decode_any W_cb7f0 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7f4 : bv 32 := 0x0113e8b3.
Lemma F_cb7f4 : fetch_word Asan.M.loaded_segments (0xcb7f4 : word) = Some W_cb7f4.
Proof. vm_refl. Qed.
Lemma D_cb7f4 : decode_any W_cb7f4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7f8 : bv 32 := 0x01031393.
Lemma F_cb7f8 : fetch_word Asan.M.loaded_segments (0xcb7f8 : word) = Some W_cb7f8.
Proof. vm_refl. Qed.
Lemma D_cb7f8 : decode_any W_cb7f8 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb7fc : bv 32 := 0x0103531b.
Lemma F_cb7fc : fetch_word Asan.M.loaded_segments (0xcb7fc : word) = Some W_cb7fc.
Proof. vm_refl. Qed.
Lemma D_cb7fc : decode_any W_cb7fc = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb800 : bv 32 := 0x0053e2b3.
Lemma F_cb800 : fetch_word Asan.M.loaded_segments (0xcb800 : word) = Some W_cb800.
Proof. vm_refl. Qed.
Lemma D_cb800 : decode_any W_cb800 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb804 : bv 32 := 0x01071393.
Lemma F_cb804 : fetch_word Asan.M.loaded_segments (0xcb804 : word) = Some W_cb804.
Proof. vm_refl. Qed.
Lemma D_cb804 : decode_any W_cb804 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb808 : bv 32 := 0x0063e333.
Lemma F_cb808 : fetch_word Asan.M.loaded_segments (0xcb808 : word) = Some W_cb808.
Proof. vm_refl. Qed.
Lemma D_cb808 : decode_any W_cb808 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb80c : bv 32 := 0xff060613.
Lemma F_cb80c : fetch_word Asan.M.loaded_segments (0xcb80c : word) = Some W_cb80c.
Proof. vm_refl. Qed.
Lemma D_cb80c : decode_any W_cb80c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb810 : bv 32 := 0x0106a023.
Lemma F_cb810 : fetch_word Asan.M.loaded_segments (0xcb810 : word) = Some W_cb810.
Proof. vm_refl. Qed.
Lemma D_cb810 : decode_any W_cb810 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb814 : bv 32 := 0x0116a223.
Lemma F_cb814 : fetch_word Asan.M.loaded_segments (0xcb814 : word) = Some W_cb814.
Proof. vm_refl. Qed.
Lemma D_cb814 : decode_any W_cb814 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb818 : bv 32 := 0x0056a423.
Lemma F_cb818 : fetch_word Asan.M.loaded_segments (0xcb818 : word) = Some W_cb818.
Proof. vm_refl. Qed.
Lemma D_cb818 : decode_any W_cb818 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb81c : bv 32 := 0x0066a623.
Lemma F_cb81c : fetch_word Asan.M.loaded_segments (0xcb81c : word) = Some W_cb81c.
Proof. vm_refl. Qed.
Lemma D_cb81c : decode_any W_cb81c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb820 : bv 32 := 0x01068693.
Lemma F_cb820 : fetch_word Asan.M.loaded_segments (0xcb820 : word) = Some W_cb820.
Proof. vm_refl. Qed.
Lemma D_cb820 : decode_any W_cb820 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb824 : bv 32 := 0x01058593.
Lemma F_cb824 : fetch_word Asan.M.loaded_segments (0xcb824 : word) = Some W_cb824.
Proof. vm_refl. Qed.
Lemma D_cb824 : decode_any W_cb824 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb828 : bv 32 := 0xfac7e2e3.
Lemma F_cb828 : fetch_word Asan.M.loaded_segments (0xcb828 : word) = Some W_cb828.
Proof. vm_refl. Qed.
Lemma D_cb828 : decode_any W_cb828 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb82c : bv 32 := 0xff258593.
Lemma F_cb82c : fetch_word Asan.M.loaded_segments (0xcb82c : word) = Some W_cb82c.
Proof. vm_refl. Qed.
Lemma D_cb82c : decode_any W_cb82c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb830 : bv 32 := 0x01000713.
Lemma F_cb830 : fetch_word Asan.M.loaded_segments (0xcb830 : word) = Some W_cb830.
Proof. vm_refl. Qed.
Lemma D_cb830 : decode_any W_cb830 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb834 : bv 32 := 0xf4e66ae3.
Lemma F_cb834 : fetch_word Asan.M.loaded_segments (0xcb834 : word) = Some W_cb834.
Proof. vm_refl. Qed.
Lemma D_cb834 : decode_any W_cb834 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb838 : bv 32 := 0x19c0006f.
Lemma F_cb838 : fetch_word Asan.M.loaded_segments (0xcb838 : word) = Some W_cb838.
Proof. vm_refl. Qed.
Lemma D_cb838 : decode_any W_cb838 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb83c : bv 32 := 0x00050693.
Lemma F_cb83c : fetch_word Asan.M.loaded_segments (0xcb83c : word) = Some W_cb83c.
Proof. vm_refl. Qed.
Lemma D_cb83c : decode_any W_cb83c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb840 : bv 32 := 0x00357793.
Lemma F_cb840 : fetch_word Asan.M.loaded_segments (0xcb840 : word) = Some W_cb840.
Proof. vm_refl. Qed.
Lemma D_cb840 : decode_any W_cb840 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb844 : bv 32 := 0xf2079ae3.
Lemma F_cb844 : fetch_word Asan.M.loaded_segments (0xcb844 : word) = Some W_cb844.
Proof. vm_refl. Qed.
Lemma D_cb844 : decode_any W_cb844 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb848 : bv 32 := 0x01000713.
Lemma F_cb848 : fetch_word Asan.M.loaded_segments (0xcb848 : word) = Some W_cb848.
Proof. vm_refl. Qed.
Lemma D_cb848 : decode_any W_cb848 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb84c : bv 32 := 0x02e66c63.
Lemma F_cb84c : fetch_word Asan.M.loaded_segments (0xcb84c : word) = Some W_cb84c.
Proof. vm_refl. Qed.
Lemma D_cb84c : decode_any W_cb84c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb850 : bv 32 := 0x00f00713.
Lemma F_cb850 : fetch_word Asan.M.loaded_segments (0xcb850 : word) = Some W_cb850.
Proof. vm_refl. Qed.
Lemma D_cb850 : decode_any W_cb850 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb854 : bv 32 := 0x0005a783.
Lemma F_cb854 : fetch_word Asan.M.loaded_segments (0xcb854 : word) = Some W_cb854.
Proof. vm_refl. Qed.
Lemma D_cb854 : decode_any W_cb854 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb858 : bv 32 := 0x0045a803.
Lemma F_cb858 : fetch_word Asan.M.loaded_segments (0xcb858 : word) = Some W_cb858.
Proof. vm_refl. Qed.
Lemma D_cb858 : decode_any W_cb858 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb85c : bv 32 := 0x0085a883.
Lemma F_cb85c : fetch_word Asan.M.loaded_segments (0xcb85c : word) = Some W_cb85c.
Proof. vm_refl. Qed.
Lemma D_cb85c : decode_any W_cb85c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb860 : bv 32 := 0x00c5a283.
Lemma F_cb860 : fetch_word Asan.M.loaded_segments (0xcb860 : word) = Some W_cb860.
Proof. vm_refl. Qed.
Lemma D_cb860 : decode_any W_cb860 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb864 : bv 32 := 0x01058593.
Lemma F_cb864 : fetch_word Asan.M.loaded_segments (0xcb864 : word) = Some W_cb864.
Proof. vm_refl. Qed.
Lemma D_cb864 : decode_any W_cb864 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb868 : bv 32 := 0xff060613.
Lemma F_cb868 : fetch_word Asan.M.loaded_segments (0xcb868 : word) = Some W_cb868.
Proof. vm_refl. Qed.
Lemma D_cb868 : decode_any W_cb868 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb86c : bv 32 := 0x00f6a023.
Lemma F_cb86c : fetch_word Asan.M.loaded_segments (0xcb86c : word) = Some W_cb86c.
Proof. vm_refl. Qed.
Lemma D_cb86c : decode_any W_cb86c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb870 : bv 32 := 0x0106a223.
Lemma F_cb870 : fetch_word Asan.M.loaded_segments (0xcb870 : word) = Some W_cb870.
Proof. vm_refl. Qed.
Lemma D_cb870 : decode_any W_cb870 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb874 : bv 32 := 0x0116a423.
Lemma F_cb874 : fetch_word Asan.M.loaded_segments (0xcb874 : word) = Some W_cb874.
Proof. vm_refl. Qed.
Lemma D_cb874 : decode_any W_cb874 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb878 : bv 32 := 0x0056a623.
Lemma F_cb878 : fetch_word Asan.M.loaded_segments (0xcb878 : word) = Some W_cb878.
Proof. vm_refl. Qed.
Lemma D_cb878 : decode_any W_cb878 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb87c : bv 32 := 0x01068693.
Lemma F_cb87c : fetch_word Asan.M.loaded_segments (0xcb87c : word) = Some W_cb87c.
Proof. vm_refl. Qed.
Lemma D_cb87c : decode_any W_cb87c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb880 : bv 32 := 0xfcc76ae3.
Lemma F_cb880 : fetch_word Asan.M.loaded_segments (0xcb880 : word) = Some W_cb880.
Proof. vm_refl. Qed.
Lemma D_cb880 : decode_any W_cb880 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb884 : bv 32 := 0x00800713.
Lemma F_cb884 : fetch_word Asan.M.loaded_segments (0xcb884 : word) = Some W_cb884.
Proof. vm_refl. Qed.
Lemma D_cb884 : decode_any W_cb884 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb888 : bv 32 := 0x00e66e63.
Lemma F_cb888 : fetch_word Asan.M.loaded_segments (0xcb888 : word) = Some W_cb888.
Proof. vm_refl. Qed.
Lemma D_cb888 : decode_any W_cb888 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb88c : bv 32 := 0x0005a703.
Lemma F_cb88c : fetch_word Asan.M.loaded_segments (0xcb88c : word) = Some W_cb88c.
Proof. vm_refl. Qed.
Lemma D_cb88c : decode_any W_cb88c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb890 : bv 32 := 0x0045a783.
Lemma F_cb890 : fetch_word Asan.M.loaded_segments (0xcb890 : word) = Some W_cb890.
Proof. vm_refl. Qed.
Lemma D_cb890 : decode_any W_cb890 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb894 : bv 32 := 0x00e6a023.
Lemma F_cb894 : fetch_word Asan.M.loaded_segments (0xcb894 : word) = Some W_cb894.
Proof. vm_refl. Qed.
Lemma D_cb894 : decode_any W_cb894 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb898 : bv 32 := 0x00f6a223.
Lemma F_cb898 : fetch_word Asan.M.loaded_segments (0xcb898 : word) = Some W_cb898.
Proof. vm_refl. Qed.
Lemma D_cb898 : decode_any W_cb898 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb89c : bv 32 := 0x00868693.
Lemma F_cb89c : fetch_word Asan.M.loaded_segments (0xcb89c : word) = Some W_cb89c.
Proof. vm_refl. Qed.
Lemma D_cb89c : decode_any W_cb89c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8a0 : bv 32 := 0x00858593.
Lemma F_cb8a0 : fetch_word Asan.M.loaded_segments (0xcb8a0 : word) = Some W_cb8a0.
Proof. vm_refl. Qed.
Lemma D_cb8a0 : decode_any W_cb8a0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8a4 : bv 32 := 0x00467713.
Lemma F_cb8a4 : fetch_word Asan.M.loaded_segments (0xcb8a4 : word) = Some W_cb8a4.
Proof. vm_refl. Qed.
Lemma D_cb8a4 : decode_any W_cb8a4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8a8 : bv 32 := 0x24070063.
Lemma F_cb8a8 : fetch_word Asan.M.loaded_segments (0xcb8a8 : word) = Some W_cb8a8.
Proof. vm_refl. Qed.
Lemma D_cb8a8 : decode_any W_cb8a8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8ac : bv 32 := 0x0005a703.
Lemma F_cb8ac : fetch_word Asan.M.loaded_segments (0xcb8ac : word) = Some W_cb8ac.
Proof. vm_refl. Qed.
Lemma D_cb8ac : decode_any W_cb8ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8b0 : bv 32 := 0x00458593.
Lemma F_cb8b0 : fetch_word Asan.M.loaded_segments (0xcb8b0 : word) = Some W_cb8b0.
Proof. vm_refl. Qed.
Lemma D_cb8b0 : decode_any W_cb8b0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8b4 : bv 32 := 0x00e6a023.
Lemma F_cb8b4 : fetch_word Asan.M.loaded_segments (0xcb8b4 : word) = Some W_cb8b4.
Proof. vm_refl. Qed.
Lemma D_cb8b4 : decode_any W_cb8b4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8b8 : bv 32 := 0x00468693.
Lemma F_cb8b8 : fetch_word Asan.M.loaded_segments (0xcb8b8 : word) = Some W_cb8b8.
Proof. vm_refl. Qed.
Lemma D_cb8b8 : decode_any W_cb8b8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8bc : bv 32 := 0x22c0006f.
Lemma F_cb8bc : fetch_word Asan.M.loaded_segments (0xcb8bc : word) = Some W_cb8bc.
Proof. vm_refl. Qed.
Lemma D_cb8bc : decode_any W_cb8bc = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8c0 : bv 32 := 0x00e68023.
Lemma F_cb8c0 : fetch_word Asan.M.loaded_segments (0xcb8c0 : word) = Some W_cb8c0.
Proof. vm_refl. Qed.
Lemma D_cb8c0 : decode_any W_cb8c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8c4 : bv 32 := 0x00168693.
Lemma F_cb8c4 : fetch_word Asan.M.loaded_segments (0xcb8c4 : word) = Some W_cb8c4.
Proof. vm_refl. Qed.
Lemma D_cb8c4 : decode_any W_cb8c4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8c8 : bv 32 := 0xfff60613.
Lemma F_cb8c8 : fetch_word Asan.M.loaded_segments (0xcb8c8 : word) = Some W_cb8c8.
Proof. vm_refl. Qed.
Lemma D_cb8c8 : decode_any W_cb8c8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8cc : bv 32 := 0x01058593.
Lemma F_cb8cc : fetch_word Asan.M.loaded_segments (0xcb8cc : word) = Some W_cb8cc.
Proof. vm_refl. Qed.
Lemma D_cb8cc : decode_any W_cb8cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8d0 : bv 32 := 0x01200793.
Lemma F_cb8d0 : fetch_word Asan.M.loaded_segments (0xcb8d0 : word) = Some W_cb8d0.
Proof. vm_refl. Qed.
Lemma D_cb8d0 : decode_any W_cb8d0 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8d4 : bv 32 := 0x0087581b.
Lemma F_cb8d4 : fetch_word Asan.M.loaded_segments (0xcb8d4 : word) = Some W_cb8d4.
Proof. vm_refl. Qed.
Lemma D_cb8d4 : decode_any W_cb8d4 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8d8 : bv 32 := 0xff45a883.
Lemma F_cb8d8 : fetch_word Asan.M.loaded_segments (0xcb8d8 : word) = Some W_cb8d8.
Proof. vm_refl. Qed.
Lemma D_cb8d8 : decode_any W_cb8d8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8dc : bv 32 := 0xff85a283.
Lemma F_cb8dc : fetch_word Asan.M.loaded_segments (0xcb8dc : word) = Some W_cb8dc.
Proof. vm_refl. Qed.
Lemma D_cb8dc : decode_any W_cb8dc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8e0 : bv 32 := 0xffc5a303.
Lemma F_cb8e0 : fetch_word Asan.M.loaded_segments (0xcb8e0 : word) = Some W_cb8e0.
Proof. vm_refl. Qed.
Lemma D_cb8e0 : decode_any W_cb8e0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8e4 : bv 32 := 0x0005a703.
Lemma F_cb8e4 : fetch_word Asan.M.loaded_segments (0xcb8e4 : word) = Some W_cb8e4.
Proof. vm_refl. Qed.
Lemma D_cb8e4 : decode_any W_cb8e4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8e8 : bv 32 := 0x01889393.
Lemma F_cb8e8 : fetch_word Asan.M.loaded_segments (0xcb8e8 : word) = Some W_cb8e8.
Proof. vm_refl. Qed.
Lemma D_cb8e8 : decode_any W_cb8e8 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8ec : bv 32 := 0x0088d89b.
Lemma F_cb8ec : fetch_word Asan.M.loaded_segments (0xcb8ec : word) = Some W_cb8ec.
Proof. vm_refl. Qed.
Lemma D_cb8ec : decode_any W_cb8ec = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8f0 : bv 32 := 0x0103e833.
Lemma F_cb8f0 : fetch_word Asan.M.loaded_segments (0xcb8f0 : word) = Some W_cb8f0.
Proof. vm_refl. Qed.
Lemma D_cb8f0 : decode_any W_cb8f0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8f4 : bv 32 := 0x01829393.
Lemma F_cb8f4 : fetch_word Asan.M.loaded_segments (0xcb8f4 : word) = Some W_cb8f4.
Proof. vm_refl. Qed.
Lemma D_cb8f4 : decode_any W_cb8f4 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8f8 : bv 32 := 0x0082d29b.
Lemma F_cb8f8 : fetch_word Asan.M.loaded_segments (0xcb8f8 : word) = Some W_cb8f8.
Proof. vm_refl. Qed.
Lemma D_cb8f8 : decode_any W_cb8f8 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb8fc : bv 32 := 0x0113e8b3.
Lemma F_cb8fc : fetch_word Asan.M.loaded_segments (0xcb8fc : word) = Some W_cb8fc.
Proof. vm_refl. Qed.
Lemma D_cb8fc : decode_any W_cb8fc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb900 : bv 32 := 0x01831393.
Lemma F_cb900 : fetch_word Asan.M.loaded_segments (0xcb900 : word) = Some W_cb900.
Proof. vm_refl. Qed.
Lemma D_cb900 : decode_any W_cb900 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb904 : bv 32 := 0x0083531b.
Lemma F_cb904 : fetch_word Asan.M.loaded_segments (0xcb904 : word) = Some W_cb904.
Proof. vm_refl. Qed.
Lemma D_cb904 : decode_any W_cb904 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb908 : bv 32 := 0x0053e2b3.
Lemma F_cb908 : fetch_word Asan.M.loaded_segments (0xcb908 : word) = Some W_cb908.
Proof. vm_refl. Qed.
Lemma D_cb908 : decode_any W_cb908 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb90c : bv 32 := 0x01871393.
Lemma F_cb90c : fetch_word Asan.M.loaded_segments (0xcb90c : word) = Some W_cb90c.
Proof. vm_refl. Qed.
Lemma D_cb90c : decode_any W_cb90c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb910 : bv 32 := 0x0063e333.
Lemma F_cb910 : fetch_word Asan.M.loaded_segments (0xcb910 : word) = Some W_cb910.
Proof. vm_refl. Qed.
Lemma D_cb910 : decode_any W_cb910 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb914 : bv 32 := 0xff060613.
Lemma F_cb914 : fetch_word Asan.M.loaded_segments (0xcb914 : word) = Some W_cb914.
Proof. vm_refl. Qed.
Lemma D_cb914 : decode_any W_cb914 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb918 : bv 32 := 0x0106a023.
Lemma F_cb918 : fetch_word Asan.M.loaded_segments (0xcb918 : word) = Some W_cb918.
Proof. vm_refl. Qed.
Lemma D_cb918 : decode_any W_cb918 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb91c : bv 32 := 0x0116a223.
Lemma F_cb91c : fetch_word Asan.M.loaded_segments (0xcb91c : word) = Some W_cb91c.
Proof. vm_refl. Qed.
Lemma D_cb91c : decode_any W_cb91c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb920 : bv 32 := 0x0056a423.
Lemma F_cb920 : fetch_word Asan.M.loaded_segments (0xcb920 : word) = Some W_cb920.
Proof. vm_refl. Qed.
Lemma D_cb920 : decode_any W_cb920 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb924 : bv 32 := 0x0066a623.
Lemma F_cb924 : fetch_word Asan.M.loaded_segments (0xcb924 : word) = Some W_cb924.
Proof. vm_refl. Qed.
Lemma D_cb924 : decode_any W_cb924 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb928 : bv 32 := 0x01068693.
Lemma F_cb928 : fetch_word Asan.M.loaded_segments (0xcb928 : word) = Some W_cb928.
Proof. vm_refl. Qed.
Lemma D_cb928 : decode_any W_cb928 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb92c : bv 32 := 0x01058593.
Lemma F_cb92c : fetch_word Asan.M.loaded_segments (0xcb92c : word) = Some W_cb92c.
Proof. vm_refl. Qed.
Lemma D_cb92c : decode_any W_cb92c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb930 : bv 32 := 0xfac7e2e3.
Lemma F_cb930 : fetch_word Asan.M.loaded_segments (0xcb930 : word) = Some W_cb930.
Proof. vm_refl. Qed.
Lemma D_cb930 : decode_any W_cb930 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb934 : bv 32 := 0xff158593.
Lemma F_cb934 : fetch_word Asan.M.loaded_segments (0xcb934 : word) = Some W_cb934.
Proof. vm_refl. Qed.
Lemma D_cb934 : decode_any W_cb934 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb938 : bv 32 := 0x01000713.
Lemma F_cb938 : fetch_word Asan.M.loaded_segments (0xcb938 : word) = Some W_cb938.
Proof. vm_refl. Qed.
Lemma D_cb938 : decode_any W_cb938 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb93c : bv 32 := 0xe4e666e3.
Lemma F_cb93c : fetch_word Asan.M.loaded_segments (0xcb93c : word) = Some W_cb93c.
Proof. vm_refl. Qed.
Lemma D_cb93c : decode_any W_cb93c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb940 : bv 32 := 0x0940006f.
Lemma F_cb940 : fetch_word Asan.M.loaded_segments (0xcb940 : word) = Some W_cb940.
Proof. vm_refl. Qed.
Lemma D_cb940 : decode_any W_cb940 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb944 : bv 32 := 0x00875793.
Lemma F_cb944 : fetch_word Asan.M.loaded_segments (0xcb944 : word) = Some W_cb944.
Proof. vm_refl. Qed.
Lemma D_cb944 : decode_any W_cb944 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb948 : bv 32 := 0x01075813.
Lemma F_cb948 : fetch_word Asan.M.loaded_segments (0xcb948 : word) = Some W_cb948.
Proof. vm_refl. Qed.
Lemma D_cb948 : decode_any W_cb948 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb94c : bv 32 := 0xffd60613.
Lemma F_cb94c : fetch_word Asan.M.loaded_segments (0xcb94c : word) = Some W_cb94c.
Proof. vm_refl. Qed.
Lemma D_cb94c : decode_any W_cb94c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb950 : bv 32 := 0x00e68023.
Lemma F_cb950 : fetch_word Asan.M.loaded_segments (0xcb950 : word) = Some W_cb950.
Proof. vm_refl. Qed.
Lemma D_cb950 : decode_any W_cb950 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb954 : bv 32 := 0x00f680a3.
Lemma F_cb954 : fetch_word Asan.M.loaded_segments (0xcb954 : word) = Some W_cb954.
Proof. vm_refl. Qed.
Lemma D_cb954 : decode_any W_cb954 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb958 : bv 32 := 0x01068123.
Lemma F_cb958 : fetch_word Asan.M.loaded_segments (0xcb958 : word) = Some W_cb958.
Proof. vm_refl. Qed.
Lemma D_cb958 : decode_any W_cb958 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb95c : bv 32 := 0x00368693.
Lemma F_cb95c : fetch_word Asan.M.loaded_segments (0xcb95c : word) = Some W_cb95c.
Proof. vm_refl. Qed.
Lemma D_cb95c : decode_any W_cb95c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb960 : bv 32 := 0x01058593.
Lemma F_cb960 : fetch_word Asan.M.loaded_segments (0xcb960 : word) = Some W_cb960.
Proof. vm_refl. Qed.
Lemma D_cb960 : decode_any W_cb960 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb964 : bv 32 := 0x01000793.
Lemma F_cb964 : fetch_word Asan.M.loaded_segments (0xcb964 : word) = Some W_cb964.
Proof. vm_refl. Qed.
Lemma D_cb964 : decode_any W_cb964 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb968 : bv 32 := 0x0187581b.
Lemma F_cb968 : fetch_word Asan.M.loaded_segments (0xcb968 : word) = Some W_cb968.
Proof. vm_refl. Qed.
Lemma D_cb968 : decode_any W_cb968 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb96c : bv 32 := 0xff45a883.
Lemma F_cb96c : fetch_word Asan.M.loaded_segments (0xcb96c : word) = Some W_cb96c.
Proof. vm_refl. Qed.
Lemma D_cb96c : decode_any W_cb96c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb970 : bv 32 := 0xff85a283.
Lemma F_cb970 : fetch_word Asan.M.loaded_segments (0xcb970 : word) = Some W_cb970.
Proof. vm_refl. Qed.
Lemma D_cb970 : decode_any W_cb970 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb974 : bv 32 := 0xffc5a303.
Lemma F_cb974 : fetch_word Asan.M.loaded_segments (0xcb974 : word) = Some W_cb974.
Proof. vm_refl. Qed.
Lemma D_cb974 : decode_any W_cb974 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb978 : bv 32 := 0x0005a703.
Lemma F_cb978 : fetch_word Asan.M.loaded_segments (0xcb978 : word) = Some W_cb978.
Proof. vm_refl. Qed.
Lemma D_cb978 : decode_any W_cb978 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb97c : bv 32 := 0x00889393.
Lemma F_cb97c : fetch_word Asan.M.loaded_segments (0xcb97c : word) = Some W_cb97c.
Proof. vm_refl. Qed.
Lemma D_cb97c : decode_any W_cb97c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb980 : bv 32 := 0x0188d89b.
Lemma F_cb980 : fetch_word Asan.M.loaded_segments (0xcb980 : word) = Some W_cb980.
Proof. vm_refl. Qed.
Lemma D_cb980 : decode_any W_cb980 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb984 : bv 32 := 0x0103e833.
Lemma F_cb984 : fetch_word Asan.M.loaded_segments (0xcb984 : word) = Some W_cb984.
Proof. vm_refl. Qed.
Lemma D_cb984 : decode_any W_cb984 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb988 : bv 32 := 0x00829393.
Lemma F_cb988 : fetch_word Asan.M.loaded_segments (0xcb988 : word) = Some W_cb988.
Proof. vm_refl. Qed.
Lemma D_cb988 : decode_any W_cb988 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb98c : bv 32 := 0x0182d29b.
Lemma F_cb98c : fetch_word Asan.M.loaded_segments (0xcb98c : word) = Some W_cb98c.
Proof. vm_refl. Qed.
Lemma D_cb98c : decode_any W_cb98c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb990 : bv 32 := 0x0113e8b3.
Lemma F_cb990 : fetch_word Asan.M.loaded_segments (0xcb990 : word) = Some W_cb990.
Proof. vm_refl. Qed.
Lemma D_cb990 : decode_any W_cb990 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb994 : bv 32 := 0x00831393.
Lemma F_cb994 : fetch_word Asan.M.loaded_segments (0xcb994 : word) = Some W_cb994.
Proof. vm_refl. Qed.
Lemma D_cb994 : decode_any W_cb994 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb998 : bv 32 := 0x0183531b.
Lemma F_cb998 : fetch_word Asan.M.loaded_segments (0xcb998 : word) = Some W_cb998.
Proof. vm_refl. Qed.
Lemma D_cb998 : decode_any W_cb998 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb99c : bv 32 := 0x0053e2b3.
Lemma F_cb99c : fetch_word Asan.M.loaded_segments (0xcb99c : word) = Some W_cb99c.
Proof. vm_refl. Qed.
Lemma D_cb99c : decode_any W_cb99c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9a0 : bv 32 := 0x00871393.
Lemma F_cb9a0 : fetch_word Asan.M.loaded_segments (0xcb9a0 : word) = Some W_cb9a0.
Proof. vm_refl. Qed.
Lemma D_cb9a0 : decode_any W_cb9a0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9a4 : bv 32 := 0x0063e333.
Lemma F_cb9a4 : fetch_word Asan.M.loaded_segments (0xcb9a4 : word) = Some W_cb9a4.
Proof. vm_refl. Qed.
Lemma D_cb9a4 : decode_any W_cb9a4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9a8 : bv 32 := 0xff060613.
Lemma F_cb9a8 : fetch_word Asan.M.loaded_segments (0xcb9a8 : word) = Some W_cb9a8.
Proof. vm_refl. Qed.
Lemma D_cb9a8 : decode_any W_cb9a8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9ac : bv 32 := 0x0106a023.
Lemma F_cb9ac : fetch_word Asan.M.loaded_segments (0xcb9ac : word) = Some W_cb9ac.
Proof. vm_refl. Qed.
Lemma D_cb9ac : decode_any W_cb9ac = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9b0 : bv 32 := 0x0116a223.
Lemma F_cb9b0 : fetch_word Asan.M.loaded_segments (0xcb9b0 : word) = Some W_cb9b0.
Proof. vm_refl. Qed.
Lemma D_cb9b0 : decode_any W_cb9b0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9b4 : bv 32 := 0x0056a423.
Lemma F_cb9b4 : fetch_word Asan.M.loaded_segments (0xcb9b4 : word) = Some W_cb9b4.
Proof. vm_refl. Qed.
Lemma D_cb9b4 : decode_any W_cb9b4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9b8 : bv 32 := 0x0066a623.
Lemma F_cb9b8 : fetch_word Asan.M.loaded_segments (0xcb9b8 : word) = Some W_cb9b8.
Proof. vm_refl. Qed.
Lemma D_cb9b8 : decode_any W_cb9b8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9bc : bv 32 := 0x01068693.
Lemma F_cb9bc : fetch_word Asan.M.loaded_segments (0xcb9bc : word) = Some W_cb9bc.
Proof. vm_refl. Qed.
Lemma D_cb9bc : decode_any W_cb9bc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9c0 : bv 32 := 0x01058593.
Lemma F_cb9c0 : fetch_word Asan.M.loaded_segments (0xcb9c0 : word) = Some W_cb9c0.
Proof. vm_refl. Qed.
Lemma D_cb9c0 : decode_any W_cb9c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9c4 : bv 32 := 0xfac7e2e3.
Lemma F_cb9c4 : fetch_word Asan.M.loaded_segments (0xcb9c4 : word) = Some W_cb9c4.
Proof. vm_refl. Qed.
Lemma D_cb9c4 : decode_any W_cb9c4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9c8 : bv 32 := 0xff358593.
Lemma F_cb9c8 : fetch_word Asan.M.loaded_segments (0xcb9c8 : word) = Some W_cb9c8.
Proof. vm_refl. Qed.
Lemma D_cb9c8 : decode_any W_cb9c8 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9cc : bv 32 := 0x01000713.
Lemma F_cb9cc : fetch_word Asan.M.loaded_segments (0xcb9cc : word) = Some W_cb9cc.
Proof. vm_refl. Qed.
Lemma D_cb9cc : decode_any W_cb9cc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9d0 : bv 32 := 0xdae66ce3.
Lemma F_cb9d0 : fetch_word Asan.M.loaded_segments (0xcb9d0 : word) = Some W_cb9d0.
Proof. vm_refl. Qed.
Lemma D_cb9d0 : decode_any W_cb9d0 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9d4 : bv 32 := 0x0005c703.
Lemma F_cb9d4 : fetch_word Asan.M.loaded_segments (0xcb9d4 : word) = Some W_cb9d4.
Proof. vm_refl. Qed.
Lemma D_cb9d4 : decode_any W_cb9d4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9d8 : bv 32 := 0x0015c783.
Lemma F_cb9d8 : fetch_word Asan.M.loaded_segments (0xcb9d8 : word) = Some W_cb9d8.
Proof. vm_refl. Qed.
Lemma D_cb9d8 : decode_any W_cb9d8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9dc : bv 32 := 0x0025c803.
Lemma F_cb9dc : fetch_word Asan.M.loaded_segments (0xcb9dc : word) = Some W_cb9dc.
Proof. vm_refl. Qed.
Lemma D_cb9dc : decode_any W_cb9dc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9e0 : bv 32 := 0x0035c883.
Lemma F_cb9e0 : fetch_word Asan.M.loaded_segments (0xcb9e0 : word) = Some W_cb9e0.
Proof. vm_refl. Qed.
Lemma D_cb9e0 : decode_any W_cb9e0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9e4 : bv 32 := 0x0045c283.
Lemma F_cb9e4 : fetch_word Asan.M.loaded_segments (0xcb9e4 : word) = Some W_cb9e4.
Proof. vm_refl. Qed.
Lemma D_cb9e4 : decode_any W_cb9e4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9e8 : bv 32 := 0x0055c303.
Lemma F_cb9e8 : fetch_word Asan.M.loaded_segments (0xcb9e8 : word) = Some W_cb9e8.
Proof. vm_refl. Qed.
Lemma D_cb9e8 : decode_any W_cb9e8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9ec : bv 32 := 0x0065c383.
Lemma F_cb9ec : fetch_word Asan.M.loaded_segments (0xcb9ec : word) = Some W_cb9ec.
Proof. vm_refl. Qed.
Lemma D_cb9ec : decode_any W_cb9ec = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9f0 : bv 32 := 0x0075ce03.
Lemma F_cb9f0 : fetch_word Asan.M.loaded_segments (0xcb9f0 : word) = Some W_cb9f0.
Proof. vm_refl. Qed.
Lemma D_cb9f0 : decode_any W_cb9f0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9f4 : bv 32 := 0x00e68023.
Lemma F_cb9f4 : fetch_word Asan.M.loaded_segments (0xcb9f4 : word) = Some W_cb9f4.
Proof. vm_refl. Qed.
Lemma D_cb9f4 : decode_any W_cb9f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9f8 : bv 32 := 0x00f680a3.
Lemma F_cb9f8 : fetch_word Asan.M.loaded_segments (0xcb9f8 : word) = Some W_cb9f8.
Proof. vm_refl. Qed.
Lemma D_cb9f8 : decode_any W_cb9f8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cb9fc : bv 32 := 0x01068123.
Lemma F_cb9fc : fetch_word Asan.M.loaded_segments (0xcb9fc : word) = Some W_cb9fc.
Proof. vm_refl. Qed.
Lemma D_cb9fc : decode_any W_cb9fc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba00 : bv 32 := 0x011681a3.
Lemma F_cba00 : fetch_word Asan.M.loaded_segments (0xcba00 : word) = Some W_cba00.
Proof. vm_refl. Qed.
Lemma D_cba00 : decode_any W_cba00 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba04 : bv 32 := 0x0085c703.
Lemma F_cba04 : fetch_word Asan.M.loaded_segments (0xcba04 : word) = Some W_cba04.
Proof. vm_refl. Qed.
Lemma D_cba04 : decode_any W_cba04 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba08 : bv 32 := 0x0095c783.
Lemma F_cba08 : fetch_word Asan.M.loaded_segments (0xcba08 : word) = Some W_cba08.
Proof. vm_refl. Qed.
Lemma D_cba08 : decode_any W_cba08 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba0c : bv 32 := 0x00a5c803.
Lemma F_cba0c : fetch_word Asan.M.loaded_segments (0xcba0c : word) = Some W_cba0c.
Proof. vm_refl. Qed.
Lemma D_cba0c : decode_any W_cba0c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba10 : bv 32 := 0x00b5c883.
Lemma F_cba10 : fetch_word Asan.M.loaded_segments (0xcba10 : word) = Some W_cba10.
Proof. vm_refl. Qed.
Lemma D_cba10 : decode_any W_cba10 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba14 : bv 32 := 0x00568223.
Lemma F_cba14 : fetch_word Asan.M.loaded_segments (0xcba14 : word) = Some W_cba14.
Proof. vm_refl. Qed.
Lemma D_cba14 : decode_any W_cba14 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba18 : bv 32 := 0x006682a3.
Lemma F_cba18 : fetch_word Asan.M.loaded_segments (0xcba18 : word) = Some W_cba18.
Proof. vm_refl. Qed.
Lemma D_cba18 : decode_any W_cba18 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba1c : bv 32 := 0x00768323.
Lemma F_cba1c : fetch_word Asan.M.loaded_segments (0xcba1c : word) = Some W_cba1c.
Proof. vm_refl. Qed.
Lemma D_cba1c : decode_any W_cba1c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba20 : bv 32 := 0x01c683a3.
Lemma F_cba20 : fetch_word Asan.M.loaded_segments (0xcba20 : word) = Some W_cba20.
Proof. vm_refl. Qed.
Lemma D_cba20 : decode_any W_cba20 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba24 : bv 32 := 0x00c5c283.
Lemma F_cba24 : fetch_word Asan.M.loaded_segments (0xcba24 : word) = Some W_cba24.
Proof. vm_refl. Qed.
Lemma D_cba24 : decode_any W_cba24 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba28 : bv 32 := 0x00d5c303.
Lemma F_cba28 : fetch_word Asan.M.loaded_segments (0xcba28 : word) = Some W_cba28.
Proof. vm_refl. Qed.
Lemma D_cba28 : decode_any W_cba28 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba2c : bv 32 := 0x00e5c383.
Lemma F_cba2c : fetch_word Asan.M.loaded_segments (0xcba2c : word) = Some W_cba2c.
Proof. vm_refl. Qed.
Lemma D_cba2c : decode_any W_cba2c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba30 : bv 32 := 0x00f5ce03.
Lemma F_cba30 : fetch_word Asan.M.loaded_segments (0xcba30 : word) = Some W_cba30.
Proof. vm_refl. Qed.
Lemma D_cba30 : decode_any W_cba30 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba34 : bv 32 := 0x01058593.
Lemma F_cba34 : fetch_word Asan.M.loaded_segments (0xcba34 : word) = Some W_cba34.
Proof. vm_refl. Qed.
Lemma D_cba34 : decode_any W_cba34 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba38 : bv 32 := 0x00e68423.
Lemma F_cba38 : fetch_word Asan.M.loaded_segments (0xcba38 : word) = Some W_cba38.
Proof. vm_refl. Qed.
Lemma D_cba38 : decode_any W_cba38 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba3c : bv 32 := 0x00f684a3.
Lemma F_cba3c : fetch_word Asan.M.loaded_segments (0xcba3c : word) = Some W_cba3c.
Proof. vm_refl. Qed.
Lemma D_cba3c : decode_any W_cba3c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba40 : bv 32 := 0x01068523.
Lemma F_cba40 : fetch_word Asan.M.loaded_segments (0xcba40 : word) = Some W_cba40.
Proof. vm_refl. Qed.
Lemma D_cba40 : decode_any W_cba40 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba44 : bv 32 := 0x011685a3.
Lemma F_cba44 : fetch_word Asan.M.loaded_segments (0xcba44 : word) = Some W_cba44.
Proof. vm_refl. Qed.
Lemma D_cba44 : decode_any W_cba44 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba48 : bv 32 := 0x01068713.
Lemma F_cba48 : fetch_word Asan.M.loaded_segments (0xcba48 : word) = Some W_cba48.
Proof. vm_refl. Qed.
Lemma D_cba48 : decode_any W_cba48 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba4c : bv 32 := 0x00568623.
Lemma F_cba4c : fetch_word Asan.M.loaded_segments (0xcba4c : word) = Some W_cba4c.
Proof. vm_refl. Qed.
Lemma D_cba4c : decode_any W_cba4c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba50 : bv 32 := 0x006686a3.
Lemma F_cba50 : fetch_word Asan.M.loaded_segments (0xcba50 : word) = Some W_cba50.
Proof. vm_refl. Qed.
Lemma D_cba50 : decode_any W_cba50 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba54 : bv 32 := 0x00768723.
Lemma F_cba54 : fetch_word Asan.M.loaded_segments (0xcba54 : word) = Some W_cba54.
Proof. vm_refl. Qed.
Lemma D_cba54 : decode_any W_cba54 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba58 : bv 32 := 0x01c687a3.
Lemma F_cba58 : fetch_word Asan.M.loaded_segments (0xcba58 : word) = Some W_cba58.
Proof. vm_refl. Qed.
Lemma D_cba58 : decode_any W_cba58 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba5c : bv 32 := 0x00070693.
Lemma F_cba5c : fetch_word Asan.M.loaded_segments (0xcba5c : word) = Some W_cba5c.
Proof. vm_refl. Qed.
Lemma D_cba5c : decode_any W_cba5c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba60 : bv 32 := 0x00867713.
Lemma F_cba60 : fetch_word Asan.M.loaded_segments (0xcba60 : word) = Some W_cba60.
Proof. vm_refl. Qed.
Lemma D_cba60 : decode_any W_cba60 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba64 : bv 32 := 0xd20706e3.
Lemma F_cba64 : fetch_word Asan.M.loaded_segments (0xcba64 : word) = Some W_cba64.
Proof. vm_refl. Qed.
Lemma D_cba64 : decode_any W_cba64 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba68 : bv 32 := 0x0005c703.
Lemma F_cba68 : fetch_word Asan.M.loaded_segments (0xcba68 : word) = Some W_cba68.
Proof. vm_refl. Qed.
Lemma D_cba68 : decode_any W_cba68 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba6c : bv 32 := 0x0015c783.
Lemma F_cba6c : fetch_word Asan.M.loaded_segments (0xcba6c : word) = Some W_cba6c.
Proof. vm_refl. Qed.
Lemma D_cba6c : decode_any W_cba6c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba70 : bv 32 := 0x0025c803.
Lemma F_cba70 : fetch_word Asan.M.loaded_segments (0xcba70 : word) = Some W_cba70.
Proof. vm_refl. Qed.
Lemma D_cba70 : decode_any W_cba70 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba74 : bv 32 := 0x0035c883.
Lemma F_cba74 : fetch_word Asan.M.loaded_segments (0xcba74 : word) = Some W_cba74.
Proof. vm_refl. Qed.
Lemma D_cba74 : decode_any W_cba74 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba78 : bv 32 := 0x0045c283.
Lemma F_cba78 : fetch_word Asan.M.loaded_segments (0xcba78 : word) = Some W_cba78.
Proof. vm_refl. Qed.
Lemma D_cba78 : decode_any W_cba78 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba7c : bv 32 := 0x0055c303.
Lemma F_cba7c : fetch_word Asan.M.loaded_segments (0xcba7c : word) = Some W_cba7c.
Proof. vm_refl. Qed.
Lemma D_cba7c : decode_any W_cba7c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba80 : bv 32 := 0x0065c383.
Lemma F_cba80 : fetch_word Asan.M.loaded_segments (0xcba80 : word) = Some W_cba80.
Proof. vm_refl. Qed.
Lemma D_cba80 : decode_any W_cba80 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba84 : bv 32 := 0x0075ce03.
Lemma F_cba84 : fetch_word Asan.M.loaded_segments (0xcba84 : word) = Some W_cba84.
Proof. vm_refl. Qed.
Lemma D_cba84 : decode_any W_cba84 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba88 : bv 32 := 0x00858593.
Lemma F_cba88 : fetch_word Asan.M.loaded_segments (0xcba88 : word) = Some W_cba88.
Proof. vm_refl. Qed.
Lemma D_cba88 : decode_any W_cba88 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba8c : bv 32 := 0x00e68023.
Lemma F_cba8c : fetch_word Asan.M.loaded_segments (0xcba8c : word) = Some W_cba8c.
Proof. vm_refl. Qed.
Lemma D_cba8c : decode_any W_cba8c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba90 : bv 32 := 0x00f680a3.
Lemma F_cba90 : fetch_word Asan.M.loaded_segments (0xcba90 : word) = Some W_cba90.
Proof. vm_refl. Qed.
Lemma D_cba90 : decode_any W_cba90 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba94 : bv 32 := 0x01068123.
Lemma F_cba94 : fetch_word Asan.M.loaded_segments (0xcba94 : word) = Some W_cba94.
Proof. vm_refl. Qed.
Lemma D_cba94 : decode_any W_cba94 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba98 : bv 32 := 0x011681a3.
Lemma F_cba98 : fetch_word Asan.M.loaded_segments (0xcba98 : word) = Some W_cba98.
Proof. vm_refl. Qed.
Lemma D_cba98 : decode_any W_cba98 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cba9c : bv 32 := 0x00868713.
Lemma F_cba9c : fetch_word Asan.M.loaded_segments (0xcba9c : word) = Some W_cba9c.
Proof. vm_refl. Qed.
Lemma D_cba9c : decode_any W_cba9c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaa0 : bv 32 := 0x00568223.
Lemma F_cbaa0 : fetch_word Asan.M.loaded_segments (0xcbaa0 : word) = Some W_cbaa0.
Proof. vm_refl. Qed.
Lemma D_cbaa0 : decode_any W_cbaa0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaa4 : bv 32 := 0x006682a3.
Lemma F_cbaa4 : fetch_word Asan.M.loaded_segments (0xcbaa4 : word) = Some W_cbaa4.
Proof. vm_refl. Qed.
Lemma D_cbaa4 : decode_any W_cbaa4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaa8 : bv 32 := 0x00768323.
Lemma F_cbaa8 : fetch_word Asan.M.loaded_segments (0xcbaa8 : word) = Some W_cbaa8.
Proof. vm_refl. Qed.
Lemma D_cbaa8 : decode_any W_cbaa8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaac : bv 32 := 0x01c683a3.
Lemma F_cbaac : fetch_word Asan.M.loaded_segments (0xcbaac : word) = Some W_cbaac.
Proof. vm_refl. Qed.
Lemma D_cbaac : decode_any W_cbaac = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbab0 : bv 32 := 0x00070693.
Lemma F_cbab0 : fetch_word Asan.M.loaded_segments (0xcbab0 : word) = Some W_cbab0.
Proof. vm_refl. Qed.
Lemma D_cbab0 : decode_any W_cbab0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbab4 : bv 32 := 0x00467713.
Lemma F_cbab4 : fetch_word Asan.M.loaded_segments (0xcbab4 : word) = Some W_cbab4.
Proof. vm_refl. Qed.
Lemma D_cbab4 : decode_any W_cbab4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbab8 : bv 32 := 0x02070863.
Lemma F_cbab8 : fetch_word Asan.M.loaded_segments (0xcbab8 : word) = Some W_cbab8.
Proof. vm_refl. Qed.
Lemma D_cbab8 : decode_any W_cbab8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbabc : bv 32 := 0x0005c703.
Lemma F_cbabc : fetch_word Asan.M.loaded_segments (0xcbabc : word) = Some W_cbabc.
Proof. vm_refl. Qed.
Lemma D_cbabc : decode_any W_cbabc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbac0 : bv 32 := 0x0015c783.
Lemma F_cbac0 : fetch_word Asan.M.loaded_segments (0xcbac0 : word) = Some W_cbac0.
Proof. vm_refl. Qed.
Lemma D_cbac0 : decode_any W_cbac0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbac4 : bv 32 := 0x0025c803.
Lemma F_cbac4 : fetch_word Asan.M.loaded_segments (0xcbac4 : word) = Some W_cbac4.
Proof. vm_refl. Qed.
Lemma D_cbac4 : decode_any W_cbac4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbac8 : bv 32 := 0x0035c883.
Lemma F_cbac8 : fetch_word Asan.M.loaded_segments (0xcbac8 : word) = Some W_cbac8.
Proof. vm_refl. Qed.
Lemma D_cbac8 : decode_any W_cbac8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbacc : bv 32 := 0x00458593.
Lemma F_cbacc : fetch_word Asan.M.loaded_segments (0xcbacc : word) = Some W_cbacc.
Proof. vm_refl. Qed.
Lemma D_cbacc : decode_any W_cbacc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbad0 : bv 32 := 0x00468293.
Lemma F_cbad0 : fetch_word Asan.M.loaded_segments (0xcbad0 : word) = Some W_cbad0.
Proof. vm_refl. Qed.
Lemma D_cbad0 : decode_any W_cbad0 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbad4 : bv 32 := 0x00e68023.
Lemma F_cbad4 : fetch_word Asan.M.loaded_segments (0xcbad4 : word) = Some W_cbad4.
Proof. vm_refl. Qed.
Lemma D_cbad4 : decode_any W_cbad4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbad8 : bv 32 := 0x00f680a3.
Lemma F_cbad8 : fetch_word Asan.M.loaded_segments (0xcbad8 : word) = Some W_cbad8.
Proof. vm_refl. Qed.
Lemma D_cbad8 : decode_any W_cbad8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbadc : bv 32 := 0x01068123.
Lemma F_cbadc : fetch_word Asan.M.loaded_segments (0xcbadc : word) = Some W_cbadc.
Proof. vm_refl. Qed.
Lemma D_cbadc : decode_any W_cbadc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbae0 : bv 32 := 0x011681a3.
Lemma F_cbae0 : fetch_word Asan.M.loaded_segments (0xcbae0 : word) = Some W_cbae0.
Proof. vm_refl. Qed.
Lemma D_cbae0 : decode_any W_cbae0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbae4 : bv 32 := 0x00028693.
Lemma F_cbae4 : fetch_word Asan.M.loaded_segments (0xcbae4 : word) = Some W_cbae4.
Proof. vm_refl. Qed.
Lemma D_cbae4 : decode_any W_cbae4 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbae8 : bv 32 := 0x00267713.
Lemma F_cbae8 : fetch_word Asan.M.loaded_segments (0xcbae8 : word) = Some W_cbae8.
Proof. vm_refl. Qed.
Lemma D_cbae8 : decode_any W_cbae8 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaec : bv 32 := 0x00071863.
Lemma F_cbaec : fetch_word Asan.M.loaded_segments (0xcbaec : word) = Some W_cbaec.
Proof. vm_refl. Qed.
Lemma D_cbaec : decode_any W_cbaec = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaf0 : bv 32 := 0x00167613.
Lemma F_cbaf0 : fetch_word Asan.M.loaded_segments (0xcbaf0 : word) = Some W_cbaf0.
Proof. vm_refl. Qed.
Lemma D_cbaf0 : decode_any W_cbaf0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaf4 : bv 32 := 0x02061663.
Lemma F_cbaf4 : fetch_word Asan.M.loaded_segments (0xcbaf4 : word) = Some W_cbaf4.
Proof. vm_refl. Qed.
Lemma D_cbaf4 : decode_any W_cbaf4 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbaf8 : bv 32 := 0x00008067.
Lemma F_cbaf8 : fetch_word Asan.M.loaded_segments (0xcbaf8 : word) = Some W_cbaf8.
Proof. vm_refl. Qed.
Lemma D_cbaf8 : decode_any W_cbaf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbafc : bv 32 := 0x0005c703.
Lemma F_cbafc : fetch_word Asan.M.loaded_segments (0xcbafc : word) = Some W_cbafc.
Proof. vm_refl. Qed.
Lemma D_cbafc : decode_any W_cbafc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb00 : bv 32 := 0x0015c783.
Lemma F_cbb00 : fetch_word Asan.M.loaded_segments (0xcbb00 : word) = Some W_cbb00.
Proof. vm_refl. Qed.
Lemma D_cbb00 : decode_any W_cbb00 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb04 : bv 32 := 0x00258593.
Lemma F_cbb04 : fetch_word Asan.M.loaded_segments (0xcbb04 : word) = Some W_cbb04.
Proof. vm_refl. Qed.
Lemma D_cbb04 : decode_any W_cbb04 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb08 : bv 32 := 0x00268813.
Lemma F_cbb08 : fetch_word Asan.M.loaded_segments (0xcbb08 : word) = Some W_cbb08.
Proof. vm_refl. Qed.
Lemma D_cbb08 : decode_any W_cbb08 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb0c : bv 32 := 0x00e68023.
Lemma F_cbb0c : fetch_word Asan.M.loaded_segments (0xcbb0c : word) = Some W_cbb0c.
Proof. vm_refl. Qed.
Lemma D_cbb0c : decode_any W_cbb0c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb10 : bv 32 := 0x00f680a3.
Lemma F_cbb10 : fetch_word Asan.M.loaded_segments (0xcbb10 : word) = Some W_cbb10.
Proof. vm_refl. Qed.
Lemma D_cbb10 : decode_any W_cbb10 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb14 : bv 32 := 0x00080693.
Lemma F_cbb14 : fetch_word Asan.M.loaded_segments (0xcbb14 : word) = Some W_cbb14.
Proof. vm_refl. Qed.
Lemma D_cbb14 : decode_any W_cbb14 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb18 : bv 32 := 0x00167613.
Lemma F_cbb18 : fetch_word Asan.M.loaded_segments (0xcbb18 : word) = Some W_cbb18.
Proof. vm_refl. Qed.
Lemma D_cbb18 : decode_any W_cbb18 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb1c : bv 32 := 0xfc060ee3.
Lemma F_cbb1c : fetch_word Asan.M.loaded_segments (0xcbb1c : word) = Some W_cbb1c.
Proof. vm_refl. Qed.
Lemma D_cbb1c : decode_any W_cbb1c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb20 : bv 32 := 0x0005c583.
Lemma F_cbb20 : fetch_word Asan.M.loaded_segments (0xcbb20 : word) = Some W_cbb20.
Proof. vm_refl. Qed.
Lemma D_cbb20 : decode_any W_cbb20 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb24 : bv 32 := 0x00b68023.
Lemma F_cbb24 : fetch_word Asan.M.loaded_segments (0xcbb24 : word) = Some W_cbb24.
Proof. vm_refl. Qed.
Lemma D_cbb24 : decode_any W_cbb24 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb28 : bv 32 := 0x00008067.
Lemma F_cbb28 : fetch_word Asan.M.loaded_segments (0xcbb28 : word) = Some W_cbb28.
Proof. vm_refl. Qed.
Lemma D_cbb28 : decode_any W_cbb28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb2c : bv 32 := 0x0e060a63.
Lemma F_cbb2c : fetch_word Asan.M.loaded_segments (0xcbb2c : word) = Some W_cbb2c.
Proof. vm_refl. Qed.
Lemma D_cbb2c : decode_any W_cbb2c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb30 : bv 32 := 0x00b50023.
Lemma F_cbb30 : fetch_word Asan.M.loaded_segments (0xcbb30 : word) = Some W_cbb30.
Proof. vm_refl. Qed.
Lemma D_cbb30 : decode_any W_cbb30 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb34 : bv 32 := 0x00c506b3.
Lemma F_cbb34 : fetch_word Asan.M.loaded_segments (0xcbb34 : word) = Some W_cbb34.
Proof. vm_refl. Qed.
Lemma D_cbb34 : decode_any W_cbb34 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb38 : bv 32 := 0x00300713.
Lemma F_cbb38 : fetch_word Asan.M.loaded_segments (0xcbb38 : word) = Some W_cbb38.
Proof. vm_refl. Qed.
Lemma D_cbb38 : decode_any W_cbb38 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb3c : bv 32 := 0xfeb68fa3.
Lemma F_cbb3c : fetch_word Asan.M.loaded_segments (0xcbb3c : word) = Some W_cbb3c.
Proof. vm_refl. Qed.
Lemma D_cbb3c : decode_any W_cbb3c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb40 : bv 32 := 0x0ee66063.
Lemma F_cbb40 : fetch_word Asan.M.loaded_segments (0xcbb40 : word) = Some W_cbb40.
Proof. vm_refl. Qed.
Lemma D_cbb40 : decode_any W_cbb40 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb44 : bv 32 := 0x00b500a3.
Lemma F_cbb44 : fetch_word Asan.M.loaded_segments (0xcbb44 : word) = Some W_cbb44.
Proof. vm_refl. Qed.
Lemma D_cbb44 : decode_any W_cbb44 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb48 : bv 32 := 0x00b50123.
Lemma F_cbb48 : fetch_word Asan.M.loaded_segments (0xcbb48 : word) = Some W_cbb48.
Proof. vm_refl. Qed.
Lemma D_cbb48 : decode_any W_cbb48 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb4c : bv 32 := 0x00700713.
Lemma F_cbb4c : fetch_word Asan.M.loaded_segments (0xcbb4c : word) = Some W_cbb4c.
Proof. vm_refl. Qed.
Lemma D_cbb4c : decode_any W_cbb4c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb50 : bv 32 := 0xfeb68ea3.
Lemma F_cbb50 : fetch_word Asan.M.loaded_segments (0xcbb50 : word) = Some W_cbb50.
Proof. vm_refl. Qed.
Lemma D_cbb50 : decode_any W_cbb50 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb54 : bv 32 := 0xfeb68f23.
Lemma F_cbb54 : fetch_word Asan.M.loaded_segments (0xcbb54 : word) = Some W_cbb54.
Proof. vm_refl. Qed.
Lemma D_cbb54 : decode_any W_cbb54 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb58 : bv 32 := 0x0ce66463.
Lemma F_cbb58 : fetch_word Asan.M.loaded_segments (0xcbb58 : word) = Some W_cbb58.
Proof. vm_refl. Qed.
Lemma D_cbb58 : decode_any W_cbb58 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb5c : bv 32 := 0x00b501a3.
Lemma F_cbb5c : fetch_word Asan.M.loaded_segments (0xcbb5c : word) = Some W_cbb5c.
Proof. vm_refl. Qed.
Lemma D_cbb5c : decode_any W_cbb5c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb60 : bv 32 := 0x00900793.
Lemma F_cbb60 : fetch_word Asan.M.loaded_segments (0xcbb60 : word) = Some W_cbb60.
Proof. vm_refl. Qed.
Lemma D_cbb60 : decode_any W_cbb60 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb64 : bv 32 := 0xfeb68e23.
Lemma F_cbb64 : fetch_word Asan.M.loaded_segments (0xcbb64 : word) = Some W_cbb64.
Proof. vm_refl. Qed.
Lemma D_cbb64 : decode_any W_cbb64 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb68 : bv 32 := 0x0af66c63.
Lemma F_cbb68 : fetch_word Asan.M.loaded_segments (0xcbb68 : word) = Some W_cbb68.
Proof. vm_refl. Qed.
Lemma D_cbb68 : decode_any W_cbb68 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb6c : bv 32 := 0x40a006bb.
Lemma F_cbb6c : fetch_word Asan.M.loaded_segments (0xcbb6c : word) = Some W_cbb6c.
Proof. vm_refl. Qed.
Lemma D_cbb6c : decode_any W_cbb6c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb70 : bv 32 := 0x03859813.
Lemma F_cbb70 : fetch_word Asan.M.loaded_segments (0xcbb70 : word) = Some W_cbb70.
Proof. vm_refl. Qed.
Lemma D_cbb70 : decode_any W_cbb70 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb74 : bv 32 := 0x101015b7.
Lemma F_cbb74 : fetch_word Asan.M.loaded_segments (0xcbb74 : word) = Some W_cbb74.
Proof. vm_refl. Qed.
Lemma D_cbb74 : decode_any W_cbb74 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb78 : bv 32 := 0x0036f693.
Lemma F_cbb78 : fetch_word Asan.M.loaded_segments (0xcbb78 : word) = Some W_cbb78.
Proof. vm_refl. Qed.
Lemma D_cbb78 : decode_any W_cbb78 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb7c : bv 32 := 0x00459713.
Lemma F_cbb7c : fetch_word Asan.M.loaded_segments (0xcbb7c : word) = Some W_cbb7c.
Proof. vm_refl. Qed.
Lemma D_cbb7c : decode_any W_cbb7c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb80 : bv 32 := 0x40d60633.
Lemma F_cbb80 : fetch_word Asan.M.loaded_segments (0xcbb80 : word) = Some W_cbb80.
Proof. vm_refl. Qed.
Lemma D_cbb80 : decode_any W_cbb80 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb84 : bv 32 := 0x00d505b3.
Lemma F_cbb84 : fetch_word Asan.M.loaded_segments (0xcbb84 : word) = Some W_cbb84.
Proof. vm_refl. Qed.
Lemma D_cbb84 : decode_any W_cbb84 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb88 : bv 32 := 0x10070693.
Lemma F_cbb88 : fetch_word Asan.M.loaded_segments (0xcbb88 : word) = Some W_cbb88.
Proof. vm_refl. Qed.
Lemma D_cbb88 : decode_any W_cbb88 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb8c : bv 32 := 0xffc67713.
Lemma F_cbb8c : fetch_word Asan.M.loaded_segments (0xcbb8c : word) = Some W_cbb8c.
Proof. vm_refl. Qed.
Lemma D_cbb8c : decode_any W_cbb8c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb90 : bv 32 := 0x02d83633.
Lemma F_cbb90 : fetch_word Asan.M.loaded_segments (0xcbb90 : word) = Some W_cbb90.
Proof. vm_refl. Qed.
Lemma D_cbb90 : decode_any W_cbb90 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb94 : bv 32 := 0x00c5a023.
Lemma F_cbb94 : fetch_word Asan.M.loaded_segments (0xcbb94 : word) = Some W_cbb94.
Proof. vm_refl. Qed.
Lemma D_cbb94 : decode_any W_cbb94 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb98 : bv 32 := 0x00e586b3.
Lemma F_cbb98 : fetch_word Asan.M.loaded_segments (0xcbb98 : word) = Some W_cbb98.
Proof. vm_refl. Qed.
Lemma D_cbb98 : decode_any W_cbb98 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbb9c : bv 32 := 0xfec6ae23.
Lemma F_cbb9c : fetch_word Asan.M.loaded_segments (0xcbb9c : word) = Some W_cbb9c.
Proof. vm_refl. Qed.
Lemma D_cbb9c : decode_any W_cbb9c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbba0 : bv 32 := 0x08f76063.
Lemma F_cbba0 : fetch_word Asan.M.loaded_segments (0xcbba0 : word) = Some W_cbba0.
Proof. vm_refl. Qed.
Lemma D_cbba0 : decode_any W_cbba0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbba4 : bv 32 := 0x00c5a223.
Lemma F_cbba4 : fetch_word Asan.M.loaded_segments (0xcbba4 : word) = Some W_cbba4.
Proof. vm_refl. Qed.
Lemma D_cbba4 : decode_any W_cbba4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbba8 : bv 32 := 0x00c5a423.
Lemma F_cbba8 : fetch_word Asan.M.loaded_segments (0xcbba8 : word) = Some W_cbba8.
Proof. vm_refl. Qed.
Lemma D_cbba8 : decode_any W_cbba8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbac : bv 32 := 0x01900793.
Lemma F_cbbac : fetch_word Asan.M.loaded_segments (0xcbbac : word) = Some W_cbbac.
Proof. vm_refl. Qed.
Lemma D_cbbac : decode_any W_cbbac = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbb0 : bv 32 := 0xfec6aa23.
Lemma F_cbbb0 : fetch_word Asan.M.loaded_segments (0xcbbb0 : word) = Some W_cbbb0.
Proof. vm_refl. Qed.
Lemma D_cbbb0 : decode_any W_cbbb0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbb4 : bv 32 := 0xfec6ac23.
Lemma F_cbbb4 : fetch_word Asan.M.loaded_segments (0xcbbb4 : word) = Some W_cbbb4.
Proof. vm_refl. Qed.
Lemma D_cbbb4 : decode_any W_cbbb4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbb8 : bv 32 := 0x06f76463.
Lemma F_cbbb8 : fetch_word Asan.M.loaded_segments (0xcbbb8 : word) = Some W_cbbb8.
Proof. vm_refl. Qed.
Lemma D_cbbb8 : decode_any W_cbbb8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbbc : bv 32 := 0x00c5a623.
Lemma F_cbbbc : fetch_word Asan.M.loaded_segments (0xcbbbc : word) = Some W_cbbbc.
Proof. vm_refl. Qed.
Lemma D_cbbbc : decode_any W_cbbbc = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbc0 : bv 32 := 0x00c5a823.
Lemma F_cbbc0 : fetch_word Asan.M.loaded_segments (0xcbbc0 : word) = Some W_cbbc0.
Proof. vm_refl. Qed.
Lemma D_cbbc0 : decode_any W_cbbc0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbc4 : bv 32 := 0x00c5aa23.
Lemma F_cbbc4 : fetch_word Asan.M.loaded_segments (0xcbbc4 : word) = Some W_cbbc4.
Proof. vm_refl. Qed.
Lemma D_cbbc4 : decode_any W_cbbc4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbc8 : bv 32 := 0x00c5ac23.
Lemma F_cbbc8 : fetch_word Asan.M.loaded_segments (0xcbbc8 : word) = Some W_cbbc8.
Proof. vm_refl. Qed.
Lemma D_cbbc8 : decode_any W_cbbc8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbcc : bv 32 := 0x0045f793.
Lemma F_cbbcc : fetch_word Asan.M.loaded_segments (0xcbbcc : word) = Some W_cbbcc.
Proof. vm_refl. Qed.
Lemma D_cbbcc : decode_any W_cbbcc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbd0 : bv 32 := 0x02000813.
Lemma F_cbbd0 : fetch_word Asan.M.loaded_segments (0xcbbd0 : word) = Some W_cbbd0.
Proof. vm_refl. Qed.
Lemma D_cbbd0 : decode_any W_cbbd0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbd4 : bv 32 := 0x01878793.
Lemma F_cbbd4 : fetch_word Asan.M.loaded_segments (0xcbbd4 : word) = Some W_cbbd4.
Proof. vm_refl. Qed.
Lemma D_cbbd4 : decode_any W_cbbd4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbd8 : bv 32 := 0x40f70733.
Lemma F_cbbd8 : fetch_word Asan.M.loaded_segments (0xcbbd8 : word) = Some W_cbbd8.
Proof. vm_refl. Qed.
Lemma D_cbbd8 : decode_any W_cbbd8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbdc : bv 32 := 0xfec6a223.
Lemma F_cbbdc : fetch_word Asan.M.loaded_segments (0xcbbdc : word) = Some W_cbbdc.
Proof. vm_refl. Qed.
Lemma D_cbbdc : decode_any W_cbbdc = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbe0 : bv 32 := 0xfec6a423.
Lemma F_cbbe0 : fetch_word Asan.M.loaded_segments (0xcbbe0 : word) = Some W_cbbe0.
Proof. vm_refl. Qed.
Lemma D_cbbe0 : decode_any W_cbbe0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbe4 : bv 32 := 0xfec6a623.
Lemma F_cbbe4 : fetch_word Asan.M.loaded_segments (0xcbbe4 : word) = Some W_cbbe4.
Proof. vm_refl. Qed.
Lemma D_cbbe4 : decode_any W_cbbe4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbe8 : bv 32 := 0xfec6a823.
Lemma F_cbbe8 : fetch_word Asan.M.loaded_segments (0xcbbe8 : word) = Some W_cbbe8.
Proof. vm_refl. Qed.
Lemma D_cbbe8 : decode_any W_cbbe8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbec : bv 32 := 0x03076a63.
Lemma F_cbbec : fetch_word Asan.M.loaded_segments (0xcbbec : word) = Some W_cbbec.
Proof. vm_refl. Qed.
Lemma D_cbbec : decode_any W_cbbec = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbf0 : bv 32 := 0x02061613.
Lemma F_cbbf0 : fetch_word Asan.M.loaded_segments (0xcbbf0 : word) = Some W_cbbf0.
Proof. vm_refl. Qed.
Lemma D_cbbf0 : decode_any W_cbbf0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbf4 : bv 32 := 0x00f585b3.
Lemma F_cbbf4 : fetch_word Asan.M.loaded_segments (0xcbbf4 : word) = Some W_cbbf4.
Proof. vm_refl. Qed.
Lemma D_cbbf4 : decode_any W_cbbf4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbf8 : bv 32 := 0x02065693.
Lemma F_cbbf8 : fetch_word Asan.M.loaded_segments (0xcbbf8 : word) = Some W_cbbf8.
Proof. vm_refl. Qed.
Lemma D_cbbf8 : decode_any W_cbbf8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbbfc : bv 32 := 0x00d66633.
Lemma F_cbbfc : fetch_word Asan.M.loaded_segments (0xcbbfc : word) = Some W_cbbfc.
Proof. vm_refl. Qed.
Lemma D_cbbfc : decode_any W_cbbfc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc00 : bv 32 := 0x01f00693.
Lemma F_cbc00 : fetch_word Asan.M.loaded_segments (0xcbc00 : word) = Some W_cbc00.
Proof. vm_refl. Qed.
Lemma D_cbc00 : decode_any W_cbc00 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc04 : bv 32 := 0x00c5b023.
Lemma F_cbc04 : fetch_word Asan.M.loaded_segments (0xcbc04 : word) = Some W_cbc04.
Proof. vm_refl. Qed.
Lemma D_cbc04 : decode_any W_cbc04 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc08 : bv 32 := 0x00c5b423.
Lemma F_cbc08 : fetch_word Asan.M.loaded_segments (0xcbc08 : word) = Some W_cbc08.
Proof. vm_refl. Qed.
Lemma D_cbc08 : decode_any W_cbc08 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc0c : bv 32 := 0x00c5b823.
Lemma F_cbc0c : fetch_word Asan.M.loaded_segments (0xcbc0c : word) = Some W_cbc0c.
Proof. vm_refl. Qed.
Lemma D_cbc0c : decode_any W_cbc0c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc10 : bv 32 := 0x00c5bc23.
Lemma F_cbc10 : fetch_word Asan.M.loaded_segments (0xcbc10 : word) = Some W_cbc10.
Proof. vm_refl. Qed.
Lemma D_cbc10 : decode_any W_cbc10 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc14 : bv 32 := 0xfe070713.
Lemma F_cbc14 : fetch_word Asan.M.loaded_segments (0xcbc14 : word) = Some W_cbc14.
Proof. vm_refl. Qed.
Lemma D_cbc14 : decode_any W_cbc14 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc18 : bv 32 := 0x02058593.
Lemma F_cbc18 : fetch_word Asan.M.loaded_segments (0xcbc18 : word) = Some W_cbc18.
Proof. vm_refl. Qed.
Lemma D_cbc18 : decode_any W_cbc18 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc1c : bv 32 := 0xfee6e4e3.
Lemma F_cbc1c : fetch_word Asan.M.loaded_segments (0xcbc1c : word) = Some W_cbc1c.
Proof. vm_refl. Qed.
Lemma D_cbc1c : decode_any W_cbc1c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc20 : bv 32 := 0x00008067.
Lemma F_cbc20 : fetch_word Asan.M.loaded_segments (0xcbc20 : word) = Some W_cbc20.
Proof. vm_refl. Qed.
Lemma D_cbc20 : decode_any W_cbc20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc24 : bv 32 := 0xff010113.
Lemma F_cbc24 : fetch_word Asan.M.loaded_segments (0xcbc24 : word) = Some W_cbc24.
Proof. vm_refl. Qed.
Lemma D_cbc24 : decode_any W_cbc24 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc28 : bv 32 := 0x00113423.
Lemma F_cbc28 : fetch_word Asan.M.loaded_segments (0xcbc28 : word) = Some W_cbc28.
Proof. vm_refl. Qed.
Lemma D_cbc28 : decode_any W_cbc28 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc2c : bv 32 := 0x00813023.
Lemma F_cbc2c : fetch_word Asan.M.loaded_segments (0xcbc2c : word) = Some W_cbc2c.
Proof. vm_refl. Qed.
Lemma D_cbc2c : decode_any W_cbc2c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc30 : bv 32 := 0x00058413.
Lemma F_cbc30 : fetch_word Asan.M.loaded_segments (0xcbc30 : word) = Some W_cbc30.
Proof. vm_refl. Qed.
Lemma D_cbc30 : decode_any W_cbc30 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc34 : bv 32 := 0x02c000ef.
Lemma F_cbc34 : fetch_word Asan.M.loaded_segments (0xcbc34 : word) = Some W_cbc34.
Proof. vm_refl. Qed.
Lemma D_cbc34 : decode_any W_cbc34 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc38 : bv 32 := 0x00054583.
Lemma F_cbc38 : fetch_word Asan.M.loaded_segments (0xcbc38 : word) = Some W_cbc38.
Proof. vm_refl. Qed.
Lemma D_cbc38 : decode_any W_cbc38 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc3c : bv 32 := 0x0ff47613.
Lemma F_cbc3c : fetch_word Asan.M.loaded_segments (0xcbc3c : word) = Some W_cbc3c.
Proof. vm_refl. Qed.
Lemma D_cbc3c : decode_any W_cbc3c = Some (OpImm ALU_AND 12 8 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc40 : bv 32 := 0x00c5c5b3.
Lemma F_cbc40 : fetch_word Asan.M.loaded_segments (0xcbc40 : word) = Some W_cbc40.
Proof. vm_refl. Qed.
Lemma D_cbc40 : decode_any W_cbc40 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc44 : bv 32 := 0x00b035b3.
Lemma F_cbc44 : fetch_word Asan.M.loaded_segments (0xcbc44 : word) = Some W_cbc44.
Proof. vm_refl. Qed.
Lemma D_cbc44 : decode_any W_cbc44 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc48 : bv 32 := 0xfff58593.
Lemma F_cbc48 : fetch_word Asan.M.loaded_segments (0xcbc48 : word) = Some W_cbc48.
Proof. vm_refl. Qed.
Lemma D_cbc48 : decode_any W_cbc48 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc4c : bv 32 := 0x00a5f533.
Lemma F_cbc4c : fetch_word Asan.M.loaded_segments (0xcbc4c : word) = Some W_cbc4c.
Proof. vm_refl. Qed.
Lemma D_cbc4c : decode_any W_cbc4c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc50 : bv 32 := 0x00813083.
Lemma F_cbc50 : fetch_word Asan.M.loaded_segments (0xcbc50 : word) = Some W_cbc50.
Proof. vm_refl. Qed.
Lemma D_cbc50 : decode_any W_cbc50 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc54 : bv 32 := 0x00013403.
Lemma F_cbc54 : fetch_word Asan.M.loaded_segments (0xcbc54 : word) = Some W_cbc54.
Proof. vm_refl. Qed.
Lemma D_cbc54 : decode_any W_cbc54 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc58 : bv 32 := 0x01010113.
Lemma F_cbc58 : fetch_word Asan.M.loaded_segments (0xcbc58 : word) = Some W_cbc58.
Proof. vm_refl. Qed.
Lemma D_cbc58 : decode_any W_cbc58 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc5c : bv 32 := 0x00008067.
Lemma F_cbc5c : fetch_word Asan.M.loaded_segments (0xcbc5c : word) = Some W_cbc5c.
Proof. vm_refl. Qed.
Lemma D_cbc5c : decode_any W_cbc5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc60 : bv 32 := 0xff010113.
Lemma F_cbc60 : fetch_word Asan.M.loaded_segments (0xcbc60 : word) = Some W_cbc60.
Proof. vm_refl. Qed.
Lemma D_cbc60 : decode_any W_cbc60 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc64 : bv 32 := 0x00113423.
Lemma F_cbc64 : fetch_word Asan.M.loaded_segments (0xcbc64 : word) = Some W_cbc64.
Proof. vm_refl. Qed.
Lemma D_cbc64 : decode_any W_cbc64 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc68 : bv 32 := 0x00813023.
Lemma F_cbc68 : fetch_word Asan.M.loaded_segments (0xcbc68 : word) = Some W_cbc68.
Proof. vm_refl. Qed.
Lemma D_cbc68 : decode_any W_cbc68 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc6c : bv 32 := 0x0ff5f593.
Lemma F_cbc6c : fetch_word Asan.M.loaded_segments (0xcbc6c : word) = Some W_cbc6c.
Proof. vm_refl. Qed.
Lemma D_cbc6c : decode_any W_cbc6c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc70 : bv 32 := 0x08058663.
Lemma F_cbc70 : fetch_word Asan.M.loaded_segments (0xcbc70 : word) = Some W_cbc70.
Proof. vm_refl. Qed.
Lemma D_cbc70 : decode_any W_cbc70 = Some (Branch BC_EQ 11 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc74 : bv 32 := 0x00757613.
Lemma F_cbc74 : fetch_word Asan.M.loaded_segments (0xcbc74 : word) = Some W_cbc74.
Proof. vm_refl. Qed.
Lemma D_cbc74 : decode_any W_cbc74 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc78 : bv 32 := 0x02060263.
Lemma F_cbc78 : fetch_word Asan.M.loaded_segments (0xcbc78 : word) = Some W_cbc78.
Proof. vm_refl. Qed.
Lemma D_cbc78 : decode_any W_cbc78 = Some (Branch BC_EQ 12 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc7c : bv 32 := 0x00150613.
Lemma F_cbc7c : fetch_word Asan.M.loaded_segments (0xcbc7c : word) = Some W_cbc7c.
Proof. vm_refl. Qed.
Lemma D_cbc7c : decode_any W_cbc7c = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc80 : bv 32 := 0x00054683.
Lemma F_cbc80 : fetch_word Asan.M.loaded_segments (0xcbc80 : word) = Some W_cbc80.
Proof. vm_refl. Qed.
Lemma D_cbc80 : decode_any W_cbc80 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc84 : bv 32 := 0x0a068663.
Lemma F_cbc84 : fetch_word Asan.M.loaded_segments (0xcbc84 : word) = Some W_cbc84.
Proof. vm_refl. Qed.
Lemma D_cbc84 : decode_any W_cbc84 = Some (Branch BC_EQ 13 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc88 : bv 32 := 0x0ab68463.
Lemma F_cbc88 : fetch_word Asan.M.loaded_segments (0xcbc88 : word) = Some W_cbc88.
Proof. vm_refl. Qed.
Lemma D_cbc88 : decode_any W_cbc88 = Some (Branch BC_EQ 13 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc8c : bv 32 := 0x00150513.
Lemma F_cbc8c : fetch_word Asan.M.loaded_segments (0xcbc8c : word) = Some W_cbc8c.
Proof. vm_refl. Qed.
Lemma D_cbc8c : decode_any W_cbc8c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc90 : bv 32 := 0x00767693.
Lemma F_cbc90 : fetch_word Asan.M.loaded_segments (0xcbc90 : word) = Some W_cbc90.
Proof. vm_refl. Qed.
Lemma D_cbc90 : decode_any W_cbc90 = Some (OpImm ALU_AND 13 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc94 : bv 32 := 0x00160613.
Lemma F_cbc94 : fetch_word Asan.M.loaded_segments (0xcbc94 : word) = Some W_cbc94.
Proof. vm_refl. Qed.
Lemma D_cbc94 : decode_any W_cbc94 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc98 : bv 32 := 0xfe0694e3.
Lemma F_cbc98 : fetch_word Asan.M.loaded_segments (0xcbc98 : word) = Some W_cbc98.
Proof. vm_refl. Qed.
Lemma D_cbc98 : decode_any W_cbc98 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbc9c : bv 32 := 0xfff44617.
Lemma F_cbc9c : fetch_word Asan.M.loaded_segments (0xcbc9c : word) = Some W_cbc9c.
Proof. vm_refl. Qed.
Lemma D_cbc9c : decode_any W_cbc9c = Some (Auipc 12 1048388, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbca0 : bv 32 := 0x6ec63603.
Lemma F_cbca0 : fetch_word Asan.M.loaded_segments (0xcbca0 : word) = Some W_cbca0.
Proof. vm_refl. Qed.
Lemma D_cbca0 : decode_any W_cbca0 = Some (Load SZ8 true 12 12 1772, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbca4 : bv 32 := 0x00053703.
Lemma F_cbca4 : fetch_word Asan.M.loaded_segments (0xcbca4 : word) = Some W_cbca4.
Proof. vm_refl. Qed.
Lemma D_cbca4 : decode_any W_cbca4 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbca8 : bv 32 := 0xfff44697.
Lemma F_cbca8 : fetch_word Asan.M.loaded_segments (0xcbca8 : word) = Some W_cbca8.
Proof. vm_refl. Qed.
Lemma D_cbca8 : decode_any W_cbca8 = Some (Auipc 13 1048388, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcac : bv 32 := 0x6c86b683.
Lemma F_cbcac : fetch_word Asan.M.loaded_segments (0xcbcac : word) = Some W_cbcac.
Proof. vm_refl. Qed.
Lemma D_cbcac : decode_any W_cbcac = Some (Load SZ8 true 13 13 1736, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcb0 : bv 32 := 0x40e607b3.
Lemma F_cbcb0 : fetch_word Asan.M.loaded_segments (0xcbcb0 : word) = Some W_cbcb0.
Proof. vm_refl. Qed.
Lemma D_cbcb0 : decode_any W_cbcb0 = Some (Op ALU_SUB 15 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcb4 : bv 32 := 0x00e7e7b3.
Lemma F_cbcb4 : fetch_word Asan.M.loaded_segments (0xcbcb4 : word) = Some W_cbcb4.
Proof. vm_refl. Qed.
Lemma D_cbcb4 : decode_any W_cbcb4 = Some (Op ALU_OR 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcb8 : bv 32 := 0x00d7f7b3.
Lemma F_cbcb8 : fetch_word Asan.M.loaded_segments (0xcbcb8 : word) = Some W_cbcb8.
Proof. vm_refl. Qed.
Lemma D_cbcb8 : decode_any W_cbcb8 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcbc : bv 32 := 0x04d79e63.
Lemma F_cbcbc : fetch_word Asan.M.loaded_segments (0xcbcbc : word) = Some W_cbcbc.
Proof. vm_refl. Qed.
Lemma D_cbcbc : decode_any W_cbcbc = Some (Branch BC_NE 15 13 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcc0 : bv 32 := 0x00160793.
Lemma F_cbcc0 : fetch_word Asan.M.loaded_segments (0xcbcc0 : word) = Some W_cbcc0.
Proof. vm_refl. Qed.
Lemma D_cbcc0 : decode_any W_cbcc0 = Some (OpImm ALU_ADD 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcc4 : bv 32 := 0x02f587b3.
Lemma F_cbcc4 : fetch_word Asan.M.loaded_segments (0xcbcc4 : word) = Some W_cbcc4.
Proof. vm_refl. Qed.
Lemma D_cbcc4 : decode_any W_cbcc4 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcc8 : bv 32 := 0x00f74733.
Lemma F_cbcc8 : fetch_word Asan.M.loaded_segments (0xcbcc8 : word) = Some W_cbcc8.
Proof. vm_refl. Qed.
Lemma D_cbcc8 : decode_any W_cbcc8 = Some (Op ALU_XOR 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbccc : bv 32 := 0x40e60833.
Lemma F_cbccc : fetch_word Asan.M.loaded_segments (0xcbccc : word) = Some W_cbccc.
Proof. vm_refl. Qed.
Lemma D_cbccc : decode_any W_cbccc = Some (Op ALU_SUB 16 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcd0 : bv 32 := 0x00e86733.
Lemma F_cbcd0 : fetch_word Asan.M.loaded_segments (0xcbcd0 : word) = Some W_cbcd0.
Proof. vm_refl. Qed.
Lemma D_cbcd0 : decode_any W_cbcd0 = Some (Op ALU_OR 14 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcd4 : bv 32 := 0x00d77733.
Lemma F_cbcd4 : fetch_word Asan.M.loaded_segments (0xcbcd4 : word) = Some W_cbcd4.
Proof. vm_refl. Qed.
Lemma D_cbcd4 : decode_any W_cbcd4 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcd8 : bv 32 := 0x04d71063.
Lemma F_cbcd8 : fetch_word Asan.M.loaded_segments (0xcbcd8 : word) = Some W_cbcd8.
Proof. vm_refl. Qed.
Lemma D_cbcd8 : decode_any W_cbcd8 = Some (Branch BC_NE 14 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcdc : bv 32 := 0x00853703.
Lemma F_cbcdc : fetch_word Asan.M.loaded_segments (0xcbcdc : word) = Some W_cbcdc.
Proof. vm_refl. Qed.
Lemma D_cbcdc : decode_any W_cbcdc = Some (Load SZ8 true 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbce0 : bv 32 := 0x00850813.
Lemma F_cbce0 : fetch_word Asan.M.loaded_segments (0xcbce0 : word) = Some W_cbce0.
Proof. vm_refl. Qed.
Lemma D_cbce0 : decode_any W_cbce0 = Some (OpImm ALU_ADD 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbce4 : bv 32 := 0x40e60533.
Lemma F_cbce4 : fetch_word Asan.M.loaded_segments (0xcbce4 : word) = Some W_cbce4.
Proof. vm_refl. Qed.
Lemma D_cbce4 : decode_any W_cbce4 = Some (Op ALU_SUB 10 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbce8 : bv 32 := 0x00e56533.
Lemma F_cbce8 : fetch_word Asan.M.loaded_segments (0xcbce8 : word) = Some W_cbce8.
Proof. vm_refl. Qed.
Lemma D_cbce8 : decode_any W_cbce8 = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcec : bv 32 := 0x00d578b3.
Lemma F_cbcec : fetch_word Asan.M.loaded_segments (0xcbcec : word) = Some W_cbcec.
Proof. vm_refl. Qed.
Lemma D_cbcec : decode_any W_cbcec = Some (Op ALU_AND 17 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcf0 : bv 32 := 0x00080513.
Lemma F_cbcf0 : fetch_word Asan.M.loaded_segments (0xcbcf0 : word) = Some W_cbcf0.
Proof. vm_refl. Qed.
Lemma D_cbcf0 : decode_any W_cbcf0 = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcf4 : bv 32 := 0xfcd88ae3.
Lemma F_cbcf4 : fetch_word Asan.M.loaded_segments (0xcbcf4 : word) = Some W_cbcf4.
Proof. vm_refl. Qed.
Lemma D_cbcf4 : decode_any W_cbcf4 = Some (Branch BC_EQ 17 13 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcf8 : bv 32 := 0x0240006f.
Lemma F_cbcf8 : fetch_word Asan.M.loaded_segments (0xcbcf8 : word) = Some W_cbcf8.
Proof. vm_refl. Qed.
Lemma D_cbcf8 : decode_any W_cbcf8 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcfc : bv 32 := 0x00050413.
Lemma F_cbcfc : fetch_word Asan.M.loaded_segments (0xcbcfc : word) = Some W_cbcfc.
Proof. vm_refl. Qed.
Lemma D_cbcfc : decode_any W_cbcfc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd00 : bv 32 := 0xeb1810ef.
Lemma F_cbd00 : fetch_word Asan.M.loaded_segments (0xcbd00 : word) = Some W_cbd00.
Proof. vm_refl. Qed.
Lemma D_cbd00 : decode_any W_cbd00 = Some (Jal 1 1580720, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd04 : bv 32 := 0x00a40533.
Lemma F_cbd04 : fetch_word Asan.M.loaded_segments (0xcbd04 : word) = Some W_cbd04.
Proof. vm_refl. Qed.
Lemma D_cbd04 : decode_any W_cbd04 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd08 : bv 32 := 0x00813083.
Lemma F_cbd08 : fetch_word Asan.M.loaded_segments (0xcbd08 : word) = Some W_cbd08.
Proof. vm_refl. Qed.
Lemma D_cbd08 : decode_any W_cbd08 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd0c : bv 32 := 0x00013403.
Lemma F_cbd0c : fetch_word Asan.M.loaded_segments (0xcbd0c : word) = Some W_cbd0c.
Proof. vm_refl. Qed.
Lemma D_cbd0c : decode_any W_cbd0c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd10 : bv 32 := 0x01010113.
Lemma F_cbd10 : fetch_word Asan.M.loaded_segments (0xcbd10 : word) = Some W_cbd10.
Proof. vm_refl. Qed.
Lemma D_cbd10 : decode_any W_cbd10 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd14 : bv 32 := 0x00008067.
Lemma F_cbd14 : fetch_word Asan.M.loaded_segments (0xcbd14 : word) = Some W_cbd14.
Proof. vm_refl. Qed.
Lemma D_cbd14 : decode_any W_cbd14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd18 : bv 32 := 0x00050813.
Lemma F_cbd18 : fetch_word Asan.M.loaded_segments (0xcbd18 : word) = Some W_cbd18.
Proof. vm_refl. Qed.
Lemma D_cbd18 : decode_any W_cbd18 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd1c : bv 32 := 0xfff80513.
Lemma F_cbd1c : fetch_word Asan.M.loaded_segments (0xcbd1c : word) = Some W_cbd1c.
Proof. vm_refl. Qed.
Lemma D_cbd1c : decode_any W_cbd1c = Some (OpImm ALU_ADD 10 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd20 : bv 32 := 0x00154603.
Lemma F_cbd20 : fetch_word Asan.M.loaded_segments (0xcbd20 : word) = Some W_cbd20.
Proof. vm_refl. Qed.
Lemma D_cbd20 : decode_any W_cbd20 = Some (Load SZ1 false 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd24 : bv 32 := 0x00150513.
Lemma F_cbd24 : fetch_word Asan.M.loaded_segments (0xcbd24 : word) = Some W_cbd24.
Proof. vm_refl. Qed.
Lemma D_cbd24 : decode_any W_cbd24 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd28 : bv 32 := 0x00060463.
Lemma F_cbd28 : fetch_word Asan.M.loaded_segments (0xcbd28 : word) = Some W_cbd28.
Proof. vm_refl. Qed.
Lemma D_cbd28 : decode_any W_cbd28 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd2c : bv 32 := 0xfeb61ae3.
Lemma F_cbd2c : fetch_word Asan.M.loaded_segments (0xcbd2c : word) = Some W_cbd2c.
Proof. vm_refl. Qed.
Lemma D_cbd2c : decode_any W_cbd2c = Some (Branch BC_NE 12 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd30 : bv 32 := 0x00813083.
Lemma F_cbd30 : fetch_word Asan.M.loaded_segments (0xcbd30 : word) = Some W_cbd30.
Proof. vm_refl. Qed.
Lemma D_cbd30 : decode_any W_cbd30 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd34 : bv 32 := 0x00013403.
Lemma F_cbd34 : fetch_word Asan.M.loaded_segments (0xcbd34 : word) = Some W_cbd34.
Proof. vm_refl. Qed.
Lemma D_cbd34 : decode_any W_cbd34 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd38 : bv 32 := 0x01010113.
Lemma F_cbd38 : fetch_word Asan.M.loaded_segments (0xcbd38 : word) = Some W_cbd38.
Proof. vm_refl. Qed.
Lemma D_cbd38 : decode_any W_cbd38 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd3c : bv 32 := 0x00008067.
Lemma F_cbd3c : fetch_word Asan.M.loaded_segments (0xcbd3c : word) = Some W_cbd3c.
Proof. vm_refl. Qed.
Lemma D_cbd3c : decode_any W_cbd3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd40 : bv 32 := 0x00054603.
Lemma F_cbd40 : fetch_word Asan.M.loaded_segments (0xcbd40 : word) = Some W_cbd40.
Proof. vm_refl. Qed.
Lemma D_cbd40 : decode_any W_cbd40 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd44 : bv 32 := 0x0005c683.
Lemma F_cbd44 : fetch_word Asan.M.loaded_segments (0xcbd44 : word) = Some W_cbd44.
Proof. vm_refl. Qed.
Lemma D_cbd44 : decode_any W_cbd44 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd48 : bv 32 := 0x02060463.
Lemma F_cbd48 : fetch_word Asan.M.loaded_segments (0xcbd48 : word) = Some W_cbd48.
Proof. vm_refl. Qed.
Lemma D_cbd48 : decode_any W_cbd48 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd4c : bv 32 := 0x02d61263.
Lemma F_cbd4c : fetch_word Asan.M.loaded_segments (0xcbd4c : word) = Some W_cbd4c.
Proof. vm_refl. Qed.
Lemma D_cbd4c : decode_any W_cbd4c = Some (Branch BC_NE 12 13 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd50 : bv 32 := 0x00158593.
Lemma F_cbd50 : fetch_word Asan.M.loaded_segments (0xcbd50 : word) = Some W_cbd50.
Proof. vm_refl. Qed.
Lemma D_cbd50 : decode_any W_cbd50 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd54 : bv 32 := 0x00150513.
Lemma F_cbd54 : fetch_word Asan.M.loaded_segments (0xcbd54 : word) = Some W_cbd54.
Proof. vm_refl. Qed.
Lemma D_cbd54 : decode_any W_cbd54 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd58 : bv 32 := 0x00054603.
Lemma F_cbd58 : fetch_word Asan.M.loaded_segments (0xcbd58 : word) = Some W_cbd58.
Proof. vm_refl. Qed.
Lemma D_cbd58 : decode_any W_cbd58 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd5c : bv 32 := 0x0005c683.
Lemma F_cbd5c : fetch_word Asan.M.loaded_segments (0xcbd5c : word) = Some W_cbd5c.
Proof. vm_refl. Qed.
Lemma D_cbd5c : decode_any W_cbd5c = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd60 : bv 32 := 0x00060863.
Lemma F_cbd60 : fetch_word Asan.M.loaded_segments (0xcbd60 : word) = Some W_cbd60.
Proof. vm_refl. Qed.
Lemma D_cbd60 : decode_any W_cbd60 = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd64 : bv 32 := 0x00158593.
Lemma F_cbd64 : fetch_word Asan.M.loaded_segments (0xcbd64 : word) = Some W_cbd64.
Proof. vm_refl. Qed.
Lemma D_cbd64 : decode_any W_cbd64 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd68 : bv 32 := 0x00150513.
Lemma F_cbd68 : fetch_word Asan.M.loaded_segments (0xcbd68 : word) = Some W_cbd68.
Proof. vm_refl. Qed.
Lemma D_cbd68 : decode_any W_cbd68 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd6c : bv 32 := 0xfed606e3.
Lemma F_cbd6c : fetch_word Asan.M.loaded_segments (0xcbd6c : word) = Some W_cbd6c.
Proof. vm_refl. Qed.
Lemma D_cbd6c : decode_any W_cbd6c = Some (Branch BC_EQ 12 13 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd70 : bv 32 := 0x40d60533.
Lemma F_cbd70 : fetch_word Asan.M.loaded_segments (0xcbd70 : word) = Some W_cbd70.
Proof. vm_refl. Qed.
Lemma D_cbd70 : decode_any W_cbd70 = Some (Op ALU_SUB 10 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd74 : bv 32 := 0x00008067.
Lemma F_cbd74 : fetch_word Asan.M.loaded_segments (0xcbd74 : word) = Some W_cbd74.
Proof. vm_refl. Qed.
Lemma D_cbd74 : decode_any W_cbd74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd78 : bv 32 := 0xfe010113.
Lemma F_cbd78 : fetch_word Asan.M.loaded_segments (0xcbd78 : word) = Some W_cbd78.
Proof. vm_refl. Qed.
Lemma D_cbd78 : decode_any W_cbd78 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd7c : bv 32 := 0x00113c23.
Lemma F_cbd7c : fetch_word Asan.M.loaded_segments (0xcbd7c : word) = Some W_cbd7c.
Proof. vm_refl. Qed.
Lemma D_cbd7c : decode_any W_cbd7c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd80 : bv 32 := 0x00813823.
Lemma F_cbd80 : fetch_word Asan.M.loaded_segments (0xcbd80 : word) = Some W_cbd80.
Proof. vm_refl. Qed.
Lemma D_cbd80 : decode_any W_cbd80 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd84 : bv 32 := 0x00913423.
Lemma F_cbd84 : fetch_word Asan.M.loaded_segments (0xcbd84 : word) = Some W_cbd84.
Proof. vm_refl. Qed.
Lemma D_cbd84 : decode_any W_cbd84 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd88 : bv 32 := 0x01213023.
Lemma F_cbd88 : fetch_word Asan.M.loaded_segments (0xcbd88 : word) = Some W_cbd88.
Proof. vm_refl. Qed.
Lemma D_cbd88 : decode_any W_cbd88 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd8c : bv 32 := 0x00060913.
Lemma F_cbd8c : fetch_word Asan.M.loaded_segments (0xcbd8c : word) = Some W_cbd8c.
Proof. vm_refl. Qed.
Lemma D_cbd8c : decode_any W_cbd8c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd90 : bv 32 := 0x00058413.
Lemma F_cbd90 : fetch_word Asan.M.loaded_segments (0xcbd90 : word) = Some W_cbd90.
Proof. vm_refl. Qed.
Lemma D_cbd90 : decode_any W_cbd90 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd94 : bv 32 := 0xe6d810ef.
Lemma F_cbd94 : fetch_word Asan.M.loaded_segments (0xcbd94 : word) = Some W_cbd94.
Proof. vm_refl. Qed.
Lemma D_cbd94 : decode_any W_cbd94 = Some (Jal 1 1580652, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd98 : bv 32 := 0x00050493.
Lemma F_cbd98 : fetch_word Asan.M.loaded_segments (0xcbd98 : word) = Some W_cbd98.
Proof. vm_refl. Qed.
Lemma D_cbd98 : decode_any W_cbd98 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbd9c : bv 32 := 0xe15810ef.
Lemma F_cbd9c : fetch_word Asan.M.loaded_segments (0xcbd9c : word) = Some W_cbd9c.
Proof. vm_refl. Qed.
Lemma D_cbd9c : decode_any W_cbd9c = Some (Jal 1 1580564, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbda0 : bv 32 := 0x03257863.
Lemma F_cbda0 : fetch_word Asan.M.loaded_segments (0xcbda0 : word) = Some W_cbda0.
Proof. vm_refl. Qed.
Lemma D_cbda0 : decode_any W_cbda0 = Some (Branch BC_GEU 10 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbda4 : bv 32 := 0x00150613.
Lemma F_cbda4 : fetch_word Asan.M.loaded_segments (0xcbda4 : word) = Some W_cbda4.
Proof. vm_refl. Qed.
Lemma D_cbda4 : decode_any W_cbda4 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbda8 : bv 32 := 0x00040513.
Lemma F_cbda8 : fetch_word Asan.M.loaded_segments (0xcbda8 : word) = Some W_cbda8.
Proof. vm_refl. Qed.
Lemma D_cbda8 : decode_any W_cbda8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdac : bv 32 := 0x00048593.
Lemma F_cbdac : fetch_word Asan.M.loaded_segments (0xcbdac : word) = Some W_cbdac.
Proof. vm_refl. Qed.
Lemma D_cbdac : decode_any W_cbdac = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdb0 : bv 32 := 0xb20920ef.
Lemma F_cbdb0 : fetch_word Asan.M.loaded_segments (0xcbdb0 : word) = Some W_cbdb0.
Proof. vm_refl. Qed.
Lemma D_cbdb0 : decode_any W_cbdb0 = Some (Jal 1 1647392, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdb4 : bv 32 := 0x00000513.
Lemma F_cbdb4 : fetch_word Asan.M.loaded_segments (0xcbdb4 : word) = Some W_cbdb4.
Proof. vm_refl. Qed.
Lemma D_cbdb4 : decode_any W_cbdb4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdb8 : bv 32 := 0x01813083.
Lemma F_cbdb8 : fetch_word Asan.M.loaded_segments (0xcbdb8 : word) = Some W_cbdb8.
Proof. vm_refl. Qed.
Lemma D_cbdb8 : decode_any W_cbdb8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdbc : bv 32 := 0x01013403.
Lemma F_cbdbc : fetch_word Asan.M.loaded_segments (0xcbdbc : word) = Some W_cbdbc.
Proof. vm_refl. Qed.
Lemma D_cbdbc : decode_any W_cbdbc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdc0 : bv 32 := 0x00813483.
Lemma F_cbdc0 : fetch_word Asan.M.loaded_segments (0xcbdc0 : word) = Some W_cbdc0.
Proof. vm_refl. Qed.
Lemma D_cbdc0 : decode_any W_cbdc0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdc4 : bv 32 := 0x00013903.
Lemma F_cbdc4 : fetch_word Asan.M.loaded_segments (0xcbdc4 : word) = Some W_cbdc4.
Proof. vm_refl. Qed.
Lemma D_cbdc4 : decode_any W_cbdc4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdc8 : bv 32 := 0x02010113.
Lemma F_cbdc8 : fetch_word Asan.M.loaded_segments (0xcbdc8 : word) = Some W_cbdc8.
Proof. vm_refl. Qed.
Lemma D_cbdc8 : decode_any W_cbdc8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdcc : bv 32 := 0x00008067.
Lemma F_cbdcc : fetch_word Asan.M.loaded_segments (0xcbdcc : word) = Some W_cbdcc.
Proof. vm_refl. Qed.
Lemma D_cbdcc : decode_any W_cbdcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdd0 : bv 32 := 0x02200513.
Lemma F_cbdd0 : fetch_word Asan.M.loaded_segments (0xcbdd0 : word) = Some W_cbdd0.
Proof. vm_refl. Qed.
Lemma D_cbdd0 : decode_any W_cbdd0 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdd4 : bv 32 := 0xfe0902e3.
Lemma F_cbdd4 : fetch_word Asan.M.loaded_segments (0xcbdd4 : word) = Some W_cbdd4.
Proof. vm_refl. Qed.
Lemma D_cbdd4 : decode_any W_cbdd4 = Some (Branch BC_EQ 18 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdd8 : bv 32 := 0xfff90913.
Lemma F_cbdd8 : fetch_word Asan.M.loaded_segments (0xcbdd8 : word) = Some W_cbdd8.
Proof. vm_refl. Qed.
Lemma D_cbdd8 : decode_any W_cbdd8 = Some (OpImm ALU_ADD 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbddc : bv 32 := 0x00040513.
Lemma F_cbddc : fetch_word Asan.M.loaded_segments (0xcbddc : word) = Some W_cbddc.
Proof. vm_refl. Qed.
Lemma D_cbddc : decode_any W_cbddc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbde0 : bv 32 := 0x00048593.
Lemma F_cbde0 : fetch_word Asan.M.loaded_segments (0xcbde0 : word) = Some W_cbde0.
Proof. vm_refl. Qed.
Lemma D_cbde0 : decode_any W_cbde0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbde4 : bv 32 := 0x00090613.
Lemma F_cbde4 : fetch_word Asan.M.loaded_segments (0xcbde4 : word) = Some W_cbde4.
Proof. vm_refl. Qed.
Lemma D_cbde4 : decode_any W_cbde4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbde8 : bv 32 := 0xae8920ef.
Lemma F_cbde8 : fetch_word Asan.M.loaded_segments (0xcbde8 : word) = Some W_cbde8.
Proof. vm_refl. Qed.
Lemma D_cbde8 : decode_any W_cbde8 = Some (Jal 1 1647336, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdec : bv 32 := 0x02200513.
Lemma F_cbdec : fetch_word Asan.M.loaded_segments (0xcbdec : word) = Some W_cbdec.
Proof. vm_refl. Qed.
Lemma D_cbdec : decode_any W_cbdec = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdf0 : bv 32 := 0x01240433.
Lemma F_cbdf0 : fetch_word Asan.M.loaded_segments (0xcbdf0 : word) = Some W_cbdf0.
Proof. vm_refl. Qed.
Lemma D_cbdf0 : decode_any W_cbdf0 = Some (Op ALU_ADD 8 8 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdf4 : bv 32 := 0x00040023.
Lemma F_cbdf4 : fetch_word Asan.M.loaded_segments (0xcbdf4 : word) = Some W_cbdf4.
Proof. vm_refl. Qed.
Lemma D_cbdf4 : decode_any W_cbdf4 = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdf8 : bv 32 := 0x01813083.
Lemma F_cbdf8 : fetch_word Asan.M.loaded_segments (0xcbdf8 : word) = Some W_cbdf8.
Proof. vm_refl. Qed.
Lemma D_cbdf8 : decode_any W_cbdf8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdfc : bv 32 := 0x01013403.
Lemma F_cbdfc : fetch_word Asan.M.loaded_segments (0xcbdfc : word) = Some W_cbdfc.
Proof. vm_refl. Qed.
Lemma D_cbdfc : decode_any W_cbdfc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe00 : bv 32 := 0x00813483.
Lemma F_cbe00 : fetch_word Asan.M.loaded_segments (0xcbe00 : word) = Some W_cbe00.
Proof. vm_refl. Qed.
Lemma D_cbe00 : decode_any W_cbe00 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe04 : bv 32 := 0x00013903.
Lemma F_cbe04 : fetch_word Asan.M.loaded_segments (0xcbe04 : word) = Some W_cbe04.
Proof. vm_refl. Qed.
Lemma D_cbe04 : decode_any W_cbe04 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe08 : bv 32 := 0x02010113.
Lemma F_cbe08 : fetch_word Asan.M.loaded_segments (0xcbe08 : word) = Some W_cbe08.
Proof. vm_refl. Qed.
Lemma D_cbe08 : decode_any W_cbe08 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe0c : bv 32 := 0x00008067.
Lemma F_cbe0c : fetch_word Asan.M.loaded_segments (0xcbe0c : word) = Some W_cbe0c.
Proof. vm_refl. Qed.
Lemma D_cbe0c : decode_any W_cbe0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe10 : bv 32 := 0x00757593.
Lemma F_cbe10 : fetch_word Asan.M.loaded_segments (0xcbe10 : word) = Some W_cbe10.
Proof. vm_refl. Qed.
Lemma D_cbe10 : decode_any W_cbe10 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe14 : bv 32 := 0x00050613.
Lemma F_cbe14 : fetch_word Asan.M.loaded_segments (0xcbe14 : word) = Some W_cbe14.
Proof. vm_refl. Qed.
Lemma D_cbe14 : decode_any W_cbe14 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe18 : bv 32 := 0x02058a63.
Lemma F_cbe18 : fetch_word Asan.M.loaded_segments (0xcbe18 : word) = Some W_cbe18.
Proof. vm_refl. Qed.
Lemma D_cbe18 : decode_any W_cbe18 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe1c : bv 32 := 0x00054583.
Lemma F_cbe1c : fetch_word Asan.M.loaded_segments (0xcbe1c : word) = Some W_cbe1c.
Proof. vm_refl. Qed.
Lemma D_cbe1c : decode_any W_cbe1c = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe20 : bv 32 := 0x06058c63.
Lemma F_cbe20 : fetch_word Asan.M.loaded_segments (0xcbe20 : word) = Some W_cbe20.
Proof. vm_refl. Qed.
Lemma D_cbe20 : decode_any W_cbe20 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe24 : bv 32 := 0x00150613.
Lemma F_cbe24 : fetch_word Asan.M.loaded_segments (0xcbe24 : word) = Some W_cbe24.
Proof. vm_refl. Qed.
Lemma D_cbe24 : decode_any W_cbe24 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe28 : bv 32 := 0x00050593.
Lemma F_cbe28 : fetch_word Asan.M.loaded_segments (0xcbe28 : word) = Some W_cbe28.
Proof. vm_refl. Qed.
Lemma D_cbe28 : decode_any W_cbe28 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe2c : bv 32 := 0x00158693.
Lemma F_cbe2c : fetch_word Asan.M.loaded_segments (0xcbe2c : word) = Some W_cbe2c.
Proof. vm_refl. Qed.
Lemma D_cbe2c : decode_any W_cbe2c = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe30 : bv 32 := 0x0076f693.
Lemma F_cbe30 : fetch_word Asan.M.loaded_segments (0xcbe30 : word) = Some W_cbe30.
Proof. vm_refl. Qed.
Lemma D_cbe30 : decode_any W_cbe30 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe34 : bv 32 := 0x00068c63.
Lemma F_cbe34 : fetch_word Asan.M.loaded_segments (0xcbe34 : word) = Some W_cbe34.
Proof. vm_refl. Qed.
Lemma D_cbe34 : decode_any W_cbe34 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe38 : bv 32 := 0x00064683.
Lemma F_cbe38 : fetch_word Asan.M.loaded_segments (0xcbe38 : word) = Some W_cbe38.
Proof. vm_refl. Qed.
Lemma D_cbe38 : decode_any W_cbe38 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe3c : bv 32 := 0x00160613.
Lemma F_cbe3c : fetch_word Asan.M.loaded_segments (0xcbe3c : word) = Some W_cbe3c.
Proof. vm_refl. Qed.
Lemma D_cbe3c : decode_any W_cbe3c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe40 : bv 32 := 0x00158593.
Lemma F_cbe40 : fetch_word Asan.M.loaded_segments (0xcbe40 : word) = Some W_cbe40.
Proof. vm_refl. Qed.
Lemma D_cbe40 : decode_any W_cbe40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe44 : bv 32 := 0xfe0694e3.
Lemma F_cbe44 : fetch_word Asan.M.loaded_segments (0xcbe44 : word) = Some W_cbe44.
Proof. vm_refl. Qed.
Lemma D_cbe44 : decode_any W_cbe44 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe48 : bv 32 := 0x0480006f.
Lemma F_cbe48 : fetch_word Asan.M.loaded_segments (0xcbe48 : word) = Some W_cbe48.
Proof. vm_refl. Qed.
Lemma D_cbe48 : decode_any W_cbe48 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe4c : bv 32 := 0xfff44597.
Lemma F_cbe4c : fetch_word Asan.M.loaded_segments (0xcbe4c : word) = Some W_cbe4c.
Proof. vm_refl. Qed.
Lemma D_cbe4c : decode_any W_cbe4c = Some (Auipc 11 1048388, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe50 : bv 32 := 0xfff44717.
Lemma F_cbe50 : fetch_word Asan.M.loaded_segments (0xcbe50 : word) = Some W_cbe50.
Proof. vm_refl. Qed.
Lemma D_cbe50 : decode_any W_cbe50 = Some (Auipc 14 1048388, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe54 : bv 32 := 0x53c5b683.
Lemma F_cbe54 : fetch_word Asan.M.loaded_segments (0xcbe54 : word) = Some W_cbe54.
Proof. vm_refl. Qed.
Lemma D_cbe54 : decode_any W_cbe54 = Some (Load SZ8 true 13 11 1340, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe58 : bv 32 := 0x52073703.
Lemma F_cbe58 : fetch_word Asan.M.loaded_segments (0xcbe58 : word) = Some W_cbe58.
Proof. vm_refl. Qed.
Lemma D_cbe58 : decode_any W_cbe58 = Some (Load SZ8 true 14 14 1312, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe5c : bv 32 := 0xff760593.
Lemma F_cbe5c : fetch_word Asan.M.loaded_segments (0xcbe5c : word) = Some W_cbe5c.
Proof. vm_refl. Qed.
Lemma D_cbe5c : decode_any W_cbe5c = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe60 : bv 32 := 0xff860613.
Lemma F_cbe60 : fetch_word Asan.M.loaded_segments (0xcbe60 : word) = Some W_cbe60.
Proof. vm_refl. Qed.
Lemma D_cbe60 : decode_any W_cbe60 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe64 : bv 32 := 0x00863783.
Lemma F_cbe64 : fetch_word Asan.M.loaded_segments (0xcbe64 : word) = Some W_cbe64.
Proof. vm_refl. Qed.
Lemma D_cbe64 : decode_any W_cbe64 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe68 : bv 32 := 0x00860613.
Lemma F_cbe68 : fetch_word Asan.M.loaded_segments (0xcbe68 : word) = Some W_cbe68.
Proof. vm_refl. Qed.
Lemma D_cbe68 : decode_any W_cbe68 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe6c : bv 32 := 0x40f68833.
Lemma F_cbe6c : fetch_word Asan.M.loaded_segments (0xcbe6c : word) = Some W_cbe6c.
Proof. vm_refl. Qed.
Lemma D_cbe6c : decode_any W_cbe6c = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe70 : bv 32 := 0x00f867b3.
Lemma F_cbe70 : fetch_word Asan.M.loaded_segments (0xcbe70 : word) = Some W_cbe70.
Proof. vm_refl. Qed.
Lemma D_cbe70 : decode_any W_cbe70 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe74 : bv 32 := 0x00e7f7b3.
Lemma F_cbe74 : fetch_word Asan.M.loaded_segments (0xcbe74 : word) = Some W_cbe74.
Proof. vm_refl. Qed.
Lemma D_cbe74 : decode_any W_cbe74 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe78 : bv 32 := 0x00858593.
Lemma F_cbe78 : fetch_word Asan.M.loaded_segments (0xcbe78 : word) = Some W_cbe78.
Proof. vm_refl. Qed.
Lemma D_cbe78 : decode_any W_cbe78 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe7c : bv 32 := 0xfee784e3.
Lemma F_cbe7c : fetch_word Asan.M.loaded_segments (0xcbe7c : word) = Some W_cbe7c.
Proof. vm_refl. Qed.
Lemma D_cbe7c : decode_any W_cbe7c = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe80 : bv 32 := 0x00064683.
Lemma F_cbe80 : fetch_word Asan.M.loaded_segments (0xcbe80 : word) = Some W_cbe80.
Proof. vm_refl. Qed.
Lemma D_cbe80 : decode_any W_cbe80 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe84 : bv 32 := 0x00160613.
Lemma F_cbe84 : fetch_word Asan.M.loaded_segments (0xcbe84 : word) = Some W_cbe84.
Proof. vm_refl. Qed.
Lemma D_cbe84 : decode_any W_cbe84 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe88 : bv 32 := 0x00158593.
Lemma F_cbe88 : fetch_word Asan.M.loaded_segments (0xcbe88 : word) = Some W_cbe88.
Proof. vm_refl. Qed.
Lemma D_cbe88 : decode_any W_cbe88 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe8c : bv 32 := 0xfe069ae3.
Lemma F_cbe8c : fetch_word Asan.M.loaded_segments (0xcbe8c : word) = Some W_cbe8c.
Proof. vm_refl. Qed.
Lemma D_cbe8c : decode_any W_cbe8c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe90 : bv 32 := 0x40a58533.
Lemma F_cbe90 : fetch_word Asan.M.loaded_segments (0xcbe90 : word) = Some W_cbe90.
Proof. vm_refl. Qed.
Lemma D_cbe90 : decode_any W_cbe90 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe94 : bv 32 := 0x00008067.
Lemma F_cbe94 : fetch_word Asan.M.loaded_segments (0xcbe94 : word) = Some W_cbe94.
Proof. vm_refl. Qed.
Lemma D_cbe94 : decode_any W_cbe94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe98 : bv 32 := 0x40a50533.
Lemma F_cbe98 : fetch_word Asan.M.loaded_segments (0xcbe98 : word) = Some W_cbe98.
Proof. vm_refl. Qed.
Lemma D_cbe98 : decode_any W_cbe98 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbe9c : bv 32 := 0x00008067.
Lemma F_cbe9c : fetch_word Asan.M.loaded_segments (0xcbe9c : word) = Some W_cbe9c.
Proof. vm_refl. Qed.
Lemma D_cbe9c : decode_any W_cbe9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbea0 : bv 32 := 0xfe010113.
Lemma F_cbea0 : fetch_word Asan.M.loaded_segments (0xcbea0 : word) = Some W_cbea0.
Proof. vm_refl. Qed.
Lemma D_cbea0 : decode_any W_cbea0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbea4 : bv 32 := 0x00113c23.
Lemma F_cbea4 : fetch_word Asan.M.loaded_segments (0xcbea4 : word) = Some W_cbea4.
Proof. vm_refl. Qed.
Lemma D_cbea4 : decode_any W_cbea4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbea8 : bv 32 := 0x00813823.
Lemma F_cbea8 : fetch_word Asan.M.loaded_segments (0xcbea8 : word) = Some W_cbea8.
Proof. vm_refl. Qed.
Lemma D_cbea8 : decode_any W_cbea8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbeac : bv 32 := 0x00913423.
Lemma F_cbeac : fetch_word Asan.M.loaded_segments (0xcbeac : word) = Some W_cbeac.
Proof. vm_refl. Qed.
Lemma D_cbeac : decode_any W_cbeac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbeb0 : bv 32 := 0x01213023.
Lemma F_cbeb0 : fetch_word Asan.M.loaded_segments (0xcbeb0 : word) = Some W_cbeb0.
Proof. vm_refl. Qed.
Lemma D_cbeb0 : decode_any W_cbeb0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbeb4 : bv 32 := 0x00060413.
Lemma F_cbeb4 : fetch_word Asan.M.loaded_segments (0xcbeb4 : word) = Some W_cbeb4.
Proof. vm_refl. Qed.
Lemma D_cbeb4 : decode_any W_cbeb4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbeb8 : bv 32 := 0x00058493.
Lemma F_cbeb8 : fetch_word Asan.M.loaded_segments (0xcbeb8 : word) = Some W_cbeb8.
Proof. vm_refl. Qed.
Lemma D_cbeb8 : decode_any W_cbeb8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbebc : bv 32 := 0x00050913.
Lemma F_cbebc : fetch_word Asan.M.loaded_segments (0xcbebc : word) = Some W_cbebc.
Proof. vm_refl. Qed.
Lemma D_cbebc : decode_any W_cbebc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbec0 : bv 32 := 0xcf1810ef.
Lemma F_cbec0 : fetch_word Asan.M.loaded_segments (0xcbec0 : word) = Some W_cbec0.
Proof. vm_refl. Qed.
Lemma D_cbec0 : decode_any W_cbec0 = Some (Jal 1 1580272, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbec4 : bv 32 := 0x00a905b3.
Lemma F_cbec4 : fetch_word Asan.M.loaded_segments (0xcbec4 : word) = Some W_cbec4.
Proof. vm_refl. Qed.
Lemma D_cbec4 : decode_any W_cbec4 = Some (Op ALU_ADD 11 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbec8 : bv 32 := 0x02040463.
Lemma F_cbec8 : fetch_word Asan.M.loaded_segments (0xcbec8 : word) = Some W_cbec8.
Proof. vm_refl. Qed.
Lemma D_cbec8 : decode_any W_cbec8 = Some (Branch BC_EQ 8 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbecc : bv 32 := 0x0004c683.
Lemma F_cbecc : fetch_word Asan.M.loaded_segments (0xcbecc : word) = Some W_cbecc.
Proof. vm_refl. Qed.
Lemma D_cbecc : decode_any W_cbecc = Some (Load SZ1 false 13 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbed0 : bv 32 := 0x02068063.
Lemma F_cbed0 : fetch_word Asan.M.loaded_segments (0xcbed0 : word) = Some W_cbed0.
Proof. vm_refl. Qed.
Lemma D_cbed0 : decode_any W_cbed0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbed4 : bv 32 := 0xfff40413.
Lemma F_cbed4 : fetch_word Asan.M.loaded_segments (0xcbed4 : word) = Some W_cbed4.
Proof. vm_refl. Qed.
Lemma D_cbed4 : decode_any W_cbed4 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbed8 : bv 32 := 0x00148493.
Lemma F_cbed8 : fetch_word Asan.M.loaded_segments (0xcbed8 : word) = Some W_cbed8.
Proof. vm_refl. Qed.
Lemma D_cbed8 : decode_any W_cbed8 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbedc : bv 32 := 0x00158613.
Lemma F_cbedc : fetch_word Asan.M.loaded_segments (0xcbedc : word) = Some W_cbedc.
Proof. vm_refl. Qed.
Lemma D_cbedc : decode_any W_cbedc = Some (OpImm ALU_ADD 12 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbee0 : bv 32 := 0x00d58023.
Lemma F_cbee0 : fetch_word Asan.M.loaded_segments (0xcbee0 : word) = Some W_cbee0.
Proof. vm_refl. Qed.
Lemma D_cbee0 : decode_any W_cbee0 = Some (Store SZ1 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbee4 : bv 32 := 0x00060593.
Lemma F_cbee4 : fetch_word Asan.M.loaded_segments (0xcbee4 : word) = Some W_cbee4.
Proof. vm_refl. Qed.
Lemma D_cbee4 : decode_any W_cbee4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbee8 : bv 32 := 0xfe0412e3.
Lemma F_cbee8 : fetch_word Asan.M.loaded_segments (0xcbee8 : word) = Some W_cbee8.
Proof. vm_refl. Qed.
Lemma D_cbee8 : decode_any W_cbee8 = Some (Branch BC_NE 8 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbeec : bv 32 := 0x0080006f.
Lemma F_cbeec : fetch_word Asan.M.loaded_segments (0xcbeec : word) = Some W_cbeec.
Proof. vm_refl. Qed.
Lemma D_cbeec : decode_any W_cbeec = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbef0 : bv 32 := 0x00058613.
Lemma F_cbef0 : fetch_word Asan.M.loaded_segments (0xcbef0 : word) = Some W_cbef0.
Proof. vm_refl. Qed.
Lemma D_cbef0 : decode_any W_cbef0 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbef4 : bv 32 := 0x00060023.
Lemma F_cbef4 : fetch_word Asan.M.loaded_segments (0xcbef4 : word) = Some W_cbef4.
Proof. vm_refl. Qed.
Lemma D_cbef4 : decode_any W_cbef4 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbef8 : bv 32 := 0x00090513.
Lemma F_cbef8 : fetch_word Asan.M.loaded_segments (0xcbef8 : word) = Some W_cbef8.
Proof. vm_refl. Qed.
Lemma D_cbef8 : decode_any W_cbef8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbefc : bv 32 := 0x01813083.
Lemma F_cbefc : fetch_word Asan.M.loaded_segments (0xcbefc : word) = Some W_cbefc.
Proof. vm_refl. Qed.
Lemma D_cbefc : decode_any W_cbefc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf00 : bv 32 := 0x01013403.
Lemma F_cbf00 : fetch_word Asan.M.loaded_segments (0xcbf00 : word) = Some W_cbf00.
Proof. vm_refl. Qed.
Lemma D_cbf00 : decode_any W_cbf00 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf04 : bv 32 := 0x00813483.
Lemma F_cbf04 : fetch_word Asan.M.loaded_segments (0xcbf04 : word) = Some W_cbf04.
Proof. vm_refl. Qed.
Lemma D_cbf04 : decode_any W_cbf04 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf08 : bv 32 := 0x00013903.
Lemma F_cbf08 : fetch_word Asan.M.loaded_segments (0xcbf08 : word) = Some W_cbf08.
Proof. vm_refl. Qed.
Lemma D_cbf08 : decode_any W_cbf08 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf0c : bv 32 := 0x02010113.
Lemma F_cbf0c : fetch_word Asan.M.loaded_segments (0xcbf0c : word) = Some W_cbf0c.
Proof. vm_refl. Qed.
Lemma D_cbf0c : decode_any W_cbf0c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf10 : bv 32 := 0x00008067.
Lemma F_cbf10 : fetch_word Asan.M.loaded_segments (0xcbf10 : word) = Some W_cbf10.
Proof. vm_refl. Qed.
Lemma D_cbf10 : decode_any W_cbf10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf14 : bv 32 := 0xff010113.
Lemma F_cbf14 : fetch_word Asan.M.loaded_segments (0xcbf14 : word) = Some W_cbf14.
Proof. vm_refl. Qed.
Lemma D_cbf14 : decode_any W_cbf14 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf18 : bv 32 := 0x00113423.
Lemma F_cbf18 : fetch_word Asan.M.loaded_segments (0xcbf18 : word) = Some W_cbf18.
Proof. vm_refl. Qed.
Lemma D_cbf18 : decode_any W_cbf18 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf1c : bv 32 := 0x00813023.
Lemma F_cbf1c : fetch_word Asan.M.loaded_segments (0xcbf1c : word) = Some W_cbf1c.
Proof. vm_refl. Qed.
Lemma D_cbf1c : decode_any W_cbf1c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf20 : bv 32 := 0x00050413.
Lemma F_cbf20 : fetch_word Asan.M.loaded_segments (0xcbf20 : word) = Some W_cbf20.
Proof. vm_refl. Qed.
Lemma D_cbf20 : decode_any W_cbf20 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf24 : bv 32 := 0x018000ef.
Lemma F_cbf24 : fetch_word Asan.M.loaded_segments (0xcbf24 : word) = Some W_cbf24.
Proof. vm_refl. Qed.
Lemma D_cbf24 : decode_any W_cbf24 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf28 : bv 32 := 0x00040513.
Lemma F_cbf28 : fetch_word Asan.M.loaded_segments (0xcbf28 : word) = Some W_cbf28.
Proof. vm_refl. Qed.
Lemma D_cbf28 : decode_any W_cbf28 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf2c : bv 32 := 0x00813083.
Lemma F_cbf2c : fetch_word Asan.M.loaded_segments (0xcbf2c : word) = Some W_cbf2c.
Proof. vm_refl. Qed.
Lemma D_cbf2c : decode_any W_cbf2c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf30 : bv 32 := 0x00013403.
Lemma F_cbf30 : fetch_word Asan.M.loaded_segments (0xcbf30 : word) = Some W_cbf30.
Proof. vm_refl. Qed.
Lemma D_cbf30 : decode_any W_cbf30 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf34 : bv 32 := 0x01010113.
Lemma F_cbf34 : fetch_word Asan.M.loaded_segments (0xcbf34 : word) = Some W_cbf34.
Proof. vm_refl. Qed.
Lemma D_cbf34 : decode_any W_cbf34 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf38 : bv 32 := 0x00008067.
Lemma F_cbf38 : fetch_word Asan.M.loaded_segments (0xcbf38 : word) = Some W_cbf38.
Proof. vm_refl. Qed.
Lemma D_cbf38 : decode_any W_cbf38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf3c : bv 32 := 0xff010113.
Lemma F_cbf3c : fetch_word Asan.M.loaded_segments (0xcbf3c : word) = Some W_cbf3c.
Proof. vm_refl. Qed.
Lemma D_cbf3c : decode_any W_cbf3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf40 : bv 32 := 0x00113423.
Lemma F_cbf40 : fetch_word Asan.M.loaded_segments (0xcbf40 : word) = Some W_cbf40.
Proof. vm_refl. Qed.
Lemma D_cbf40 : decode_any W_cbf40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf44 : bv 32 := 0x00813023.
Lemma F_cbf44 : fetch_word Asan.M.loaded_segments (0xcbf44 : word) = Some W_cbf44.
Proof. vm_refl. Qed.
Lemma D_cbf44 : decode_any W_cbf44 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf48 : bv 32 := 0x00050413.
Lemma F_cbf48 : fetch_word Asan.M.loaded_segments (0xcbf48 : word) = Some W_cbf48.
Proof. vm_refl. Qed.
Lemma D_cbf48 : decode_any W_cbf48 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf4c : bv 32 := 0x00a5c6b3.
Lemma F_cbf4c : fetch_word Asan.M.loaded_segments (0xcbf4c : word) = Some W_cbf4c.
Proof. vm_refl. Qed.
Lemma D_cbf4c : decode_any W_cbf4c = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf50 : bv 32 := 0x0076f693.
Lemma F_cbf50 : fetch_word Asan.M.loaded_segments (0xcbf50 : word) = Some W_cbf50.
Proof. vm_refl. Qed.
Lemma D_cbf50 : decode_any W_cbf50 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf54 : bv 32 := 0x02068663.
Lemma F_cbf54 : fetch_word Asan.M.loaded_segments (0xcbf54 : word) = Some W_cbf54.
Proof. vm_refl. Qed.
Lemma D_cbf54 : decode_any W_cbf54 = Some (Branch BC_EQ 13 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf58 : bv 32 := 0x0c060263.
Lemma F_cbf58 : fetch_word Asan.M.loaded_segments (0xcbf58 : word) = Some W_cbf58.
Proof. vm_refl. Qed.
Lemma D_cbf58 : decode_any W_cbf58 = Some (Branch BC_EQ 12 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf5c : bv 32 := 0x00060693.
Lemma F_cbf5c : fetch_word Asan.M.loaded_segments (0xcbf5c : word) = Some W_cbf5c.
Proof. vm_refl. Qed.
Lemma D_cbf5c : decode_any W_cbf5c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf60 : bv 32 := 0x0005c603.
Lemma F_cbf60 : fetch_word Asan.M.loaded_segments (0xcbf60 : word) = Some W_cbf60.
Proof. vm_refl. Qed.
Lemma D_cbf60 : decode_any W_cbf60 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf64 : bv 32 := 0x00c40023.
Lemma F_cbf64 : fetch_word Asan.M.loaded_segments (0xcbf64 : word) = Some W_cbf64.
Proof. vm_refl. Qed.
Lemma D_cbf64 : decode_any W_cbf64 = Some (Store SZ1 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf68 : bv 32 := 0x0a060c63.
Lemma F_cbf68 : fetch_word Asan.M.loaded_segments (0xcbf68 : word) = Some W_cbf68.
Proof. vm_refl. Qed.
Lemma D_cbf68 : decode_any W_cbf68 = Some (Branch BC_EQ 12 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf6c : bv 32 := 0xfff68693.
Lemma F_cbf6c : fetch_word Asan.M.loaded_segments (0xcbf6c : word) = Some W_cbf6c.
Proof. vm_refl. Qed.
Lemma D_cbf6c : decode_any W_cbf6c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf70 : bv 32 := 0x00158593.
Lemma F_cbf70 : fetch_word Asan.M.loaded_segments (0xcbf70 : word) = Some W_cbf70.
Proof. vm_refl. Qed.
Lemma D_cbf70 : decode_any W_cbf70 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf74 : bv 32 := 0x00140413.
Lemma F_cbf74 : fetch_word Asan.M.loaded_segments (0xcbf74 : word) = Some W_cbf74.
Proof. vm_refl. Qed.
Lemma D_cbf74 : decode_any W_cbf74 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf78 : bv 32 := 0xfe0694e3.
Lemma F_cbf78 : fetch_word Asan.M.loaded_segments (0xcbf78 : word) = Some W_cbf78.
Proof. vm_refl. Qed.
Lemma D_cbf78 : decode_any W_cbf78 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf7c : bv 32 := 0x0a40006f.
Lemma F_cbf7c : fetch_word Asan.M.loaded_segments (0xcbf7c : word) = Some W_cbf7c.
Proof. vm_refl. Qed.
Lemma D_cbf7c : decode_any W_cbf7c = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf80 : bv 32 := 0x0075f693.
Lemma F_cbf80 : fetch_word Asan.M.loaded_segments (0xcbf80 : word) = Some W_cbf80.
Proof. vm_refl. Qed.
Lemma D_cbf80 : decode_any W_cbf80 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf84 : bv 32 := 0x00c03733.
Lemma F_cbf84 : fetch_word Asan.M.loaded_segments (0xcbf84 : word) = Some W_cbf84.
Proof. vm_refl. Qed.
Lemma D_cbf84 : decode_any W_cbf84 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf88 : bv 32 := 0x04068063.
Lemma F_cbf88 : fetch_word Asan.M.loaded_segments (0xcbf88 : word) = Some W_cbf88.
Proof. vm_refl. Qed.
Lemma D_cbf88 : decode_any W_cbf88 = Some (Branch BC_EQ 13 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf8c : bv 32 := 0x02060e63.
Lemma F_cbf8c : fetch_word Asan.M.loaded_segments (0xcbf8c : word) = Some W_cbf8c.
Proof. vm_refl. Qed.
Lemma D_cbf8c : decode_any W_cbf8c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf90 : bv 32 := 0x00158793.
Lemma F_cbf90 : fetch_word Asan.M.loaded_segments (0xcbf90 : word) = Some W_cbf90.
Proof. vm_refl. Qed.
Lemma D_cbf90 : decode_any W_cbf90 = Some (OpImm ALU_ADD 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf94 : bv 32 := 0x00100813.
Lemma F_cbf94 : fetch_word Asan.M.loaded_segments (0xcbf94 : word) = Some W_cbf94.
Proof. vm_refl. Qed.
Lemma D_cbf94 : decode_any W_cbf94 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf98 : bv 32 := 0x0005c703.
Lemma F_cbf98 : fetch_word Asan.M.loaded_segments (0xcbf98 : word) = Some W_cbf98.
Proof. vm_refl. Qed.
Lemma D_cbf98 : decode_any W_cbf98 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbf9c : bv 32 := 0x00060693.
Lemma F_cbf9c : fetch_word Asan.M.loaded_segments (0xcbf9c : word) = Some W_cbf9c.
Proof. vm_refl. Qed.
Lemma D_cbf9c : decode_any W_cbf9c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfa0 : bv 32 := 0x00e40023.
Lemma F_cbfa0 : fetch_word Asan.M.loaded_segments (0xcbfa0 : word) = Some W_cbfa0.
Proof. vm_refl. Qed.
Lemma D_cbfa0 : decode_any W_cbfa0 = Some (Store SZ1 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfa4 : bv 32 := 0x06070e63.
Lemma F_cbfa4 : fetch_word Asan.M.loaded_segments (0xcbfa4 : word) = Some W_cbfa4.
Proof. vm_refl. Qed.
Lemma D_cbfa4 : decode_any W_cbfa4 = Some (Branch BC_EQ 14 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfa8 : bv 32 := 0xfff68613.
Lemma F_cbfa8 : fetch_word Asan.M.loaded_segments (0xcbfa8 : word) = Some W_cbfa8.
Proof. vm_refl. Qed.
Lemma D_cbfa8 : decode_any W_cbfa8 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfac : bv 32 := 0x00158593.
Lemma F_cbfac : fetch_word Asan.M.loaded_segments (0xcbfac : word) = Some W_cbfac.
Proof. vm_refl. Qed.
Lemma D_cbfac : decode_any W_cbfac = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfb0 : bv 32 := 0x00140413.
Lemma F_cbfb0 : fetch_word Asan.M.loaded_segments (0xcbfb0 : word) = Some W_cbfb0.
Proof. vm_refl. Qed.
Lemma D_cbfb0 : decode_any W_cbfb0 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfb4 : bv 32 := 0x0077f893.
Lemma F_cbfb4 : fetch_word Asan.M.loaded_segments (0xcbfb4 : word) = Some W_cbfb4.
Proof. vm_refl. Qed.
Lemma D_cbfb4 : decode_any W_cbfb4 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfb8 : bv 32 := 0x00c03733.
Lemma F_cbfb8 : fetch_word Asan.M.loaded_segments (0xcbfb8 : word) = Some W_cbfb8.
Proof. vm_refl. Qed.
Lemma D_cbfb8 : decode_any W_cbfb8 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfbc : bv 32 := 0x00088663.
Lemma F_cbfbc : fetch_word Asan.M.loaded_segments (0xcbfbc : word) = Some W_cbfbc.
Proof. vm_refl. Qed.
Lemma D_cbfbc : decode_any W_cbfbc = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfc0 : bv 32 := 0x00178793.
Lemma F_cbfc0 : fetch_word Asan.M.loaded_segments (0xcbfc0 : word) = Some W_cbfc0.
Proof. vm_refl. Qed.
Lemma D_cbfc0 : decode_any W_cbfc0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfc4 : bv 32 := 0xfd069ae3.
Lemma F_cbfc4 : fetch_word Asan.M.loaded_segments (0xcbfc4 : word) = Some W_cbfc4.
Proof. vm_refl. Qed.
Lemma D_cbfc4 : decode_any W_cbfc4 = Some (Branch BC_NE 13 16 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfc8 : bv 32 := 0x04070a63.
Lemma F_cbfc8 : fetch_word Asan.M.loaded_segments (0xcbfc8 : word) = Some W_cbfc8.
Proof. vm_refl. Qed.
Lemma D_cbfc8 : decode_any W_cbfc8 = Some (Branch BC_EQ 14 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfcc : bv 32 := 0x0005c683.
Lemma F_cbfcc : fetch_word Asan.M.loaded_segments (0xcbfcc : word) = Some W_cbfcc.
Proof. vm_refl. Qed.
Lemma D_cbfcc : decode_any W_cbfcc = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfd0 : bv 32 := 0x06068a63.
Lemma F_cbfd0 : fetch_word Asan.M.loaded_segments (0xcbfd0 : word) = Some W_cbfd0.
Proof. vm_refl. Qed.
Lemma D_cbfd0 : decode_any W_cbfd0 = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfd4 : bv 32 := 0x00800693.
Lemma F_cbfd4 : fetch_word Asan.M.loaded_segments (0xcbfd4 : word) = Some W_cbfd4.
Proof. vm_refl. Qed.
Lemma D_cbfd4 : decode_any W_cbfd4 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfd8 : bv 32 := 0xf8d660e3.
Lemma F_cbfd8 : fetch_word Asan.M.loaded_segments (0xcbfd8 : word) = Some W_cbfd8.
Proof. vm_refl. Qed.
Lemma D_cbfd8 : decode_any W_cbfd8 = Some (Branch BC_LTU 12 13 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfdc : bv 32 := 0xfff44697.
Lemma F_cbfdc : fetch_word Asan.M.loaded_segments (0xcbfdc : word) = Some W_cbfdc.
Proof. vm_refl. Qed.
Lemma D_cbfdc : decode_any W_cbfdc = Some (Auipc 13 1048388, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfe0 : bv 32 := 0xfff44717.
Lemma F_cbfe0 : fetch_word Asan.M.loaded_segments (0xcbfe0 : word) = Some W_cbfe0.
Proof. vm_refl. Qed.
Lemma D_cbfe0 : decode_any W_cbfe0 = Some (Auipc 14 1048388, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfe4 : bv 32 := 0x3ac6b683.
Lemma F_cbfe4 : fetch_word Asan.M.loaded_segments (0xcbfe4 : word) = Some W_cbfe4.
Proof. vm_refl. Qed.
Lemma D_cbfe4 : decode_any W_cbfe4 = Some (Load SZ8 true 13 13 940, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfe8 : bv 32 := 0x39073703.
Lemma F_cbfe8 : fetch_word Asan.M.loaded_segments (0xcbfe8 : word) = Some W_cbfe8.
Proof. vm_refl. Qed.
Lemma D_cbfe8 : decode_any W_cbfe8 = Some (Load SZ8 true 14 14 912, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbfec : bv 32 := 0x00700793.
Lemma F_cbfec : fetch_word Asan.M.loaded_segments (0xcbfec : word) = Some W_cbfec.
Proof. vm_refl. Qed.
Lemma D_cbfec : decode_any W_cbfec = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbff0 : bv 32 := 0x0005b803.
Lemma F_cbff0 : fetch_word Asan.M.loaded_segments (0xcbff0 : word) = Some W_cbff0.
Proof. vm_refl. Qed.
Lemma D_cbff0 : decode_any W_cbff0 = Some (Load SZ8 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbff4 : bv 32 := 0x410688b3.
Lemma F_cbff4 : fetch_word Asan.M.loaded_segments (0xcbff4 : word) = Some W_cbff4.
Proof. vm_refl. Qed.
Lemma D_cbff4 : decode_any W_cbff4 = Some (Op ALU_SUB 17 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbff8 : bv 32 := 0x0108e8b3.
Lemma F_cbff8 : fetch_word Asan.M.loaded_segments (0xcbff8 : word) = Some W_cbff8.
Proof. vm_refl. Qed.
Lemma D_cbff8 : decode_any W_cbff8 = Some (Op ALU_OR 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbffc : bv 32 := 0x00e8f8b3.
Lemma F_cbffc : fetch_word Asan.M.loaded_segments (0xcbffc : word) = Some W_cbffc.
Proof. vm_refl. Qed.
Lemma D_cbffc : decode_any W_cbffc = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc000 : bv 32 := 0xf4e89ee3.
Lemma F_cc000 : fetch_word Asan.M.loaded_segments (0xcc000 : word) = Some W_cc000.
Proof. vm_refl. Qed.
Lemma D_cc000 : decode_any W_cc000 = Some (Branch BC_NE 17 14 8028, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc004 : bv 32 := 0x01043023.
Lemma F_cc004 : fetch_word Asan.M.loaded_segments (0xcc004 : word) = Some W_cc004.
Proof. vm_refl. Qed.
Lemma D_cc004 : decode_any W_cc004 = Some (Store SZ8 8 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc008 : bv 32 := 0xff860613.
Lemma F_cc008 : fetch_word Asan.M.loaded_segments (0xcc008 : word) = Some W_cc008.
Proof. vm_refl. Qed.
Lemma D_cc008 : decode_any W_cc008 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc00c : bv 32 := 0x00858593.
Lemma F_cc00c : fetch_word Asan.M.loaded_segments (0xcc00c : word) = Some W_cc00c.
Proof. vm_refl. Qed.
Lemma D_cc00c : decode_any W_cc00c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc010 : bv 32 := 0x00840413.
Lemma F_cc010 : fetch_word Asan.M.loaded_segments (0xcc010 : word) = Some W_cc010.
Proof. vm_refl. Qed.
Lemma D_cc010 : decode_any W_cc010 = Some (OpImm ALU_ADD 8 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc014 : bv 32 := 0xfcc7eee3.
Lemma F_cc014 : fetch_word Asan.M.loaded_segments (0xcc014 : word) = Some W_cc014.
Proof. vm_refl. Qed.
Lemma D_cc014 : decode_any W_cc014 = Some (Branch BC_LTU 15 12 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc018 : bv 32 := 0xf41ff06f.
Lemma F_cc018 : fetch_word Asan.M.loaded_segments (0xcc018 : word) = Some W_cc018.
Proof. vm_refl. Qed.
Lemma D_cc018 : decode_any W_cc018 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc01c : bv 32 := 0x00000693.
Lemma F_cc01c : fetch_word Asan.M.loaded_segments (0xcc01c : word) = Some W_cc01c.
Proof. vm_refl. Qed.
Lemma D_cc01c : decode_any W_cc01c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc020 : bv 32 := 0x00040513.
Lemma F_cc020 : fetch_word Asan.M.loaded_segments (0xcc020 : word) = Some W_cc020.
Proof. vm_refl. Qed.
Lemma D_cc020 : decode_any W_cc020 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc024 : bv 32 := 0x00000593.
Lemma F_cc024 : fetch_word Asan.M.loaded_segments (0xcc024 : word) = Some W_cc024.
Proof. vm_refl. Qed.
Lemma D_cc024 : decode_any W_cc024 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc028 : bv 32 := 0x00068613.
Lemma F_cc028 : fetch_word Asan.M.loaded_segments (0xcc028 : word) = Some W_cc028.
Proof. vm_refl. Qed.
Lemma D_cc028 : decode_any W_cc028 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc02c : bv 32 := 0x89c920ef.
Lemma F_cc02c : fetch_word Asan.M.loaded_segments (0xcc02c : word) = Some W_cc02c.
Proof. vm_refl. Qed.
Lemma D_cc02c : decode_any W_cc02c = Some (Jal 1 1646748, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc030 : bv 32 := 0x00040513.
Lemma F_cc030 : fetch_word Asan.M.loaded_segments (0xcc030 : word) = Some W_cc030.
Proof. vm_refl. Qed.
Lemma D_cc030 : decode_any W_cc030 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc034 : bv 32 := 0x00813083.
Lemma F_cc034 : fetch_word Asan.M.loaded_segments (0xcc034 : word) = Some W_cc034.
Proof. vm_refl. Qed.
Lemma D_cc034 : decode_any W_cc034 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc038 : bv 32 := 0x00013403.
Lemma F_cc038 : fetch_word Asan.M.loaded_segments (0xcc038 : word) = Some W_cc038.
Proof. vm_refl. Qed.
Lemma D_cc038 : decode_any W_cc038 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc03c : bv 32 := 0x01010113.
Lemma F_cc03c : fetch_word Asan.M.loaded_segments (0xcc03c : word) = Some W_cc03c.
Proof. vm_refl. Qed.
Lemma D_cc03c : decode_any W_cc03c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc040 : bv 32 := 0x00008067.
Lemma F_cc040 : fetch_word Asan.M.loaded_segments (0xcc040 : word) = Some W_cc040.
Proof. vm_refl. Qed.
Lemma D_cc040 : decode_any W_cc040 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc044 : bv 32 := 0x00060693.
Lemma F_cc044 : fetch_word Asan.M.loaded_segments (0xcc044 : word) = Some W_cc044.
Proof. vm_refl. Qed.
Lemma D_cc044 : decode_any W_cc044 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc048 : bv 32 := 0xfd9ff06f.
Lemma F_cc048 : fetch_word Asan.M.loaded_segments (0xcc048 : word) = Some W_cc048.
Proof. vm_refl. Qed.
Lemma D_cc048 : decode_any W_cc048 = Some (Jal 0 2097112, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc04c : bv 32 := 0xfe010113.
Lemma F_cc04c : fetch_word Asan.M.loaded_segments (0xcc04c : word) = Some W_cc04c.
Proof. vm_refl. Qed.
Lemma D_cc04c : decode_any W_cc04c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.
