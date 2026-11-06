(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_db774 : bv 32 := 0x0e060a63.
Lemma F_db774 : fetch_word Asan.M.loaded_segments (0xdb750 : word) = Some W_db774.
Proof. vm_refl. Qed.
Lemma D_db774 : decode_any W_db774 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_db778 : bv 32 := 0x00b50023.
Lemma F_db778 : fetch_word Asan.M.loaded_segments (0xdb754 : word) = Some W_db778.
Proof. vm_refl. Qed.
Lemma D_db778 : decode_any W_db778 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db77c : bv 32 := 0x00c506b3.
Lemma F_db77c : fetch_word Asan.M.loaded_segments (0xdb758 : word) = Some W_db77c.
Proof. vm_refl. Qed.
Lemma D_db77c : decode_any W_db77c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db780 : bv 32 := 0x00300713.
Lemma F_db780 : fetch_word Asan.M.loaded_segments (0xdb75c : word) = Some W_db780.
Proof. vm_refl. Qed.
Lemma D_db780 : decode_any W_db780 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db784 : bv 32 := 0xfeb68fa3.
Lemma F_db784 : fetch_word Asan.M.loaded_segments (0xdb760 : word) = Some W_db784.
Proof. vm_refl. Qed.
Lemma D_db784 : decode_any W_db784 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_db788 : bv 32 := 0x0ee66063.
Lemma F_db788 : fetch_word Asan.M.loaded_segments (0xdb764 : word) = Some W_db788.
Proof. vm_refl. Qed.
Lemma D_db788 : decode_any W_db788 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_db78c : bv 32 := 0x00b500a3.
Lemma F_db78c : fetch_word Asan.M.loaded_segments (0xdb768 : word) = Some W_db78c.
Proof. vm_refl. Qed.
Lemma D_db78c : decode_any W_db78c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db790 : bv 32 := 0x00b50123.
Lemma F_db790 : fetch_word Asan.M.loaded_segments (0xdb76c : word) = Some W_db790.
Proof. vm_refl. Qed.
Lemma D_db790 : decode_any W_db790 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db794 : bv 32 := 0x00700713.
Lemma F_db794 : fetch_word Asan.M.loaded_segments (0xdb770 : word) = Some W_db794.
Proof. vm_refl. Qed.
Lemma D_db794 : decode_any W_db794 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_db798 : bv 32 := 0xfeb68ea3.
Lemma F_db798 : fetch_word Asan.M.loaded_segments (0xdb774 : word) = Some W_db798.
Proof. vm_refl. Qed.
Lemma D_db798 : decode_any W_db798 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_db79c : bv 32 := 0xfeb68f23.
Lemma F_db79c : fetch_word Asan.M.loaded_segments (0xdb778 : word) = Some W_db79c.
Proof. vm_refl. Qed.
Lemma D_db79c : decode_any W_db79c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7a0 : bv 32 := 0x0ce66463.
Lemma F_db7a0 : fetch_word Asan.M.loaded_segments (0xdb77c : word) = Some W_db7a0.
Proof. vm_refl. Qed.
Lemma D_db7a0 : decode_any W_db7a0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7a4 : bv 32 := 0x00b501a3.
Lemma F_db7a4 : fetch_word Asan.M.loaded_segments (0xdb780 : word) = Some W_db7a4.
Proof. vm_refl. Qed.
Lemma D_db7a4 : decode_any W_db7a4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7a8 : bv 32 := 0x00900793.
Lemma F_db7a8 : fetch_word Asan.M.loaded_segments (0xdb784 : word) = Some W_db7a8.
Proof. vm_refl. Qed.
Lemma D_db7a8 : decode_any W_db7a8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7ac : bv 32 := 0xfeb68e23.
Lemma F_db7ac : fetch_word Asan.M.loaded_segments (0xdb788 : word) = Some W_db7ac.
Proof. vm_refl. Qed.
Lemma D_db7ac : decode_any W_db7ac = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7b0 : bv 32 := 0x0af66c63.
Lemma F_db7b0 : fetch_word Asan.M.loaded_segments (0xdb78c : word) = Some W_db7b0.
Proof. vm_refl. Qed.
Lemma D_db7b0 : decode_any W_db7b0 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7b4 : bv 32 := 0x40a006bb.
Lemma F_db7b4 : fetch_word Asan.M.loaded_segments (0xdb790 : word) = Some W_db7b4.
Proof. vm_refl. Qed.
Lemma D_db7b4 : decode_any W_db7b4 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7b8 : bv 32 := 0x03859813.
Lemma F_db7b8 : fetch_word Asan.M.loaded_segments (0xdb794 : word) = Some W_db7b8.
Proof. vm_refl. Qed.
Lemma D_db7b8 : decode_any W_db7b8 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7bc : bv 32 := 0x101015b7.
Lemma F_db7bc : fetch_word Asan.M.loaded_segments (0xdb798 : word) = Some W_db7bc.
Proof. vm_refl. Qed.
Lemma D_db7bc : decode_any W_db7bc = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7c0 : bv 32 := 0x0036f693.
Lemma F_db7c0 : fetch_word Asan.M.loaded_segments (0xdb79c : word) = Some W_db7c0.
Proof. vm_refl. Qed.
Lemma D_db7c0 : decode_any W_db7c0 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7c4 : bv 32 := 0x00459713.
Lemma F_db7c4 : fetch_word Asan.M.loaded_segments (0xdb7a0 : word) = Some W_db7c4.
Proof. vm_refl. Qed.
Lemma D_db7c4 : decode_any W_db7c4 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7c8 : bv 32 := 0x40d60633.
Lemma F_db7c8 : fetch_word Asan.M.loaded_segments (0xdb7a4 : word) = Some W_db7c8.
Proof. vm_refl. Qed.
Lemma D_db7c8 : decode_any W_db7c8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7cc : bv 32 := 0x00d505b3.
Lemma F_db7cc : fetch_word Asan.M.loaded_segments (0xdb7a8 : word) = Some W_db7cc.
Proof. vm_refl. Qed.
Lemma D_db7cc : decode_any W_db7cc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7d0 : bv 32 := 0x10070693.
Lemma F_db7d0 : fetch_word Asan.M.loaded_segments (0xdb7ac : word) = Some W_db7d0.
Proof. vm_refl. Qed.
Lemma D_db7d0 : decode_any W_db7d0 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7d4 : bv 32 := 0xffc67713.
Lemma F_db7d4 : fetch_word Asan.M.loaded_segments (0xdb7b0 : word) = Some W_db7d4.
Proof. vm_refl. Qed.
Lemma D_db7d4 : decode_any W_db7d4 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7d8 : bv 32 := 0x02d83633.
Lemma F_db7d8 : fetch_word Asan.M.loaded_segments (0xdb7b4 : word) = Some W_db7d8.
Proof. vm_refl. Qed.
Lemma D_db7d8 : decode_any W_db7d8 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7dc : bv 32 := 0x00c5a023.
Lemma F_db7dc : fetch_word Asan.M.loaded_segments (0xdb7b8 : word) = Some W_db7dc.
Proof. vm_refl. Qed.
Lemma D_db7dc : decode_any W_db7dc = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7e0 : bv 32 := 0x00e586b3.
Lemma F_db7e0 : fetch_word Asan.M.loaded_segments (0xdb7bc : word) = Some W_db7e0.
Proof. vm_refl. Qed.
Lemma D_db7e0 : decode_any W_db7e0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7e4 : bv 32 := 0xfec6ae23.
Lemma F_db7e4 : fetch_word Asan.M.loaded_segments (0xdb7c0 : word) = Some W_db7e4.
Proof. vm_refl. Qed.
Lemma D_db7e4 : decode_any W_db7e4 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7e8 : bv 32 := 0x08f76063.
Lemma F_db7e8 : fetch_word Asan.M.loaded_segments (0xdb7c4 : word) = Some W_db7e8.
Proof. vm_refl. Qed.
Lemma D_db7e8 : decode_any W_db7e8 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7ec : bv 32 := 0x00c5a223.
Lemma F_db7ec : fetch_word Asan.M.loaded_segments (0xdb7c8 : word) = Some W_db7ec.
Proof. vm_refl. Qed.
Lemma D_db7ec : decode_any W_db7ec = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7f0 : bv 32 := 0x00c5a423.
Lemma F_db7f0 : fetch_word Asan.M.loaded_segments (0xdb7cc : word) = Some W_db7f0.
Proof. vm_refl. Qed.
Lemma D_db7f0 : decode_any W_db7f0 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7f4 : bv 32 := 0x01900793.
Lemma F_db7f4 : fetch_word Asan.M.loaded_segments (0xdb7d0 : word) = Some W_db7f4.
Proof. vm_refl. Qed.
Lemma D_db7f4 : decode_any W_db7f4 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7f8 : bv 32 := 0xfec6aa23.
Lemma F_db7f8 : fetch_word Asan.M.loaded_segments (0xdb7d4 : word) = Some W_db7f8.
Proof. vm_refl. Qed.
Lemma D_db7f8 : decode_any W_db7f8 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_db7fc : bv 32 := 0xfec6ac23.
Lemma F_db7fc : fetch_word Asan.M.loaded_segments (0xdb7d8 : word) = Some W_db7fc.
Proof. vm_refl. Qed.
Lemma D_db7fc : decode_any W_db7fc = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_db800 : bv 32 := 0x06f76463.
Lemma F_db800 : fetch_word Asan.M.loaded_segments (0xdb7dc : word) = Some W_db800.
Proof. vm_refl. Qed.
Lemma D_db800 : decode_any W_db800 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_db804 : bv 32 := 0x00c5a623.
Lemma F_db804 : fetch_word Asan.M.loaded_segments (0xdb7e0 : word) = Some W_db804.
Proof. vm_refl. Qed.
Lemma D_db804 : decode_any W_db804 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db808 : bv 32 := 0x00c5a823.
Lemma F_db808 : fetch_word Asan.M.loaded_segments (0xdb7e4 : word) = Some W_db808.
Proof. vm_refl. Qed.
Lemma D_db808 : decode_any W_db808 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db80c : bv 32 := 0x00c5aa23.
Lemma F_db80c : fetch_word Asan.M.loaded_segments (0xdb7e8 : word) = Some W_db80c.
Proof. vm_refl. Qed.
Lemma D_db80c : decode_any W_db80c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_db810 : bv 32 := 0x00c5ac23.
Lemma F_db810 : fetch_word Asan.M.loaded_segments (0xdb7ec : word) = Some W_db810.
Proof. vm_refl. Qed.
Lemma D_db810 : decode_any W_db810 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db814 : bv 32 := 0x0045f793.
Lemma F_db814 : fetch_word Asan.M.loaded_segments (0xdb7f0 : word) = Some W_db814.
Proof. vm_refl. Qed.
Lemma D_db814 : decode_any W_db814 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db818 : bv 32 := 0x02000813.
Lemma F_db818 : fetch_word Asan.M.loaded_segments (0xdb7f4 : word) = Some W_db818.
Proof. vm_refl. Qed.
Lemma D_db818 : decode_any W_db818 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_db81c : bv 32 := 0x01878793.
Lemma F_db81c : fetch_word Asan.M.loaded_segments (0xdb7f8 : word) = Some W_db81c.
Proof. vm_refl. Qed.
Lemma D_db81c : decode_any W_db81c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db820 : bv 32 := 0x40f70733.
Lemma F_db820 : fetch_word Asan.M.loaded_segments (0xdb7fc : word) = Some W_db820.
Proof. vm_refl. Qed.
Lemma D_db820 : decode_any W_db820 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_db824 : bv 32 := 0xfec6a223.
Lemma F_db824 : fetch_word Asan.M.loaded_segments (0xdb800 : word) = Some W_db824.
Proof. vm_refl. Qed.
Lemma D_db824 : decode_any W_db824 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_db828 : bv 32 := 0xfec6a423.
Lemma F_db828 : fetch_word Asan.M.loaded_segments (0xdb804 : word) = Some W_db828.
Proof. vm_refl. Qed.
Lemma D_db828 : decode_any W_db828 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_db82c : bv 32 := 0xfec6a623.
Lemma F_db82c : fetch_word Asan.M.loaded_segments (0xdb808 : word) = Some W_db82c.
Proof. vm_refl. Qed.
Lemma D_db82c : decode_any W_db82c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_db830 : bv 32 := 0xfec6a823.
Lemma F_db830 : fetch_word Asan.M.loaded_segments (0xdb80c : word) = Some W_db830.
Proof. vm_refl. Qed.
Lemma D_db830 : decode_any W_db830 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_db834 : bv 32 := 0x03076a63.
Lemma F_db834 : fetch_word Asan.M.loaded_segments (0xdb810 : word) = Some W_db834.
Proof. vm_refl. Qed.
Lemma D_db834 : decode_any W_db834 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_db838 : bv 32 := 0x02061613.
Lemma F_db838 : fetch_word Asan.M.loaded_segments (0xdb814 : word) = Some W_db838.
Proof. vm_refl. Qed.
Lemma D_db838 : decode_any W_db838 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_db83c : bv 32 := 0x00f585b3.
Lemma F_db83c : fetch_word Asan.M.loaded_segments (0xdb818 : word) = Some W_db83c.
Proof. vm_refl. Qed.
Lemma D_db83c : decode_any W_db83c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_db840 : bv 32 := 0x02065693.
Lemma F_db840 : fetch_word Asan.M.loaded_segments (0xdb81c : word) = Some W_db840.
Proof. vm_refl. Qed.
Lemma D_db840 : decode_any W_db840 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_db844 : bv 32 := 0x00d66633.
Lemma F_db844 : fetch_word Asan.M.loaded_segments (0xdb820 : word) = Some W_db844.
Proof. vm_refl. Qed.
Lemma D_db844 : decode_any W_db844 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_db848 : bv 32 := 0x01f00693.
Lemma F_db848 : fetch_word Asan.M.loaded_segments (0xdb824 : word) = Some W_db848.
Proof. vm_refl. Qed.
Lemma D_db848 : decode_any W_db848 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_db84c : bv 32 := 0x00c5b023.
Lemma F_db84c : fetch_word Asan.M.loaded_segments (0xdb828 : word) = Some W_db84c.
Proof. vm_refl. Qed.
Lemma D_db84c : decode_any W_db84c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db850 : bv 32 := 0x00c5b423.
Lemma F_db850 : fetch_word Asan.M.loaded_segments (0xdb82c : word) = Some W_db850.
Proof. vm_refl. Qed.
Lemma D_db850 : decode_any W_db850 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db854 : bv 32 := 0x00c5b823.
Lemma F_db854 : fetch_word Asan.M.loaded_segments (0xdb830 : word) = Some W_db854.
Proof. vm_refl. Qed.
Lemma D_db854 : decode_any W_db854 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db858 : bv 32 := 0x00c5bc23.
Lemma F_db858 : fetch_word Asan.M.loaded_segments (0xdb834 : word) = Some W_db858.
Proof. vm_refl. Qed.
Lemma D_db858 : decode_any W_db858 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db85c : bv 32 := 0xfe070713.
Lemma F_db85c : fetch_word Asan.M.loaded_segments (0xdb838 : word) = Some W_db85c.
Proof. vm_refl. Qed.
Lemma D_db85c : decode_any W_db85c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_db860 : bv 32 := 0x02058593.
Lemma F_db860 : fetch_word Asan.M.loaded_segments (0xdb83c : word) = Some W_db860.
Proof. vm_refl. Qed.
Lemma D_db860 : decode_any W_db860 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_db864 : bv 32 := 0xfee6e4e3.
Lemma F_db864 : fetch_word Asan.M.loaded_segments (0xdb840 : word) = Some W_db864.
Proof. vm_refl. Qed.
Lemma D_db864 : decode_any W_db864 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_db868 : bv 32 := 0x00008067.
Lemma F_db868 : fetch_word Asan.M.loaded_segments (0xdb844 : word) = Some W_db868.
Proof. vm_refl. Qed.
Lemma D_db868 : decode_any W_db868 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xdb750%Z.
Definition Fo_000 := F_db774.
Definition Do_000 := D_db774.
Definition Fo_004 := F_db778.
Definition Do_004 := D_db778.
Definition Fo_008 := F_db77c.
Definition Do_008 := D_db77c.
Definition Fo_00c := F_db780.
Definition Do_00c := D_db780.
Definition Fo_010 := F_db784.
Definition Do_010 := D_db784.
Definition Fo_014 := F_db788.
Definition Do_014 := D_db788.
Definition Fo_018 := F_db78c.
Definition Do_018 := D_db78c.
Definition Fo_01c := F_db790.
Definition Do_01c := D_db790.
Definition Fo_020 := F_db794.
Definition Do_020 := D_db794.
Definition Fo_024 := F_db798.
Definition Do_024 := D_db798.
Definition Fo_028 := F_db79c.
Definition Do_028 := D_db79c.
Definition Fo_02c := F_db7a0.
Definition Do_02c := D_db7a0.
Definition Fo_030 := F_db7a4.
Definition Do_030 := D_db7a4.
Definition Fo_034 := F_db7a8.
Definition Do_034 := D_db7a8.
Definition Fo_038 := F_db7ac.
Definition Do_038 := D_db7ac.
Definition Fo_03c := F_db7b0.
Definition Do_03c := D_db7b0.
Definition Fo_040 := F_db7b4.
Definition Do_040 := D_db7b4.
Definition Fo_044 := F_db7b8.
Definition Do_044 := D_db7b8.
Definition Fo_048 := F_db7bc.
Definition Do_048 := D_db7bc.
Definition Fo_04c := F_db7c0.
Definition Do_04c := D_db7c0.
Definition Fo_050 := F_db7c4.
Definition Do_050 := D_db7c4.
Definition Fo_054 := F_db7c8.
Definition Do_054 := D_db7c8.
Definition Fo_058 := F_db7cc.
Definition Do_058 := D_db7cc.
Definition Fo_05c := F_db7d0.
Definition Do_05c := D_db7d0.
Definition Fo_060 := F_db7d4.
Definition Do_060 := D_db7d4.
Definition Fo_064 := F_db7d8.
Definition Do_064 := D_db7d8.
Definition Fo_068 := F_db7dc.
Definition Do_068 := D_db7dc.
Definition Fo_06c := F_db7e0.
Definition Do_06c := D_db7e0.
Definition Fo_070 := F_db7e4.
Definition Do_070 := D_db7e4.
Definition Fo_074 := F_db7e8.
Definition Do_074 := D_db7e8.
Definition Fo_078 := F_db7ec.
Definition Do_078 := D_db7ec.
Definition Fo_07c := F_db7f0.
Definition Do_07c := D_db7f0.
Definition Fo_080 := F_db7f4.
Definition Do_080 := D_db7f4.
Definition Fo_084 := F_db7f8.
Definition Do_084 := D_db7f8.
Definition Fo_088 := F_db7fc.
Definition Do_088 := D_db7fc.
Definition Fo_08c := F_db800.
Definition Do_08c := D_db800.
Definition Fo_090 := F_db804.
Definition Do_090 := D_db804.
Definition Fo_094 := F_db808.
Definition Do_094 := D_db808.
Definition Fo_098 := F_db80c.
Definition Do_098 := D_db80c.
Definition Fo_09c := F_db810.
Definition Do_09c := D_db810.
Definition Fo_0a0 := F_db814.
Definition Do_0a0 := D_db814.
Definition Fo_0a4 := F_db818.
Definition Do_0a4 := D_db818.
Definition Fo_0a8 := F_db81c.
Definition Do_0a8 := D_db81c.
Definition Fo_0ac := F_db820.
Definition Do_0ac := D_db820.
Definition Fo_0b0 := F_db824.
Definition Do_0b0 := D_db824.
Definition Fo_0b4 := F_db828.
Definition Do_0b4 := D_db828.
Definition Fo_0b8 := F_db82c.
Definition Do_0b8 := D_db82c.
Definition Fo_0bc := F_db830.
Definition Do_0bc := D_db830.
Definition Fo_0c0 := F_db834.
Definition Do_0c0 := D_db834.
Definition Fo_0c4 := F_db838.
Definition Do_0c4 := D_db838.
Definition Fo_0c8 := F_db83c.
Definition Do_0c8 := D_db83c.
Definition Fo_0cc := F_db840.
Definition Do_0cc := D_db840.
Definition Fo_0d0 := F_db844.
Definition Do_0d0 := D_db844.
Definition Fo_0d4 := F_db848.
Definition Do_0d4 := D_db848.
Definition Fo_0d8 := F_db84c.
Definition Do_0d8 := D_db84c.
Definition Fo_0dc := F_db850.
Definition Do_0dc := D_db850.
Definition Fo_0e0 := F_db854.
Definition Do_0e0 := D_db854.
Definition Fo_0e4 := F_db858.
Definition Do_0e4 := D_db858.
Definition Fo_0e8 := F_db85c.
Definition Do_0e8 := D_db85c.
Definition Fo_0ec := F_db860.
Definition Do_0ec := D_db860.
Definition Fo_0f0 := F_db864.
Definition Do_0f0 := D_db864.
Definition Fo_0f4 := F_db868.
Definition Do_0f4 := D_db868.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_db370 : bv 32 := 0x0035f693.
Lemma F_db370 : fetch_word Asan.M.loaded_segments (0xdb34c : word) = Some W_db370.
Proof. vm_refl. Qed.
Lemma D_db370 : decode_any W_db370 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db374 : bv 32 := 0x10068863.
Lemma F_db374 : fetch_word Asan.M.loaded_segments (0xdb350 : word) = Some W_db374.
Proof. vm_refl. Qed.
Lemma D_db374 : decode_any W_db374 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_db378 : bv 32 := 0x02060e63.
Lemma F_db378 : fetch_word Asan.M.loaded_segments (0xdb354 : word) = Some W_db378.
Proof. vm_refl. Qed.
Lemma D_db378 : decode_any W_db378 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_db37c : bv 32 := 0x00158713.
Lemma F_db37c : fetch_word Asan.M.loaded_segments (0xdb358 : word) = Some W_db37c.
Proof. vm_refl. Qed.
Lemma D_db37c : decode_any W_db37c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db380 : bv 32 := 0x00100793.
Lemma F_db380 : fetch_word Asan.M.loaded_segments (0xdb35c : word) = Some W_db380.
Proof. vm_refl. Qed.
Lemma D_db380 : decode_any W_db380 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db384 : bv 32 := 0x00050693.
Lemma F_db384 : fetch_word Asan.M.loaded_segments (0xdb360 : word) = Some W_db384.
Proof. vm_refl. Qed.
Lemma D_db384 : decode_any W_db384 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db388 : bv 32 := 0x0005c883.
Lemma F_db388 : fetch_word Asan.M.loaded_segments (0xdb364 : word) = Some W_db388.
Proof. vm_refl. Qed.
Lemma D_db388 : decode_any W_db388 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db38c : bv 32 := 0x00060813.
Lemma F_db38c : fetch_word Asan.M.loaded_segments (0xdb368 : word) = Some W_db38c.
Proof. vm_refl. Qed.
Lemma D_db38c : decode_any W_db38c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db390 : bv 32 := 0x00158593.
Lemma F_db390 : fetch_word Asan.M.loaded_segments (0xdb36c : word) = Some W_db390.
Proof. vm_refl. Qed.
Lemma D_db390 : decode_any W_db390 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db394 : bv 32 := 0x00377293.
Lemma F_db394 : fetch_word Asan.M.loaded_segments (0xdb370 : word) = Some W_db394.
Proof. vm_refl. Qed.
Lemma D_db394 : decode_any W_db394 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db398 : bv 32 := 0x01168023.
Lemma F_db398 : fetch_word Asan.M.loaded_segments (0xdb374 : word) = Some W_db398.
Proof. vm_refl. Qed.
Lemma D_db398 : decode_any W_db398 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db39c : bv 32 := 0x00168693.
Lemma F_db39c : fetch_word Asan.M.loaded_segments (0xdb378 : word) = Some W_db39c.
Proof. vm_refl. Qed.
Lemma D_db39c : decode_any W_db39c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3a0 : bv 32 := 0xfff60613.
Lemma F_db3a0 : fetch_word Asan.M.loaded_segments (0xdb37c : word) = Some W_db3a0.
Proof. vm_refl. Qed.
Lemma D_db3a0 : decode_any W_db3a0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3a4 : bv 32 := 0x00028a63.
Lemma F_db3a4 : fetch_word Asan.M.loaded_segments (0xdb380 : word) = Some W_db3a4.
Proof. vm_refl. Qed.
Lemma D_db3a4 : decode_any W_db3a4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3a8 : bv 32 := 0x00170713.
Lemma F_db3a8 : fetch_word Asan.M.loaded_segments (0xdb384 : word) = Some W_db3a8.
Proof. vm_refl. Qed.
Lemma D_db3a8 : decode_any W_db3a8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3ac : bv 32 := 0xfcf81ee3.
Lemma F_db3ac : fetch_word Asan.M.loaded_segments (0xdb388 : word) = Some W_db3ac.
Proof. vm_refl. Qed.
Lemma D_db3ac : decode_any W_db3ac = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3b0 : bv 32 := 0x0080006f.
Lemma F_db3b0 : fetch_word Asan.M.loaded_segments (0xdb38c : word) = Some W_db3b0.
Proof. vm_refl. Qed.
Lemma D_db3b0 : decode_any W_db3b0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3b4 : bv 32 := 0x00050693.
Lemma F_db3b4 : fetch_word Asan.M.loaded_segments (0xdb390 : word) = Some W_db3b4.
Proof. vm_refl. Qed.
Lemma D_db3b4 : decode_any W_db3b4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3b8 : bv 32 := 0x0036f793.
Lemma F_db3b8 : fetch_word Asan.M.loaded_segments (0xdb394 : word) = Some W_db3b8.
Proof. vm_refl. Qed.
Lemma D_db3b8 : decode_any W_db3b8 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3bc : bv 32 := 0x0c078a63.
Lemma F_db3bc : fetch_word Asan.M.loaded_segments (0xdb398 : word) = Some W_db3bc.
Proof. vm_refl. Qed.
Lemma D_db3bc : decode_any W_db3bc = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3c0 : bv 32 := 0x02000713.
Lemma F_db3c0 : fetch_word Asan.M.loaded_segments (0xdb39c : word) = Some W_db3c0.
Proof. vm_refl. Qed.
Lemma D_db3c0 : decode_any W_db3c0 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3c4 : bv 32 := 0x02e67063.
Lemma F_db3c4 : fetch_word Asan.M.loaded_segments (0xdb3a0 : word) = Some W_db3c4.
Proof. vm_refl. Qed.
Lemma D_db3c4 : decode_any W_db3c4 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3c8 : bv 32 := 0x01000713.
Lemma F_db3c8 : fetch_word Asan.M.loaded_segments (0xdb3a4 : word) = Some W_db3c8.
Proof. vm_refl. Qed.
Lemma D_db3c8 : decode_any W_db3c8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3cc : bv 32 := 0x24e67863.
Lemma F_db3cc : fetch_word Asan.M.loaded_segments (0xdb3a8 : word) = Some W_db3cc.
Proof. vm_refl. Qed.
Lemma D_db3cc : decode_any W_db3cc = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3d0 : bv 32 := 0x00867713.
Lemma F_db3d0 : fetch_word Asan.M.loaded_segments (0xdb3ac : word) = Some W_db3d0.
Proof. vm_refl. Qed.
Lemma D_db3d0 : decode_any W_db3d0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3d4 : bv 32 := 0x2c071e63.
Lemma F_db3d4 : fetch_word Asan.M.loaded_segments (0xdb3b0 : word) = Some W_db3d4.
Proof. vm_refl. Qed.
Lemma D_db3d4 : decode_any W_db3d4 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3d8 : bv 32 := 0x00467713.
Lemma F_db3d8 : fetch_word Asan.M.loaded_segments (0xdb3b4 : word) = Some W_db3d8.
Proof. vm_refl. Qed.
Lemma D_db3d8 : decode_any W_db3d8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3dc : bv 32 := 0x32071463.
Lemma F_db3dc : fetch_word Asan.M.loaded_segments (0xdb3b8 : word) = Some W_db3dc.
Proof. vm_refl. Qed.
Lemma D_db3dc : decode_any W_db3dc = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3e0 : bv 32 := 0x3500006f.
Lemma F_db3e0 : fetch_word Asan.M.loaded_segments (0xdb3bc : word) = Some W_db3e0.
Proof. vm_refl. Qed.
Lemma D_db3e0 : decode_any W_db3e0 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3e4 : bv 32 := 0x0005a703.
Lemma F_db3e4 : fetch_word Asan.M.loaded_segments (0xdb3c0 : word) = Some W_db3e4.
Proof. vm_refl. Qed.
Lemma D_db3e4 : decode_any W_db3e4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3e8 : bv 32 := 0x00300813.
Lemma F_db3e8 : fetch_word Asan.M.loaded_segments (0xdb3c4 : word) = Some W_db3e8.
Proof. vm_refl. Qed.
Lemma D_db3e8 : decode_any W_db3e8 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3ec : bv 32 := 0x11078e63.
Lemma F_db3ec : fetch_word Asan.M.loaded_segments (0xdb3c8 : word) = Some W_db3ec.
Proof. vm_refl. Qed.
Lemma D_db3ec : decode_any W_db3ec = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3f0 : bv 32 := 0x00200813.
Lemma F_db3f0 : fetch_word Asan.M.loaded_segments (0xdb3cc : word) = Some W_db3f0.
Proof. vm_refl. Qed.
Lemma D_db3f0 : decode_any W_db3f0 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3f4 : bv 32 := 0x19079c63.
Lemma F_db3f4 : fetch_word Asan.M.loaded_segments (0xdb3d0 : word) = Some W_db3f4.
Proof. vm_refl. Qed.
Lemma D_db3f4 : decode_any W_db3f4 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3f8 : bv 32 := 0x00875793.
Lemma F_db3f8 : fetch_word Asan.M.loaded_segments (0xdb3d4 : word) = Some W_db3f8.
Proof. vm_refl. Qed.
Lemma D_db3f8 : decode_any W_db3f8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db3fc : bv 32 := 0xffe60613.
Lemma F_db3fc : fetch_word Asan.M.loaded_segments (0xdb3d8 : word) = Some W_db3fc.
Proof. vm_refl. Qed.
Lemma D_db3fc : decode_any W_db3fc = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_db400 : bv 32 := 0x00e68023.
Lemma F_db400 : fetch_word Asan.M.loaded_segments (0xdb3dc : word) = Some W_db400.
Proof. vm_refl. Qed.
Lemma D_db400 : decode_any W_db400 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db404 : bv 32 := 0x00f680a3.
Lemma F_db404 : fetch_word Asan.M.loaded_segments (0xdb3e0 : word) = Some W_db404.
Proof. vm_refl. Qed.
Lemma D_db404 : decode_any W_db404 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db408 : bv 32 := 0x00268693.
Lemma F_db408 : fetch_word Asan.M.loaded_segments (0xdb3e4 : word) = Some W_db408.
Proof. vm_refl. Qed.
Lemma D_db408 : decode_any W_db408 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db40c : bv 32 := 0x01058593.
Lemma F_db40c : fetch_word Asan.M.loaded_segments (0xdb3e8 : word) = Some W_db40c.
Proof. vm_refl. Qed.
Lemma D_db40c : decode_any W_db40c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db410 : bv 32 := 0x01100793.
Lemma F_db410 : fetch_word Asan.M.loaded_segments (0xdb3ec : word) = Some W_db410.
Proof. vm_refl. Qed.
Lemma D_db410 : decode_any W_db410 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_db414 : bv 32 := 0x0107581b.
Lemma F_db414 : fetch_word Asan.M.loaded_segments (0xdb3f0 : word) = Some W_db414.
Proof. vm_refl. Qed.
Lemma D_db414 : decode_any W_db414 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db418 : bv 32 := 0xff45a883.
Lemma F_db418 : fetch_word Asan.M.loaded_segments (0xdb3f4 : word) = Some W_db418.
Proof. vm_refl. Qed.
Lemma D_db418 : decode_any W_db418 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_db41c : bv 32 := 0xff85a283.
Lemma F_db41c : fetch_word Asan.M.loaded_segments (0xdb3f8 : word) = Some W_db41c.
Proof. vm_refl. Qed.
Lemma D_db41c : decode_any W_db41c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_db420 : bv 32 := 0xffc5a303.
Lemma F_db420 : fetch_word Asan.M.loaded_segments (0xdb3fc : word) = Some W_db420.
Proof. vm_refl. Qed.
Lemma D_db420 : decode_any W_db420 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_db424 : bv 32 := 0x0005a703.
Lemma F_db424 : fetch_word Asan.M.loaded_segments (0xdb400 : word) = Some W_db424.
Proof. vm_refl. Qed.
Lemma D_db424 : decode_any W_db424 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db428 : bv 32 := 0x01089393.
Lemma F_db428 : fetch_word Asan.M.loaded_segments (0xdb404 : word) = Some W_db428.
Proof. vm_refl. Qed.
Lemma D_db428 : decode_any W_db428 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db42c : bv 32 := 0x0108d89b.
Lemma F_db42c : fetch_word Asan.M.loaded_segments (0xdb408 : word) = Some W_db42c.
Proof. vm_refl. Qed.
Lemma D_db42c : decode_any W_db42c = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db430 : bv 32 := 0x0103e833.
Lemma F_db430 : fetch_word Asan.M.loaded_segments (0xdb40c : word) = Some W_db430.
Proof. vm_refl. Qed.
Lemma D_db430 : decode_any W_db430 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db434 : bv 32 := 0x01029393.
Lemma F_db434 : fetch_word Asan.M.loaded_segments (0xdb410 : word) = Some W_db434.
Proof. vm_refl. Qed.
Lemma D_db434 : decode_any W_db434 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db438 : bv 32 := 0x0102d29b.
Lemma F_db438 : fetch_word Asan.M.loaded_segments (0xdb414 : word) = Some W_db438.
Proof. vm_refl. Qed.
Lemma D_db438 : decode_any W_db438 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db43c : bv 32 := 0x0113e8b3.
Lemma F_db43c : fetch_word Asan.M.loaded_segments (0xdb418 : word) = Some W_db43c.
Proof. vm_refl. Qed.
Lemma D_db43c : decode_any W_db43c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_db440 : bv 32 := 0x01031393.
Lemma F_db440 : fetch_word Asan.M.loaded_segments (0xdb41c : word) = Some W_db440.
Proof. vm_refl. Qed.
Lemma D_db440 : decode_any W_db440 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db444 : bv 32 := 0x0103531b.
Lemma F_db444 : fetch_word Asan.M.loaded_segments (0xdb420 : word) = Some W_db444.
Proof. vm_refl. Qed.
Lemma D_db444 : decode_any W_db444 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db448 : bv 32 := 0x0053e2b3.
Lemma F_db448 : fetch_word Asan.M.loaded_segments (0xdb424 : word) = Some W_db448.
Proof. vm_refl. Qed.
Lemma D_db448 : decode_any W_db448 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db44c : bv 32 := 0x01071393.
Lemma F_db44c : fetch_word Asan.M.loaded_segments (0xdb428 : word) = Some W_db44c.
Proof. vm_refl. Qed.
Lemma D_db44c : decode_any W_db44c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db450 : bv 32 := 0x0063e333.
Lemma F_db450 : fetch_word Asan.M.loaded_segments (0xdb42c : word) = Some W_db450.
Proof. vm_refl. Qed.
Lemma D_db450 : decode_any W_db450 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db454 : bv 32 := 0xff060613.
Lemma F_db454 : fetch_word Asan.M.loaded_segments (0xdb430 : word) = Some W_db454.
Proof. vm_refl. Qed.
Lemma D_db454 : decode_any W_db454 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_db458 : bv 32 := 0x0106a023.
Lemma F_db458 : fetch_word Asan.M.loaded_segments (0xdb434 : word) = Some W_db458.
Proof. vm_refl. Qed.
Lemma D_db458 : decode_any W_db458 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db45c : bv 32 := 0x0116a223.
Lemma F_db45c : fetch_word Asan.M.loaded_segments (0xdb438 : word) = Some W_db45c.
Proof. vm_refl. Qed.
Lemma D_db45c : decode_any W_db45c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db460 : bv 32 := 0x0056a423.
Lemma F_db460 : fetch_word Asan.M.loaded_segments (0xdb43c : word) = Some W_db460.
Proof. vm_refl. Qed.
Lemma D_db460 : decode_any W_db460 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db464 : bv 32 := 0x0066a623.
Lemma F_db464 : fetch_word Asan.M.loaded_segments (0xdb440 : word) = Some W_db464.
Proof. vm_refl. Qed.
Lemma D_db464 : decode_any W_db464 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db468 : bv 32 := 0x01068693.
Lemma F_db468 : fetch_word Asan.M.loaded_segments (0xdb444 : word) = Some W_db468.
Proof. vm_refl. Qed.
Lemma D_db468 : decode_any W_db468 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db46c : bv 32 := 0x01058593.
Lemma F_db46c : fetch_word Asan.M.loaded_segments (0xdb448 : word) = Some W_db46c.
Proof. vm_refl. Qed.
Lemma D_db46c : decode_any W_db46c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db470 : bv 32 := 0xfac7e2e3.
Lemma F_db470 : fetch_word Asan.M.loaded_segments (0xdb44c : word) = Some W_db470.
Proof. vm_refl. Qed.
Lemma D_db470 : decode_any W_db470 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_db474 : bv 32 := 0xff258593.
Lemma F_db474 : fetch_word Asan.M.loaded_segments (0xdb450 : word) = Some W_db474.
Proof. vm_refl. Qed.
Lemma D_db474 : decode_any W_db474 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_db478 : bv 32 := 0x01000713.
Lemma F_db478 : fetch_word Asan.M.loaded_segments (0xdb454 : word) = Some W_db478.
Proof. vm_refl. Qed.
Lemma D_db478 : decode_any W_db478 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db47c : bv 32 := 0xf4e66ae3.
Lemma F_db47c : fetch_word Asan.M.loaded_segments (0xdb458 : word) = Some W_db47c.
Proof. vm_refl. Qed.
Lemma D_db47c : decode_any W_db47c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_db480 : bv 32 := 0x19c0006f.
Lemma F_db480 : fetch_word Asan.M.loaded_segments (0xdb45c : word) = Some W_db480.
Proof. vm_refl. Qed.
Lemma D_db480 : decode_any W_db480 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_db484 : bv 32 := 0x00050693.
Lemma F_db484 : fetch_word Asan.M.loaded_segments (0xdb460 : word) = Some W_db484.
Proof. vm_refl. Qed.
Lemma D_db484 : decode_any W_db484 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db488 : bv 32 := 0x00357793.
Lemma F_db488 : fetch_word Asan.M.loaded_segments (0xdb464 : word) = Some W_db488.
Proof. vm_refl. Qed.
Lemma D_db488 : decode_any W_db488 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db48c : bv 32 := 0xf2079ae3.
Lemma F_db48c : fetch_word Asan.M.loaded_segments (0xdb468 : word) = Some W_db48c.
Proof. vm_refl. Qed.
Lemma D_db48c : decode_any W_db48c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_db490 : bv 32 := 0x01000713.
Lemma F_db490 : fetch_word Asan.M.loaded_segments (0xdb46c : word) = Some W_db490.
Proof. vm_refl. Qed.
Lemma D_db490 : decode_any W_db490 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db494 : bv 32 := 0x02e66c63.
Lemma F_db494 : fetch_word Asan.M.loaded_segments (0xdb470 : word) = Some W_db494.
Proof. vm_refl. Qed.
Lemma D_db494 : decode_any W_db494 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_db498 : bv 32 := 0x00f00713.
Lemma F_db498 : fetch_word Asan.M.loaded_segments (0xdb474 : word) = Some W_db498.
Proof. vm_refl. Qed.
Lemma D_db498 : decode_any W_db498 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_db49c : bv 32 := 0x0005a783.
Lemma F_db49c : fetch_word Asan.M.loaded_segments (0xdb478 : word) = Some W_db49c.
Proof. vm_refl. Qed.
Lemma D_db49c : decode_any W_db49c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4a0 : bv 32 := 0x0045a803.
Lemma F_db4a0 : fetch_word Asan.M.loaded_segments (0xdb47c : word) = Some W_db4a0.
Proof. vm_refl. Qed.
Lemma D_db4a0 : decode_any W_db4a0 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4a4 : bv 32 := 0x0085a883.
Lemma F_db4a4 : fetch_word Asan.M.loaded_segments (0xdb480 : word) = Some W_db4a4.
Proof. vm_refl. Qed.
Lemma D_db4a4 : decode_any W_db4a4 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4a8 : bv 32 := 0x00c5a283.
Lemma F_db4a8 : fetch_word Asan.M.loaded_segments (0xdb484 : word) = Some W_db4a8.
Proof. vm_refl. Qed.
Lemma D_db4a8 : decode_any W_db4a8 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4ac : bv 32 := 0x01058593.
Lemma F_db4ac : fetch_word Asan.M.loaded_segments (0xdb488 : word) = Some W_db4ac.
Proof. vm_refl. Qed.
Lemma D_db4ac : decode_any W_db4ac = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4b0 : bv 32 := 0xff060613.
Lemma F_db4b0 : fetch_word Asan.M.loaded_segments (0xdb48c : word) = Some W_db4b0.
Proof. vm_refl. Qed.
Lemma D_db4b0 : decode_any W_db4b0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4b4 : bv 32 := 0x00f6a023.
Lemma F_db4b4 : fetch_word Asan.M.loaded_segments (0xdb490 : word) = Some W_db4b4.
Proof. vm_refl. Qed.
Lemma D_db4b4 : decode_any W_db4b4 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4b8 : bv 32 := 0x0106a223.
Lemma F_db4b8 : fetch_word Asan.M.loaded_segments (0xdb494 : word) = Some W_db4b8.
Proof. vm_refl. Qed.
Lemma D_db4b8 : decode_any W_db4b8 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4bc : bv 32 := 0x0116a423.
Lemma F_db4bc : fetch_word Asan.M.loaded_segments (0xdb498 : word) = Some W_db4bc.
Proof. vm_refl. Qed.
Lemma D_db4bc : decode_any W_db4bc = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4c0 : bv 32 := 0x0056a623.
Lemma F_db4c0 : fetch_word Asan.M.loaded_segments (0xdb49c : word) = Some W_db4c0.
Proof. vm_refl. Qed.
Lemma D_db4c0 : decode_any W_db4c0 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4c4 : bv 32 := 0x01068693.
Lemma F_db4c4 : fetch_word Asan.M.loaded_segments (0xdb4a0 : word) = Some W_db4c4.
Proof. vm_refl. Qed.
Lemma D_db4c4 : decode_any W_db4c4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4c8 : bv 32 := 0xfcc76ae3.
Lemma F_db4c8 : fetch_word Asan.M.loaded_segments (0xdb4a4 : word) = Some W_db4c8.
Proof. vm_refl. Qed.
Lemma D_db4c8 : decode_any W_db4c8 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4cc : bv 32 := 0x00800713.
Lemma F_db4cc : fetch_word Asan.M.loaded_segments (0xdb4a8 : word) = Some W_db4cc.
Proof. vm_refl. Qed.
Lemma D_db4cc : decode_any W_db4cc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4d0 : bv 32 := 0x00e66e63.
Lemma F_db4d0 : fetch_word Asan.M.loaded_segments (0xdb4ac : word) = Some W_db4d0.
Proof. vm_refl. Qed.
Lemma D_db4d0 : decode_any W_db4d0 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4d4 : bv 32 := 0x0005a703.
Lemma F_db4d4 : fetch_word Asan.M.loaded_segments (0xdb4b0 : word) = Some W_db4d4.
Proof. vm_refl. Qed.
Lemma D_db4d4 : decode_any W_db4d4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4d8 : bv 32 := 0x0045a783.
Lemma F_db4d8 : fetch_word Asan.M.loaded_segments (0xdb4b4 : word) = Some W_db4d8.
Proof. vm_refl. Qed.
Lemma D_db4d8 : decode_any W_db4d8 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4dc : bv 32 := 0x00e6a023.
Lemma F_db4dc : fetch_word Asan.M.loaded_segments (0xdb4b8 : word) = Some W_db4dc.
Proof. vm_refl. Qed.
Lemma D_db4dc : decode_any W_db4dc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4e0 : bv 32 := 0x00f6a223.
Lemma F_db4e0 : fetch_word Asan.M.loaded_segments (0xdb4bc : word) = Some W_db4e0.
Proof. vm_refl. Qed.
Lemma D_db4e0 : decode_any W_db4e0 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4e4 : bv 32 := 0x00868693.
Lemma F_db4e4 : fetch_word Asan.M.loaded_segments (0xdb4c0 : word) = Some W_db4e4.
Proof. vm_refl. Qed.
Lemma D_db4e4 : decode_any W_db4e4 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4e8 : bv 32 := 0x00858593.
Lemma F_db4e8 : fetch_word Asan.M.loaded_segments (0xdb4c4 : word) = Some W_db4e8.
Proof. vm_refl. Qed.
Lemma D_db4e8 : decode_any W_db4e8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4ec : bv 32 := 0x00467713.
Lemma F_db4ec : fetch_word Asan.M.loaded_segments (0xdb4c8 : word) = Some W_db4ec.
Proof. vm_refl. Qed.
Lemma D_db4ec : decode_any W_db4ec = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4f0 : bv 32 := 0x24070063.
Lemma F_db4f0 : fetch_word Asan.M.loaded_segments (0xdb4cc : word) = Some W_db4f0.
Proof. vm_refl. Qed.
Lemma D_db4f0 : decode_any W_db4f0 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4f4 : bv 32 := 0x0005a703.
Lemma F_db4f4 : fetch_word Asan.M.loaded_segments (0xdb4d0 : word) = Some W_db4f4.
Proof. vm_refl. Qed.
Lemma D_db4f4 : decode_any W_db4f4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4f8 : bv 32 := 0x00458593.
Lemma F_db4f8 : fetch_word Asan.M.loaded_segments (0xdb4d4 : word) = Some W_db4f8.
Proof. vm_refl. Qed.
Lemma D_db4f8 : decode_any W_db4f8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db4fc : bv 32 := 0x00e6a023.
Lemma F_db4fc : fetch_word Asan.M.loaded_segments (0xdb4d8 : word) = Some W_db4fc.
Proof. vm_refl. Qed.
Lemma D_db4fc : decode_any W_db4fc = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db500 : bv 32 := 0x00468693.
Lemma F_db500 : fetch_word Asan.M.loaded_segments (0xdb4dc : word) = Some W_db500.
Proof. vm_refl. Qed.
Lemma D_db500 : decode_any W_db500 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db504 : bv 32 := 0x22c0006f.
Lemma F_db504 : fetch_word Asan.M.loaded_segments (0xdb4e0 : word) = Some W_db504.
Proof. vm_refl. Qed.
Lemma D_db504 : decode_any W_db504 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_db508 : bv 32 := 0x00e68023.
Lemma F_db508 : fetch_word Asan.M.loaded_segments (0xdb4e4 : word) = Some W_db508.
Proof. vm_refl. Qed.
Lemma D_db508 : decode_any W_db508 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db50c : bv 32 := 0x00168693.
Lemma F_db50c : fetch_word Asan.M.loaded_segments (0xdb4e8 : word) = Some W_db50c.
Proof. vm_refl. Qed.
Lemma D_db50c : decode_any W_db50c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db510 : bv 32 := 0xfff60613.
Lemma F_db510 : fetch_word Asan.M.loaded_segments (0xdb4ec : word) = Some W_db510.
Proof. vm_refl. Qed.
Lemma D_db510 : decode_any W_db510 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_db514 : bv 32 := 0x01058593.
Lemma F_db514 : fetch_word Asan.M.loaded_segments (0xdb4f0 : word) = Some W_db514.
Proof. vm_refl. Qed.
Lemma D_db514 : decode_any W_db514 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db518 : bv 32 := 0x01200793.
Lemma F_db518 : fetch_word Asan.M.loaded_segments (0xdb4f4 : word) = Some W_db518.
Proof. vm_refl. Qed.
Lemma D_db518 : decode_any W_db518 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_db51c : bv 32 := 0x0087581b.
Lemma F_db51c : fetch_word Asan.M.loaded_segments (0xdb4f8 : word) = Some W_db51c.
Proof. vm_refl. Qed.
Lemma D_db51c : decode_any W_db51c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db520 : bv 32 := 0xff45a883.
Lemma F_db520 : fetch_word Asan.M.loaded_segments (0xdb4fc : word) = Some W_db520.
Proof. vm_refl. Qed.
Lemma D_db520 : decode_any W_db520 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_db524 : bv 32 := 0xff85a283.
Lemma F_db524 : fetch_word Asan.M.loaded_segments (0xdb500 : word) = Some W_db524.
Proof. vm_refl. Qed.
Lemma D_db524 : decode_any W_db524 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_db528 : bv 32 := 0xffc5a303.
Lemma F_db528 : fetch_word Asan.M.loaded_segments (0xdb504 : word) = Some W_db528.
Proof. vm_refl. Qed.
Lemma D_db528 : decode_any W_db528 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_db52c : bv 32 := 0x0005a703.
Lemma F_db52c : fetch_word Asan.M.loaded_segments (0xdb508 : word) = Some W_db52c.
Proof. vm_refl. Qed.
Lemma D_db52c : decode_any W_db52c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db530 : bv 32 := 0x01889393.
Lemma F_db530 : fetch_word Asan.M.loaded_segments (0xdb50c : word) = Some W_db530.
Proof. vm_refl. Qed.
Lemma D_db530 : decode_any W_db530 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db534 : bv 32 := 0x0088d89b.
Lemma F_db534 : fetch_word Asan.M.loaded_segments (0xdb510 : word) = Some W_db534.
Proof. vm_refl. Qed.
Lemma D_db534 : decode_any W_db534 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db538 : bv 32 := 0x0103e833.
Lemma F_db538 : fetch_word Asan.M.loaded_segments (0xdb514 : word) = Some W_db538.
Proof. vm_refl. Qed.
Lemma D_db538 : decode_any W_db538 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db53c : bv 32 := 0x01829393.
Lemma F_db53c : fetch_word Asan.M.loaded_segments (0xdb518 : word) = Some W_db53c.
Proof. vm_refl. Qed.
Lemma D_db53c : decode_any W_db53c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db540 : bv 32 := 0x0082d29b.
Lemma F_db540 : fetch_word Asan.M.loaded_segments (0xdb51c : word) = Some W_db540.
Proof. vm_refl. Qed.
Lemma D_db540 : decode_any W_db540 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db544 : bv 32 := 0x0113e8b3.
Lemma F_db544 : fetch_word Asan.M.loaded_segments (0xdb520 : word) = Some W_db544.
Proof. vm_refl. Qed.
Lemma D_db544 : decode_any W_db544 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_db548 : bv 32 := 0x01831393.
Lemma F_db548 : fetch_word Asan.M.loaded_segments (0xdb524 : word) = Some W_db548.
Proof. vm_refl. Qed.
Lemma D_db548 : decode_any W_db548 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db54c : bv 32 := 0x0083531b.
Lemma F_db54c : fetch_word Asan.M.loaded_segments (0xdb528 : word) = Some W_db54c.
Proof. vm_refl. Qed.
Lemma D_db54c : decode_any W_db54c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db550 : bv 32 := 0x0053e2b3.
Lemma F_db550 : fetch_word Asan.M.loaded_segments (0xdb52c : word) = Some W_db550.
Proof. vm_refl. Qed.
Lemma D_db550 : decode_any W_db550 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db554 : bv 32 := 0x01871393.
Lemma F_db554 : fetch_word Asan.M.loaded_segments (0xdb530 : word) = Some W_db554.
Proof. vm_refl. Qed.
Lemma D_db554 : decode_any W_db554 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db558 : bv 32 := 0x0063e333.
Lemma F_db558 : fetch_word Asan.M.loaded_segments (0xdb534 : word) = Some W_db558.
Proof. vm_refl. Qed.
Lemma D_db558 : decode_any W_db558 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db55c : bv 32 := 0xff060613.
Lemma F_db55c : fetch_word Asan.M.loaded_segments (0xdb538 : word) = Some W_db55c.
Proof. vm_refl. Qed.
Lemma D_db55c : decode_any W_db55c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_db560 : bv 32 := 0x0106a023.
Lemma F_db560 : fetch_word Asan.M.loaded_segments (0xdb53c : word) = Some W_db560.
Proof. vm_refl. Qed.
Lemma D_db560 : decode_any W_db560 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db564 : bv 32 := 0x0116a223.
Lemma F_db564 : fetch_word Asan.M.loaded_segments (0xdb540 : word) = Some W_db564.
Proof. vm_refl. Qed.
Lemma D_db564 : decode_any W_db564 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db568 : bv 32 := 0x0056a423.
Lemma F_db568 : fetch_word Asan.M.loaded_segments (0xdb544 : word) = Some W_db568.
Proof. vm_refl. Qed.
Lemma D_db568 : decode_any W_db568 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db56c : bv 32 := 0x0066a623.
Lemma F_db56c : fetch_word Asan.M.loaded_segments (0xdb548 : word) = Some W_db56c.
Proof. vm_refl. Qed.
Lemma D_db56c : decode_any W_db56c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db570 : bv 32 := 0x01068693.
Lemma F_db570 : fetch_word Asan.M.loaded_segments (0xdb54c : word) = Some W_db570.
Proof. vm_refl. Qed.
Lemma D_db570 : decode_any W_db570 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db574 : bv 32 := 0x01058593.
Lemma F_db574 : fetch_word Asan.M.loaded_segments (0xdb550 : word) = Some W_db574.
Proof. vm_refl. Qed.
Lemma D_db574 : decode_any W_db574 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db578 : bv 32 := 0xfac7e2e3.
Lemma F_db578 : fetch_word Asan.M.loaded_segments (0xdb554 : word) = Some W_db578.
Proof. vm_refl. Qed.
Lemma D_db578 : decode_any W_db578 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_db57c : bv 32 := 0xff158593.
Lemma F_db57c : fetch_word Asan.M.loaded_segments (0xdb558 : word) = Some W_db57c.
Proof. vm_refl. Qed.
Lemma D_db57c : decode_any W_db57c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_db580 : bv 32 := 0x01000713.
Lemma F_db580 : fetch_word Asan.M.loaded_segments (0xdb55c : word) = Some W_db580.
Proof. vm_refl. Qed.
Lemma D_db580 : decode_any W_db580 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db584 : bv 32 := 0xe4e666e3.
Lemma F_db584 : fetch_word Asan.M.loaded_segments (0xdb560 : word) = Some W_db584.
Proof. vm_refl. Qed.
Lemma D_db584 : decode_any W_db584 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_db588 : bv 32 := 0x0940006f.
Lemma F_db588 : fetch_word Asan.M.loaded_segments (0xdb564 : word) = Some W_db588.
Proof. vm_refl. Qed.
Lemma D_db588 : decode_any W_db588 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_db58c : bv 32 := 0x00875793.
Lemma F_db58c : fetch_word Asan.M.loaded_segments (0xdb568 : word) = Some W_db58c.
Proof. vm_refl. Qed.
Lemma D_db58c : decode_any W_db58c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db590 : bv 32 := 0x01075813.
Lemma F_db590 : fetch_word Asan.M.loaded_segments (0xdb56c : word) = Some W_db590.
Proof. vm_refl. Qed.
Lemma D_db590 : decode_any W_db590 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db594 : bv 32 := 0xffd60613.
Lemma F_db594 : fetch_word Asan.M.loaded_segments (0xdb570 : word) = Some W_db594.
Proof. vm_refl. Qed.
Lemma D_db594 : decode_any W_db594 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_db598 : bv 32 := 0x00e68023.
Lemma F_db598 : fetch_word Asan.M.loaded_segments (0xdb574 : word) = Some W_db598.
Proof. vm_refl. Qed.
Lemma D_db598 : decode_any W_db598 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db59c : bv 32 := 0x00f680a3.
Lemma F_db59c : fetch_word Asan.M.loaded_segments (0xdb578 : word) = Some W_db59c.
Proof. vm_refl. Qed.
Lemma D_db59c : decode_any W_db59c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5a0 : bv 32 := 0x01068123.
Lemma F_db5a0 : fetch_word Asan.M.loaded_segments (0xdb57c : word) = Some W_db5a0.
Proof. vm_refl. Qed.
Lemma D_db5a0 : decode_any W_db5a0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5a4 : bv 32 := 0x00368693.
Lemma F_db5a4 : fetch_word Asan.M.loaded_segments (0xdb580 : word) = Some W_db5a4.
Proof. vm_refl. Qed.
Lemma D_db5a4 : decode_any W_db5a4 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5a8 : bv 32 := 0x01058593.
Lemma F_db5a8 : fetch_word Asan.M.loaded_segments (0xdb584 : word) = Some W_db5a8.
Proof. vm_refl. Qed.
Lemma D_db5a8 : decode_any W_db5a8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5ac : bv 32 := 0x01000793.
Lemma F_db5ac : fetch_word Asan.M.loaded_segments (0xdb588 : word) = Some W_db5ac.
Proof. vm_refl. Qed.
Lemma D_db5ac : decode_any W_db5ac = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5b0 : bv 32 := 0x0187581b.
Lemma F_db5b0 : fetch_word Asan.M.loaded_segments (0xdb58c : word) = Some W_db5b0.
Proof. vm_refl. Qed.
Lemma D_db5b0 : decode_any W_db5b0 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5b4 : bv 32 := 0xff45a883.
Lemma F_db5b4 : fetch_word Asan.M.loaded_segments (0xdb590 : word) = Some W_db5b4.
Proof. vm_refl. Qed.
Lemma D_db5b4 : decode_any W_db5b4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5b8 : bv 32 := 0xff85a283.
Lemma F_db5b8 : fetch_word Asan.M.loaded_segments (0xdb594 : word) = Some W_db5b8.
Proof. vm_refl. Qed.
Lemma D_db5b8 : decode_any W_db5b8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5bc : bv 32 := 0xffc5a303.
Lemma F_db5bc : fetch_word Asan.M.loaded_segments (0xdb598 : word) = Some W_db5bc.
Proof. vm_refl. Qed.
Lemma D_db5bc : decode_any W_db5bc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5c0 : bv 32 := 0x0005a703.
Lemma F_db5c0 : fetch_word Asan.M.loaded_segments (0xdb59c : word) = Some W_db5c0.
Proof. vm_refl. Qed.
Lemma D_db5c0 : decode_any W_db5c0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5c4 : bv 32 := 0x00889393.
Lemma F_db5c4 : fetch_word Asan.M.loaded_segments (0xdb5a0 : word) = Some W_db5c4.
Proof. vm_refl. Qed.
Lemma D_db5c4 : decode_any W_db5c4 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5c8 : bv 32 := 0x0188d89b.
Lemma F_db5c8 : fetch_word Asan.M.loaded_segments (0xdb5a4 : word) = Some W_db5c8.
Proof. vm_refl. Qed.
Lemma D_db5c8 : decode_any W_db5c8 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5cc : bv 32 := 0x0103e833.
Lemma F_db5cc : fetch_word Asan.M.loaded_segments (0xdb5a8 : word) = Some W_db5cc.
Proof. vm_refl. Qed.
Lemma D_db5cc : decode_any W_db5cc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5d0 : bv 32 := 0x00829393.
Lemma F_db5d0 : fetch_word Asan.M.loaded_segments (0xdb5ac : word) = Some W_db5d0.
Proof. vm_refl. Qed.
Lemma D_db5d0 : decode_any W_db5d0 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5d4 : bv 32 := 0x0182d29b.
Lemma F_db5d4 : fetch_word Asan.M.loaded_segments (0xdb5b0 : word) = Some W_db5d4.
Proof. vm_refl. Qed.
Lemma D_db5d4 : decode_any W_db5d4 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5d8 : bv 32 := 0x0113e8b3.
Lemma F_db5d8 : fetch_word Asan.M.loaded_segments (0xdb5b4 : word) = Some W_db5d8.
Proof. vm_refl. Qed.
Lemma D_db5d8 : decode_any W_db5d8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5dc : bv 32 := 0x00831393.
Lemma F_db5dc : fetch_word Asan.M.loaded_segments (0xdb5b8 : word) = Some W_db5dc.
Proof. vm_refl. Qed.
Lemma D_db5dc : decode_any W_db5dc = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5e0 : bv 32 := 0x0183531b.
Lemma F_db5e0 : fetch_word Asan.M.loaded_segments (0xdb5bc : word) = Some W_db5e0.
Proof. vm_refl. Qed.
Lemma D_db5e0 : decode_any W_db5e0 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5e4 : bv 32 := 0x0053e2b3.
Lemma F_db5e4 : fetch_word Asan.M.loaded_segments (0xdb5c0 : word) = Some W_db5e4.
Proof. vm_refl. Qed.
Lemma D_db5e4 : decode_any W_db5e4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5e8 : bv 32 := 0x00871393.
Lemma F_db5e8 : fetch_word Asan.M.loaded_segments (0xdb5c4 : word) = Some W_db5e8.
Proof. vm_refl. Qed.
Lemma D_db5e8 : decode_any W_db5e8 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5ec : bv 32 := 0x0063e333.
Lemma F_db5ec : fetch_word Asan.M.loaded_segments (0xdb5c8 : word) = Some W_db5ec.
Proof. vm_refl. Qed.
Lemma D_db5ec : decode_any W_db5ec = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5f0 : bv 32 := 0xff060613.
Lemma F_db5f0 : fetch_word Asan.M.loaded_segments (0xdb5cc : word) = Some W_db5f0.
Proof. vm_refl. Qed.
Lemma D_db5f0 : decode_any W_db5f0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5f4 : bv 32 := 0x0106a023.
Lemma F_db5f4 : fetch_word Asan.M.loaded_segments (0xdb5d0 : word) = Some W_db5f4.
Proof. vm_refl. Qed.
Lemma D_db5f4 : decode_any W_db5f4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5f8 : bv 32 := 0x0116a223.
Lemma F_db5f8 : fetch_word Asan.M.loaded_segments (0xdb5d4 : word) = Some W_db5f8.
Proof. vm_refl. Qed.
Lemma D_db5f8 : decode_any W_db5f8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db5fc : bv 32 := 0x0056a423.
Lemma F_db5fc : fetch_word Asan.M.loaded_segments (0xdb5d8 : word) = Some W_db5fc.
Proof. vm_refl. Qed.
Lemma D_db5fc : decode_any W_db5fc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db600 : bv 32 := 0x0066a623.
Lemma F_db600 : fetch_word Asan.M.loaded_segments (0xdb5dc : word) = Some W_db600.
Proof. vm_refl. Qed.
Lemma D_db600 : decode_any W_db600 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db604 : bv 32 := 0x01068693.
Lemma F_db604 : fetch_word Asan.M.loaded_segments (0xdb5e0 : word) = Some W_db604.
Proof. vm_refl. Qed.
Lemma D_db604 : decode_any W_db604 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db608 : bv 32 := 0x01058593.
Lemma F_db608 : fetch_word Asan.M.loaded_segments (0xdb5e4 : word) = Some W_db608.
Proof. vm_refl. Qed.
Lemma D_db608 : decode_any W_db608 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db60c : bv 32 := 0xfac7e2e3.
Lemma F_db60c : fetch_word Asan.M.loaded_segments (0xdb5e8 : word) = Some W_db60c.
Proof. vm_refl. Qed.
Lemma D_db60c : decode_any W_db60c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_db610 : bv 32 := 0xff358593.
Lemma F_db610 : fetch_word Asan.M.loaded_segments (0xdb5ec : word) = Some W_db610.
Proof. vm_refl. Qed.
Lemma D_db610 : decode_any W_db610 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_db614 : bv 32 := 0x01000713.
Lemma F_db614 : fetch_word Asan.M.loaded_segments (0xdb5f0 : word) = Some W_db614.
Proof. vm_refl. Qed.
Lemma D_db614 : decode_any W_db614 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db618 : bv 32 := 0xdae66ce3.
Lemma F_db618 : fetch_word Asan.M.loaded_segments (0xdb5f4 : word) = Some W_db618.
Proof. vm_refl. Qed.
Lemma D_db618 : decode_any W_db618 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_db61c : bv 32 := 0x0005c703.
Lemma F_db61c : fetch_word Asan.M.loaded_segments (0xdb5f8 : word) = Some W_db61c.
Proof. vm_refl. Qed.
Lemma D_db61c : decode_any W_db61c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db620 : bv 32 := 0x0015c783.
Lemma F_db620 : fetch_word Asan.M.loaded_segments (0xdb5fc : word) = Some W_db620.
Proof. vm_refl. Qed.
Lemma D_db620 : decode_any W_db620 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db624 : bv 32 := 0x0025c803.
Lemma F_db624 : fetch_word Asan.M.loaded_segments (0xdb600 : word) = Some W_db624.
Proof. vm_refl. Qed.
Lemma D_db624 : decode_any W_db624 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db628 : bv 32 := 0x0035c883.
Lemma F_db628 : fetch_word Asan.M.loaded_segments (0xdb604 : word) = Some W_db628.
Proof. vm_refl. Qed.
Lemma D_db628 : decode_any W_db628 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db62c : bv 32 := 0x0045c283.
Lemma F_db62c : fetch_word Asan.M.loaded_segments (0xdb608 : word) = Some W_db62c.
Proof. vm_refl. Qed.
Lemma D_db62c : decode_any W_db62c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db630 : bv 32 := 0x0055c303.
Lemma F_db630 : fetch_word Asan.M.loaded_segments (0xdb60c : word) = Some W_db630.
Proof. vm_refl. Qed.
Lemma D_db630 : decode_any W_db630 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db634 : bv 32 := 0x0065c383.
Lemma F_db634 : fetch_word Asan.M.loaded_segments (0xdb610 : word) = Some W_db634.
Proof. vm_refl. Qed.
Lemma D_db634 : decode_any W_db634 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db638 : bv 32 := 0x0075ce03.
Lemma F_db638 : fetch_word Asan.M.loaded_segments (0xdb614 : word) = Some W_db638.
Proof. vm_refl. Qed.
Lemma D_db638 : decode_any W_db638 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_db63c : bv 32 := 0x00e68023.
Lemma F_db63c : fetch_word Asan.M.loaded_segments (0xdb618 : word) = Some W_db63c.
Proof. vm_refl. Qed.
Lemma D_db63c : decode_any W_db63c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db640 : bv 32 := 0x00f680a3.
Lemma F_db640 : fetch_word Asan.M.loaded_segments (0xdb61c : word) = Some W_db640.
Proof. vm_refl. Qed.
Lemma D_db640 : decode_any W_db640 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db644 : bv 32 := 0x01068123.
Lemma F_db644 : fetch_word Asan.M.loaded_segments (0xdb620 : word) = Some W_db644.
Proof. vm_refl. Qed.
Lemma D_db644 : decode_any W_db644 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db648 : bv 32 := 0x011681a3.
Lemma F_db648 : fetch_word Asan.M.loaded_segments (0xdb624 : word) = Some W_db648.
Proof. vm_refl. Qed.
Lemma D_db648 : decode_any W_db648 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db64c : bv 32 := 0x0085c703.
Lemma F_db64c : fetch_word Asan.M.loaded_segments (0xdb628 : word) = Some W_db64c.
Proof. vm_refl. Qed.
Lemma D_db64c : decode_any W_db64c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db650 : bv 32 := 0x0095c783.
Lemma F_db650 : fetch_word Asan.M.loaded_segments (0xdb62c : word) = Some W_db650.
Proof. vm_refl. Qed.
Lemma D_db650 : decode_any W_db650 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_db654 : bv 32 := 0x00a5c803.
Lemma F_db654 : fetch_word Asan.M.loaded_segments (0xdb630 : word) = Some W_db654.
Proof. vm_refl. Qed.
Lemma D_db654 : decode_any W_db654 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_db658 : bv 32 := 0x00b5c883.
Lemma F_db658 : fetch_word Asan.M.loaded_segments (0xdb634 : word) = Some W_db658.
Proof. vm_refl. Qed.
Lemma D_db658 : decode_any W_db658 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_db65c : bv 32 := 0x00568223.
Lemma F_db65c : fetch_word Asan.M.loaded_segments (0xdb638 : word) = Some W_db65c.
Proof. vm_refl. Qed.
Lemma D_db65c : decode_any W_db65c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db660 : bv 32 := 0x006682a3.
Lemma F_db660 : fetch_word Asan.M.loaded_segments (0xdb63c : word) = Some W_db660.
Proof. vm_refl. Qed.
Lemma D_db660 : decode_any W_db660 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db664 : bv 32 := 0x00768323.
Lemma F_db664 : fetch_word Asan.M.loaded_segments (0xdb640 : word) = Some W_db664.
Proof. vm_refl. Qed.
Lemma D_db664 : decode_any W_db664 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db668 : bv 32 := 0x01c683a3.
Lemma F_db668 : fetch_word Asan.M.loaded_segments (0xdb644 : word) = Some W_db668.
Proof. vm_refl. Qed.
Lemma D_db668 : decode_any W_db668 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_db66c : bv 32 := 0x00c5c283.
Lemma F_db66c : fetch_word Asan.M.loaded_segments (0xdb648 : word) = Some W_db66c.
Proof. vm_refl. Qed.
Lemma D_db66c : decode_any W_db66c = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db670 : bv 32 := 0x00d5c303.
Lemma F_db670 : fetch_word Asan.M.loaded_segments (0xdb64c : word) = Some W_db670.
Proof. vm_refl. Qed.
Lemma D_db670 : decode_any W_db670 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_db674 : bv 32 := 0x00e5c383.
Lemma F_db674 : fetch_word Asan.M.loaded_segments (0xdb650 : word) = Some W_db674.
Proof. vm_refl. Qed.
Lemma D_db674 : decode_any W_db674 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_db678 : bv 32 := 0x00f5ce03.
Lemma F_db678 : fetch_word Asan.M.loaded_segments (0xdb654 : word) = Some W_db678.
Proof. vm_refl. Qed.
Lemma D_db678 : decode_any W_db678 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_db67c : bv 32 := 0x01058593.
Lemma F_db67c : fetch_word Asan.M.loaded_segments (0xdb658 : word) = Some W_db67c.
Proof. vm_refl. Qed.
Lemma D_db67c : decode_any W_db67c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db680 : bv 32 := 0x00e68423.
Lemma F_db680 : fetch_word Asan.M.loaded_segments (0xdb65c : word) = Some W_db680.
Proof. vm_refl. Qed.
Lemma D_db680 : decode_any W_db680 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db684 : bv 32 := 0x00f684a3.
Lemma F_db684 : fetch_word Asan.M.loaded_segments (0xdb660 : word) = Some W_db684.
Proof. vm_refl. Qed.
Lemma D_db684 : decode_any W_db684 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_db688 : bv 32 := 0x01068523.
Lemma F_db688 : fetch_word Asan.M.loaded_segments (0xdb664 : word) = Some W_db688.
Proof. vm_refl. Qed.
Lemma D_db688 : decode_any W_db688 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_db68c : bv 32 := 0x011685a3.
Lemma F_db68c : fetch_word Asan.M.loaded_segments (0xdb668 : word) = Some W_db68c.
Proof. vm_refl. Qed.
Lemma D_db68c : decode_any W_db68c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_db690 : bv 32 := 0x01068713.
Lemma F_db690 : fetch_word Asan.M.loaded_segments (0xdb66c : word) = Some W_db690.
Proof. vm_refl. Qed.
Lemma D_db690 : decode_any W_db690 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db694 : bv 32 := 0x00568623.
Lemma F_db694 : fetch_word Asan.M.loaded_segments (0xdb670 : word) = Some W_db694.
Proof. vm_refl. Qed.
Lemma D_db694 : decode_any W_db694 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_db698 : bv 32 := 0x006686a3.
Lemma F_db698 : fetch_word Asan.M.loaded_segments (0xdb674 : word) = Some W_db698.
Proof. vm_refl. Qed.
Lemma D_db698 : decode_any W_db698 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_db69c : bv 32 := 0x00768723.
Lemma F_db69c : fetch_word Asan.M.loaded_segments (0xdb678 : word) = Some W_db69c.
Proof. vm_refl. Qed.
Lemma D_db69c : decode_any W_db69c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6a0 : bv 32 := 0x01c687a3.
Lemma F_db6a0 : fetch_word Asan.M.loaded_segments (0xdb67c : word) = Some W_db6a0.
Proof. vm_refl. Qed.
Lemma D_db6a0 : decode_any W_db6a0 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6a4 : bv 32 := 0x00070693.
Lemma F_db6a4 : fetch_word Asan.M.loaded_segments (0xdb680 : word) = Some W_db6a4.
Proof. vm_refl. Qed.
Lemma D_db6a4 : decode_any W_db6a4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6a8 : bv 32 := 0x00867713.
Lemma F_db6a8 : fetch_word Asan.M.loaded_segments (0xdb684 : word) = Some W_db6a8.
Proof. vm_refl. Qed.
Lemma D_db6a8 : decode_any W_db6a8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6ac : bv 32 := 0xd20706e3.
Lemma F_db6ac : fetch_word Asan.M.loaded_segments (0xdb688 : word) = Some W_db6ac.
Proof. vm_refl. Qed.
Lemma D_db6ac : decode_any W_db6ac = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6b0 : bv 32 := 0x0005c703.
Lemma F_db6b0 : fetch_word Asan.M.loaded_segments (0xdb68c : word) = Some W_db6b0.
Proof. vm_refl. Qed.
Lemma D_db6b0 : decode_any W_db6b0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6b4 : bv 32 := 0x0015c783.
Lemma F_db6b4 : fetch_word Asan.M.loaded_segments (0xdb690 : word) = Some W_db6b4.
Proof. vm_refl. Qed.
Lemma D_db6b4 : decode_any W_db6b4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6b8 : bv 32 := 0x0025c803.
Lemma F_db6b8 : fetch_word Asan.M.loaded_segments (0xdb694 : word) = Some W_db6b8.
Proof. vm_refl. Qed.
Lemma D_db6b8 : decode_any W_db6b8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6bc : bv 32 := 0x0035c883.
Lemma F_db6bc : fetch_word Asan.M.loaded_segments (0xdb698 : word) = Some W_db6bc.
Proof. vm_refl. Qed.
Lemma D_db6bc : decode_any W_db6bc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6c0 : bv 32 := 0x0045c283.
Lemma F_db6c0 : fetch_word Asan.M.loaded_segments (0xdb69c : word) = Some W_db6c0.
Proof. vm_refl. Qed.
Lemma D_db6c0 : decode_any W_db6c0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6c4 : bv 32 := 0x0055c303.
Lemma F_db6c4 : fetch_word Asan.M.loaded_segments (0xdb6a0 : word) = Some W_db6c4.
Proof. vm_refl. Qed.
Lemma D_db6c4 : decode_any W_db6c4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6c8 : bv 32 := 0x0065c383.
Lemma F_db6c8 : fetch_word Asan.M.loaded_segments (0xdb6a4 : word) = Some W_db6c8.
Proof. vm_refl. Qed.
Lemma D_db6c8 : decode_any W_db6c8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6cc : bv 32 := 0x0075ce03.
Lemma F_db6cc : fetch_word Asan.M.loaded_segments (0xdb6a8 : word) = Some W_db6cc.
Proof. vm_refl. Qed.
Lemma D_db6cc : decode_any W_db6cc = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6d0 : bv 32 := 0x00858593.
Lemma F_db6d0 : fetch_word Asan.M.loaded_segments (0xdb6ac : word) = Some W_db6d0.
Proof. vm_refl. Qed.
Lemma D_db6d0 : decode_any W_db6d0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6d4 : bv 32 := 0x00e68023.
Lemma F_db6d4 : fetch_word Asan.M.loaded_segments (0xdb6b0 : word) = Some W_db6d4.
Proof. vm_refl. Qed.
Lemma D_db6d4 : decode_any W_db6d4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6d8 : bv 32 := 0x00f680a3.
Lemma F_db6d8 : fetch_word Asan.M.loaded_segments (0xdb6b4 : word) = Some W_db6d8.
Proof. vm_refl. Qed.
Lemma D_db6d8 : decode_any W_db6d8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6dc : bv 32 := 0x01068123.
Lemma F_db6dc : fetch_word Asan.M.loaded_segments (0xdb6b8 : word) = Some W_db6dc.
Proof. vm_refl. Qed.
Lemma D_db6dc : decode_any W_db6dc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6e0 : bv 32 := 0x011681a3.
Lemma F_db6e0 : fetch_word Asan.M.loaded_segments (0xdb6bc : word) = Some W_db6e0.
Proof. vm_refl. Qed.
Lemma D_db6e0 : decode_any W_db6e0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6e4 : bv 32 := 0x00868713.
Lemma F_db6e4 : fetch_word Asan.M.loaded_segments (0xdb6c0 : word) = Some W_db6e4.
Proof. vm_refl. Qed.
Lemma D_db6e4 : decode_any W_db6e4 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6e8 : bv 32 := 0x00568223.
Lemma F_db6e8 : fetch_word Asan.M.loaded_segments (0xdb6c4 : word) = Some W_db6e8.
Proof. vm_refl. Qed.
Lemma D_db6e8 : decode_any W_db6e8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6ec : bv 32 := 0x006682a3.
Lemma F_db6ec : fetch_word Asan.M.loaded_segments (0xdb6c8 : word) = Some W_db6ec.
Proof. vm_refl. Qed.
Lemma D_db6ec : decode_any W_db6ec = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6f0 : bv 32 := 0x00768323.
Lemma F_db6f0 : fetch_word Asan.M.loaded_segments (0xdb6cc : word) = Some W_db6f0.
Proof. vm_refl. Qed.
Lemma D_db6f0 : decode_any W_db6f0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6f4 : bv 32 := 0x01c683a3.
Lemma F_db6f4 : fetch_word Asan.M.loaded_segments (0xdb6d0 : word) = Some W_db6f4.
Proof. vm_refl. Qed.
Lemma D_db6f4 : decode_any W_db6f4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6f8 : bv 32 := 0x00070693.
Lemma F_db6f8 : fetch_word Asan.M.loaded_segments (0xdb6d4 : word) = Some W_db6f8.
Proof. vm_refl. Qed.
Lemma D_db6f8 : decode_any W_db6f8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db6fc : bv 32 := 0x00467713.
Lemma F_db6fc : fetch_word Asan.M.loaded_segments (0xdb6d8 : word) = Some W_db6fc.
Proof. vm_refl. Qed.
Lemma D_db6fc : decode_any W_db6fc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db700 : bv 32 := 0x02070863.
Lemma F_db700 : fetch_word Asan.M.loaded_segments (0xdb6dc : word) = Some W_db700.
Proof. vm_refl. Qed.
Lemma D_db700 : decode_any W_db700 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_db704 : bv 32 := 0x0005c703.
Lemma F_db704 : fetch_word Asan.M.loaded_segments (0xdb6e0 : word) = Some W_db704.
Proof. vm_refl. Qed.
Lemma D_db704 : decode_any W_db704 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db708 : bv 32 := 0x0015c783.
Lemma F_db708 : fetch_word Asan.M.loaded_segments (0xdb6e4 : word) = Some W_db708.
Proof. vm_refl. Qed.
Lemma D_db708 : decode_any W_db708 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db70c : bv 32 := 0x0025c803.
Lemma F_db70c : fetch_word Asan.M.loaded_segments (0xdb6e8 : word) = Some W_db70c.
Proof. vm_refl. Qed.
Lemma D_db70c : decode_any W_db70c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db710 : bv 32 := 0x0035c883.
Lemma F_db710 : fetch_word Asan.M.loaded_segments (0xdb6ec : word) = Some W_db710.
Proof. vm_refl. Qed.
Lemma D_db710 : decode_any W_db710 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db714 : bv 32 := 0x00458593.
Lemma F_db714 : fetch_word Asan.M.loaded_segments (0xdb6f0 : word) = Some W_db714.
Proof. vm_refl. Qed.
Lemma D_db714 : decode_any W_db714 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db718 : bv 32 := 0x00468293.
Lemma F_db718 : fetch_word Asan.M.loaded_segments (0xdb6f4 : word) = Some W_db718.
Proof. vm_refl. Qed.
Lemma D_db718 : decode_any W_db718 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_db71c : bv 32 := 0x00e68023.
Lemma F_db71c : fetch_word Asan.M.loaded_segments (0xdb6f8 : word) = Some W_db71c.
Proof. vm_refl. Qed.
Lemma D_db71c : decode_any W_db71c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db720 : bv 32 := 0x00f680a3.
Lemma F_db720 : fetch_word Asan.M.loaded_segments (0xdb6fc : word) = Some W_db720.
Proof. vm_refl. Qed.
Lemma D_db720 : decode_any W_db720 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db724 : bv 32 := 0x01068123.
Lemma F_db724 : fetch_word Asan.M.loaded_segments (0xdb700 : word) = Some W_db724.
Proof. vm_refl. Qed.
Lemma D_db724 : decode_any W_db724 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db728 : bv 32 := 0x011681a3.
Lemma F_db728 : fetch_word Asan.M.loaded_segments (0xdb704 : word) = Some W_db728.
Proof. vm_refl. Qed.
Lemma D_db728 : decode_any W_db728 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_db72c : bv 32 := 0x00028693.
Lemma F_db72c : fetch_word Asan.M.loaded_segments (0xdb708 : word) = Some W_db72c.
Proof. vm_refl. Qed.
Lemma D_db72c : decode_any W_db72c = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db730 : bv 32 := 0x00267713.
Lemma F_db730 : fetch_word Asan.M.loaded_segments (0xdb70c : word) = Some W_db730.
Proof. vm_refl. Qed.
Lemma D_db730 : decode_any W_db730 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db734 : bv 32 := 0x00071863.
Lemma F_db734 : fetch_word Asan.M.loaded_segments (0xdb710 : word) = Some W_db734.
Proof. vm_refl. Qed.
Lemma D_db734 : decode_any W_db734 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_db738 : bv 32 := 0x00167613.
Lemma F_db738 : fetch_word Asan.M.loaded_segments (0xdb714 : word) = Some W_db738.
Proof. vm_refl. Qed.
Lemma D_db738 : decode_any W_db738 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db73c : bv 32 := 0x02061663.
Lemma F_db73c : fetch_word Asan.M.loaded_segments (0xdb718 : word) = Some W_db73c.
Proof. vm_refl. Qed.
Lemma D_db73c : decode_any W_db73c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_db740 : bv 32 := 0x00008067.
Lemma F_db740 : fetch_word Asan.M.loaded_segments (0xdb71c : word) = Some W_db740.
Proof. vm_refl. Qed.
Lemma D_db740 : decode_any W_db740 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db744 : bv 32 := 0x0005c703.
Lemma F_db744 : fetch_word Asan.M.loaded_segments (0xdb720 : word) = Some W_db744.
Proof. vm_refl. Qed.
Lemma D_db744 : decode_any W_db744 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db748 : bv 32 := 0x0015c783.
Lemma F_db748 : fetch_word Asan.M.loaded_segments (0xdb724 : word) = Some W_db748.
Proof. vm_refl. Qed.
Lemma D_db748 : decode_any W_db748 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db74c : bv 32 := 0x00258593.
Lemma F_db74c : fetch_word Asan.M.loaded_segments (0xdb728 : word) = Some W_db74c.
Proof. vm_refl. Qed.
Lemma D_db74c : decode_any W_db74c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db750 : bv 32 := 0x00268813.
Lemma F_db750 : fetch_word Asan.M.loaded_segments (0xdb72c : word) = Some W_db750.
Proof. vm_refl. Qed.
Lemma D_db750 : decode_any W_db750 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_db754 : bv 32 := 0x00e68023.
Lemma F_db754 : fetch_word Asan.M.loaded_segments (0xdb730 : word) = Some W_db754.
Proof. vm_refl. Qed.
Lemma D_db754 : decode_any W_db754 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db758 : bv 32 := 0x00f680a3.
Lemma F_db758 : fetch_word Asan.M.loaded_segments (0xdb734 : word) = Some W_db758.
Proof. vm_refl. Qed.
Lemma D_db758 : decode_any W_db758 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db75c : bv 32 := 0x00080693.
Lemma F_db75c : fetch_word Asan.M.loaded_segments (0xdb738 : word) = Some W_db75c.
Proof. vm_refl. Qed.
Lemma D_db75c : decode_any W_db75c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db760 : bv 32 := 0x00167613.
Lemma F_db760 : fetch_word Asan.M.loaded_segments (0xdb73c : word) = Some W_db760.
Proof. vm_refl. Qed.
Lemma D_db760 : decode_any W_db760 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_db764 : bv 32 := 0xfc060ee3.
Lemma F_db764 : fetch_word Asan.M.loaded_segments (0xdb740 : word) = Some W_db764.
Proof. vm_refl. Qed.
Lemma D_db764 : decode_any W_db764 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_db768 : bv 32 := 0x0005c583.
Lemma F_db768 : fetch_word Asan.M.loaded_segments (0xdb744 : word) = Some W_db768.
Proof. vm_refl. Qed.
Lemma D_db768 : decode_any W_db768 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db76c : bv 32 := 0x00b68023.
Lemma F_db76c : fetch_word Asan.M.loaded_segments (0xdb748 : word) = Some W_db76c.
Proof. vm_refl. Qed.
Lemma D_db76c : decode_any W_db76c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_db770 : bv 32 := 0x00008067.
Lemma F_db770 : fetch_word Asan.M.loaded_segments (0xdb74c : word) = Some W_db770.
Proof. vm_refl. Qed.
Lemma D_db770 : decode_any W_db770 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.Asan.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_cbce4 : bv 32 := 0x0004b503.
Lemma F_cbce4 : fetch_word Asan.M.loaded_segments (0xcbccc : word) = Some W_cbce4.
Proof. vm_refl. Qed.
Lemma D_cbce4 : decode_any W_cbce4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbce8 : bv 32 := 0x00848493.
Lemma F_cbce8 : fetch_word Asan.M.loaded_segments (0xcbcd0 : word) = Some W_cbce8.
Proof. vm_refl. Qed.
Lemma D_cbce8 : decode_any W_cbce8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbcec : bv 32 := 0xfe051ce3.
Lemma F_cbcec : fetch_word Asan.M.loaded_segments (0xcbcd4 : word) = Some W_cbcec.
Proof. vm_refl. Qed.
Lemma D_cbcec : decode_any W_cbcec = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbda0 : bv 32 := 0x00b53023.
Lemma F_cbda0 : fetch_word Asan.M.loaded_segments (0xcbd88 : word) = Some W_cbda0.
Proof. vm_refl. Qed.
Lemma D_cbda0 : decode_any W_cbda0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbda4 : bv 32 := 0x00158593.
Lemma F_cbda4 : fetch_word Asan.M.loaded_segments (0xcbd8c : word) = Some W_cbda4.
Proof. vm_refl. Qed.
Lemma D_cbda4 : decode_any W_cbda4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbda8 : bv 32 := 0xfff5c683.
Lemma F_cbda8 : fetch_word Asan.M.loaded_segments (0xcbd90 : word) = Some W_cbda8.
Proof. vm_refl. Qed.
Lemma D_cbda8 : decode_any W_cbda8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdac : bv 32 := 0xfec68ae3.
Lemma F_cbdac : fetch_word Asan.M.loaded_segments (0xcbd94 : word) = Some W_cbdac.
Proof. vm_refl. Qed.
Lemma D_cbdac : decode_any W_cbdac = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cbdb0 : bv 32 := 0xfe069ae3.
Lemma F_cbdb0 : fetch_word Asan.M.loaded_segments (0xcbd98 : word) = Some W_cbdb0.
Proof. vm_refl. Qed.
Lemma D_cbdb0 : decode_any W_cbdb0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
End Mq2.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_dde60 : bv 32 := 0x0e060a63.
Lemma F_dde60 : fetch_word AsanUbsan.M.loaded_segments (0xdde14 : word) = Some W_dde60.
Proof. vm_refl. Qed.
Lemma D_dde60 : decode_any W_dde60 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde64 : bv 32 := 0x00b50023.
Lemma F_dde64 : fetch_word AsanUbsan.M.loaded_segments (0xdde18 : word) = Some W_dde64.
Proof. vm_refl. Qed.
Lemma D_dde64 : decode_any W_dde64 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde68 : bv 32 := 0x00c506b3.
Lemma F_dde68 : fetch_word AsanUbsan.M.loaded_segments (0xdde1c : word) = Some W_dde68.
Proof. vm_refl. Qed.
Lemma D_dde68 : decode_any W_dde68 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde6c : bv 32 := 0x00300713.
Lemma F_dde6c : fetch_word AsanUbsan.M.loaded_segments (0xdde20 : word) = Some W_dde6c.
Proof. vm_refl. Qed.
Lemma D_dde6c : decode_any W_dde6c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde70 : bv 32 := 0xfeb68fa3.
Lemma F_dde70 : fetch_word AsanUbsan.M.loaded_segments (0xdde24 : word) = Some W_dde70.
Proof. vm_refl. Qed.
Lemma D_dde70 : decode_any W_dde70 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde74 : bv 32 := 0x0ee66063.
Lemma F_dde74 : fetch_word AsanUbsan.M.loaded_segments (0xdde28 : word) = Some W_dde74.
Proof. vm_refl. Qed.
Lemma D_dde74 : decode_any W_dde74 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde78 : bv 32 := 0x00b500a3.
Lemma F_dde78 : fetch_word AsanUbsan.M.loaded_segments (0xdde2c : word) = Some W_dde78.
Proof. vm_refl. Qed.
Lemma D_dde78 : decode_any W_dde78 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde7c : bv 32 := 0x00b50123.
Lemma F_dde7c : fetch_word AsanUbsan.M.loaded_segments (0xdde30 : word) = Some W_dde7c.
Proof. vm_refl. Qed.
Lemma D_dde7c : decode_any W_dde7c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde80 : bv 32 := 0x00700713.
Lemma F_dde80 : fetch_word AsanUbsan.M.loaded_segments (0xdde34 : word) = Some W_dde80.
Proof. vm_refl. Qed.
Lemma D_dde80 : decode_any W_dde80 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde84 : bv 32 := 0xfeb68ea3.
Lemma F_dde84 : fetch_word AsanUbsan.M.loaded_segments (0xdde38 : word) = Some W_dde84.
Proof. vm_refl. Qed.
Lemma D_dde84 : decode_any W_dde84 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde88 : bv 32 := 0xfeb68f23.
Lemma F_dde88 : fetch_word AsanUbsan.M.loaded_segments (0xdde3c : word) = Some W_dde88.
Proof. vm_refl. Qed.
Lemma D_dde88 : decode_any W_dde88 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde8c : bv 32 := 0x0ce66463.
Lemma F_dde8c : fetch_word AsanUbsan.M.loaded_segments (0xdde40 : word) = Some W_dde8c.
Proof. vm_refl. Qed.
Lemma D_dde8c : decode_any W_dde8c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde90 : bv 32 := 0x00b501a3.
Lemma F_dde90 : fetch_word AsanUbsan.M.loaded_segments (0xdde44 : word) = Some W_dde90.
Proof. vm_refl. Qed.
Lemma D_dde90 : decode_any W_dde90 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde94 : bv 32 := 0x00900793.
Lemma F_dde94 : fetch_word AsanUbsan.M.loaded_segments (0xdde48 : word) = Some W_dde94.
Proof. vm_refl. Qed.
Lemma D_dde94 : decode_any W_dde94 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde98 : bv 32 := 0xfeb68e23.
Lemma F_dde98 : fetch_word AsanUbsan.M.loaded_segments (0xdde4c : word) = Some W_dde98.
Proof. vm_refl. Qed.
Lemma D_dde98 : decode_any W_dde98 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde9c : bv 32 := 0x0af66c63.
Lemma F_dde9c : fetch_word AsanUbsan.M.loaded_segments (0xdde50 : word) = Some W_dde9c.
Proof. vm_refl. Qed.
Lemma D_dde9c : decode_any W_dde9c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddea0 : bv 32 := 0x40a006bb.
Lemma F_ddea0 : fetch_word AsanUbsan.M.loaded_segments (0xdde54 : word) = Some W_ddea0.
Proof. vm_refl. Qed.
Lemma D_ddea0 : decode_any W_ddea0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddea4 : bv 32 := 0x03859813.
Lemma F_ddea4 : fetch_word AsanUbsan.M.loaded_segments (0xdde58 : word) = Some W_ddea4.
Proof. vm_refl. Qed.
Lemma D_ddea4 : decode_any W_ddea4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddea8 : bv 32 := 0x101015b7.
Lemma F_ddea8 : fetch_word AsanUbsan.M.loaded_segments (0xdde5c : word) = Some W_ddea8.
Proof. vm_refl. Qed.
Lemma D_ddea8 : decode_any W_ddea8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddeac : bv 32 := 0x0036f693.
Lemma F_ddeac : fetch_word AsanUbsan.M.loaded_segments (0xdde60 : word) = Some W_ddeac.
Proof. vm_refl. Qed.
Lemma D_ddeac : decode_any W_ddeac = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddeb0 : bv 32 := 0x00459713.
Lemma F_ddeb0 : fetch_word AsanUbsan.M.loaded_segments (0xdde64 : word) = Some W_ddeb0.
Proof. vm_refl. Qed.
Lemma D_ddeb0 : decode_any W_ddeb0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddeb4 : bv 32 := 0x40d60633.
Lemma F_ddeb4 : fetch_word AsanUbsan.M.loaded_segments (0xdde68 : word) = Some W_ddeb4.
Proof. vm_refl. Qed.
Lemma D_ddeb4 : decode_any W_ddeb4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddeb8 : bv 32 := 0x00d505b3.
Lemma F_ddeb8 : fetch_word AsanUbsan.M.loaded_segments (0xdde6c : word) = Some W_ddeb8.
Proof. vm_refl. Qed.
Lemma D_ddeb8 : decode_any W_ddeb8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddebc : bv 32 := 0x10070693.
Lemma F_ddebc : fetch_word AsanUbsan.M.loaded_segments (0xdde70 : word) = Some W_ddebc.
Proof. vm_refl. Qed.
Lemma D_ddebc : decode_any W_ddebc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddec0 : bv 32 := 0xffc67713.
Lemma F_ddec0 : fetch_word AsanUbsan.M.loaded_segments (0xdde74 : word) = Some W_ddec0.
Proof. vm_refl. Qed.
Lemma D_ddec0 : decode_any W_ddec0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddec4 : bv 32 := 0x02d83633.
Lemma F_ddec4 : fetch_word AsanUbsan.M.loaded_segments (0xdde78 : word) = Some W_ddec4.
Proof. vm_refl. Qed.
Lemma D_ddec4 : decode_any W_ddec4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddec8 : bv 32 := 0x00c5a023.
Lemma F_ddec8 : fetch_word AsanUbsan.M.loaded_segments (0xdde7c : word) = Some W_ddec8.
Proof. vm_refl. Qed.
Lemma D_ddec8 : decode_any W_ddec8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddecc : bv 32 := 0x00e586b3.
Lemma F_ddecc : fetch_word AsanUbsan.M.loaded_segments (0xdde80 : word) = Some W_ddecc.
Proof. vm_refl. Qed.
Lemma D_ddecc : decode_any W_ddecc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_dded0 : bv 32 := 0xfec6ae23.
Lemma F_dded0 : fetch_word AsanUbsan.M.loaded_segments (0xdde84 : word) = Some W_dded0.
Proof. vm_refl. Qed.
Lemma D_dded0 : decode_any W_dded0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_dded4 : bv 32 := 0x08f76063.
Lemma F_dded4 : fetch_word AsanUbsan.M.loaded_segments (0xdde88 : word) = Some W_dded4.
Proof. vm_refl. Qed.
Lemma D_dded4 : decode_any W_dded4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_dded8 : bv 32 := 0x00c5a223.
Lemma F_dded8 : fetch_word AsanUbsan.M.loaded_segments (0xdde8c : word) = Some W_dded8.
Proof. vm_refl. Qed.
Lemma D_dded8 : decode_any W_dded8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddedc : bv 32 := 0x00c5a423.
Lemma F_ddedc : fetch_word AsanUbsan.M.loaded_segments (0xdde90 : word) = Some W_ddedc.
Proof. vm_refl. Qed.
Lemma D_ddedc : decode_any W_ddedc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddee0 : bv 32 := 0x01900793.
Lemma F_ddee0 : fetch_word AsanUbsan.M.loaded_segments (0xdde94 : word) = Some W_ddee0.
Proof. vm_refl. Qed.
Lemma D_ddee0 : decode_any W_ddee0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddee4 : bv 32 := 0xfec6aa23.
Lemma F_ddee4 : fetch_word AsanUbsan.M.loaded_segments (0xdde98 : word) = Some W_ddee4.
Proof. vm_refl. Qed.
Lemma D_ddee4 : decode_any W_ddee4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddee8 : bv 32 := 0xfec6ac23.
Lemma F_ddee8 : fetch_word AsanUbsan.M.loaded_segments (0xdde9c : word) = Some W_ddee8.
Proof. vm_refl. Qed.
Lemma D_ddee8 : decode_any W_ddee8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddeec : bv 32 := 0x06f76463.
Lemma F_ddeec : fetch_word AsanUbsan.M.loaded_segments (0xddea0 : word) = Some W_ddeec.
Proof. vm_refl. Qed.
Lemma D_ddeec : decode_any W_ddeec = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddef0 : bv 32 := 0x00c5a623.
Lemma F_ddef0 : fetch_word AsanUbsan.M.loaded_segments (0xddea4 : word) = Some W_ddef0.
Proof. vm_refl. Qed.
Lemma D_ddef0 : decode_any W_ddef0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddef4 : bv 32 := 0x00c5a823.
Lemma F_ddef4 : fetch_word AsanUbsan.M.loaded_segments (0xddea8 : word) = Some W_ddef4.
Proof. vm_refl. Qed.
Lemma D_ddef4 : decode_any W_ddef4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddef8 : bv 32 := 0x00c5aa23.
Lemma F_ddef8 : fetch_word AsanUbsan.M.loaded_segments (0xddeac : word) = Some W_ddef8.
Proof. vm_refl. Qed.
Lemma D_ddef8 : decode_any W_ddef8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddefc : bv 32 := 0x00c5ac23.
Lemma F_ddefc : fetch_word AsanUbsan.M.loaded_segments (0xddeb0 : word) = Some W_ddefc.
Proof. vm_refl. Qed.
Lemma D_ddefc : decode_any W_ddefc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf00 : bv 32 := 0x0045f793.
Lemma F_ddf00 : fetch_word AsanUbsan.M.loaded_segments (0xddeb4 : word) = Some W_ddf00.
Proof. vm_refl. Qed.
Lemma D_ddf00 : decode_any W_ddf00 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf04 : bv 32 := 0x02000813.
Lemma F_ddf04 : fetch_word AsanUbsan.M.loaded_segments (0xddeb8 : word) = Some W_ddf04.
Proof. vm_refl. Qed.
Lemma D_ddf04 : decode_any W_ddf04 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf08 : bv 32 := 0x01878793.
Lemma F_ddf08 : fetch_word AsanUbsan.M.loaded_segments (0xddebc : word) = Some W_ddf08.
Proof. vm_refl. Qed.
Lemma D_ddf08 : decode_any W_ddf08 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf0c : bv 32 := 0x40f70733.
Lemma F_ddf0c : fetch_word AsanUbsan.M.loaded_segments (0xddec0 : word) = Some W_ddf0c.
Proof. vm_refl. Qed.
Lemma D_ddf0c : decode_any W_ddf0c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf10 : bv 32 := 0xfec6a223.
Lemma F_ddf10 : fetch_word AsanUbsan.M.loaded_segments (0xddec4 : word) = Some W_ddf10.
Proof. vm_refl. Qed.
Lemma D_ddf10 : decode_any W_ddf10 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf14 : bv 32 := 0xfec6a423.
Lemma F_ddf14 : fetch_word AsanUbsan.M.loaded_segments (0xddec8 : word) = Some W_ddf14.
Proof. vm_refl. Qed.
Lemma D_ddf14 : decode_any W_ddf14 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf18 : bv 32 := 0xfec6a623.
Lemma F_ddf18 : fetch_word AsanUbsan.M.loaded_segments (0xddecc : word) = Some W_ddf18.
Proof. vm_refl. Qed.
Lemma D_ddf18 : decode_any W_ddf18 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf1c : bv 32 := 0xfec6a823.
Lemma F_ddf1c : fetch_word AsanUbsan.M.loaded_segments (0xdded0 : word) = Some W_ddf1c.
Proof. vm_refl. Qed.
Lemma D_ddf1c : decode_any W_ddf1c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf20 : bv 32 := 0x03076a63.
Lemma F_ddf20 : fetch_word AsanUbsan.M.loaded_segments (0xdded4 : word) = Some W_ddf20.
Proof. vm_refl. Qed.
Lemma D_ddf20 : decode_any W_ddf20 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf24 : bv 32 := 0x02061613.
Lemma F_ddf24 : fetch_word AsanUbsan.M.loaded_segments (0xdded8 : word) = Some W_ddf24.
Proof. vm_refl. Qed.
Lemma D_ddf24 : decode_any W_ddf24 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf28 : bv 32 := 0x00f585b3.
Lemma F_ddf28 : fetch_word AsanUbsan.M.loaded_segments (0xddedc : word) = Some W_ddf28.
Proof. vm_refl. Qed.
Lemma D_ddf28 : decode_any W_ddf28 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf2c : bv 32 := 0x02065693.
Lemma F_ddf2c : fetch_word AsanUbsan.M.loaded_segments (0xddee0 : word) = Some W_ddf2c.
Proof. vm_refl. Qed.
Lemma D_ddf2c : decode_any W_ddf2c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf30 : bv 32 := 0x00d66633.
Lemma F_ddf30 : fetch_word AsanUbsan.M.loaded_segments (0xddee4 : word) = Some W_ddf30.
Proof. vm_refl. Qed.
Lemma D_ddf30 : decode_any W_ddf30 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf34 : bv 32 := 0x01f00693.
Lemma F_ddf34 : fetch_word AsanUbsan.M.loaded_segments (0xddee8 : word) = Some W_ddf34.
Proof. vm_refl. Qed.
Lemma D_ddf34 : decode_any W_ddf34 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf38 : bv 32 := 0x00c5b023.
Lemma F_ddf38 : fetch_word AsanUbsan.M.loaded_segments (0xddeec : word) = Some W_ddf38.
Proof. vm_refl. Qed.
Lemma D_ddf38 : decode_any W_ddf38 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf3c : bv 32 := 0x00c5b423.
Lemma F_ddf3c : fetch_word AsanUbsan.M.loaded_segments (0xddef0 : word) = Some W_ddf3c.
Proof. vm_refl. Qed.
Lemma D_ddf3c : decode_any W_ddf3c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf40 : bv 32 := 0x00c5b823.
Lemma F_ddf40 : fetch_word AsanUbsan.M.loaded_segments (0xddef4 : word) = Some W_ddf40.
Proof. vm_refl. Qed.
Lemma D_ddf40 : decode_any W_ddf40 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf44 : bv 32 := 0x00c5bc23.
Lemma F_ddf44 : fetch_word AsanUbsan.M.loaded_segments (0xddef8 : word) = Some W_ddf44.
Proof. vm_refl. Qed.
Lemma D_ddf44 : decode_any W_ddf44 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf48 : bv 32 := 0xfe070713.
Lemma F_ddf48 : fetch_word AsanUbsan.M.loaded_segments (0xddefc : word) = Some W_ddf48.
Proof. vm_refl. Qed.
Lemma D_ddf48 : decode_any W_ddf48 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf4c : bv 32 := 0x02058593.
Lemma F_ddf4c : fetch_word AsanUbsan.M.loaded_segments (0xddf00 : word) = Some W_ddf4c.
Proof. vm_refl. Qed.
Lemma D_ddf4c : decode_any W_ddf4c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf50 : bv 32 := 0xfee6e4e3.
Lemma F_ddf50 : fetch_word AsanUbsan.M.loaded_segments (0xddf04 : word) = Some W_ddf50.
Proof. vm_refl. Qed.
Lemma D_ddf50 : decode_any W_ddf50 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddf54 : bv 32 := 0x00008067.
Lemma F_ddf54 : fetch_word AsanUbsan.M.loaded_segments (0xddf08 : word) = Some W_ddf54.
Proof. vm_refl. Qed.
Lemma D_ddf54 : decode_any W_ddf54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xdde14%Z.
Definition Fo_000 := F_dde60.
Definition Do_000 := D_dde60.
Definition Fo_004 := F_dde64.
Definition Do_004 := D_dde64.
Definition Fo_008 := F_dde68.
Definition Do_008 := D_dde68.
Definition Fo_00c := F_dde6c.
Definition Do_00c := D_dde6c.
Definition Fo_010 := F_dde70.
Definition Do_010 := D_dde70.
Definition Fo_014 := F_dde74.
Definition Do_014 := D_dde74.
Definition Fo_018 := F_dde78.
Definition Do_018 := D_dde78.
Definition Fo_01c := F_dde7c.
Definition Do_01c := D_dde7c.
Definition Fo_020 := F_dde80.
Definition Do_020 := D_dde80.
Definition Fo_024 := F_dde84.
Definition Do_024 := D_dde84.
Definition Fo_028 := F_dde88.
Definition Do_028 := D_dde88.
Definition Fo_02c := F_dde8c.
Definition Do_02c := D_dde8c.
Definition Fo_030 := F_dde90.
Definition Do_030 := D_dde90.
Definition Fo_034 := F_dde94.
Definition Do_034 := D_dde94.
Definition Fo_038 := F_dde98.
Definition Do_038 := D_dde98.
Definition Fo_03c := F_dde9c.
Definition Do_03c := D_dde9c.
Definition Fo_040 := F_ddea0.
Definition Do_040 := D_ddea0.
Definition Fo_044 := F_ddea4.
Definition Do_044 := D_ddea4.
Definition Fo_048 := F_ddea8.
Definition Do_048 := D_ddea8.
Definition Fo_04c := F_ddeac.
Definition Do_04c := D_ddeac.
Definition Fo_050 := F_ddeb0.
Definition Do_050 := D_ddeb0.
Definition Fo_054 := F_ddeb4.
Definition Do_054 := D_ddeb4.
Definition Fo_058 := F_ddeb8.
Definition Do_058 := D_ddeb8.
Definition Fo_05c := F_ddebc.
Definition Do_05c := D_ddebc.
Definition Fo_060 := F_ddec0.
Definition Do_060 := D_ddec0.
Definition Fo_064 := F_ddec4.
Definition Do_064 := D_ddec4.
Definition Fo_068 := F_ddec8.
Definition Do_068 := D_ddec8.
Definition Fo_06c := F_ddecc.
Definition Do_06c := D_ddecc.
Definition Fo_070 := F_dded0.
Definition Do_070 := D_dded0.
Definition Fo_074 := F_dded4.
Definition Do_074 := D_dded4.
Definition Fo_078 := F_dded8.
Definition Do_078 := D_dded8.
Definition Fo_07c := F_ddedc.
Definition Do_07c := D_ddedc.
Definition Fo_080 := F_ddee0.
Definition Do_080 := D_ddee0.
Definition Fo_084 := F_ddee4.
Definition Do_084 := D_ddee4.
Definition Fo_088 := F_ddee8.
Definition Do_088 := D_ddee8.
Definition Fo_08c := F_ddeec.
Definition Do_08c := D_ddeec.
Definition Fo_090 := F_ddef0.
Definition Do_090 := D_ddef0.
Definition Fo_094 := F_ddef4.
Definition Do_094 := D_ddef4.
Definition Fo_098 := F_ddef8.
Definition Do_098 := D_ddef8.
Definition Fo_09c := F_ddefc.
Definition Do_09c := D_ddefc.
Definition Fo_0a0 := F_ddf00.
Definition Do_0a0 := D_ddf00.
Definition Fo_0a4 := F_ddf04.
Definition Do_0a4 := D_ddf04.
Definition Fo_0a8 := F_ddf08.
Definition Do_0a8 := D_ddf08.
Definition Fo_0ac := F_ddf0c.
Definition Do_0ac := D_ddf0c.
Definition Fo_0b0 := F_ddf10.
Definition Do_0b0 := D_ddf10.
Definition Fo_0b4 := F_ddf14.
Definition Do_0b4 := D_ddf14.
Definition Fo_0b8 := F_ddf18.
Definition Do_0b8 := D_ddf18.
Definition Fo_0bc := F_ddf1c.
Definition Do_0bc := D_ddf1c.
Definition Fo_0c0 := F_ddf20.
Definition Do_0c0 := D_ddf20.
Definition Fo_0c4 := F_ddf24.
Definition Do_0c4 := D_ddf24.
Definition Fo_0c8 := F_ddf28.
Definition Do_0c8 := D_ddf28.
Definition Fo_0cc := F_ddf2c.
Definition Do_0cc := D_ddf2c.
Definition Fo_0d0 := F_ddf30.
Definition Do_0d0 := D_ddf30.
Definition Fo_0d4 := F_ddf34.
Definition Do_0d4 := D_ddf34.
Definition Fo_0d8 := F_ddf38.
Definition Do_0d8 := D_ddf38.
Definition Fo_0dc := F_ddf3c.
Definition Do_0dc := D_ddf3c.
Definition Fo_0e0 := F_ddf40.
Definition Do_0e0 := D_ddf40.
Definition Fo_0e4 := F_ddf44.
Definition Do_0e4 := D_ddf44.
Definition Fo_0e8 := F_ddf48.
Definition Do_0e8 := D_ddf48.
Definition Fo_0ec := F_ddf4c.
Definition Do_0ec := D_ddf4c.
Definition Fo_0f0 := F_ddf50.
Definition Do_0f0 := D_ddf50.
Definition Fo_0f4 := F_ddf54.
Definition Do_0f4 := D_ddf54.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_dda5c : bv 32 := 0x0035f693.
Lemma F_dda5c : fetch_word AsanUbsan.M.loaded_segments (0xdda10 : word) = Some W_dda5c.
Proof. vm_refl. Qed.
Lemma D_dda5c : decode_any W_dda5c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda60 : bv 32 := 0x10068863.
Lemma F_dda60 : fetch_word AsanUbsan.M.loaded_segments (0xdda14 : word) = Some W_dda60.
Proof. vm_refl. Qed.
Lemma D_dda60 : decode_any W_dda60 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda64 : bv 32 := 0x02060e63.
Lemma F_dda64 : fetch_word AsanUbsan.M.loaded_segments (0xdda18 : word) = Some W_dda64.
Proof. vm_refl. Qed.
Lemma D_dda64 : decode_any W_dda64 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda68 : bv 32 := 0x00158713.
Lemma F_dda68 : fetch_word AsanUbsan.M.loaded_segments (0xdda1c : word) = Some W_dda68.
Proof. vm_refl. Qed.
Lemma D_dda68 : decode_any W_dda68 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda6c : bv 32 := 0x00100793.
Lemma F_dda6c : fetch_word AsanUbsan.M.loaded_segments (0xdda20 : word) = Some W_dda6c.
Proof. vm_refl. Qed.
Lemma D_dda6c : decode_any W_dda6c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda70 : bv 32 := 0x00050693.
Lemma F_dda70 : fetch_word AsanUbsan.M.loaded_segments (0xdda24 : word) = Some W_dda70.
Proof. vm_refl. Qed.
Lemma D_dda70 : decode_any W_dda70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda74 : bv 32 := 0x0005c883.
Lemma F_dda74 : fetch_word AsanUbsan.M.loaded_segments (0xdda28 : word) = Some W_dda74.
Proof. vm_refl. Qed.
Lemma D_dda74 : decode_any W_dda74 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda78 : bv 32 := 0x00060813.
Lemma F_dda78 : fetch_word AsanUbsan.M.loaded_segments (0xdda2c : word) = Some W_dda78.
Proof. vm_refl. Qed.
Lemma D_dda78 : decode_any W_dda78 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda7c : bv 32 := 0x00158593.
Lemma F_dda7c : fetch_word AsanUbsan.M.loaded_segments (0xdda30 : word) = Some W_dda7c.
Proof. vm_refl. Qed.
Lemma D_dda7c : decode_any W_dda7c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda80 : bv 32 := 0x00377293.
Lemma F_dda80 : fetch_word AsanUbsan.M.loaded_segments (0xdda34 : word) = Some W_dda80.
Proof. vm_refl. Qed.
Lemma D_dda80 : decode_any W_dda80 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda84 : bv 32 := 0x01168023.
Lemma F_dda84 : fetch_word AsanUbsan.M.loaded_segments (0xdda38 : word) = Some W_dda84.
Proof. vm_refl. Qed.
Lemma D_dda84 : decode_any W_dda84 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda88 : bv 32 := 0x00168693.
Lemma F_dda88 : fetch_word AsanUbsan.M.loaded_segments (0xdda3c : word) = Some W_dda88.
Proof. vm_refl. Qed.
Lemma D_dda88 : decode_any W_dda88 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda8c : bv 32 := 0xfff60613.
Lemma F_dda8c : fetch_word AsanUbsan.M.loaded_segments (0xdda40 : word) = Some W_dda8c.
Proof. vm_refl. Qed.
Lemma D_dda8c : decode_any W_dda8c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda90 : bv 32 := 0x00028a63.
Lemma F_dda90 : fetch_word AsanUbsan.M.loaded_segments (0xdda44 : word) = Some W_dda90.
Proof. vm_refl. Qed.
Lemma D_dda90 : decode_any W_dda90 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda94 : bv 32 := 0x00170713.
Lemma F_dda94 : fetch_word AsanUbsan.M.loaded_segments (0xdda48 : word) = Some W_dda94.
Proof. vm_refl. Qed.
Lemma D_dda94 : decode_any W_dda94 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda98 : bv 32 := 0xfcf81ee3.
Lemma F_dda98 : fetch_word AsanUbsan.M.loaded_segments (0xdda4c : word) = Some W_dda98.
Proof. vm_refl. Qed.
Lemma D_dda98 : decode_any W_dda98 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_dda9c : bv 32 := 0x0080006f.
Lemma F_dda9c : fetch_word AsanUbsan.M.loaded_segments (0xdda50 : word) = Some W_dda9c.
Proof. vm_refl. Qed.
Lemma D_dda9c : decode_any W_dda9c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaa0 : bv 32 := 0x00050693.
Lemma F_ddaa0 : fetch_word AsanUbsan.M.loaded_segments (0xdda54 : word) = Some W_ddaa0.
Proof. vm_refl. Qed.
Lemma D_ddaa0 : decode_any W_ddaa0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaa4 : bv 32 := 0x0036f793.
Lemma F_ddaa4 : fetch_word AsanUbsan.M.loaded_segments (0xdda58 : word) = Some W_ddaa4.
Proof. vm_refl. Qed.
Lemma D_ddaa4 : decode_any W_ddaa4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaa8 : bv 32 := 0x0c078a63.
Lemma F_ddaa8 : fetch_word AsanUbsan.M.loaded_segments (0xdda5c : word) = Some W_ddaa8.
Proof. vm_refl. Qed.
Lemma D_ddaa8 : decode_any W_ddaa8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaac : bv 32 := 0x02000713.
Lemma F_ddaac : fetch_word AsanUbsan.M.loaded_segments (0xdda60 : word) = Some W_ddaac.
Proof. vm_refl. Qed.
Lemma D_ddaac : decode_any W_ddaac = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddab0 : bv 32 := 0x02e67063.
Lemma F_ddab0 : fetch_word AsanUbsan.M.loaded_segments (0xdda64 : word) = Some W_ddab0.
Proof. vm_refl. Qed.
Lemma D_ddab0 : decode_any W_ddab0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddab4 : bv 32 := 0x01000713.
Lemma F_ddab4 : fetch_word AsanUbsan.M.loaded_segments (0xdda68 : word) = Some W_ddab4.
Proof. vm_refl. Qed.
Lemma D_ddab4 : decode_any W_ddab4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddab8 : bv 32 := 0x24e67863.
Lemma F_ddab8 : fetch_word AsanUbsan.M.loaded_segments (0xdda6c : word) = Some W_ddab8.
Proof. vm_refl. Qed.
Lemma D_ddab8 : decode_any W_ddab8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddabc : bv 32 := 0x00867713.
Lemma F_ddabc : fetch_word AsanUbsan.M.loaded_segments (0xdda70 : word) = Some W_ddabc.
Proof. vm_refl. Qed.
Lemma D_ddabc : decode_any W_ddabc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddac0 : bv 32 := 0x2c071e63.
Lemma F_ddac0 : fetch_word AsanUbsan.M.loaded_segments (0xdda74 : word) = Some W_ddac0.
Proof. vm_refl. Qed.
Lemma D_ddac0 : decode_any W_ddac0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddac4 : bv 32 := 0x00467713.
Lemma F_ddac4 : fetch_word AsanUbsan.M.loaded_segments (0xdda78 : word) = Some W_ddac4.
Proof. vm_refl. Qed.
Lemma D_ddac4 : decode_any W_ddac4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddac8 : bv 32 := 0x32071463.
Lemma F_ddac8 : fetch_word AsanUbsan.M.loaded_segments (0xdda7c : word) = Some W_ddac8.
Proof. vm_refl. Qed.
Lemma D_ddac8 : decode_any W_ddac8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddacc : bv 32 := 0x3500006f.
Lemma F_ddacc : fetch_word AsanUbsan.M.loaded_segments (0xdda80 : word) = Some W_ddacc.
Proof. vm_refl. Qed.
Lemma D_ddacc : decode_any W_ddacc = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddad0 : bv 32 := 0x0005a703.
Lemma F_ddad0 : fetch_word AsanUbsan.M.loaded_segments (0xdda84 : word) = Some W_ddad0.
Proof. vm_refl. Qed.
Lemma D_ddad0 : decode_any W_ddad0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddad4 : bv 32 := 0x00300813.
Lemma F_ddad4 : fetch_word AsanUbsan.M.loaded_segments (0xdda88 : word) = Some W_ddad4.
Proof. vm_refl. Qed.
Lemma D_ddad4 : decode_any W_ddad4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddad8 : bv 32 := 0x11078e63.
Lemma F_ddad8 : fetch_word AsanUbsan.M.loaded_segments (0xdda8c : word) = Some W_ddad8.
Proof. vm_refl. Qed.
Lemma D_ddad8 : decode_any W_ddad8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddadc : bv 32 := 0x00200813.
Lemma F_ddadc : fetch_word AsanUbsan.M.loaded_segments (0xdda90 : word) = Some W_ddadc.
Proof. vm_refl. Qed.
Lemma D_ddadc : decode_any W_ddadc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddae0 : bv 32 := 0x19079c63.
Lemma F_ddae0 : fetch_word AsanUbsan.M.loaded_segments (0xdda94 : word) = Some W_ddae0.
Proof. vm_refl. Qed.
Lemma D_ddae0 : decode_any W_ddae0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddae4 : bv 32 := 0x00875793.
Lemma F_ddae4 : fetch_word AsanUbsan.M.loaded_segments (0xdda98 : word) = Some W_ddae4.
Proof. vm_refl. Qed.
Lemma D_ddae4 : decode_any W_ddae4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddae8 : bv 32 := 0xffe60613.
Lemma F_ddae8 : fetch_word AsanUbsan.M.loaded_segments (0xdda9c : word) = Some W_ddae8.
Proof. vm_refl. Qed.
Lemma D_ddae8 : decode_any W_ddae8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaec : bv 32 := 0x00e68023.
Lemma F_ddaec : fetch_word AsanUbsan.M.loaded_segments (0xddaa0 : word) = Some W_ddaec.
Proof. vm_refl. Qed.
Lemma D_ddaec : decode_any W_ddaec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaf0 : bv 32 := 0x00f680a3.
Lemma F_ddaf0 : fetch_word AsanUbsan.M.loaded_segments (0xddaa4 : word) = Some W_ddaf0.
Proof. vm_refl. Qed.
Lemma D_ddaf0 : decode_any W_ddaf0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaf4 : bv 32 := 0x00268693.
Lemma F_ddaf4 : fetch_word AsanUbsan.M.loaded_segments (0xddaa8 : word) = Some W_ddaf4.
Proof. vm_refl. Qed.
Lemma D_ddaf4 : decode_any W_ddaf4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddaf8 : bv 32 := 0x01058593.
Lemma F_ddaf8 : fetch_word AsanUbsan.M.loaded_segments (0xddaac : word) = Some W_ddaf8.
Proof. vm_refl. Qed.
Lemma D_ddaf8 : decode_any W_ddaf8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddafc : bv 32 := 0x01100793.
Lemma F_ddafc : fetch_word AsanUbsan.M.loaded_segments (0xddab0 : word) = Some W_ddafc.
Proof. vm_refl. Qed.
Lemma D_ddafc : decode_any W_ddafc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb00 : bv 32 := 0x0107581b.
Lemma F_ddb00 : fetch_word AsanUbsan.M.loaded_segments (0xddab4 : word) = Some W_ddb00.
Proof. vm_refl. Qed.
Lemma D_ddb00 : decode_any W_ddb00 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb04 : bv 32 := 0xff45a883.
Lemma F_ddb04 : fetch_word AsanUbsan.M.loaded_segments (0xddab8 : word) = Some W_ddb04.
Proof. vm_refl. Qed.
Lemma D_ddb04 : decode_any W_ddb04 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb08 : bv 32 := 0xff85a283.
Lemma F_ddb08 : fetch_word AsanUbsan.M.loaded_segments (0xddabc : word) = Some W_ddb08.
Proof. vm_refl. Qed.
Lemma D_ddb08 : decode_any W_ddb08 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb0c : bv 32 := 0xffc5a303.
Lemma F_ddb0c : fetch_word AsanUbsan.M.loaded_segments (0xddac0 : word) = Some W_ddb0c.
Proof. vm_refl. Qed.
Lemma D_ddb0c : decode_any W_ddb0c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb10 : bv 32 := 0x0005a703.
Lemma F_ddb10 : fetch_word AsanUbsan.M.loaded_segments (0xddac4 : word) = Some W_ddb10.
Proof. vm_refl. Qed.
Lemma D_ddb10 : decode_any W_ddb10 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb14 : bv 32 := 0x01089393.
Lemma F_ddb14 : fetch_word AsanUbsan.M.loaded_segments (0xddac8 : word) = Some W_ddb14.
Proof. vm_refl. Qed.
Lemma D_ddb14 : decode_any W_ddb14 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb18 : bv 32 := 0x0108d89b.
Lemma F_ddb18 : fetch_word AsanUbsan.M.loaded_segments (0xddacc : word) = Some W_ddb18.
Proof. vm_refl. Qed.
Lemma D_ddb18 : decode_any W_ddb18 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb1c : bv 32 := 0x0103e833.
Lemma F_ddb1c : fetch_word AsanUbsan.M.loaded_segments (0xddad0 : word) = Some W_ddb1c.
Proof. vm_refl. Qed.
Lemma D_ddb1c : decode_any W_ddb1c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb20 : bv 32 := 0x01029393.
Lemma F_ddb20 : fetch_word AsanUbsan.M.loaded_segments (0xddad4 : word) = Some W_ddb20.
Proof. vm_refl. Qed.
Lemma D_ddb20 : decode_any W_ddb20 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb24 : bv 32 := 0x0102d29b.
Lemma F_ddb24 : fetch_word AsanUbsan.M.loaded_segments (0xddad8 : word) = Some W_ddb24.
Proof. vm_refl. Qed.
Lemma D_ddb24 : decode_any W_ddb24 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb28 : bv 32 := 0x0113e8b3.
Lemma F_ddb28 : fetch_word AsanUbsan.M.loaded_segments (0xddadc : word) = Some W_ddb28.
Proof. vm_refl. Qed.
Lemma D_ddb28 : decode_any W_ddb28 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb2c : bv 32 := 0x01031393.
Lemma F_ddb2c : fetch_word AsanUbsan.M.loaded_segments (0xddae0 : word) = Some W_ddb2c.
Proof. vm_refl. Qed.
Lemma D_ddb2c : decode_any W_ddb2c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb30 : bv 32 := 0x0103531b.
Lemma F_ddb30 : fetch_word AsanUbsan.M.loaded_segments (0xddae4 : word) = Some W_ddb30.
Proof. vm_refl. Qed.
Lemma D_ddb30 : decode_any W_ddb30 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb34 : bv 32 := 0x0053e2b3.
Lemma F_ddb34 : fetch_word AsanUbsan.M.loaded_segments (0xddae8 : word) = Some W_ddb34.
Proof. vm_refl. Qed.
Lemma D_ddb34 : decode_any W_ddb34 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb38 : bv 32 := 0x01071393.
Lemma F_ddb38 : fetch_word AsanUbsan.M.loaded_segments (0xddaec : word) = Some W_ddb38.
Proof. vm_refl. Qed.
Lemma D_ddb38 : decode_any W_ddb38 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb3c : bv 32 := 0x0063e333.
Lemma F_ddb3c : fetch_word AsanUbsan.M.loaded_segments (0xddaf0 : word) = Some W_ddb3c.
Proof. vm_refl. Qed.
Lemma D_ddb3c : decode_any W_ddb3c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb40 : bv 32 := 0xff060613.
Lemma F_ddb40 : fetch_word AsanUbsan.M.loaded_segments (0xddaf4 : word) = Some W_ddb40.
Proof. vm_refl. Qed.
Lemma D_ddb40 : decode_any W_ddb40 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb44 : bv 32 := 0x0106a023.
Lemma F_ddb44 : fetch_word AsanUbsan.M.loaded_segments (0xddaf8 : word) = Some W_ddb44.
Proof. vm_refl. Qed.
Lemma D_ddb44 : decode_any W_ddb44 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb48 : bv 32 := 0x0116a223.
Lemma F_ddb48 : fetch_word AsanUbsan.M.loaded_segments (0xddafc : word) = Some W_ddb48.
Proof. vm_refl. Qed.
Lemma D_ddb48 : decode_any W_ddb48 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb4c : bv 32 := 0x0056a423.
Lemma F_ddb4c : fetch_word AsanUbsan.M.loaded_segments (0xddb00 : word) = Some W_ddb4c.
Proof. vm_refl. Qed.
Lemma D_ddb4c : decode_any W_ddb4c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb50 : bv 32 := 0x0066a623.
Lemma F_ddb50 : fetch_word AsanUbsan.M.loaded_segments (0xddb04 : word) = Some W_ddb50.
Proof. vm_refl. Qed.
Lemma D_ddb50 : decode_any W_ddb50 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb54 : bv 32 := 0x01068693.
Lemma F_ddb54 : fetch_word AsanUbsan.M.loaded_segments (0xddb08 : word) = Some W_ddb54.
Proof. vm_refl. Qed.
Lemma D_ddb54 : decode_any W_ddb54 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb58 : bv 32 := 0x01058593.
Lemma F_ddb58 : fetch_word AsanUbsan.M.loaded_segments (0xddb0c : word) = Some W_ddb58.
Proof. vm_refl. Qed.
Lemma D_ddb58 : decode_any W_ddb58 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb5c : bv 32 := 0xfac7e2e3.
Lemma F_ddb5c : fetch_word AsanUbsan.M.loaded_segments (0xddb10 : word) = Some W_ddb5c.
Proof. vm_refl. Qed.
Lemma D_ddb5c : decode_any W_ddb5c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb60 : bv 32 := 0xff258593.
Lemma F_ddb60 : fetch_word AsanUbsan.M.loaded_segments (0xddb14 : word) = Some W_ddb60.
Proof. vm_refl. Qed.
Lemma D_ddb60 : decode_any W_ddb60 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb64 : bv 32 := 0x01000713.
Lemma F_ddb64 : fetch_word AsanUbsan.M.loaded_segments (0xddb18 : word) = Some W_ddb64.
Proof. vm_refl. Qed.
Lemma D_ddb64 : decode_any W_ddb64 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb68 : bv 32 := 0xf4e66ae3.
Lemma F_ddb68 : fetch_word AsanUbsan.M.loaded_segments (0xddb1c : word) = Some W_ddb68.
Proof. vm_refl. Qed.
Lemma D_ddb68 : decode_any W_ddb68 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb6c : bv 32 := 0x19c0006f.
Lemma F_ddb6c : fetch_word AsanUbsan.M.loaded_segments (0xddb20 : word) = Some W_ddb6c.
Proof. vm_refl. Qed.
Lemma D_ddb6c : decode_any W_ddb6c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb70 : bv 32 := 0x00050693.
Lemma F_ddb70 : fetch_word AsanUbsan.M.loaded_segments (0xddb24 : word) = Some W_ddb70.
Proof. vm_refl. Qed.
Lemma D_ddb70 : decode_any W_ddb70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb74 : bv 32 := 0x00357793.
Lemma F_ddb74 : fetch_word AsanUbsan.M.loaded_segments (0xddb28 : word) = Some W_ddb74.
Proof. vm_refl. Qed.
Lemma D_ddb74 : decode_any W_ddb74 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb78 : bv 32 := 0xf2079ae3.
Lemma F_ddb78 : fetch_word AsanUbsan.M.loaded_segments (0xddb2c : word) = Some W_ddb78.
Proof. vm_refl. Qed.
Lemma D_ddb78 : decode_any W_ddb78 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb7c : bv 32 := 0x01000713.
Lemma F_ddb7c : fetch_word AsanUbsan.M.loaded_segments (0xddb30 : word) = Some W_ddb7c.
Proof. vm_refl. Qed.
Lemma D_ddb7c : decode_any W_ddb7c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb80 : bv 32 := 0x02e66c63.
Lemma F_ddb80 : fetch_word AsanUbsan.M.loaded_segments (0xddb34 : word) = Some W_ddb80.
Proof. vm_refl. Qed.
Lemma D_ddb80 : decode_any W_ddb80 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb84 : bv 32 := 0x00f00713.
Lemma F_ddb84 : fetch_word AsanUbsan.M.loaded_segments (0xddb38 : word) = Some W_ddb84.
Proof. vm_refl. Qed.
Lemma D_ddb84 : decode_any W_ddb84 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb88 : bv 32 := 0x0005a783.
Lemma F_ddb88 : fetch_word AsanUbsan.M.loaded_segments (0xddb3c : word) = Some W_ddb88.
Proof. vm_refl. Qed.
Lemma D_ddb88 : decode_any W_ddb88 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb8c : bv 32 := 0x0045a803.
Lemma F_ddb8c : fetch_word AsanUbsan.M.loaded_segments (0xddb40 : word) = Some W_ddb8c.
Proof. vm_refl. Qed.
Lemma D_ddb8c : decode_any W_ddb8c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb90 : bv 32 := 0x0085a883.
Lemma F_ddb90 : fetch_word AsanUbsan.M.loaded_segments (0xddb44 : word) = Some W_ddb90.
Proof. vm_refl. Qed.
Lemma D_ddb90 : decode_any W_ddb90 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb94 : bv 32 := 0x00c5a283.
Lemma F_ddb94 : fetch_word AsanUbsan.M.loaded_segments (0xddb48 : word) = Some W_ddb94.
Proof. vm_refl. Qed.
Lemma D_ddb94 : decode_any W_ddb94 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb98 : bv 32 := 0x01058593.
Lemma F_ddb98 : fetch_word AsanUbsan.M.loaded_segments (0xddb4c : word) = Some W_ddb98.
Proof. vm_refl. Qed.
Lemma D_ddb98 : decode_any W_ddb98 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddb9c : bv 32 := 0xff060613.
Lemma F_ddb9c : fetch_word AsanUbsan.M.loaded_segments (0xddb50 : word) = Some W_ddb9c.
Proof. vm_refl. Qed.
Lemma D_ddb9c : decode_any W_ddb9c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddba0 : bv 32 := 0x00f6a023.
Lemma F_ddba0 : fetch_word AsanUbsan.M.loaded_segments (0xddb54 : word) = Some W_ddba0.
Proof. vm_refl. Qed.
Lemma D_ddba0 : decode_any W_ddba0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddba4 : bv 32 := 0x0106a223.
Lemma F_ddba4 : fetch_word AsanUbsan.M.loaded_segments (0xddb58 : word) = Some W_ddba4.
Proof. vm_refl. Qed.
Lemma D_ddba4 : decode_any W_ddba4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddba8 : bv 32 := 0x0116a423.
Lemma F_ddba8 : fetch_word AsanUbsan.M.loaded_segments (0xddb5c : word) = Some W_ddba8.
Proof. vm_refl. Qed.
Lemma D_ddba8 : decode_any W_ddba8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbac : bv 32 := 0x0056a623.
Lemma F_ddbac : fetch_word AsanUbsan.M.loaded_segments (0xddb60 : word) = Some W_ddbac.
Proof. vm_refl. Qed.
Lemma D_ddbac : decode_any W_ddbac = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbb0 : bv 32 := 0x01068693.
Lemma F_ddbb0 : fetch_word AsanUbsan.M.loaded_segments (0xddb64 : word) = Some W_ddbb0.
Proof. vm_refl. Qed.
Lemma D_ddbb0 : decode_any W_ddbb0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbb4 : bv 32 := 0xfcc76ae3.
Lemma F_ddbb4 : fetch_word AsanUbsan.M.loaded_segments (0xddb68 : word) = Some W_ddbb4.
Proof. vm_refl. Qed.
Lemma D_ddbb4 : decode_any W_ddbb4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbb8 : bv 32 := 0x00800713.
Lemma F_ddbb8 : fetch_word AsanUbsan.M.loaded_segments (0xddb6c : word) = Some W_ddbb8.
Proof. vm_refl. Qed.
Lemma D_ddbb8 : decode_any W_ddbb8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbbc : bv 32 := 0x00e66e63.
Lemma F_ddbbc : fetch_word AsanUbsan.M.loaded_segments (0xddb70 : word) = Some W_ddbbc.
Proof. vm_refl. Qed.
Lemma D_ddbbc : decode_any W_ddbbc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbc0 : bv 32 := 0x0005a703.
Lemma F_ddbc0 : fetch_word AsanUbsan.M.loaded_segments (0xddb74 : word) = Some W_ddbc0.
Proof. vm_refl. Qed.
Lemma D_ddbc0 : decode_any W_ddbc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbc4 : bv 32 := 0x0045a783.
Lemma F_ddbc4 : fetch_word AsanUbsan.M.loaded_segments (0xddb78 : word) = Some W_ddbc4.
Proof. vm_refl. Qed.
Lemma D_ddbc4 : decode_any W_ddbc4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbc8 : bv 32 := 0x00e6a023.
Lemma F_ddbc8 : fetch_word AsanUbsan.M.loaded_segments (0xddb7c : word) = Some W_ddbc8.
Proof. vm_refl. Qed.
Lemma D_ddbc8 : decode_any W_ddbc8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbcc : bv 32 := 0x00f6a223.
Lemma F_ddbcc : fetch_word AsanUbsan.M.loaded_segments (0xddb80 : word) = Some W_ddbcc.
Proof. vm_refl. Qed.
Lemma D_ddbcc : decode_any W_ddbcc = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbd0 : bv 32 := 0x00868693.
Lemma F_ddbd0 : fetch_word AsanUbsan.M.loaded_segments (0xddb84 : word) = Some W_ddbd0.
Proof. vm_refl. Qed.
Lemma D_ddbd0 : decode_any W_ddbd0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbd4 : bv 32 := 0x00858593.
Lemma F_ddbd4 : fetch_word AsanUbsan.M.loaded_segments (0xddb88 : word) = Some W_ddbd4.
Proof. vm_refl. Qed.
Lemma D_ddbd4 : decode_any W_ddbd4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbd8 : bv 32 := 0x00467713.
Lemma F_ddbd8 : fetch_word AsanUbsan.M.loaded_segments (0xddb8c : word) = Some W_ddbd8.
Proof. vm_refl. Qed.
Lemma D_ddbd8 : decode_any W_ddbd8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbdc : bv 32 := 0x24070063.
Lemma F_ddbdc : fetch_word AsanUbsan.M.loaded_segments (0xddb90 : word) = Some W_ddbdc.
Proof. vm_refl. Qed.
Lemma D_ddbdc : decode_any W_ddbdc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbe0 : bv 32 := 0x0005a703.
Lemma F_ddbe0 : fetch_word AsanUbsan.M.loaded_segments (0xddb94 : word) = Some W_ddbe0.
Proof. vm_refl. Qed.
Lemma D_ddbe0 : decode_any W_ddbe0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbe4 : bv 32 := 0x00458593.
Lemma F_ddbe4 : fetch_word AsanUbsan.M.loaded_segments (0xddb98 : word) = Some W_ddbe4.
Proof. vm_refl. Qed.
Lemma D_ddbe4 : decode_any W_ddbe4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbe8 : bv 32 := 0x00e6a023.
Lemma F_ddbe8 : fetch_word AsanUbsan.M.loaded_segments (0xddb9c : word) = Some W_ddbe8.
Proof. vm_refl. Qed.
Lemma D_ddbe8 : decode_any W_ddbe8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbec : bv 32 := 0x00468693.
Lemma F_ddbec : fetch_word AsanUbsan.M.loaded_segments (0xddba0 : word) = Some W_ddbec.
Proof. vm_refl. Qed.
Lemma D_ddbec : decode_any W_ddbec = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbf0 : bv 32 := 0x22c0006f.
Lemma F_ddbf0 : fetch_word AsanUbsan.M.loaded_segments (0xddba4 : word) = Some W_ddbf0.
Proof. vm_refl. Qed.
Lemma D_ddbf0 : decode_any W_ddbf0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbf4 : bv 32 := 0x00e68023.
Lemma F_ddbf4 : fetch_word AsanUbsan.M.loaded_segments (0xddba8 : word) = Some W_ddbf4.
Proof. vm_refl. Qed.
Lemma D_ddbf4 : decode_any W_ddbf4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbf8 : bv 32 := 0x00168693.
Lemma F_ddbf8 : fetch_word AsanUbsan.M.loaded_segments (0xddbac : word) = Some W_ddbf8.
Proof. vm_refl. Qed.
Lemma D_ddbf8 : decode_any W_ddbf8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddbfc : bv 32 := 0xfff60613.
Lemma F_ddbfc : fetch_word AsanUbsan.M.loaded_segments (0xddbb0 : word) = Some W_ddbfc.
Proof. vm_refl. Qed.
Lemma D_ddbfc : decode_any W_ddbfc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc00 : bv 32 := 0x01058593.
Lemma F_ddc00 : fetch_word AsanUbsan.M.loaded_segments (0xddbb4 : word) = Some W_ddc00.
Proof. vm_refl. Qed.
Lemma D_ddc00 : decode_any W_ddc00 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc04 : bv 32 := 0x01200793.
Lemma F_ddc04 : fetch_word AsanUbsan.M.loaded_segments (0xddbb8 : word) = Some W_ddc04.
Proof. vm_refl. Qed.
Lemma D_ddc04 : decode_any W_ddc04 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc08 : bv 32 := 0x0087581b.
Lemma F_ddc08 : fetch_word AsanUbsan.M.loaded_segments (0xddbbc : word) = Some W_ddc08.
Proof. vm_refl. Qed.
Lemma D_ddc08 : decode_any W_ddc08 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc0c : bv 32 := 0xff45a883.
Lemma F_ddc0c : fetch_word AsanUbsan.M.loaded_segments (0xddbc0 : word) = Some W_ddc0c.
Proof. vm_refl. Qed.
Lemma D_ddc0c : decode_any W_ddc0c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc10 : bv 32 := 0xff85a283.
Lemma F_ddc10 : fetch_word AsanUbsan.M.loaded_segments (0xddbc4 : word) = Some W_ddc10.
Proof. vm_refl. Qed.
Lemma D_ddc10 : decode_any W_ddc10 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc14 : bv 32 := 0xffc5a303.
Lemma F_ddc14 : fetch_word AsanUbsan.M.loaded_segments (0xddbc8 : word) = Some W_ddc14.
Proof. vm_refl. Qed.
Lemma D_ddc14 : decode_any W_ddc14 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc18 : bv 32 := 0x0005a703.
Lemma F_ddc18 : fetch_word AsanUbsan.M.loaded_segments (0xddbcc : word) = Some W_ddc18.
Proof. vm_refl. Qed.
Lemma D_ddc18 : decode_any W_ddc18 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc1c : bv 32 := 0x01889393.
Lemma F_ddc1c : fetch_word AsanUbsan.M.loaded_segments (0xddbd0 : word) = Some W_ddc1c.
Proof. vm_refl. Qed.
Lemma D_ddc1c : decode_any W_ddc1c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc20 : bv 32 := 0x0088d89b.
Lemma F_ddc20 : fetch_word AsanUbsan.M.loaded_segments (0xddbd4 : word) = Some W_ddc20.
Proof. vm_refl. Qed.
Lemma D_ddc20 : decode_any W_ddc20 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc24 : bv 32 := 0x0103e833.
Lemma F_ddc24 : fetch_word AsanUbsan.M.loaded_segments (0xddbd8 : word) = Some W_ddc24.
Proof. vm_refl. Qed.
Lemma D_ddc24 : decode_any W_ddc24 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc28 : bv 32 := 0x01829393.
Lemma F_ddc28 : fetch_word AsanUbsan.M.loaded_segments (0xddbdc : word) = Some W_ddc28.
Proof. vm_refl. Qed.
Lemma D_ddc28 : decode_any W_ddc28 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc2c : bv 32 := 0x0082d29b.
Lemma F_ddc2c : fetch_word AsanUbsan.M.loaded_segments (0xddbe0 : word) = Some W_ddc2c.
Proof. vm_refl. Qed.
Lemma D_ddc2c : decode_any W_ddc2c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc30 : bv 32 := 0x0113e8b3.
Lemma F_ddc30 : fetch_word AsanUbsan.M.loaded_segments (0xddbe4 : word) = Some W_ddc30.
Proof. vm_refl. Qed.
Lemma D_ddc30 : decode_any W_ddc30 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc34 : bv 32 := 0x01831393.
Lemma F_ddc34 : fetch_word AsanUbsan.M.loaded_segments (0xddbe8 : word) = Some W_ddc34.
Proof. vm_refl. Qed.
Lemma D_ddc34 : decode_any W_ddc34 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc38 : bv 32 := 0x0083531b.
Lemma F_ddc38 : fetch_word AsanUbsan.M.loaded_segments (0xddbec : word) = Some W_ddc38.
Proof. vm_refl. Qed.
Lemma D_ddc38 : decode_any W_ddc38 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc3c : bv 32 := 0x0053e2b3.
Lemma F_ddc3c : fetch_word AsanUbsan.M.loaded_segments (0xddbf0 : word) = Some W_ddc3c.
Proof. vm_refl. Qed.
Lemma D_ddc3c : decode_any W_ddc3c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc40 : bv 32 := 0x01871393.
Lemma F_ddc40 : fetch_word AsanUbsan.M.loaded_segments (0xddbf4 : word) = Some W_ddc40.
Proof. vm_refl. Qed.
Lemma D_ddc40 : decode_any W_ddc40 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc44 : bv 32 := 0x0063e333.
Lemma F_ddc44 : fetch_word AsanUbsan.M.loaded_segments (0xddbf8 : word) = Some W_ddc44.
Proof. vm_refl. Qed.
Lemma D_ddc44 : decode_any W_ddc44 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc48 : bv 32 := 0xff060613.
Lemma F_ddc48 : fetch_word AsanUbsan.M.loaded_segments (0xddbfc : word) = Some W_ddc48.
Proof. vm_refl. Qed.
Lemma D_ddc48 : decode_any W_ddc48 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc4c : bv 32 := 0x0106a023.
Lemma F_ddc4c : fetch_word AsanUbsan.M.loaded_segments (0xddc00 : word) = Some W_ddc4c.
Proof. vm_refl. Qed.
Lemma D_ddc4c : decode_any W_ddc4c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc50 : bv 32 := 0x0116a223.
Lemma F_ddc50 : fetch_word AsanUbsan.M.loaded_segments (0xddc04 : word) = Some W_ddc50.
Proof. vm_refl. Qed.
Lemma D_ddc50 : decode_any W_ddc50 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc54 : bv 32 := 0x0056a423.
Lemma F_ddc54 : fetch_word AsanUbsan.M.loaded_segments (0xddc08 : word) = Some W_ddc54.
Proof. vm_refl. Qed.
Lemma D_ddc54 : decode_any W_ddc54 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc58 : bv 32 := 0x0066a623.
Lemma F_ddc58 : fetch_word AsanUbsan.M.loaded_segments (0xddc0c : word) = Some W_ddc58.
Proof. vm_refl. Qed.
Lemma D_ddc58 : decode_any W_ddc58 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc5c : bv 32 := 0x01068693.
Lemma F_ddc5c : fetch_word AsanUbsan.M.loaded_segments (0xddc10 : word) = Some W_ddc5c.
Proof. vm_refl. Qed.
Lemma D_ddc5c : decode_any W_ddc5c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc60 : bv 32 := 0x01058593.
Lemma F_ddc60 : fetch_word AsanUbsan.M.loaded_segments (0xddc14 : word) = Some W_ddc60.
Proof. vm_refl. Qed.
Lemma D_ddc60 : decode_any W_ddc60 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc64 : bv 32 := 0xfac7e2e3.
Lemma F_ddc64 : fetch_word AsanUbsan.M.loaded_segments (0xddc18 : word) = Some W_ddc64.
Proof. vm_refl. Qed.
Lemma D_ddc64 : decode_any W_ddc64 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc68 : bv 32 := 0xff158593.
Lemma F_ddc68 : fetch_word AsanUbsan.M.loaded_segments (0xddc1c : word) = Some W_ddc68.
Proof. vm_refl. Qed.
Lemma D_ddc68 : decode_any W_ddc68 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc6c : bv 32 := 0x01000713.
Lemma F_ddc6c : fetch_word AsanUbsan.M.loaded_segments (0xddc20 : word) = Some W_ddc6c.
Proof. vm_refl. Qed.
Lemma D_ddc6c : decode_any W_ddc6c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc70 : bv 32 := 0xe4e666e3.
Lemma F_ddc70 : fetch_word AsanUbsan.M.loaded_segments (0xddc24 : word) = Some W_ddc70.
Proof. vm_refl. Qed.
Lemma D_ddc70 : decode_any W_ddc70 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc74 : bv 32 := 0x0940006f.
Lemma F_ddc74 : fetch_word AsanUbsan.M.loaded_segments (0xddc28 : word) = Some W_ddc74.
Proof. vm_refl. Qed.
Lemma D_ddc74 : decode_any W_ddc74 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc78 : bv 32 := 0x00875793.
Lemma F_ddc78 : fetch_word AsanUbsan.M.loaded_segments (0xddc2c : word) = Some W_ddc78.
Proof. vm_refl. Qed.
Lemma D_ddc78 : decode_any W_ddc78 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc7c : bv 32 := 0x01075813.
Lemma F_ddc7c : fetch_word AsanUbsan.M.loaded_segments (0xddc30 : word) = Some W_ddc7c.
Proof. vm_refl. Qed.
Lemma D_ddc7c : decode_any W_ddc7c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc80 : bv 32 := 0xffd60613.
Lemma F_ddc80 : fetch_word AsanUbsan.M.loaded_segments (0xddc34 : word) = Some W_ddc80.
Proof. vm_refl. Qed.
Lemma D_ddc80 : decode_any W_ddc80 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc84 : bv 32 := 0x00e68023.
Lemma F_ddc84 : fetch_word AsanUbsan.M.loaded_segments (0xddc38 : word) = Some W_ddc84.
Proof. vm_refl. Qed.
Lemma D_ddc84 : decode_any W_ddc84 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc88 : bv 32 := 0x00f680a3.
Lemma F_ddc88 : fetch_word AsanUbsan.M.loaded_segments (0xddc3c : word) = Some W_ddc88.
Proof. vm_refl. Qed.
Lemma D_ddc88 : decode_any W_ddc88 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc8c : bv 32 := 0x01068123.
Lemma F_ddc8c : fetch_word AsanUbsan.M.loaded_segments (0xddc40 : word) = Some W_ddc8c.
Proof. vm_refl. Qed.
Lemma D_ddc8c : decode_any W_ddc8c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc90 : bv 32 := 0x00368693.
Lemma F_ddc90 : fetch_word AsanUbsan.M.loaded_segments (0xddc44 : word) = Some W_ddc90.
Proof. vm_refl. Qed.
Lemma D_ddc90 : decode_any W_ddc90 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc94 : bv 32 := 0x01058593.
Lemma F_ddc94 : fetch_word AsanUbsan.M.loaded_segments (0xddc48 : word) = Some W_ddc94.
Proof. vm_refl. Qed.
Lemma D_ddc94 : decode_any W_ddc94 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc98 : bv 32 := 0x01000793.
Lemma F_ddc98 : fetch_word AsanUbsan.M.loaded_segments (0xddc4c : word) = Some W_ddc98.
Proof. vm_refl. Qed.
Lemma D_ddc98 : decode_any W_ddc98 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddc9c : bv 32 := 0x0187581b.
Lemma F_ddc9c : fetch_word AsanUbsan.M.loaded_segments (0xddc50 : word) = Some W_ddc9c.
Proof. vm_refl. Qed.
Lemma D_ddc9c : decode_any W_ddc9c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddca0 : bv 32 := 0xff45a883.
Lemma F_ddca0 : fetch_word AsanUbsan.M.loaded_segments (0xddc54 : word) = Some W_ddca0.
Proof. vm_refl. Qed.
Lemma D_ddca0 : decode_any W_ddca0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddca4 : bv 32 := 0xff85a283.
Lemma F_ddca4 : fetch_word AsanUbsan.M.loaded_segments (0xddc58 : word) = Some W_ddca4.
Proof. vm_refl. Qed.
Lemma D_ddca4 : decode_any W_ddca4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddca8 : bv 32 := 0xffc5a303.
Lemma F_ddca8 : fetch_word AsanUbsan.M.loaded_segments (0xddc5c : word) = Some W_ddca8.
Proof. vm_refl. Qed.
Lemma D_ddca8 : decode_any W_ddca8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcac : bv 32 := 0x0005a703.
Lemma F_ddcac : fetch_word AsanUbsan.M.loaded_segments (0xddc60 : word) = Some W_ddcac.
Proof. vm_refl. Qed.
Lemma D_ddcac : decode_any W_ddcac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcb0 : bv 32 := 0x00889393.
Lemma F_ddcb0 : fetch_word AsanUbsan.M.loaded_segments (0xddc64 : word) = Some W_ddcb0.
Proof. vm_refl. Qed.
Lemma D_ddcb0 : decode_any W_ddcb0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcb4 : bv 32 := 0x0188d89b.
Lemma F_ddcb4 : fetch_word AsanUbsan.M.loaded_segments (0xddc68 : word) = Some W_ddcb4.
Proof. vm_refl. Qed.
Lemma D_ddcb4 : decode_any W_ddcb4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcb8 : bv 32 := 0x0103e833.
Lemma F_ddcb8 : fetch_word AsanUbsan.M.loaded_segments (0xddc6c : word) = Some W_ddcb8.
Proof. vm_refl. Qed.
Lemma D_ddcb8 : decode_any W_ddcb8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcbc : bv 32 := 0x00829393.
Lemma F_ddcbc : fetch_word AsanUbsan.M.loaded_segments (0xddc70 : word) = Some W_ddcbc.
Proof. vm_refl. Qed.
Lemma D_ddcbc : decode_any W_ddcbc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcc0 : bv 32 := 0x0182d29b.
Lemma F_ddcc0 : fetch_word AsanUbsan.M.loaded_segments (0xddc74 : word) = Some W_ddcc0.
Proof. vm_refl. Qed.
Lemma D_ddcc0 : decode_any W_ddcc0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcc4 : bv 32 := 0x0113e8b3.
Lemma F_ddcc4 : fetch_word AsanUbsan.M.loaded_segments (0xddc78 : word) = Some W_ddcc4.
Proof. vm_refl. Qed.
Lemma D_ddcc4 : decode_any W_ddcc4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcc8 : bv 32 := 0x00831393.
Lemma F_ddcc8 : fetch_word AsanUbsan.M.loaded_segments (0xddc7c : word) = Some W_ddcc8.
Proof. vm_refl. Qed.
Lemma D_ddcc8 : decode_any W_ddcc8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddccc : bv 32 := 0x0183531b.
Lemma F_ddccc : fetch_word AsanUbsan.M.loaded_segments (0xddc80 : word) = Some W_ddccc.
Proof. vm_refl. Qed.
Lemma D_ddccc : decode_any W_ddccc = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcd0 : bv 32 := 0x0053e2b3.
Lemma F_ddcd0 : fetch_word AsanUbsan.M.loaded_segments (0xddc84 : word) = Some W_ddcd0.
Proof. vm_refl. Qed.
Lemma D_ddcd0 : decode_any W_ddcd0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcd4 : bv 32 := 0x00871393.
Lemma F_ddcd4 : fetch_word AsanUbsan.M.loaded_segments (0xddc88 : word) = Some W_ddcd4.
Proof. vm_refl. Qed.
Lemma D_ddcd4 : decode_any W_ddcd4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcd8 : bv 32 := 0x0063e333.
Lemma F_ddcd8 : fetch_word AsanUbsan.M.loaded_segments (0xddc8c : word) = Some W_ddcd8.
Proof. vm_refl. Qed.
Lemma D_ddcd8 : decode_any W_ddcd8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcdc : bv 32 := 0xff060613.
Lemma F_ddcdc : fetch_word AsanUbsan.M.loaded_segments (0xddc90 : word) = Some W_ddcdc.
Proof. vm_refl. Qed.
Lemma D_ddcdc : decode_any W_ddcdc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddce0 : bv 32 := 0x0106a023.
Lemma F_ddce0 : fetch_word AsanUbsan.M.loaded_segments (0xddc94 : word) = Some W_ddce0.
Proof. vm_refl. Qed.
Lemma D_ddce0 : decode_any W_ddce0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddce4 : bv 32 := 0x0116a223.
Lemma F_ddce4 : fetch_word AsanUbsan.M.loaded_segments (0xddc98 : word) = Some W_ddce4.
Proof. vm_refl. Qed.
Lemma D_ddce4 : decode_any W_ddce4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddce8 : bv 32 := 0x0056a423.
Lemma F_ddce8 : fetch_word AsanUbsan.M.loaded_segments (0xddc9c : word) = Some W_ddce8.
Proof. vm_refl. Qed.
Lemma D_ddce8 : decode_any W_ddce8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcec : bv 32 := 0x0066a623.
Lemma F_ddcec : fetch_word AsanUbsan.M.loaded_segments (0xddca0 : word) = Some W_ddcec.
Proof. vm_refl. Qed.
Lemma D_ddcec : decode_any W_ddcec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcf0 : bv 32 := 0x01068693.
Lemma F_ddcf0 : fetch_word AsanUbsan.M.loaded_segments (0xddca4 : word) = Some W_ddcf0.
Proof. vm_refl. Qed.
Lemma D_ddcf0 : decode_any W_ddcf0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcf4 : bv 32 := 0x01058593.
Lemma F_ddcf4 : fetch_word AsanUbsan.M.loaded_segments (0xddca8 : word) = Some W_ddcf4.
Proof. vm_refl. Qed.
Lemma D_ddcf4 : decode_any W_ddcf4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcf8 : bv 32 := 0xfac7e2e3.
Lemma F_ddcf8 : fetch_word AsanUbsan.M.loaded_segments (0xddcac : word) = Some W_ddcf8.
Proof. vm_refl. Qed.
Lemma D_ddcf8 : decode_any W_ddcf8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddcfc : bv 32 := 0xff358593.
Lemma F_ddcfc : fetch_word AsanUbsan.M.loaded_segments (0xddcb0 : word) = Some W_ddcfc.
Proof. vm_refl. Qed.
Lemma D_ddcfc : decode_any W_ddcfc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd00 : bv 32 := 0x01000713.
Lemma F_ddd00 : fetch_word AsanUbsan.M.loaded_segments (0xddcb4 : word) = Some W_ddd00.
Proof. vm_refl. Qed.
Lemma D_ddd00 : decode_any W_ddd00 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd04 : bv 32 := 0xdae66ce3.
Lemma F_ddd04 : fetch_word AsanUbsan.M.loaded_segments (0xddcb8 : word) = Some W_ddd04.
Proof. vm_refl. Qed.
Lemma D_ddd04 : decode_any W_ddd04 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd08 : bv 32 := 0x0005c703.
Lemma F_ddd08 : fetch_word AsanUbsan.M.loaded_segments (0xddcbc : word) = Some W_ddd08.
Proof. vm_refl. Qed.
Lemma D_ddd08 : decode_any W_ddd08 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd0c : bv 32 := 0x0015c783.
Lemma F_ddd0c : fetch_word AsanUbsan.M.loaded_segments (0xddcc0 : word) = Some W_ddd0c.
Proof. vm_refl. Qed.
Lemma D_ddd0c : decode_any W_ddd0c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd10 : bv 32 := 0x0025c803.
Lemma F_ddd10 : fetch_word AsanUbsan.M.loaded_segments (0xddcc4 : word) = Some W_ddd10.
Proof. vm_refl. Qed.
Lemma D_ddd10 : decode_any W_ddd10 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd14 : bv 32 := 0x0035c883.
Lemma F_ddd14 : fetch_word AsanUbsan.M.loaded_segments (0xddcc8 : word) = Some W_ddd14.
Proof. vm_refl. Qed.
Lemma D_ddd14 : decode_any W_ddd14 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd18 : bv 32 := 0x0045c283.
Lemma F_ddd18 : fetch_word AsanUbsan.M.loaded_segments (0xddccc : word) = Some W_ddd18.
Proof. vm_refl. Qed.
Lemma D_ddd18 : decode_any W_ddd18 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd1c : bv 32 := 0x0055c303.
Lemma F_ddd1c : fetch_word AsanUbsan.M.loaded_segments (0xddcd0 : word) = Some W_ddd1c.
Proof. vm_refl. Qed.
Lemma D_ddd1c : decode_any W_ddd1c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd20 : bv 32 := 0x0065c383.
Lemma F_ddd20 : fetch_word AsanUbsan.M.loaded_segments (0xddcd4 : word) = Some W_ddd20.
Proof. vm_refl. Qed.
Lemma D_ddd20 : decode_any W_ddd20 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd24 : bv 32 := 0x0075ce03.
Lemma F_ddd24 : fetch_word AsanUbsan.M.loaded_segments (0xddcd8 : word) = Some W_ddd24.
Proof. vm_refl. Qed.
Lemma D_ddd24 : decode_any W_ddd24 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd28 : bv 32 := 0x00e68023.
Lemma F_ddd28 : fetch_word AsanUbsan.M.loaded_segments (0xddcdc : word) = Some W_ddd28.
Proof. vm_refl. Qed.
Lemma D_ddd28 : decode_any W_ddd28 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd2c : bv 32 := 0x00f680a3.
Lemma F_ddd2c : fetch_word AsanUbsan.M.loaded_segments (0xddce0 : word) = Some W_ddd2c.
Proof. vm_refl. Qed.
Lemma D_ddd2c : decode_any W_ddd2c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd30 : bv 32 := 0x01068123.
Lemma F_ddd30 : fetch_word AsanUbsan.M.loaded_segments (0xddce4 : word) = Some W_ddd30.
Proof. vm_refl. Qed.
Lemma D_ddd30 : decode_any W_ddd30 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd34 : bv 32 := 0x011681a3.
Lemma F_ddd34 : fetch_word AsanUbsan.M.loaded_segments (0xddce8 : word) = Some W_ddd34.
Proof. vm_refl. Qed.
Lemma D_ddd34 : decode_any W_ddd34 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd38 : bv 32 := 0x0085c703.
Lemma F_ddd38 : fetch_word AsanUbsan.M.loaded_segments (0xddcec : word) = Some W_ddd38.
Proof. vm_refl. Qed.
Lemma D_ddd38 : decode_any W_ddd38 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd3c : bv 32 := 0x0095c783.
Lemma F_ddd3c : fetch_word AsanUbsan.M.loaded_segments (0xddcf0 : word) = Some W_ddd3c.
Proof. vm_refl. Qed.
Lemma D_ddd3c : decode_any W_ddd3c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd40 : bv 32 := 0x00a5c803.
Lemma F_ddd40 : fetch_word AsanUbsan.M.loaded_segments (0xddcf4 : word) = Some W_ddd40.
Proof. vm_refl. Qed.
Lemma D_ddd40 : decode_any W_ddd40 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd44 : bv 32 := 0x00b5c883.
Lemma F_ddd44 : fetch_word AsanUbsan.M.loaded_segments (0xddcf8 : word) = Some W_ddd44.
Proof. vm_refl. Qed.
Lemma D_ddd44 : decode_any W_ddd44 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd48 : bv 32 := 0x00568223.
Lemma F_ddd48 : fetch_word AsanUbsan.M.loaded_segments (0xddcfc : word) = Some W_ddd48.
Proof. vm_refl. Qed.
Lemma D_ddd48 : decode_any W_ddd48 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd4c : bv 32 := 0x006682a3.
Lemma F_ddd4c : fetch_word AsanUbsan.M.loaded_segments (0xddd00 : word) = Some W_ddd4c.
Proof. vm_refl. Qed.
Lemma D_ddd4c : decode_any W_ddd4c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd50 : bv 32 := 0x00768323.
Lemma F_ddd50 : fetch_word AsanUbsan.M.loaded_segments (0xddd04 : word) = Some W_ddd50.
Proof. vm_refl. Qed.
Lemma D_ddd50 : decode_any W_ddd50 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd54 : bv 32 := 0x01c683a3.
Lemma F_ddd54 : fetch_word AsanUbsan.M.loaded_segments (0xddd08 : word) = Some W_ddd54.
Proof. vm_refl. Qed.
Lemma D_ddd54 : decode_any W_ddd54 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd58 : bv 32 := 0x00c5c283.
Lemma F_ddd58 : fetch_word AsanUbsan.M.loaded_segments (0xddd0c : word) = Some W_ddd58.
Proof. vm_refl. Qed.
Lemma D_ddd58 : decode_any W_ddd58 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd5c : bv 32 := 0x00d5c303.
Lemma F_ddd5c : fetch_word AsanUbsan.M.loaded_segments (0xddd10 : word) = Some W_ddd5c.
Proof. vm_refl. Qed.
Lemma D_ddd5c : decode_any W_ddd5c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd60 : bv 32 := 0x00e5c383.
Lemma F_ddd60 : fetch_word AsanUbsan.M.loaded_segments (0xddd14 : word) = Some W_ddd60.
Proof. vm_refl. Qed.
Lemma D_ddd60 : decode_any W_ddd60 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd64 : bv 32 := 0x00f5ce03.
Lemma F_ddd64 : fetch_word AsanUbsan.M.loaded_segments (0xddd18 : word) = Some W_ddd64.
Proof. vm_refl. Qed.
Lemma D_ddd64 : decode_any W_ddd64 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd68 : bv 32 := 0x01058593.
Lemma F_ddd68 : fetch_word AsanUbsan.M.loaded_segments (0xddd1c : word) = Some W_ddd68.
Proof. vm_refl. Qed.
Lemma D_ddd68 : decode_any W_ddd68 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd6c : bv 32 := 0x00e68423.
Lemma F_ddd6c : fetch_word AsanUbsan.M.loaded_segments (0xddd20 : word) = Some W_ddd6c.
Proof. vm_refl. Qed.
Lemma D_ddd6c : decode_any W_ddd6c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd70 : bv 32 := 0x00f684a3.
Lemma F_ddd70 : fetch_word AsanUbsan.M.loaded_segments (0xddd24 : word) = Some W_ddd70.
Proof. vm_refl. Qed.
Lemma D_ddd70 : decode_any W_ddd70 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd74 : bv 32 := 0x01068523.
Lemma F_ddd74 : fetch_word AsanUbsan.M.loaded_segments (0xddd28 : word) = Some W_ddd74.
Proof. vm_refl. Qed.
Lemma D_ddd74 : decode_any W_ddd74 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd78 : bv 32 := 0x011685a3.
Lemma F_ddd78 : fetch_word AsanUbsan.M.loaded_segments (0xddd2c : word) = Some W_ddd78.
Proof. vm_refl. Qed.
Lemma D_ddd78 : decode_any W_ddd78 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd7c : bv 32 := 0x01068713.
Lemma F_ddd7c : fetch_word AsanUbsan.M.loaded_segments (0xddd30 : word) = Some W_ddd7c.
Proof. vm_refl. Qed.
Lemma D_ddd7c : decode_any W_ddd7c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd80 : bv 32 := 0x00568623.
Lemma F_ddd80 : fetch_word AsanUbsan.M.loaded_segments (0xddd34 : word) = Some W_ddd80.
Proof. vm_refl. Qed.
Lemma D_ddd80 : decode_any W_ddd80 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd84 : bv 32 := 0x006686a3.
Lemma F_ddd84 : fetch_word AsanUbsan.M.loaded_segments (0xddd38 : word) = Some W_ddd84.
Proof. vm_refl. Qed.
Lemma D_ddd84 : decode_any W_ddd84 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd88 : bv 32 := 0x00768723.
Lemma F_ddd88 : fetch_word AsanUbsan.M.loaded_segments (0xddd3c : word) = Some W_ddd88.
Proof. vm_refl. Qed.
Lemma D_ddd88 : decode_any W_ddd88 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd8c : bv 32 := 0x01c687a3.
Lemma F_ddd8c : fetch_word AsanUbsan.M.loaded_segments (0xddd40 : word) = Some W_ddd8c.
Proof. vm_refl. Qed.
Lemma D_ddd8c : decode_any W_ddd8c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd90 : bv 32 := 0x00070693.
Lemma F_ddd90 : fetch_word AsanUbsan.M.loaded_segments (0xddd44 : word) = Some W_ddd90.
Proof. vm_refl. Qed.
Lemma D_ddd90 : decode_any W_ddd90 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd94 : bv 32 := 0x00867713.
Lemma F_ddd94 : fetch_word AsanUbsan.M.loaded_segments (0xddd48 : word) = Some W_ddd94.
Proof. vm_refl. Qed.
Lemma D_ddd94 : decode_any W_ddd94 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd98 : bv 32 := 0xd20706e3.
Lemma F_ddd98 : fetch_word AsanUbsan.M.loaded_segments (0xddd4c : word) = Some W_ddd98.
Proof. vm_refl. Qed.
Lemma D_ddd98 : decode_any W_ddd98 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddd9c : bv 32 := 0x0005c703.
Lemma F_ddd9c : fetch_word AsanUbsan.M.loaded_segments (0xddd50 : word) = Some W_ddd9c.
Proof. vm_refl. Qed.
Lemma D_ddd9c : decode_any W_ddd9c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddda0 : bv 32 := 0x0015c783.
Lemma F_ddda0 : fetch_word AsanUbsan.M.loaded_segments (0xddd54 : word) = Some W_ddda0.
Proof. vm_refl. Qed.
Lemma D_ddda0 : decode_any W_ddda0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddda4 : bv 32 := 0x0025c803.
Lemma F_ddda4 : fetch_word AsanUbsan.M.loaded_segments (0xddd58 : word) = Some W_ddda4.
Proof. vm_refl. Qed.
Lemma D_ddda4 : decode_any W_ddda4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddda8 : bv 32 := 0x0035c883.
Lemma F_ddda8 : fetch_word AsanUbsan.M.loaded_segments (0xddd5c : word) = Some W_ddda8.
Proof. vm_refl. Qed.
Lemma D_ddda8 : decode_any W_ddda8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddac : bv 32 := 0x0045c283.
Lemma F_dddac : fetch_word AsanUbsan.M.loaded_segments (0xddd60 : word) = Some W_dddac.
Proof. vm_refl. Qed.
Lemma D_dddac : decode_any W_dddac = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddb0 : bv 32 := 0x0055c303.
Lemma F_dddb0 : fetch_word AsanUbsan.M.loaded_segments (0xddd64 : word) = Some W_dddb0.
Proof. vm_refl. Qed.
Lemma D_dddb0 : decode_any W_dddb0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddb4 : bv 32 := 0x0065c383.
Lemma F_dddb4 : fetch_word AsanUbsan.M.loaded_segments (0xddd68 : word) = Some W_dddb4.
Proof. vm_refl. Qed.
Lemma D_dddb4 : decode_any W_dddb4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddb8 : bv 32 := 0x0075ce03.
Lemma F_dddb8 : fetch_word AsanUbsan.M.loaded_segments (0xddd6c : word) = Some W_dddb8.
Proof. vm_refl. Qed.
Lemma D_dddb8 : decode_any W_dddb8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddbc : bv 32 := 0x00858593.
Lemma F_dddbc : fetch_word AsanUbsan.M.loaded_segments (0xddd70 : word) = Some W_dddbc.
Proof. vm_refl. Qed.
Lemma D_dddbc : decode_any W_dddbc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddc0 : bv 32 := 0x00e68023.
Lemma F_dddc0 : fetch_word AsanUbsan.M.loaded_segments (0xddd74 : word) = Some W_dddc0.
Proof. vm_refl. Qed.
Lemma D_dddc0 : decode_any W_dddc0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddc4 : bv 32 := 0x00f680a3.
Lemma F_dddc4 : fetch_word AsanUbsan.M.loaded_segments (0xddd78 : word) = Some W_dddc4.
Proof. vm_refl. Qed.
Lemma D_dddc4 : decode_any W_dddc4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddc8 : bv 32 := 0x01068123.
Lemma F_dddc8 : fetch_word AsanUbsan.M.loaded_segments (0xddd7c : word) = Some W_dddc8.
Proof. vm_refl. Qed.
Lemma D_dddc8 : decode_any W_dddc8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddcc : bv 32 := 0x011681a3.
Lemma F_dddcc : fetch_word AsanUbsan.M.loaded_segments (0xddd80 : word) = Some W_dddcc.
Proof. vm_refl. Qed.
Lemma D_dddcc : decode_any W_dddcc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddd0 : bv 32 := 0x00868713.
Lemma F_dddd0 : fetch_word AsanUbsan.M.loaded_segments (0xddd84 : word) = Some W_dddd0.
Proof. vm_refl. Qed.
Lemma D_dddd0 : decode_any W_dddd0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddd4 : bv 32 := 0x00568223.
Lemma F_dddd4 : fetch_word AsanUbsan.M.loaded_segments (0xddd88 : word) = Some W_dddd4.
Proof. vm_refl. Qed.
Lemma D_dddd4 : decode_any W_dddd4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddd8 : bv 32 := 0x006682a3.
Lemma F_dddd8 : fetch_word AsanUbsan.M.loaded_segments (0xddd8c : word) = Some W_dddd8.
Proof. vm_refl. Qed.
Lemma D_dddd8 : decode_any W_dddd8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddddc : bv 32 := 0x00768323.
Lemma F_ddddc : fetch_word AsanUbsan.M.loaded_segments (0xddd90 : word) = Some W_ddddc.
Proof. vm_refl. Qed.
Lemma D_ddddc : decode_any W_ddddc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddde0 : bv 32 := 0x01c683a3.
Lemma F_ddde0 : fetch_word AsanUbsan.M.loaded_segments (0xddd94 : word) = Some W_ddde0.
Proof. vm_refl. Qed.
Lemma D_ddde0 : decode_any W_ddde0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddde4 : bv 32 := 0x00070693.
Lemma F_ddde4 : fetch_word AsanUbsan.M.loaded_segments (0xddd98 : word) = Some W_ddde4.
Proof. vm_refl. Qed.
Lemma D_ddde4 : decode_any W_ddde4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ddde8 : bv 32 := 0x00467713.
Lemma F_ddde8 : fetch_word AsanUbsan.M.loaded_segments (0xddd9c : word) = Some W_ddde8.
Proof. vm_refl. Qed.
Lemma D_ddde8 : decode_any W_ddde8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddec : bv 32 := 0x02070863.
Lemma F_dddec : fetch_word AsanUbsan.M.loaded_segments (0xddda0 : word) = Some W_dddec.
Proof. vm_refl. Qed.
Lemma D_dddec : decode_any W_dddec = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddf0 : bv 32 := 0x0005c703.
Lemma F_dddf0 : fetch_word AsanUbsan.M.loaded_segments (0xddda4 : word) = Some W_dddf0.
Proof. vm_refl. Qed.
Lemma D_dddf0 : decode_any W_dddf0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddf4 : bv 32 := 0x0015c783.
Lemma F_dddf4 : fetch_word AsanUbsan.M.loaded_segments (0xddda8 : word) = Some W_dddf4.
Proof. vm_refl. Qed.
Lemma D_dddf4 : decode_any W_dddf4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddf8 : bv 32 := 0x0025c803.
Lemma F_dddf8 : fetch_word AsanUbsan.M.loaded_segments (0xdddac : word) = Some W_dddf8.
Proof. vm_refl. Qed.
Lemma D_dddf8 : decode_any W_dddf8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dddfc : bv 32 := 0x0035c883.
Lemma F_dddfc : fetch_word AsanUbsan.M.loaded_segments (0xdddb0 : word) = Some W_dddfc.
Proof. vm_refl. Qed.
Lemma D_dddfc : decode_any W_dddfc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde00 : bv 32 := 0x00458593.
Lemma F_dde00 : fetch_word AsanUbsan.M.loaded_segments (0xdddb4 : word) = Some W_dde00.
Proof. vm_refl. Qed.
Lemma D_dde00 : decode_any W_dde00 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde04 : bv 32 := 0x00468293.
Lemma F_dde04 : fetch_word AsanUbsan.M.loaded_segments (0xdddb8 : word) = Some W_dde04.
Proof. vm_refl. Qed.
Lemma D_dde04 : decode_any W_dde04 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde08 : bv 32 := 0x00e68023.
Lemma F_dde08 : fetch_word AsanUbsan.M.loaded_segments (0xdddbc : word) = Some W_dde08.
Proof. vm_refl. Qed.
Lemma D_dde08 : decode_any W_dde08 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde0c : bv 32 := 0x00f680a3.
Lemma F_dde0c : fetch_word AsanUbsan.M.loaded_segments (0xdddc0 : word) = Some W_dde0c.
Proof. vm_refl. Qed.
Lemma D_dde0c : decode_any W_dde0c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde10 : bv 32 := 0x01068123.
Lemma F_dde10 : fetch_word AsanUbsan.M.loaded_segments (0xdddc4 : word) = Some W_dde10.
Proof. vm_refl. Qed.
Lemma D_dde10 : decode_any W_dde10 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde14 : bv 32 := 0x011681a3.
Lemma F_dde14 : fetch_word AsanUbsan.M.loaded_segments (0xdddc8 : word) = Some W_dde14.
Proof. vm_refl. Qed.
Lemma D_dde14 : decode_any W_dde14 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde18 : bv 32 := 0x00028693.
Lemma F_dde18 : fetch_word AsanUbsan.M.loaded_segments (0xdddcc : word) = Some W_dde18.
Proof. vm_refl. Qed.
Lemma D_dde18 : decode_any W_dde18 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde1c : bv 32 := 0x00267713.
Lemma F_dde1c : fetch_word AsanUbsan.M.loaded_segments (0xdddd0 : word) = Some W_dde1c.
Proof. vm_refl. Qed.
Lemma D_dde1c : decode_any W_dde1c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde20 : bv 32 := 0x00071863.
Lemma F_dde20 : fetch_word AsanUbsan.M.loaded_segments (0xdddd4 : word) = Some W_dde20.
Proof. vm_refl. Qed.
Lemma D_dde20 : decode_any W_dde20 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde24 : bv 32 := 0x00167613.
Lemma F_dde24 : fetch_word AsanUbsan.M.loaded_segments (0xdddd8 : word) = Some W_dde24.
Proof. vm_refl. Qed.
Lemma D_dde24 : decode_any W_dde24 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde28 : bv 32 := 0x02061663.
Lemma F_dde28 : fetch_word AsanUbsan.M.loaded_segments (0xddddc : word) = Some W_dde28.
Proof. vm_refl. Qed.
Lemma D_dde28 : decode_any W_dde28 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde2c : bv 32 := 0x00008067.
Lemma F_dde2c : fetch_word AsanUbsan.M.loaded_segments (0xddde0 : word) = Some W_dde2c.
Proof. vm_refl. Qed.
Lemma D_dde2c : decode_any W_dde2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde30 : bv 32 := 0x0005c703.
Lemma F_dde30 : fetch_word AsanUbsan.M.loaded_segments (0xddde4 : word) = Some W_dde30.
Proof. vm_refl. Qed.
Lemma D_dde30 : decode_any W_dde30 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde34 : bv 32 := 0x0015c783.
Lemma F_dde34 : fetch_word AsanUbsan.M.loaded_segments (0xddde8 : word) = Some W_dde34.
Proof. vm_refl. Qed.
Lemma D_dde34 : decode_any W_dde34 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde38 : bv 32 := 0x00258593.
Lemma F_dde38 : fetch_word AsanUbsan.M.loaded_segments (0xdddec : word) = Some W_dde38.
Proof. vm_refl. Qed.
Lemma D_dde38 : decode_any W_dde38 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde3c : bv 32 := 0x00268813.
Lemma F_dde3c : fetch_word AsanUbsan.M.loaded_segments (0xdddf0 : word) = Some W_dde3c.
Proof. vm_refl. Qed.
Lemma D_dde3c : decode_any W_dde3c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde40 : bv 32 := 0x00e68023.
Lemma F_dde40 : fetch_word AsanUbsan.M.loaded_segments (0xdddf4 : word) = Some W_dde40.
Proof. vm_refl. Qed.
Lemma D_dde40 : decode_any W_dde40 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde44 : bv 32 := 0x00f680a3.
Lemma F_dde44 : fetch_word AsanUbsan.M.loaded_segments (0xdddf8 : word) = Some W_dde44.
Proof. vm_refl. Qed.
Lemma D_dde44 : decode_any W_dde44 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde48 : bv 32 := 0x00080693.
Lemma F_dde48 : fetch_word AsanUbsan.M.loaded_segments (0xdddfc : word) = Some W_dde48.
Proof. vm_refl. Qed.
Lemma D_dde48 : decode_any W_dde48 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde4c : bv 32 := 0x00167613.
Lemma F_dde4c : fetch_word AsanUbsan.M.loaded_segments (0xdde00 : word) = Some W_dde4c.
Proof. vm_refl. Qed.
Lemma D_dde4c : decode_any W_dde4c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde50 : bv 32 := 0xfc060ee3.
Lemma F_dde50 : fetch_word AsanUbsan.M.loaded_segments (0xdde04 : word) = Some W_dde50.
Proof. vm_refl. Qed.
Lemma D_dde50 : decode_any W_dde50 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde54 : bv 32 := 0x0005c583.
Lemma F_dde54 : fetch_word AsanUbsan.M.loaded_segments (0xdde08 : word) = Some W_dde54.
Proof. vm_refl. Qed.
Lemma D_dde54 : decode_any W_dde54 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde58 : bv 32 := 0x00b68023.
Lemma F_dde58 : fetch_word AsanUbsan.M.loaded_segments (0xdde0c : word) = Some W_dde58.
Proof. vm_refl. Qed.
Lemma D_dde58 : decode_any W_dde58 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_dde5c : bv 32 := 0x00008067.
Lemma F_dde5c : fetch_word AsanUbsan.M.loaded_segments (0xdde10 : word) = Some W_dde5c.
Proof. vm_refl. Qed.
Lemma D_dde5c : decode_any W_dde5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_ce3d0 : bv 32 := 0x0004b503.
Lemma F_ce3d0 : fetch_word AsanUbsan.M.loaded_segments (0xce390 : word) = Some W_ce3d0.
Proof. vm_refl. Qed.
Lemma D_ce3d0 : decode_any W_ce3d0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce3d4 : bv 32 := 0x00848493.
Lemma F_ce3d4 : fetch_word AsanUbsan.M.loaded_segments (0xce394 : word) = Some W_ce3d4.
Proof. vm_refl. Qed.
Lemma D_ce3d4 : decode_any W_ce3d4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce3d8 : bv 32 := 0xfe051ce3.
Lemma F_ce3d8 : fetch_word AsanUbsan.M.loaded_segments (0xce398 : word) = Some W_ce3d8.
Proof. vm_refl. Qed.
Lemma D_ce3d8 : decode_any W_ce3d8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce48c : bv 32 := 0x00b53023.
Lemma F_ce48c : fetch_word AsanUbsan.M.loaded_segments (0xce44c : word) = Some W_ce48c.
Proof. vm_refl. Qed.
Lemma D_ce48c : decode_any W_ce48c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce490 : bv 32 := 0x00158593.
Lemma F_ce490 : fetch_word AsanUbsan.M.loaded_segments (0xce450 : word) = Some W_ce490.
Proof. vm_refl. Qed.
Lemma D_ce490 : decode_any W_ce490 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce494 : bv 32 := 0xfff5c683.
Lemma F_ce494 : fetch_word AsanUbsan.M.loaded_segments (0xce454 : word) = Some W_ce494.
Proof. vm_refl. Qed.
Lemma D_ce494 : decode_any W_ce494 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce498 : bv 32 := 0xfec68ae3.
Lemma F_ce498 : fetch_word AsanUbsan.M.loaded_segments (0xce458 : word) = Some W_ce498.
Proof. vm_refl. Qed.
Lemma D_ce498 : decode_any W_ce498 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce49c : bv 32 := 0xfe069ae3.
Lemma F_ce49c : fetch_word AsanUbsan.M.loaded_segments (0xce45c : word) = Some W_ce49c.
Proof. vm_refl. Qed.
Lemma D_ce49c : decode_any W_ce49c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_757b4 : bv 32 := 0x06060663.
Lemma D_757b4 : decode_any W_757b4 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_757b8 : bv 32 := 0x00000693.
Lemma D_757b8 : decode_any W_757b8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_757bc : bv 32 := 0x00d58733.
Lemma D_757bc : decode_any W_757bc = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_757c0 : bv 32 := 0x00074703.
Lemma D_757c0 : decode_any W_757c0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_757c4 : bv 32 := 0x00070c63.
Lemma D_757c4 : decode_any W_757c4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_757c8 : bv 32 := 0x00d507b3.
Lemma D_757c8 : decode_any W_757c8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_757cc : bv 32 := 0x00168693.
Lemma D_757cc : decode_any W_757cc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_757d0 : bv 32 := 0x00e78023.
Lemma D_757d0 : decode_any W_757d0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_757d4 : bv 32 := 0xfed614e3.
Lemma D_757d4 : decode_any W_757d4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_757d8 : bv 32 := 0x00060693.

Definition W_757dc : bv 32 := 0x00d505b3.
Lemma D_757dc : decode_any W_757dc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_757e0 : bv 32 := 0x40d6073b.
Lemma D_757e0 : decode_any W_757e0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_757e4 : bv 32 := 0x00b76733.
Lemma D_757e4 : decode_any W_757e4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_757e8 : bv 32 := 0x00f77713.
Lemma D_757e8 : decode_any W_757e8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_757ec : bv 32 := 0x00070e63.
Lemma D_757ec : decode_any W_757ec = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_757f0 : bv 32 := 0x02d60863.
Lemma D_757f0 : decode_any W_757f0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_757f4 : bv 32 := 0x00c50633.
Lemma D_757f4 : decode_any W_757f4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_757f8 : bv 32 := 0x00058023.
Lemma D_757f8 : decode_any W_757f8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_757fc : bv 32 := 0x00158593.
Lemma D_757fc : decode_any W_757fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75800 : bv 32 := 0xfec59ce3.
Lemma D_75800 : decode_any W_75800 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_75804 : bv 32 := 0x01c0006f.
Lemma D_75804 : decode_any W_75804 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_75808 : bv 32 := 0x00d60c63.

Definition W_7580c : bv 32 := 0x00c50633.

Definition W_75810 : bv 32 := 0x0005b023.

Definition W_75814 : bv 32 := 0x0005b423.

Definition W_75818 : bv 32 := 0x01058593.

Definition W_7581c : bv 32 := 0xfec5eae3.

Definition W_75820 : bv 32 := 0x00008067.
Lemma D_75820 : decode_any W_75820 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61534 : bv 32 := 0x00200613.

Definition W_61538 : bv 32 := 0x14c5ea63.

Definition W_6153c : bv 32 := 0x00100613.

Definition W_61540 : bv 32 := 0x00100693.

Definition W_61544 : bv 32 := 0x00c0006f.

Definition W_61548 : bv 32 := 0x00160613.

Definition W_6154c : bv 32 := 0x12b60c63.

Definition W_61550 : bv 32 := 0x00461713.

Definition W_61554 : bv 32 := 0x00e50733.

Definition W_61558 : bv 32 := 0x00072703.

Definition W_6155c : bv 32 := 0x00060893.

Definition W_61560 : bv 32 := 0xfff88793.

Definition W_61564 : bv 32 := 0x0017d813.

Definition W_61568 : bv 32 := 0x00481293.

Definition W_6156c : bv 32 := 0x005502b3.

Definition W_61570 : bv 32 := 0x0002a303.

Definition W_61574 : bv 32 := 0xfce37ae3.

Definition W_61578 : bv 32 := 0x0002b303.

Definition W_6157c : bv 32 := 0x00489893.

Definition W_61580 : bv 32 := 0x011508b3.

Definition W_61584 : bv 32 := 0x0048a383.

Definition W_61588 : bv 32 := 0x0068b023.

Definition W_6158c : bv 32 := 0x0082b303.

Definition W_61590 : bv 32 := 0x0088be03.

Definition W_61594 : bv 32 := 0x0068b423.

Definition W_61598 : bv 32 := 0x00e2a023.

Definition W_6159c : bv 32 := 0x0072a223.

Definition W_615a0 : bv 32 := 0x01c2b423.

Definition W_615a4 : bv 32 := 0x00080893.

Definition W_615a8 : bv 32 := 0xfaf6ece3.

Definition W_615ac : bv 32 := 0xf9dff06f.

Definition W_615b0 : bv 32 := 0x00000613.

Definition W_615b4 : bv 32 := 0x00459693.

Definition W_615b8 : bv 32 := 0x00d506b3.

Definition W_615bc : bv 32 := 0x0006b703.

Definition W_615c0 : bv 32 := 0x0086b783.

Definition W_615c4 : bv 32 := 0x00053803.

Definition W_615c8 : bv 32 := 0x00853883.

Definition W_615cc : bv 32 := 0x00e53023.

Definition W_615d0 : bv 32 := 0x00f53423.

Definition W_615d4 : bv 32 := 0x0106b023.

Definition W_615d8 : bv 32 := 0x0116b423.

Definition W_615dc : bv 32 := 0x00000693.

Definition W_615e0 : bv 32 := 0x00161793.

Definition W_615e4 : bv 32 := 0x00178813.

Definition W_615e8 : bv 32 := 0x00461713.

Definition W_615ec : bv 32 := 0x00b86a63.

Definition W_615f0 : bv 32 := 0x00278793.

Definition W_615f4 : bv 32 := 0x02b7ea63.

Definition W_615f8 : bv 32 := 0x04c69c63.

Definition W_615fc : bv 32 := 0x0880006f.

Definition W_61600 : bv 32 := 0x00e506b3.

Definition W_61604 : bv 32 := 0x00481893.

Definition W_61608 : bv 32 := 0x011508b3.

Definition W_6160c : bv 32 := 0x0006a683.

Definition W_61610 : bv 32 := 0x0008a883.

Definition W_61614 : bv 32 := 0x0116e463.

Definition W_61618 : bv 32 := 0x00060813.

Definition W_6161c : bv 32 := 0x00080693.

Definition W_61620 : bv 32 := 0x00278793.

Definition W_61624 : bv 32 := 0xfcb7fae3.

Definition W_61628 : bv 32 := 0x00469813.

Definition W_6162c : bv 32 := 0x00479893.

Definition W_61630 : bv 32 := 0x01050833.

Definition W_61634 : bv 32 := 0x011508b3.

Definition W_61638 : bv 32 := 0x00082803.

Definition W_6163c : bv 32 := 0x0008a883.

Definition W_61640 : bv 32 := 0x01186463.

Definition W_61644 : bv 32 := 0x00068793.

Definition W_61648 : bv 32 := 0x00078693.

Definition W_6164c : bv 32 := 0x02c78c63.

Definition W_61650 : bv 32 := 0x00469613.

Definition W_61654 : bv 32 := 0x00c50633.

Definition W_61658 : bv 32 := 0x00063783.

Definition W_6165c : bv 32 := 0x00e50733.

Definition W_61660 : bv 32 := 0x00073803.

Definition W_61664 : bv 32 := 0x00873883.

Definition W_61668 : bv 32 := 0x00f73023.

Definition W_6166c : bv 32 := 0x00863783.

Definition W_61670 : bv 32 := 0x00f73423.

Definition W_61674 : bv 32 := 0x01063023.

Definition W_61678 : bv 32 := 0x01163423.

Definition W_6167c : bv 32 := 0x00068613.

Definition W_61680 : bv 32 := 0xf6b6e0e3.

Definition W_61684 : bv 32 := 0xfff58593.

Definition W_61688 : bv 32 := 0xf20594e3.

Definition W_6168c : bv 32 := 0x00008067.

End Mq6.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_753b4 : bv 32 := 0x06060663.
Lemma D_753b4 : decode_any W_753b4 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_753b8 : bv 32 := 0x00000693.
Lemma D_753b8 : decode_any W_753b8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753bc : bv 32 := 0x00d58733.
Lemma D_753bc : decode_any W_753bc = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_753c0 : bv 32 := 0x00074703.
Lemma D_753c0 : decode_any W_753c0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753c4 : bv 32 := 0x00070c63.
Lemma D_753c4 : decode_any W_753c4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_753c8 : bv 32 := 0x00d507b3.
Lemma D_753c8 : decode_any W_753c8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_753cc : bv 32 := 0x00168693.
Lemma D_753cc : decode_any W_753cc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_753d0 : bv 32 := 0x00e78023.
Lemma D_753d0 : decode_any W_753d0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753d4 : bv 32 := 0xfed614e3.
Lemma D_753d4 : decode_any W_753d4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_753d8 : bv 32 := 0x00060693.

Definition W_753dc : bv 32 := 0x00d505b3.
Lemma D_753dc : decode_any W_753dc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_753e0 : bv 32 := 0x40d6073b.
Lemma D_753e0 : decode_any W_753e0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_753e4 : bv 32 := 0x00b76733.
Lemma D_753e4 : decode_any W_753e4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_753e8 : bv 32 := 0x00f77713.
Lemma D_753e8 : decode_any W_753e8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_753ec : bv 32 := 0x00070e63.
Lemma D_753ec : decode_any W_753ec = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_753f0 : bv 32 := 0x02d60863.
Lemma D_753f0 : decode_any W_753f0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_753f4 : bv 32 := 0x00c50633.
Lemma D_753f4 : decode_any W_753f4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_753f8 : bv 32 := 0x00058023.
Lemma D_753f8 : decode_any W_753f8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_753fc : bv 32 := 0x00158593.
Lemma D_753fc : decode_any W_753fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_75400 : bv 32 := 0xfec59ce3.
Lemma D_75400 : decode_any W_75400 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_75404 : bv 32 := 0x01c0006f.
Lemma D_75404 : decode_any W_75404 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_75408 : bv 32 := 0x00d60c63.

Definition W_7540c : bv 32 := 0x00c50633.

Definition W_75410 : bv 32 := 0x0005b023.

Definition W_75414 : bv 32 := 0x0005b423.

Definition W_75418 : bv 32 := 0x01058593.

Definition W_7541c : bv 32 := 0xfec5eae3.

Definition W_75420 : bv 32 := 0x00008067.
Lemma D_75420 : decode_any W_75420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61134 : bv 32 := 0x00200613.

Definition W_61138 : bv 32 := 0x14c5ea63.

Definition W_6113c : bv 32 := 0x00100613.

Definition W_61140 : bv 32 := 0x00100693.

Definition W_61144 : bv 32 := 0x00c0006f.

Definition W_61148 : bv 32 := 0x00160613.

Definition W_6114c : bv 32 := 0x12b60c63.

Definition W_61150 : bv 32 := 0x00461713.

Definition W_61154 : bv 32 := 0x00e50733.

Definition W_61158 : bv 32 := 0x00072703.

Definition W_6115c : bv 32 := 0x00060893.

Definition W_61160 : bv 32 := 0xfff88793.

Definition W_61164 : bv 32 := 0x0017d813.

Definition W_61168 : bv 32 := 0x00481293.

Definition W_6116c : bv 32 := 0x005502b3.

Definition W_61170 : bv 32 := 0x0002a303.

Definition W_61174 : bv 32 := 0xfce37ae3.

Definition W_61178 : bv 32 := 0x0002b303.

Definition W_6117c : bv 32 := 0x00489893.

Definition W_61180 : bv 32 := 0x011508b3.

Definition W_61184 : bv 32 := 0x0048a383.

Definition W_61188 : bv 32 := 0x0068b023.

Definition W_6118c : bv 32 := 0x0082b303.

Definition W_61190 : bv 32 := 0x0088be03.

Definition W_61194 : bv 32 := 0x0068b423.

Definition W_61198 : bv 32 := 0x00e2a023.

Definition W_6119c : bv 32 := 0x0072a223.

Definition W_611a0 : bv 32 := 0x01c2b423.

Definition W_611a4 : bv 32 := 0x00080893.

Definition W_611a8 : bv 32 := 0xfaf6ece3.

Definition W_611ac : bv 32 := 0xf9dff06f.

Definition W_611b0 : bv 32 := 0x00000613.

Definition W_611b4 : bv 32 := 0x00459693.

Definition W_611b8 : bv 32 := 0x00d506b3.

Definition W_611bc : bv 32 := 0x0006b703.

Definition W_611c0 : bv 32 := 0x0086b783.

Definition W_611c4 : bv 32 := 0x00053803.

Definition W_611c8 : bv 32 := 0x00853883.

Definition W_611cc : bv 32 := 0x00e53023.

Definition W_611d0 : bv 32 := 0x00f53423.

Definition W_611d4 : bv 32 := 0x0106b023.

Definition W_611d8 : bv 32 := 0x0116b423.

Definition W_611dc : bv 32 := 0x00000693.

Definition W_611e0 : bv 32 := 0x00161793.

Definition W_611e4 : bv 32 := 0x00178813.

Definition W_611e8 : bv 32 := 0x00461713.

Definition W_611ec : bv 32 := 0x00b86a63.

Definition W_611f0 : bv 32 := 0x00278793.

Definition W_611f4 : bv 32 := 0x02b7ea63.

Definition W_611f8 : bv 32 := 0x04c69c63.

Definition W_611fc : bv 32 := 0x0880006f.

Definition W_61200 : bv 32 := 0x00e506b3.

Definition W_61204 : bv 32 := 0x00481893.

Definition W_61208 : bv 32 := 0x011508b3.

Definition W_6120c : bv 32 := 0x0006a683.

Definition W_61210 : bv 32 := 0x0008a883.

Definition W_61214 : bv 32 := 0x0116e463.

Definition W_61218 : bv 32 := 0x00060813.

Definition W_6121c : bv 32 := 0x00080693.

Definition W_61220 : bv 32 := 0x00278793.

Definition W_61224 : bv 32 := 0xfcb7fae3.

Definition W_61228 : bv 32 := 0x00469813.

Definition W_6122c : bv 32 := 0x00479893.

Definition W_61230 : bv 32 := 0x01050833.

Definition W_61234 : bv 32 := 0x011508b3.

Definition W_61238 : bv 32 := 0x00082803.

Definition W_6123c : bv 32 := 0x0008a883.

Definition W_61240 : bv 32 := 0x01186463.

Definition W_61244 : bv 32 := 0x00068793.

Definition W_61248 : bv 32 := 0x00078693.

Definition W_6124c : bv 32 := 0x02c78c63.

Definition W_61250 : bv 32 := 0x00469613.

Definition W_61254 : bv 32 := 0x00c50633.

Definition W_61258 : bv 32 := 0x00063783.

Definition W_6125c : bv 32 := 0x00e50733.

Definition W_61260 : bv 32 := 0x00073803.

Definition W_61264 : bv 32 := 0x00873883.

Definition W_61268 : bv 32 := 0x00f73023.

Definition W_6126c : bv 32 := 0x00863783.

Definition W_61270 : bv 32 := 0x00f73423.

Definition W_61274 : bv 32 := 0x01063023.

Definition W_61278 : bv 32 := 0x01163423.

Definition W_6127c : bv 32 := 0x00068613.

Definition W_61280 : bv 32 := 0xf6b6e0e3.

Definition W_61284 : bv 32 := 0xfff58593.

Definition W_61288 : bv 32 := 0xf20594e3.

Definition W_6128c : bv 32 := 0x00008067.

