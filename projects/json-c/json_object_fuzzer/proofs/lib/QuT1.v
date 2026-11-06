(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_4e7a4 : bv 32 := 0x00008067.
Lemma F_4e7a4 : fetch_word Plain.M.loaded_segments (0x4e804 : word) = Some W_4e7a4.
Proof. vm_refl. Qed.
Lemma D_4e7a4 : decode_any W_4e7a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7a8 : bv 32 := 0xe8010113.
Lemma F_4e7a8 : fetch_word Plain.M.loaded_segments (0x4e808 : word) = Some W_4e7a8.
Proof. vm_refl. Qed.
Lemma D_4e7a8 : decode_any W_4e7a8 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7ac : bv 32 := 0x16113c23.
Lemma F_4e7ac : fetch_word Plain.M.loaded_segments (0x4e80c : word) = Some W_4e7ac.
Proof. vm_refl. Qed.
Lemma D_4e7ac : decode_any W_4e7ac = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7b0 : bv 32 := 0x16813823.
Lemma F_4e7b0 : fetch_word Plain.M.loaded_segments (0x4e810 : word) = Some W_4e7b0.
Proof. vm_refl. Qed.
Lemma D_4e7b0 : decode_any W_4e7b0 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7b4 : bv 32 := 0x16913423.
Lemma F_4e7b4 : fetch_word Plain.M.loaded_segments (0x4e814 : word) = Some W_4e7b4.
Proof. vm_refl. Qed.
Lemma D_4e7b4 : decode_any W_4e7b4 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7b8 : bv 32 := 0x17213023.
Lemma F_4e7b8 : fetch_word Plain.M.loaded_segments (0x4e818 : word) = Some W_4e7b8.
Proof. vm_refl. Qed.
Lemma D_4e7b8 : decode_any W_4e7b8 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7bc : bv 32 := 0x00058413.
Lemma F_4e7bc : fetch_word Plain.M.loaded_segments (0x4e81c : word) = Some W_4e7bc.
Proof. vm_refl. Qed.
Lemma D_4e7bc : decode_any W_4e7bc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7c0 : bv 32 := 0x00050493.
Lemma F_4e7c0 : fetch_word Plain.M.loaded_segments (0x4e820 : word) = Some W_4e7c0.
Proof. vm_refl. Qed.
Lemma D_4e7c0 : decode_any W_4e7c0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7c4 : bv 32 := 0x03010513.
Lemma F_4e7c4 : fetch_word Plain.M.loaded_segments (0x4e824 : word) = Some W_4e7c4.
Proof. vm_refl. Qed.
Lemma D_4e7c4 : decode_any W_4e7c4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7c8 : bv 32 := 0x13000613.
Lemma F_4e7c8 : fetch_word Plain.M.loaded_segments (0x4e828 : word) = Some W_4e7c8.
Proof. vm_refl. Qed.
Lemma D_4e7c8 : decode_any W_4e7c8 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7cc : bv 32 := 0x00000593.
Lemma F_4e7cc : fetch_word Plain.M.loaded_segments (0x4e82c : word) = Some W_4e7cc.
Proof. vm_refl. Qed.
Lemma D_4e7cc : decode_any W_4e7cc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7d0 : bv 32 := 0x4000f0ef.
Lemma F_4e7d0 : fetch_word Plain.M.loaded_segments (0x4e830 : word) = Some W_4e7d0.
Proof. vm_refl. Qed.
Lemma D_4e7d0 : decode_any W_4e7d0 = Some (Jal 1 62464, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7d4 : bv 32 := 0x00015517.
Lemma F_4e7d4 : fetch_word Plain.M.loaded_segments (0x4e834 : word) = Some W_4e7d4.
Proof. vm_refl. Qed.
Lemma D_4e7d4 : decode_any W_4e7d4 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7d8 : bv 32 := 0x62c53503.
Lemma F_4e7d8 : fetch_word Plain.M.loaded_segments (0x4e838 : word) = Some W_4e7d8.
Proof. vm_refl. Qed.
Lemma D_4e7d8 : decode_any W_4e7d8 = Some (Load SZ8 true 10 10 1580, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7dc : bv 32 := 0x00953023.
Lemma F_4e7dc : fetch_word Plain.M.loaded_segments (0x4e83c : word) = Some W_4e7dc.
Proof. vm_refl. Qed.
Lemma D_4e7dc : decode_any W_4e7dc = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7e0 : bv 32 := 0x0004b503.
Lemma F_4e7e0 : fetch_word Plain.M.loaded_segments (0x4e840 : word) = Some W_4e7e0.
Proof. vm_refl. Qed.
Lemma D_4e7e0 : decode_any W_4e7e0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7e4 : bv 32 := 0x00848493.
Lemma F_4e7e4 : fetch_word Plain.M.loaded_segments (0x4e844 : word) = Some W_4e7e4.
Proof. vm_refl. Qed.
Lemma D_4e7e4 : decode_any W_4e7e4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7e8 : bv 32 := 0xfe051ce3.
Lemma F_4e7e8 : fetch_word Plain.M.loaded_segments (0x4e848 : word) = Some W_4e7e8.
Proof. vm_refl. Qed.
Lemma D_4e7e8 : decode_any W_4e7e8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7ec : bv 32 := 0x00048517.
Lemma F_4e7ec : fetch_word Plain.M.loaded_segments (0x4e84c : word) = Some W_4e7ec.
Proof. vm_refl. Qed.
Lemma D_4e7ec : decode_any W_4e7ec = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7f0 : bv 32 := 0x8b450913.
Lemma F_4e7f0 : fetch_word Plain.M.loaded_segments (0x4e850 : word) = Some W_4e7f0.
Proof. vm_refl. Qed.
Lemma D_4e7f0 : decode_any W_4e7f0 = Some (OpImm ALU_ADD 18 10 2228, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7f4 : bv 32 := 0x00993423.
Lemma F_4e7f4 : fetch_word Plain.M.loaded_segments (0x4e854 : word) = Some W_4e7f4.
Proof. vm_refl. Qed.
Lemma D_4e7f4 : decode_any W_4e7f4 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7f8 : bv 32 := 0x0004b583.
Lemma F_4e7f8 : fetch_word Plain.M.loaded_segments (0x4e858 : word) = Some W_4e7f8.
Proof. vm_refl. Qed.
Lemma D_4e7f8 : decode_any W_4e7f8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e7fc : bv 32 := 0x04058c63.
Lemma F_4e7fc : fetch_word Plain.M.loaded_segments (0x4e85c : word) = Some W_4e7fc.
Proof. vm_refl. Qed.
Lemma D_4e7fc : decode_any W_4e7fc = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e800 : bv 32 := 0x01048493.
Lemma F_4e800 : fetch_word Plain.M.loaded_segments (0x4e860 : word) = Some W_4e800.
Proof. vm_refl. Qed.
Lemma D_4e800 : decode_any W_4e800 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e804 : bv 32 := 0x02500513.
Lemma F_4e804 : fetch_word Plain.M.loaded_segments (0x4e864 : word) = Some W_4e804.
Proof. vm_refl. Qed.
Lemma D_4e804 : decode_any W_4e804 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e808 : bv 32 := 0x03010613.
Lemma F_4e808 : fetch_word Plain.M.loaded_segments (0x4e868 : word) = Some W_4e808.
Proof. vm_refl. Qed.
Lemma D_4e808 : decode_any W_4e808 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e80c : bv 32 := 0x0100006f.
Lemma F_4e80c : fetch_word Plain.M.loaded_segments (0x4e86c : word) = Some W_4e80c.
Proof. vm_refl. Qed.
Lemma D_4e80c : decode_any W_4e80c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e810 : bv 32 := 0x0004b583.
Lemma F_4e810 : fetch_word Plain.M.loaded_segments (0x4e870 : word) = Some W_4e810.
Proof. vm_refl. Qed.
Lemma D_4e810 : decode_any W_4e810 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e814 : bv 32 := 0x01048493.
Lemma F_4e814 : fetch_word Plain.M.loaded_segments (0x4e874 : word) = Some W_4e814.
Proof. vm_refl. Qed.
Lemma D_4e814 : decode_any W_4e814 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e818 : bv 32 := 0x00058e63.
Lemma F_4e818 : fetch_word Plain.M.loaded_segments (0x4e878 : word) = Some W_4e818.
Proof. vm_refl. Qed.
Lemma D_4e818 : decode_any W_4e818 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e81c : bv 32 := 0xfeb56ae3.
Lemma F_4e81c : fetch_word Plain.M.loaded_segments (0x4e87c : word) = Some W_4e81c.
Proof. vm_refl. Qed.
Lemma D_4e81c : decode_any W_4e81c = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e820 : bv 32 := 0xff84b683.
Lemma F_4e820 : fetch_word Plain.M.loaded_segments (0x4e880 : word) = Some W_4e820.
Proof. vm_refl. Qed.
Lemma D_4e820 : decode_any W_4e820 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e824 : bv 32 := 0x00359593.
Lemma F_4e824 : fetch_word Plain.M.loaded_segments (0x4e884 : word) = Some W_4e824.
Proof. vm_refl. Qed.
Lemma D_4e824 : decode_any W_4e824 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e828 : bv 32 := 0x00b605b3.
Lemma F_4e828 : fetch_word Plain.M.loaded_segments (0x4e888 : word) = Some W_4e828.
Proof. vm_refl. Qed.
Lemma D_4e828 : decode_any W_4e828 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e82c : bv 32 := 0x00d5b023.
Lemma F_4e82c : fetch_word Plain.M.loaded_segments (0x4e88c : word) = Some W_4e82c.
Proof. vm_refl. Qed.
Lemma D_4e82c : decode_any W_4e82c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e830 : bv 32 := 0xfe1ff06f.
Lemma F_4e830 : fetch_word Plain.M.loaded_segments (0x4e890 : word) = Some W_4e830.
Proof. vm_refl. Qed.
Lemma D_4e830 : decode_any W_4e830 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e834 : bv 32 := 0x0b013583.
Lemma F_4e834 : fetch_word Plain.M.loaded_segments (0x4e894 : word) = Some W_4e834.
Proof. vm_refl. Qed.
Lemma D_4e834 : decode_any W_4e834 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e838 : bv 32 := 0x13013503.
Lemma F_4e838 : fetch_word Plain.M.loaded_segments (0x4e898 : word) = Some W_4e838.
Proof. vm_refl. Qed.
Lemma D_4e838 : decode_any W_4e838 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e83c : bv 32 := 0x00048617.
Lemma F_4e83c : fetch_word Plain.M.loaded_segments (0x4e89c : word) = Some W_4e83c.
Proof. vm_refl. Qed.
Lemma D_4e83c : decode_any W_4e83c = Some (Auipc 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e840 : bv 32 := 0x8cb63623.
Lemma F_4e840 : fetch_word Plain.M.loaded_segments (0x4e8a0 : word) = Some W_4e840.
Proof. vm_refl. Qed.
Lemma D_4e840 : decode_any W_4e840 = Some (Store SZ8 12 11 2252, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e844 : bv 32 := 0x00050c63.
Lemma F_4e844 : fetch_word Plain.M.loaded_segments (0x4e8a4 : word) = Some W_4e844.
Proof. vm_refl. Qed.
Lemma D_4e844 : decode_any W_4e844 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e85c : bv 32 := 0x06013503.
Lemma F_4e85c : fetch_word Plain.M.loaded_segments (0x4e8bc : word) = Some W_4e85c.
Proof. vm_refl. Qed.
Lemma D_4e85c : decode_any W_4e85c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e860 : bv 32 := 0x02a93823.
Lemma F_4e860 : fetch_word Plain.M.loaded_segments (0x4e8c0 : word) = Some W_4e860.
Proof. vm_refl. Qed.
Lemma D_4e860 : decode_any W_4e860 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e864 : bv 32 := 0x00041463.
Lemma F_4e864 : fetch_word Plain.M.loaded_segments (0x4e8c4 : word) = Some W_4e864.
Proof. vm_refl. Qed.
Lemma D_4e864 : decode_any W_4e864 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e86c : bv 32 := 0x00041663.
Lemma F_4e86c : fetch_word Plain.M.loaded_segments (0x4e8cc : word) = Some W_4e86c.
Proof. vm_refl. Qed.
Lemma D_4e86c : decode_any W_4e86c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e878 : bv 32 := 0x00015517.
Lemma F_4e878 : fetch_word Plain.M.loaded_segments (0x4e8d8 : word) = Some W_4e878.
Proof. vm_refl. Qed.
Lemma D_4e878 : decode_any W_4e878 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e87c : bv 32 := 0x59053583.
Lemma F_4e87c : fetch_word Plain.M.loaded_segments (0x4e8dc : word) = Some W_4e87c.
Proof. vm_refl. Qed.
Lemma D_4e87c : decode_any W_4e87c = Some (Load SZ8 true 11 10 1424, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e880 : bv 32 := 0x00015517.
Lemma F_4e880 : fetch_word Plain.M.loaded_segments (0x4e8e0 : word) = Some W_4e880.
Proof. vm_refl. Qed.
Lemma D_4e880 : decode_any W_4e880 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e884 : bv 32 := 0x59053503.
Lemma F_4e884 : fetch_word Plain.M.loaded_segments (0x4e8e4 : word) = Some W_4e884.
Proof. vm_refl. Qed.
Lemma D_4e884 : decode_any W_4e884 = Some (Load SZ8 true 10 10 1424, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e888 : bv 32 := 0x0085b023.
Lemma F_4e888 : fetch_word Plain.M.loaded_segments (0x4e8e8 : word) = Some W_4e888.
Proof. vm_refl. Qed.
Lemma D_4e888 : decode_any W_4e888 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e88c : bv 32 := 0x00140593.
Lemma F_4e88c : fetch_word Plain.M.loaded_segments (0x4e8ec : word) = Some W_4e88c.
Proof. vm_refl. Qed.
Lemma D_4e88c : decode_any W_4e88c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e890 : bv 32 := 0x00853023.
Lemma F_4e890 : fetch_word Plain.M.loaded_segments (0x4e8f0 : word) = Some W_4e890.
Proof. vm_refl. Qed.
Lemma D_4e890 : decode_any W_4e890 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e894 : bv 32 := 0x02f00613.
Lemma F_4e894 : fetch_word Plain.M.loaded_segments (0x4e8f4 : word) = Some W_4e894.
Proof. vm_refl. Qed.
Lemma D_4e894 : decode_any W_4e894 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e898 : bv 32 := 0x00c0006f.
Lemma F_4e898 : fetch_word Plain.M.loaded_segments (0x4e8f8 : word) = Some W_4e898.
Proof. vm_refl. Qed.
Lemma D_4e898 : decode_any W_4e898 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e89c : bv 32 := 0x00b53023.
Lemma F_4e89c : fetch_word Plain.M.loaded_segments (0x4e8fc : word) = Some W_4e89c.
Proof. vm_refl. Qed.
Lemma D_4e89c : decode_any W_4e89c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8a0 : bv 32 := 0x00158593.
Lemma F_4e8a0 : fetch_word Plain.M.loaded_segments (0x4e900 : word) = Some W_4e8a0.
Proof. vm_refl. Qed.
Lemma D_4e8a0 : decode_any W_4e8a0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8a4 : bv 32 := 0xfff5c683.
Lemma F_4e8a4 : fetch_word Plain.M.loaded_segments (0x4e904 : word) = Some W_4e8a4.
Proof. vm_refl. Qed.
Lemma D_4e8a4 : decode_any W_4e8a4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8a8 : bv 32 := 0xfec68ae3.
Lemma F_4e8a8 : fetch_word Plain.M.loaded_segments (0x4e908 : word) = Some W_4e8a8.
Proof. vm_refl. Qed.
Lemma D_4e8a8 : decode_any W_4e8a8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8ac : bv 32 := 0xfe069ae3.
Lemma F_4e8ac : fetch_word Plain.M.loaded_segments (0x4e90c : word) = Some W_4e8ac.
Proof. vm_refl. Qed.
Lemma D_4e8ac : decode_any W_4e8ac = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8b0 : bv 32 := 0x03010513.
Lemma F_4e8b0 : fetch_word Plain.M.loaded_segments (0x4e910 : word) = Some W_4e8b0.
Proof. vm_refl. Qed.
Lemma D_4e8b0 : decode_any W_4e8b0 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8b4 : bv 32 := 0x214000ef.
Lemma F_4e8b4 : fetch_word Plain.M.loaded_segments (0x4e914 : word) = Some W_4e8b4.
Proof. vm_refl. Qed.
Lemma D_4e8b4 : decode_any W_4e8b4 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8b8 : bv 32 := 0x0f813503.
Lemma F_4e8b8 : fetch_word Plain.M.loaded_segments (0x4e918 : word) = Some W_4e8b8.
Proof. vm_refl. Qed.
Lemma D_4e8b8 : decode_any W_4e8b8 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8bc : bv 32 := 0x121000ef.
Lemma F_4e8bc : fetch_word Plain.M.loaded_segments (0x4e91c : word) = Some W_4e8bc.
Proof. vm_refl. Qed.
Lemma D_4e8bc : decode_any W_4e8bc = Some (Jal 1 2336, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8c0 : bv 32 := 0x08813503.
Lemma F_4e8c0 : fetch_word Plain.M.loaded_segments (0x4e920 : word) = Some W_4e8c0.
Proof. vm_refl. Qed.
Lemma D_4e8c0 : decode_any W_4e8c0 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8c4 : bv 32 := 0x09013583.
Lemma F_4e8c4 : fetch_word Plain.M.loaded_segments (0x4e924 : word) = Some W_4e8c4.
Proof. vm_refl. Qed.
Lemma D_4e8c4 : decode_any W_4e8c4 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8c8 : bv 32 := 0x00b51c63.
Lemma F_4e8c8 : fetch_word Plain.M.loaded_segments (0x4e928 : word) = Some W_4e8c8.
Proof. vm_refl. Qed.
Lemma D_4e8c8 : decode_any W_4e8c8 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8cc : bv 32 := 0x09813503.
Lemma F_4e8cc : fetch_word Plain.M.loaded_segments (0x4e92c : word) = Some W_4e8cc.
Proof. vm_refl. Qed.
Lemma D_4e8cc : decode_any W_4e8cc = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8d0 : bv 32 := 0x0a013583.
Lemma F_4e8d0 : fetch_word Plain.M.loaded_segments (0x4e930 : word) = Some W_4e8d0.
Proof. vm_refl. Qed.
Lemma D_4e8d0 : decode_any W_4e8d0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8d4 : bv 32 := 0x00b51663.
Lemma F_4e8d4 : fetch_word Plain.M.loaded_segments (0x4e934 : word) = Some W_4e8d4.
Proof. vm_refl. Qed.
Lemma D_4e8d4 : decode_any W_4e8d4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8d8 : bv 32 := 0x0e813503.
Lemma F_4e8d8 : fetch_word Plain.M.loaded_segments (0x4e938 : word) = Some W_4e8d8.
Proof. vm_refl. Qed.
Lemma D_4e8d8 : decode_any W_4e8d8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e8dc : bv 32 := 0x0e050063.
Lemma F_4e8dc : fetch_word Plain.M.loaded_segments (0x4e93c : word) = Some W_4e8dc.
Proof. vm_refl. Qed.
Lemma D_4e8dc : decode_any W_4e8dc = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.
