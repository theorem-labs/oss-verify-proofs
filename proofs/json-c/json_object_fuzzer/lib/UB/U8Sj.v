(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_5d794 : bv 32 := 0x00c5a283.
Lemma F_5d794 : fetch_word Ubsan.M.loaded_segments (0x5f570 : word) = Some W_5d794.
Proof. vm_refl. Qed.
Lemma D_5d794 : decode_any W_5d794 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d798 : bv 32 := 0x01058593.
Lemma F_5d798 : fetch_word Ubsan.M.loaded_segments (0x5f574 : word) = Some W_5d798.
Proof. vm_refl. Qed.
Lemma D_5d798 : decode_any W_5d798 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d79c : bv 32 := 0xff060613.
Lemma F_5d79c : fetch_word Ubsan.M.loaded_segments (0x5f578 : word) = Some W_5d79c.
Proof. vm_refl. Qed.
Lemma D_5d79c : decode_any W_5d79c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7a0 : bv 32 := 0x00f6a023.
Lemma F_5d7a0 : fetch_word Ubsan.M.loaded_segments (0x5f57c : word) = Some W_5d7a0.
Proof. vm_refl. Qed.
Lemma D_5d7a0 : decode_any W_5d7a0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7a4 : bv 32 := 0x0106a223.
Lemma F_5d7a4 : fetch_word Ubsan.M.loaded_segments (0x5f580 : word) = Some W_5d7a4.
Proof. vm_refl. Qed.
Lemma D_5d7a4 : decode_any W_5d7a4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7a8 : bv 32 := 0x0116a423.
Lemma F_5d7a8 : fetch_word Ubsan.M.loaded_segments (0x5f584 : word) = Some W_5d7a8.
Proof. vm_refl. Qed.
Lemma D_5d7a8 : decode_any W_5d7a8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7ac : bv 32 := 0x0056a623.
Lemma F_5d7ac : fetch_word Ubsan.M.loaded_segments (0x5f588 : word) = Some W_5d7ac.
Proof. vm_refl. Qed.
Lemma D_5d7ac : decode_any W_5d7ac = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7b0 : bv 32 := 0x01068693.
Lemma F_5d7b0 : fetch_word Ubsan.M.loaded_segments (0x5f58c : word) = Some W_5d7b0.
Proof. vm_refl. Qed.
Lemma D_5d7b0 : decode_any W_5d7b0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7b4 : bv 32 := 0xfcc76ae3.
Lemma F_5d7b4 : fetch_word Ubsan.M.loaded_segments (0x5f590 : word) = Some W_5d7b4.
Proof. vm_refl. Qed.
Lemma D_5d7b4 : decode_any W_5d7b4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7b8 : bv 32 := 0x00800713.
Lemma F_5d7b8 : fetch_word Ubsan.M.loaded_segments (0x5f594 : word) = Some W_5d7b8.
Proof. vm_refl. Qed.
Lemma D_5d7b8 : decode_any W_5d7b8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7bc : bv 32 := 0x00e66e63.
Lemma F_5d7bc : fetch_word Ubsan.M.loaded_segments (0x5f598 : word) = Some W_5d7bc.
Proof. vm_refl. Qed.
Lemma D_5d7bc : decode_any W_5d7bc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7c0 : bv 32 := 0x0005a703.
Lemma F_5d7c0 : fetch_word Ubsan.M.loaded_segments (0x5f59c : word) = Some W_5d7c0.
Proof. vm_refl. Qed.
Lemma D_5d7c0 : decode_any W_5d7c0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7c4 : bv 32 := 0x0045a783.
Lemma F_5d7c4 : fetch_word Ubsan.M.loaded_segments (0x5f5a0 : word) = Some W_5d7c4.
Proof. vm_refl. Qed.
Lemma D_5d7c4 : decode_any W_5d7c4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7c8 : bv 32 := 0x00e6a023.
Lemma F_5d7c8 : fetch_word Ubsan.M.loaded_segments (0x5f5a4 : word) = Some W_5d7c8.
Proof. vm_refl. Qed.
Lemma D_5d7c8 : decode_any W_5d7c8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7cc : bv 32 := 0x00f6a223.
Lemma F_5d7cc : fetch_word Ubsan.M.loaded_segments (0x5f5a8 : word) = Some W_5d7cc.
Proof. vm_refl. Qed.
Lemma D_5d7cc : decode_any W_5d7cc = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d0 : bv 32 := 0x00868693.
Lemma F_5d7d0 : fetch_word Ubsan.M.loaded_segments (0x5f5ac : word) = Some W_5d7d0.
Proof. vm_refl. Qed.
Lemma D_5d7d0 : decode_any W_5d7d0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d4 : bv 32 := 0x00858593.
Lemma F_5d7d4 : fetch_word Ubsan.M.loaded_segments (0x5f5b0 : word) = Some W_5d7d4.
Proof. vm_refl. Qed.
Lemma D_5d7d4 : decode_any W_5d7d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7d8 : bv 32 := 0x00467713.
Lemma F_5d7d8 : fetch_word Ubsan.M.loaded_segments (0x5f5b4 : word) = Some W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : decode_any W_5d7d8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7dc : bv 32 := 0x24070063.
Lemma F_5d7dc : fetch_word Ubsan.M.loaded_segments (0x5f5b8 : word) = Some W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : decode_any W_5d7dc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e0 : bv 32 := 0x0005a703.
Lemma F_5d7e0 : fetch_word Ubsan.M.loaded_segments (0x5f5bc : word) = Some W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : decode_any W_5d7e0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e4 : bv 32 := 0x00458593.
Lemma F_5d7e4 : fetch_word Ubsan.M.loaded_segments (0x5f5c0 : word) = Some W_5d7e4.
Proof. vm_refl. Qed.
Lemma D_5d7e4 : decode_any W_5d7e4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7e8 : bv 32 := 0x00e6a023.
Lemma F_5d7e8 : fetch_word Ubsan.M.loaded_segments (0x5f5c4 : word) = Some W_5d7e8.
Proof. vm_refl. Qed.
Lemma D_5d7e8 : decode_any W_5d7e8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7ec : bv 32 := 0x00468693.
Lemma F_5d7ec : fetch_word Ubsan.M.loaded_segments (0x5f5c8 : word) = Some W_5d7ec.
Proof. vm_refl. Qed.
Lemma D_5d7ec : decode_any W_5d7ec = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f0 : bv 32 := 0x22c0006f.
Lemma F_5d7f0 : fetch_word Ubsan.M.loaded_segments (0x5f5cc : word) = Some W_5d7f0.
Proof. vm_refl. Qed.
Lemma D_5d7f0 : decode_any W_5d7f0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f4 : bv 32 := 0x00e68023.
Lemma F_5d7f4 : fetch_word Ubsan.M.loaded_segments (0x5f5d0 : word) = Some W_5d7f4.
Proof. vm_refl. Qed.
Lemma D_5d7f4 : decode_any W_5d7f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7f8 : bv 32 := 0x00168693.
Lemma F_5d7f8 : fetch_word Ubsan.M.loaded_segments (0x5f5d4 : word) = Some W_5d7f8.
Proof. vm_refl. Qed.
Lemma D_5d7f8 : decode_any W_5d7f8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d7fc : bv 32 := 0xfff60613.
Lemma F_5d7fc : fetch_word Ubsan.M.loaded_segments (0x5f5d8 : word) = Some W_5d7fc.
Proof. vm_refl. Qed.
Lemma D_5d7fc : decode_any W_5d7fc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d800 : bv 32 := 0x01058593.
Lemma F_5d800 : fetch_word Ubsan.M.loaded_segments (0x5f5dc : word) = Some W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : decode_any W_5d800 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d804 : bv 32 := 0x01200793.
Lemma F_5d804 : fetch_word Ubsan.M.loaded_segments (0x5f5e0 : word) = Some W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : decode_any W_5d804 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d808 : bv 32 := 0x0087581b.
Lemma F_5d808 : fetch_word Ubsan.M.loaded_segments (0x5f5e4 : word) = Some W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : decode_any W_5d808 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d80c : bv 32 := 0xff45a883.
Lemma F_5d80c : fetch_word Ubsan.M.loaded_segments (0x5f5e8 : word) = Some W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : decode_any W_5d80c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d810 : bv 32 := 0xff85a283.
Lemma F_5d810 : fetch_word Ubsan.M.loaded_segments (0x5f5ec : word) = Some W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : decode_any W_5d810 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d814 : bv 32 := 0xffc5a303.
Lemma F_5d814 : fetch_word Ubsan.M.loaded_segments (0x5f5f0 : word) = Some W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : decode_any W_5d814 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d818 : bv 32 := 0x0005a703.
Lemma F_5d818 : fetch_word Ubsan.M.loaded_segments (0x5f5f4 : word) = Some W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : decode_any W_5d818 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d81c : bv 32 := 0x01889393.
Lemma F_5d81c : fetch_word Ubsan.M.loaded_segments (0x5f5f8 : word) = Some W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : decode_any W_5d81c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d820 : bv 32 := 0x0088d89b.
Lemma F_5d820 : fetch_word Ubsan.M.loaded_segments (0x5f5fc : word) = Some W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : decode_any W_5d820 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d824 : bv 32 := 0x0103e833.
Lemma F_5d824 : fetch_word Ubsan.M.loaded_segments (0x5f600 : word) = Some W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : decode_any W_5d824 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d828 : bv 32 := 0x01829393.
Lemma F_5d828 : fetch_word Ubsan.M.loaded_segments (0x5f604 : word) = Some W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : decode_any W_5d828 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d82c : bv 32 := 0x0082d29b.
Lemma F_5d82c : fetch_word Ubsan.M.loaded_segments (0x5f608 : word) = Some W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : decode_any W_5d82c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d830 : bv 32 := 0x0113e8b3.
Lemma F_5d830 : fetch_word Ubsan.M.loaded_segments (0x5f60c : word) = Some W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : decode_any W_5d830 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d834 : bv 32 := 0x01831393.
Lemma F_5d834 : fetch_word Ubsan.M.loaded_segments (0x5f610 : word) = Some W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : decode_any W_5d834 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d838 : bv 32 := 0x0083531b.
Lemma F_5d838 : fetch_word Ubsan.M.loaded_segments (0x5f614 : word) = Some W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : decode_any W_5d838 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d83c : bv 32 := 0x0053e2b3.
Lemma F_5d83c : fetch_word Ubsan.M.loaded_segments (0x5f618 : word) = Some W_5d83c.
Proof. vm_refl. Qed.
Lemma D_5d83c : decode_any W_5d83c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d840 : bv 32 := 0x01871393.
Lemma F_5d840 : fetch_word Ubsan.M.loaded_segments (0x5f61c : word) = Some W_5d840.
Proof. vm_refl. Qed.
Lemma D_5d840 : decode_any W_5d840 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d844 : bv 32 := 0x0063e333.
Lemma F_5d844 : fetch_word Ubsan.M.loaded_segments (0x5f620 : word) = Some W_5d844.
Proof. vm_refl. Qed.
Lemma D_5d844 : decode_any W_5d844 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d848 : bv 32 := 0xff060613.
Lemma F_5d848 : fetch_word Ubsan.M.loaded_segments (0x5f624 : word) = Some W_5d848.
Proof. vm_refl. Qed.
Lemma D_5d848 : decode_any W_5d848 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d84c : bv 32 := 0x0106a023.
Lemma F_5d84c : fetch_word Ubsan.M.loaded_segments (0x5f628 : word) = Some W_5d84c.
Proof. vm_refl. Qed.
Lemma D_5d84c : decode_any W_5d84c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d850 : bv 32 := 0x0116a223.
Lemma F_5d850 : fetch_word Ubsan.M.loaded_segments (0x5f62c : word) = Some W_5d850.
Proof. vm_refl. Qed.
Lemma D_5d850 : decode_any W_5d850 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d854 : bv 32 := 0x0056a423.
Lemma F_5d854 : fetch_word Ubsan.M.loaded_segments (0x5f630 : word) = Some W_5d854.
Proof. vm_refl. Qed.
Lemma D_5d854 : decode_any W_5d854 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d858 : bv 32 := 0x0066a623.
Lemma F_5d858 : fetch_word Ubsan.M.loaded_segments (0x5f634 : word) = Some W_5d858.
Proof. vm_refl. Qed.
Lemma D_5d858 : decode_any W_5d858 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d85c : bv 32 := 0x01068693.
Lemma F_5d85c : fetch_word Ubsan.M.loaded_segments (0x5f638 : word) = Some W_5d85c.
Proof. vm_refl. Qed.
Lemma D_5d85c : decode_any W_5d85c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d860 : bv 32 := 0x01058593.
Lemma F_5d860 : fetch_word Ubsan.M.loaded_segments (0x5f63c : word) = Some W_5d860.
Proof. vm_refl. Qed.
Lemma D_5d860 : decode_any W_5d860 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d864 : bv 32 := 0xfac7e2e3.
Lemma F_5d864 : fetch_word Ubsan.M.loaded_segments (0x5f640 : word) = Some W_5d864.
Proof. vm_refl. Qed.
Lemma D_5d864 : decode_any W_5d864 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d868 : bv 32 := 0xff158593.
Lemma F_5d868 : fetch_word Ubsan.M.loaded_segments (0x5f644 : word) = Some W_5d868.
Proof. vm_refl. Qed.
Lemma D_5d868 : decode_any W_5d868 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d86c : bv 32 := 0x01000713.
Lemma F_5d86c : fetch_word Ubsan.M.loaded_segments (0x5f648 : word) = Some W_5d86c.
Proof. vm_refl. Qed.
Lemma D_5d86c : decode_any W_5d86c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d870 : bv 32 := 0xe4e666e3.
Lemma F_5d870 : fetch_word Ubsan.M.loaded_segments (0x5f64c : word) = Some W_5d870.
Proof. vm_refl. Qed.
Lemma D_5d870 : decode_any W_5d870 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d874 : bv 32 := 0x0940006f.
Lemma F_5d874 : fetch_word Ubsan.M.loaded_segments (0x5f650 : word) = Some W_5d874.
Proof. vm_refl. Qed.
Lemma D_5d874 : decode_any W_5d874 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d878 : bv 32 := 0x00875793.
Lemma F_5d878 : fetch_word Ubsan.M.loaded_segments (0x5f654 : word) = Some W_5d878.
Proof. vm_refl. Qed.
Lemma D_5d878 : decode_any W_5d878 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d87c : bv 32 := 0x01075813.
Lemma F_5d87c : fetch_word Ubsan.M.loaded_segments (0x5f658 : word) = Some W_5d87c.
Proof. vm_refl. Qed.
Lemma D_5d87c : decode_any W_5d87c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d880 : bv 32 := 0xffd60613.
Lemma F_5d880 : fetch_word Ubsan.M.loaded_segments (0x5f65c : word) = Some W_5d880.
Proof. vm_refl. Qed.
Lemma D_5d880 : decode_any W_5d880 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d884 : bv 32 := 0x00e68023.
Lemma F_5d884 : fetch_word Ubsan.M.loaded_segments (0x5f660 : word) = Some W_5d884.
Proof. vm_refl. Qed.
Lemma D_5d884 : decode_any W_5d884 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d888 : bv 32 := 0x00f680a3.
Lemma F_5d888 : fetch_word Ubsan.M.loaded_segments (0x5f664 : word) = Some W_5d888.
Proof. vm_refl. Qed.
Lemma D_5d888 : decode_any W_5d888 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d88c : bv 32 := 0x01068123.
Lemma F_5d88c : fetch_word Ubsan.M.loaded_segments (0x5f668 : word) = Some W_5d88c.
Proof. vm_refl. Qed.
Lemma D_5d88c : decode_any W_5d88c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d890 : bv 32 := 0x00368693.
Lemma F_5d890 : fetch_word Ubsan.M.loaded_segments (0x5f66c : word) = Some W_5d890.
Proof. vm_refl. Qed.
Lemma D_5d890 : decode_any W_5d890 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d894 : bv 32 := 0x01058593.
Lemma F_5d894 : fetch_word Ubsan.M.loaded_segments (0x5f670 : word) = Some W_5d894.
Proof. vm_refl. Qed.
Lemma D_5d894 : decode_any W_5d894 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d898 : bv 32 := 0x01000793.
Lemma F_5d898 : fetch_word Ubsan.M.loaded_segments (0x5f674 : word) = Some W_5d898.
Proof. vm_refl. Qed.
Lemma D_5d898 : decode_any W_5d898 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d89c : bv 32 := 0x0187581b.
Lemma F_5d89c : fetch_word Ubsan.M.loaded_segments (0x5f678 : word) = Some W_5d89c.
Proof. vm_refl. Qed.
Lemma D_5d89c : decode_any W_5d89c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8a0 : bv 32 := 0xff45a883.
Lemma F_5d8a0 : fetch_word Ubsan.M.loaded_segments (0x5f67c : word) = Some W_5d8a0.
Proof. vm_refl. Qed.
Lemma D_5d8a0 : decode_any W_5d8a0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8a4 : bv 32 := 0xff85a283.
Lemma F_5d8a4 : fetch_word Ubsan.M.loaded_segments (0x5f680 : word) = Some W_5d8a4.
Proof. vm_refl. Qed.
Lemma D_5d8a4 : decode_any W_5d8a4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8a8 : bv 32 := 0xffc5a303.
Lemma F_5d8a8 : fetch_word Ubsan.M.loaded_segments (0x5f684 : word) = Some W_5d8a8.
Proof. vm_refl. Qed.
Lemma D_5d8a8 : decode_any W_5d8a8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8ac : bv 32 := 0x0005a703.
Lemma F_5d8ac : fetch_word Ubsan.M.loaded_segments (0x5f688 : word) = Some W_5d8ac.
Proof. vm_refl. Qed.
Lemma D_5d8ac : decode_any W_5d8ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b0 : bv 32 := 0x00889393.
Lemma F_5d8b0 : fetch_word Ubsan.M.loaded_segments (0x5f68c : word) = Some W_5d8b0.
Proof. vm_refl. Qed.
Lemma D_5d8b0 : decode_any W_5d8b0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b4 : bv 32 := 0x0188d89b.
Lemma F_5d8b4 : fetch_word Ubsan.M.loaded_segments (0x5f690 : word) = Some W_5d8b4.
Proof. vm_refl. Qed.
Lemma D_5d8b4 : decode_any W_5d8b4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8b8 : bv 32 := 0x0103e833.
Lemma F_5d8b8 : fetch_word Ubsan.M.loaded_segments (0x5f694 : word) = Some W_5d8b8.
Proof. vm_refl. Qed.
Lemma D_5d8b8 : decode_any W_5d8b8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8bc : bv 32 := 0x00829393.
Lemma F_5d8bc : fetch_word Ubsan.M.loaded_segments (0x5f698 : word) = Some W_5d8bc.
Proof. vm_refl. Qed.
Lemma D_5d8bc : decode_any W_5d8bc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c0 : bv 32 := 0x0182d29b.
Lemma F_5d8c0 : fetch_word Ubsan.M.loaded_segments (0x5f69c : word) = Some W_5d8c0.
Proof. vm_refl. Qed.
Lemma D_5d8c0 : decode_any W_5d8c0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c4 : bv 32 := 0x0113e8b3.
Lemma F_5d8c4 : fetch_word Ubsan.M.loaded_segments (0x5f6a0 : word) = Some W_5d8c4.
Proof. vm_refl. Qed.
Lemma D_5d8c4 : decode_any W_5d8c4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8c8 : bv 32 := 0x00831393.
Lemma F_5d8c8 : fetch_word Ubsan.M.loaded_segments (0x5f6a4 : word) = Some W_5d8c8.
Proof. vm_refl. Qed.
Lemma D_5d8c8 : decode_any W_5d8c8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8cc : bv 32 := 0x0183531b.
Lemma F_5d8cc : fetch_word Ubsan.M.loaded_segments (0x5f6a8 : word) = Some W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : decode_any W_5d8cc = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d0 : bv 32 := 0x0053e2b3.
Lemma F_5d8d0 : fetch_word Ubsan.M.loaded_segments (0x5f6ac : word) = Some W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : decode_any W_5d8d0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d4 : bv 32 := 0x00871393.
Lemma F_5d8d4 : fetch_word Ubsan.M.loaded_segments (0x5f6b0 : word) = Some W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : decode_any W_5d8d4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8d8 : bv 32 := 0x0063e333.
Lemma F_5d8d8 : fetch_word Ubsan.M.loaded_segments (0x5f6b4 : word) = Some W_5d8d8.
Proof. vm_refl. Qed.
Lemma D_5d8d8 : decode_any W_5d8d8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8dc : bv 32 := 0xff060613.
Lemma F_5d8dc : fetch_word Ubsan.M.loaded_segments (0x5f6b8 : word) = Some W_5d8dc.
Proof. vm_refl. Qed.
Lemma D_5d8dc : decode_any W_5d8dc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8e0 : bv 32 := 0x0106a023.
Lemma F_5d8e0 : fetch_word Ubsan.M.loaded_segments (0x5f6bc : word) = Some W_5d8e0.
Proof. vm_refl. Qed.
Lemma D_5d8e0 : decode_any W_5d8e0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8e4 : bv 32 := 0x0116a223.
Lemma F_5d8e4 : fetch_word Ubsan.M.loaded_segments (0x5f6c0 : word) = Some W_5d8e4.
Proof. vm_refl. Qed.
Lemma D_5d8e4 : decode_any W_5d8e4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8e8 : bv 32 := 0x0056a423.
Lemma F_5d8e8 : fetch_word Ubsan.M.loaded_segments (0x5f6c4 : word) = Some W_5d8e8.
Proof. vm_refl. Qed.
Lemma D_5d8e8 : decode_any W_5d8e8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8ec : bv 32 := 0x0066a623.
Lemma F_5d8ec : fetch_word Ubsan.M.loaded_segments (0x5f6c8 : word) = Some W_5d8ec.
Proof. vm_refl. Qed.
Lemma D_5d8ec : decode_any W_5d8ec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8f0 : bv 32 := 0x01068693.
Lemma F_5d8f0 : fetch_word Ubsan.M.loaded_segments (0x5f6cc : word) = Some W_5d8f0.
Proof. vm_refl. Qed.
Lemma D_5d8f0 : decode_any W_5d8f0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8f4 : bv 32 := 0x01058593.
Lemma F_5d8f4 : fetch_word Ubsan.M.loaded_segments (0x5f6d0 : word) = Some W_5d8f4.
Proof. vm_refl. Qed.
Lemma D_5d8f4 : decode_any W_5d8f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8f8 : bv 32 := 0xfac7e2e3.
Lemma F_5d8f8 : fetch_word Ubsan.M.loaded_segments (0x5f6d4 : word) = Some W_5d8f8.
Proof. vm_refl. Qed.
Lemma D_5d8f8 : decode_any W_5d8f8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d8fc : bv 32 := 0xff358593.
Lemma F_5d8fc : fetch_word Ubsan.M.loaded_segments (0x5f6d8 : word) = Some W_5d8fc.
Proof. vm_refl. Qed.
Lemma D_5d8fc : decode_any W_5d8fc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d900 : bv 32 := 0x01000713.
Lemma F_5d900 : fetch_word Ubsan.M.loaded_segments (0x5f6dc : word) = Some W_5d900.
Proof. vm_refl. Qed.
Lemma D_5d900 : decode_any W_5d900 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d904 : bv 32 := 0xdae66ce3.
Lemma F_5d904 : fetch_word Ubsan.M.loaded_segments (0x5f6e0 : word) = Some W_5d904.
Proof. vm_refl. Qed.
Lemma D_5d904 : decode_any W_5d904 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d908 : bv 32 := 0x0005c703.
Lemma F_5d908 : fetch_word Ubsan.M.loaded_segments (0x5f6e4 : word) = Some W_5d908.
Proof. vm_refl. Qed.
Lemma D_5d908 : decode_any W_5d908 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d90c : bv 32 := 0x0015c783.
Lemma F_5d90c : fetch_word Ubsan.M.loaded_segments (0x5f6e8 : word) = Some W_5d90c.
Proof. vm_refl. Qed.
Lemma D_5d90c : decode_any W_5d90c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d910 : bv 32 := 0x0025c803.
Lemma F_5d910 : fetch_word Ubsan.M.loaded_segments (0x5f6ec : word) = Some W_5d910.
Proof. vm_refl. Qed.
Lemma D_5d910 : decode_any W_5d910 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d914 : bv 32 := 0x0035c883.
Lemma F_5d914 : fetch_word Ubsan.M.loaded_segments (0x5f6f0 : word) = Some W_5d914.
Proof. vm_refl. Qed.
Lemma D_5d914 : decode_any W_5d914 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d918 : bv 32 := 0x0045c283.
Lemma F_5d918 : fetch_word Ubsan.M.loaded_segments (0x5f6f4 : word) = Some W_5d918.
Proof. vm_refl. Qed.
Lemma D_5d918 : decode_any W_5d918 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d91c : bv 32 := 0x0055c303.
Lemma F_5d91c : fetch_word Ubsan.M.loaded_segments (0x5f6f8 : word) = Some W_5d91c.
Proof. vm_refl. Qed.
Lemma D_5d91c : decode_any W_5d91c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d920 : bv 32 := 0x0065c383.
Lemma F_5d920 : fetch_word Ubsan.M.loaded_segments (0x5f6fc : word) = Some W_5d920.
Proof. vm_refl. Qed.
Lemma D_5d920 : decode_any W_5d920 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d924 : bv 32 := 0x0075ce03.
Lemma F_5d924 : fetch_word Ubsan.M.loaded_segments (0x5f700 : word) = Some W_5d924.
Proof. vm_refl. Qed.
Lemma D_5d924 : decode_any W_5d924 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d928 : bv 32 := 0x00e68023.
Lemma F_5d928 : fetch_word Ubsan.M.loaded_segments (0x5f704 : word) = Some W_5d928.
Proof. vm_refl. Qed.
Lemma D_5d928 : decode_any W_5d928 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d92c : bv 32 := 0x00f680a3.
Lemma F_5d92c : fetch_word Ubsan.M.loaded_segments (0x5f708 : word) = Some W_5d92c.
Proof. vm_refl. Qed.
Lemma D_5d92c : decode_any W_5d92c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d930 : bv 32 := 0x01068123.
Lemma F_5d930 : fetch_word Ubsan.M.loaded_segments (0x5f70c : word) = Some W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : decode_any W_5d930 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d934 : bv 32 := 0x011681a3.
Lemma F_5d934 : fetch_word Ubsan.M.loaded_segments (0x5f710 : word) = Some W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : decode_any W_5d934 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d938 : bv 32 := 0x0085c703.
Lemma F_5d938 : fetch_word Ubsan.M.loaded_segments (0x5f714 : word) = Some W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : decode_any W_5d938 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d93c : bv 32 := 0x0095c783.
Lemma F_5d93c : fetch_word Ubsan.M.loaded_segments (0x5f718 : word) = Some W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : decode_any W_5d93c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d940 : bv 32 := 0x00a5c803.
Lemma F_5d940 : fetch_word Ubsan.M.loaded_segments (0x5f71c : word) = Some W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : decode_any W_5d940 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d944 : bv 32 := 0x00b5c883.
Lemma F_5d944 : fetch_word Ubsan.M.loaded_segments (0x5f720 : word) = Some W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : decode_any W_5d944 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d948 : bv 32 := 0x00568223.
Lemma F_5d948 : fetch_word Ubsan.M.loaded_segments (0x5f724 : word) = Some W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : decode_any W_5d948 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d94c : bv 32 := 0x006682a3.
Lemma F_5d94c : fetch_word Ubsan.M.loaded_segments (0x5f728 : word) = Some W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : decode_any W_5d94c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d950 : bv 32 := 0x00768323.
Lemma F_5d950 : fetch_word Ubsan.M.loaded_segments (0x5f72c : word) = Some W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : decode_any W_5d950 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d954 : bv 32 := 0x01c683a3.
Lemma F_5d954 : fetch_word Ubsan.M.loaded_segments (0x5f730 : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d958 : bv 32 := 0x00c5c283.
Lemma F_5d958 : fetch_word Ubsan.M.loaded_segments (0x5f734 : word) = Some W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : decode_any W_5d958 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d95c : bv 32 := 0x00d5c303.
Lemma F_5d95c : fetch_word Ubsan.M.loaded_segments (0x5f738 : word) = Some W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : decode_any W_5d95c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d960 : bv 32 := 0x00e5c383.
Lemma F_5d960 : fetch_word Ubsan.M.loaded_segments (0x5f73c : word) = Some W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : decode_any W_5d960 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d964 : bv 32 := 0x00f5ce03.
Lemma F_5d964 : fetch_word Ubsan.M.loaded_segments (0x5f740 : word) = Some W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : decode_any W_5d964 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d968 : bv 32 := 0x01058593.
Lemma F_5d968 : fetch_word Ubsan.M.loaded_segments (0x5f744 : word) = Some W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : decode_any W_5d968 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d96c : bv 32 := 0x00e68423.
Lemma F_5d96c : fetch_word Ubsan.M.loaded_segments (0x5f748 : word) = Some W_5d96c.
Proof. vm_refl. Qed.
Lemma D_5d96c : decode_any W_5d96c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d970 : bv 32 := 0x00f684a3.
Lemma F_5d970 : fetch_word Ubsan.M.loaded_segments (0x5f74c : word) = Some W_5d970.
Proof. vm_refl. Qed.
Lemma D_5d970 : decode_any W_5d970 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d974 : bv 32 := 0x01068523.
Lemma F_5d974 : fetch_word Ubsan.M.loaded_segments (0x5f750 : word) = Some W_5d974.
Proof. vm_refl. Qed.
Lemma D_5d974 : decode_any W_5d974 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d978 : bv 32 := 0x011685a3.
Lemma F_5d978 : fetch_word Ubsan.M.loaded_segments (0x5f754 : word) = Some W_5d978.
Proof. vm_refl. Qed.
Lemma D_5d978 : decode_any W_5d978 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d97c : bv 32 := 0x01068713.
Lemma F_5d97c : fetch_word Ubsan.M.loaded_segments (0x5f758 : word) = Some W_5d97c.
Proof. vm_refl. Qed.
Lemma D_5d97c : decode_any W_5d97c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d980 : bv 32 := 0x00568623.
Lemma F_5d980 : fetch_word Ubsan.M.loaded_segments (0x5f75c : word) = Some W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : decode_any W_5d980 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d984 : bv 32 := 0x006686a3.
Lemma F_5d984 : fetch_word Ubsan.M.loaded_segments (0x5f760 : word) = Some W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : decode_any W_5d984 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d988 : bv 32 := 0x00768723.
Lemma F_5d988 : fetch_word Ubsan.M.loaded_segments (0x5f764 : word) = Some W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : decode_any W_5d988 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d98c : bv 32 := 0x01c687a3.
Lemma F_5d98c : fetch_word Ubsan.M.loaded_segments (0x5f768 : word) = Some W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : decode_any W_5d98c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d990 : bv 32 := 0x00070693.
Lemma F_5d990 : fetch_word Ubsan.M.loaded_segments (0x5f76c : word) = Some W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : decode_any W_5d990 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d994 : bv 32 := 0x00867713.
Lemma F_5d994 : fetch_word Ubsan.M.loaded_segments (0x5f770 : word) = Some W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : decode_any W_5d994 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d998 : bv 32 := 0xd20706e3.
Lemma F_5d998 : fetch_word Ubsan.M.loaded_segments (0x5f774 : word) = Some W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : decode_any W_5d998 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d99c : bv 32 := 0x0005c703.
Lemma F_5d99c : fetch_word Ubsan.M.loaded_segments (0x5f778 : word) = Some W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : decode_any W_5d99c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a0 : bv 32 := 0x0015c783.
Lemma F_5d9a0 : fetch_word Ubsan.M.loaded_segments (0x5f77c : word) = Some W_5d9a0.
Proof. vm_refl. Qed.
Lemma D_5d9a0 : decode_any W_5d9a0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a4 : bv 32 := 0x0025c803.
Lemma F_5d9a4 : fetch_word Ubsan.M.loaded_segments (0x5f780 : word) = Some W_5d9a4.
Proof. vm_refl. Qed.
Lemma D_5d9a4 : decode_any W_5d9a4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9a8 : bv 32 := 0x0035c883.
Lemma F_5d9a8 : fetch_word Ubsan.M.loaded_segments (0x5f784 : word) = Some W_5d9a8.
Proof. vm_refl. Qed.
Lemma D_5d9a8 : decode_any W_5d9a8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9ac : bv 32 := 0x0045c283.
Lemma F_5d9ac : fetch_word Ubsan.M.loaded_segments (0x5f788 : word) = Some W_5d9ac.
Proof. vm_refl. Qed.
Lemma D_5d9ac : decode_any W_5d9ac = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b0 : bv 32 := 0x0055c303.
Lemma F_5d9b0 : fetch_word Ubsan.M.loaded_segments (0x5f78c : word) = Some W_5d9b0.
Proof. vm_refl. Qed.
Lemma D_5d9b0 : decode_any W_5d9b0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b4 : bv 32 := 0x0065c383.
Lemma F_5d9b4 : fetch_word Ubsan.M.loaded_segments (0x5f790 : word) = Some W_5d9b4.
Proof. vm_refl. Qed.
Lemma D_5d9b4 : decode_any W_5d9b4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9b8 : bv 32 := 0x0075ce03.
Lemma F_5d9b8 : fetch_word Ubsan.M.loaded_segments (0x5f794 : word) = Some W_5d9b8.
Proof. vm_refl. Qed.
Lemma D_5d9b8 : decode_any W_5d9b8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9bc : bv 32 := 0x00858593.
Lemma F_5d9bc : fetch_word Ubsan.M.loaded_segments (0x5f798 : word) = Some W_5d9bc.
Proof. vm_refl. Qed.
Lemma D_5d9bc : decode_any W_5d9bc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c0 : bv 32 := 0x00e68023.
Lemma F_5d9c0 : fetch_word Ubsan.M.loaded_segments (0x5f79c : word) = Some W_5d9c0.
Proof. vm_refl. Qed.
Lemma D_5d9c0 : decode_any W_5d9c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c4 : bv 32 := 0x00f680a3.
Lemma F_5d9c4 : fetch_word Ubsan.M.loaded_segments (0x5f7a0 : word) = Some W_5d9c4.
Proof. vm_refl. Qed.
Lemma D_5d9c4 : decode_any W_5d9c4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9c8 : bv 32 := 0x01068123.
Lemma F_5d9c8 : fetch_word Ubsan.M.loaded_segments (0x5f7a4 : word) = Some W_5d9c8.
Proof. vm_refl. Qed.
Lemma D_5d9c8 : decode_any W_5d9c8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9cc : bv 32 := 0x011681a3.
Lemma F_5d9cc : fetch_word Ubsan.M.loaded_segments (0x5f7a8 : word) = Some W_5d9cc.
Proof. vm_refl. Qed.
Lemma D_5d9cc : decode_any W_5d9cc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d0 : bv 32 := 0x00868713.
Lemma F_5d9d0 : fetch_word Ubsan.M.loaded_segments (0x5f7ac : word) = Some W_5d9d0.
Proof. vm_refl. Qed.
Lemma D_5d9d0 : decode_any W_5d9d0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d4 : bv 32 := 0x00568223.
Lemma F_5d9d4 : fetch_word Ubsan.M.loaded_segments (0x5f7b0 : word) = Some W_5d9d4.
Proof. vm_refl. Qed.
Lemma D_5d9d4 : decode_any W_5d9d4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9d8 : bv 32 := 0x006682a3.
Lemma F_5d9d8 : fetch_word Ubsan.M.loaded_segments (0x5f7b4 : word) = Some W_5d9d8.
Proof. vm_refl. Qed.
Lemma D_5d9d8 : decode_any W_5d9d8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9dc : bv 32 := 0x00768323.
Lemma F_5d9dc : fetch_word Ubsan.M.loaded_segments (0x5f7b8 : word) = Some W_5d9dc.
Proof. vm_refl. Qed.
Lemma D_5d9dc : decode_any W_5d9dc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e0 : bv 32 := 0x01c683a3.
Lemma F_5d9e0 : fetch_word Ubsan.M.loaded_segments (0x5f7bc : word) = Some W_5d9e0.
Proof. vm_refl. Qed.
Lemma D_5d9e0 : decode_any W_5d9e0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e4 : bv 32 := 0x00070693.
Lemma F_5d9e4 : fetch_word Ubsan.M.loaded_segments (0x5f7c0 : word) = Some W_5d9e4.
Proof. vm_refl. Qed.
Lemma D_5d9e4 : decode_any W_5d9e4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9e8 : bv 32 := 0x00467713.
Lemma F_5d9e8 : fetch_word Ubsan.M.loaded_segments (0x5f7c4 : word) = Some W_5d9e8.
Proof. vm_refl. Qed.
Lemma D_5d9e8 : decode_any W_5d9e8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9ec : bv 32 := 0x02070863.
Lemma F_5d9ec : fetch_word Ubsan.M.loaded_segments (0x5f7c8 : word) = Some W_5d9ec.
Proof. vm_refl. Qed.
Lemma D_5d9ec : decode_any W_5d9ec = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f0 : bv 32 := 0x0005c703.
Lemma F_5d9f0 : fetch_word Ubsan.M.loaded_segments (0x5f7cc : word) = Some W_5d9f0.
Proof. vm_refl. Qed.
Lemma D_5d9f0 : decode_any W_5d9f0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f4 : bv 32 := 0x0015c783.
Lemma F_5d9f4 : fetch_word Ubsan.M.loaded_segments (0x5f7d0 : word) = Some W_5d9f4.
Proof. vm_refl. Qed.
Lemma D_5d9f4 : decode_any W_5d9f4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9f8 : bv 32 := 0x0025c803.
Lemma F_5d9f8 : fetch_word Ubsan.M.loaded_segments (0x5f7d4 : word) = Some W_5d9f8.
Proof. vm_refl. Qed.
Lemma D_5d9f8 : decode_any W_5d9f8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5d9fc : bv 32 := 0x0035c883.
Lemma F_5d9fc : fetch_word Ubsan.M.loaded_segments (0x5f7d8 : word) = Some W_5d9fc.
Proof. vm_refl. Qed.
Lemma D_5d9fc : decode_any W_5d9fc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da00 : bv 32 := 0x00458593.
Lemma F_5da00 : fetch_word Ubsan.M.loaded_segments (0x5f7dc : word) = Some W_5da00.
Proof. vm_refl. Qed.
Lemma D_5da00 : decode_any W_5da00 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da04 : bv 32 := 0x00468293.
Lemma F_5da04 : fetch_word Ubsan.M.loaded_segments (0x5f7e0 : word) = Some W_5da04.
Proof. vm_refl. Qed.
Lemma D_5da04 : decode_any W_5da04 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da08 : bv 32 := 0x00e68023.
Lemma F_5da08 : fetch_word Ubsan.M.loaded_segments (0x5f7e4 : word) = Some W_5da08.
Proof. vm_refl. Qed.
Lemma D_5da08 : decode_any W_5da08 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da0c : bv 32 := 0x00f680a3.
Lemma F_5da0c : fetch_word Ubsan.M.loaded_segments (0x5f7e8 : word) = Some W_5da0c.
Proof. vm_refl. Qed.
Lemma D_5da0c : decode_any W_5da0c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da10 : bv 32 := 0x01068123.
Lemma F_5da10 : fetch_word Ubsan.M.loaded_segments (0x5f7ec : word) = Some W_5da10.
Proof. vm_refl. Qed.
Lemma D_5da10 : decode_any W_5da10 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da14 : bv 32 := 0x011681a3.
Lemma F_5da14 : fetch_word Ubsan.M.loaded_segments (0x5f7f0 : word) = Some W_5da14.
Proof. vm_refl. Qed.
Lemma D_5da14 : decode_any W_5da14 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da18 : bv 32 := 0x00028693.
Lemma F_5da18 : fetch_word Ubsan.M.loaded_segments (0x5f7f4 : word) = Some W_5da18.
Proof. vm_refl. Qed.
Lemma D_5da18 : decode_any W_5da18 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da1c : bv 32 := 0x00267713.
Lemma F_5da1c : fetch_word Ubsan.M.loaded_segments (0x5f7f8 : word) = Some W_5da1c.
Proof. vm_refl. Qed.
Lemma D_5da1c : decode_any W_5da1c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da20 : bv 32 := 0x00071863.
Lemma F_5da20 : fetch_word Ubsan.M.loaded_segments (0x5f7fc : word) = Some W_5da20.
Proof. vm_refl. Qed.
Lemma D_5da20 : decode_any W_5da20 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da24 : bv 32 := 0x00167613.
Lemma F_5da24 : fetch_word Ubsan.M.loaded_segments (0x5f800 : word) = Some W_5da24.
Proof. vm_refl. Qed.
Lemma D_5da24 : decode_any W_5da24 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da28 : bv 32 := 0x02061663.
Lemma F_5da28 : fetch_word Ubsan.M.loaded_segments (0x5f804 : word) = Some W_5da28.
Proof. vm_refl. Qed.
Lemma D_5da28 : decode_any W_5da28 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da2c : bv 32 := 0x00008067.
Lemma F_5da2c : fetch_word Ubsan.M.loaded_segments (0x5f808 : word) = Some W_5da2c.
Proof. vm_refl. Qed.
Lemma D_5da2c : decode_any W_5da2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da30 : bv 32 := 0x0005c703.
Lemma F_5da30 : fetch_word Ubsan.M.loaded_segments (0x5f80c : word) = Some W_5da30.
Proof. vm_refl. Qed.
Lemma D_5da30 : decode_any W_5da30 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da34 : bv 32 := 0x0015c783.
Lemma F_5da34 : fetch_word Ubsan.M.loaded_segments (0x5f810 : word) = Some W_5da34.
Proof. vm_refl. Qed.
Lemma D_5da34 : decode_any W_5da34 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da38 : bv 32 := 0x00258593.
Lemma F_5da38 : fetch_word Ubsan.M.loaded_segments (0x5f814 : word) = Some W_5da38.
Proof. vm_refl. Qed.
Lemma D_5da38 : decode_any W_5da38 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da3c : bv 32 := 0x00268813.
Lemma F_5da3c : fetch_word Ubsan.M.loaded_segments (0x5f818 : word) = Some W_5da3c.
Proof. vm_refl. Qed.
Lemma D_5da3c : decode_any W_5da3c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da40 : bv 32 := 0x00e68023.
Lemma F_5da40 : fetch_word Ubsan.M.loaded_segments (0x5f81c : word) = Some W_5da40.
Proof. vm_refl. Qed.
Lemma D_5da40 : decode_any W_5da40 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da44 : bv 32 := 0x00f680a3.
Lemma F_5da44 : fetch_word Ubsan.M.loaded_segments (0x5f820 : word) = Some W_5da44.
Proof. vm_refl. Qed.
Lemma D_5da44 : decode_any W_5da44 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da48 : bv 32 := 0x00080693.
Lemma F_5da48 : fetch_word Ubsan.M.loaded_segments (0x5f824 : word) = Some W_5da48.
Proof. vm_refl. Qed.
Lemma D_5da48 : decode_any W_5da48 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da4c : bv 32 := 0x00167613.
Lemma F_5da4c : fetch_word Ubsan.M.loaded_segments (0x5f828 : word) = Some W_5da4c.
Proof. vm_refl. Qed.
Lemma D_5da4c : decode_any W_5da4c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da50 : bv 32 := 0xfc060ee3.
Lemma F_5da50 : fetch_word Ubsan.M.loaded_segments (0x5f82c : word) = Some W_5da50.
Proof. vm_refl. Qed.
Lemma D_5da50 : decode_any W_5da50 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da54 : bv 32 := 0x0005c583.
Lemma F_5da54 : fetch_word Ubsan.M.loaded_segments (0x5f830 : word) = Some W_5da54.
Proof. vm_refl. Qed.
Lemma D_5da54 : decode_any W_5da54 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da58 : bv 32 := 0x00b68023.
Lemma F_5da58 : fetch_word Ubsan.M.loaded_segments (0x5f834 : word) = Some W_5da58.
Proof. vm_refl. Qed.
Lemma D_5da58 : decode_any W_5da58 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5da5c : bv 32 := 0x00008067.
Lemma F_5da5c : fetch_word Ubsan.M.loaded_segments (0x5f838 : word) = Some W_5da5c.
Proof. vm_refl. Qed.
Lemma D_5da5c : decode_any W_5da5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbdc : bv 32 := 0x0e060a63.
Lemma F_5dbdc : fetch_word Ubsan.M.loaded_segments (0x5f9b8 : word) = Some W_5dbdc.
Proof. vm_refl. Qed.
Lemma D_5dbdc : decode_any W_5dbdc = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe0 : bv 32 := 0x00b50023.
Lemma F_5dbe0 : fetch_word Ubsan.M.loaded_segments (0x5f9bc : word) = Some W_5dbe0.
Proof. vm_refl. Qed.
Lemma D_5dbe0 : decode_any W_5dbe0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe4 : bv 32 := 0x00c506b3.
Lemma F_5dbe4 : fetch_word Ubsan.M.loaded_segments (0x5f9c0 : word) = Some W_5dbe4.
Proof. vm_refl. Qed.
Lemma D_5dbe4 : decode_any W_5dbe4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbe8 : bv 32 := 0x00300713.
Lemma F_5dbe8 : fetch_word Ubsan.M.loaded_segments (0x5f9c4 : word) = Some W_5dbe8.
Proof. vm_refl. Qed.
Lemma D_5dbe8 : decode_any W_5dbe8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbec : bv 32 := 0xfeb68fa3.
Lemma F_5dbec : fetch_word Ubsan.M.loaded_segments (0x5f9c8 : word) = Some W_5dbec.
Proof. vm_refl. Qed.
Lemma D_5dbec : decode_any W_5dbec = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf0 : bv 32 := 0x0ee66063.
Lemma F_5dbf0 : fetch_word Ubsan.M.loaded_segments (0x5f9cc : word) = Some W_5dbf0.
Proof. vm_refl. Qed.
Lemma D_5dbf0 : decode_any W_5dbf0 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf4 : bv 32 := 0x00b500a3.
Lemma F_5dbf4 : fetch_word Ubsan.M.loaded_segments (0x5f9d0 : word) = Some W_5dbf4.
Proof. vm_refl. Qed.
Lemma D_5dbf4 : decode_any W_5dbf4 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbf8 : bv 32 := 0x00b50123.
Lemma F_5dbf8 : fetch_word Ubsan.M.loaded_segments (0x5f9d4 : word) = Some W_5dbf8.
Proof. vm_refl. Qed.
Lemma D_5dbf8 : decode_any W_5dbf8 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dbfc : bv 32 := 0x00700713.
Lemma F_5dbfc : fetch_word Ubsan.M.loaded_segments (0x5f9d8 : word) = Some W_5dbfc.
Proof. vm_refl. Qed.
Lemma D_5dbfc : decode_any W_5dbfc = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc00 : bv 32 := 0xfeb68ea3.
Lemma F_5dc00 : fetch_word Ubsan.M.loaded_segments (0x5f9dc : word) = Some W_5dc00.
Proof. vm_refl. Qed.
Lemma D_5dc00 : decode_any W_5dc00 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc04 : bv 32 := 0xfeb68f23.
Lemma F_5dc04 : fetch_word Ubsan.M.loaded_segments (0x5f9e0 : word) = Some W_5dc04.
Proof. vm_refl. Qed.
Lemma D_5dc04 : decode_any W_5dc04 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc08 : bv 32 := 0x0ce66463.
Lemma F_5dc08 : fetch_word Ubsan.M.loaded_segments (0x5f9e4 : word) = Some W_5dc08.
Proof. vm_refl. Qed.
Lemma D_5dc08 : decode_any W_5dc08 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc0c : bv 32 := 0x00b501a3.
Lemma F_5dc0c : fetch_word Ubsan.M.loaded_segments (0x5f9e8 : word) = Some W_5dc0c.
Proof. vm_refl. Qed.
Lemma D_5dc0c : decode_any W_5dc0c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc10 : bv 32 := 0x00900793.
Lemma F_5dc10 : fetch_word Ubsan.M.loaded_segments (0x5f9ec : word) = Some W_5dc10.
Proof. vm_refl. Qed.
Lemma D_5dc10 : decode_any W_5dc10 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc14 : bv 32 := 0xfeb68e23.
Lemma F_5dc14 : fetch_word Ubsan.M.loaded_segments (0x5f9f0 : word) = Some W_5dc14.
Proof. vm_refl. Qed.
Lemma D_5dc14 : decode_any W_5dc14 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc18 : bv 32 := 0x0af66c63.
Lemma F_5dc18 : fetch_word Ubsan.M.loaded_segments (0x5f9f4 : word) = Some W_5dc18.
Proof. vm_refl. Qed.
Lemma D_5dc18 : decode_any W_5dc18 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc1c : bv 32 := 0x40a006bb.
Lemma F_5dc1c : fetch_word Ubsan.M.loaded_segments (0x5f9f8 : word) = Some W_5dc1c.
Proof. vm_refl. Qed.
Lemma D_5dc1c : decode_any W_5dc1c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc20 : bv 32 := 0x03859813.
Lemma F_5dc20 : fetch_word Ubsan.M.loaded_segments (0x5f9fc : word) = Some W_5dc20.
Proof. vm_refl. Qed.
Lemma D_5dc20 : decode_any W_5dc20 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc24 : bv 32 := 0x101015b7.
Lemma F_5dc24 : fetch_word Ubsan.M.loaded_segments (0x5fa00 : word) = Some W_5dc24.
Proof. vm_refl. Qed.
Lemma D_5dc24 : decode_any W_5dc24 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc28 : bv 32 := 0x0036f693.
Lemma F_5dc28 : fetch_word Ubsan.M.loaded_segments (0x5fa04 : word) = Some W_5dc28.
Proof. vm_refl. Qed.
Lemma D_5dc28 : decode_any W_5dc28 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc2c : bv 32 := 0x00459713.
Lemma F_5dc2c : fetch_word Ubsan.M.loaded_segments (0x5fa08 : word) = Some W_5dc2c.
Proof. vm_refl. Qed.
Lemma D_5dc2c : decode_any W_5dc2c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc30 : bv 32 := 0x40d60633.
Lemma F_5dc30 : fetch_word Ubsan.M.loaded_segments (0x5fa0c : word) = Some W_5dc30.
Proof. vm_refl. Qed.
Lemma D_5dc30 : decode_any W_5dc30 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc34 : bv 32 := 0x00d505b3.
Lemma F_5dc34 : fetch_word Ubsan.M.loaded_segments (0x5fa10 : word) = Some W_5dc34.
Proof. vm_refl. Qed.
Lemma D_5dc34 : decode_any W_5dc34 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc38 : bv 32 := 0x10070693.
Lemma F_5dc38 : fetch_word Ubsan.M.loaded_segments (0x5fa14 : word) = Some W_5dc38.
Proof. vm_refl. Qed.
Lemma D_5dc38 : decode_any W_5dc38 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc3c : bv 32 := 0xffc67713.
Lemma F_5dc3c : fetch_word Ubsan.M.loaded_segments (0x5fa18 : word) = Some W_5dc3c.
Proof. vm_refl. Qed.
Lemma D_5dc3c : decode_any W_5dc3c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc40 : bv 32 := 0x02d83633.
Lemma F_5dc40 : fetch_word Ubsan.M.loaded_segments (0x5fa1c : word) = Some W_5dc40.
Proof. vm_refl. Qed.
Lemma D_5dc40 : decode_any W_5dc40 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc44 : bv 32 := 0x00c5a023.
Lemma F_5dc44 : fetch_word Ubsan.M.loaded_segments (0x5fa20 : word) = Some W_5dc44.
Proof. vm_refl. Qed.
Lemma D_5dc44 : decode_any W_5dc44 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc48 : bv 32 := 0x00e586b3.
Lemma F_5dc48 : fetch_word Ubsan.M.loaded_segments (0x5fa24 : word) = Some W_5dc48.
Proof. vm_refl. Qed.
Lemma D_5dc48 : decode_any W_5dc48 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc4c : bv 32 := 0xfec6ae23.
Lemma F_5dc4c : fetch_word Ubsan.M.loaded_segments (0x5fa28 : word) = Some W_5dc4c.
Proof. vm_refl. Qed.
Lemma D_5dc4c : decode_any W_5dc4c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc50 : bv 32 := 0x08f76063.
Lemma F_5dc50 : fetch_word Ubsan.M.loaded_segments (0x5fa2c : word) = Some W_5dc50.
Proof. vm_refl. Qed.
Lemma D_5dc50 : decode_any W_5dc50 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc54 : bv 32 := 0x00c5a223.
Lemma F_5dc54 : fetch_word Ubsan.M.loaded_segments (0x5fa30 : word) = Some W_5dc54.
Proof. vm_refl. Qed.
Lemma D_5dc54 : decode_any W_5dc54 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc58 : bv 32 := 0x00c5a423.
Lemma F_5dc58 : fetch_word Ubsan.M.loaded_segments (0x5fa34 : word) = Some W_5dc58.
Proof. vm_refl. Qed.
Lemma D_5dc58 : decode_any W_5dc58 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc5c : bv 32 := 0x01900793.
Lemma F_5dc5c : fetch_word Ubsan.M.loaded_segments (0x5fa38 : word) = Some W_5dc5c.
Proof. vm_refl. Qed.
Lemma D_5dc5c : decode_any W_5dc5c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc60 : bv 32 := 0xfec6aa23.
Lemma F_5dc60 : fetch_word Ubsan.M.loaded_segments (0x5fa3c : word) = Some W_5dc60.
Proof. vm_refl. Qed.
Lemma D_5dc60 : decode_any W_5dc60 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc64 : bv 32 := 0xfec6ac23.
Lemma F_5dc64 : fetch_word Ubsan.M.loaded_segments (0x5fa40 : word) = Some W_5dc64.
Proof. vm_refl. Qed.
Lemma D_5dc64 : decode_any W_5dc64 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc68 : bv 32 := 0x06f76463.
Lemma F_5dc68 : fetch_word Ubsan.M.loaded_segments (0x5fa44 : word) = Some W_5dc68.
Proof. vm_refl. Qed.
Lemma D_5dc68 : decode_any W_5dc68 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc6c : bv 32 := 0x00c5a623.
Lemma F_5dc6c : fetch_word Ubsan.M.loaded_segments (0x5fa48 : word) = Some W_5dc6c.
Proof. vm_refl. Qed.
Lemma D_5dc6c : decode_any W_5dc6c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc70 : bv 32 := 0x00c5a823.
Lemma F_5dc70 : fetch_word Ubsan.M.loaded_segments (0x5fa4c : word) = Some W_5dc70.
Proof. vm_refl. Qed.
Lemma D_5dc70 : decode_any W_5dc70 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc74 : bv 32 := 0x00c5aa23.
Lemma F_5dc74 : fetch_word Ubsan.M.loaded_segments (0x5fa50 : word) = Some W_5dc74.
Proof. vm_refl. Qed.
Lemma D_5dc74 : decode_any W_5dc74 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc78 : bv 32 := 0x00c5ac23.
Lemma F_5dc78 : fetch_word Ubsan.M.loaded_segments (0x5fa54 : word) = Some W_5dc78.
Proof. vm_refl. Qed.
Lemma D_5dc78 : decode_any W_5dc78 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc7c : bv 32 := 0x0045f793.
Lemma F_5dc7c : fetch_word Ubsan.M.loaded_segments (0x5fa58 : word) = Some W_5dc7c.
Proof. vm_refl. Qed.
Lemma D_5dc7c : decode_any W_5dc7c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc80 : bv 32 := 0x02000813.
Lemma F_5dc80 : fetch_word Ubsan.M.loaded_segments (0x5fa5c : word) = Some W_5dc80.
Proof. vm_refl. Qed.
Lemma D_5dc80 : decode_any W_5dc80 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc84 : bv 32 := 0x01878793.
Lemma F_5dc84 : fetch_word Ubsan.M.loaded_segments (0x5fa60 : word) = Some W_5dc84.
Proof. vm_refl. Qed.
Lemma D_5dc84 : decode_any W_5dc84 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc88 : bv 32 := 0x40f70733.
Lemma F_5dc88 : fetch_word Ubsan.M.loaded_segments (0x5fa64 : word) = Some W_5dc88.
Proof. vm_refl. Qed.
Lemma D_5dc88 : decode_any W_5dc88 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc8c : bv 32 := 0xfec6a223.
Lemma F_5dc8c : fetch_word Ubsan.M.loaded_segments (0x5fa68 : word) = Some W_5dc8c.
Proof. vm_refl. Qed.
Lemma D_5dc8c : decode_any W_5dc8c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc90 : bv 32 := 0xfec6a423.
Lemma F_5dc90 : fetch_word Ubsan.M.loaded_segments (0x5fa6c : word) = Some W_5dc90.
Proof. vm_refl. Qed.
Lemma D_5dc90 : decode_any W_5dc90 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc94 : bv 32 := 0xfec6a623.
Lemma F_5dc94 : fetch_word Ubsan.M.loaded_segments (0x5fa70 : word) = Some W_5dc94.
Proof. vm_refl. Qed.
Lemma D_5dc94 : decode_any W_5dc94 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc98 : bv 32 := 0xfec6a823.
Lemma F_5dc98 : fetch_word Ubsan.M.loaded_segments (0x5fa74 : word) = Some W_5dc98.
Proof. vm_refl. Qed.
Lemma D_5dc98 : decode_any W_5dc98 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dc9c : bv 32 := 0x03076a63.
Lemma F_5dc9c : fetch_word Ubsan.M.loaded_segments (0x5fa78 : word) = Some W_5dc9c.
Proof. vm_refl. Qed.
Lemma D_5dc9c : decode_any W_5dc9c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca0 : bv 32 := 0x02061613.
Lemma F_5dca0 : fetch_word Ubsan.M.loaded_segments (0x5fa7c : word) = Some W_5dca0.
Proof. vm_refl. Qed.
Lemma D_5dca0 : decode_any W_5dca0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca4 : bv 32 := 0x00f585b3.
Lemma F_5dca4 : fetch_word Ubsan.M.loaded_segments (0x5fa80 : word) = Some W_5dca4.
Proof. vm_refl. Qed.
Lemma D_5dca4 : decode_any W_5dca4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dca8 : bv 32 := 0x02065693.
Lemma F_5dca8 : fetch_word Ubsan.M.loaded_segments (0x5fa84 : word) = Some W_5dca8.
Proof. vm_refl. Qed.
Lemma D_5dca8 : decode_any W_5dca8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcac : bv 32 := 0x00d66633.
Lemma F_5dcac : fetch_word Ubsan.M.loaded_segments (0x5fa88 : word) = Some W_5dcac.
Proof. vm_refl. Qed.
Lemma D_5dcac : decode_any W_5dcac = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb0 : bv 32 := 0x01f00693.
Lemma F_5dcb0 : fetch_word Ubsan.M.loaded_segments (0x5fa8c : word) = Some W_5dcb0.
Proof. vm_refl. Qed.
Lemma D_5dcb0 : decode_any W_5dcb0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb4 : bv 32 := 0x00c5b023.
Lemma F_5dcb4 : fetch_word Ubsan.M.loaded_segments (0x5fa90 : word) = Some W_5dcb4.
Proof. vm_refl. Qed.
Lemma D_5dcb4 : decode_any W_5dcb4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcb8 : bv 32 := 0x00c5b423.
Lemma F_5dcb8 : fetch_word Ubsan.M.loaded_segments (0x5fa94 : word) = Some W_5dcb8.
Proof. vm_refl. Qed.
Lemma D_5dcb8 : decode_any W_5dcb8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcbc : bv 32 := 0x00c5b823.
Lemma F_5dcbc : fetch_word Ubsan.M.loaded_segments (0x5fa98 : word) = Some W_5dcbc.
Proof. vm_refl. Qed.
Lemma D_5dcbc : decode_any W_5dcbc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc0 : bv 32 := 0x00c5bc23.
Lemma F_5dcc0 : fetch_word Ubsan.M.loaded_segments (0x5fa9c : word) = Some W_5dcc0.
Proof. vm_refl. Qed.
Lemma D_5dcc0 : decode_any W_5dcc0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc4 : bv 32 := 0xfe070713.
Lemma F_5dcc4 : fetch_word Ubsan.M.loaded_segments (0x5faa0 : word) = Some W_5dcc4.
Proof. vm_refl. Qed.
Lemma D_5dcc4 : decode_any W_5dcc4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcc8 : bv 32 := 0x02058593.
Lemma F_5dcc8 : fetch_word Ubsan.M.loaded_segments (0x5faa4 : word) = Some W_5dcc8.
Proof. vm_refl. Qed.
Lemma D_5dcc8 : decode_any W_5dcc8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dccc : bv 32 := 0xfee6e4e3.
Lemma F_5dccc : fetch_word Ubsan.M.loaded_segments (0x5faa8 : word) = Some W_5dccc.
Proof. vm_refl. Qed.
Lemma D_5dccc : decode_any W_5dccc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5dcd0 : bv 32 := 0x00008067.
Lemma F_5dcd0 : fetch_word Ubsan.M.loaded_segments (0x5faac : word) = Some W_5dcd0.
Proof. vm_refl. Qed.
Lemma D_5dcd0 : decode_any W_5dcd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e048 : bv 32 := 0xfe010113.
Lemma F_5e048 : fetch_word Ubsan.M.loaded_segments (0x5fe24 : word) = Some W_5e048.
Proof. vm_refl. Qed.
Lemma D_5e048 : decode_any W_5e048 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e04c : bv 32 := 0x00113c23.
Lemma F_5e04c : fetch_word Ubsan.M.loaded_segments (0x5fe28 : word) = Some W_5e04c.
Proof. vm_refl. Qed.
Lemma D_5e04c : decode_any W_5e04c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e050 : bv 32 := 0x00813823.
Lemma F_5e050 : fetch_word Ubsan.M.loaded_segments (0x5fe2c : word) = Some W_5e050.
Proof. vm_refl. Qed.
Lemma D_5e050 : decode_any W_5e050 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e054 : bv 32 := 0x00913423.
Lemma F_5e054 : fetch_word Ubsan.M.loaded_segments (0x5fe30 : word) = Some W_5e054.
Proof. vm_refl. Qed.
Lemma D_5e054 : decode_any W_5e054 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e058 : bv 32 := 0x00058413.
Lemma F_5e058 : fetch_word Ubsan.M.loaded_segments (0x5fe34 : word) = Some W_5e058.
Proof. vm_refl. Qed.
Lemma D_5e058 : decode_any W_5e058 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e05c : bv 32 := 0x00050493.
Lemma F_5e05c : fetch_word Ubsan.M.loaded_segments (0x5fe38 : word) = Some W_5e05c.
Proof. vm_refl. Qed.
Lemma D_5e05c : decode_any W_5e05c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e060 : bv 32 := 0x00000593.
Lemma F_5e060 : fetch_word Ubsan.M.loaded_segments (0x5fe3c : word) = Some W_5e060.
Proof. vm_refl. Qed.
Lemma D_5e060 : decode_any W_5e060 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e064 : bv 32 := 0x00040613.
Lemma F_5e064 : fetch_word Ubsan.M.loaded_segments (0x5fe40 : word) = Some W_5e064.
Proof. vm_refl. Qed.
Lemma D_5e064 : decode_any W_5e064 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e068 : bv 32 := 0xcf8ff0ef.
Lemma F_5e068 : fetch_word Ubsan.M.loaded_segments (0x5fe44 : word) = Some W_5e068.
Proof. vm_refl. Qed.
Lemma D_5e068 : decode_any W_5e068 = Some (Jal 1 2094328, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e06c : bv 32 := 0x00050463.
Lemma F_5e06c : fetch_word Ubsan.M.loaded_segments (0x5fe48 : word) = Some W_5e06c.
Proof. vm_refl. Qed.
Lemma D_5e06c : decode_any W_5e06c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e070 : bv 32 := 0x40950433.
Lemma F_5e070 : fetch_word Ubsan.M.loaded_segments (0x5fe4c : word) = Some W_5e070.
Proof. vm_refl. Qed.
Lemma D_5e070 : decode_any W_5e070 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e074 : bv 32 := 0x00040513.
Lemma F_5e074 : fetch_word Ubsan.M.loaded_segments (0x5fe50 : word) = Some W_5e074.
Proof. vm_refl. Qed.
Lemma D_5e074 : decode_any W_5e074 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e078 : bv 32 := 0x01813083.
Lemma F_5e078 : fetch_word Ubsan.M.loaded_segments (0x5fe54 : word) = Some W_5e078.
Proof. vm_refl. Qed.
Lemma D_5e078 : decode_any W_5e078 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e07c : bv 32 := 0x01013403.
Lemma F_5e07c : fetch_word Ubsan.M.loaded_segments (0x5fe58 : word) = Some W_5e07c.
Proof. vm_refl. Qed.
Lemma D_5e07c : decode_any W_5e07c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e080 : bv 32 := 0x00813483.
Lemma F_5e080 : fetch_word Ubsan.M.loaded_segments (0x5fe5c : word) = Some W_5e080.
Proof. vm_refl. Qed.
Lemma D_5e080 : decode_any W_5e080 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e084 : bv 32 := 0x02010113.
Lemma F_5e084 : fetch_word Ubsan.M.loaded_segments (0x5fe60 : word) = Some W_5e084.
Proof. vm_refl. Qed.
Lemma D_5e084 : decode_any W_5e084 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5e088 : bv 32 := 0x00008067.
Lemma F_5e088 : fetch_word Ubsan.M.loaded_segments (0x5fe64 : word) = Some W_5e088.
Proof. vm_refl. Qed.
Lemma D_5e088 : decode_any W_5e088 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
