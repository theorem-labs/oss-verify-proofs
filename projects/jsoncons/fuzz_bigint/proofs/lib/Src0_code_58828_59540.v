(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_58828 : bv 32 := 0x0ff5f593.
Lemma F_58828 : fetch_word Plain.M.loaded_segments (0x58828 : word) = Some W_58828.
Proof. vm_refl. Qed.
Lemma D_58828 : decode_any W_58828 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5882c : bv 32 := 0x00757693.
Lemma F_5882c : fetch_word Plain.M.loaded_segments (0x5882c : word) = Some W_5882c.
Proof. vm_refl. Qed.
Lemma D_5882c : decode_any W_5882c = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_58830 : bv 32 := 0x00c03733.
Lemma F_58830 : fetch_word Plain.M.loaded_segments (0x58830 : word) = Some W_58830.
Proof. vm_refl. Qed.
Lemma D_58830 : decode_any W_58830 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58834 : bv 32 := 0x02068c63.
Lemma F_58834 : fetch_word Plain.M.loaded_segments (0x58834 : word) = Some W_58834.
Proof. vm_refl. Qed.
Lemma D_58834 : decode_any W_58834 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_58838 : bv 32 := 0x02060a63.
Lemma F_58838 : fetch_word Plain.M.loaded_segments (0x58838 : word) = Some W_58838.
Proof. vm_refl. Qed.
Lemma D_58838 : decode_any W_58838 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5883c : bv 32 := 0x00150793.
Lemma F_5883c : fetch_word Plain.M.loaded_segments (0x5883c : word) = Some W_5883c.
Proof. vm_refl. Qed.
Lemma D_5883c : decode_any W_5883c = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58840 : bv 32 := 0x00100813.
Lemma F_58840 : fetch_word Plain.M.loaded_segments (0x58840 : word) = Some W_58840.
Proof. vm_refl. Qed.
Lemma D_58840 : decode_any W_58840 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58844 : bv 32 := 0x00054703.
Lemma F_58844 : fetch_word Plain.M.loaded_segments (0x58844 : word) = Some W_58844.
Proof. vm_refl. Qed.
Lemma D_58844 : decode_any W_58844 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58848 : bv 32 := 0x00060693.
Lemma F_58848 : fetch_word Plain.M.loaded_segments (0x58848 : word) = Some W_58848.
Proof. vm_refl. Qed.
Lemma D_58848 : decode_any W_58848 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5884c : bv 32 := 0x06b70e63.
Lemma F_5884c : fetch_word Plain.M.loaded_segments (0x5884c : word) = Some W_5884c.
Proof. vm_refl. Qed.
Lemma D_5884c : decode_any W_5884c = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_58850 : bv 32 := 0x00150513.
Lemma F_58850 : fetch_word Plain.M.loaded_segments (0x58850 : word) = Some W_58850.
Proof. vm_refl. Qed.
Lemma D_58850 : decode_any W_58850 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58854 : bv 32 := 0xfff68613.
Lemma F_58854 : fetch_word Plain.M.loaded_segments (0x58854 : word) = Some W_58854.
Proof. vm_refl. Qed.
Lemma D_58854 : decode_any W_58854 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_58858 : bv 32 := 0x0077f893.
Lemma F_58858 : fetch_word Plain.M.loaded_segments (0x58858 : word) = Some W_58858.
Proof. vm_refl. Qed.
Lemma D_58858 : decode_any W_58858 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5885c : bv 32 := 0x00c03733.
Lemma F_5885c : fetch_word Plain.M.loaded_segments (0x5885c : word) = Some W_5885c.
Proof. vm_refl. Qed.
Lemma D_5885c : decode_any W_5885c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58860 : bv 32 := 0x00088663.
Lemma F_58860 : fetch_word Plain.M.loaded_segments (0x58860 : word) = Some W_58860.
Proof. vm_refl. Qed.
Lemma D_58860 : decode_any W_58860 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58864 : bv 32 := 0x00178793.
Lemma F_58864 : fetch_word Plain.M.loaded_segments (0x58864 : word) = Some W_58864.
Proof. vm_refl. Qed.
Lemma D_58864 : decode_any W_58864 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58868 : bv 32 := 0xfd069ee3.
Lemma F_58868 : fetch_word Plain.M.loaded_segments (0x58868 : word) = Some W_58868.
Proof. vm_refl. Qed.
Lemma D_58868 : decode_any W_58868 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5886c : bv 32 := 0x06070863.
Lemma F_5886c : fetch_word Plain.M.loaded_segments (0x5886c : word) = Some W_5886c.
Proof. vm_refl. Qed.
Lemma D_5886c : decode_any W_5886c = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_58870 : bv 32 := 0x00054683.
Lemma F_58870 : fetch_word Plain.M.loaded_segments (0x58870 : word) = Some W_58870.
Proof. vm_refl. Qed.
Lemma D_58870 : decode_any W_58870 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58874 : bv 32 := 0x04b68663.
Lemma F_58874 : fetch_word Plain.M.loaded_segments (0x58874 : word) = Some W_58874.
Proof. vm_refl. Qed.
Lemma D_58874 : decode_any W_58874 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_58878 : bv 32 := 0x00800693.
Lemma F_58878 : fetch_word Plain.M.loaded_segments (0x58878 : word) = Some W_58878.
Proof. vm_refl. Qed.
Lemma D_58878 : decode_any W_58878 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5887c : bv 32 := 0x04d66263.
Lemma F_5887c : fetch_word Plain.M.loaded_segments (0x5887c : word) = Some W_5887c.
Proof. vm_refl. Qed.
Lemma D_5887c : decode_any W_5887c = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_58880 : bv 32 := 0xfffbb697.
Lemma F_58880 : fetch_word Plain.M.loaded_segments (0x58880 : word) = Some W_58880.
Proof. vm_refl. Qed.
Lemma D_58880 : decode_any W_58880 = Some (Auipc 13 1048507, 4%Z).
Proof. vm_refl. Qed.

Definition W_58884 : bv 32 := 0x8a86b683.
Lemma F_58884 : fetch_word Plain.M.loaded_segments (0x58884 : word) = Some W_58884.
Proof. vm_refl. Qed.
Lemma D_58884 : decode_any W_58884 = Some (Load SZ8 true 13 13 2216, 4%Z).
Proof. vm_refl. Qed.

Definition W_58888 : bv 32 := 0xfffbb717.
Lemma F_58888 : fetch_word Plain.M.loaded_segments (0x58888 : word) = Some W_58888.
Proof. vm_refl. Qed.
Lemma D_58888 : decode_any W_58888 = Some (Auipc 14 1048507, 4%Z).
Proof. vm_refl. Qed.

Definition W_5888c : bv 32 := 0x89073703.
Lemma F_5888c : fetch_word Plain.M.loaded_segments (0x5888c : word) = Some W_5888c.
Proof. vm_refl. Qed.
Lemma D_5888c : decode_any W_5888c = Some (Load SZ8 true 14 14 2192, 4%Z).
Proof. vm_refl. Qed.

Definition W_58890 : bv 32 := 0x00168793.
Lemma F_58890 : fetch_word Plain.M.loaded_segments (0x58890 : word) = Some W_58890.
Proof. vm_refl. Qed.
Lemma D_58890 : decode_any W_58890 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58894 : bv 32 := 0x02f587b3.
Lemma F_58894 : fetch_word Plain.M.loaded_segments (0x58894 : word) = Some W_58894.
Proof. vm_refl. Qed.
Lemma D_58894 : decode_any W_58894 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58898 : bv 32 := 0x00700813.
Lemma F_58898 : fetch_word Plain.M.loaded_segments (0x58898 : word) = Some W_58898.
Proof. vm_refl. Qed.
Lemma D_58898 : decode_any W_58898 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5889c : bv 32 := 0x00053883.
Lemma F_5889c : fetch_word Plain.M.loaded_segments (0x5889c : word) = Some W_5889c.
Proof. vm_refl. Qed.
Lemma D_5889c : decode_any W_5889c = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_588a0 : bv 32 := 0x00f8c8b3.
Lemma F_588a0 : fetch_word Plain.M.loaded_segments (0x588a0 : word) = Some W_588a0.
Proof. vm_refl. Qed.
Lemma D_588a0 : decode_any W_588a0 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_588a4 : bv 32 := 0x411682b3.
Lemma F_588a4 : fetch_word Plain.M.loaded_segments (0x588a4 : word) = Some W_588a4.
Proof. vm_refl. Qed.
Lemma D_588a4 : decode_any W_588a4 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_588a8 : bv 32 := 0x0112e8b3.
Lemma F_588a8 : fetch_word Plain.M.loaded_segments (0x588a8 : word) = Some W_588a8.
Proof. vm_refl. Qed.
Lemma D_588a8 : decode_any W_588a8 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_588ac : bv 32 := 0x00e8f8b3.
Lemma F_588ac : fetch_word Plain.M.loaded_segments (0x588ac : word) = Some W_588ac.
Proof. vm_refl. Qed.
Lemma D_588ac : decode_any W_588ac = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_588b0 : bv 32 := 0x02e89a63.
Lemma F_588b0 : fetch_word Plain.M.loaded_segments (0x588b0 : word) = Some W_588b0.
Proof. vm_refl. Qed.
Lemma D_588b0 : decode_any W_588b0 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_588b4 : bv 32 := 0xff860613.
Lemma F_588b4 : fetch_word Plain.M.loaded_segments (0x588b4 : word) = Some W_588b4.
Proof. vm_refl. Qed.
Lemma D_588b4 : decode_any W_588b4 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_588b8 : bv 32 := 0x00850513.
Lemma F_588b8 : fetch_word Plain.M.loaded_segments (0x588b8 : word) = Some W_588b8.
Proof. vm_refl. Qed.
Lemma D_588b8 : decode_any W_588b8 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_588bc : bv 32 := 0xfec860e3.
Lemma F_588bc : fetch_word Plain.M.loaded_segments (0x588bc : word) = Some W_588bc.
Proof. vm_refl. Qed.
Lemma D_588bc : decode_any W_588bc = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_588c0 : bv 32 := 0x00060693.
Lemma F_588c0 : fetch_word Plain.M.loaded_segments (0x588c0 : word) = Some W_588c0.
Proof. vm_refl. Qed.
Lemma D_588c0 : decode_any W_588c0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_588c4 : bv 32 := 0x00060c63.
Lemma F_588c4 : fetch_word Plain.M.loaded_segments (0x588c4 : word) = Some W_588c4.
Proof. vm_refl. Qed.
Lemma D_588c4 : decode_any W_588c4 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_588c8 : bv 32 := 0x00054603.
Lemma F_588c8 : fetch_word Plain.M.loaded_segments (0x588c8 : word) = Some W_588c8.
Proof. vm_refl. Qed.
Lemma D_588c8 : decode_any W_588c8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_588cc : bv 32 := 0x00b60a63.
Lemma F_588cc : fetch_word Plain.M.loaded_segments (0x588cc : word) = Some W_588cc.
Proof. vm_refl. Qed.
Lemma D_588cc : decode_any W_588cc = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_588d0 : bv 32 := 0xfff68693.
Lemma F_588d0 : fetch_word Plain.M.loaded_segments (0x588d0 : word) = Some W_588d0.
Proof. vm_refl. Qed.
Lemma D_588d0 : decode_any W_588d0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_588d4 : bv 32 := 0x00150513.
Lemma F_588d4 : fetch_word Plain.M.loaded_segments (0x588d4 : word) = Some W_588d4.
Proof. vm_refl. Qed.
Lemma D_588d4 : decode_any W_588d4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_588d8 : bv 32 := 0xfe0698e3.
Lemma F_588d8 : fetch_word Plain.M.loaded_segments (0x588d8 : word) = Some W_588d8.
Proof. vm_refl. Qed.
Lemma D_588d8 : decode_any W_588d8 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_588e0 : bv 32 := 0x00008067.
Lemma F_588e0 : fetch_word Plain.M.loaded_segments (0x588e0 : word) = Some W_588e0.
Proof. vm_refl. Qed.
Lemma D_588e0 : decode_any W_588e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_588e4 : bv 32 := 0x00060693.
Lemma F_588e4 : fetch_word Plain.M.loaded_segments (0x588e4 : word) = Some W_588e4.
Proof. vm_refl. Qed.
Lemma D_588e4 : decode_any W_588e4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_588e8 : bv 32 := 0x00054603.
Lemma F_588e8 : fetch_word Plain.M.loaded_segments (0x588e8 : word) = Some W_588e8.
Proof. vm_refl. Qed.
Lemma D_588e8 : decode_any W_588e8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_588ec : bv 32 := 0xfeb612e3.
Lemma F_588ec : fetch_word Plain.M.loaded_segments (0x588ec : word) = Some W_588ec.
Proof. vm_refl. Qed.
Lemma D_588ec : decode_any W_588ec = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_588f0 : bv 32 := 0xff1ff06f.
Lemma F_588f0 : fetch_word Plain.M.loaded_segments (0x588f0 : word) = Some W_588f0.
Proof. vm_refl. Qed.
Lemma D_588f0 : decode_any W_588f0 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_58924 : bv 32 := 0x0035f693.
Lemma F_58924 : fetch_word Plain.M.loaded_segments (0x58924 : word) = Some W_58924.
Proof. vm_refl. Qed.
Lemma D_58924 : decode_any W_58924 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58928 : bv 32 := 0x10068863.
Lemma F_58928 : fetch_word Plain.M.loaded_segments (0x58928 : word) = Some W_58928.
Proof. vm_refl. Qed.
Lemma D_58928 : decode_any W_58928 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_5892c : bv 32 := 0x02060e63.
Lemma F_5892c : fetch_word Plain.M.loaded_segments (0x5892c : word) = Some W_5892c.
Proof. vm_refl. Qed.
Lemma D_5892c : decode_any W_5892c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_58930 : bv 32 := 0x00158713.
Lemma F_58930 : fetch_word Plain.M.loaded_segments (0x58930 : word) = Some W_58930.
Proof. vm_refl. Qed.
Lemma D_58930 : decode_any W_58930 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58934 : bv 32 := 0x00100793.
Lemma F_58934 : fetch_word Plain.M.loaded_segments (0x58934 : word) = Some W_58934.
Proof. vm_refl. Qed.
Lemma D_58934 : decode_any W_58934 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58938 : bv 32 := 0x00050693.
Lemma F_58938 : fetch_word Plain.M.loaded_segments (0x58938 : word) = Some W_58938.
Proof. vm_refl. Qed.
Lemma D_58938 : decode_any W_58938 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5893c : bv 32 := 0x0005c883.
Lemma F_5893c : fetch_word Plain.M.loaded_segments (0x5893c : word) = Some W_5893c.
Proof. vm_refl. Qed.
Lemma D_5893c : decode_any W_5893c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58940 : bv 32 := 0x00060813.
Lemma F_58940 : fetch_word Plain.M.loaded_segments (0x58940 : word) = Some W_58940.
Proof. vm_refl. Qed.
Lemma D_58940 : decode_any W_58940 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58944 : bv 32 := 0x00158593.
Lemma F_58944 : fetch_word Plain.M.loaded_segments (0x58944 : word) = Some W_58944.
Proof. vm_refl. Qed.
Lemma D_58944 : decode_any W_58944 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58948 : bv 32 := 0x00377293.
Lemma F_58948 : fetch_word Plain.M.loaded_segments (0x58948 : word) = Some W_58948.
Proof. vm_refl. Qed.
Lemma D_58948 : decode_any W_58948 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5894c : bv 32 := 0x01168023.
Lemma F_5894c : fetch_word Plain.M.loaded_segments (0x5894c : word) = Some W_5894c.
Proof. vm_refl. Qed.
Lemma D_5894c : decode_any W_5894c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58950 : bv 32 := 0x00168693.
Lemma F_58950 : fetch_word Plain.M.loaded_segments (0x58950 : word) = Some W_58950.
Proof. vm_refl. Qed.
Lemma D_58950 : decode_any W_58950 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58954 : bv 32 := 0xfff60613.
Lemma F_58954 : fetch_word Plain.M.loaded_segments (0x58954 : word) = Some W_58954.
Proof. vm_refl. Qed.
Lemma D_58954 : decode_any W_58954 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_58958 : bv 32 := 0x00028a63.
Lemma F_58958 : fetch_word Plain.M.loaded_segments (0x58958 : word) = Some W_58958.
Proof. vm_refl. Qed.
Lemma D_58958 : decode_any W_58958 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5895c : bv 32 := 0x00170713.
Lemma F_5895c : fetch_word Plain.M.loaded_segments (0x5895c : word) = Some W_5895c.
Proof. vm_refl. Qed.
Lemma D_5895c : decode_any W_5895c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58960 : bv 32 := 0xfcf81ee3.
Lemma F_58960 : fetch_word Plain.M.loaded_segments (0x58960 : word) = Some W_58960.
Proof. vm_refl. Qed.
Lemma D_58960 : decode_any W_58960 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_58964 : bv 32 := 0x0080006f.
Lemma F_58964 : fetch_word Plain.M.loaded_segments (0x58964 : word) = Some W_58964.
Proof. vm_refl. Qed.
Lemma D_58964 : decode_any W_58964 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58968 : bv 32 := 0x00050693.
Lemma F_58968 : fetch_word Plain.M.loaded_segments (0x58968 : word) = Some W_58968.
Proof. vm_refl. Qed.
Lemma D_58968 : decode_any W_58968 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5896c : bv 32 := 0x0036f793.
Lemma F_5896c : fetch_word Plain.M.loaded_segments (0x5896c : word) = Some W_5896c.
Proof. vm_refl. Qed.
Lemma D_5896c : decode_any W_5896c = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58970 : bv 32 := 0x0c078a63.
Lemma F_58970 : fetch_word Plain.M.loaded_segments (0x58970 : word) = Some W_58970.
Proof. vm_refl. Qed.
Lemma D_58970 : decode_any W_58970 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_58974 : bv 32 := 0x02000713.
Lemma F_58974 : fetch_word Plain.M.loaded_segments (0x58974 : word) = Some W_58974.
Proof. vm_refl. Qed.
Lemma D_58974 : decode_any W_58974 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58978 : bv 32 := 0x02e67063.
Lemma F_58978 : fetch_word Plain.M.loaded_segments (0x58978 : word) = Some W_58978.
Proof. vm_refl. Qed.
Lemma D_58978 : decode_any W_58978 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5897c : bv 32 := 0x01000713.
Lemma F_5897c : fetch_word Plain.M.loaded_segments (0x5897c : word) = Some W_5897c.
Proof. vm_refl. Qed.
Lemma D_5897c : decode_any W_5897c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58980 : bv 32 := 0x24e67863.
Lemma F_58980 : fetch_word Plain.M.loaded_segments (0x58980 : word) = Some W_58980.
Proof. vm_refl. Qed.
Lemma D_58980 : decode_any W_58980 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_58984 : bv 32 := 0x00867713.
Lemma F_58984 : fetch_word Plain.M.loaded_segments (0x58984 : word) = Some W_58984.
Proof. vm_refl. Qed.
Lemma D_58984 : decode_any W_58984 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58988 : bv 32 := 0x2c071e63.
Lemma F_58988 : fetch_word Plain.M.loaded_segments (0x58988 : word) = Some W_58988.
Proof. vm_refl. Qed.
Lemma D_58988 : decode_any W_58988 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_5898c : bv 32 := 0x00467713.
Lemma F_5898c : fetch_word Plain.M.loaded_segments (0x5898c : word) = Some W_5898c.
Proof. vm_refl. Qed.
Lemma D_5898c : decode_any W_5898c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58990 : bv 32 := 0x32071463.
Lemma F_58990 : fetch_word Plain.M.loaded_segments (0x58990 : word) = Some W_58990.
Proof. vm_refl. Qed.
Lemma D_58990 : decode_any W_58990 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_58994 : bv 32 := 0x3500006f.
Lemma F_58994 : fetch_word Plain.M.loaded_segments (0x58994 : word) = Some W_58994.
Proof. vm_refl. Qed.
Lemma D_58994 : decode_any W_58994 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_58998 : bv 32 := 0x0005a703.
Lemma F_58998 : fetch_word Plain.M.loaded_segments (0x58998 : word) = Some W_58998.
Proof. vm_refl. Qed.
Lemma D_58998 : decode_any W_58998 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5899c : bv 32 := 0x00300813.
Lemma F_5899c : fetch_word Plain.M.loaded_segments (0x5899c : word) = Some W_5899c.
Proof. vm_refl. Qed.
Lemma D_5899c : decode_any W_5899c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_589a0 : bv 32 := 0x11078e63.
Lemma F_589a0 : fetch_word Plain.M.loaded_segments (0x589a0 : word) = Some W_589a0.
Proof. vm_refl. Qed.
Lemma D_589a0 : decode_any W_589a0 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_589a4 : bv 32 := 0x00200813.
Lemma F_589a4 : fetch_word Plain.M.loaded_segments (0x589a4 : word) = Some W_589a4.
Proof. vm_refl. Qed.
Lemma D_589a4 : decode_any W_589a4 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_589a8 : bv 32 := 0x19079c63.
Lemma F_589a8 : fetch_word Plain.M.loaded_segments (0x589a8 : word) = Some W_589a8.
Proof. vm_refl. Qed.
Lemma D_589a8 : decode_any W_589a8 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_589ac : bv 32 := 0x00875793.
Lemma F_589ac : fetch_word Plain.M.loaded_segments (0x589ac : word) = Some W_589ac.
Proof. vm_refl. Qed.
Lemma D_589ac : decode_any W_589ac = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_589b0 : bv 32 := 0xffe60613.
Lemma F_589b0 : fetch_word Plain.M.loaded_segments (0x589b0 : word) = Some W_589b0.
Proof. vm_refl. Qed.
Lemma D_589b0 : decode_any W_589b0 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_589b4 : bv 32 := 0x00e68023.
Lemma F_589b4 : fetch_word Plain.M.loaded_segments (0x589b4 : word) = Some W_589b4.
Proof. vm_refl. Qed.
Lemma D_589b4 : decode_any W_589b4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_589b8 : bv 32 := 0x00f680a3.
Lemma F_589b8 : fetch_word Plain.M.loaded_segments (0x589b8 : word) = Some W_589b8.
Proof. vm_refl. Qed.
Lemma D_589b8 : decode_any W_589b8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_589bc : bv 32 := 0x00268693.
Lemma F_589bc : fetch_word Plain.M.loaded_segments (0x589bc : word) = Some W_589bc.
Proof. vm_refl. Qed.
Lemma D_589bc : decode_any W_589bc = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_589c0 : bv 32 := 0x01058593.
Lemma F_589c0 : fetch_word Plain.M.loaded_segments (0x589c0 : word) = Some W_589c0.
Proof. vm_refl. Qed.
Lemma D_589c0 : decode_any W_589c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589c4 : bv 32 := 0x01100793.
Lemma F_589c4 : fetch_word Plain.M.loaded_segments (0x589c4 : word) = Some W_589c4.
Proof. vm_refl. Qed.
Lemma D_589c4 : decode_any W_589c4 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_589c8 : bv 32 := 0x0107581b.
Lemma F_589c8 : fetch_word Plain.M.loaded_segments (0x589c8 : word) = Some W_589c8.
Proof. vm_refl. Qed.
Lemma D_589c8 : decode_any W_589c8 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589cc : bv 32 := 0xff45a883.
Lemma F_589cc : fetch_word Plain.M.loaded_segments (0x589cc : word) = Some W_589cc.
Proof. vm_refl. Qed.
Lemma D_589cc : decode_any W_589cc = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_589d0 : bv 32 := 0xff85a283.
Lemma F_589d0 : fetch_word Plain.M.loaded_segments (0x589d0 : word) = Some W_589d0.
Proof. vm_refl. Qed.
Lemma D_589d0 : decode_any W_589d0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_589d4 : bv 32 := 0xffc5a303.
Lemma F_589d4 : fetch_word Plain.M.loaded_segments (0x589d4 : word) = Some W_589d4.
Proof. vm_refl. Qed.
Lemma D_589d4 : decode_any W_589d4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_589d8 : bv 32 := 0x0005a703.
Lemma F_589d8 : fetch_word Plain.M.loaded_segments (0x589d8 : word) = Some W_589d8.
Proof. vm_refl. Qed.
Lemma D_589d8 : decode_any W_589d8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_589dc : bv 32 := 0x01089393.
Lemma F_589dc : fetch_word Plain.M.loaded_segments (0x589dc : word) = Some W_589dc.
Proof. vm_refl. Qed.
Lemma D_589dc : decode_any W_589dc = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589e0 : bv 32 := 0x0108d89b.
Lemma F_589e0 : fetch_word Plain.M.loaded_segments (0x589e0 : word) = Some W_589e0.
Proof. vm_refl. Qed.
Lemma D_589e0 : decode_any W_589e0 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589e4 : bv 32 := 0x0103e833.
Lemma F_589e4 : fetch_word Plain.M.loaded_segments (0x589e4 : word) = Some W_589e4.
Proof. vm_refl. Qed.
Lemma D_589e4 : decode_any W_589e4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589e8 : bv 32 := 0x01029393.
Lemma F_589e8 : fetch_word Plain.M.loaded_segments (0x589e8 : word) = Some W_589e8.
Proof. vm_refl. Qed.
Lemma D_589e8 : decode_any W_589e8 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589ec : bv 32 := 0x0102d29b.
Lemma F_589ec : fetch_word Plain.M.loaded_segments (0x589ec : word) = Some W_589ec.
Proof. vm_refl. Qed.
Lemma D_589ec : decode_any W_589ec = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589f0 : bv 32 := 0x0113e8b3.
Lemma F_589f0 : fetch_word Plain.M.loaded_segments (0x589f0 : word) = Some W_589f0.
Proof. vm_refl. Qed.
Lemma D_589f0 : decode_any W_589f0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_589f4 : bv 32 := 0x01031393.
Lemma F_589f4 : fetch_word Plain.M.loaded_segments (0x589f4 : word) = Some W_589f4.
Proof. vm_refl. Qed.
Lemma D_589f4 : decode_any W_589f4 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589f8 : bv 32 := 0x0103531b.
Lemma F_589f8 : fetch_word Plain.M.loaded_segments (0x589f8 : word) = Some W_589f8.
Proof. vm_refl. Qed.
Lemma D_589f8 : decode_any W_589f8 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_589fc : bv 32 := 0x0053e2b3.
Lemma F_589fc : fetch_word Plain.M.loaded_segments (0x589fc : word) = Some W_589fc.
Proof. vm_refl. Qed.
Lemma D_589fc : decode_any W_589fc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a00 : bv 32 := 0x01071393.
Lemma F_58a00 : fetch_word Plain.M.loaded_segments (0x58a00 : word) = Some W_58a00.
Proof. vm_refl. Qed.
Lemma D_58a00 : decode_any W_58a00 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a04 : bv 32 := 0x0063e333.
Lemma F_58a04 : fetch_word Plain.M.loaded_segments (0x58a04 : word) = Some W_58a04.
Proof. vm_refl. Qed.
Lemma D_58a04 : decode_any W_58a04 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a08 : bv 32 := 0xff060613.
Lemma F_58a08 : fetch_word Plain.M.loaded_segments (0x58a08 : word) = Some W_58a08.
Proof. vm_refl. Qed.
Lemma D_58a08 : decode_any W_58a08 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a0c : bv 32 := 0x0106a023.
Lemma F_58a0c : fetch_word Plain.M.loaded_segments (0x58a0c : word) = Some W_58a0c.
Proof. vm_refl. Qed.
Lemma D_58a0c : decode_any W_58a0c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a10 : bv 32 := 0x0116a223.
Lemma F_58a10 : fetch_word Plain.M.loaded_segments (0x58a10 : word) = Some W_58a10.
Proof. vm_refl. Qed.
Lemma D_58a10 : decode_any W_58a10 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a14 : bv 32 := 0x0056a423.
Lemma F_58a14 : fetch_word Plain.M.loaded_segments (0x58a14 : word) = Some W_58a14.
Proof. vm_refl. Qed.
Lemma D_58a14 : decode_any W_58a14 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a18 : bv 32 := 0x0066a623.
Lemma F_58a18 : fetch_word Plain.M.loaded_segments (0x58a18 : word) = Some W_58a18.
Proof. vm_refl. Qed.
Lemma D_58a18 : decode_any W_58a18 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a1c : bv 32 := 0x01068693.
Lemma F_58a1c : fetch_word Plain.M.loaded_segments (0x58a1c : word) = Some W_58a1c.
Proof. vm_refl. Qed.
Lemma D_58a1c : decode_any W_58a1c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a20 : bv 32 := 0x01058593.
Lemma F_58a20 : fetch_word Plain.M.loaded_segments (0x58a20 : word) = Some W_58a20.
Proof. vm_refl. Qed.
Lemma D_58a20 : decode_any W_58a20 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a24 : bv 32 := 0xfac7e2e3.
Lemma F_58a24 : fetch_word Plain.M.loaded_segments (0x58a24 : word) = Some W_58a24.
Proof. vm_refl. Qed.
Lemma D_58a24 : decode_any W_58a24 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a28 : bv 32 := 0xff258593.
Lemma F_58a28 : fetch_word Plain.M.loaded_segments (0x58a28 : word) = Some W_58a28.
Proof. vm_refl. Qed.
Lemma D_58a28 : decode_any W_58a28 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a2c : bv 32 := 0x01000713.
Lemma F_58a2c : fetch_word Plain.M.loaded_segments (0x58a2c : word) = Some W_58a2c.
Proof. vm_refl. Qed.
Lemma D_58a2c : decode_any W_58a2c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a30 : bv 32 := 0xf4e66ae3.
Lemma F_58a30 : fetch_word Plain.M.loaded_segments (0x58a30 : word) = Some W_58a30.
Proof. vm_refl. Qed.
Lemma D_58a30 : decode_any W_58a30 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a34 : bv 32 := 0x19c0006f.
Lemma F_58a34 : fetch_word Plain.M.loaded_segments (0x58a34 : word) = Some W_58a34.
Proof. vm_refl. Qed.
Lemma D_58a34 : decode_any W_58a34 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a38 : bv 32 := 0x00050693.
Lemma F_58a38 : fetch_word Plain.M.loaded_segments (0x58a38 : word) = Some W_58a38.
Proof. vm_refl. Qed.
Lemma D_58a38 : decode_any W_58a38 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a3c : bv 32 := 0x00357793.
Lemma F_58a3c : fetch_word Plain.M.loaded_segments (0x58a3c : word) = Some W_58a3c.
Proof. vm_refl. Qed.
Lemma D_58a3c : decode_any W_58a3c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a40 : bv 32 := 0xf2079ae3.
Lemma F_58a40 : fetch_word Plain.M.loaded_segments (0x58a40 : word) = Some W_58a40.
Proof. vm_refl. Qed.
Lemma D_58a40 : decode_any W_58a40 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a44 : bv 32 := 0x01000713.
Lemma F_58a44 : fetch_word Plain.M.loaded_segments (0x58a44 : word) = Some W_58a44.
Proof. vm_refl. Qed.
Lemma D_58a44 : decode_any W_58a44 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a48 : bv 32 := 0x02e66c63.
Lemma F_58a48 : fetch_word Plain.M.loaded_segments (0x58a48 : word) = Some W_58a48.
Proof. vm_refl. Qed.
Lemma D_58a48 : decode_any W_58a48 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a4c : bv 32 := 0x00f00713.
Lemma F_58a4c : fetch_word Plain.M.loaded_segments (0x58a4c : word) = Some W_58a4c.
Proof. vm_refl. Qed.
Lemma D_58a4c : decode_any W_58a4c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a50 : bv 32 := 0x0005a783.
Lemma F_58a50 : fetch_word Plain.M.loaded_segments (0x58a50 : word) = Some W_58a50.
Proof. vm_refl. Qed.
Lemma D_58a50 : decode_any W_58a50 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a54 : bv 32 := 0x0045a803.
Lemma F_58a54 : fetch_word Plain.M.loaded_segments (0x58a54 : word) = Some W_58a54.
Proof. vm_refl. Qed.
Lemma D_58a54 : decode_any W_58a54 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a58 : bv 32 := 0x0085a883.
Lemma F_58a58 : fetch_word Plain.M.loaded_segments (0x58a58 : word) = Some W_58a58.
Proof. vm_refl. Qed.
Lemma D_58a58 : decode_any W_58a58 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a5c : bv 32 := 0x00c5a283.
Lemma F_58a5c : fetch_word Plain.M.loaded_segments (0x58a5c : word) = Some W_58a5c.
Proof. vm_refl. Qed.
Lemma D_58a5c : decode_any W_58a5c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a60 : bv 32 := 0x01058593.
Lemma F_58a60 : fetch_word Plain.M.loaded_segments (0x58a60 : word) = Some W_58a60.
Proof. vm_refl. Qed.
Lemma D_58a60 : decode_any W_58a60 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a64 : bv 32 := 0xff060613.
Lemma F_58a64 : fetch_word Plain.M.loaded_segments (0x58a64 : word) = Some W_58a64.
Proof. vm_refl. Qed.
Lemma D_58a64 : decode_any W_58a64 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a68 : bv 32 := 0x00f6a023.
Lemma F_58a68 : fetch_word Plain.M.loaded_segments (0x58a68 : word) = Some W_58a68.
Proof. vm_refl. Qed.
Lemma D_58a68 : decode_any W_58a68 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a6c : bv 32 := 0x0106a223.
Lemma F_58a6c : fetch_word Plain.M.loaded_segments (0x58a6c : word) = Some W_58a6c.
Proof. vm_refl. Qed.
Lemma D_58a6c : decode_any W_58a6c = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a70 : bv 32 := 0x0116a423.
Lemma F_58a70 : fetch_word Plain.M.loaded_segments (0x58a70 : word) = Some W_58a70.
Proof. vm_refl. Qed.
Lemma D_58a70 : decode_any W_58a70 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a74 : bv 32 := 0x0056a623.
Lemma F_58a74 : fetch_word Plain.M.loaded_segments (0x58a74 : word) = Some W_58a74.
Proof. vm_refl. Qed.
Lemma D_58a74 : decode_any W_58a74 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a78 : bv 32 := 0x01068693.
Lemma F_58a78 : fetch_word Plain.M.loaded_segments (0x58a78 : word) = Some W_58a78.
Proof. vm_refl. Qed.
Lemma D_58a78 : decode_any W_58a78 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a7c : bv 32 := 0xfcc76ae3.
Lemma F_58a7c : fetch_word Plain.M.loaded_segments (0x58a7c : word) = Some W_58a7c.
Proof. vm_refl. Qed.
Lemma D_58a7c : decode_any W_58a7c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a80 : bv 32 := 0x00800713.
Lemma F_58a80 : fetch_word Plain.M.loaded_segments (0x58a80 : word) = Some W_58a80.
Proof. vm_refl. Qed.
Lemma D_58a80 : decode_any W_58a80 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a84 : bv 32 := 0x00e66e63.
Lemma F_58a84 : fetch_word Plain.M.loaded_segments (0x58a84 : word) = Some W_58a84.
Proof. vm_refl. Qed.
Lemma D_58a84 : decode_any W_58a84 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a88 : bv 32 := 0x0005a703.
Lemma F_58a88 : fetch_word Plain.M.loaded_segments (0x58a88 : word) = Some W_58a88.
Proof. vm_refl. Qed.
Lemma D_58a88 : decode_any W_58a88 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a8c : bv 32 := 0x0045a783.
Lemma F_58a8c : fetch_word Plain.M.loaded_segments (0x58a8c : word) = Some W_58a8c.
Proof. vm_refl. Qed.
Lemma D_58a8c : decode_any W_58a8c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a90 : bv 32 := 0x00e6a023.
Lemma F_58a90 : fetch_word Plain.M.loaded_segments (0x58a90 : word) = Some W_58a90.
Proof. vm_refl. Qed.
Lemma D_58a90 : decode_any W_58a90 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a94 : bv 32 := 0x00f6a223.
Lemma F_58a94 : fetch_word Plain.M.loaded_segments (0x58a94 : word) = Some W_58a94.
Proof. vm_refl. Qed.
Lemma D_58a94 : decode_any W_58a94 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a98 : bv 32 := 0x00868693.
Lemma F_58a98 : fetch_word Plain.M.loaded_segments (0x58a98 : word) = Some W_58a98.
Proof. vm_refl. Qed.
Lemma D_58a98 : decode_any W_58a98 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58a9c : bv 32 := 0x00858593.
Lemma F_58a9c : fetch_word Plain.M.loaded_segments (0x58a9c : word) = Some W_58a9c.
Proof. vm_refl. Qed.
Lemma D_58a9c : decode_any W_58a9c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58aa0 : bv 32 := 0x00467713.
Lemma F_58aa0 : fetch_word Plain.M.loaded_segments (0x58aa0 : word) = Some W_58aa0.
Proof. vm_refl. Qed.
Lemma D_58aa0 : decode_any W_58aa0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58aa4 : bv 32 := 0x24070063.
Lemma F_58aa4 : fetch_word Plain.M.loaded_segments (0x58aa4 : word) = Some W_58aa4.
Proof. vm_refl. Qed.
Lemma D_58aa4 : decode_any W_58aa4 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_58aa8 : bv 32 := 0x0005a703.
Lemma F_58aa8 : fetch_word Plain.M.loaded_segments (0x58aa8 : word) = Some W_58aa8.
Proof. vm_refl. Qed.
Lemma D_58aa8 : decode_any W_58aa8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58aac : bv 32 := 0x00458593.
Lemma F_58aac : fetch_word Plain.M.loaded_segments (0x58aac : word) = Some W_58aac.
Proof. vm_refl. Qed.
Lemma D_58aac : decode_any W_58aac = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ab0 : bv 32 := 0x00e6a023.
Lemma F_58ab0 : fetch_word Plain.M.loaded_segments (0x58ab0 : word) = Some W_58ab0.
Proof. vm_refl. Qed.
Lemma D_58ab0 : decode_any W_58ab0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ab4 : bv 32 := 0x00468693.
Lemma F_58ab4 : fetch_word Plain.M.loaded_segments (0x58ab4 : word) = Some W_58ab4.
Proof. vm_refl. Qed.
Lemma D_58ab4 : decode_any W_58ab4 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ab8 : bv 32 := 0x22c0006f.
Lemma F_58ab8 : fetch_word Plain.M.loaded_segments (0x58ab8 : word) = Some W_58ab8.
Proof. vm_refl. Qed.
Lemma D_58ab8 : decode_any W_58ab8 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_58abc : bv 32 := 0x00e68023.
Lemma F_58abc : fetch_word Plain.M.loaded_segments (0x58abc : word) = Some W_58abc.
Proof. vm_refl. Qed.
Lemma D_58abc : decode_any W_58abc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ac0 : bv 32 := 0x00168693.
Lemma F_58ac0 : fetch_word Plain.M.loaded_segments (0x58ac0 : word) = Some W_58ac0.
Proof. vm_refl. Qed.
Lemma D_58ac0 : decode_any W_58ac0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ac4 : bv 32 := 0xfff60613.
Lemma F_58ac4 : fetch_word Plain.M.loaded_segments (0x58ac4 : word) = Some W_58ac4.
Proof. vm_refl. Qed.
Lemma D_58ac4 : decode_any W_58ac4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ac8 : bv 32 := 0x01058593.
Lemma F_58ac8 : fetch_word Plain.M.loaded_segments (0x58ac8 : word) = Some W_58ac8.
Proof. vm_refl. Qed.
Lemma D_58ac8 : decode_any W_58ac8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58acc : bv 32 := 0x01200793.
Lemma F_58acc : fetch_word Plain.M.loaded_segments (0x58acc : word) = Some W_58acc.
Proof. vm_refl. Qed.
Lemma D_58acc : decode_any W_58acc = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ad0 : bv 32 := 0x0087581b.
Lemma F_58ad0 : fetch_word Plain.M.loaded_segments (0x58ad0 : word) = Some W_58ad0.
Proof. vm_refl. Qed.
Lemma D_58ad0 : decode_any W_58ad0 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ad4 : bv 32 := 0xff45a883.
Lemma F_58ad4 : fetch_word Plain.M.loaded_segments (0x58ad4 : word) = Some W_58ad4.
Proof. vm_refl. Qed.
Lemma D_58ad4 : decode_any W_58ad4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ad8 : bv 32 := 0xff85a283.
Lemma F_58ad8 : fetch_word Plain.M.loaded_segments (0x58ad8 : word) = Some W_58ad8.
Proof. vm_refl. Qed.
Lemma D_58ad8 : decode_any W_58ad8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_58adc : bv 32 := 0xffc5a303.
Lemma F_58adc : fetch_word Plain.M.loaded_segments (0x58adc : word) = Some W_58adc.
Proof. vm_refl. Qed.
Lemma D_58adc : decode_any W_58adc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ae0 : bv 32 := 0x0005a703.
Lemma F_58ae0 : fetch_word Plain.M.loaded_segments (0x58ae0 : word) = Some W_58ae0.
Proof. vm_refl. Qed.
Lemma D_58ae0 : decode_any W_58ae0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ae4 : bv 32 := 0x01889393.
Lemma F_58ae4 : fetch_word Plain.M.loaded_segments (0x58ae4 : word) = Some W_58ae4.
Proof. vm_refl. Qed.
Lemma D_58ae4 : decode_any W_58ae4 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ae8 : bv 32 := 0x0088d89b.
Lemma F_58ae8 : fetch_word Plain.M.loaded_segments (0x58ae8 : word) = Some W_58ae8.
Proof. vm_refl. Qed.
Lemma D_58ae8 : decode_any W_58ae8 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58aec : bv 32 := 0x0103e833.
Lemma F_58aec : fetch_word Plain.M.loaded_segments (0x58aec : word) = Some W_58aec.
Proof. vm_refl. Qed.
Lemma D_58aec : decode_any W_58aec = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58af0 : bv 32 := 0x01829393.
Lemma F_58af0 : fetch_word Plain.M.loaded_segments (0x58af0 : word) = Some W_58af0.
Proof. vm_refl. Qed.
Lemma D_58af0 : decode_any W_58af0 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58af4 : bv 32 := 0x0082d29b.
Lemma F_58af4 : fetch_word Plain.M.loaded_segments (0x58af4 : word) = Some W_58af4.
Proof. vm_refl. Qed.
Lemma D_58af4 : decode_any W_58af4 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58af8 : bv 32 := 0x0113e8b3.
Lemma F_58af8 : fetch_word Plain.M.loaded_segments (0x58af8 : word) = Some W_58af8.
Proof. vm_refl. Qed.
Lemma D_58af8 : decode_any W_58af8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_58afc : bv 32 := 0x01831393.
Lemma F_58afc : fetch_word Plain.M.loaded_segments (0x58afc : word) = Some W_58afc.
Proof. vm_refl. Qed.
Lemma D_58afc : decode_any W_58afc = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b00 : bv 32 := 0x0083531b.
Lemma F_58b00 : fetch_word Plain.M.loaded_segments (0x58b00 : word) = Some W_58b00.
Proof. vm_refl. Qed.
Lemma D_58b00 : decode_any W_58b00 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b04 : bv 32 := 0x0053e2b3.
Lemma F_58b04 : fetch_word Plain.M.loaded_segments (0x58b04 : word) = Some W_58b04.
Proof. vm_refl. Qed.
Lemma D_58b04 : decode_any W_58b04 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b08 : bv 32 := 0x01871393.
Lemma F_58b08 : fetch_word Plain.M.loaded_segments (0x58b08 : word) = Some W_58b08.
Proof. vm_refl. Qed.
Lemma D_58b08 : decode_any W_58b08 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b0c : bv 32 := 0x0063e333.
Lemma F_58b0c : fetch_word Plain.M.loaded_segments (0x58b0c : word) = Some W_58b0c.
Proof. vm_refl. Qed.
Lemma D_58b0c : decode_any W_58b0c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b10 : bv 32 := 0xff060613.
Lemma F_58b10 : fetch_word Plain.M.loaded_segments (0x58b10 : word) = Some W_58b10.
Proof. vm_refl. Qed.
Lemma D_58b10 : decode_any W_58b10 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b14 : bv 32 := 0x0106a023.
Lemma F_58b14 : fetch_word Plain.M.loaded_segments (0x58b14 : word) = Some W_58b14.
Proof. vm_refl. Qed.
Lemma D_58b14 : decode_any W_58b14 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b18 : bv 32 := 0x0116a223.
Lemma F_58b18 : fetch_word Plain.M.loaded_segments (0x58b18 : word) = Some W_58b18.
Proof. vm_refl. Qed.
Lemma D_58b18 : decode_any W_58b18 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b1c : bv 32 := 0x0056a423.
Lemma F_58b1c : fetch_word Plain.M.loaded_segments (0x58b1c : word) = Some W_58b1c.
Proof. vm_refl. Qed.
Lemma D_58b1c : decode_any W_58b1c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b20 : bv 32 := 0x0066a623.
Lemma F_58b20 : fetch_word Plain.M.loaded_segments (0x58b20 : word) = Some W_58b20.
Proof. vm_refl. Qed.
Lemma D_58b20 : decode_any W_58b20 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b24 : bv 32 := 0x01068693.
Lemma F_58b24 : fetch_word Plain.M.loaded_segments (0x58b24 : word) = Some W_58b24.
Proof. vm_refl. Qed.
Lemma D_58b24 : decode_any W_58b24 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b28 : bv 32 := 0x01058593.
Lemma F_58b28 : fetch_word Plain.M.loaded_segments (0x58b28 : word) = Some W_58b28.
Proof. vm_refl. Qed.
Lemma D_58b28 : decode_any W_58b28 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b2c : bv 32 := 0xfac7e2e3.
Lemma F_58b2c : fetch_word Plain.M.loaded_segments (0x58b2c : word) = Some W_58b2c.
Proof. vm_refl. Qed.
Lemma D_58b2c : decode_any W_58b2c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b30 : bv 32 := 0xff158593.
Lemma F_58b30 : fetch_word Plain.M.loaded_segments (0x58b30 : word) = Some W_58b30.
Proof. vm_refl. Qed.
Lemma D_58b30 : decode_any W_58b30 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b34 : bv 32 := 0x01000713.
Lemma F_58b34 : fetch_word Plain.M.loaded_segments (0x58b34 : word) = Some W_58b34.
Proof. vm_refl. Qed.
Lemma D_58b34 : decode_any W_58b34 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b38 : bv 32 := 0xe4e666e3.
Lemma F_58b38 : fetch_word Plain.M.loaded_segments (0x58b38 : word) = Some W_58b38.
Proof. vm_refl. Qed.
Lemma D_58b38 : decode_any W_58b38 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b3c : bv 32 := 0x0940006f.
Lemma F_58b3c : fetch_word Plain.M.loaded_segments (0x58b3c : word) = Some W_58b3c.
Proof. vm_refl. Qed.
Lemma D_58b3c : decode_any W_58b3c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b40 : bv 32 := 0x00875793.
Lemma F_58b40 : fetch_word Plain.M.loaded_segments (0x58b40 : word) = Some W_58b40.
Proof. vm_refl. Qed.
Lemma D_58b40 : decode_any W_58b40 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b44 : bv 32 := 0x01075813.
Lemma F_58b44 : fetch_word Plain.M.loaded_segments (0x58b44 : word) = Some W_58b44.
Proof. vm_refl. Qed.
Lemma D_58b44 : decode_any W_58b44 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b48 : bv 32 := 0xffd60613.
Lemma F_58b48 : fetch_word Plain.M.loaded_segments (0x58b48 : word) = Some W_58b48.
Proof. vm_refl. Qed.
Lemma D_58b48 : decode_any W_58b48 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b4c : bv 32 := 0x00e68023.
Lemma F_58b4c : fetch_word Plain.M.loaded_segments (0x58b4c : word) = Some W_58b4c.
Proof. vm_refl. Qed.
Lemma D_58b4c : decode_any W_58b4c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b50 : bv 32 := 0x00f680a3.
Lemma F_58b50 : fetch_word Plain.M.loaded_segments (0x58b50 : word) = Some W_58b50.
Proof. vm_refl. Qed.
Lemma D_58b50 : decode_any W_58b50 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b54 : bv 32 := 0x01068123.
Lemma F_58b54 : fetch_word Plain.M.loaded_segments (0x58b54 : word) = Some W_58b54.
Proof. vm_refl. Qed.
Lemma D_58b54 : decode_any W_58b54 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b58 : bv 32 := 0x00368693.
Lemma F_58b58 : fetch_word Plain.M.loaded_segments (0x58b58 : word) = Some W_58b58.
Proof. vm_refl. Qed.
Lemma D_58b58 : decode_any W_58b58 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b5c : bv 32 := 0x01058593.
Lemma F_58b5c : fetch_word Plain.M.loaded_segments (0x58b5c : word) = Some W_58b5c.
Proof. vm_refl. Qed.
Lemma D_58b5c : decode_any W_58b5c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b60 : bv 32 := 0x01000793.
Lemma F_58b60 : fetch_word Plain.M.loaded_segments (0x58b60 : word) = Some W_58b60.
Proof. vm_refl. Qed.
Lemma D_58b60 : decode_any W_58b60 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b64 : bv 32 := 0x0187581b.
Lemma F_58b64 : fetch_word Plain.M.loaded_segments (0x58b64 : word) = Some W_58b64.
Proof. vm_refl. Qed.
Lemma D_58b64 : decode_any W_58b64 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b68 : bv 32 := 0xff45a883.
Lemma F_58b68 : fetch_word Plain.M.loaded_segments (0x58b68 : word) = Some W_58b68.
Proof. vm_refl. Qed.
Lemma D_58b68 : decode_any W_58b68 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b6c : bv 32 := 0xff85a283.
Lemma F_58b6c : fetch_word Plain.M.loaded_segments (0x58b6c : word) = Some W_58b6c.
Proof. vm_refl. Qed.
Lemma D_58b6c : decode_any W_58b6c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b70 : bv 32 := 0xffc5a303.
Lemma F_58b70 : fetch_word Plain.M.loaded_segments (0x58b70 : word) = Some W_58b70.
Proof. vm_refl. Qed.
Lemma D_58b70 : decode_any W_58b70 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b74 : bv 32 := 0x0005a703.
Lemma F_58b74 : fetch_word Plain.M.loaded_segments (0x58b74 : word) = Some W_58b74.
Proof. vm_refl. Qed.
Lemma D_58b74 : decode_any W_58b74 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b78 : bv 32 := 0x00889393.
Lemma F_58b78 : fetch_word Plain.M.loaded_segments (0x58b78 : word) = Some W_58b78.
Proof. vm_refl. Qed.
Lemma D_58b78 : decode_any W_58b78 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b7c : bv 32 := 0x0188d89b.
Lemma F_58b7c : fetch_word Plain.M.loaded_segments (0x58b7c : word) = Some W_58b7c.
Proof. vm_refl. Qed.
Lemma D_58b7c : decode_any W_58b7c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b80 : bv 32 := 0x0103e833.
Lemma F_58b80 : fetch_word Plain.M.loaded_segments (0x58b80 : word) = Some W_58b80.
Proof. vm_refl. Qed.
Lemma D_58b80 : decode_any W_58b80 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b84 : bv 32 := 0x00829393.
Lemma F_58b84 : fetch_word Plain.M.loaded_segments (0x58b84 : word) = Some W_58b84.
Proof. vm_refl. Qed.
Lemma D_58b84 : decode_any W_58b84 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b88 : bv 32 := 0x0182d29b.
Lemma F_58b88 : fetch_word Plain.M.loaded_segments (0x58b88 : word) = Some W_58b88.
Proof. vm_refl. Qed.
Lemma D_58b88 : decode_any W_58b88 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b8c : bv 32 := 0x0113e8b3.
Lemma F_58b8c : fetch_word Plain.M.loaded_segments (0x58b8c : word) = Some W_58b8c.
Proof. vm_refl. Qed.
Lemma D_58b8c : decode_any W_58b8c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b90 : bv 32 := 0x00831393.
Lemma F_58b90 : fetch_word Plain.M.loaded_segments (0x58b90 : word) = Some W_58b90.
Proof. vm_refl. Qed.
Lemma D_58b90 : decode_any W_58b90 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b94 : bv 32 := 0x0183531b.
Lemma F_58b94 : fetch_word Plain.M.loaded_segments (0x58b94 : word) = Some W_58b94.
Proof. vm_refl. Qed.
Lemma D_58b94 : decode_any W_58b94 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b98 : bv 32 := 0x0053e2b3.
Lemma F_58b98 : fetch_word Plain.M.loaded_segments (0x58b98 : word) = Some W_58b98.
Proof. vm_refl. Qed.
Lemma D_58b98 : decode_any W_58b98 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58b9c : bv 32 := 0x00871393.
Lemma F_58b9c : fetch_word Plain.M.loaded_segments (0x58b9c : word) = Some W_58b9c.
Proof. vm_refl. Qed.
Lemma D_58b9c : decode_any W_58b9c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ba0 : bv 32 := 0x0063e333.
Lemma F_58ba0 : fetch_word Plain.M.loaded_segments (0x58ba0 : word) = Some W_58ba0.
Proof. vm_refl. Qed.
Lemma D_58ba0 : decode_any W_58ba0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ba4 : bv 32 := 0xff060613.
Lemma F_58ba4 : fetch_word Plain.M.loaded_segments (0x58ba4 : word) = Some W_58ba4.
Proof. vm_refl. Qed.
Lemma D_58ba4 : decode_any W_58ba4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ba8 : bv 32 := 0x0106a023.
Lemma F_58ba8 : fetch_word Plain.M.loaded_segments (0x58ba8 : word) = Some W_58ba8.
Proof. vm_refl. Qed.
Lemma D_58ba8 : decode_any W_58ba8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bac : bv 32 := 0x0116a223.
Lemma F_58bac : fetch_word Plain.M.loaded_segments (0x58bac : word) = Some W_58bac.
Proof. vm_refl. Qed.
Lemma D_58bac : decode_any W_58bac = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bb0 : bv 32 := 0x0056a423.
Lemma F_58bb0 : fetch_word Plain.M.loaded_segments (0x58bb0 : word) = Some W_58bb0.
Proof. vm_refl. Qed.
Lemma D_58bb0 : decode_any W_58bb0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bb4 : bv 32 := 0x0066a623.
Lemma F_58bb4 : fetch_word Plain.M.loaded_segments (0x58bb4 : word) = Some W_58bb4.
Proof. vm_refl. Qed.
Lemma D_58bb4 : decode_any W_58bb4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bb8 : bv 32 := 0x01068693.
Lemma F_58bb8 : fetch_word Plain.M.loaded_segments (0x58bb8 : word) = Some W_58bb8.
Proof. vm_refl. Qed.
Lemma D_58bb8 : decode_any W_58bb8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bbc : bv 32 := 0x01058593.
Lemma F_58bbc : fetch_word Plain.M.loaded_segments (0x58bbc : word) = Some W_58bbc.
Proof. vm_refl. Qed.
Lemma D_58bbc : decode_any W_58bbc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bc0 : bv 32 := 0xfac7e2e3.
Lemma F_58bc0 : fetch_word Plain.M.loaded_segments (0x58bc0 : word) = Some W_58bc0.
Proof. vm_refl. Qed.
Lemma D_58bc0 : decode_any W_58bc0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bc4 : bv 32 := 0xff358593.
Lemma F_58bc4 : fetch_word Plain.M.loaded_segments (0x58bc4 : word) = Some W_58bc4.
Proof. vm_refl. Qed.
Lemma D_58bc4 : decode_any W_58bc4 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bc8 : bv 32 := 0x01000713.
Lemma F_58bc8 : fetch_word Plain.M.loaded_segments (0x58bc8 : word) = Some W_58bc8.
Proof. vm_refl. Qed.
Lemma D_58bc8 : decode_any W_58bc8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bcc : bv 32 := 0xdae66ce3.
Lemma F_58bcc : fetch_word Plain.M.loaded_segments (0x58bcc : word) = Some W_58bcc.
Proof. vm_refl. Qed.
Lemma D_58bcc : decode_any W_58bcc = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bd0 : bv 32 := 0x0005c703.
Lemma F_58bd0 : fetch_word Plain.M.loaded_segments (0x58bd0 : word) = Some W_58bd0.
Proof. vm_refl. Qed.
Lemma D_58bd0 : decode_any W_58bd0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bd4 : bv 32 := 0x0015c783.
Lemma F_58bd4 : fetch_word Plain.M.loaded_segments (0x58bd4 : word) = Some W_58bd4.
Proof. vm_refl. Qed.
Lemma D_58bd4 : decode_any W_58bd4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bd8 : bv 32 := 0x0025c803.
Lemma F_58bd8 : fetch_word Plain.M.loaded_segments (0x58bd8 : word) = Some W_58bd8.
Proof. vm_refl. Qed.
Lemma D_58bd8 : decode_any W_58bd8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bdc : bv 32 := 0x0035c883.
Lemma F_58bdc : fetch_word Plain.M.loaded_segments (0x58bdc : word) = Some W_58bdc.
Proof. vm_refl. Qed.
Lemma D_58bdc : decode_any W_58bdc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58be0 : bv 32 := 0x0045c283.
Lemma F_58be0 : fetch_word Plain.M.loaded_segments (0x58be0 : word) = Some W_58be0.
Proof. vm_refl. Qed.
Lemma D_58be0 : decode_any W_58be0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58be4 : bv 32 := 0x0055c303.
Lemma F_58be4 : fetch_word Plain.M.loaded_segments (0x58be4 : word) = Some W_58be4.
Proof. vm_refl. Qed.
Lemma D_58be4 : decode_any W_58be4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58be8 : bv 32 := 0x0065c383.
Lemma F_58be8 : fetch_word Plain.M.loaded_segments (0x58be8 : word) = Some W_58be8.
Proof. vm_refl. Qed.
Lemma D_58be8 : decode_any W_58be8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bec : bv 32 := 0x0075ce03.
Lemma F_58bec : fetch_word Plain.M.loaded_segments (0x58bec : word) = Some W_58bec.
Proof. vm_refl. Qed.
Lemma D_58bec : decode_any W_58bec = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bf0 : bv 32 := 0x00e68023.
Lemma F_58bf0 : fetch_word Plain.M.loaded_segments (0x58bf0 : word) = Some W_58bf0.
Proof. vm_refl. Qed.
Lemma D_58bf0 : decode_any W_58bf0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bf4 : bv 32 := 0x00f680a3.
Lemma F_58bf4 : fetch_word Plain.M.loaded_segments (0x58bf4 : word) = Some W_58bf4.
Proof. vm_refl. Qed.
Lemma D_58bf4 : decode_any W_58bf4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bf8 : bv 32 := 0x01068123.
Lemma F_58bf8 : fetch_word Plain.M.loaded_segments (0x58bf8 : word) = Some W_58bf8.
Proof. vm_refl. Qed.
Lemma D_58bf8 : decode_any W_58bf8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58bfc : bv 32 := 0x011681a3.
Lemma F_58bfc : fetch_word Plain.M.loaded_segments (0x58bfc : word) = Some W_58bfc.
Proof. vm_refl. Qed.
Lemma D_58bfc : decode_any W_58bfc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c00 : bv 32 := 0x0085c703.
Lemma F_58c00 : fetch_word Plain.M.loaded_segments (0x58c00 : word) = Some W_58c00.
Proof. vm_refl. Qed.
Lemma D_58c00 : decode_any W_58c00 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c04 : bv 32 := 0x0095c783.
Lemma F_58c04 : fetch_word Plain.M.loaded_segments (0x58c04 : word) = Some W_58c04.
Proof. vm_refl. Qed.
Lemma D_58c04 : decode_any W_58c04 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c08 : bv 32 := 0x00a5c803.
Lemma F_58c08 : fetch_word Plain.M.loaded_segments (0x58c08 : word) = Some W_58c08.
Proof. vm_refl. Qed.
Lemma D_58c08 : decode_any W_58c08 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c0c : bv 32 := 0x00b5c883.
Lemma F_58c0c : fetch_word Plain.M.loaded_segments (0x58c0c : word) = Some W_58c0c.
Proof. vm_refl. Qed.
Lemma D_58c0c : decode_any W_58c0c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c10 : bv 32 := 0x00568223.
Lemma F_58c10 : fetch_word Plain.M.loaded_segments (0x58c10 : word) = Some W_58c10.
Proof. vm_refl. Qed.
Lemma D_58c10 : decode_any W_58c10 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c14 : bv 32 := 0x006682a3.
Lemma F_58c14 : fetch_word Plain.M.loaded_segments (0x58c14 : word) = Some W_58c14.
Proof. vm_refl. Qed.
Lemma D_58c14 : decode_any W_58c14 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c18 : bv 32 := 0x00768323.
Lemma F_58c18 : fetch_word Plain.M.loaded_segments (0x58c18 : word) = Some W_58c18.
Proof. vm_refl. Qed.
Lemma D_58c18 : decode_any W_58c18 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c1c : bv 32 := 0x01c683a3.
Lemma F_58c1c : fetch_word Plain.M.loaded_segments (0x58c1c : word) = Some W_58c1c.
Proof. vm_refl. Qed.
Lemma D_58c1c : decode_any W_58c1c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c20 : bv 32 := 0x00c5c283.
Lemma F_58c20 : fetch_word Plain.M.loaded_segments (0x58c20 : word) = Some W_58c20.
Proof. vm_refl. Qed.
Lemma D_58c20 : decode_any W_58c20 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c24 : bv 32 := 0x00d5c303.
Lemma F_58c24 : fetch_word Plain.M.loaded_segments (0x58c24 : word) = Some W_58c24.
Proof. vm_refl. Qed.
Lemma D_58c24 : decode_any W_58c24 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c28 : bv 32 := 0x00e5c383.
Lemma F_58c28 : fetch_word Plain.M.loaded_segments (0x58c28 : word) = Some W_58c28.
Proof. vm_refl. Qed.
Lemma D_58c28 : decode_any W_58c28 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c2c : bv 32 := 0x00f5ce03.
Lemma F_58c2c : fetch_word Plain.M.loaded_segments (0x58c2c : word) = Some W_58c2c.
Proof. vm_refl. Qed.
Lemma D_58c2c : decode_any W_58c2c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c30 : bv 32 := 0x01058593.
Lemma F_58c30 : fetch_word Plain.M.loaded_segments (0x58c30 : word) = Some W_58c30.
Proof. vm_refl. Qed.
Lemma D_58c30 : decode_any W_58c30 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c34 : bv 32 := 0x00e68423.
Lemma F_58c34 : fetch_word Plain.M.loaded_segments (0x58c34 : word) = Some W_58c34.
Proof. vm_refl. Qed.
Lemma D_58c34 : decode_any W_58c34 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c38 : bv 32 := 0x00f684a3.
Lemma F_58c38 : fetch_word Plain.M.loaded_segments (0x58c38 : word) = Some W_58c38.
Proof. vm_refl. Qed.
Lemma D_58c38 : decode_any W_58c38 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c3c : bv 32 := 0x01068523.
Lemma F_58c3c : fetch_word Plain.M.loaded_segments (0x58c3c : word) = Some W_58c3c.
Proof. vm_refl. Qed.
Lemma D_58c3c : decode_any W_58c3c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c40 : bv 32 := 0x011685a3.
Lemma F_58c40 : fetch_word Plain.M.loaded_segments (0x58c40 : word) = Some W_58c40.
Proof. vm_refl. Qed.
Lemma D_58c40 : decode_any W_58c40 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c44 : bv 32 := 0x01068713.
Lemma F_58c44 : fetch_word Plain.M.loaded_segments (0x58c44 : word) = Some W_58c44.
Proof. vm_refl. Qed.
Lemma D_58c44 : decode_any W_58c44 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c48 : bv 32 := 0x00568623.
Lemma F_58c48 : fetch_word Plain.M.loaded_segments (0x58c48 : word) = Some W_58c48.
Proof. vm_refl. Qed.
Lemma D_58c48 : decode_any W_58c48 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c4c : bv 32 := 0x006686a3.
Lemma F_58c4c : fetch_word Plain.M.loaded_segments (0x58c4c : word) = Some W_58c4c.
Proof. vm_refl. Qed.
Lemma D_58c4c : decode_any W_58c4c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c50 : bv 32 := 0x00768723.
Lemma F_58c50 : fetch_word Plain.M.loaded_segments (0x58c50 : word) = Some W_58c50.
Proof. vm_refl. Qed.
Lemma D_58c50 : decode_any W_58c50 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c54 : bv 32 := 0x01c687a3.
Lemma F_58c54 : fetch_word Plain.M.loaded_segments (0x58c54 : word) = Some W_58c54.
Proof. vm_refl. Qed.
Lemma D_58c54 : decode_any W_58c54 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c58 : bv 32 := 0x00070693.
Lemma F_58c58 : fetch_word Plain.M.loaded_segments (0x58c58 : word) = Some W_58c58.
Proof. vm_refl. Qed.
Lemma D_58c58 : decode_any W_58c58 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c5c : bv 32 := 0x00867713.
Lemma F_58c5c : fetch_word Plain.M.loaded_segments (0x58c5c : word) = Some W_58c5c.
Proof. vm_refl. Qed.
Lemma D_58c5c : decode_any W_58c5c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c60 : bv 32 := 0xd20706e3.
Lemma F_58c60 : fetch_word Plain.M.loaded_segments (0x58c60 : word) = Some W_58c60.
Proof. vm_refl. Qed.
Lemma D_58c60 : decode_any W_58c60 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c64 : bv 32 := 0x0005c703.
Lemma F_58c64 : fetch_word Plain.M.loaded_segments (0x58c64 : word) = Some W_58c64.
Proof. vm_refl. Qed.
Lemma D_58c64 : decode_any W_58c64 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c68 : bv 32 := 0x0015c783.
Lemma F_58c68 : fetch_word Plain.M.loaded_segments (0x58c68 : word) = Some W_58c68.
Proof. vm_refl. Qed.
Lemma D_58c68 : decode_any W_58c68 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c6c : bv 32 := 0x0025c803.
Lemma F_58c6c : fetch_word Plain.M.loaded_segments (0x58c6c : word) = Some W_58c6c.
Proof. vm_refl. Qed.
Lemma D_58c6c : decode_any W_58c6c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c70 : bv 32 := 0x0035c883.
Lemma F_58c70 : fetch_word Plain.M.loaded_segments (0x58c70 : word) = Some W_58c70.
Proof. vm_refl. Qed.
Lemma D_58c70 : decode_any W_58c70 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c74 : bv 32 := 0x0045c283.
Lemma F_58c74 : fetch_word Plain.M.loaded_segments (0x58c74 : word) = Some W_58c74.
Proof. vm_refl. Qed.
Lemma D_58c74 : decode_any W_58c74 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c78 : bv 32 := 0x0055c303.
Lemma F_58c78 : fetch_word Plain.M.loaded_segments (0x58c78 : word) = Some W_58c78.
Proof. vm_refl. Qed.
Lemma D_58c78 : decode_any W_58c78 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c7c : bv 32 := 0x0065c383.
Lemma F_58c7c : fetch_word Plain.M.loaded_segments (0x58c7c : word) = Some W_58c7c.
Proof. vm_refl. Qed.
Lemma D_58c7c : decode_any W_58c7c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c80 : bv 32 := 0x0075ce03.
Lemma F_58c80 : fetch_word Plain.M.loaded_segments (0x58c80 : word) = Some W_58c80.
Proof. vm_refl. Qed.
Lemma D_58c80 : decode_any W_58c80 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c84 : bv 32 := 0x00858593.
Lemma F_58c84 : fetch_word Plain.M.loaded_segments (0x58c84 : word) = Some W_58c84.
Proof. vm_refl. Qed.
Lemma D_58c84 : decode_any W_58c84 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c88 : bv 32 := 0x00e68023.
Lemma F_58c88 : fetch_word Plain.M.loaded_segments (0x58c88 : word) = Some W_58c88.
Proof. vm_refl. Qed.
Lemma D_58c88 : decode_any W_58c88 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c8c : bv 32 := 0x00f680a3.
Lemma F_58c8c : fetch_word Plain.M.loaded_segments (0x58c8c : word) = Some W_58c8c.
Proof. vm_refl. Qed.
Lemma D_58c8c : decode_any W_58c8c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c90 : bv 32 := 0x01068123.
Lemma F_58c90 : fetch_word Plain.M.loaded_segments (0x58c90 : word) = Some W_58c90.
Proof. vm_refl. Qed.
Lemma D_58c90 : decode_any W_58c90 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c94 : bv 32 := 0x011681a3.
Lemma F_58c94 : fetch_word Plain.M.loaded_segments (0x58c94 : word) = Some W_58c94.
Proof. vm_refl. Qed.
Lemma D_58c94 : decode_any W_58c94 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c98 : bv 32 := 0x00868713.
Lemma F_58c98 : fetch_word Plain.M.loaded_segments (0x58c98 : word) = Some W_58c98.
Proof. vm_refl. Qed.
Lemma D_58c98 : decode_any W_58c98 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58c9c : bv 32 := 0x00568223.
Lemma F_58c9c : fetch_word Plain.M.loaded_segments (0x58c9c : word) = Some W_58c9c.
Proof. vm_refl. Qed.
Lemma D_58c9c : decode_any W_58c9c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ca0 : bv 32 := 0x006682a3.
Lemma F_58ca0 : fetch_word Plain.M.loaded_segments (0x58ca0 : word) = Some W_58ca0.
Proof. vm_refl. Qed.
Lemma D_58ca0 : decode_any W_58ca0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ca4 : bv 32 := 0x00768323.
Lemma F_58ca4 : fetch_word Plain.M.loaded_segments (0x58ca4 : word) = Some W_58ca4.
Proof. vm_refl. Qed.
Lemma D_58ca4 : decode_any W_58ca4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ca8 : bv 32 := 0x01c683a3.
Lemma F_58ca8 : fetch_word Plain.M.loaded_segments (0x58ca8 : word) = Some W_58ca8.
Proof. vm_refl. Qed.
Lemma D_58ca8 : decode_any W_58ca8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cac : bv 32 := 0x00070693.
Lemma F_58cac : fetch_word Plain.M.loaded_segments (0x58cac : word) = Some W_58cac.
Proof. vm_refl. Qed.
Lemma D_58cac : decode_any W_58cac = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cb0 : bv 32 := 0x00467713.
Lemma F_58cb0 : fetch_word Plain.M.loaded_segments (0x58cb0 : word) = Some W_58cb0.
Proof. vm_refl. Qed.
Lemma D_58cb0 : decode_any W_58cb0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cb4 : bv 32 := 0x02070863.
Lemma F_58cb4 : fetch_word Plain.M.loaded_segments (0x58cb4 : word) = Some W_58cb4.
Proof. vm_refl. Qed.
Lemma D_58cb4 : decode_any W_58cb4 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cb8 : bv 32 := 0x0005c703.
Lemma F_58cb8 : fetch_word Plain.M.loaded_segments (0x58cb8 : word) = Some W_58cb8.
Proof. vm_refl. Qed.
Lemma D_58cb8 : decode_any W_58cb8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cbc : bv 32 := 0x0015c783.
Lemma F_58cbc : fetch_word Plain.M.loaded_segments (0x58cbc : word) = Some W_58cbc.
Proof. vm_refl. Qed.
Lemma D_58cbc : decode_any W_58cbc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cc0 : bv 32 := 0x0025c803.
Lemma F_58cc0 : fetch_word Plain.M.loaded_segments (0x58cc0 : word) = Some W_58cc0.
Proof. vm_refl. Qed.
Lemma D_58cc0 : decode_any W_58cc0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cc4 : bv 32 := 0x0035c883.
Lemma F_58cc4 : fetch_word Plain.M.loaded_segments (0x58cc4 : word) = Some W_58cc4.
Proof. vm_refl. Qed.
Lemma D_58cc4 : decode_any W_58cc4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cc8 : bv 32 := 0x00458593.
Lemma F_58cc8 : fetch_word Plain.M.loaded_segments (0x58cc8 : word) = Some W_58cc8.
Proof. vm_refl. Qed.
Lemma D_58cc8 : decode_any W_58cc8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ccc : bv 32 := 0x00468293.
Lemma F_58ccc : fetch_word Plain.M.loaded_segments (0x58ccc : word) = Some W_58ccc.
Proof. vm_refl. Qed.
Lemma D_58ccc : decode_any W_58ccc = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cd0 : bv 32 := 0x00e68023.
Lemma F_58cd0 : fetch_word Plain.M.loaded_segments (0x58cd0 : word) = Some W_58cd0.
Proof. vm_refl. Qed.
Lemma D_58cd0 : decode_any W_58cd0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cd4 : bv 32 := 0x00f680a3.
Lemma F_58cd4 : fetch_word Plain.M.loaded_segments (0x58cd4 : word) = Some W_58cd4.
Proof. vm_refl. Qed.
Lemma D_58cd4 : decode_any W_58cd4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cd8 : bv 32 := 0x01068123.
Lemma F_58cd8 : fetch_word Plain.M.loaded_segments (0x58cd8 : word) = Some W_58cd8.
Proof. vm_refl. Qed.
Lemma D_58cd8 : decode_any W_58cd8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cdc : bv 32 := 0x011681a3.
Lemma F_58cdc : fetch_word Plain.M.loaded_segments (0x58cdc : word) = Some W_58cdc.
Proof. vm_refl. Qed.
Lemma D_58cdc : decode_any W_58cdc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ce0 : bv 32 := 0x00028693.
Lemma F_58ce0 : fetch_word Plain.M.loaded_segments (0x58ce0 : word) = Some W_58ce0.
Proof. vm_refl. Qed.
Lemma D_58ce0 : decode_any W_58ce0 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ce4 : bv 32 := 0x00267713.
Lemma F_58ce4 : fetch_word Plain.M.loaded_segments (0x58ce4 : word) = Some W_58ce4.
Proof. vm_refl. Qed.
Lemma D_58ce4 : decode_any W_58ce4 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ce8 : bv 32 := 0x00071863.
Lemma F_58ce8 : fetch_word Plain.M.loaded_segments (0x58ce8 : word) = Some W_58ce8.
Proof. vm_refl. Qed.
Lemma D_58ce8 : decode_any W_58ce8 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cec : bv 32 := 0x00167613.
Lemma F_58cec : fetch_word Plain.M.loaded_segments (0x58cec : word) = Some W_58cec.
Proof. vm_refl. Qed.
Lemma D_58cec : decode_any W_58cec = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cf0 : bv 32 := 0x02061663.
Lemma F_58cf0 : fetch_word Plain.M.loaded_segments (0x58cf0 : word) = Some W_58cf0.
Proof. vm_refl. Qed.
Lemma D_58cf0 : decode_any W_58cf0 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cf4 : bv 32 := 0x00008067.
Lemma F_58cf4 : fetch_word Plain.M.loaded_segments (0x58cf4 : word) = Some W_58cf4.
Proof. vm_refl. Qed.
Lemma D_58cf4 : decode_any W_58cf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cf8 : bv 32 := 0x0005c703.
Lemma F_58cf8 : fetch_word Plain.M.loaded_segments (0x58cf8 : word) = Some W_58cf8.
Proof. vm_refl. Qed.
Lemma D_58cf8 : decode_any W_58cf8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58cfc : bv 32 := 0x0015c783.
Lemma F_58cfc : fetch_word Plain.M.loaded_segments (0x58cfc : word) = Some W_58cfc.
Proof. vm_refl. Qed.
Lemma D_58cfc : decode_any W_58cfc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d00 : bv 32 := 0x00258593.
Lemma F_58d00 : fetch_word Plain.M.loaded_segments (0x58d00 : word) = Some W_58d00.
Proof. vm_refl. Qed.
Lemma D_58d00 : decode_any W_58d00 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d04 : bv 32 := 0x00268813.
Lemma F_58d04 : fetch_word Plain.M.loaded_segments (0x58d04 : word) = Some W_58d04.
Proof. vm_refl. Qed.
Lemma D_58d04 : decode_any W_58d04 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d08 : bv 32 := 0x00e68023.
Lemma F_58d08 : fetch_word Plain.M.loaded_segments (0x58d08 : word) = Some W_58d08.
Proof. vm_refl. Qed.
Lemma D_58d08 : decode_any W_58d08 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d0c : bv 32 := 0x00f680a3.
Lemma F_58d0c : fetch_word Plain.M.loaded_segments (0x58d0c : word) = Some W_58d0c.
Proof. vm_refl. Qed.
Lemma D_58d0c : decode_any W_58d0c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d10 : bv 32 := 0x00080693.
Lemma F_58d10 : fetch_word Plain.M.loaded_segments (0x58d10 : word) = Some W_58d10.
Proof. vm_refl. Qed.
Lemma D_58d10 : decode_any W_58d10 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d14 : bv 32 := 0x00167613.
Lemma F_58d14 : fetch_word Plain.M.loaded_segments (0x58d14 : word) = Some W_58d14.
Proof. vm_refl. Qed.
Lemma D_58d14 : decode_any W_58d14 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d18 : bv 32 := 0xfc060ee3.
Lemma F_58d18 : fetch_word Plain.M.loaded_segments (0x58d18 : word) = Some W_58d18.
Proof. vm_refl. Qed.
Lemma D_58d18 : decode_any W_58d18 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d1c : bv 32 := 0x0005c583.
Lemma F_58d1c : fetch_word Plain.M.loaded_segments (0x58d1c : word) = Some W_58d1c.
Proof. vm_refl. Qed.
Lemma D_58d1c : decode_any W_58d1c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d20 : bv 32 := 0x00b68023.
Lemma F_58d20 : fetch_word Plain.M.loaded_segments (0x58d20 : word) = Some W_58d20.
Proof. vm_refl. Qed.
Lemma D_58d20 : decode_any W_58d20 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58d24 : bv 32 := 0x00008067.
Lemma F_58d24 : fetch_word Plain.M.loaded_segments (0x58d24 : word) = Some W_58d24.
Proof. vm_refl. Qed.
Lemma D_58d24 : decode_any W_58d24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ea4 : bv 32 := 0x0e060a63.
Lemma F_58ea4 : fetch_word Plain.M.loaded_segments (0x58ea4 : word) = Some W_58ea4.
Proof. vm_refl. Qed.
Lemma D_58ea4 : decode_any W_58ea4 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ea8 : bv 32 := 0x00b50023.
Lemma F_58ea8 : fetch_word Plain.M.loaded_segments (0x58ea8 : word) = Some W_58ea8.
Proof. vm_refl. Qed.
Lemma D_58ea8 : decode_any W_58ea8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eac : bv 32 := 0x00c506b3.
Lemma F_58eac : fetch_word Plain.M.loaded_segments (0x58eac : word) = Some W_58eac.
Proof. vm_refl. Qed.
Lemma D_58eac : decode_any W_58eac = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eb0 : bv 32 := 0x00300713.
Lemma F_58eb0 : fetch_word Plain.M.loaded_segments (0x58eb0 : word) = Some W_58eb0.
Proof. vm_refl. Qed.
Lemma D_58eb0 : decode_any W_58eb0 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eb4 : bv 32 := 0xfeb68fa3.
Lemma F_58eb4 : fetch_word Plain.M.loaded_segments (0x58eb4 : word) = Some W_58eb4.
Proof. vm_refl. Qed.
Lemma D_58eb4 : decode_any W_58eb4 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eb8 : bv 32 := 0x0ee66063.
Lemma F_58eb8 : fetch_word Plain.M.loaded_segments (0x58eb8 : word) = Some W_58eb8.
Proof. vm_refl. Qed.
Lemma D_58eb8 : decode_any W_58eb8 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ebc : bv 32 := 0x00b500a3.
Lemma F_58ebc : fetch_word Plain.M.loaded_segments (0x58ebc : word) = Some W_58ebc.
Proof. vm_refl. Qed.
Lemma D_58ebc : decode_any W_58ebc = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ec0 : bv 32 := 0x00b50123.
Lemma F_58ec0 : fetch_word Plain.M.loaded_segments (0x58ec0 : word) = Some W_58ec0.
Proof. vm_refl. Qed.
Lemma D_58ec0 : decode_any W_58ec0 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ec4 : bv 32 := 0x00700713.
Lemma F_58ec4 : fetch_word Plain.M.loaded_segments (0x58ec4 : word) = Some W_58ec4.
Proof. vm_refl. Qed.
Lemma D_58ec4 : decode_any W_58ec4 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ec8 : bv 32 := 0xfeb68ea3.
Lemma F_58ec8 : fetch_word Plain.M.loaded_segments (0x58ec8 : word) = Some W_58ec8.
Proof. vm_refl. Qed.
Lemma D_58ec8 : decode_any W_58ec8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ecc : bv 32 := 0xfeb68f23.
Lemma F_58ecc : fetch_word Plain.M.loaded_segments (0x58ecc : word) = Some W_58ecc.
Proof. vm_refl. Qed.
Lemma D_58ecc : decode_any W_58ecc = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ed0 : bv 32 := 0x0ce66463.
Lemma F_58ed0 : fetch_word Plain.M.loaded_segments (0x58ed0 : word) = Some W_58ed0.
Proof. vm_refl. Qed.
Lemma D_58ed0 : decode_any W_58ed0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ed4 : bv 32 := 0x00b501a3.
Lemma F_58ed4 : fetch_word Plain.M.loaded_segments (0x58ed4 : word) = Some W_58ed4.
Proof. vm_refl. Qed.
Lemma D_58ed4 : decode_any W_58ed4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ed8 : bv 32 := 0x00900793.
Lemma F_58ed8 : fetch_word Plain.M.loaded_segments (0x58ed8 : word) = Some W_58ed8.
Proof. vm_refl. Qed.
Lemma D_58ed8 : decode_any W_58ed8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_58edc : bv 32 := 0xfeb68e23.
Lemma F_58edc : fetch_word Plain.M.loaded_segments (0x58edc : word) = Some W_58edc.
Proof. vm_refl. Qed.
Lemma D_58edc : decode_any W_58edc = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ee0 : bv 32 := 0x0af66c63.
Lemma F_58ee0 : fetch_word Plain.M.loaded_segments (0x58ee0 : word) = Some W_58ee0.
Proof. vm_refl. Qed.
Lemma D_58ee0 : decode_any W_58ee0 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ee4 : bv 32 := 0x40a006bb.
Lemma F_58ee4 : fetch_word Plain.M.loaded_segments (0x58ee4 : word) = Some W_58ee4.
Proof. vm_refl. Qed.
Lemma D_58ee4 : decode_any W_58ee4 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ee8 : bv 32 := 0x03859813.
Lemma F_58ee8 : fetch_word Plain.M.loaded_segments (0x58ee8 : word) = Some W_58ee8.
Proof. vm_refl. Qed.
Lemma D_58ee8 : decode_any W_58ee8 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_58eec : bv 32 := 0x101015b7.
Lemma F_58eec : fetch_word Plain.M.loaded_segments (0x58eec : word) = Some W_58eec.
Proof. vm_refl. Qed.
Lemma D_58eec : decode_any W_58eec = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ef0 : bv 32 := 0x0036f693.
Lemma F_58ef0 : fetch_word Plain.M.loaded_segments (0x58ef0 : word) = Some W_58ef0.
Proof. vm_refl. Qed.
Lemma D_58ef0 : decode_any W_58ef0 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ef4 : bv 32 := 0x00459713.
Lemma F_58ef4 : fetch_word Plain.M.loaded_segments (0x58ef4 : word) = Some W_58ef4.
Proof. vm_refl. Qed.
Lemma D_58ef4 : decode_any W_58ef4 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58ef8 : bv 32 := 0x40d60633.
Lemma F_58ef8 : fetch_word Plain.M.loaded_segments (0x58ef8 : word) = Some W_58ef8.
Proof. vm_refl. Qed.
Lemma D_58ef8 : decode_any W_58ef8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58efc : bv 32 := 0x00d505b3.
Lemma F_58efc : fetch_word Plain.M.loaded_segments (0x58efc : word) = Some W_58efc.
Proof. vm_refl. Qed.
Lemma D_58efc : decode_any W_58efc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f00 : bv 32 := 0x10070693.
Lemma F_58f00 : fetch_word Plain.M.loaded_segments (0x58f00 : word) = Some W_58f00.
Proof. vm_refl. Qed.
Lemma D_58f00 : decode_any W_58f00 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f04 : bv 32 := 0xffc67713.
Lemma F_58f04 : fetch_word Plain.M.loaded_segments (0x58f04 : word) = Some W_58f04.
Proof. vm_refl. Qed.
Lemma D_58f04 : decode_any W_58f04 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f08 : bv 32 := 0x02d83633.
Lemma F_58f08 : fetch_word Plain.M.loaded_segments (0x58f08 : word) = Some W_58f08.
Proof. vm_refl. Qed.
Lemma D_58f08 : decode_any W_58f08 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f0c : bv 32 := 0x00c5a023.
Lemma F_58f0c : fetch_word Plain.M.loaded_segments (0x58f0c : word) = Some W_58f0c.
Proof. vm_refl. Qed.
Lemma D_58f0c : decode_any W_58f0c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f10 : bv 32 := 0x00e586b3.
Lemma F_58f10 : fetch_word Plain.M.loaded_segments (0x58f10 : word) = Some W_58f10.
Proof. vm_refl. Qed.
Lemma D_58f10 : decode_any W_58f10 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f14 : bv 32 := 0xfec6ae23.
Lemma F_58f14 : fetch_word Plain.M.loaded_segments (0x58f14 : word) = Some W_58f14.
Proof. vm_refl. Qed.
Lemma D_58f14 : decode_any W_58f14 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f18 : bv 32 := 0x08f76063.
Lemma F_58f18 : fetch_word Plain.M.loaded_segments (0x58f18 : word) = Some W_58f18.
Proof. vm_refl. Qed.
Lemma D_58f18 : decode_any W_58f18 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f1c : bv 32 := 0x00c5a223.
Lemma F_58f1c : fetch_word Plain.M.loaded_segments (0x58f1c : word) = Some W_58f1c.
Proof. vm_refl. Qed.
Lemma D_58f1c : decode_any W_58f1c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f20 : bv 32 := 0x00c5a423.
Lemma F_58f20 : fetch_word Plain.M.loaded_segments (0x58f20 : word) = Some W_58f20.
Proof. vm_refl. Qed.
Lemma D_58f20 : decode_any W_58f20 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f24 : bv 32 := 0x01900793.
Lemma F_58f24 : fetch_word Plain.M.loaded_segments (0x58f24 : word) = Some W_58f24.
Proof. vm_refl. Qed.
Lemma D_58f24 : decode_any W_58f24 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f28 : bv 32 := 0xfec6aa23.
Lemma F_58f28 : fetch_word Plain.M.loaded_segments (0x58f28 : word) = Some W_58f28.
Proof. vm_refl. Qed.
Lemma D_58f28 : decode_any W_58f28 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f2c : bv 32 := 0xfec6ac23.
Lemma F_58f2c : fetch_word Plain.M.loaded_segments (0x58f2c : word) = Some W_58f2c.
Proof. vm_refl. Qed.
Lemma D_58f2c : decode_any W_58f2c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f30 : bv 32 := 0x06f76463.
Lemma F_58f30 : fetch_word Plain.M.loaded_segments (0x58f30 : word) = Some W_58f30.
Proof. vm_refl. Qed.
Lemma D_58f30 : decode_any W_58f30 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f34 : bv 32 := 0x00c5a623.
Lemma F_58f34 : fetch_word Plain.M.loaded_segments (0x58f34 : word) = Some W_58f34.
Proof. vm_refl. Qed.
Lemma D_58f34 : decode_any W_58f34 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f38 : bv 32 := 0x00c5a823.
Lemma F_58f38 : fetch_word Plain.M.loaded_segments (0x58f38 : word) = Some W_58f38.
Proof. vm_refl. Qed.
Lemma D_58f38 : decode_any W_58f38 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f3c : bv 32 := 0x00c5aa23.
Lemma F_58f3c : fetch_word Plain.M.loaded_segments (0x58f3c : word) = Some W_58f3c.
Proof. vm_refl. Qed.
Lemma D_58f3c : decode_any W_58f3c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f40 : bv 32 := 0x00c5ac23.
Lemma F_58f40 : fetch_word Plain.M.loaded_segments (0x58f40 : word) = Some W_58f40.
Proof. vm_refl. Qed.
Lemma D_58f40 : decode_any W_58f40 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f44 : bv 32 := 0x0045f793.
Lemma F_58f44 : fetch_word Plain.M.loaded_segments (0x58f44 : word) = Some W_58f44.
Proof. vm_refl. Qed.
Lemma D_58f44 : decode_any W_58f44 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f48 : bv 32 := 0x02000813.
Lemma F_58f48 : fetch_word Plain.M.loaded_segments (0x58f48 : word) = Some W_58f48.
Proof. vm_refl. Qed.
Lemma D_58f48 : decode_any W_58f48 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f4c : bv 32 := 0x01878793.
Lemma F_58f4c : fetch_word Plain.M.loaded_segments (0x58f4c : word) = Some W_58f4c.
Proof. vm_refl. Qed.
Lemma D_58f4c : decode_any W_58f4c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f50 : bv 32 := 0x40f70733.
Lemma F_58f50 : fetch_word Plain.M.loaded_segments (0x58f50 : word) = Some W_58f50.
Proof. vm_refl. Qed.
Lemma D_58f50 : decode_any W_58f50 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f54 : bv 32 := 0xfec6a223.
Lemma F_58f54 : fetch_word Plain.M.loaded_segments (0x58f54 : word) = Some W_58f54.
Proof. vm_refl. Qed.
Lemma D_58f54 : decode_any W_58f54 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f58 : bv 32 := 0xfec6a423.
Lemma F_58f58 : fetch_word Plain.M.loaded_segments (0x58f58 : word) = Some W_58f58.
Proof. vm_refl. Qed.
Lemma D_58f58 : decode_any W_58f58 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f5c : bv 32 := 0xfec6a623.
Lemma F_58f5c : fetch_word Plain.M.loaded_segments (0x58f5c : word) = Some W_58f5c.
Proof. vm_refl. Qed.
Lemma D_58f5c : decode_any W_58f5c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f60 : bv 32 := 0xfec6a823.
Lemma F_58f60 : fetch_word Plain.M.loaded_segments (0x58f60 : word) = Some W_58f60.
Proof. vm_refl. Qed.
Lemma D_58f60 : decode_any W_58f60 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f64 : bv 32 := 0x03076a63.
Lemma F_58f64 : fetch_word Plain.M.loaded_segments (0x58f64 : word) = Some W_58f64.
Proof. vm_refl. Qed.
Lemma D_58f64 : decode_any W_58f64 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f68 : bv 32 := 0x02061613.
Lemma F_58f68 : fetch_word Plain.M.loaded_segments (0x58f68 : word) = Some W_58f68.
Proof. vm_refl. Qed.
Lemma D_58f68 : decode_any W_58f68 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f6c : bv 32 := 0x00f585b3.
Lemma F_58f6c : fetch_word Plain.M.loaded_segments (0x58f6c : word) = Some W_58f6c.
Proof. vm_refl. Qed.
Lemma D_58f6c : decode_any W_58f6c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f70 : bv 32 := 0x02065693.
Lemma F_58f70 : fetch_word Plain.M.loaded_segments (0x58f70 : word) = Some W_58f70.
Proof. vm_refl. Qed.
Lemma D_58f70 : decode_any W_58f70 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f74 : bv 32 := 0x00d66633.
Lemma F_58f74 : fetch_word Plain.M.loaded_segments (0x58f74 : word) = Some W_58f74.
Proof. vm_refl. Qed.
Lemma D_58f74 : decode_any W_58f74 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f78 : bv 32 := 0x01f00693.
Lemma F_58f78 : fetch_word Plain.M.loaded_segments (0x58f78 : word) = Some W_58f78.
Proof. vm_refl. Qed.
Lemma D_58f78 : decode_any W_58f78 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f7c : bv 32 := 0x00c5b023.
Lemma F_58f7c : fetch_word Plain.M.loaded_segments (0x58f7c : word) = Some W_58f7c.
Proof. vm_refl. Qed.
Lemma D_58f7c : decode_any W_58f7c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f80 : bv 32 := 0x00c5b423.
Lemma F_58f80 : fetch_word Plain.M.loaded_segments (0x58f80 : word) = Some W_58f80.
Proof. vm_refl. Qed.
Lemma D_58f80 : decode_any W_58f80 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f84 : bv 32 := 0x00c5b823.
Lemma F_58f84 : fetch_word Plain.M.loaded_segments (0x58f84 : word) = Some W_58f84.
Proof. vm_refl. Qed.
Lemma D_58f84 : decode_any W_58f84 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f88 : bv 32 := 0x00c5bc23.
Lemma F_58f88 : fetch_word Plain.M.loaded_segments (0x58f88 : word) = Some W_58f88.
Proof. vm_refl. Qed.
Lemma D_58f88 : decode_any W_58f88 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f8c : bv 32 := 0xfe070713.
Lemma F_58f8c : fetch_word Plain.M.loaded_segments (0x58f8c : word) = Some W_58f8c.
Proof. vm_refl. Qed.
Lemma D_58f8c : decode_any W_58f8c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f90 : bv 32 := 0x02058593.
Lemma F_58f90 : fetch_word Plain.M.loaded_segments (0x58f90 : word) = Some W_58f90.
Proof. vm_refl. Qed.
Lemma D_58f90 : decode_any W_58f90 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f94 : bv 32 := 0xfee6e4e3.
Lemma F_58f94 : fetch_word Plain.M.loaded_segments (0x58f94 : word) = Some W_58f94.
Proof. vm_refl. Qed.
Lemma D_58f94 : decode_any W_58f94 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_58f98 : bv 32 := 0x00008067.
Lemma F_58f98 : fetch_word Plain.M.loaded_segments (0x58f98 : word) = Some W_58f98.
Proof. vm_refl. Qed.
Lemma D_58f98 : decode_any W_58f98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5906c : bv 32 := 0x00757593.
Lemma F_5906c : fetch_word Plain.M.loaded_segments (0x5906c : word) = Some W_5906c.
Proof. vm_refl. Qed.
Lemma D_5906c : decode_any W_5906c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_59070 : bv 32 := 0x00050613.
Lemma F_59070 : fetch_word Plain.M.loaded_segments (0x59070 : word) = Some W_59070.
Proof. vm_refl. Qed.
Lemma D_59070 : decode_any W_59070 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59074 : bv 32 := 0x02058a63.
Lemma F_59074 : fetch_word Plain.M.loaded_segments (0x59074 : word) = Some W_59074.
Proof. vm_refl. Qed.
Lemma D_59074 : decode_any W_59074 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_59078 : bv 32 := 0x00054583.
Lemma F_59078 : fetch_word Plain.M.loaded_segments (0x59078 : word) = Some W_59078.
Proof. vm_refl. Qed.
Lemma D_59078 : decode_any W_59078 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5907c : bv 32 := 0x06058c63.
Lemma F_5907c : fetch_word Plain.M.loaded_segments (0x5907c : word) = Some W_5907c.
Proof. vm_refl. Qed.
Lemma D_5907c : decode_any W_5907c = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_59080 : bv 32 := 0x00150613.
Lemma F_59080 : fetch_word Plain.M.loaded_segments (0x59080 : word) = Some W_59080.
Proof. vm_refl. Qed.
Lemma D_59080 : decode_any W_59080 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_59084 : bv 32 := 0x00050593.
Lemma F_59084 : fetch_word Plain.M.loaded_segments (0x59084 : word) = Some W_59084.
Proof. vm_refl. Qed.
Lemma D_59084 : decode_any W_59084 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59088 : bv 32 := 0x00158693.
Lemma F_59088 : fetch_word Plain.M.loaded_segments (0x59088 : word) = Some W_59088.
Proof. vm_refl. Qed.
Lemma D_59088 : decode_any W_59088 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5908c : bv 32 := 0x0076f693.
Lemma F_5908c : fetch_word Plain.M.loaded_segments (0x5908c : word) = Some W_5908c.
Proof. vm_refl. Qed.
Lemma D_5908c : decode_any W_5908c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_59090 : bv 32 := 0x00068c63.
Lemma F_59090 : fetch_word Plain.M.loaded_segments (0x59090 : word) = Some W_59090.
Proof. vm_refl. Qed.
Lemma D_59090 : decode_any W_59090 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59094 : bv 32 := 0x00064683.
Lemma F_59094 : fetch_word Plain.M.loaded_segments (0x59094 : word) = Some W_59094.
Proof. vm_refl. Qed.
Lemma D_59094 : decode_any W_59094 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59098 : bv 32 := 0x00160613.
Lemma F_59098 : fetch_word Plain.M.loaded_segments (0x59098 : word) = Some W_59098.
Proof. vm_refl. Qed.
Lemma D_59098 : decode_any W_59098 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5909c : bv 32 := 0x00158593.
Lemma F_5909c : fetch_word Plain.M.loaded_segments (0x5909c : word) = Some W_5909c.
Proof. vm_refl. Qed.
Lemma D_5909c : decode_any W_5909c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_590a0 : bv 32 := 0xfe0694e3.
Lemma F_590a0 : fetch_word Plain.M.loaded_segments (0x590a0 : word) = Some W_590a0.
Proof. vm_refl. Qed.
Lemma D_590a0 : decode_any W_590a0 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_590a4 : bv 32 := 0x0480006f.
Lemma F_590a4 : fetch_word Plain.M.loaded_segments (0x590a4 : word) = Some W_590a4.
Proof. vm_refl. Qed.
Lemma D_590a4 : decode_any W_590a4 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_590a8 : bv 32 := 0xfffba597.
Lemma F_590a8 : fetch_word Plain.M.loaded_segments (0x590a8 : word) = Some W_590a8.
Proof. vm_refl. Qed.
Lemma D_590a8 : decode_any W_590a8 = Some (Auipc 11 1048506, 4%Z).
Proof. vm_refl. Qed.

Definition W_590ac : bv 32 := 0xfffba717.
Lemma F_590ac : fetch_word Plain.M.loaded_segments (0x590ac : word) = Some W_590ac.
Proof. vm_refl. Qed.
Lemma D_590ac : decode_any W_590ac = Some (Auipc 14 1048506, 4%Z).
Proof. vm_refl. Qed.

Definition W_590b0 : bv 32 := 0x0805b683.
Lemma F_590b0 : fetch_word Plain.M.loaded_segments (0x590b0 : word) = Some W_590b0.
Proof. vm_refl. Qed.
Lemma D_590b0 : decode_any W_590b0 = Some (Load SZ8 true 13 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_590b4 : bv 32 := 0x06c73703.
Lemma F_590b4 : fetch_word Plain.M.loaded_segments (0x590b4 : word) = Some W_590b4.
Proof. vm_refl. Qed.
Lemma D_590b4 : decode_any W_590b4 = Some (Load SZ8 true 14 14 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_590b8 : bv 32 := 0xff760593.
Lemma F_590b8 : fetch_word Plain.M.loaded_segments (0x590b8 : word) = Some W_590b8.
Proof. vm_refl. Qed.
Lemma D_590b8 : decode_any W_590b8 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_590bc : bv 32 := 0xff860613.
Lemma F_590bc : fetch_word Plain.M.loaded_segments (0x590bc : word) = Some W_590bc.
Proof. vm_refl. Qed.
Lemma D_590bc : decode_any W_590bc = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_590c0 : bv 32 := 0x00863783.
Lemma F_590c0 : fetch_word Plain.M.loaded_segments (0x590c0 : word) = Some W_590c0.
Proof. vm_refl. Qed.
Lemma D_590c0 : decode_any W_590c0 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_590c4 : bv 32 := 0x00860613.
Lemma F_590c4 : fetch_word Plain.M.loaded_segments (0x590c4 : word) = Some W_590c4.
Proof. vm_refl. Qed.
Lemma D_590c4 : decode_any W_590c4 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_590c8 : bv 32 := 0x40f68833.
Lemma F_590c8 : fetch_word Plain.M.loaded_segments (0x590c8 : word) = Some W_590c8.
Proof. vm_refl. Qed.
Lemma D_590c8 : decode_any W_590c8 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_590cc : bv 32 := 0x00f867b3.
Lemma F_590cc : fetch_word Plain.M.loaded_segments (0x590cc : word) = Some W_590cc.
Proof. vm_refl. Qed.
Lemma D_590cc : decode_any W_590cc = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_590d0 : bv 32 := 0x00e7f7b3.
Lemma F_590d0 : fetch_word Plain.M.loaded_segments (0x590d0 : word) = Some W_590d0.
Proof. vm_refl. Qed.
Lemma D_590d0 : decode_any W_590d0 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_590d4 : bv 32 := 0x00858593.
Lemma F_590d4 : fetch_word Plain.M.loaded_segments (0x590d4 : word) = Some W_590d4.
Proof. vm_refl. Qed.
Lemma D_590d4 : decode_any W_590d4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_590d8 : bv 32 := 0xfee784e3.
Lemma F_590d8 : fetch_word Plain.M.loaded_segments (0x590d8 : word) = Some W_590d8.
Proof. vm_refl. Qed.
Lemma D_590d8 : decode_any W_590d8 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_590dc : bv 32 := 0x00064683.
Lemma F_590dc : fetch_word Plain.M.loaded_segments (0x590dc : word) = Some W_590dc.
Proof. vm_refl. Qed.
Lemma D_590dc : decode_any W_590dc = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590e0 : bv 32 := 0x00160613.
Lemma F_590e0 : fetch_word Plain.M.loaded_segments (0x590e0 : word) = Some W_590e0.
Proof. vm_refl. Qed.
Lemma D_590e0 : decode_any W_590e0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_590e4 : bv 32 := 0x00158593.
Lemma F_590e4 : fetch_word Plain.M.loaded_segments (0x590e4 : word) = Some W_590e4.
Proof. vm_refl. Qed.
Lemma D_590e4 : decode_any W_590e4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_590e8 : bv 32 := 0xfe069ae3.
Lemma F_590e8 : fetch_word Plain.M.loaded_segments (0x590e8 : word) = Some W_590e8.
Proof. vm_refl. Qed.
Lemma D_590e8 : decode_any W_590e8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_590ec : bv 32 := 0x40a58533.
Lemma F_590ec : fetch_word Plain.M.loaded_segments (0x590ec : word) = Some W_590ec.
Proof. vm_refl. Qed.
Lemma D_590ec : decode_any W_590ec = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_590f0 : bv 32 := 0x00008067.
Lemma F_590f0 : fetch_word Plain.M.loaded_segments (0x590f0 : word) = Some W_590f0.
Proof. vm_refl. Qed.
Lemma D_590f0 : decode_any W_590f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590f4 : bv 32 := 0x40a50533.
Lemma F_590f4 : fetch_word Plain.M.loaded_segments (0x590f4 : word) = Some W_590f4.
Proof. vm_refl. Qed.
Lemma D_590f4 : decode_any W_590f4 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_590f8 : bv 32 := 0x00008067.
Lemma F_590f8 : fetch_word Plain.M.loaded_segments (0x590f8 : word) = Some W_590f8.
Proof. vm_refl. Qed.
Lemma D_590f8 : decode_any W_590f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_590fc : bv 32 := 0xfe010113.
Lemma F_590fc : fetch_word Plain.M.loaded_segments (0x590fc : word) = Some W_590fc.
Proof. vm_refl. Qed.
Lemma D_590fc : decode_any W_590fc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_59100 : bv 32 := 0x00113c23.
Lemma F_59100 : fetch_word Plain.M.loaded_segments (0x59100 : word) = Some W_59100.
Proof. vm_refl. Qed.
Lemma D_59100 : decode_any W_59100 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59104 : bv 32 := 0x00813823.
Lemma F_59104 : fetch_word Plain.M.loaded_segments (0x59104 : word) = Some W_59104.
Proof. vm_refl. Qed.
Lemma D_59104 : decode_any W_59104 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59108 : bv 32 := 0x00913423.
Lemma F_59108 : fetch_word Plain.M.loaded_segments (0x59108 : word) = Some W_59108.
Proof. vm_refl. Qed.
Lemma D_59108 : decode_any W_59108 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5910c : bv 32 := 0x00058413.
Lemma F_5910c : fetch_word Plain.M.loaded_segments (0x5910c : word) = Some W_5910c.
Proof. vm_refl. Qed.
Lemma D_5910c : decode_any W_5910c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59110 : bv 32 := 0x00050493.
Lemma F_59110 : fetch_word Plain.M.loaded_segments (0x59110 : word) = Some W_59110.
Proof. vm_refl. Qed.
Lemma D_59110 : decode_any W_59110 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59114 : bv 32 := 0x00000593.
Lemma F_59114 : fetch_word Plain.M.loaded_segments (0x59114 : word) = Some W_59114.
Proof. vm_refl. Qed.
Lemma D_59114 : decode_any W_59114 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59118 : bv 32 := 0x00040613.
Lemma F_59118 : fetch_word Plain.M.loaded_segments (0x59118 : word) = Some W_59118.
Proof. vm_refl. Qed.
Lemma D_59118 : decode_any W_59118 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5911c : bv 32 := 0xf0cff0ef.
Lemma F_5911c : fetch_word Plain.M.loaded_segments (0x5911c : word) = Some W_5911c.
Proof. vm_refl. Qed.
Lemma D_5911c : decode_any W_5911c = Some (Jal 1 2094860, 4%Z).
Proof. vm_refl. Qed.

Definition W_59120 : bv 32 := 0x00050463.
Lemma F_59120 : fetch_word Plain.M.loaded_segments (0x59120 : word) = Some W_59120.
Proof. vm_refl. Qed.
Lemma D_59120 : decode_any W_59120 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59124 : bv 32 := 0x40950433.
Lemma F_59124 : fetch_word Plain.M.loaded_segments (0x59124 : word) = Some W_59124.
Proof. vm_refl. Qed.
Lemma D_59124 : decode_any W_59124 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_59128 : bv 32 := 0x00040513.
Lemma F_59128 : fetch_word Plain.M.loaded_segments (0x59128 : word) = Some W_59128.
Proof. vm_refl. Qed.
Lemma D_59128 : decode_any W_59128 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5912c : bv 32 := 0x01813083.
Lemma F_5912c : fetch_word Plain.M.loaded_segments (0x5912c : word) = Some W_5912c.
Proof. vm_refl. Qed.
Lemma D_5912c : decode_any W_5912c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_59130 : bv 32 := 0x01013403.
Lemma F_59130 : fetch_word Plain.M.loaded_segments (0x59130 : word) = Some W_59130.
Proof. vm_refl. Qed.
Lemma D_59130 : decode_any W_59130 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_59134 : bv 32 := 0x00813483.
Lemma F_59134 : fetch_word Plain.M.loaded_segments (0x59134 : word) = Some W_59134.
Proof. vm_refl. Qed.
Lemma D_59134 : decode_any W_59134 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_59138 : bv 32 := 0x02010113.
Lemma F_59138 : fetch_word Plain.M.loaded_segments (0x59138 : word) = Some W_59138.
Proof. vm_refl. Qed.
Lemma D_59138 : decode_any W_59138 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5913c : bv 32 := 0x00008067.
Lemma F_5913c : fetch_word Plain.M.loaded_segments (0x5913c : word) = Some W_5913c.
Proof. vm_refl. Qed.
Lemma D_5913c : decode_any W_5913c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59228 : bv 32 := 0x00037597.
Lemma F_59228 : fetch_word Plain.M.loaded_segments (0x59228 : word) = Some W_59228.
Proof. vm_refl. Qed.
Lemma D_59228 : decode_any W_59228 = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

Definition W_5922c : bv 32 := 0x4a358683.
Lemma F_5922c : fetch_word Plain.M.loaded_segments (0x5922c : word) = Some W_5922c.
Proof. vm_refl. Qed.
Lemma D_5922c : decode_any W_5922c = Some (Load SZ1 true 13 11 1187, 4%Z).
Proof. vm_refl. Qed.

Definition W_59230 : bv 32 := 0x1e068863.
Lemma F_59230 : fetch_word Plain.M.loaded_segments (0x59230 : word) = Some W_59230.
Proof. vm_refl. Qed.
Lemma D_59230 : decode_any W_59230 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_59420 : bv 32 := 0x00008067.
Lemma F_59420 : fetch_word Plain.M.loaded_segments (0x59420 : word) = Some W_59420.
Proof. vm_refl. Qed.
Lemma D_59420 : decode_any W_59420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59524 : bv 32 := 0x00050893.
Lemma F_59524 : fetch_word Plain.M.loaded_segments (0x59524 : word) = Some W_59524.
Proof. vm_refl. Qed.
Lemma D_59524 : decode_any W_59524 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59528 : bv 32 := 0x00058513.
Lemma F_59528 : fetch_word Plain.M.loaded_segments (0x59528 : word) = Some W_59528.
Proof. vm_refl. Qed.
Lemma D_59528 : decode_any W_59528 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5952c : bv 32 := 0x00060593.
Lemma F_5952c : fetch_word Plain.M.loaded_segments (0x5952c : word) = Some W_5952c.
Proof. vm_refl. Qed.
Lemma D_5952c : decode_any W_5952c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59530 : bv 32 := 0x00068613.
Lemma F_59530 : fetch_word Plain.M.loaded_segments (0x59530 : word) = Some W_59530.
Proof. vm_refl. Qed.
Lemma D_59530 : decode_any W_59530 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59534 : bv 32 := 0x00070693.
Lemma F_59534 : fetch_word Plain.M.loaded_segments (0x59534 : word) = Some W_59534.
Proof. vm_refl. Qed.
Lemma D_59534 : decode_any W_59534 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59538 : bv 32 := 0x00078713.
Lemma F_59538 : fetch_word Plain.M.loaded_segments (0x59538 : word) = Some W_59538.
Proof. vm_refl. Qed.
Lemma D_59538 : decode_any W_59538 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5953c : bv 32 := 0x00080793.
Lemma F_5953c : fetch_word Plain.M.loaded_segments (0x5953c : word) = Some W_5953c.
Proof. vm_refl. Qed.
Lemma D_5953c : decode_any W_5953c = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.
