(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_b5908 : bv 32 := 0x0ff5f593.
Lemma F_b5908 : fetch_word Ubsan.M.loaded_segments (0xb7798 : word) = Some W_b5908.
Proof. vm_refl. Qed.
Lemma D_b5908 : decode_any W_b5908 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_b590c : bv 32 := 0x00757693.
Lemma F_b590c : fetch_word Ubsan.M.loaded_segments (0xb779c : word) = Some W_b590c.
Proof. vm_refl. Qed.
Lemma D_b590c : decode_any W_b590c = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5910 : bv 32 := 0x00c03733.
Lemma F_b5910 : fetch_word Ubsan.M.loaded_segments (0xb77a0 : word) = Some W_b5910.
Proof. vm_refl. Qed.
Lemma D_b5910 : decode_any W_b5910 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5914 : bv 32 := 0x02068c63.
Lemma F_b5914 : fetch_word Ubsan.M.loaded_segments (0xb77a4 : word) = Some W_b5914.
Proof. vm_refl. Qed.
Lemma D_b5914 : decode_any W_b5914 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5918 : bv 32 := 0x02060a63.
Lemma F_b5918 : fetch_word Ubsan.M.loaded_segments (0xb77a8 : word) = Some W_b5918.
Proof. vm_refl. Qed.
Lemma D_b5918 : decode_any W_b5918 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_b591c : bv 32 := 0x00150793.
Lemma F_b591c : fetch_word Ubsan.M.loaded_segments (0xb77ac : word) = Some W_b591c.
Proof. vm_refl. Qed.
Lemma D_b591c : decode_any W_b591c = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5920 : bv 32 := 0x00100813.
Lemma F_b5920 : fetch_word Ubsan.M.loaded_segments (0xb77b0 : word) = Some W_b5920.
Proof. vm_refl. Qed.
Lemma D_b5920 : decode_any W_b5920 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5924 : bv 32 := 0x00054703.
Lemma F_b5924 : fetch_word Ubsan.M.loaded_segments (0xb77b4 : word) = Some W_b5924.
Proof. vm_refl. Qed.
Lemma D_b5924 : decode_any W_b5924 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5928 : bv 32 := 0x00060693.
Lemma F_b5928 : fetch_word Ubsan.M.loaded_segments (0xb77b8 : word) = Some W_b5928.
Proof. vm_refl. Qed.
Lemma D_b5928 : decode_any W_b5928 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b592c : bv 32 := 0x06b70e63.
Lemma F_b592c : fetch_word Ubsan.M.loaded_segments (0xb77bc : word) = Some W_b592c.
Proof. vm_refl. Qed.
Lemma D_b592c : decode_any W_b592c = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5930 : bv 32 := 0x00150513.
Lemma F_b5930 : fetch_word Ubsan.M.loaded_segments (0xb77c0 : word) = Some W_b5930.
Proof. vm_refl. Qed.
Lemma D_b5930 : decode_any W_b5930 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5934 : bv 32 := 0xfff68613.
Lemma F_b5934 : fetch_word Ubsan.M.loaded_segments (0xb77c4 : word) = Some W_b5934.
Proof. vm_refl. Qed.
Lemma D_b5934 : decode_any W_b5934 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5938 : bv 32 := 0x0077f893.
Lemma F_b5938 : fetch_word Ubsan.M.loaded_segments (0xb77c8 : word) = Some W_b5938.
Proof. vm_refl. Qed.
Lemma D_b5938 : decode_any W_b5938 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b593c : bv 32 := 0x00c03733.
Lemma F_b593c : fetch_word Ubsan.M.loaded_segments (0xb77cc : word) = Some W_b593c.
Proof. vm_refl. Qed.
Lemma D_b593c : decode_any W_b593c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5940 : bv 32 := 0x00088663.
Lemma F_b5940 : fetch_word Ubsan.M.loaded_segments (0xb77d0 : word) = Some W_b5940.
Proof. vm_refl. Qed.
Lemma D_b5940 : decode_any W_b5940 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5944 : bv 32 := 0x00178793.
Lemma F_b5944 : fetch_word Ubsan.M.loaded_segments (0xb77d4 : word) = Some W_b5944.
Proof. vm_refl. Qed.
Lemma D_b5944 : decode_any W_b5944 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5948 : bv 32 := 0xfd069ee3.
Lemma F_b5948 : fetch_word Ubsan.M.loaded_segments (0xb77d8 : word) = Some W_b5948.
Proof. vm_refl. Qed.
Lemma D_b5948 : decode_any W_b5948 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_b594c : bv 32 := 0x06070863.
Lemma F_b594c : fetch_word Ubsan.M.loaded_segments (0xb77dc : word) = Some W_b594c.
Proof. vm_refl. Qed.
Lemma D_b594c : decode_any W_b594c = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5950 : bv 32 := 0x00054683.
Lemma F_b5950 : fetch_word Ubsan.M.loaded_segments (0xb77e0 : word) = Some W_b5950.
Proof. vm_refl. Qed.
Lemma D_b5950 : decode_any W_b5950 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5954 : bv 32 := 0x04b68663.
Lemma F_b5954 : fetch_word Ubsan.M.loaded_segments (0xb77e4 : word) = Some W_b5954.
Proof. vm_refl. Qed.
Lemma D_b5954 : decode_any W_b5954 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5958 : bv 32 := 0x00800693.
Lemma F_b5958 : fetch_word Ubsan.M.loaded_segments (0xb77e8 : word) = Some W_b5958.
Proof. vm_refl. Qed.
Lemma D_b5958 : decode_any W_b5958 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b595c : bv 32 := 0x04d66263.
Lemma F_b595c : fetch_word Ubsan.M.loaded_segments (0xb77ec : word) = Some W_b595c.
Proof. vm_refl. Qed.
Lemma D_b595c : decode_any W_b595c = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5960 : bv 32 := 0xfff5d697.
Lemma F_b5960 : fetch_word Ubsan.M.loaded_segments (0xb77f0 : word) = Some W_b5960.
Proof. vm_refl. Qed.
Lemma D_b5960 : decode_any W_b5960 = Some (Auipc 13 1048413, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5964 : bv 32 := 0xff06b683.
Lemma F_b5964 : fetch_word Ubsan.M.loaded_segments (0xb77f4 : word) = Some W_b5964.
Proof. vm_refl. Qed.
Lemma D_b5964 : decode_any W_b5964 = Some (Load SZ8 true 13 13 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5968 : bv 32 := 0xfff5d717.
Lemma F_b5968 : fetch_word Ubsan.M.loaded_segments (0xb77f8 : word) = Some W_b5968.
Proof. vm_refl. Qed.
Lemma D_b5968 : decode_any W_b5968 = Some (Auipc 14 1048413, 4%Z).
Proof. vm_refl. Qed.

Definition W_b596c : bv 32 := 0xfd873703.
Lemma F_b596c : fetch_word Ubsan.M.loaded_segments (0xb77fc : word) = Some W_b596c.
Proof. vm_refl. Qed.
Lemma D_b596c : decode_any W_b596c = Some (Load SZ8 true 14 14 4056, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5970 : bv 32 := 0x00168793.
Lemma F_b5970 : fetch_word Ubsan.M.loaded_segments (0xb7800 : word) = Some W_b5970.
Proof. vm_refl. Qed.
Lemma D_b5970 : decode_any W_b5970 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5974 : bv 32 := 0x02f587b3.
Lemma F_b5974 : fetch_word Ubsan.M.loaded_segments (0xb7804 : word) = Some W_b5974.
Proof. vm_refl. Qed.
Lemma D_b5974 : decode_any W_b5974 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5978 : bv 32 := 0x00700813.
Lemma F_b5978 : fetch_word Ubsan.M.loaded_segments (0xb7808 : word) = Some W_b5978.
Proof. vm_refl. Qed.
Lemma D_b5978 : decode_any W_b5978 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b597c : bv 32 := 0x00053883.
Lemma F_b597c : fetch_word Ubsan.M.loaded_segments (0xb780c : word) = Some W_b597c.
Proof. vm_refl. Qed.
Lemma D_b597c : decode_any W_b597c = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5980 : bv 32 := 0x00f8c8b3.
Lemma F_b5980 : fetch_word Ubsan.M.loaded_segments (0xb7810 : word) = Some W_b5980.
Proof. vm_refl. Qed.
Lemma D_b5980 : decode_any W_b5980 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5984 : bv 32 := 0x411682b3.
Lemma F_b5984 : fetch_word Ubsan.M.loaded_segments (0xb7814 : word) = Some W_b5984.
Proof. vm_refl. Qed.
Lemma D_b5984 : decode_any W_b5984 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5988 : bv 32 := 0x0112e8b3.
Lemma F_b5988 : fetch_word Ubsan.M.loaded_segments (0xb7818 : word) = Some W_b5988.
Proof. vm_refl. Qed.
Lemma D_b5988 : decode_any W_b5988 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b598c : bv 32 := 0x00e8f8b3.
Lemma F_b598c : fetch_word Ubsan.M.loaded_segments (0xb781c : word) = Some W_b598c.
Proof. vm_refl. Qed.
Lemma D_b598c : decode_any W_b598c = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5990 : bv 32 := 0x02e89a63.
Lemma F_b5990 : fetch_word Ubsan.M.loaded_segments (0xb7820 : word) = Some W_b5990.
Proof. vm_refl. Qed.
Lemma D_b5990 : decode_any W_b5990 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5994 : bv 32 := 0xff860613.
Lemma F_b5994 : fetch_word Ubsan.M.loaded_segments (0xb7824 : word) = Some W_b5994.
Proof. vm_refl. Qed.
Lemma D_b5994 : decode_any W_b5994 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5998 : bv 32 := 0x00850513.
Lemma F_b5998 : fetch_word Ubsan.M.loaded_segments (0xb7828 : word) = Some W_b5998.
Proof. vm_refl. Qed.
Lemma D_b5998 : decode_any W_b5998 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b599c : bv 32 := 0xfec860e3.
Lemma F_b599c : fetch_word Ubsan.M.loaded_segments (0xb782c : word) = Some W_b599c.
Proof. vm_refl. Qed.
Lemma D_b599c : decode_any W_b599c = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59a0 : bv 32 := 0x00060693.
Lemma F_b59a0 : fetch_word Ubsan.M.loaded_segments (0xb7830 : word) = Some W_b59a0.
Proof. vm_refl. Qed.
Lemma D_b59a0 : decode_any W_b59a0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59a4 : bv 32 := 0x00060c63.
Lemma F_b59a4 : fetch_word Ubsan.M.loaded_segments (0xb7834 : word) = Some W_b59a4.
Proof. vm_refl. Qed.
Lemma D_b59a4 : decode_any W_b59a4 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59a8 : bv 32 := 0x00054603.
Lemma F_b59a8 : fetch_word Ubsan.M.loaded_segments (0xb7838 : word) = Some W_b59a8.
Proof. vm_refl. Qed.
Lemma D_b59a8 : decode_any W_b59a8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59ac : bv 32 := 0x00b60a63.
Lemma F_b59ac : fetch_word Ubsan.M.loaded_segments (0xb783c : word) = Some W_b59ac.
Proof. vm_refl. Qed.
Lemma D_b59ac : decode_any W_b59ac = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59b0 : bv 32 := 0xfff68693.
Lemma F_b59b0 : fetch_word Ubsan.M.loaded_segments (0xb7840 : word) = Some W_b59b0.
Proof. vm_refl. Qed.
Lemma D_b59b0 : decode_any W_b59b0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59b4 : bv 32 := 0x00150513.
Lemma F_b59b4 : fetch_word Ubsan.M.loaded_segments (0xb7844 : word) = Some W_b59b4.
Proof. vm_refl. Qed.
Lemma D_b59b4 : decode_any W_b59b4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59b8 : bv 32 := 0xfe0698e3.
Lemma F_b59b8 : fetch_word Ubsan.M.loaded_segments (0xb7848 : word) = Some W_b59b8.
Proof. vm_refl. Qed.
Lemma D_b59b8 : decode_any W_b59b8 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59c0 : bv 32 := 0x00008067.
Lemma F_b59c0 : fetch_word Ubsan.M.loaded_segments (0xb7850 : word) = Some W_b59c0.
Proof. vm_refl. Qed.
Lemma D_b59c0 : decode_any W_b59c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59c4 : bv 32 := 0x00060693.
Lemma F_b59c4 : fetch_word Ubsan.M.loaded_segments (0xb7854 : word) = Some W_b59c4.
Proof. vm_refl. Qed.
Lemma D_b59c4 : decode_any W_b59c4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59c8 : bv 32 := 0x00054603.
Lemma F_b59c8 : fetch_word Ubsan.M.loaded_segments (0xb7858 : word) = Some W_b59c8.
Proof. vm_refl. Qed.
Lemma D_b59c8 : decode_any W_b59c8 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59cc : bv 32 := 0xfeb612e3.
Lemma F_b59cc : fetch_word Ubsan.M.loaded_segments (0xb785c : word) = Some W_b59cc.
Proof. vm_refl. Qed.
Lemma D_b59cc : decode_any W_b59cc = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_b59d0 : bv 32 := 0xff1ff06f.
Lemma F_b59d0 : fetch_word Ubsan.M.loaded_segments (0xb7860 : word) = Some W_b59d0.
Proof. vm_refl. Qed.
Lemma D_b59d0 : decode_any W_b59d0 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a04 : bv 32 := 0x0035f693.
Lemma F_b5a04 : fetch_word Ubsan.M.loaded_segments (0xb7894 : word) = Some W_b5a04.
Proof. vm_refl. Qed.
Lemma D_b5a04 : decode_any W_b5a04 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a08 : bv 32 := 0x10068863.
Lemma F_b5a08 : fetch_word Ubsan.M.loaded_segments (0xb7898 : word) = Some W_b5a08.
Proof. vm_refl. Qed.
Lemma D_b5a08 : decode_any W_b5a08 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a0c : bv 32 := 0x02060e63.
Lemma F_b5a0c : fetch_word Ubsan.M.loaded_segments (0xb789c : word) = Some W_b5a0c.
Proof. vm_refl. Qed.
Lemma D_b5a0c : decode_any W_b5a0c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a10 : bv 32 := 0x00158713.
Lemma F_b5a10 : fetch_word Ubsan.M.loaded_segments (0xb78a0 : word) = Some W_b5a10.
Proof. vm_refl. Qed.
Lemma D_b5a10 : decode_any W_b5a10 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a14 : bv 32 := 0x00100793.
Lemma F_b5a14 : fetch_word Ubsan.M.loaded_segments (0xb78a4 : word) = Some W_b5a14.
Proof. vm_refl. Qed.
Lemma D_b5a14 : decode_any W_b5a14 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a18 : bv 32 := 0x00050693.
Lemma F_b5a18 : fetch_word Ubsan.M.loaded_segments (0xb78a8 : word) = Some W_b5a18.
Proof. vm_refl. Qed.
Lemma D_b5a18 : decode_any W_b5a18 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a1c : bv 32 := 0x0005c883.
Lemma F_b5a1c : fetch_word Ubsan.M.loaded_segments (0xb78ac : word) = Some W_b5a1c.
Proof. vm_refl. Qed.
Lemma D_b5a1c : decode_any W_b5a1c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a20 : bv 32 := 0x00060813.
Lemma F_b5a20 : fetch_word Ubsan.M.loaded_segments (0xb78b0 : word) = Some W_b5a20.
Proof. vm_refl. Qed.
Lemma D_b5a20 : decode_any W_b5a20 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a24 : bv 32 := 0x00158593.
Lemma F_b5a24 : fetch_word Ubsan.M.loaded_segments (0xb78b4 : word) = Some W_b5a24.
Proof. vm_refl. Qed.
Lemma D_b5a24 : decode_any W_b5a24 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a28 : bv 32 := 0x00377293.
Lemma F_b5a28 : fetch_word Ubsan.M.loaded_segments (0xb78b8 : word) = Some W_b5a28.
Proof. vm_refl. Qed.
Lemma D_b5a28 : decode_any W_b5a28 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a2c : bv 32 := 0x01168023.
Lemma F_b5a2c : fetch_word Ubsan.M.loaded_segments (0xb78bc : word) = Some W_b5a2c.
Proof. vm_refl. Qed.
Lemma D_b5a2c : decode_any W_b5a2c = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a30 : bv 32 := 0x00168693.
Lemma F_b5a30 : fetch_word Ubsan.M.loaded_segments (0xb78c0 : word) = Some W_b5a30.
Proof. vm_refl. Qed.
Lemma D_b5a30 : decode_any W_b5a30 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a34 : bv 32 := 0xfff60613.
Lemma F_b5a34 : fetch_word Ubsan.M.loaded_segments (0xb78c4 : word) = Some W_b5a34.
Proof. vm_refl. Qed.
Lemma D_b5a34 : decode_any W_b5a34 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a38 : bv 32 := 0x00028a63.
Lemma F_b5a38 : fetch_word Ubsan.M.loaded_segments (0xb78c8 : word) = Some W_b5a38.
Proof. vm_refl. Qed.
Lemma D_b5a38 : decode_any W_b5a38 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a3c : bv 32 := 0x00170713.
Lemma F_b5a3c : fetch_word Ubsan.M.loaded_segments (0xb78cc : word) = Some W_b5a3c.
Proof. vm_refl. Qed.
Lemma D_b5a3c : decode_any W_b5a3c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a40 : bv 32 := 0xfcf81ee3.
Lemma F_b5a40 : fetch_word Ubsan.M.loaded_segments (0xb78d0 : word) = Some W_b5a40.
Proof. vm_refl. Qed.
Lemma D_b5a40 : decode_any W_b5a40 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a44 : bv 32 := 0x0080006f.
Lemma F_b5a44 : fetch_word Ubsan.M.loaded_segments (0xb78d4 : word) = Some W_b5a44.
Proof. vm_refl. Qed.
Lemma D_b5a44 : decode_any W_b5a44 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a48 : bv 32 := 0x00050693.
Lemma F_b5a48 : fetch_word Ubsan.M.loaded_segments (0xb78d8 : word) = Some W_b5a48.
Proof. vm_refl. Qed.
Lemma D_b5a48 : decode_any W_b5a48 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a4c : bv 32 := 0x0036f793.
Lemma F_b5a4c : fetch_word Ubsan.M.loaded_segments (0xb78dc : word) = Some W_b5a4c.
Proof. vm_refl. Qed.
Lemma D_b5a4c : decode_any W_b5a4c = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a50 : bv 32 := 0x0c078a63.
Lemma F_b5a50 : fetch_word Ubsan.M.loaded_segments (0xb78e0 : word) = Some W_b5a50.
Proof. vm_refl. Qed.
Lemma D_b5a50 : decode_any W_b5a50 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a54 : bv 32 := 0x02000713.
Lemma F_b5a54 : fetch_word Ubsan.M.loaded_segments (0xb78e4 : word) = Some W_b5a54.
Proof. vm_refl. Qed.
Lemma D_b5a54 : decode_any W_b5a54 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a58 : bv 32 := 0x02e67063.
Lemma F_b5a58 : fetch_word Ubsan.M.loaded_segments (0xb78e8 : word) = Some W_b5a58.
Proof. vm_refl. Qed.
Lemma D_b5a58 : decode_any W_b5a58 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a5c : bv 32 := 0x01000713.
Lemma F_b5a5c : fetch_word Ubsan.M.loaded_segments (0xb78ec : word) = Some W_b5a5c.
Proof. vm_refl. Qed.
Lemma D_b5a5c : decode_any W_b5a5c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a60 : bv 32 := 0x24e67863.
Lemma F_b5a60 : fetch_word Ubsan.M.loaded_segments (0xb78f0 : word) = Some W_b5a60.
Proof. vm_refl. Qed.
Lemma D_b5a60 : decode_any W_b5a60 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a64 : bv 32 := 0x00867713.
Lemma F_b5a64 : fetch_word Ubsan.M.loaded_segments (0xb78f4 : word) = Some W_b5a64.
Proof. vm_refl. Qed.
Lemma D_b5a64 : decode_any W_b5a64 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a68 : bv 32 := 0x2c071e63.
Lemma F_b5a68 : fetch_word Ubsan.M.loaded_segments (0xb78f8 : word) = Some W_b5a68.
Proof. vm_refl. Qed.
Lemma D_b5a68 : decode_any W_b5a68 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a6c : bv 32 := 0x00467713.
Lemma F_b5a6c : fetch_word Ubsan.M.loaded_segments (0xb78fc : word) = Some W_b5a6c.
Proof. vm_refl. Qed.
Lemma D_b5a6c : decode_any W_b5a6c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a70 : bv 32 := 0x32071463.
Lemma F_b5a70 : fetch_word Ubsan.M.loaded_segments (0xb7900 : word) = Some W_b5a70.
Proof. vm_refl. Qed.
Lemma D_b5a70 : decode_any W_b5a70 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a74 : bv 32 := 0x3500006f.
Lemma F_b5a74 : fetch_word Ubsan.M.loaded_segments (0xb7904 : word) = Some W_b5a74.
Proof. vm_refl. Qed.
Lemma D_b5a74 : decode_any W_b5a74 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a78 : bv 32 := 0x0005a703.
Lemma F_b5a78 : fetch_word Ubsan.M.loaded_segments (0xb7908 : word) = Some W_b5a78.
Proof. vm_refl. Qed.
Lemma D_b5a78 : decode_any W_b5a78 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a7c : bv 32 := 0x00300813.
Lemma F_b5a7c : fetch_word Ubsan.M.loaded_segments (0xb790c : word) = Some W_b5a7c.
Proof. vm_refl. Qed.
Lemma D_b5a7c : decode_any W_b5a7c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a80 : bv 32 := 0x11078e63.
Lemma F_b5a80 : fetch_word Ubsan.M.loaded_segments (0xb7910 : word) = Some W_b5a80.
Proof. vm_refl. Qed.
Lemma D_b5a80 : decode_any W_b5a80 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a84 : bv 32 := 0x00200813.
Lemma F_b5a84 : fetch_word Ubsan.M.loaded_segments (0xb7914 : word) = Some W_b5a84.
Proof. vm_refl. Qed.
Lemma D_b5a84 : decode_any W_b5a84 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a88 : bv 32 := 0x19079c63.
Lemma F_b5a88 : fetch_word Ubsan.M.loaded_segments (0xb7918 : word) = Some W_b5a88.
Proof. vm_refl. Qed.
Lemma D_b5a88 : decode_any W_b5a88 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a8c : bv 32 := 0x00875793.
Lemma F_b5a8c : fetch_word Ubsan.M.loaded_segments (0xb791c : word) = Some W_b5a8c.
Proof. vm_refl. Qed.
Lemma D_b5a8c : decode_any W_b5a8c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a90 : bv 32 := 0xffe60613.
Lemma F_b5a90 : fetch_word Ubsan.M.loaded_segments (0xb7920 : word) = Some W_b5a90.
Proof. vm_refl. Qed.
Lemma D_b5a90 : decode_any W_b5a90 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a94 : bv 32 := 0x00e68023.
Lemma F_b5a94 : fetch_word Ubsan.M.loaded_segments (0xb7924 : word) = Some W_b5a94.
Proof. vm_refl. Qed.
Lemma D_b5a94 : decode_any W_b5a94 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a98 : bv 32 := 0x00f680a3.
Lemma F_b5a98 : fetch_word Ubsan.M.loaded_segments (0xb7928 : word) = Some W_b5a98.
Proof. vm_refl. Qed.
Lemma D_b5a98 : decode_any W_b5a98 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5a9c : bv 32 := 0x00268693.
Lemma F_b5a9c : fetch_word Ubsan.M.loaded_segments (0xb792c : word) = Some W_b5a9c.
Proof. vm_refl. Qed.
Lemma D_b5a9c : decode_any W_b5a9c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5aa0 : bv 32 := 0x01058593.
Lemma F_b5aa0 : fetch_word Ubsan.M.loaded_segments (0xb7930 : word) = Some W_b5aa0.
Proof. vm_refl. Qed.
Lemma D_b5aa0 : decode_any W_b5aa0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5aa4 : bv 32 := 0x01100793.
Lemma F_b5aa4 : fetch_word Ubsan.M.loaded_segments (0xb7934 : word) = Some W_b5aa4.
Proof. vm_refl. Qed.
Lemma D_b5aa4 : decode_any W_b5aa4 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5aa8 : bv 32 := 0x0107581b.
Lemma F_b5aa8 : fetch_word Ubsan.M.loaded_segments (0xb7938 : word) = Some W_b5aa8.
Proof. vm_refl. Qed.
Lemma D_b5aa8 : decode_any W_b5aa8 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5aac : bv 32 := 0xff45a883.
Lemma F_b5aac : fetch_word Ubsan.M.loaded_segments (0xb793c : word) = Some W_b5aac.
Proof. vm_refl. Qed.
Lemma D_b5aac : decode_any W_b5aac = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ab0 : bv 32 := 0xff85a283.
Lemma F_b5ab0 : fetch_word Ubsan.M.loaded_segments (0xb7940 : word) = Some W_b5ab0.
Proof. vm_refl. Qed.
Lemma D_b5ab0 : decode_any W_b5ab0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ab4 : bv 32 := 0xffc5a303.
Lemma F_b5ab4 : fetch_word Ubsan.M.loaded_segments (0xb7944 : word) = Some W_b5ab4.
Proof. vm_refl. Qed.
Lemma D_b5ab4 : decode_any W_b5ab4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ab8 : bv 32 := 0x0005a703.
Lemma F_b5ab8 : fetch_word Ubsan.M.loaded_segments (0xb7948 : word) = Some W_b5ab8.
Proof. vm_refl. Qed.
Lemma D_b5ab8 : decode_any W_b5ab8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5abc : bv 32 := 0x01089393.
Lemma F_b5abc : fetch_word Ubsan.M.loaded_segments (0xb794c : word) = Some W_b5abc.
Proof. vm_refl. Qed.
Lemma D_b5abc : decode_any W_b5abc = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ac0 : bv 32 := 0x0108d89b.
Lemma F_b5ac0 : fetch_word Ubsan.M.loaded_segments (0xb7950 : word) = Some W_b5ac0.
Proof. vm_refl. Qed.
Lemma D_b5ac0 : decode_any W_b5ac0 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ac4 : bv 32 := 0x0103e833.
Lemma F_b5ac4 : fetch_word Ubsan.M.loaded_segments (0xb7954 : word) = Some W_b5ac4.
Proof. vm_refl. Qed.
Lemma D_b5ac4 : decode_any W_b5ac4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ac8 : bv 32 := 0x01029393.
Lemma F_b5ac8 : fetch_word Ubsan.M.loaded_segments (0xb7958 : word) = Some W_b5ac8.
Proof. vm_refl. Qed.
Lemma D_b5ac8 : decode_any W_b5ac8 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5acc : bv 32 := 0x0102d29b.
Lemma F_b5acc : fetch_word Ubsan.M.loaded_segments (0xb795c : word) = Some W_b5acc.
Proof. vm_refl. Qed.
Lemma D_b5acc : decode_any W_b5acc = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ad0 : bv 32 := 0x0113e8b3.
Lemma F_b5ad0 : fetch_word Ubsan.M.loaded_segments (0xb7960 : word) = Some W_b5ad0.
Proof. vm_refl. Qed.
Lemma D_b5ad0 : decode_any W_b5ad0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ad4 : bv 32 := 0x01031393.
Lemma F_b5ad4 : fetch_word Ubsan.M.loaded_segments (0xb7964 : word) = Some W_b5ad4.
Proof. vm_refl. Qed.
Lemma D_b5ad4 : decode_any W_b5ad4 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ad8 : bv 32 := 0x0103531b.
Lemma F_b5ad8 : fetch_word Ubsan.M.loaded_segments (0xb7968 : word) = Some W_b5ad8.
Proof. vm_refl. Qed.
Lemma D_b5ad8 : decode_any W_b5ad8 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5adc : bv 32 := 0x0053e2b3.
Lemma F_b5adc : fetch_word Ubsan.M.loaded_segments (0xb796c : word) = Some W_b5adc.
Proof. vm_refl. Qed.
Lemma D_b5adc : decode_any W_b5adc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ae0 : bv 32 := 0x01071393.
Lemma F_b5ae0 : fetch_word Ubsan.M.loaded_segments (0xb7970 : word) = Some W_b5ae0.
Proof. vm_refl. Qed.
Lemma D_b5ae0 : decode_any W_b5ae0 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ae4 : bv 32 := 0x0063e333.
Lemma F_b5ae4 : fetch_word Ubsan.M.loaded_segments (0xb7974 : word) = Some W_b5ae4.
Proof. vm_refl. Qed.
Lemma D_b5ae4 : decode_any W_b5ae4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ae8 : bv 32 := 0xff060613.
Lemma F_b5ae8 : fetch_word Ubsan.M.loaded_segments (0xb7978 : word) = Some W_b5ae8.
Proof. vm_refl. Qed.
Lemma D_b5ae8 : decode_any W_b5ae8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5aec : bv 32 := 0x0106a023.
Lemma F_b5aec : fetch_word Ubsan.M.loaded_segments (0xb797c : word) = Some W_b5aec.
Proof. vm_refl. Qed.
Lemma D_b5aec : decode_any W_b5aec = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5af0 : bv 32 := 0x0116a223.
Lemma F_b5af0 : fetch_word Ubsan.M.loaded_segments (0xb7980 : word) = Some W_b5af0.
Proof. vm_refl. Qed.
Lemma D_b5af0 : decode_any W_b5af0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5af4 : bv 32 := 0x0056a423.
Lemma F_b5af4 : fetch_word Ubsan.M.loaded_segments (0xb7984 : word) = Some W_b5af4.
Proof. vm_refl. Qed.
Lemma D_b5af4 : decode_any W_b5af4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5af8 : bv 32 := 0x0066a623.
Lemma F_b5af8 : fetch_word Ubsan.M.loaded_segments (0xb7988 : word) = Some W_b5af8.
Proof. vm_refl. Qed.
Lemma D_b5af8 : decode_any W_b5af8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5afc : bv 32 := 0x01068693.
Lemma F_b5afc : fetch_word Ubsan.M.loaded_segments (0xb798c : word) = Some W_b5afc.
Proof. vm_refl. Qed.
Lemma D_b5afc : decode_any W_b5afc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b00 : bv 32 := 0x01058593.
Lemma F_b5b00 : fetch_word Ubsan.M.loaded_segments (0xb7990 : word) = Some W_b5b00.
Proof. vm_refl. Qed.
Lemma D_b5b00 : decode_any W_b5b00 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b04 : bv 32 := 0xfac7e2e3.
Lemma F_b5b04 : fetch_word Ubsan.M.loaded_segments (0xb7994 : word) = Some W_b5b04.
Proof. vm_refl. Qed.
Lemma D_b5b04 : decode_any W_b5b04 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b08 : bv 32 := 0xff258593.
Lemma F_b5b08 : fetch_word Ubsan.M.loaded_segments (0xb7998 : word) = Some W_b5b08.
Proof. vm_refl. Qed.
Lemma D_b5b08 : decode_any W_b5b08 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b0c : bv 32 := 0x01000713.
Lemma F_b5b0c : fetch_word Ubsan.M.loaded_segments (0xb799c : word) = Some W_b5b0c.
Proof. vm_refl. Qed.
Lemma D_b5b0c : decode_any W_b5b0c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b10 : bv 32 := 0xf4e66ae3.
Lemma F_b5b10 : fetch_word Ubsan.M.loaded_segments (0xb79a0 : word) = Some W_b5b10.
Proof. vm_refl. Qed.
Lemma D_b5b10 : decode_any W_b5b10 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b14 : bv 32 := 0x19c0006f.
Lemma F_b5b14 : fetch_word Ubsan.M.loaded_segments (0xb79a4 : word) = Some W_b5b14.
Proof. vm_refl. Qed.
Lemma D_b5b14 : decode_any W_b5b14 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b18 : bv 32 := 0x00050693.
Lemma F_b5b18 : fetch_word Ubsan.M.loaded_segments (0xb79a8 : word) = Some W_b5b18.
Proof. vm_refl. Qed.
Lemma D_b5b18 : decode_any W_b5b18 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b1c : bv 32 := 0x00357793.
Lemma F_b5b1c : fetch_word Ubsan.M.loaded_segments (0xb79ac : word) = Some W_b5b1c.
Proof. vm_refl. Qed.
Lemma D_b5b1c : decode_any W_b5b1c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b20 : bv 32 := 0xf2079ae3.
Lemma F_b5b20 : fetch_word Ubsan.M.loaded_segments (0xb79b0 : word) = Some W_b5b20.
Proof. vm_refl. Qed.
Lemma D_b5b20 : decode_any W_b5b20 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b24 : bv 32 := 0x01000713.
Lemma F_b5b24 : fetch_word Ubsan.M.loaded_segments (0xb79b4 : word) = Some W_b5b24.
Proof. vm_refl. Qed.
Lemma D_b5b24 : decode_any W_b5b24 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b28 : bv 32 := 0x02e66c63.
Lemma F_b5b28 : fetch_word Ubsan.M.loaded_segments (0xb79b8 : word) = Some W_b5b28.
Proof. vm_refl. Qed.
Lemma D_b5b28 : decode_any W_b5b28 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b2c : bv 32 := 0x00f00713.
Lemma F_b5b2c : fetch_word Ubsan.M.loaded_segments (0xb79bc : word) = Some W_b5b2c.
Proof. vm_refl. Qed.
Lemma D_b5b2c : decode_any W_b5b2c = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b30 : bv 32 := 0x0005a783.
Lemma F_b5b30 : fetch_word Ubsan.M.loaded_segments (0xb79c0 : word) = Some W_b5b30.
Proof. vm_refl. Qed.
Lemma D_b5b30 : decode_any W_b5b30 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b34 : bv 32 := 0x0045a803.
Lemma F_b5b34 : fetch_word Ubsan.M.loaded_segments (0xb79c4 : word) = Some W_b5b34.
Proof. vm_refl. Qed.
Lemma D_b5b34 : decode_any W_b5b34 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b38 : bv 32 := 0x0085a883.
Lemma F_b5b38 : fetch_word Ubsan.M.loaded_segments (0xb79c8 : word) = Some W_b5b38.
Proof. vm_refl. Qed.
Lemma D_b5b38 : decode_any W_b5b38 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b3c : bv 32 := 0x00c5a283.
Lemma F_b5b3c : fetch_word Ubsan.M.loaded_segments (0xb79cc : word) = Some W_b5b3c.
Proof. vm_refl. Qed.
Lemma D_b5b3c : decode_any W_b5b3c = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b40 : bv 32 := 0x01058593.
Lemma F_b5b40 : fetch_word Ubsan.M.loaded_segments (0xb79d0 : word) = Some W_b5b40.
Proof. vm_refl. Qed.
Lemma D_b5b40 : decode_any W_b5b40 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b44 : bv 32 := 0xff060613.
Lemma F_b5b44 : fetch_word Ubsan.M.loaded_segments (0xb79d4 : word) = Some W_b5b44.
Proof. vm_refl. Qed.
Lemma D_b5b44 : decode_any W_b5b44 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b48 : bv 32 := 0x00f6a023.
Lemma F_b5b48 : fetch_word Ubsan.M.loaded_segments (0xb79d8 : word) = Some W_b5b48.
Proof. vm_refl. Qed.
Lemma D_b5b48 : decode_any W_b5b48 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b4c : bv 32 := 0x0106a223.
Lemma F_b5b4c : fetch_word Ubsan.M.loaded_segments (0xb79dc : word) = Some W_b5b4c.
Proof. vm_refl. Qed.
Lemma D_b5b4c : decode_any W_b5b4c = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b50 : bv 32 := 0x0116a423.
Lemma F_b5b50 : fetch_word Ubsan.M.loaded_segments (0xb79e0 : word) = Some W_b5b50.
Proof. vm_refl. Qed.
Lemma D_b5b50 : decode_any W_b5b50 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b54 : bv 32 := 0x0056a623.
Lemma F_b5b54 : fetch_word Ubsan.M.loaded_segments (0xb79e4 : word) = Some W_b5b54.
Proof. vm_refl. Qed.
Lemma D_b5b54 : decode_any W_b5b54 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b58 : bv 32 := 0x01068693.
Lemma F_b5b58 : fetch_word Ubsan.M.loaded_segments (0xb79e8 : word) = Some W_b5b58.
Proof. vm_refl. Qed.
Lemma D_b5b58 : decode_any W_b5b58 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b5c : bv 32 := 0xfcc76ae3.
Lemma F_b5b5c : fetch_word Ubsan.M.loaded_segments (0xb79ec : word) = Some W_b5b5c.
Proof. vm_refl. Qed.
Lemma D_b5b5c : decode_any W_b5b5c = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b60 : bv 32 := 0x00800713.
Lemma F_b5b60 : fetch_word Ubsan.M.loaded_segments (0xb79f0 : word) = Some W_b5b60.
Proof. vm_refl. Qed.
Lemma D_b5b60 : decode_any W_b5b60 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b64 : bv 32 := 0x00e66e63.
Lemma F_b5b64 : fetch_word Ubsan.M.loaded_segments (0xb79f4 : word) = Some W_b5b64.
Proof. vm_refl. Qed.
Lemma D_b5b64 : decode_any W_b5b64 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b68 : bv 32 := 0x0005a703.
Lemma F_b5b68 : fetch_word Ubsan.M.loaded_segments (0xb79f8 : word) = Some W_b5b68.
Proof. vm_refl. Qed.
Lemma D_b5b68 : decode_any W_b5b68 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b6c : bv 32 := 0x0045a783.
Lemma F_b5b6c : fetch_word Ubsan.M.loaded_segments (0xb79fc : word) = Some W_b5b6c.
Proof. vm_refl. Qed.
Lemma D_b5b6c : decode_any W_b5b6c = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b70 : bv 32 := 0x00e6a023.
Lemma F_b5b70 : fetch_word Ubsan.M.loaded_segments (0xb7a00 : word) = Some W_b5b70.
Proof. vm_refl. Qed.
Lemma D_b5b70 : decode_any W_b5b70 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b74 : bv 32 := 0x00f6a223.
Lemma F_b5b74 : fetch_word Ubsan.M.loaded_segments (0xb7a04 : word) = Some W_b5b74.
Proof. vm_refl. Qed.
Lemma D_b5b74 : decode_any W_b5b74 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b78 : bv 32 := 0x00868693.
Lemma F_b5b78 : fetch_word Ubsan.M.loaded_segments (0xb7a08 : word) = Some W_b5b78.
Proof. vm_refl. Qed.
Lemma D_b5b78 : decode_any W_b5b78 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b7c : bv 32 := 0x00858593.
Lemma F_b5b7c : fetch_word Ubsan.M.loaded_segments (0xb7a0c : word) = Some W_b5b7c.
Proof. vm_refl. Qed.
Lemma D_b5b7c : decode_any W_b5b7c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b80 : bv 32 := 0x00467713.
Lemma F_b5b80 : fetch_word Ubsan.M.loaded_segments (0xb7a10 : word) = Some W_b5b80.
Proof. vm_refl. Qed.
Lemma D_b5b80 : decode_any W_b5b80 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b84 : bv 32 := 0x24070063.
Lemma F_b5b84 : fetch_word Ubsan.M.loaded_segments (0xb7a14 : word) = Some W_b5b84.
Proof. vm_refl. Qed.
Lemma D_b5b84 : decode_any W_b5b84 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b88 : bv 32 := 0x0005a703.
Lemma F_b5b88 : fetch_word Ubsan.M.loaded_segments (0xb7a18 : word) = Some W_b5b88.
Proof. vm_refl. Qed.
Lemma D_b5b88 : decode_any W_b5b88 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b8c : bv 32 := 0x00458593.
Lemma F_b5b8c : fetch_word Ubsan.M.loaded_segments (0xb7a1c : word) = Some W_b5b8c.
Proof. vm_refl. Qed.
Lemma D_b5b8c : decode_any W_b5b8c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b90 : bv 32 := 0x00e6a023.
Lemma F_b5b90 : fetch_word Ubsan.M.loaded_segments (0xb7a20 : word) = Some W_b5b90.
Proof. vm_refl. Qed.
Lemma D_b5b90 : decode_any W_b5b90 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b94 : bv 32 := 0x00468693.
Lemma F_b5b94 : fetch_word Ubsan.M.loaded_segments (0xb7a24 : word) = Some W_b5b94.
Proof. vm_refl. Qed.
Lemma D_b5b94 : decode_any W_b5b94 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b98 : bv 32 := 0x22c0006f.
Lemma F_b5b98 : fetch_word Ubsan.M.loaded_segments (0xb7a28 : word) = Some W_b5b98.
Proof. vm_refl. Qed.
Lemma D_b5b98 : decode_any W_b5b98 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5b9c : bv 32 := 0x00e68023.
Lemma F_b5b9c : fetch_word Ubsan.M.loaded_segments (0xb7a2c : word) = Some W_b5b9c.
Proof. vm_refl. Qed.
Lemma D_b5b9c : decode_any W_b5b9c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ba0 : bv 32 := 0x00168693.
Lemma F_b5ba0 : fetch_word Ubsan.M.loaded_segments (0xb7a30 : word) = Some W_b5ba0.
Proof. vm_refl. Qed.
Lemma D_b5ba0 : decode_any W_b5ba0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ba4 : bv 32 := 0xfff60613.
Lemma F_b5ba4 : fetch_word Ubsan.M.loaded_segments (0xb7a34 : word) = Some W_b5ba4.
Proof. vm_refl. Qed.
Lemma D_b5ba4 : decode_any W_b5ba4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ba8 : bv 32 := 0x01058593.
Lemma F_b5ba8 : fetch_word Ubsan.M.loaded_segments (0xb7a38 : word) = Some W_b5ba8.
Proof. vm_refl. Qed.
Lemma D_b5ba8 : decode_any W_b5ba8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bac : bv 32 := 0x01200793.
Lemma F_b5bac : fetch_word Ubsan.M.loaded_segments (0xb7a3c : word) = Some W_b5bac.
Proof. vm_refl. Qed.
Lemma D_b5bac : decode_any W_b5bac = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bb0 : bv 32 := 0x0087581b.
Lemma F_b5bb0 : fetch_word Ubsan.M.loaded_segments (0xb7a40 : word) = Some W_b5bb0.
Proof. vm_refl. Qed.
Lemma D_b5bb0 : decode_any W_b5bb0 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bb4 : bv 32 := 0xff45a883.
Lemma F_b5bb4 : fetch_word Ubsan.M.loaded_segments (0xb7a44 : word) = Some W_b5bb4.
Proof. vm_refl. Qed.
Lemma D_b5bb4 : decode_any W_b5bb4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bb8 : bv 32 := 0xff85a283.
Lemma F_b5bb8 : fetch_word Ubsan.M.loaded_segments (0xb7a48 : word) = Some W_b5bb8.
Proof. vm_refl. Qed.
Lemma D_b5bb8 : decode_any W_b5bb8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bbc : bv 32 := 0xffc5a303.
Lemma F_b5bbc : fetch_word Ubsan.M.loaded_segments (0xb7a4c : word) = Some W_b5bbc.
Proof. vm_refl. Qed.
Lemma D_b5bbc : decode_any W_b5bbc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bc0 : bv 32 := 0x0005a703.
Lemma F_b5bc0 : fetch_word Ubsan.M.loaded_segments (0xb7a50 : word) = Some W_b5bc0.
Proof. vm_refl. Qed.
Lemma D_b5bc0 : decode_any W_b5bc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bc4 : bv 32 := 0x01889393.
Lemma F_b5bc4 : fetch_word Ubsan.M.loaded_segments (0xb7a54 : word) = Some W_b5bc4.
Proof. vm_refl. Qed.
Lemma D_b5bc4 : decode_any W_b5bc4 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bc8 : bv 32 := 0x0088d89b.
Lemma F_b5bc8 : fetch_word Ubsan.M.loaded_segments (0xb7a58 : word) = Some W_b5bc8.
Proof. vm_refl. Qed.
Lemma D_b5bc8 : decode_any W_b5bc8 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bcc : bv 32 := 0x0103e833.
Lemma F_b5bcc : fetch_word Ubsan.M.loaded_segments (0xb7a5c : word) = Some W_b5bcc.
Proof. vm_refl. Qed.
Lemma D_b5bcc : decode_any W_b5bcc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bd0 : bv 32 := 0x01829393.
Lemma F_b5bd0 : fetch_word Ubsan.M.loaded_segments (0xb7a60 : word) = Some W_b5bd0.
Proof. vm_refl. Qed.
Lemma D_b5bd0 : decode_any W_b5bd0 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bd4 : bv 32 := 0x0082d29b.
Lemma F_b5bd4 : fetch_word Ubsan.M.loaded_segments (0xb7a64 : word) = Some W_b5bd4.
Proof. vm_refl. Qed.
Lemma D_b5bd4 : decode_any W_b5bd4 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bd8 : bv 32 := 0x0113e8b3.
Lemma F_b5bd8 : fetch_word Ubsan.M.loaded_segments (0xb7a68 : word) = Some W_b5bd8.
Proof. vm_refl. Qed.
Lemma D_b5bd8 : decode_any W_b5bd8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bdc : bv 32 := 0x01831393.
Lemma F_b5bdc : fetch_word Ubsan.M.loaded_segments (0xb7a6c : word) = Some W_b5bdc.
Proof. vm_refl. Qed.
Lemma D_b5bdc : decode_any W_b5bdc = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5be0 : bv 32 := 0x0083531b.
Lemma F_b5be0 : fetch_word Ubsan.M.loaded_segments (0xb7a70 : word) = Some W_b5be0.
Proof. vm_refl. Qed.
Lemma D_b5be0 : decode_any W_b5be0 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5be4 : bv 32 := 0x0053e2b3.
Lemma F_b5be4 : fetch_word Ubsan.M.loaded_segments (0xb7a74 : word) = Some W_b5be4.
Proof. vm_refl. Qed.
Lemma D_b5be4 : decode_any W_b5be4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5be8 : bv 32 := 0x01871393.
Lemma F_b5be8 : fetch_word Ubsan.M.loaded_segments (0xb7a78 : word) = Some W_b5be8.
Proof. vm_refl. Qed.
Lemma D_b5be8 : decode_any W_b5be8 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bec : bv 32 := 0x0063e333.
Lemma F_b5bec : fetch_word Ubsan.M.loaded_segments (0xb7a7c : word) = Some W_b5bec.
Proof. vm_refl. Qed.
Lemma D_b5bec : decode_any W_b5bec = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bf0 : bv 32 := 0xff060613.
Lemma F_b5bf0 : fetch_word Ubsan.M.loaded_segments (0xb7a80 : word) = Some W_b5bf0.
Proof. vm_refl. Qed.
Lemma D_b5bf0 : decode_any W_b5bf0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bf4 : bv 32 := 0x0106a023.
Lemma F_b5bf4 : fetch_word Ubsan.M.loaded_segments (0xb7a84 : word) = Some W_b5bf4.
Proof. vm_refl. Qed.
Lemma D_b5bf4 : decode_any W_b5bf4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bf8 : bv 32 := 0x0116a223.
Lemma F_b5bf8 : fetch_word Ubsan.M.loaded_segments (0xb7a88 : word) = Some W_b5bf8.
Proof. vm_refl. Qed.
Lemma D_b5bf8 : decode_any W_b5bf8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5bfc : bv 32 := 0x0056a423.
Lemma F_b5bfc : fetch_word Ubsan.M.loaded_segments (0xb7a8c : word) = Some W_b5bfc.
Proof. vm_refl. Qed.
Lemma D_b5bfc : decode_any W_b5bfc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c00 : bv 32 := 0x0066a623.
Lemma F_b5c00 : fetch_word Ubsan.M.loaded_segments (0xb7a90 : word) = Some W_b5c00.
Proof. vm_refl. Qed.
Lemma D_b5c00 : decode_any W_b5c00 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c04 : bv 32 := 0x01068693.
Lemma F_b5c04 : fetch_word Ubsan.M.loaded_segments (0xb7a94 : word) = Some W_b5c04.
Proof. vm_refl. Qed.
Lemma D_b5c04 : decode_any W_b5c04 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c08 : bv 32 := 0x01058593.
Lemma F_b5c08 : fetch_word Ubsan.M.loaded_segments (0xb7a98 : word) = Some W_b5c08.
Proof. vm_refl. Qed.
Lemma D_b5c08 : decode_any W_b5c08 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c0c : bv 32 := 0xfac7e2e3.
Lemma F_b5c0c : fetch_word Ubsan.M.loaded_segments (0xb7a9c : word) = Some W_b5c0c.
Proof. vm_refl. Qed.
Lemma D_b5c0c : decode_any W_b5c0c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c10 : bv 32 := 0xff158593.
Lemma F_b5c10 : fetch_word Ubsan.M.loaded_segments (0xb7aa0 : word) = Some W_b5c10.
Proof. vm_refl. Qed.
Lemma D_b5c10 : decode_any W_b5c10 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c14 : bv 32 := 0x01000713.
Lemma F_b5c14 : fetch_word Ubsan.M.loaded_segments (0xb7aa4 : word) = Some W_b5c14.
Proof. vm_refl. Qed.
Lemma D_b5c14 : decode_any W_b5c14 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c18 : bv 32 := 0xe4e666e3.
Lemma F_b5c18 : fetch_word Ubsan.M.loaded_segments (0xb7aa8 : word) = Some W_b5c18.
Proof. vm_refl. Qed.
Lemma D_b5c18 : decode_any W_b5c18 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c1c : bv 32 := 0x0940006f.
Lemma F_b5c1c : fetch_word Ubsan.M.loaded_segments (0xb7aac : word) = Some W_b5c1c.
Proof. vm_refl. Qed.
Lemma D_b5c1c : decode_any W_b5c1c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c20 : bv 32 := 0x00875793.
Lemma F_b5c20 : fetch_word Ubsan.M.loaded_segments (0xb7ab0 : word) = Some W_b5c20.
Proof. vm_refl. Qed.
Lemma D_b5c20 : decode_any W_b5c20 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c24 : bv 32 := 0x01075813.
Lemma F_b5c24 : fetch_word Ubsan.M.loaded_segments (0xb7ab4 : word) = Some W_b5c24.
Proof. vm_refl. Qed.
Lemma D_b5c24 : decode_any W_b5c24 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c28 : bv 32 := 0xffd60613.
Lemma F_b5c28 : fetch_word Ubsan.M.loaded_segments (0xb7ab8 : word) = Some W_b5c28.
Proof. vm_refl. Qed.
Lemma D_b5c28 : decode_any W_b5c28 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c2c : bv 32 := 0x00e68023.
Lemma F_b5c2c : fetch_word Ubsan.M.loaded_segments (0xb7abc : word) = Some W_b5c2c.
Proof. vm_refl. Qed.
Lemma D_b5c2c : decode_any W_b5c2c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c30 : bv 32 := 0x00f680a3.
Lemma F_b5c30 : fetch_word Ubsan.M.loaded_segments (0xb7ac0 : word) = Some W_b5c30.
Proof. vm_refl. Qed.
Lemma D_b5c30 : decode_any W_b5c30 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c34 : bv 32 := 0x01068123.
Lemma F_b5c34 : fetch_word Ubsan.M.loaded_segments (0xb7ac4 : word) = Some W_b5c34.
Proof. vm_refl. Qed.
Lemma D_b5c34 : decode_any W_b5c34 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c38 : bv 32 := 0x00368693.
Lemma F_b5c38 : fetch_word Ubsan.M.loaded_segments (0xb7ac8 : word) = Some W_b5c38.
Proof. vm_refl. Qed.
Lemma D_b5c38 : decode_any W_b5c38 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c3c : bv 32 := 0x01058593.
Lemma F_b5c3c : fetch_word Ubsan.M.loaded_segments (0xb7acc : word) = Some W_b5c3c.
Proof. vm_refl. Qed.
Lemma D_b5c3c : decode_any W_b5c3c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c40 : bv 32 := 0x01000793.
Lemma F_b5c40 : fetch_word Ubsan.M.loaded_segments (0xb7ad0 : word) = Some W_b5c40.
Proof. vm_refl. Qed.
Lemma D_b5c40 : decode_any W_b5c40 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c44 : bv 32 := 0x0187581b.
Lemma F_b5c44 : fetch_word Ubsan.M.loaded_segments (0xb7ad4 : word) = Some W_b5c44.
Proof. vm_refl. Qed.
Lemma D_b5c44 : decode_any W_b5c44 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c48 : bv 32 := 0xff45a883.
Lemma F_b5c48 : fetch_word Ubsan.M.loaded_segments (0xb7ad8 : word) = Some W_b5c48.
Proof. vm_refl. Qed.
Lemma D_b5c48 : decode_any W_b5c48 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c4c : bv 32 := 0xff85a283.
Lemma F_b5c4c : fetch_word Ubsan.M.loaded_segments (0xb7adc : word) = Some W_b5c4c.
Proof. vm_refl. Qed.
Lemma D_b5c4c : decode_any W_b5c4c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c50 : bv 32 := 0xffc5a303.
Lemma F_b5c50 : fetch_word Ubsan.M.loaded_segments (0xb7ae0 : word) = Some W_b5c50.
Proof. vm_refl. Qed.
Lemma D_b5c50 : decode_any W_b5c50 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c54 : bv 32 := 0x0005a703.
Lemma F_b5c54 : fetch_word Ubsan.M.loaded_segments (0xb7ae4 : word) = Some W_b5c54.
Proof. vm_refl. Qed.
Lemma D_b5c54 : decode_any W_b5c54 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c58 : bv 32 := 0x00889393.
Lemma F_b5c58 : fetch_word Ubsan.M.loaded_segments (0xb7ae8 : word) = Some W_b5c58.
Proof. vm_refl. Qed.
Lemma D_b5c58 : decode_any W_b5c58 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c5c : bv 32 := 0x0188d89b.
Lemma F_b5c5c : fetch_word Ubsan.M.loaded_segments (0xb7aec : word) = Some W_b5c5c.
Proof. vm_refl. Qed.
Lemma D_b5c5c : decode_any W_b5c5c = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c60 : bv 32 := 0x0103e833.
Lemma F_b5c60 : fetch_word Ubsan.M.loaded_segments (0xb7af0 : word) = Some W_b5c60.
Proof. vm_refl. Qed.
Lemma D_b5c60 : decode_any W_b5c60 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c64 : bv 32 := 0x00829393.
Lemma F_b5c64 : fetch_word Ubsan.M.loaded_segments (0xb7af4 : word) = Some W_b5c64.
Proof. vm_refl. Qed.
Lemma D_b5c64 : decode_any W_b5c64 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c68 : bv 32 := 0x0182d29b.
Lemma F_b5c68 : fetch_word Ubsan.M.loaded_segments (0xb7af8 : word) = Some W_b5c68.
Proof. vm_refl. Qed.
Lemma D_b5c68 : decode_any W_b5c68 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c6c : bv 32 := 0x0113e8b3.
Lemma F_b5c6c : fetch_word Ubsan.M.loaded_segments (0xb7afc : word) = Some W_b5c6c.
Proof. vm_refl. Qed.
Lemma D_b5c6c : decode_any W_b5c6c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c70 : bv 32 := 0x00831393.
Lemma F_b5c70 : fetch_word Ubsan.M.loaded_segments (0xb7b00 : word) = Some W_b5c70.
Proof. vm_refl. Qed.
Lemma D_b5c70 : decode_any W_b5c70 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c74 : bv 32 := 0x0183531b.
Lemma F_b5c74 : fetch_word Ubsan.M.loaded_segments (0xb7b04 : word) = Some W_b5c74.
Proof. vm_refl. Qed.
Lemma D_b5c74 : decode_any W_b5c74 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c78 : bv 32 := 0x0053e2b3.
Lemma F_b5c78 : fetch_word Ubsan.M.loaded_segments (0xb7b08 : word) = Some W_b5c78.
Proof. vm_refl. Qed.
Lemma D_b5c78 : decode_any W_b5c78 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c7c : bv 32 := 0x00871393.
Lemma F_b5c7c : fetch_word Ubsan.M.loaded_segments (0xb7b0c : word) = Some W_b5c7c.
Proof. vm_refl. Qed.
Lemma D_b5c7c : decode_any W_b5c7c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c80 : bv 32 := 0x0063e333.
Lemma F_b5c80 : fetch_word Ubsan.M.loaded_segments (0xb7b10 : word) = Some W_b5c80.
Proof. vm_refl. Qed.
Lemma D_b5c80 : decode_any W_b5c80 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c84 : bv 32 := 0xff060613.
Lemma F_b5c84 : fetch_word Ubsan.M.loaded_segments (0xb7b14 : word) = Some W_b5c84.
Proof. vm_refl. Qed.
Lemma D_b5c84 : decode_any W_b5c84 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c88 : bv 32 := 0x0106a023.
Lemma F_b5c88 : fetch_word Ubsan.M.loaded_segments (0xb7b18 : word) = Some W_b5c88.
Proof. vm_refl. Qed.
Lemma D_b5c88 : decode_any W_b5c88 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c8c : bv 32 := 0x0116a223.
Lemma F_b5c8c : fetch_word Ubsan.M.loaded_segments (0xb7b1c : word) = Some W_b5c8c.
Proof. vm_refl. Qed.
Lemma D_b5c8c : decode_any W_b5c8c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c90 : bv 32 := 0x0056a423.
Lemma F_b5c90 : fetch_word Ubsan.M.loaded_segments (0xb7b20 : word) = Some W_b5c90.
Proof. vm_refl. Qed.
Lemma D_b5c90 : decode_any W_b5c90 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c94 : bv 32 := 0x0066a623.
Lemma F_b5c94 : fetch_word Ubsan.M.loaded_segments (0xb7b24 : word) = Some W_b5c94.
Proof. vm_refl. Qed.
Lemma D_b5c94 : decode_any W_b5c94 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c98 : bv 32 := 0x01068693.
Lemma F_b5c98 : fetch_word Ubsan.M.loaded_segments (0xb7b28 : word) = Some W_b5c98.
Proof. vm_refl. Qed.
Lemma D_b5c98 : decode_any W_b5c98 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5c9c : bv 32 := 0x01058593.
Lemma F_b5c9c : fetch_word Ubsan.M.loaded_segments (0xb7b2c : word) = Some W_b5c9c.
Proof. vm_refl. Qed.
Lemma D_b5c9c : decode_any W_b5c9c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ca0 : bv 32 := 0xfac7e2e3.
Lemma F_b5ca0 : fetch_word Ubsan.M.loaded_segments (0xb7b30 : word) = Some W_b5ca0.
Proof. vm_refl. Qed.
Lemma D_b5ca0 : decode_any W_b5ca0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ca4 : bv 32 := 0xff358593.
Lemma F_b5ca4 : fetch_word Ubsan.M.loaded_segments (0xb7b34 : word) = Some W_b5ca4.
Proof. vm_refl. Qed.
Lemma D_b5ca4 : decode_any W_b5ca4 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ca8 : bv 32 := 0x01000713.
Lemma F_b5ca8 : fetch_word Ubsan.M.loaded_segments (0xb7b38 : word) = Some W_b5ca8.
Proof. vm_refl. Qed.
Lemma D_b5ca8 : decode_any W_b5ca8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cac : bv 32 := 0xdae66ce3.
Lemma F_b5cac : fetch_word Ubsan.M.loaded_segments (0xb7b3c : word) = Some W_b5cac.
Proof. vm_refl. Qed.
Lemma D_b5cac : decode_any W_b5cac = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cb0 : bv 32 := 0x0005c703.
Lemma F_b5cb0 : fetch_word Ubsan.M.loaded_segments (0xb7b40 : word) = Some W_b5cb0.
Proof. vm_refl. Qed.
Lemma D_b5cb0 : decode_any W_b5cb0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cb4 : bv 32 := 0x0015c783.
Lemma F_b5cb4 : fetch_word Ubsan.M.loaded_segments (0xb7b44 : word) = Some W_b5cb4.
Proof. vm_refl. Qed.
Lemma D_b5cb4 : decode_any W_b5cb4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cb8 : bv 32 := 0x0025c803.
Lemma F_b5cb8 : fetch_word Ubsan.M.loaded_segments (0xb7b48 : word) = Some W_b5cb8.
Proof. vm_refl. Qed.
Lemma D_b5cb8 : decode_any W_b5cb8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cbc : bv 32 := 0x0035c883.
Lemma F_b5cbc : fetch_word Ubsan.M.loaded_segments (0xb7b4c : word) = Some W_b5cbc.
Proof. vm_refl. Qed.
Lemma D_b5cbc : decode_any W_b5cbc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cc0 : bv 32 := 0x0045c283.
Lemma F_b5cc0 : fetch_word Ubsan.M.loaded_segments (0xb7b50 : word) = Some W_b5cc0.
Proof. vm_refl. Qed.
Lemma D_b5cc0 : decode_any W_b5cc0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cc4 : bv 32 := 0x0055c303.
Lemma F_b5cc4 : fetch_word Ubsan.M.loaded_segments (0xb7b54 : word) = Some W_b5cc4.
Proof. vm_refl. Qed.
Lemma D_b5cc4 : decode_any W_b5cc4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cc8 : bv 32 := 0x0065c383.
Lemma F_b5cc8 : fetch_word Ubsan.M.loaded_segments (0xb7b58 : word) = Some W_b5cc8.
Proof. vm_refl. Qed.
Lemma D_b5cc8 : decode_any W_b5cc8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ccc : bv 32 := 0x0075ce03.
Lemma F_b5ccc : fetch_word Ubsan.M.loaded_segments (0xb7b5c : word) = Some W_b5ccc.
Proof. vm_refl. Qed.
Lemma D_b5ccc : decode_any W_b5ccc = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cd0 : bv 32 := 0x00e68023.
Lemma F_b5cd0 : fetch_word Ubsan.M.loaded_segments (0xb7b60 : word) = Some W_b5cd0.
Proof. vm_refl. Qed.
Lemma D_b5cd0 : decode_any W_b5cd0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cd4 : bv 32 := 0x00f680a3.
Lemma F_b5cd4 : fetch_word Ubsan.M.loaded_segments (0xb7b64 : word) = Some W_b5cd4.
Proof. vm_refl. Qed.
Lemma D_b5cd4 : decode_any W_b5cd4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cd8 : bv 32 := 0x01068123.
Lemma F_b5cd8 : fetch_word Ubsan.M.loaded_segments (0xb7b68 : word) = Some W_b5cd8.
Proof. vm_refl. Qed.
Lemma D_b5cd8 : decode_any W_b5cd8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cdc : bv 32 := 0x011681a3.
Lemma F_b5cdc : fetch_word Ubsan.M.loaded_segments (0xb7b6c : word) = Some W_b5cdc.
Proof. vm_refl. Qed.
Lemma D_b5cdc : decode_any W_b5cdc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ce0 : bv 32 := 0x0085c703.
Lemma F_b5ce0 : fetch_word Ubsan.M.loaded_segments (0xb7b70 : word) = Some W_b5ce0.
Proof. vm_refl. Qed.
Lemma D_b5ce0 : decode_any W_b5ce0 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ce4 : bv 32 := 0x0095c783.
Lemma F_b5ce4 : fetch_word Ubsan.M.loaded_segments (0xb7b74 : word) = Some W_b5ce4.
Proof. vm_refl. Qed.
Lemma D_b5ce4 : decode_any W_b5ce4 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ce8 : bv 32 := 0x00a5c803.
Lemma F_b5ce8 : fetch_word Ubsan.M.loaded_segments (0xb7b78 : word) = Some W_b5ce8.
Proof. vm_refl. Qed.
Lemma D_b5ce8 : decode_any W_b5ce8 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cec : bv 32 := 0x00b5c883.
Lemma F_b5cec : fetch_word Ubsan.M.loaded_segments (0xb7b7c : word) = Some W_b5cec.
Proof. vm_refl. Qed.
Lemma D_b5cec : decode_any W_b5cec = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cf0 : bv 32 := 0x00568223.
Lemma F_b5cf0 : fetch_word Ubsan.M.loaded_segments (0xb7b80 : word) = Some W_b5cf0.
Proof. vm_refl. Qed.
Lemma D_b5cf0 : decode_any W_b5cf0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cf4 : bv 32 := 0x006682a3.
Lemma F_b5cf4 : fetch_word Ubsan.M.loaded_segments (0xb7b84 : word) = Some W_b5cf4.
Proof. vm_refl. Qed.
Lemma D_b5cf4 : decode_any W_b5cf4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cf8 : bv 32 := 0x00768323.
Lemma F_b5cf8 : fetch_word Ubsan.M.loaded_segments (0xb7b88 : word) = Some W_b5cf8.
Proof. vm_refl. Qed.
Lemma D_b5cf8 : decode_any W_b5cf8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5cfc : bv 32 := 0x01c683a3.
Lemma F_b5cfc : fetch_word Ubsan.M.loaded_segments (0xb7b8c : word) = Some W_b5cfc.
Proof. vm_refl. Qed.
Lemma D_b5cfc : decode_any W_b5cfc = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d00 : bv 32 := 0x00c5c283.
Lemma F_b5d00 : fetch_word Ubsan.M.loaded_segments (0xb7b90 : word) = Some W_b5d00.
Proof. vm_refl. Qed.
Lemma D_b5d00 : decode_any W_b5d00 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d04 : bv 32 := 0x00d5c303.
Lemma F_b5d04 : fetch_word Ubsan.M.loaded_segments (0xb7b94 : word) = Some W_b5d04.
Proof. vm_refl. Qed.
Lemma D_b5d04 : decode_any W_b5d04 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d08 : bv 32 := 0x00e5c383.
Lemma F_b5d08 : fetch_word Ubsan.M.loaded_segments (0xb7b98 : word) = Some W_b5d08.
Proof. vm_refl. Qed.
Lemma D_b5d08 : decode_any W_b5d08 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d0c : bv 32 := 0x00f5ce03.
Lemma F_b5d0c : fetch_word Ubsan.M.loaded_segments (0xb7b9c : word) = Some W_b5d0c.
Proof. vm_refl. Qed.
Lemma D_b5d0c : decode_any W_b5d0c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d10 : bv 32 := 0x01058593.
Lemma F_b5d10 : fetch_word Ubsan.M.loaded_segments (0xb7ba0 : word) = Some W_b5d10.
Proof. vm_refl. Qed.
Lemma D_b5d10 : decode_any W_b5d10 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d14 : bv 32 := 0x00e68423.
Lemma F_b5d14 : fetch_word Ubsan.M.loaded_segments (0xb7ba4 : word) = Some W_b5d14.
Proof. vm_refl. Qed.
Lemma D_b5d14 : decode_any W_b5d14 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d18 : bv 32 := 0x00f684a3.
Lemma F_b5d18 : fetch_word Ubsan.M.loaded_segments (0xb7ba8 : word) = Some W_b5d18.
Proof. vm_refl. Qed.
Lemma D_b5d18 : decode_any W_b5d18 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d1c : bv 32 := 0x01068523.
Lemma F_b5d1c : fetch_word Ubsan.M.loaded_segments (0xb7bac : word) = Some W_b5d1c.
Proof. vm_refl. Qed.
Lemma D_b5d1c : decode_any W_b5d1c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d20 : bv 32 := 0x011685a3.
Lemma F_b5d20 : fetch_word Ubsan.M.loaded_segments (0xb7bb0 : word) = Some W_b5d20.
Proof. vm_refl. Qed.
Lemma D_b5d20 : decode_any W_b5d20 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d24 : bv 32 := 0x01068713.
Lemma F_b5d24 : fetch_word Ubsan.M.loaded_segments (0xb7bb4 : word) = Some W_b5d24.
Proof. vm_refl. Qed.
Lemma D_b5d24 : decode_any W_b5d24 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d28 : bv 32 := 0x00568623.
Lemma F_b5d28 : fetch_word Ubsan.M.loaded_segments (0xb7bb8 : word) = Some W_b5d28.
Proof. vm_refl. Qed.
Lemma D_b5d28 : decode_any W_b5d28 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d2c : bv 32 := 0x006686a3.
Lemma F_b5d2c : fetch_word Ubsan.M.loaded_segments (0xb7bbc : word) = Some W_b5d2c.
Proof. vm_refl. Qed.
Lemma D_b5d2c : decode_any W_b5d2c = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d30 : bv 32 := 0x00768723.
Lemma F_b5d30 : fetch_word Ubsan.M.loaded_segments (0xb7bc0 : word) = Some W_b5d30.
Proof. vm_refl. Qed.
Lemma D_b5d30 : decode_any W_b5d30 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d34 : bv 32 := 0x01c687a3.
Lemma F_b5d34 : fetch_word Ubsan.M.loaded_segments (0xb7bc4 : word) = Some W_b5d34.
Proof. vm_refl. Qed.
Lemma D_b5d34 : decode_any W_b5d34 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d38 : bv 32 := 0x00070693.
Lemma F_b5d38 : fetch_word Ubsan.M.loaded_segments (0xb7bc8 : word) = Some W_b5d38.
Proof. vm_refl. Qed.
Lemma D_b5d38 : decode_any W_b5d38 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d3c : bv 32 := 0x00867713.
Lemma F_b5d3c : fetch_word Ubsan.M.loaded_segments (0xb7bcc : word) = Some W_b5d3c.
Proof. vm_refl. Qed.
Lemma D_b5d3c : decode_any W_b5d3c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d40 : bv 32 := 0xd20706e3.
Lemma F_b5d40 : fetch_word Ubsan.M.loaded_segments (0xb7bd0 : word) = Some W_b5d40.
Proof. vm_refl. Qed.
Lemma D_b5d40 : decode_any W_b5d40 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d44 : bv 32 := 0x0005c703.
Lemma F_b5d44 : fetch_word Ubsan.M.loaded_segments (0xb7bd4 : word) = Some W_b5d44.
Proof. vm_refl. Qed.
Lemma D_b5d44 : decode_any W_b5d44 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d48 : bv 32 := 0x0015c783.
Lemma F_b5d48 : fetch_word Ubsan.M.loaded_segments (0xb7bd8 : word) = Some W_b5d48.
Proof. vm_refl. Qed.
Lemma D_b5d48 : decode_any W_b5d48 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d4c : bv 32 := 0x0025c803.
Lemma F_b5d4c : fetch_word Ubsan.M.loaded_segments (0xb7bdc : word) = Some W_b5d4c.
Proof. vm_refl. Qed.
Lemma D_b5d4c : decode_any W_b5d4c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d50 : bv 32 := 0x0035c883.
Lemma F_b5d50 : fetch_word Ubsan.M.loaded_segments (0xb7be0 : word) = Some W_b5d50.
Proof. vm_refl. Qed.
Lemma D_b5d50 : decode_any W_b5d50 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d54 : bv 32 := 0x0045c283.
Lemma F_b5d54 : fetch_word Ubsan.M.loaded_segments (0xb7be4 : word) = Some W_b5d54.
Proof. vm_refl. Qed.
Lemma D_b5d54 : decode_any W_b5d54 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d58 : bv 32 := 0x0055c303.
Lemma F_b5d58 : fetch_word Ubsan.M.loaded_segments (0xb7be8 : word) = Some W_b5d58.
Proof. vm_refl. Qed.
Lemma D_b5d58 : decode_any W_b5d58 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d5c : bv 32 := 0x0065c383.
Lemma F_b5d5c : fetch_word Ubsan.M.loaded_segments (0xb7bec : word) = Some W_b5d5c.
Proof. vm_refl. Qed.
Lemma D_b5d5c : decode_any W_b5d5c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d60 : bv 32 := 0x0075ce03.
Lemma F_b5d60 : fetch_word Ubsan.M.loaded_segments (0xb7bf0 : word) = Some W_b5d60.
Proof. vm_refl. Qed.
Lemma D_b5d60 : decode_any W_b5d60 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d64 : bv 32 := 0x00858593.
Lemma F_b5d64 : fetch_word Ubsan.M.loaded_segments (0xb7bf4 : word) = Some W_b5d64.
Proof. vm_refl. Qed.
Lemma D_b5d64 : decode_any W_b5d64 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d68 : bv 32 := 0x00e68023.
Lemma F_b5d68 : fetch_word Ubsan.M.loaded_segments (0xb7bf8 : word) = Some W_b5d68.
Proof. vm_refl. Qed.
Lemma D_b5d68 : decode_any W_b5d68 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d6c : bv 32 := 0x00f680a3.
Lemma F_b5d6c : fetch_word Ubsan.M.loaded_segments (0xb7bfc : word) = Some W_b5d6c.
Proof. vm_refl. Qed.
Lemma D_b5d6c : decode_any W_b5d6c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d70 : bv 32 := 0x01068123.
Lemma F_b5d70 : fetch_word Ubsan.M.loaded_segments (0xb7c00 : word) = Some W_b5d70.
Proof. vm_refl. Qed.
Lemma D_b5d70 : decode_any W_b5d70 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d74 : bv 32 := 0x011681a3.
Lemma F_b5d74 : fetch_word Ubsan.M.loaded_segments (0xb7c04 : word) = Some W_b5d74.
Proof. vm_refl. Qed.
Lemma D_b5d74 : decode_any W_b5d74 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d78 : bv 32 := 0x00868713.
Lemma F_b5d78 : fetch_word Ubsan.M.loaded_segments (0xb7c08 : word) = Some W_b5d78.
Proof. vm_refl. Qed.
Lemma D_b5d78 : decode_any W_b5d78 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d7c : bv 32 := 0x00568223.
Lemma F_b5d7c : fetch_word Ubsan.M.loaded_segments (0xb7c0c : word) = Some W_b5d7c.
Proof. vm_refl. Qed.
Lemma D_b5d7c : decode_any W_b5d7c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d80 : bv 32 := 0x006682a3.
Lemma F_b5d80 : fetch_word Ubsan.M.loaded_segments (0xb7c10 : word) = Some W_b5d80.
Proof. vm_refl. Qed.
Lemma D_b5d80 : decode_any W_b5d80 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d84 : bv 32 := 0x00768323.
Lemma F_b5d84 : fetch_word Ubsan.M.loaded_segments (0xb7c14 : word) = Some W_b5d84.
Proof. vm_refl. Qed.
Lemma D_b5d84 : decode_any W_b5d84 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d88 : bv 32 := 0x01c683a3.
Lemma F_b5d88 : fetch_word Ubsan.M.loaded_segments (0xb7c18 : word) = Some W_b5d88.
Proof. vm_refl. Qed.
Lemma D_b5d88 : decode_any W_b5d88 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d8c : bv 32 := 0x00070693.
Lemma F_b5d8c : fetch_word Ubsan.M.loaded_segments (0xb7c1c : word) = Some W_b5d8c.
Proof. vm_refl. Qed.
Lemma D_b5d8c : decode_any W_b5d8c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d90 : bv 32 := 0x00467713.
Lemma F_b5d90 : fetch_word Ubsan.M.loaded_segments (0xb7c20 : word) = Some W_b5d90.
Proof. vm_refl. Qed.
Lemma D_b5d90 : decode_any W_b5d90 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d94 : bv 32 := 0x02070863.
Lemma F_b5d94 : fetch_word Ubsan.M.loaded_segments (0xb7c24 : word) = Some W_b5d94.
Proof. vm_refl. Qed.
Lemma D_b5d94 : decode_any W_b5d94 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d98 : bv 32 := 0x0005c703.
Lemma F_b5d98 : fetch_word Ubsan.M.loaded_segments (0xb7c28 : word) = Some W_b5d98.
Proof. vm_refl. Qed.
Lemma D_b5d98 : decode_any W_b5d98 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5d9c : bv 32 := 0x0015c783.
Lemma F_b5d9c : fetch_word Ubsan.M.loaded_segments (0xb7c2c : word) = Some W_b5d9c.
Proof. vm_refl. Qed.
Lemma D_b5d9c : decode_any W_b5d9c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5da0 : bv 32 := 0x0025c803.
Lemma F_b5da0 : fetch_word Ubsan.M.loaded_segments (0xb7c30 : word) = Some W_b5da0.
Proof. vm_refl. Qed.
Lemma D_b5da0 : decode_any W_b5da0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5da4 : bv 32 := 0x0035c883.
Lemma F_b5da4 : fetch_word Ubsan.M.loaded_segments (0xb7c34 : word) = Some W_b5da4.
Proof. vm_refl. Qed.
Lemma D_b5da4 : decode_any W_b5da4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5da8 : bv 32 := 0x00458593.
Lemma F_b5da8 : fetch_word Ubsan.M.loaded_segments (0xb7c38 : word) = Some W_b5da8.
Proof. vm_refl. Qed.
Lemma D_b5da8 : decode_any W_b5da8 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dac : bv 32 := 0x00468293.
Lemma F_b5dac : fetch_word Ubsan.M.loaded_segments (0xb7c3c : word) = Some W_b5dac.
Proof. vm_refl. Qed.
Lemma D_b5dac : decode_any W_b5dac = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5db0 : bv 32 := 0x00e68023.
Lemma F_b5db0 : fetch_word Ubsan.M.loaded_segments (0xb7c40 : word) = Some W_b5db0.
Proof. vm_refl. Qed.
Lemma D_b5db0 : decode_any W_b5db0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5db4 : bv 32 := 0x00f680a3.
Lemma F_b5db4 : fetch_word Ubsan.M.loaded_segments (0xb7c44 : word) = Some W_b5db4.
Proof. vm_refl. Qed.
Lemma D_b5db4 : decode_any W_b5db4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5db8 : bv 32 := 0x01068123.
Lemma F_b5db8 : fetch_word Ubsan.M.loaded_segments (0xb7c48 : word) = Some W_b5db8.
Proof. vm_refl. Qed.
Lemma D_b5db8 : decode_any W_b5db8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dbc : bv 32 := 0x011681a3.
Lemma F_b5dbc : fetch_word Ubsan.M.loaded_segments (0xb7c4c : word) = Some W_b5dbc.
Proof. vm_refl. Qed.
Lemma D_b5dbc : decode_any W_b5dbc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dc0 : bv 32 := 0x00028693.
Lemma F_b5dc0 : fetch_word Ubsan.M.loaded_segments (0xb7c50 : word) = Some W_b5dc0.
Proof. vm_refl. Qed.
Lemma D_b5dc0 : decode_any W_b5dc0 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dc4 : bv 32 := 0x00267713.
Lemma F_b5dc4 : fetch_word Ubsan.M.loaded_segments (0xb7c54 : word) = Some W_b5dc4.
Proof. vm_refl. Qed.
Lemma D_b5dc4 : decode_any W_b5dc4 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dc8 : bv 32 := 0x00071863.
Lemma F_b5dc8 : fetch_word Ubsan.M.loaded_segments (0xb7c58 : word) = Some W_b5dc8.
Proof. vm_refl. Qed.
Lemma D_b5dc8 : decode_any W_b5dc8 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dcc : bv 32 := 0x00167613.
Lemma F_b5dcc : fetch_word Ubsan.M.loaded_segments (0xb7c5c : word) = Some W_b5dcc.
Proof. vm_refl. Qed.
Lemma D_b5dcc : decode_any W_b5dcc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dd0 : bv 32 := 0x02061663.
Lemma F_b5dd0 : fetch_word Ubsan.M.loaded_segments (0xb7c60 : word) = Some W_b5dd0.
Proof. vm_refl. Qed.
Lemma D_b5dd0 : decode_any W_b5dd0 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dd4 : bv 32 := 0x00008067.
Lemma F_b5dd4 : fetch_word Ubsan.M.loaded_segments (0xb7c64 : word) = Some W_b5dd4.
Proof. vm_refl. Qed.
Lemma D_b5dd4 : decode_any W_b5dd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dd8 : bv 32 := 0x0005c703.
Lemma F_b5dd8 : fetch_word Ubsan.M.loaded_segments (0xb7c68 : word) = Some W_b5dd8.
Proof. vm_refl. Qed.
Lemma D_b5dd8 : decode_any W_b5dd8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ddc : bv 32 := 0x0015c783.
Lemma F_b5ddc : fetch_word Ubsan.M.loaded_segments (0xb7c6c : word) = Some W_b5ddc.
Proof. vm_refl. Qed.
Lemma D_b5ddc : decode_any W_b5ddc = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5de0 : bv 32 := 0x00258593.
Lemma F_b5de0 : fetch_word Ubsan.M.loaded_segments (0xb7c70 : word) = Some W_b5de0.
Proof. vm_refl. Qed.
Lemma D_b5de0 : decode_any W_b5de0 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5de4 : bv 32 := 0x00268813.
Lemma F_b5de4 : fetch_word Ubsan.M.loaded_segments (0xb7c74 : word) = Some W_b5de4.
Proof. vm_refl. Qed.
Lemma D_b5de4 : decode_any W_b5de4 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5de8 : bv 32 := 0x00e68023.
Lemma F_b5de8 : fetch_word Ubsan.M.loaded_segments (0xb7c78 : word) = Some W_b5de8.
Proof. vm_refl. Qed.
Lemma D_b5de8 : decode_any W_b5de8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dec : bv 32 := 0x00f680a3.
Lemma F_b5dec : fetch_word Ubsan.M.loaded_segments (0xb7c7c : word) = Some W_b5dec.
Proof. vm_refl. Qed.
Lemma D_b5dec : decode_any W_b5dec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5df0 : bv 32 := 0x00080693.
Lemma F_b5df0 : fetch_word Ubsan.M.loaded_segments (0xb7c80 : word) = Some W_b5df0.
Proof. vm_refl. Qed.
Lemma D_b5df0 : decode_any W_b5df0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5df4 : bv 32 := 0x00167613.
Lemma F_b5df4 : fetch_word Ubsan.M.loaded_segments (0xb7c84 : word) = Some W_b5df4.
Proof. vm_refl. Qed.
Lemma D_b5df4 : decode_any W_b5df4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5df8 : bv 32 := 0xfc060ee3.
Lemma F_b5df8 : fetch_word Ubsan.M.loaded_segments (0xb7c88 : word) = Some W_b5df8.
Proof. vm_refl. Qed.
Lemma D_b5df8 : decode_any W_b5df8 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5dfc : bv 32 := 0x0005c583.
Lemma F_b5dfc : fetch_word Ubsan.M.loaded_segments (0xb7c8c : word) = Some W_b5dfc.
Proof. vm_refl. Qed.
Lemma D_b5dfc : decode_any W_b5dfc = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5e00 : bv 32 := 0x00b68023.
Lemma F_b5e00 : fetch_word Ubsan.M.loaded_segments (0xb7c90 : word) = Some W_b5e00.
Proof. vm_refl. Qed.
Lemma D_b5e00 : decode_any W_b5e00 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5e04 : bv 32 := 0x00008067.
Lemma F_b5e04 : fetch_word Ubsan.M.loaded_segments (0xb7c94 : word) = Some W_b5e04.
Proof. vm_refl. Qed.
Lemma D_b5e04 : decode_any W_b5e04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f84 : bv 32 := 0x0e060a63.
Lemma F_b5f84 : fetch_word Ubsan.M.loaded_segments (0xb7e14 : word) = Some W_b5f84.
Proof. vm_refl. Qed.
Lemma D_b5f84 : decode_any W_b5f84 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f88 : bv 32 := 0x00b50023.
Lemma F_b5f88 : fetch_word Ubsan.M.loaded_segments (0xb7e18 : word) = Some W_b5f88.
Proof. vm_refl. Qed.
Lemma D_b5f88 : decode_any W_b5f88 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f8c : bv 32 := 0x00c506b3.
Lemma F_b5f8c : fetch_word Ubsan.M.loaded_segments (0xb7e1c : word) = Some W_b5f8c.
Proof. vm_refl. Qed.
Lemma D_b5f8c : decode_any W_b5f8c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f90 : bv 32 := 0x00300713.
Lemma F_b5f90 : fetch_word Ubsan.M.loaded_segments (0xb7e20 : word) = Some W_b5f90.
Proof. vm_refl. Qed.
Lemma D_b5f90 : decode_any W_b5f90 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f94 : bv 32 := 0xfeb68fa3.
Lemma F_b5f94 : fetch_word Ubsan.M.loaded_segments (0xb7e24 : word) = Some W_b5f94.
Proof. vm_refl. Qed.
Lemma D_b5f94 : decode_any W_b5f94 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f98 : bv 32 := 0x0ee66063.
Lemma F_b5f98 : fetch_word Ubsan.M.loaded_segments (0xb7e28 : word) = Some W_b5f98.
Proof. vm_refl. Qed.
Lemma D_b5f98 : decode_any W_b5f98 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5f9c : bv 32 := 0x00b500a3.
Lemma F_b5f9c : fetch_word Ubsan.M.loaded_segments (0xb7e2c : word) = Some W_b5f9c.
Proof. vm_refl. Qed.
Lemma D_b5f9c : decode_any W_b5f9c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fa0 : bv 32 := 0x00b50123.
Lemma F_b5fa0 : fetch_word Ubsan.M.loaded_segments (0xb7e30 : word) = Some W_b5fa0.
Proof. vm_refl. Qed.
Lemma D_b5fa0 : decode_any W_b5fa0 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fa4 : bv 32 := 0x00700713.
Lemma F_b5fa4 : fetch_word Ubsan.M.loaded_segments (0xb7e34 : word) = Some W_b5fa4.
Proof. vm_refl. Qed.
Lemma D_b5fa4 : decode_any W_b5fa4 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fa8 : bv 32 := 0xfeb68ea3.
Lemma F_b5fa8 : fetch_word Ubsan.M.loaded_segments (0xb7e38 : word) = Some W_b5fa8.
Proof. vm_refl. Qed.
Lemma D_b5fa8 : decode_any W_b5fa8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fac : bv 32 := 0xfeb68f23.
Lemma F_b5fac : fetch_word Ubsan.M.loaded_segments (0xb7e3c : word) = Some W_b5fac.
Proof. vm_refl. Qed.
Lemma D_b5fac : decode_any W_b5fac = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fb0 : bv 32 := 0x0ce66463.
Lemma F_b5fb0 : fetch_word Ubsan.M.loaded_segments (0xb7e40 : word) = Some W_b5fb0.
Proof. vm_refl. Qed.
Lemma D_b5fb0 : decode_any W_b5fb0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fb4 : bv 32 := 0x00b501a3.
Lemma F_b5fb4 : fetch_word Ubsan.M.loaded_segments (0xb7e44 : word) = Some W_b5fb4.
Proof. vm_refl. Qed.
Lemma D_b5fb4 : decode_any W_b5fb4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fb8 : bv 32 := 0x00900793.
Lemma F_b5fb8 : fetch_word Ubsan.M.loaded_segments (0xb7e48 : word) = Some W_b5fb8.
Proof. vm_refl. Qed.
Lemma D_b5fb8 : decode_any W_b5fb8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fbc : bv 32 := 0xfeb68e23.
Lemma F_b5fbc : fetch_word Ubsan.M.loaded_segments (0xb7e4c : word) = Some W_b5fbc.
Proof. vm_refl. Qed.
Lemma D_b5fbc : decode_any W_b5fbc = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fc0 : bv 32 := 0x0af66c63.
Lemma F_b5fc0 : fetch_word Ubsan.M.loaded_segments (0xb7e50 : word) = Some W_b5fc0.
Proof. vm_refl. Qed.
Lemma D_b5fc0 : decode_any W_b5fc0 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fc4 : bv 32 := 0x40a006bb.
Lemma F_b5fc4 : fetch_word Ubsan.M.loaded_segments (0xb7e54 : word) = Some W_b5fc4.
Proof. vm_refl. Qed.
Lemma D_b5fc4 : decode_any W_b5fc4 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fc8 : bv 32 := 0x03859813.
Lemma F_b5fc8 : fetch_word Ubsan.M.loaded_segments (0xb7e58 : word) = Some W_b5fc8.
Proof. vm_refl. Qed.
Lemma D_b5fc8 : decode_any W_b5fc8 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fcc : bv 32 := 0x101015b7.
Lemma F_b5fcc : fetch_word Ubsan.M.loaded_segments (0xb7e5c : word) = Some W_b5fcc.
Proof. vm_refl. Qed.
Lemma D_b5fcc : decode_any W_b5fcc = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fd0 : bv 32 := 0x0036f693.
Lemma F_b5fd0 : fetch_word Ubsan.M.loaded_segments (0xb7e60 : word) = Some W_b5fd0.
Proof. vm_refl. Qed.
Lemma D_b5fd0 : decode_any W_b5fd0 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fd4 : bv 32 := 0x00459713.
Lemma F_b5fd4 : fetch_word Ubsan.M.loaded_segments (0xb7e64 : word) = Some W_b5fd4.
Proof. vm_refl. Qed.
Lemma D_b5fd4 : decode_any W_b5fd4 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fd8 : bv 32 := 0x40d60633.
Lemma F_b5fd8 : fetch_word Ubsan.M.loaded_segments (0xb7e68 : word) = Some W_b5fd8.
Proof. vm_refl. Qed.
Lemma D_b5fd8 : decode_any W_b5fd8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fdc : bv 32 := 0x00d505b3.
Lemma F_b5fdc : fetch_word Ubsan.M.loaded_segments (0xb7e6c : word) = Some W_b5fdc.
Proof. vm_refl. Qed.
Lemma D_b5fdc : decode_any W_b5fdc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fe0 : bv 32 := 0x10070693.
Lemma F_b5fe0 : fetch_word Ubsan.M.loaded_segments (0xb7e70 : word) = Some W_b5fe0.
Proof. vm_refl. Qed.
Lemma D_b5fe0 : decode_any W_b5fe0 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fe4 : bv 32 := 0xffc67713.
Lemma F_b5fe4 : fetch_word Ubsan.M.loaded_segments (0xb7e74 : word) = Some W_b5fe4.
Proof. vm_refl. Qed.
Lemma D_b5fe4 : decode_any W_b5fe4 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fe8 : bv 32 := 0x02d83633.
Lemma F_b5fe8 : fetch_word Ubsan.M.loaded_segments (0xb7e78 : word) = Some W_b5fe8.
Proof. vm_refl. Qed.
Lemma D_b5fe8 : decode_any W_b5fe8 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5fec : bv 32 := 0x00c5a023.
Lemma F_b5fec : fetch_word Ubsan.M.loaded_segments (0xb7e7c : word) = Some W_b5fec.
Proof. vm_refl. Qed.
Lemma D_b5fec : decode_any W_b5fec = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ff0 : bv 32 := 0x00e586b3.
Lemma F_b5ff0 : fetch_word Ubsan.M.loaded_segments (0xb7e80 : word) = Some W_b5ff0.
Proof. vm_refl. Qed.
Lemma D_b5ff0 : decode_any W_b5ff0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ff4 : bv 32 := 0xfec6ae23.
Lemma F_b5ff4 : fetch_word Ubsan.M.loaded_segments (0xb7e84 : word) = Some W_b5ff4.
Proof. vm_refl. Qed.
Lemma D_b5ff4 : decode_any W_b5ff4 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ff8 : bv 32 := 0x08f76063.
Lemma F_b5ff8 : fetch_word Ubsan.M.loaded_segments (0xb7e88 : word) = Some W_b5ff8.
Proof. vm_refl. Qed.
Lemma D_b5ff8 : decode_any W_b5ff8 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_b5ffc : bv 32 := 0x00c5a223.
Lemma F_b5ffc : fetch_word Ubsan.M.loaded_segments (0xb7e8c : word) = Some W_b5ffc.
Proof. vm_refl. Qed.
Lemma D_b5ffc : decode_any W_b5ffc = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

