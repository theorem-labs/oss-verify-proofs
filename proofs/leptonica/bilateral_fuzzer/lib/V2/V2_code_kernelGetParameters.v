(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_38860 : bv 32 := 0x0035f793.
Lemma F_38860 : fetch_word Ubsan.M.loaded_segments (0x38860 : word) = Some W_38860.
Proof. vm_refl. Qed.
Lemma D_38860 : decode_any W_38860 = Some (OpImm ALU_AND 15 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38864 : bv 32 := 0x00058663.
Lemma F_38864 : fetch_word Ubsan.M.loaded_segments (0x38864 : word) = Some W_38864.
Proof. vm_refl. Qed.
Lemma D_38864 : decode_any W_38864 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38868 : bv 32 := 0x0c079a63.
Lemma F_38868 : fetch_word Ubsan.M.loaded_segments (0x38868 : word) = Some W_38868.
Proof. vm_refl. Qed.
Lemma D_38868 : decode_any W_38868 = Some (Branch BC_NE 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_3886c : bv 32 := 0x0005a023.
Lemma F_3886c : fetch_word Ubsan.M.loaded_segments (0x3886c : word) = Some W_3886c.
Proof. vm_refl. Qed.
Lemma D_3886c : decode_any W_3886c = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38870 : bv 32 := 0x00367813.
Lemma F_38870 : fetch_word Ubsan.M.loaded_segments (0x38870 : word) = Some W_38870.
Proof. vm_refl. Qed.
Lemma D_38870 : decode_any W_38870 = Some (OpImm ALU_AND 16 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38874 : bv 32 := 0x00060663.
Lemma F_38874 : fetch_word Ubsan.M.loaded_segments (0x38874 : word) = Some W_38874.
Proof. vm_refl. Qed.
Lemma D_38874 : decode_any W_38874 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38878 : bv 32 := 0x0c081263.
Lemma F_38878 : fetch_word Ubsan.M.loaded_segments (0x38878 : word) = Some W_38878.
Proof. vm_refl. Qed.
Lemma D_38878 : decode_any W_38878 = Some (Branch BC_NE 16 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_3887c : bv 32 := 0x00062023.
Lemma F_3887c : fetch_word Ubsan.M.loaded_segments (0x3887c : word) = Some W_3887c.
Proof. vm_refl. Qed.
Lemma D_3887c : decode_any W_3887c = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38880 : bv 32 := 0x0036f893.
Lemma F_38880 : fetch_word Ubsan.M.loaded_segments (0x38880 : word) = Some W_38880.
Proof. vm_refl. Qed.
Lemma D_38880 : decode_any W_38880 = Some (OpImm ALU_AND 17 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38884 : bv 32 := 0x00068663.
Lemma F_38884 : fetch_word Ubsan.M.loaded_segments (0x38884 : word) = Some W_38884.
Proof. vm_refl. Qed.
Lemma D_38884 : decode_any W_38884 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38888 : bv 32 := 0x0a089a63.
Lemma F_38888 : fetch_word Ubsan.M.loaded_segments (0x38888 : word) = Some W_38888.
Proof. vm_refl. Qed.
Lemma D_38888 : decode_any W_38888 = Some (Branch BC_NE 17 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_3888c : bv 32 := 0x0006a023.
Lemma F_3888c : fetch_word Ubsan.M.loaded_segments (0x3888c : word) = Some W_3888c.
Proof. vm_refl. Qed.
Lemma D_3888c : decode_any W_3888c = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38890 : bv 32 := 0x00377293.
Lemma F_38890 : fetch_word Ubsan.M.loaded_segments (0x38890 : word) = Some W_38890.
Proof. vm_refl. Qed.
Lemma D_38890 : decode_any W_38890 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38894 : bv 32 := 0x00070663.
Lemma F_38894 : fetch_word Ubsan.M.loaded_segments (0x38894 : word) = Some W_38894.
Proof. vm_refl. Qed.
Lemma D_38894 : decode_any W_38894 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38898 : bv 32 := 0x0a029263.
Lemma F_38898 : fetch_word Ubsan.M.loaded_segments (0x38898 : word) = Some W_38898.
Proof. vm_refl. Qed.
Lemma D_38898 : decode_any W_38898 = Some (Branch BC_NE 5 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_3889c : bv 32 := 0x00072023.
Lemma F_3889c : fetch_word Ubsan.M.loaded_segments (0x3889c : word) = Some W_3889c.
Proof. vm_refl. Qed.
Lemma D_3889c : decode_any W_3889c = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388a0 : bv 32 := 0x06050063.
Lemma F_388a0 : fetch_word Ubsan.M.loaded_segments (0x388a0 : word) = Some W_388a0.
Proof. vm_refl. Qed.
Lemma D_388a0 : decode_any W_388a0 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_388a4 : bv 32 := 0x00757313.
Lemma F_388a4 : fetch_word Ubsan.M.loaded_segments (0x388a4 : word) = Some W_388a4.
Proof. vm_refl. Qed.
Lemma D_388a4 : decode_any W_388a4 = Some (OpImm ALU_AND 6 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_388a8 : bv 32 := 0x00058a63.
Lemma F_388a8 : fetch_word Ubsan.M.loaded_segments (0x388a8 : word) = Some W_388a8.
Proof. vm_refl. Qed.
Lemma D_388a8 : decode_any W_388a8 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_388ac : bv 32 := 0x00f367b3.
Lemma F_388ac : fetch_word Ubsan.M.loaded_segments (0x388ac : word) = Some W_388ac.
Proof. vm_refl. Qed.
Lemma D_388ac : decode_any W_388ac = Some (Op ALU_OR 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_388b0 : bv 32 := 0x08079663.
Lemma F_388b0 : fetch_word Ubsan.M.loaded_segments (0x388b0 : word) = Some W_388b0.
Proof. vm_refl. Qed.
Lemma D_388b0 : decode_any W_388b0 = Some (Branch BC_NE 15 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_388b4 : bv 32 := 0x00052783.
Lemma F_388b4 : fetch_word Ubsan.M.loaded_segments (0x388b4 : word) = Some W_388b4.
Proof. vm_refl. Qed.
Lemma D_388b4 : decode_any W_388b4 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388b8 : bv 32 := 0x00f5a023.
Lemma F_388b8 : fetch_word Ubsan.M.loaded_segments (0x388b8 : word) = Some W_388b8.
Proof. vm_refl. Qed.
Lemma D_388b8 : decode_any W_388b8 = Some (Store SZ4 11 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388bc : bv 32 := 0x00060a63.
Lemma F_388bc : fetch_word Ubsan.M.loaded_segments (0x388bc : word) = Some W_388bc.
Proof. vm_refl. Qed.
Lemma D_388bc : decode_any W_388bc = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_388c0 : bv 32 := 0x010365b3.
Lemma F_388c0 : fetch_word Ubsan.M.loaded_segments (0x388c0 : word) = Some W_388c0.
Proof. vm_refl. Qed.
Lemma D_388c0 : decode_any W_388c0 = Some (Op ALU_OR 11 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_388c4 : bv 32 := 0x06059c63.
Lemma F_388c4 : fetch_word Ubsan.M.loaded_segments (0x388c4 : word) = Some W_388c4.
Proof. vm_refl. Qed.
Lemma D_388c4 : decode_any W_388c4 = Some (Branch BC_NE 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_388c8 : bv 32 := 0x00452583.
Lemma F_388c8 : fetch_word Ubsan.M.loaded_segments (0x388c8 : word) = Some W_388c8.
Proof. vm_refl. Qed.
Lemma D_388c8 : decode_any W_388c8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_388cc : bv 32 := 0x00b62023.
Lemma F_388cc : fetch_word Ubsan.M.loaded_segments (0x388cc : word) = Some W_388cc.
Proof. vm_refl. Qed.
Lemma D_388cc : decode_any W_388cc = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388d0 : bv 32 := 0x00068a63.
Lemma F_388d0 : fetch_word Ubsan.M.loaded_segments (0x388d0 : word) = Some W_388d0.
Proof. vm_refl. Qed.
Lemma D_388d0 : decode_any W_388d0 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_388d4 : bv 32 := 0x011365b3.
Lemma F_388d4 : fetch_word Ubsan.M.loaded_segments (0x388d4 : word) = Some W_388d4.
Proof. vm_refl. Qed.
Lemma D_388d4 : decode_any W_388d4 = Some (Op ALU_OR 11 6 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_388d8 : bv 32 := 0x06059263.
Lemma F_388d8 : fetch_word Ubsan.M.loaded_segments (0x388d8 : word) = Some W_388d8.
Proof. vm_refl. Qed.
Lemma D_388d8 : decode_any W_388d8 = Some (Branch BC_NE 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_388dc : bv 32 := 0x00852583.
Lemma F_388dc : fetch_word Ubsan.M.loaded_segments (0x388dc : word) = Some W_388dc.
Proof. vm_refl. Qed.
Lemma D_388dc : decode_any W_388dc = Some (Load SZ4 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_388e0 : bv 32 := 0x00b6a023.
Lemma F_388e0 : fetch_word Ubsan.M.loaded_segments (0x388e0 : word) = Some W_388e0.
Proof. vm_refl. Qed.
Lemma D_388e0 : decode_any W_388e0 = Some (Store SZ4 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388e4 : bv 32 := 0x04070463.
Lemma F_388e4 : fetch_word Ubsan.M.loaded_segments (0x388e4 : word) = Some W_388e4.
Proof. vm_refl. Qed.
Lemma D_388e4 : decode_any W_388e4 = Some (Branch BC_EQ 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_388e8 : bv 32 := 0x005365b3.
Lemma F_388e8 : fetch_word Ubsan.M.loaded_segments (0x388e8 : word) = Some W_388e8.
Proof. vm_refl. Qed.
Lemma D_388e8 : decode_any W_388e8 = Some (Op ALU_OR 11 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_388ec : bv 32 := 0x04059863.
Lemma F_388ec : fetch_word Ubsan.M.loaded_segments (0x388ec : word) = Some W_388ec.
Proof. vm_refl. Qed.
Lemma D_388ec : decode_any W_388ec = Some (Branch BC_NE 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_388f0 : bv 32 := 0x00c52503.
Lemma F_388f0 : fetch_word Ubsan.M.loaded_segments (0x388f0 : word) = Some W_388f0.
Proof. vm_refl. Qed.
Lemma D_388f0 : decode_any W_388f0 = Some (Load SZ4 true 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_388f4 : bv 32 := 0x00a72023.
Lemma F_388f4 : fetch_word Ubsan.M.loaded_segments (0x388f4 : word) = Some W_388f4.
Proof. vm_refl. Qed.
Lemma D_388f4 : decode_any W_388f4 = Some (Store SZ4 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388f8 : bv 32 := 0x00058513.
Lemma F_388f8 : fetch_word Ubsan.M.loaded_segments (0x388f8 : word) = Some W_388f8.
Proof. vm_refl. Qed.
Lemma D_388f8 : decode_any W_388f8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_388fc : bv 32 := 0x00008067.
Lemma F_388fc : fetch_word Ubsan.M.loaded_segments (0x388fc : word) = Some W_388fc.
Proof. vm_refl. Qed.
Lemma D_388fc : decode_any W_388fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38900 : bv 32 := 0x0000c517.
Lemma F_38900 : fetch_word Ubsan.M.loaded_segments (0x38900 : word) = Some W_38900.
Proof. vm_refl. Qed.
Lemma D_38900 : decode_any W_38900 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38904 : bv 32 := 0x59853503.
Lemma F_38904 : fetch_word Ubsan.M.loaded_segments (0x38904 : word) = Some W_38904.
Proof. vm_refl. Qed.
Lemma D_38904 : decode_any W_38904 = Some (Load SZ8 true 10 10 1432, 4%Z).
Proof. vm_refl. Qed.

Definition W_38908 : bv 32 := 0x00052503.
Lemma F_38908 : fetch_word Ubsan.M.loaded_segments (0x38908 : word) = Some W_38908.
Proof. vm_refl. Qed.
Lemma D_38908 : decode_any W_38908 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3890c : bv 32 := 0x00500593.
Lemma F_3890c : fetch_word Ubsan.M.loaded_segments (0x3890c : word) = Some W_3890c.
Proof. vm_refl. Qed.
Lemma D_3890c : decode_any W_3890c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38910 : bv 32 := 0x02a5c263.
Lemma F_38910 : fetch_word Ubsan.M.loaded_segments (0x38910 : word) = Some W_38910.
Proof. vm_refl. Qed.
Lemma D_38910 : decode_any W_38910 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_38914 : bv 32 := 0xfffda517.
Lemma F_38914 : fetch_word Ubsan.M.loaded_segments (0x38914 : word) = Some W_38914.
Proof. vm_refl. Qed.
Lemma D_38914 : decode_any W_38914 = Some (Auipc 10 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_38918 : bv 32 := 0xfffd8597.
Lemma F_38918 : fetch_word Ubsan.M.loaded_segments (0x38918 : word) = Some W_38918.
Proof. vm_refl. Qed.
Lemma D_38918 : decode_any W_38918 = Some (Auipc 11 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3891c : bv 32 := 0x8af50513.
Lemma F_3891c : fetch_word Ubsan.M.loaded_segments (0x3891c : word) = Some W_3891c.
Proof. vm_refl. Qed.
Lemma D_3891c : decode_any W_3891c = Some (OpImm ALU_ADD 10 10 2223, 4%Z).
Proof. vm_refl. Qed.

Definition W_38920 : bv 32 := 0xdd858593.
Lemma F_38920 : fetch_word Ubsan.M.loaded_segments (0x38920 : word) = Some W_38920.
Proof. vm_refl. Qed.
Lemma D_38920 : decode_any W_38920 = Some (OpImm ALU_ADD 11 11 3544, 4%Z).
Proof. vm_refl. Qed.

Definition W_38924 : bv 32 := 0x00100613.
Lemma F_38924 : fetch_word Ubsan.M.loaded_segments (0x38924 : word) = Some W_38924.
Proof. vm_refl. Qed.
Lemma D_38924 : decode_any W_38924 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38928 : bv 32 := 0xcccdf06f.
Lemma F_38928 : fetch_word Ubsan.M.loaded_segments (0x38928 : word) = Some W_38928.
Proof. vm_refl. Qed.
Lemma D_38928 : decode_any W_38928 = Some (Jal 0 1963212, 4%Z).
Proof. vm_refl. Qed.

Definition W_3892c : bv 32 := 0x00000513.
Lemma F_3892c : fetch_word Ubsan.M.loaded_segments (0x3892c : word) = Some W_3892c.
Proof. vm_refl. Qed.
Lemma D_3892c : decode_any W_3892c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38930 : bv 32 := 0x00008067.
Lemma F_38930 : fetch_word Ubsan.M.loaded_segments (0x38930 : word) = Some W_38930.
Proof. vm_refl. Qed.
Lemma D_38930 : decode_any W_38930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38934 : bv 32 := 0x00100513.
Lemma F_38934 : fetch_word Ubsan.M.loaded_segments (0x38934 : word) = Some W_38934.
Proof. vm_refl. Qed.
Lemma D_38934 : decode_any W_38934 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38938 : bv 32 := 0x00008067.
Lemma F_38938 : fetch_word Ubsan.M.loaded_segments (0x38938 : word) = Some W_38938.
Proof. vm_refl. Qed.
Lemma D_38938 : decode_any W_38938 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3893c : bv 32 := 0xc0001073.
Lemma F_3893c : fetch_word Ubsan.M.loaded_segments (0x3893c : word) = Some W_3893c.
Proof. vm_refl. Qed.
Lemma D_3893c : decode_any W_3893c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
