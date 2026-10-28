(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_997e0 : bv 32 := 0xf9010113.
Lemma F_997e0 : fetch_word Ubsan.M.loaded_segments (0x997e0 : word) = Some W_997e0.
Proof. vm_refl. Qed.
Lemma D_997e0 : decode_any W_997e0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_997e4 : bv 32 := 0x06113423.
Lemma F_997e4 : fetch_word Ubsan.M.loaded_segments (0x997e4 : word) = Some W_997e4.
Proof. vm_refl. Qed.
Lemma D_997e4 : decode_any W_997e4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_997e8 : bv 32 := 0x06813023.
Lemma F_997e8 : fetch_word Ubsan.M.loaded_segments (0x997e8 : word) = Some W_997e8.
Proof. vm_refl. Qed.
Lemma D_997e8 : decode_any W_997e8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_997ec : bv 32 := 0x04913c23.
Lemma F_997ec : fetch_word Ubsan.M.loaded_segments (0x997ec : word) = Some W_997ec.
Proof. vm_refl. Qed.
Lemma D_997ec : decode_any W_997ec = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_997f0 : bv 32 := 0x05213823.
Lemma F_997f0 : fetch_word Ubsan.M.loaded_segments (0x997f0 : word) = Some W_997f0.
Proof. vm_refl. Qed.
Lemma D_997f0 : decode_any W_997f0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_997f4 : bv 32 := 0x05313423.
Lemma F_997f4 : fetch_word Ubsan.M.loaded_segments (0x997f4 : word) = Some W_997f4.
Proof. vm_refl. Qed.
Lemma D_997f4 : decode_any W_997f4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_997f8 : bv 32 := 0x05413023.
Lemma F_997f8 : fetch_word Ubsan.M.loaded_segments (0x997f8 : word) = Some W_997f8.
Proof. vm_refl. Qed.
Lemma D_997f8 : decode_any W_997f8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_997fc : bv 32 := 0x03513c23.
Lemma F_997fc : fetch_word Ubsan.M.loaded_segments (0x997fc : word) = Some W_997fc.
Proof. vm_refl. Qed.
Lemma D_997fc : decode_any W_997fc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_99800 : bv 32 := 0x03613823.
Lemma F_99800 : fetch_word Ubsan.M.loaded_segments (0x99800 : word) = Some W_99800.
Proof. vm_refl. Qed.
Lemma D_99800 : decode_any W_99800 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_99804 : bv 32 := 0x03713423.
Lemma F_99804 : fetch_word Ubsan.M.loaded_segments (0x99804 : word) = Some W_99804.
Proof. vm_refl. Qed.
Lemma D_99804 : decode_any W_99804 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_99808 : bv 32 := 0x03813023.
Lemma F_99808 : fetch_word Ubsan.M.loaded_segments (0x99808 : word) = Some W_99808.
Proof. vm_refl. Qed.
Lemma D_99808 : decode_any W_99808 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9980c : bv 32 := 0x01913c23.
Lemma F_9980c : fetch_word Ubsan.M.loaded_segments (0x9980c : word) = Some W_9980c.
Proof. vm_refl. Qed.
Lemma D_9980c : decode_any W_9980c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_99810 : bv 32 := 0x01a13823.
Lemma F_99810 : fetch_word Ubsan.M.loaded_segments (0x99810 : word) = Some W_99810.
Proof. vm_refl. Qed.
Lemma D_99810 : decode_any W_99810 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_99814 : bv 32 := 0x01b13423.
Lemma F_99814 : fetch_word Ubsan.M.loaded_segments (0x99814 : word) = Some W_99814.
Proof. vm_refl. Qed.
Lemma D_99814 : decode_any W_99814 = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_99818 : bv 32 := 0x18058263.
Lemma F_99818 : fetch_word Ubsan.M.loaded_segments (0x99818 : word) = Some W_99818.
Proof. vm_refl. Qed.
Lemma D_99818 : decode_any W_99818 = Some (Branch BC_EQ 11 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_9981c : bv 32 := 0x00058413.
Lemma F_9981c : fetch_word Ubsan.M.loaded_segments (0x9981c : word) = Some W_9981c.
Proof. vm_refl. Qed.
Lemma D_9981c : decode_any W_9981c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99820 : bv 32 := 0x00050493.
Lemma F_99820 : fetch_word Ubsan.M.loaded_segments (0x99820 : word) = Some W_99820.
Proof. vm_refl. Qed.
Lemma D_99820 : decode_any W_99820 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99824 : bv 32 := 0x00410613.
Lemma F_99824 : fetch_word Ubsan.M.loaded_segments (0x99824 : word) = Some W_99824.
Proof. vm_refl. Qed.
Lemma D_99824 : decode_any W_99824 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_99828 : bv 32 := 0x00010693.
Lemma F_99828 : fetch_word Ubsan.M.loaded_segments (0x99828 : word) = Some W_99828.
Proof. vm_refl. Qed.
Lemma D_99828 : decode_any W_99828 = Some (OpImm ALU_ADD 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9982c : bv 32 := 0x00058513.
Lemma F_9982c : fetch_word Ubsan.M.loaded_segments (0x9982c : word) = Some W_9982c.
Proof. vm_refl. Qed.
Lemma D_9982c : decode_any W_9982c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99830 : bv 32 := 0x00000593.
Lemma F_99830 : fetch_word Ubsan.M.loaded_segments (0x99830 : word) = Some W_99830.
Proof. vm_refl. Qed.
Lemma D_99830 : decode_any W_99830 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99834 : bv 32 := 0xa71d40ef.
Lemma F_99834 : fetch_word Ubsan.M.loaded_segments (0x99834 : word) = Some W_99834.
Proof. vm_refl. Qed.
Lemma D_99834 : decode_any W_99834 = Some (Jal 1 1919600, 4%Z).
Proof. vm_refl. Qed.

Definition W_99838 : bv 32 := 0x00012503.
Lemma F_99838 : fetch_word Ubsan.M.loaded_segments (0x99838 : word) = Some W_99838.
Proof. vm_refl. Qed.
Lemma D_99838 : decode_any W_99838 = Some (Load SZ4 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9983c : bv 32 := 0x02000593.
Lemma F_9983c : fetch_word Ubsan.M.loaded_segments (0x9983c : word) = Some W_9983c.
Proof. vm_refl. Qed.
Lemma D_9983c : decode_any W_9983c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_99840 : bv 32 := 0x22a5e663.
Lemma F_99840 : fetch_word Ubsan.M.loaded_segments (0x99840 : word) = Some W_99840.
Proof. vm_refl. Qed.
Lemma D_99840 : decode_any W_99840 = Some (Branch BC_LTU 11 10 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_99844 : bv 32 := 0x100015b7.
Lemma F_99844 : fetch_word Ubsan.M.loaded_segments (0x99844 : word) = Some W_99844.
Proof. vm_refl. Qed.
Lemma D_99844 : decode_any W_99844 = Some (Lui 11 65537, 4%Z).
Proof. vm_refl. Qed.

Definition W_99848 : bv 32 := 0x00459593.
Lemma F_99848 : fetch_word Ubsan.M.loaded_segments (0x99848 : word) = Some W_99848.
Proof. vm_refl. Qed.
Lemma D_99848 : decode_any W_99848 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9984c : bv 32 := 0x11658593.
Lemma F_9984c : fetch_word Ubsan.M.loaded_segments (0x9984c : word) = Some W_9984c.
Proof. vm_refl. Qed.
Lemma D_9984c : decode_any W_9984c = Some (OpImm ALU_ADD 11 11 278, 4%Z).
Proof. vm_refl. Qed.

Definition W_99850 : bv 32 := 0x00a5d533.
Lemma F_99850 : fetch_word Ubsan.M.loaded_segments (0x99850 : word) = Some W_99850.
Proof. vm_refl. Qed.
Lemma D_99850 : decode_any W_99850 = Some (Op ALU_SRL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_99854 : bv 32 := 0x00157513.
Lemma F_99854 : fetch_word Ubsan.M.loaded_segments (0x99854 : word) = Some W_99854.
Proof. vm_refl. Qed.
Lemma D_99854 : decode_any W_99854 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_99858 : bv 32 := 0x20050a63.
Lemma F_99858 : fetch_word Ubsan.M.loaded_segments (0x99858 : word) = Some W_99858.
Proof. vm_refl. Qed.
Lemma D_99858 : decode_any W_99858 = Some (Branch BC_EQ 10 0 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_9985c : bv 32 := 0x00048513.
Lemma F_9985c : fetch_word Ubsan.M.loaded_segments (0x9985c : word) = Some W_9985c.
Proof. vm_refl. Qed.
Lemma D_9985c : decode_any W_9985c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99860 : bv 32 := 0x00040593.
Lemma F_99860 : fetch_word Ubsan.M.loaded_segments (0x99860 : word) = Some W_99860.
Proof. vm_refl. Qed.
Lemma D_99860 : decode_any W_99860 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99864 : bv 32 := 0xaf8d50ef.
Lemma F_99864 : fetch_word Ubsan.M.loaded_segments (0x99864 : word) = Some W_99864.
Proof. vm_refl. Qed.
Lemma D_99864 : decode_any W_99864 = Some (Jal 1 1921784, 4%Z).
Proof. vm_refl. Qed.

Definition W_99868 : bv 32 := 0x1a050263.
Lemma F_99868 : fetch_word Ubsan.M.loaded_segments (0x99868 : word) = Some W_99868.
Proof. vm_refl. Qed.
Lemma D_99868 : decode_any W_99868 = Some (Branch BC_EQ 10 0 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_9986c : bv 32 := 0x00050913.
Lemma F_9986c : fetch_word Ubsan.M.loaded_segments (0x9986c : word) = Some W_9986c.
Proof. vm_refl. Qed.
Lemma D_9986c : decode_any W_9986c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99870 : bv 32 := 0x97dd50ef.
Lemma F_99870 : fetch_word Ubsan.M.loaded_segments (0x99870 : word) = Some W_99870.
Proof. vm_refl. Qed.
Lemma D_99870 : decode_any W_99870 = Some (Jal 1 1923452, 4%Z).
Proof. vm_refl. Qed.

Definition W_99874 : bv 32 := 0x00050493.
Lemma F_99874 : fetch_word Ubsan.M.loaded_segments (0x99874 : word) = Some W_99874.
Proof. vm_refl. Qed.
Lemma D_99874 : decode_any W_99874 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99878 : bv 32 := 0x00090413.
Lemma F_99878 : fetch_word Ubsan.M.loaded_segments (0x99878 : word) = Some W_99878.
Proof. vm_refl. Qed.
Lemma D_99878 : decode_any W_99878 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9987c : bv 32 := 0x00090513.
Lemma F_9987c : fetch_word Ubsan.M.loaded_segments (0x9987c : word) = Some W_9987c.
Proof. vm_refl. Qed.
Lemma D_9987c : decode_any W_9987c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99880 : bv 32 := 0xeccd40ef.
Lemma F_99880 : fetch_word Ubsan.M.loaded_segments (0x99880 : word) = Some W_99880.
Proof. vm_refl. Qed.
Lemma D_99880 : decode_any W_99880 = Some (Jal 1 1918668, 4%Z).
Proof. vm_refl. Qed.

Definition W_99884 : bv 32 := 0x00050913.
Lemma F_99884 : fetch_word Ubsan.M.loaded_segments (0x99884 : word) = Some W_99884.
Proof. vm_refl. Qed.
Lemma D_99884 : decode_any W_99884 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99888 : bv 32 := 0x00400593.
Lemma F_99888 : fetch_word Ubsan.M.loaded_segments (0x99888 : word) = Some W_99888.
Proof. vm_refl. Qed.
Lemma D_99888 : decode_any W_99888 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9988c : bv 32 := 0x655740ef.
Lemma F_9988c : fetch_word Ubsan.M.loaded_segments (0x9988c : word) = Some W_9988c.
Proof. vm_refl. Qed.
Lemma D_9988c : decode_any W_9988c = Some (Jal 1 478804, 4%Z).
Proof. vm_refl. Qed.

Definition W_99890 : bv 32 := 0x1a050263.
Lemma F_99890 : fetch_word Ubsan.M.loaded_segments (0x99890 : word) = Some W_99890.
Proof. vm_refl. Qed.
Lemma D_99890 : decode_any W_99890 = Some (Branch BC_EQ 10 0 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_99894 : bv 32 := 0x00050993.
Lemma F_99894 : fetch_word Ubsan.M.loaded_segments (0x99894 : word) = Some W_99894.
Proof. vm_refl. Qed.
Lemma D_99894 : decode_any W_99894 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99898 : bv 32 := 0x20000537.
Lemma F_99898 : fetch_word Ubsan.M.loaded_segments (0x99898 : word) = Some W_99898.
Proof. vm_refl. Qed.
Lemma D_99898 : decode_any W_99898 = Some (Lui 10 131072, 4%Z).
Proof. vm_refl. Qed.

Definition W_9989c : bv 32 := 0x00a90533.
Lemma F_9989c : fetch_word Ubsan.M.loaded_segments (0x9989c : word) = Some W_9989c.
Proof. vm_refl. Qed.
Lemma D_9989c : decode_any W_9989c = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_998a0 : bv 32 := 0x01e5551b.
Lemma F_998a0 : fetch_word Ubsan.M.loaded_segments (0x998a0 : word) = Some W_998a0.
Proof. vm_refl. Qed.
Lemma D_998a0 : decode_any W_998a0 = Some (ShiftImm32 ALU_SRL 10 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_998a4 : bv 32 := 0x0e051a63.
Lemma F_998a4 : fetch_word Ubsan.M.loaded_segments (0x998a4 : word) = Some W_998a4.
Proof. vm_refl. Qed.
Lemma D_998a4 : decode_any W_998a4 = Some (Branch BC_NE 10 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_998a8 : bv 32 := 0x00416583.
Lemma F_998a8 : fetch_word Ubsan.M.loaded_segments (0x998a8 : word) = Some W_998a8.
Proof. vm_refl. Qed.
Lemma D_998a8 : decode_any W_998a8 = Some (Load SZ4 false 11 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_998ac : bv 32 := 0x0005861b.
Lemma F_998ac : fetch_word Ubsan.M.loaded_segments (0x998ac : word) = Some W_998ac.
Proof. vm_refl. Qed.
Lemma D_998ac : decode_any W_998ac = Some (OpImm32 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_998b0 : bv 32 := 0xfff5851b.
Lemma F_998b0 : fetch_word Ubsan.M.loaded_segments (0x998b0 : word) = Some W_998b0.
Proof. vm_refl. Qed.
Lemma D_998b0 : decode_any W_998b0 = Some (OpImm32 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_998b4 : bv 32 := 0x0ec55263.
Lemma F_998b4 : fetch_word Ubsan.M.loaded_segments (0x998b4 : word) = Some W_998b4.
Proof. vm_refl. Qed.
Lemma D_998b4 : decode_any W_998b4 = Some (Branch BC_GE 10 12 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_998b8 : bv 32 := 0x00000b93.
Lemma F_998b8 : fetch_word Ubsan.M.loaded_segments (0x998b8 : word) = Some W_998b8.
Proof. vm_refl. Qed.
Lemma D_998b8 : decode_any W_998b8 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_998bc : bv 32 := 0x01f5d613.
Lemma F_998bc : fetch_word Ubsan.M.loaded_segments (0x998bc : word) = Some W_998bc.
Proof. vm_refl. Qed.
Lemma D_998bc : decode_any W_998bc = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_998c0 : bv 32 := 0x00291a1b.
Lemma F_998c0 : fetch_word Ubsan.M.loaded_segments (0x998c0 : word) = Some W_998c0.
Proof. vm_refl. Qed.
Lemma D_998c0 : decode_any W_998c0 = Some (ShiftImm32 ALU_SLL 20 18 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_998c4 : bv 32 := 0x0039fc13.
Lemma F_998c4 : fetch_word Ubsan.M.loaded_segments (0x998c4 : word) = Some W_998c4.
Proof. vm_refl. Qed.
Lemma D_998c4 : decode_any W_998c4 = Some (OpImm ALU_AND 24 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_998c8 : bv 32 := 0x00c585b3.
Lemma F_998c8 : fetch_word Ubsan.M.loaded_segments (0x998c8 : word) = Some W_998c8.
Proof. vm_refl. Qed.
Lemma D_998c8 : decode_any W_998c8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_998cc : bv 32 := 0x4015d59b.
Lemma F_998cc : fetch_word Ubsan.M.loaded_segments (0x998cc : word) = Some W_998cc.
Proof. vm_refl. Qed.
Lemma D_998cc : decode_any W_998cc = Some (ShiftImm32 ALU_SRA 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_998d0 : bv 32 := 0x00b02633.
Lemma F_998d0 : fetch_word Ubsan.M.loaded_segments (0x998d0 : word) = Some W_998d0.
Proof. vm_refl. Qed.
Lemma D_998d0 : decode_any W_998d0 = Some (Op ALU_SLT 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_998d4 : bv 32 := 0x40c0063b.
Lemma F_998d4 : fetch_word Ubsan.M.loaded_segments (0x998d4 : word) = Some W_998d4.
Proof. vm_refl. Qed.
Lemma D_998d4 : decode_any W_998d4 = Some (Op32 ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_998d8 : bv 32 := 0x00b67cb3.
Lemma F_998d8 : fetch_word Ubsan.M.loaded_segments (0x998d8 : word) = Some W_998d8.
Proof. vm_refl. Qed.
Lemma D_998d8 : decode_any W_998d8 = Some (Op ALU_AND 25 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_998dc : bv 32 := 0x00903d33.
Lemma F_998dc : fetch_word Ubsan.M.loaded_segments (0x998dc : word) = Some W_998dc.
Proof. vm_refl. Qed.
Lemma D_998dc : decode_any W_998dc = Some (Op ALU_SLTU 26 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_998e0 : bv 32 := 0x137c8063.
Lemma F_998e0 : fetch_word Ubsan.M.loaded_segments (0x998e0 : word) = Some W_998e0.
Proof. vm_refl. Qed.
Lemma D_998e0 : decode_any W_998e0 = Some (Branch BC_EQ 25 23 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_998e4 : bv 32 := 0x00050d93.
Lemma F_998e4 : fetch_word Ubsan.M.loaded_segments (0x998e4 : word) = Some W_998e4.
Proof. vm_refl. Qed.
Lemma D_998e4 : decode_any W_998e4 = Some (OpImm ALU_ADD 27 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_998e8 : bv 32 := 0x032b8533.
Lemma F_998e8 : fetch_word Ubsan.M.loaded_segments (0x998e8 : word) = Some W_998e8.
Proof. vm_refl. Qed.
Lemma D_998e8 : decode_any W_998e8 = Some (Mul M_MUL 10 23 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_998ec : bv 32 := 0x032b85bb.
Lemma F_998ec : fetch_word Ubsan.M.loaded_segments (0x998ec : word) = Some W_998ec.
Proof. vm_refl. Qed.
Lemma D_998ec : decode_any W_998ec = Some (Mul32 M_MUL 11 23 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_998f0 : bv 32 := 0x0aa59463.
Lemma F_998f0 : fetch_word Ubsan.M.loaded_segments (0x998f0 : word) = Some W_998f0.
Proof. vm_refl. Qed.
Lemma D_998f0 : decode_any W_998f0 = Some (Branch BC_NE 11 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_998f4 : bv 32 := 0x0005051b.
Lemma F_998f4 : fetch_word Ubsan.M.loaded_segments (0x998f4 : word) = Some W_998f4.
Proof. vm_refl. Qed.
Lemma D_998f4 : decode_any W_998f4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_998f8 : bv 32 := 0x00251a93.
Lemma F_998f8 : fetch_word Ubsan.M.loaded_segments (0x998f8 : word) = Some W_998f8.
Proof. vm_refl. Qed.
Lemma D_998f8 : decode_any W_998f8 = Some (ShiftImm ALU_SLL 21 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_998fc : bv 32 := 0x01548ab3.
Lemma F_998fc : fetch_word Ubsan.M.loaded_segments (0x998fc : word) = Some W_998fc.
Proof. vm_refl. Qed.
Lemma D_998fc : decode_any W_998fc = Some (Op ALU_ADD 21 9 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_99900 : bv 32 := 0x001ab593.
Lemma F_99900 : fetch_word Ubsan.M.loaded_segments (0x99900 : word) = Some W_99900.
Proof. vm_refl. Qed.
Lemma D_99900 : decode_any W_99900 = Some (OpImm ALU_SLTU 11 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_99904 : bv 32 := 0x08bd0a63.
Lemma F_99904 : fetch_word Ubsan.M.loaded_segments (0x99904 : word) = Some W_99904.
Proof. vm_refl. Qed.
Lemma D_99904 : decode_any W_99904 = Some (Branch BC_EQ 26 11 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_99908 : bv 32 := 0x009ab5b3.
Lemma F_99908 : fetch_word Ubsan.M.loaded_segments (0x99908 : word) = Some W_99908.
Proof. vm_refl. Qed.
Lemma D_99908 : decode_any W_99908 = Some (Op ALU_SLTU 11 21 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9990c : bv 32 := 0x00052513.
Lemma F_9990c : fetch_word Ubsan.M.loaded_segments (0x9990c : word) = Some W_9990c.
Proof. vm_refl. Qed.
Lemma D_9990c : decode_any W_9990c = Some (OpImm ALU_SLT 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99910 : bv 32 := 0x00a5c533.
Lemma F_99910 : fetch_word Ubsan.M.loaded_segments (0x99910 : word) = Some W_99910.
Proof. vm_refl. Qed.
Lemma D_99910 : decode_any W_99910 = Some (Op ALU_XOR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_99914 : bv 32 := 0x00154513.
Lemma F_99914 : fetch_word Ubsan.M.loaded_segments (0x99914 : word) = Some W_99914.
Proof. vm_refl. Qed.
Lemma D_99914 : decode_any W_99914 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_99918 : bv 32 := 0x08050063.
Lemma F_99918 : fetch_word Ubsan.M.loaded_segments (0x99918 : word) = Some W_99918.
Proof. vm_refl. Qed.
Lemma D_99918 : decode_any W_99918 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_9991c : bv 32 := 0x032d8533.
Lemma F_9991c : fetch_word Ubsan.M.loaded_segments (0x9991c : word) = Some W_9991c.
Proof. vm_refl. Qed.
Lemma D_9991c : decode_any W_9991c = Some (Mul M_MUL 10 27 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_99920 : bv 32 := 0x032d85bb.
Lemma F_99920 : fetch_word Ubsan.M.loaded_segments (0x99920 : word) = Some W_99920.
Proof. vm_refl. Qed.
Lemma D_99920 : decode_any W_99920 = Some (Mul32 M_MUL 11 27 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_99924 : bv 32 := 0x06a59a63.
Lemma F_99924 : fetch_word Ubsan.M.loaded_segments (0x99924 : word) = Some W_99924.
Proof. vm_refl. Qed.
Lemma D_99924 : decode_any W_99924 = Some (Branch BC_NE 11 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_99928 : bv 32 := 0x0005051b.
Lemma F_99928 : fetch_word Ubsan.M.loaded_segments (0x99928 : word) = Some W_99928.
Proof. vm_refl. Qed.
Lemma D_99928 : decode_any W_99928 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9992c : bv 32 := 0x00251b13.
Lemma F_9992c : fetch_word Ubsan.M.loaded_segments (0x9992c : word) = Some W_9992c.
Proof. vm_refl. Qed.
Lemma D_9992c : decode_any W_9992c = Some (ShiftImm ALU_SLL 22 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_99930 : bv 32 := 0x01648b33.
Lemma F_99930 : fetch_word Ubsan.M.loaded_segments (0x99930 : word) = Some W_99930.
Proof. vm_refl. Qed.
Lemma D_99930 : decode_any W_99930 = Some (Op ALU_ADD 22 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_99934 : bv 32 := 0x001b3593.
Lemma F_99934 : fetch_word Ubsan.M.loaded_segments (0x99934 : word) = Some W_99934.
Proof. vm_refl. Qed.
Lemma D_99934 : decode_any W_99934 = Some (OpImm ALU_SLTU 11 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_99938 : bv 32 := 0x06bd0063.
Lemma F_99938 : fetch_word Ubsan.M.loaded_segments (0x99938 : word) = Some W_99938.
Proof. vm_refl. Qed.
Lemma D_99938 : decode_any W_99938 = Some (Branch BC_EQ 26 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9993c : bv 32 := 0x009b35b3.
Lemma F_9993c : fetch_word Ubsan.M.loaded_segments (0x9993c : word) = Some W_9993c.
Proof. vm_refl. Qed.
Lemma D_9993c : decode_any W_9993c = Some (Op ALU_SLTU 11 22 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_99940 : bv 32 := 0x00052513.
Lemma F_99940 : fetch_word Ubsan.M.loaded_segments (0x99940 : word) = Some W_99940.
Proof. vm_refl. Qed.
Lemma D_99940 : decode_any W_99940 = Some (OpImm ALU_SLT 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99944 : bv 32 := 0x00a5c533.
Lemma F_99944 : fetch_word Ubsan.M.loaded_segments (0x99944 : word) = Some W_99944.
Proof. vm_refl. Qed.
Lemma D_99944 : decode_any W_99944 = Some (Op ALU_XOR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_99948 : bv 32 := 0x00154513.
Lemma F_99948 : fetch_word Ubsan.M.loaded_segments (0x99948 : word) = Some W_99948.
Proof. vm_refl. Qed.
Lemma D_99948 : decode_any W_99948 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9994c : bv 32 := 0x04050663.
Lemma F_9994c : fetch_word Ubsan.M.loaded_segments (0x9994c : word) = Some W_9994c.
Proof. vm_refl. Qed.
Lemma D_9994c : decode_any W_9994c = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_99950 : bv 32 := 0x003af513.
Lemma F_99950 : fetch_word Ubsan.M.loaded_segments (0x99950 : word) = Some W_99950.
Proof. vm_refl. Qed.
Lemma D_99950 : decode_any W_99950 = Some (OpImm ALU_AND 10 21 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_99954 : bv 32 := 0x00ac6533.
Lemma F_99954 : fetch_word Ubsan.M.loaded_segments (0x99954 : word) = Some W_99954.
Proof. vm_refl. Qed.
Lemma D_99954 : decode_any W_99954 = Some (Op ALU_OR 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_99958 : bv 32 := 0x04051063.
Lemma F_99958 : fetch_word Ubsan.M.loaded_segments (0x99958 : word) = Some W_99958.
Proof. vm_refl. Qed.
Lemma D_99958 : decode_any W_99958 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9995c : bv 32 := 0x00098513.
Lemma F_9995c : fetch_word Ubsan.M.loaded_segments (0x9995c : word) = Some W_9995c.
Proof. vm_refl. Qed.
Lemma D_9995c : decode_any W_9995c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99960 : bv 32 := 0x000a8593.
Lemma F_99960 : fetch_word Ubsan.M.loaded_segments (0x99960 : word) = Some W_99960.
Proof. vm_refl. Qed.
Lemma D_99960 : decode_any W_99960 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99964 : bv 32 := 0x000a0613.
Lemma F_99964 : fetch_word Ubsan.M.loaded_segments (0x99964 : word) = Some W_99964.
Proof. vm_refl. Qed.
Lemma D_99964 : decode_any W_99964 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99968 : bv 32 := 0x7ec840ef.
Lemma F_99968 : fetch_word Ubsan.M.loaded_segments (0x99968 : word) = Some W_99968.
Proof. vm_refl. Qed.
Lemma D_99968 : decode_any W_99968 = Some (Jal 1 542700, 4%Z).
Proof. vm_refl. Qed.

Definition W_9996c : bv 32 := 0x000a8513.
Lemma F_9996c : fetch_word Ubsan.M.loaded_segments (0x9996c : word) = Some W_9996c.
Proof. vm_refl. Qed.
Lemma D_9996c : decode_any W_9996c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99970 : bv 32 := 0x000b0593.
Lemma F_99970 : fetch_word Ubsan.M.loaded_segments (0x99970 : word) = Some W_99970.
Proof. vm_refl. Qed.
Lemma D_99970 : decode_any W_99970 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99974 : bv 32 := 0x000a0613.
Lemma F_99974 : fetch_word Ubsan.M.loaded_segments (0x99974 : word) = Some W_99974.
Proof. vm_refl. Qed.
Lemma D_99974 : decode_any W_99974 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99978 : bv 32 := 0x7dc840ef.
Lemma F_99978 : fetch_word Ubsan.M.loaded_segments (0x99978 : word) = Some W_99978.
Proof. vm_refl. Qed.
Lemma D_99978 : decode_any W_99978 = Some (Jal 1 542684, 4%Z).
Proof. vm_refl. Qed.

Definition W_9997c : bv 32 := 0x000b0513.
Lemma F_9997c : fetch_word Ubsan.M.loaded_segments (0x9997c : word) = Some W_9997c.
Proof. vm_refl. Qed.
Lemma D_9997c : decode_any W_9997c = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99980 : bv 32 := 0x00098593.
Lemma F_99980 : fetch_word Ubsan.M.loaded_segments (0x99980 : word) = Some W_99980.
Proof. vm_refl. Qed.
Lemma D_99980 : decode_any W_99980 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99984 : bv 32 := 0x000a0613.
Lemma F_99984 : fetch_word Ubsan.M.loaded_segments (0x99984 : word) = Some W_99984.
Proof. vm_refl. Qed.
Lemma D_99984 : decode_any W_99984 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99988 : bv 32 := 0x7cc840ef.
Lemma F_99988 : fetch_word Ubsan.M.loaded_segments (0x99988 : word) = Some W_99988.
Proof. vm_refl. Qed.
Lemma D_99988 : decode_any W_99988 = Some (Jal 1 542668, 4%Z).
Proof. vm_refl. Qed.

Definition W_9998c : bv 32 := 0xfffd851b.
Lemma F_9998c : fetch_word Ubsan.M.loaded_segments (0x9998c : word) = Some W_9998c.
Proof. vm_refl. Qed.
Lemma D_9998c : decode_any W_9998c = Some (OpImm32 10 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_99990 : bv 32 := 0x001b8b9b.
Lemma F_99990 : fetch_word Ubsan.M.loaded_segments (0x99990 : word) = Some W_99990.
Proof. vm_refl. Qed.
Lemma D_99990 : decode_any W_99990 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_99994 : bv 32 := 0xf5b546e3.
Lemma F_99994 : fetch_word Ubsan.M.loaded_segments (0x99994 : word) = Some W_99994.
Proof. vm_refl. Qed.
Lemma D_99994 : decode_any W_99994 = Some (Branch BC_LT 10 27 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_9999c : bv 32 := 0x0008d517.
Lemma F_9999c : fetch_word Ubsan.M.loaded_segments (0x9999c : word) = Some W_9999c.
Proof. vm_refl. Qed.
Lemma D_9999c : decode_any W_9999c = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_999a0 : bv 32 := 0x0d453503.
Lemma F_999a0 : fetch_word Ubsan.M.loaded_segments (0x999a0 : word) = Some W_999a0.
Proof. vm_refl. Qed.
Lemma D_999a0 : decode_any W_999a0 = Some (Load SZ8 true 10 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_999a4 : bv 32 := 0x00052503.
Lemma F_999a4 : fetch_word Ubsan.M.loaded_segments (0x999a4 : word) = Some W_999a4.
Proof. vm_refl. Qed.
Lemma D_999a4 : decode_any W_999a4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_999a8 : bv 32 := 0x00500593.
Lemma F_999a8 : fetch_word Ubsan.M.loaded_segments (0x999a8 : word) = Some W_999a8.
Proof. vm_refl. Qed.
Lemma D_999a8 : decode_any W_999a8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_999ac : bv 32 := 0x0ea5c863.
Lemma F_999ac : fetch_word Ubsan.M.loaded_segments (0x999ac : word) = Some W_999ac.
Proof. vm_refl. Qed.
Lemma D_999ac : decode_any W_999ac = Some (Branch BC_LT 11 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_999b0 : bv 32 := 0xfff77517.
Lemma F_999b0 : fetch_word Ubsan.M.loaded_segments (0x999b0 : word) = Some W_999b0.
Proof. vm_refl. Qed.
Lemma D_999b0 : decode_any W_999b0 = Some (Auipc 10 1048439, 4%Z).
Proof. vm_refl. Qed.

Definition W_999b4 : bv 32 := 0xfff7b597.
Lemma F_999b4 : fetch_word Ubsan.M.loaded_segments (0x999b4 : word) = Some W_999b4.
Proof. vm_refl. Qed.
Lemma D_999b4 : decode_any W_999b4 = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_999b8 : bv 32 := 0x9a550513.
Lemma F_999b8 : fetch_word Ubsan.M.loaded_segments (0x999b8 : word) = Some W_999b8.
Proof. vm_refl. Qed.
Lemma D_999b8 : decode_any W_999b8 = Some (OpImm ALU_ADD 10 10 2469, 4%Z).
Proof. vm_refl. Qed.

Definition W_999bc : bv 32 := 0x1d858593.
Lemma F_999bc : fetch_word Ubsan.M.loaded_segments (0x999bc : word) = Some W_999bc.
Proof. vm_refl. Qed.
Lemma D_999bc : decode_any W_999bc = Some (OpImm ALU_ADD 11 11 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_999c0 : bv 32 := 0x00000613.
Lemma F_999c0 : fetch_word Ubsan.M.loaded_segments (0x999c0 : word) = Some W_999c0.
Proof. vm_refl. Qed.
Lemma D_999c0 : decode_any W_999c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_999c4 : bv 32 := 0x06813083.
Lemma F_999c4 : fetch_word Ubsan.M.loaded_segments (0x999c4 : word) = Some W_999c4.
Proof. vm_refl. Qed.
Lemma D_999c4 : decode_any W_999c4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_999c8 : bv 32 := 0x06013403.
Lemma F_999c8 : fetch_word Ubsan.M.loaded_segments (0x999c8 : word) = Some W_999c8.
Proof. vm_refl. Qed.
Lemma D_999c8 : decode_any W_999c8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_999cc : bv 32 := 0x05813483.
Lemma F_999cc : fetch_word Ubsan.M.loaded_segments (0x999cc : word) = Some W_999cc.
Proof. vm_refl. Qed.
Lemma D_999cc : decode_any W_999cc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_999d0 : bv 32 := 0x05013903.
Lemma F_999d0 : fetch_word Ubsan.M.loaded_segments (0x999d0 : word) = Some W_999d0.
Proof. vm_refl. Qed.
Lemma D_999d0 : decode_any W_999d0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_999d4 : bv 32 := 0x04813983.
Lemma F_999d4 : fetch_word Ubsan.M.loaded_segments (0x999d4 : word) = Some W_999d4.
Proof. vm_refl. Qed.
Lemma D_999d4 : decode_any W_999d4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_999d8 : bv 32 := 0x04013a03.
Lemma F_999d8 : fetch_word Ubsan.M.loaded_segments (0x999d8 : word) = Some W_999d8.
Proof. vm_refl. Qed.
Lemma D_999d8 : decode_any W_999d8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_999dc : bv 32 := 0x03813a83.
Lemma F_999dc : fetch_word Ubsan.M.loaded_segments (0x999dc : word) = Some W_999dc.
Proof. vm_refl. Qed.
Lemma D_999dc : decode_any W_999dc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_999e0 : bv 32 := 0x03013b03.
Lemma F_999e0 : fetch_word Ubsan.M.loaded_segments (0x999e0 : word) = Some W_999e0.
Proof. vm_refl. Qed.
Lemma D_999e0 : decode_any W_999e0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_999e4 : bv 32 := 0x02813b83.
Lemma F_999e4 : fetch_word Ubsan.M.loaded_segments (0x999e4 : word) = Some W_999e4.
Proof. vm_refl. Qed.
Lemma D_999e4 : decode_any W_999e4 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_999e8 : bv 32 := 0x02013c03.
Lemma F_999e8 : fetch_word Ubsan.M.loaded_segments (0x999e8 : word) = Some W_999e8.
Proof. vm_refl. Qed.
Lemma D_999e8 : decode_any W_999e8 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_999ec : bv 32 := 0x01813c83.
Lemma F_999ec : fetch_word Ubsan.M.loaded_segments (0x999ec : word) = Some W_999ec.
Proof. vm_refl. Qed.
Lemma D_999ec : decode_any W_999ec = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_999f0 : bv 32 := 0x01013d03.
Lemma F_999f0 : fetch_word Ubsan.M.loaded_segments (0x999f0 : word) = Some W_999f0.
Proof. vm_refl. Qed.
Lemma D_999f0 : decode_any W_999f0 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_999f4 : bv 32 := 0x00813d83.
Lemma F_999f4 : fetch_word Ubsan.M.loaded_segments (0x999f4 : word) = Some W_999f4.
Proof. vm_refl. Qed.
Lemma D_999f4 : decode_any W_999f4 = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_999f8 : bv 32 := 0x07010113.
Lemma F_999f8 : fetch_word Ubsan.M.loaded_segments (0x999f8 : word) = Some W_999f8.
Proof. vm_refl. Qed.
Lemma D_999f8 : decode_any W_999f8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_999fc : bv 32 := 0xd45c906f.
Lemma F_999fc : fetch_word Ubsan.M.loaded_segments (0x999fc : word) = Some W_999fc.
Proof. vm_refl. Qed.
Lemma D_999fc : decode_any W_999fc = Some (Jal 0 1875268, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a00 : bv 32 := 0x00098513.
Lemma F_99a00 : fetch_word Ubsan.M.loaded_segments (0x99a00 : word) = Some W_99a00.
Proof. vm_refl. Qed.
Lemma D_99a00 : decode_any W_99a00 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a04 : bv 32 := 0x615740ef.
Lemma F_99a04 : fetch_word Ubsan.M.loaded_segments (0x99a04 : word) = Some W_99a04.
Proof. vm_refl. Qed.
Lemma D_99a04 : decode_any W_99a04 = Some (Jal 1 478740, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a08 : bv 32 := 0x05c0006f.
Lemma F_99a08 : fetch_word Ubsan.M.loaded_segments (0x99a08 : word) = Some W_99a08.
Proof. vm_refl. Qed.
Lemma D_99a08 : decode_any W_99a08 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a0c : bv 32 := 0x0008d517.
Lemma F_99a0c : fetch_word Ubsan.M.loaded_segments (0x99a0c : word) = Some W_99a0c.
Proof. vm_refl. Qed.
Lemma D_99a0c : decode_any W_99a0c = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a10 : bv 32 := 0x06453503.
Lemma F_99a10 : fetch_word Ubsan.M.loaded_segments (0x99a10 : word) = Some W_99a10.
Proof. vm_refl. Qed.
Lemma D_99a10 : decode_any W_99a10 = Some (Load SZ8 true 10 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a14 : bv 32 := 0x00052503.
Lemma F_99a14 : fetch_word Ubsan.M.loaded_segments (0x99a14 : word) = Some W_99a14.
Proof. vm_refl. Qed.
Lemma D_99a14 : decode_any W_99a14 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a18 : bv 32 := 0x00500593.
Lemma F_99a18 : fetch_word Ubsan.M.loaded_segments (0x99a18 : word) = Some W_99a18.
Proof. vm_refl. Qed.
Lemma D_99a18 : decode_any W_99a18 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a1c : bv 32 := 0x08a5c063.
Lemma F_99a1c : fetch_word Ubsan.M.loaded_segments (0x99a1c : word) = Some W_99a1c.
Proof. vm_refl. Qed.
Lemma D_99a1c : decode_any W_99a1c = Some (Branch BC_LT 11 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a20 : bv 32 := 0xfff79517.
Lemma F_99a20 : fetch_word Ubsan.M.loaded_segments (0x99a20 : word) = Some W_99a20.
Proof. vm_refl. Qed.
Lemma D_99a20 : decode_any W_99a20 = Some (Auipc 10 1048441, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a24 : bv 32 := 0xfff7b597.
Lemma F_99a24 : fetch_word Ubsan.M.loaded_segments (0x99a24 : word) = Some W_99a24.
Proof. vm_refl. Qed.
Lemma D_99a24 : decode_any W_99a24 = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a28 : bv 32 := 0xcba50513.
Lemma F_99a28 : fetch_word Ubsan.M.loaded_segments (0x99a28 : word) = Some W_99a28.
Proof. vm_refl. Qed.
Lemma D_99a28 : decode_any W_99a28 = Some (OpImm ALU_ADD 10 10 3258, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a2c : bv 32 := 0x16858593.
Lemma F_99a2c : fetch_word Ubsan.M.loaded_segments (0x99a2c : word) = Some W_99a2c.
Proof. vm_refl. Qed.
Lemma D_99a2c : decode_any W_99a2c = Some (OpImm ALU_ADD 11 11 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a30 : bv 32 := 0x0600006f.
Lemma F_99a30 : fetch_word Ubsan.M.loaded_segments (0x99a30 : word) = Some W_99a30.
Proof. vm_refl. Qed.
Lemma D_99a30 : decode_any W_99a30 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a34 : bv 32 := 0x0008d517.
Lemma F_99a34 : fetch_word Ubsan.M.loaded_segments (0x99a34 : word) = Some W_99a34.
Proof. vm_refl. Qed.
Lemma D_99a34 : decode_any W_99a34 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a38 : bv 32 := 0x03c53503.
Lemma F_99a38 : fetch_word Ubsan.M.loaded_segments (0x99a38 : word) = Some W_99a38.
Proof. vm_refl. Qed.
Lemma D_99a38 : decode_any W_99a38 = Some (Load SZ8 true 10 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a3c : bv 32 := 0x00052503.
Lemma F_99a3c : fetch_word Ubsan.M.loaded_segments (0x99a3c : word) = Some W_99a3c.
Proof. vm_refl. Qed.
Lemma D_99a3c : decode_any W_99a3c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a40 : bv 32 := 0x00500593.
Lemma F_99a40 : fetch_word Ubsan.M.loaded_segments (0x99a40 : word) = Some W_99a40.
Proof. vm_refl. Qed.
Lemma D_99a40 : decode_any W_99a40 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a44 : bv 32 := 0x02a5c063.
Lemma F_99a44 : fetch_word Ubsan.M.loaded_segments (0x99a44 : word) = Some W_99a44.
Proof. vm_refl. Qed.
Lemma D_99a44 : decode_any W_99a44 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a48 : bv 32 := 0xfff7c517.
Lemma F_99a48 : fetch_word Ubsan.M.loaded_segments (0x99a48 : word) = Some W_99a48.
Proof. vm_refl. Qed.
Lemma D_99a48 : decode_any W_99a48 = Some (Auipc 10 1048444, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a4c : bv 32 := 0xfff7b597.
Lemma F_99a4c : fetch_word Ubsan.M.loaded_segments (0x99a4c : word) = Some W_99a4c.
Proof. vm_refl. Qed.
Lemma D_99a4c : decode_any W_99a4c = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a50 : bv 32 := 0x1d850513.
Lemma F_99a50 : fetch_word Ubsan.M.loaded_segments (0x99a50 : word) = Some W_99a50.
Proof. vm_refl. Qed.
Lemma D_99a50 : decode_any W_99a50 = Some (OpImm ALU_ADD 10 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a54 : bv 32 := 0x14058593.
Lemma F_99a54 : fetch_word Ubsan.M.loaded_segments (0x99a54 : word) = Some W_99a54.
Proof. vm_refl. Qed.
Lemma D_99a54 : decode_any W_99a54 = Some (OpImm ALU_ADD 11 11 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a58 : bv 32 := 0x00040613.
Lemma F_99a58 : fetch_word Ubsan.M.loaded_segments (0x99a58 : word) = Some W_99a58.
Proof. vm_refl. Qed.
Lemma D_99a58 : decode_any W_99a58 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a5c : bv 32 := 0xce5c90ef.
Lemma F_99a5c : fetch_word Ubsan.M.loaded_segments (0x99a5c : word) = Some W_99a5c.
Proof. vm_refl. Qed.
Lemma D_99a5c : decode_any W_99a5c = Some (Jal 1 1875172, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a60 : bv 32 := 0x0400006f.
Lemma F_99a60 : fetch_word Ubsan.M.loaded_segments (0x99a60 : word) = Some W_99a60.
Proof. vm_refl. Qed.
Lemma D_99a60 : decode_any W_99a60 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a64 : bv 32 := 0x00040513.
Lemma F_99a64 : fetch_word Ubsan.M.loaded_segments (0x99a64 : word) = Some W_99a64.
Proof. vm_refl. Qed.
Lemma D_99a64 : decode_any W_99a64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a68 : bv 32 := 0x0380006f.
Lemma F_99a68 : fetch_word Ubsan.M.loaded_segments (0x99a68 : word) = Some W_99a68.
Proof. vm_refl. Qed.
Lemma D_99a68 : decode_any W_99a68 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a6c : bv 32 := 0x0008d517.
Lemma F_99a6c : fetch_word Ubsan.M.loaded_segments (0x99a6c : word) = Some W_99a6c.
Proof. vm_refl. Qed.
Lemma D_99a6c : decode_any W_99a6c = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a70 : bv 32 := 0x00453503.
Lemma F_99a70 : fetch_word Ubsan.M.loaded_segments (0x99a70 : word) = Some W_99a70.
Proof. vm_refl. Qed.
Lemma D_99a70 : decode_any W_99a70 = Some (Load SZ8 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a74 : bv 32 := 0x00052503.
Lemma F_99a74 : fetch_word Ubsan.M.loaded_segments (0x99a74 : word) = Some W_99a74.
Proof. vm_refl. Qed.
Lemma D_99a74 : decode_any W_99a74 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a78 : bv 32 := 0x00500593.
Lemma F_99a78 : fetch_word Ubsan.M.loaded_segments (0x99a78 : word) = Some W_99a78.
Proof. vm_refl. Qed.
Lemma D_99a78 : decode_any W_99a78 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a7c : bv 32 := 0x02a5c063.
Lemma F_99a7c : fetch_word Ubsan.M.loaded_segments (0x99a7c : word) = Some W_99a7c.
Proof. vm_refl. Qed.
Lemma D_99a7c : decode_any W_99a7c = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a80 : bv 32 := 0xfff7a517.
Lemma F_99a80 : fetch_word Ubsan.M.loaded_segments (0x99a80 : word) = Some W_99a80.
Proof. vm_refl. Qed.
Lemma D_99a80 : decode_any W_99a80 = Some (Auipc 10 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a84 : bv 32 := 0xfff7b597.
Lemma F_99a84 : fetch_word Ubsan.M.loaded_segments (0x99a84 : word) = Some W_99a84.
Proof. vm_refl. Qed.
Lemma D_99a84 : decode_any W_99a84 = Some (Auipc 11 1048443, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a88 : bv 32 := 0xb7550513.
Lemma F_99a88 : fetch_word Ubsan.M.loaded_segments (0x99a88 : word) = Some W_99a88.
Proof. vm_refl. Qed.
Lemma D_99a88 : decode_any W_99a88 = Some (OpImm ALU_ADD 10 10 2933, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a8c : bv 32 := 0x10858593.
Lemma F_99a8c : fetch_word Ubsan.M.loaded_segments (0x99a8c : word) = Some W_99a8c.
Proof. vm_refl. Qed.
Lemma D_99a8c : decode_any W_99a8c = Some (OpImm ALU_ADD 11 11 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a90 : bv 32 := 0x00000613.
Lemma F_99a90 : fetch_word Ubsan.M.loaded_segments (0x99a90 : word) = Some W_99a90.
Proof. vm_refl. Qed.
Lemma D_99a90 : decode_any W_99a90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a94 : bv 32 := 0xcadc90ef.
Lemma F_99a94 : fetch_word Ubsan.M.loaded_segments (0x99a94 : word) = Some W_99a94.
Proof. vm_refl. Qed.
Lemma D_99a94 : decode_any W_99a94 = Some (Jal 1 1875116, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a98 : bv 32 := 0x0080006f.
Lemma F_99a98 : fetch_word Ubsan.M.loaded_segments (0x99a98 : word) = Some W_99a98.
Proof. vm_refl. Qed.
Lemma D_99a98 : decode_any W_99a98 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_99a9c : bv 32 := 0x00000513.
Lemma F_99a9c : fetch_word Ubsan.M.loaded_segments (0x99a9c : word) = Some W_99a9c.
Proof. vm_refl. Qed.
Lemma D_99a9c : decode_any W_99a9c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_99aa0 : bv 32 := 0x06813083.
Lemma F_99aa0 : fetch_word Ubsan.M.loaded_segments (0x99aa0 : word) = Some W_99aa0.
Proof. vm_refl. Qed.
Lemma D_99aa0 : decode_any W_99aa0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_99aa4 : bv 32 := 0x06013403.
Lemma F_99aa4 : fetch_word Ubsan.M.loaded_segments (0x99aa4 : word) = Some W_99aa4.
Proof. vm_refl. Qed.
Lemma D_99aa4 : decode_any W_99aa4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_99aa8 : bv 32 := 0x05813483.
Lemma F_99aa8 : fetch_word Ubsan.M.loaded_segments (0x99aa8 : word) = Some W_99aa8.
Proof. vm_refl. Qed.
Lemma D_99aa8 : decode_any W_99aa8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_99aac : bv 32 := 0x05013903.
Lemma F_99aac : fetch_word Ubsan.M.loaded_segments (0x99aac : word) = Some W_99aac.
Proof. vm_refl. Qed.
Lemma D_99aac : decode_any W_99aac = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ab0 : bv 32 := 0x04813983.
Lemma F_99ab0 : fetch_word Ubsan.M.loaded_segments (0x99ab0 : word) = Some W_99ab0.
Proof. vm_refl. Qed.
Lemma D_99ab0 : decode_any W_99ab0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ab4 : bv 32 := 0x04013a03.
Lemma F_99ab4 : fetch_word Ubsan.M.loaded_segments (0x99ab4 : word) = Some W_99ab4.
Proof. vm_refl. Qed.
Lemma D_99ab4 : decode_any W_99ab4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ab8 : bv 32 := 0x03813a83.
Lemma F_99ab8 : fetch_word Ubsan.M.loaded_segments (0x99ab8 : word) = Some W_99ab8.
Proof. vm_refl. Qed.
Lemma D_99ab8 : decode_any W_99ab8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_99abc : bv 32 := 0x03013b03.
Lemma F_99abc : fetch_word Ubsan.M.loaded_segments (0x99abc : word) = Some W_99abc.
Proof. vm_refl. Qed.
Lemma D_99abc : decode_any W_99abc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ac0 : bv 32 := 0x02813b83.
Lemma F_99ac0 : fetch_word Ubsan.M.loaded_segments (0x99ac0 : word) = Some W_99ac0.
Proof. vm_refl. Qed.
Lemma D_99ac0 : decode_any W_99ac0 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ac4 : bv 32 := 0x02013c03.
Lemma F_99ac4 : fetch_word Ubsan.M.loaded_segments (0x99ac4 : word) = Some W_99ac4.
Proof. vm_refl. Qed.
Lemma D_99ac4 : decode_any W_99ac4 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ac8 : bv 32 := 0x01813c83.
Lemma F_99ac8 : fetch_word Ubsan.M.loaded_segments (0x99ac8 : word) = Some W_99ac8.
Proof. vm_refl. Qed.
Lemma D_99ac8 : decode_any W_99ac8 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_99acc : bv 32 := 0x01013d03.
Lemma F_99acc : fetch_word Ubsan.M.loaded_segments (0x99acc : word) = Some W_99acc.
Proof. vm_refl. Qed.
Lemma D_99acc : decode_any W_99acc = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ad0 : bv 32 := 0x00813d83.
Lemma F_99ad0 : fetch_word Ubsan.M.loaded_segments (0x99ad0 : word) = Some W_99ad0.
Proof. vm_refl. Qed.
Lemma D_99ad0 : decode_any W_99ad0 = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ad4 : bv 32 := 0x07010113.
Lemma F_99ad4 : fetch_word Ubsan.M.loaded_segments (0x99ad4 : word) = Some W_99ad4.
Proof. vm_refl. Qed.
Lemma D_99ad4 : decode_any W_99ad4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_99ad8 : bv 32 := 0x00008067.
Lemma F_99ad8 : fetch_word Ubsan.M.loaded_segments (0x99ad8 : word) = Some W_99ad8.
Proof. vm_refl. Qed.
Lemma D_99ad8 : decode_any W_99ad8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
