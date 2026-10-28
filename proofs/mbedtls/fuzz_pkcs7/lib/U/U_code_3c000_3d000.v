(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3c000 : bv 32 := 0xff010113.
Lemma F_3c000 : fetch_word Ubsan.M.loaded_segments (0x3f74c : word) = Some W_3c000.
Proof. vm_refl. Qed.
Lemma D_3c000 : decode_any W_3c000 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c004 : bv 32 := 0x00113423.
Lemma F_3c004 : fetch_word Ubsan.M.loaded_segments (0x3f750 : word) = Some W_3c004.
Proof. vm_refl. Qed.
Lemma D_3c004 : decode_any W_3c004 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c008 : bv 32 := 0x00813023.
Lemma F_3c008 : fetch_word Ubsan.M.loaded_segments (0x3f754 : word) = Some W_3c008.
Proof. vm_refl. Qed.
Lemma D_3c008 : decode_any W_3c008 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c00c : bv 32 := 0x00000593.
Lemma F_3c00c : fetch_word Ubsan.M.loaded_segments (0x3f758 : word) = Some W_3c00c.
Proof. vm_refl. Qed.
Lemma D_3c00c : decode_any W_3c00c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c010 : bv 32 := 0x00020613.
Lemma F_3c010 : fetch_word Ubsan.M.loaded_segments (0x3f75c : word) = Some W_3c010.
Proof. vm_refl. Qed.
Lemma D_3c010 : decode_any W_3c010 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c014 : bv 32 := 0xf5862603.
Lemma F_3c014 : fetch_word Ubsan.M.loaded_segments (0x3f760 : word) = Some W_3c014.
Proof. vm_refl. Qed.
Lemma D_3c014 : decode_any W_3c014 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c018 : bv 32 := 0x0003e697.
Lemma F_3c018 : fetch_word Ubsan.M.loaded_segments (0x3f764 : word) = Some W_3c018.
Proof. vm_refl. Qed.
Lemma D_3c018 : decode_any W_3c018 = Some (Auipc 13 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c01c : bv 32 := 0xbc468693.
Lemma F_3c01c : fetch_word Ubsan.M.loaded_segments (0x3f768 : word) = Some W_3c01c.
Proof. vm_refl. Qed.
Lemma D_3c01c : decode_any W_3c01c = Some (OpImm ALU_ADD 13 13 3012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c020 : bv 32 := 0x1606a72f.
Lemma F_3c020 : fetch_word Ubsan.M.loaded_segments (0x3f76c : word) = Some W_3c020.
Proof. vm_refl. Qed.
Lemma D_3c020 : decode_any W_3c020 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c024 : bv 32 := 0x00b71663.
Lemma F_3c024 : fetch_word Ubsan.M.loaded_segments (0x3f770 : word) = Some W_3c024.
Proof. vm_refl. Qed.
Lemma D_3c024 : decode_any W_3c024 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c028 : bv 32 := 0x1ec6a7af.
Lemma F_3c028 : fetch_word Ubsan.M.loaded_segments (0x3f774 : word) = Some W_3c028.
Proof. vm_refl. Qed.
Lemma D_3c028 : decode_any W_3c028 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c02c : bv 32 := 0xfe079ae3.
Lemma F_3c02c : fetch_word Ubsan.M.loaded_segments (0x3f778 : word) = Some W_3c02c.
Proof. vm_refl. Qed.
Lemma D_3c02c : decode_any W_3c02c = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c030 : bv 32 := 0x0007059b.
Lemma F_3c030 : fetch_word Ubsan.M.loaded_segments (0x3f77c : word) = Some W_3c030.
Proof. vm_refl. Qed.
Lemma D_3c030 : decode_any W_3c030 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c034 : bv 32 := 0x02c58263.
Lemma F_3c034 : fetch_word Ubsan.M.loaded_segments (0x3f780 : word) = Some W_3c034.
Proof. vm_refl. Qed.
Lemma D_3c034 : decode_any W_3c034 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c038 : bv 32 := 0x02058263.
Lemma F_3c038 : fetch_word Ubsan.M.loaded_segments (0x3f784 : word) = Some W_3c038.
Proof. vm_refl. Qed.
Lemma D_3c038 : decode_any W_3c038 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c05c : bv 32 := 0x00050413.
Lemma F_3c05c : fetch_word Ubsan.M.loaded_segments (0x3f7a8 : word) = Some W_3c05c.
Proof. vm_refl. Qed.
Lemma D_3c05c : decode_any W_3c05c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c060 : bv 32 := 0xdbdff0ef.
Lemma F_3c060 : fetch_word Ubsan.M.loaded_segments (0x3f7ac : word) = Some W_3c060.
Proof. vm_refl. Qed.
Lemma D_3c060 : decode_any W_3c060 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c064 : bv 32 := 0xf51ff0ef.
Lemma F_3c064 : fetch_word Ubsan.M.loaded_segments (0x3f7b0 : word) = Some W_3c064.
Proof. vm_refl. Qed.
Lemma D_3c064 : decode_any W_3c064 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c068 : bv 32 := 0x0dc020ef.
Lemma F_3c068 : fetch_word Ubsan.M.loaded_segments (0x3f7b4 : word) = Some W_3c068.
Proof. vm_refl. Qed.
Lemma D_3c068 : decode_any W_3c068 = Some (Jal 1 8412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c06c : bv 32 := 0x00040513.
Lemma F_3c06c : fetch_word Ubsan.M.loaded_segments (0x3f7b8 : word) = Some W_3c06c.
Proof. vm_refl. Qed.
Lemma D_3c06c : decode_any W_3c06c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c070 : bv 32 := 0x004000ef.
Lemma F_3c070 : fetch_word Ubsan.M.loaded_segments (0x3f7bc : word) = Some W_3c070.
Proof. vm_refl. Qed.
Lemma D_3c070 : decode_any W_3c070 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c074 : bv 32 := 0x00050593.
Lemma F_3c074 : fetch_word Ubsan.M.loaded_segments (0x3f7c0 : word) = Some W_3c074.
Proof. vm_refl. Qed.
Lemma D_3c074 : decode_any W_3c074 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c078 : bv 32 := 0x05e00893.
Lemma F_3c078 : fetch_word Ubsan.M.loaded_segments (0x3f7c4 : word) = Some W_3c078.
Proof. vm_refl. Qed.
Lemma D_3c078 : decode_any W_3c078 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c07c : bv 32 := 0x00000073.
Lemma F_3c07c : fetch_word Ubsan.M.loaded_segments (0x3f7c8 : word) = Some W_3c07c.
Proof. vm_refl. Qed.
Lemma E_3c07c : is_ecall W_3c07c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_3c174 : bv 32 := 0xff010113.
Lemma F_3c174 : fetch_word Ubsan.M.loaded_segments (0x3f8c0 : word) = Some W_3c174.
Proof. vm_refl. Qed.
Lemma D_3c174 : decode_any W_3c174 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c178 : bv 32 := 0x00113423.
Lemma F_3c178 : fetch_word Ubsan.M.loaded_segments (0x3f8c4 : word) = Some W_3c178.
Proof. vm_refl. Qed.
Lemma D_3c178 : decode_any W_3c178 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c17c : bv 32 := 0x00050e63.
Lemma F_3c17c : fetch_word Ubsan.M.loaded_segments (0x3f8c8 : word) = Some W_3c17c.
Proof. vm_refl. Qed.
Lemma D_3c17c : decode_any W_3c17c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c180 : bv 32 := 0x00050593.
Lemma F_3c180 : fetch_word Ubsan.M.loaded_segments (0x3f8cc : word) = Some W_3c180.
Proof. vm_refl. Qed.
Lemma D_3c180 : decode_any W_3c180 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c184 : bv 32 := 0x0000c517.
Lemma F_3c184 : fetch_word Ubsan.M.loaded_segments (0x3f8d0 : word) = Some W_3c184.
Proof. vm_refl. Qed.
Lemma D_3c184 : decode_any W_3c184 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c188 : bv 32 := 0x40853503.
Lemma F_3c188 : fetch_word Ubsan.M.loaded_segments (0x3f8d4 : word) = Some W_3c188.
Proof. vm_refl. Qed.
Lemma D_3c188 : decode_any W_3c188 = Some (Load SZ8 true 10 10 1032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c18c : bv 32 := 0x00800613.
Lemma F_3c18c : fetch_word Ubsan.M.loaded_segments (0x3f8d8 : word) = Some W_3c18c.
Proof. vm_refl. Qed.
Lemma D_3c18c : decode_any W_3c18c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c190 : bv 32 := 0x164070ef.
Lemma F_3c190 : fetch_word Ubsan.M.loaded_segments (0x3f8dc : word) = Some W_3c190.
Proof. vm_refl. Qed.
Lemma D_3c190 : decode_any W_3c190 = Some (Jal 1 29028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c194 : bv 32 := 0x01c0006f.
Lemma F_3c194 : fetch_word Ubsan.M.loaded_segments (0x3f8e0 : word) = Some W_3c194.
Proof. vm_refl. Qed.
Lemma D_3c194 : decode_any W_3c194 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1b0 : bv 32 := 0x0000c517.
Lemma F_3c1b0 : fetch_word Ubsan.M.loaded_segments (0x3f8fc : word) = Some W_3c1b0.
Proof. vm_refl. Qed.
Lemma D_3c1b0 : decode_any W_3c1b0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1b4 : bv 32 := 0x3dc53503.
Lemma F_3c1b4 : fetch_word Ubsan.M.loaded_segments (0x3f900 : word) = Some W_3c1b4.
Proof. vm_refl. Qed.
Lemma D_3c1b4 : decode_any W_3c1b4 = Some (Load SZ8 true 10 10 988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1b8 : bv 32 := 0x000500a3.
Lemma F_3c1b8 : fetch_word Ubsan.M.loaded_segments (0x3f904 : word) = Some W_3c1b8.
Proof. vm_refl. Qed.
Lemma D_3c1b8 : decode_any W_3c1b8 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1bc : bv 32 := 0x00053503.
Lemma F_3c1bc : fetch_word Ubsan.M.loaded_segments (0x3f908 : word) = Some W_3c1bc.
Proof. vm_refl. Qed.
Lemma D_3c1bc : decode_any W_3c1bc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1c0 : bv 32 := 0x00020593.
Lemma F_3c1c0 : fetch_word Ubsan.M.loaded_segments (0x3f90c : word) = Some W_3c1c0.
Proof. vm_refl. Qed.
Lemma D_3c1c0 : decode_any W_3c1c0 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1c4 : bv 32 := 0xfea5b823.
Lemma F_3c1c4 : fetch_word Ubsan.M.loaded_segments (0x3f910 : word) = Some W_3c1c4.
Proof. vm_refl. Qed.
Lemma D_3c1c4 : decode_any W_3c1c4 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1c8 : bv 32 := 0x00813083.
Lemma F_3c1c8 : fetch_word Ubsan.M.loaded_segments (0x3f914 : word) = Some W_3c1c8.
Proof. vm_refl. Qed.
Lemma D_3c1c8 : decode_any W_3c1c8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1cc : bv 32 := 0x01010113.
Lemma F_3c1cc : fetch_word Ubsan.M.loaded_segments (0x3f918 : word) = Some W_3c1cc.
Proof. vm_refl. Qed.
Lemma D_3c1cc : decode_any W_3c1cc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1d0 : bv 32 := 0x00008067.
Lemma F_3c1d0 : fetch_word Ubsan.M.loaded_segments (0x3f91c : word) = Some W_3c1d0.
Proof. vm_refl. Qed.
Lemma D_3c1d0 : decode_any W_3c1d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1dc : bv 32 := 0xfffff5b7.
Lemma F_3c1dc : fetch_word Ubsan.M.loaded_segments (0x3f928 : word) = Some W_3c1dc.
Proof. vm_refl. Qed.
Lemma D_3c1dc : decode_any W_3c1dc = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1e0 : bv 32 := 0x0015859b.
Lemma F_3c1e0 : fetch_word Ubsan.M.loaded_segments (0x3f92c : word) = Some W_3c1e0.
Proof. vm_refl. Qed.
Lemma D_3c1e0 : decode_any W_3c1e0 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c1e4 : bv 32 := 0x02b56663.
Lemma F_3c1e4 : fetch_word Ubsan.M.loaded_segments (0x3f930 : word) = Some W_3c1e4.
Proof. vm_refl. Qed.
Lemma D_3c1e4 : decode_any W_3c1e4 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3c210 : bv 32 := 0x00008067.
Lemma F_3c210 : fetch_word Ubsan.M.loaded_segments (0x3f95c : word) = Some W_3c210.
Proof. vm_refl. Qed.
Lemma D_3c210 : decode_any W_3c210 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
