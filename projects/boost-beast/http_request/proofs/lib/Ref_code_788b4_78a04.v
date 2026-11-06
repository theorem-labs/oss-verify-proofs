(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_788b4 : bv 32 := 0x00050213.
Lemma F_788b4 : fetch_word Plain.M.loaded_segments (0x788b4 : word) = Some W_788b4.
Proof. vm_refl. Qed.
Lemma D_788b4 : decode_any W_788b4 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788b8 : bv 32 := 0x00000513.
Lemma F_788b8 : fetch_word Plain.M.loaded_segments (0x788b8 : word) = Some W_788b8.
Proof. vm_refl. Qed.
Lemma D_788b8 : decode_any W_788b8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788bc : bv 32 := 0x00008067.
Lemma F_788bc : fetch_word Plain.M.loaded_segments (0x788bc : word) = Some W_788bc.
Proof. vm_refl. Qed.
Lemma D_788bc : decode_any W_788bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788c0 : bv 32 := 0x0d700893.
Lemma F_788c0 : fetch_word Plain.M.loaded_segments (0x788c0 : word) = Some W_788c0.
Proof. vm_refl. Qed.
Lemma D_788c0 : decode_any W_788c0 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788c4 : bv 32 := 0x00000073.
Lemma F_788c4 : fetch_word Plain.M.loaded_segments (0x788c4 : word) = Some W_788c4.
Proof. vm_refl. Qed.
Lemma D_788c4 : decode_any W_788c4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_788c4 : is_ecall W_788c4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_788c8 : bv 32 := 0x05d00893.
Lemma F_788c8 : fetch_word Plain.M.loaded_segments (0x788c8 : word) = Some W_788c8.
Proof. vm_refl. Qed.
Lemma D_788c8 : decode_any W_788c8 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788cc : bv 32 := 0x00000073.
Lemma F_788cc : fetch_word Plain.M.loaded_segments (0x788cc : word) = Some W_788cc.
Proof. vm_refl. Qed.
Lemma D_788cc : decode_any W_788cc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_788cc : is_ecall W_788cc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_788d0 : bv 32 := 0xff05f593.
Lemma F_788d0 : fetch_word Plain.M.loaded_segments (0x788d0 : word) = Some W_788d0.
Proof. vm_refl. Qed.
Lemma D_788d0 : decode_any W_788d0 = Some (OpImm ALU_AND 11 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788d4 : bv 32 := 0xff058593.
Lemma F_788d4 : fetch_word Plain.M.loaded_segments (0x788d4 : word) = Some W_788d4.
Proof. vm_refl. Qed.
Lemma D_788d4 : decode_any W_788d4 = Some (OpImm ALU_ADD 11 11 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788d8 : bv 32 := 0x00a5b023.
Lemma F_788d8 : fetch_word Plain.M.loaded_segments (0x788d8 : word) = Some W_788d8.
Proof. vm_refl. Qed.
Lemma D_788d8 : decode_any W_788d8 = Some (Store SZ8 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788dc : bv 32 := 0x00d5b423.
Lemma F_788dc : fetch_word Plain.M.loaded_segments (0x788dc : word) = Some W_788dc.
Proof. vm_refl. Qed.
Lemma D_788dc : decode_any W_788dc = Some (Store SZ8 11 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788e0 : bv 32 := 0x00060513.
Lemma F_788e0 : fetch_word Plain.M.loaded_segments (0x788e0 : word) = Some W_788e0.
Proof. vm_refl. Qed.
Lemma D_788e0 : decode_any W_788e0 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788e4 : bv 32 := 0x00070613.
Lemma F_788e4 : fetch_word Plain.M.loaded_segments (0x788e4 : word) = Some W_788e4.
Proof. vm_refl. Qed.
Lemma D_788e4 : decode_any W_788e4 = Some (OpImm ALU_ADD 12 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788e8 : bv 32 := 0x00078693.
Lemma F_788e8 : fetch_word Plain.M.loaded_segments (0x788e8 : word) = Some W_788e8.
Proof. vm_refl. Qed.
Lemma D_788e8 : decode_any W_788e8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788ec : bv 32 := 0x00080713.
Lemma F_788ec : fetch_word Plain.M.loaded_segments (0x788ec : word) = Some W_788ec.
Proof. vm_refl. Qed.
Lemma D_788ec : decode_any W_788ec = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788f0 : bv 32 := 0x0dc00893.
Lemma F_788f0 : fetch_word Plain.M.loaded_segments (0x788f0 : word) = Some W_788f0.
Proof. vm_refl. Qed.
Lemma D_788f0 : decode_any W_788f0 = Some (OpImm ALU_ADD 17 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788f4 : bv 32 := 0x00000073.
Lemma F_788f4 : fetch_word Plain.M.loaded_segments (0x788f4 : word) = Some W_788f4.
Proof. vm_refl. Qed.
Lemma D_788f4 : decode_any W_788f4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_788f4 : is_ecall W_788f4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_788f8 : bv 32 := 0x00050463.
Lemma F_788f8 : fetch_word Plain.M.loaded_segments (0x788f8 : word) = Some W_788f8.
Proof. vm_refl. Qed.
Lemma D_788f8 : decode_any W_788f8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_788fc : bv 32 := 0x00008067.
Lemma F_788fc : fetch_word Plain.M.loaded_segments (0x788fc : word) = Some W_788fc.
Proof. vm_refl. Qed.
Lemma D_788fc : decode_any W_788fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78900 : bv 32 := 0x00013583.
Lemma F_78900 : fetch_word Plain.M.loaded_segments (0x78900 : word) = Some W_78900.
Proof. vm_refl. Qed.
Lemma D_78900 : decode_any W_78900 = Some (Load SZ8 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78904 : bv 32 := 0x00813503.
Lemma F_78904 : fetch_word Plain.M.loaded_segments (0x78904 : word) = Some W_78904.
Proof. vm_refl. Qed.
Lemma D_78904 : decode_any W_78904 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78908 : bv 32 := 0x000580e7.
Lemma F_78908 : fetch_word Plain.M.loaded_segments (0x78908 : word) = Some W_78908.
Proof. vm_refl. Qed.
Lemma D_78908 : decode_any W_78908 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7890c : bv 32 := 0x05d00893.
Lemma F_7890c : fetch_word Plain.M.loaded_segments (0x7890c : word) = Some W_7890c.
Proof. vm_refl. Qed.
Lemma D_7890c : decode_any W_7890c = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78910 : bv 32 := 0x00000073.
Lemma F_78910 : fetch_word Plain.M.loaded_segments (0x78910 : word) = Some W_78910.
Proof. vm_refl. Qed.
Lemma D_78910 : decode_any W_78910 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_78910 : is_ecall W_78910 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_78914 : bv 32 := 0xfe010113.
Lemma F_78914 : fetch_word Plain.M.loaded_segments (0x78914 : word) = Some W_78914.
Proof. vm_refl. Qed.
Lemma D_78914 : decode_any W_78914 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78918 : bv 32 := 0x00113c23.
Lemma F_78918 : fetch_word Plain.M.loaded_segments (0x78918 : word) = Some W_78918.
Proof. vm_refl. Qed.
Lemma D_78918 : decode_any W_78918 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7891c : bv 32 := 0x00813823.
Lemma F_7891c : fetch_word Plain.M.loaded_segments (0x7891c : word) = Some W_7891c.
Proof. vm_refl. Qed.
Lemma D_7891c : decode_any W_7891c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78920 : bv 32 := 0x00913423.
Lemma F_78920 : fetch_word Plain.M.loaded_segments (0x78920 : word) = Some W_78920.
Proof. vm_refl. Qed.
Lemma D_78920 : decode_any W_78920 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78924 : bv 32 := 0x0003b517.
Lemma F_78924 : fetch_word Plain.M.loaded_segments (0x78924 : word) = Some W_78924.
Proof. vm_refl. Qed.
Lemma D_78924 : decode_any W_78924 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78928 : bv 32 := 0x05450413.
Lemma F_78928 : fetch_word Plain.M.loaded_segments (0x78928 : word) = Some W_78928.
Proof. vm_refl. Qed.
Lemma D_78928 : decode_any W_78928 = Some (OpImm ALU_ADD 8 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7892c : bv 32 := 0x00042603.
Lemma F_7892c : fetch_word Plain.M.loaded_segments (0x7892c : word) = Some W_7892c.
Proof. vm_refl. Qed.
Lemma D_7892c : decode_any W_7892c = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78930 : bv 32 := 0x02060063.
Lemma F_78930 : fetch_word Plain.M.loaded_segments (0x78930 : word) = Some W_78930.
Proof. vm_refl. Qed.
Lemma D_78930 : decode_any W_78930 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78934 : bv 32 := 0x00440493.
Lemma F_78934 : fetch_word Plain.M.loaded_segments (0x78934 : word) = Some W_78934.
Proof. vm_refl. Qed.
Lemma D_78934 : decode_any W_78934 = Some (OpImm ALU_ADD 9 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78938 : bv 32 := 0x00100693.
Lemma F_78938 : fetch_word Plain.M.loaded_segments (0x78938 : word) = Some W_78938.
Proof. vm_refl. Qed.
Lemma D_78938 : decode_any W_78938 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7893c : bv 32 := 0x00040513.
Lemma F_7893c : fetch_word Plain.M.loaded_segments (0x7893c : word) = Some W_7893c.
Proof. vm_refl. Qed.
Lemma D_7893c : decode_any W_7893c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78940 : bv 32 := 0x00048593.
Lemma F_78940 : fetch_word Plain.M.loaded_segments (0x78940 : word) = Some W_78940.
Proof. vm_refl. Qed.
Lemma D_78940 : decode_any W_78940 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78944 : bv 32 := 0xfc0fd0ef.
Lemma F_78944 : fetch_word Plain.M.loaded_segments (0x78944 : word) = Some W_78944.
Proof. vm_refl. Qed.
Lemma D_78944 : decode_any W_78944 = Some (Jal 1 2086848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78948 : bv 32 := 0x00042603.
Lemma F_78948 : fetch_word Plain.M.loaded_segments (0x78948 : word) = Some W_78948.
Proof. vm_refl. Qed.
Lemma D_78948 : decode_any W_78948 = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7894c : bv 32 := 0xfe0616e3.
Lemma F_7894c : fetch_word Plain.M.loaded_segments (0x7894c : word) = Some W_7894c.
Proof. vm_refl. Qed.
Lemma D_7894c : decode_any W_7894c = Some (Branch BC_NE 12 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78950 : bv 32 := 0x01813083.
Lemma F_78950 : fetch_word Plain.M.loaded_segments (0x78950 : word) = Some W_78950.
Proof. vm_refl. Qed.
Lemma D_78950 : decode_any W_78950 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78954 : bv 32 := 0x01013403.
Lemma F_78954 : fetch_word Plain.M.loaded_segments (0x78954 : word) = Some W_78954.
Proof. vm_refl. Qed.
Lemma D_78954 : decode_any W_78954 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78958 : bv 32 := 0x00813483.
Lemma F_78958 : fetch_word Plain.M.loaded_segments (0x78958 : word) = Some W_78958.
Proof. vm_refl. Qed.
Lemma D_78958 : decode_any W_78958 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7895c : bv 32 := 0x02010113.
Lemma F_7895c : fetch_word Plain.M.loaded_segments (0x7895c : word) = Some W_7895c.
Proof. vm_refl. Qed.
Lemma D_7895c : decode_any W_7895c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78960 : bv 32 := 0x00008067.
Lemma F_78960 : fetch_word Plain.M.loaded_segments (0x78960 : word) = Some W_78960.
Proof. vm_refl. Qed.
Lemma D_78960 : decode_any W_78960 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78964 : bv 32 := 0x0003b517.
Lemma F_78964 : fetch_word Plain.M.loaded_segments (0x78964 : word) = Some W_78964.
Proof. vm_refl. Qed.
Lemma D_78964 : decode_any W_78964 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78968 : bv 32 := 0x01450513.
Lemma F_78968 : fetch_word Plain.M.loaded_segments (0x78968 : word) = Some W_78968.
Proof. vm_refl. Qed.
Lemma D_78968 : decode_any W_78968 = Some (OpImm ALU_ADD 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7896c : bv 32 := 0x00052583.
Lemma F_7896c : fetch_word Plain.M.loaded_segments (0x7896c : word) = Some W_7896c.
Proof. vm_refl. Qed.
Lemma D_7896c : decode_any W_7896c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78970 : bv 32 := 0x0015861b.
Lemma F_78970 : fetch_word Plain.M.loaded_segments (0x78970 : word) = Some W_78970.
Proof. vm_refl. Qed.
Lemma D_78970 : decode_any W_78970 = Some (OpImm32 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78974 : bv 32 := 0x160526af.
Lemma F_78974 : fetch_word Plain.M.loaded_segments (0x78974 : word) = Some W_78974.
Proof. vm_refl. Qed.
Lemma D_78974 : decode_any W_78974 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78978 : bv 32 := 0x00b69663.
Lemma F_78978 : fetch_word Plain.M.loaded_segments (0x78978 : word) = Some W_78978.
Proof. vm_refl. Qed.
Lemma D_78978 : decode_any W_78978 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7897c : bv 32 := 0x1ec5272f.
Lemma F_7897c : fetch_word Plain.M.loaded_segments (0x7897c : word) = Some W_7897c.
Proof. vm_refl. Qed.
Lemma D_7897c : decode_any W_7897c = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78980 : bv 32 := 0xfe071ae3.
Lemma F_78980 : fetch_word Plain.M.loaded_segments (0x78980 : word) = Some W_78980.
Proof. vm_refl. Qed.
Lemma D_78980 : decode_any W_78980 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78984 : bv 32 := 0x0006869b.
Lemma F_78984 : fetch_word Plain.M.loaded_segments (0x78984 : word) = Some W_78984.
Proof. vm_refl. Qed.
Lemma D_78984 : decode_any W_78984 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78988 : bv 32 := 0xfeb692e3.
Lemma F_78988 : fetch_word Plain.M.loaded_segments (0x78988 : word) = Some W_78988.
Proof. vm_refl. Qed.
Lemma D_78988 : decode_any W_78988 = Some (Branch BC_NE 13 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7898c : bv 32 := 0x00008067.
Lemma F_7898c : fetch_word Plain.M.loaded_segments (0x7898c : word) = Some W_7898c.
Proof. vm_refl. Qed.
Lemma D_7898c : decode_any W_7898c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78990 : bv 32 := 0x0003b517.
Lemma F_78990 : fetch_word Plain.M.loaded_segments (0x78990 : word) = Some W_78990.
Proof. vm_refl. Qed.
Lemma D_78990 : decode_any W_78990 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78994 : bv 32 := 0xfe850513.
Lemma F_78994 : fetch_word Plain.M.loaded_segments (0x78994 : word) = Some W_78994.
Proof. vm_refl. Qed.
Lemma D_78994 : decode_any W_78994 = Some (OpImm ALU_ADD 10 10 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_78998 : bv 32 := 0x00052583.
Lemma F_78998 : fetch_word Plain.M.loaded_segments (0x78998 : word) = Some W_78998.
Proof. vm_refl. Qed.
Lemma D_78998 : decode_any W_78998 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7899c : bv 32 := 0xfff5861b.
Lemma F_7899c : fetch_word Plain.M.loaded_segments (0x7899c : word) = Some W_7899c.
Proof. vm_refl. Qed.
Lemma D_7899c : decode_any W_7899c = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789a0 : bv 32 := 0x160526af.
Lemma F_789a0 : fetch_word Plain.M.loaded_segments (0x789a0 : word) = Some W_789a0.
Proof. vm_refl. Qed.
Lemma D_789a0 : decode_any W_789a0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789a4 : bv 32 := 0x00b69663.
Lemma F_789a4 : fetch_word Plain.M.loaded_segments (0x789a4 : word) = Some W_789a4.
Proof. vm_refl. Qed.
Lemma D_789a4 : decode_any W_789a4 = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789a8 : bv 32 := 0x1ec5272f.
Lemma F_789a8 : fetch_word Plain.M.loaded_segments (0x789a8 : word) = Some W_789a8.
Proof. vm_refl. Qed.
Lemma D_789a8 : decode_any W_789a8 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789ac : bv 32 := 0xfe071ae3.
Lemma F_789ac : fetch_word Plain.M.loaded_segments (0x789ac : word) = Some W_789ac.
Proof. vm_refl. Qed.
Lemma D_789ac : decode_any W_789ac = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789b0 : bv 32 := 0x0006869b.
Lemma F_789b0 : fetch_word Plain.M.loaded_segments (0x789b0 : word) = Some W_789b0.
Proof. vm_refl. Qed.
Lemma D_789b0 : decode_any W_789b0 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789b4 : bv 32 := 0xfeb692e3.
Lemma F_789b4 : fetch_word Plain.M.loaded_segments (0x789b4 : word) = Some W_789b4.
Proof. vm_refl. Qed.
Lemma D_789b4 : decode_any W_789b4 = Some (Branch BC_NE 13 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789b8 : bv 32 := 0x00100613.
Lemma F_789b8 : fetch_word Plain.M.loaded_segments (0x789b8 : word) = Some W_789b8.
Proof. vm_refl. Qed.
Lemma D_789b8 : decode_any W_789b8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789bc : bv 32 := 0x04c59263.
Lemma F_789bc : fetch_word Plain.M.loaded_segments (0x789bc : word) = Some W_789bc.
Proof. vm_refl. Qed.
Lemma D_789bc : decode_any W_789bc = Some (Branch BC_NE 11 12 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789c0 : bv 32 := 0x00452503.
Lemma F_789c0 : fetch_word Plain.M.loaded_segments (0x789c0 : word) = Some W_789c0.
Proof. vm_refl. Qed.
Lemma D_789c0 : decode_any W_789c0 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789c4 : bv 32 := 0x02050e63.
Lemma F_789c4 : fetch_word Plain.M.loaded_segments (0x789c4 : word) = Some W_789c4.
Proof. vm_refl. Qed.
Lemma D_789c4 : decode_any W_789c4 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789c8 : bv 32 := 0x0003b517.
Lemma F_789c8 : fetch_word Plain.M.loaded_segments (0x789c8 : word) = Some W_789c8.
Proof. vm_refl. Qed.
Lemma D_789c8 : decode_any W_789c8 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789cc : bv 32 := 0x80000637.
Lemma F_789cc : fetch_word Plain.M.loaded_segments (0x789cc : word) = Some W_789cc.
Proof. vm_refl. Qed.
Lemma D_789cc : decode_any W_789cc = Some (Lui 12 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789d0 : bv 32 := 0x06200893.
Lemma F_789d0 : fetch_word Plain.M.loaded_segments (0x789d0 : word) = Some W_789d0.
Proof. vm_refl. Qed.
Lemma D_789d0 : decode_any W_789d0 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789d4 : bv 32 := 0xfb050513.
Lemma F_789d4 : fetch_word Plain.M.loaded_segments (0x789d4 : word) = Some W_789d4.
Proof. vm_refl. Qed.
Lemma D_789d4 : decode_any W_789d4 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789d8 : bv 32 := 0xfff6061b.
Lemma F_789d8 : fetch_word Plain.M.loaded_segments (0x789d8 : word) = Some W_789d8.
Proof. vm_refl. Qed.
Lemma D_789d8 : decode_any W_789d8 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789dc : bv 32 := 0x08100593.
Lemma F_789dc : fetch_word Plain.M.loaded_segments (0x789dc : word) = Some W_789dc.
Proof. vm_refl. Qed.
Lemma D_789dc : decode_any W_789dc = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789e0 : bv 32 := 0xfda00693.
Lemma F_789e0 : fetch_word Plain.M.loaded_segments (0x789e0 : word) = Some W_789e0.
Proof. vm_refl. Qed.
Lemma D_789e0 : decode_any W_789e0 = Some (OpImm ALU_ADD 13 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789e4 : bv 32 := 0x00000073.
Lemma F_789e4 : fetch_word Plain.M.loaded_segments (0x789e4 : word) = Some W_789e4.
Proof. vm_refl. Qed.
Lemma D_789e4 : decode_any W_789e4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_789e4 : is_ecall W_789e4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_789e8 : bv 32 := 0x00d51c63.
Lemma F_789e8 : fetch_word Plain.M.loaded_segments (0x789e8 : word) = Some W_789e8.
Proof. vm_refl. Qed.
Lemma D_789e8 : decode_any W_789e8 = Some (Branch BC_NE 10 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789ec : bv 32 := 0x0003b517.
Lemma F_789ec : fetch_word Plain.M.loaded_segments (0x789ec : word) = Some W_789ec.
Proof. vm_refl. Qed.
Lemma D_789ec : decode_any W_789ec = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789f0 : bv 32 := 0xf8c50513.
Lemma F_789f0 : fetch_word Plain.M.loaded_segments (0x789f0 : word) = Some W_789f0.
Proof. vm_refl. Qed.
Lemma D_789f0 : decode_any W_789f0 = Some (OpImm ALU_ADD 10 10 3980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789f4 : bv 32 := 0x06200893.
Lemma F_789f4 : fetch_word Plain.M.loaded_segments (0x789f4 : word) = Some W_789f4.
Proof. vm_refl. Qed.
Lemma D_789f4 : decode_any W_789f4 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789f8 : bv 32 := 0x00100593.
Lemma F_789f8 : fetch_word Plain.M.loaded_segments (0x789f8 : word) = Some W_789f8.
Proof. vm_refl. Qed.
Lemma D_789f8 : decode_any W_789f8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_789fc : bv 32 := 0x00000073.
Lemma F_789fc : fetch_word Plain.M.loaded_segments (0x789fc : word) = Some W_789fc.
Proof. vm_refl. Qed.
Lemma D_789fc : decode_any W_789fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_789fc : is_ecall W_789fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_78a00 : bv 32 := 0x00008067.
Lemma F_78a00 : fetch_word Plain.M.loaded_segments (0x78a00 : word) = Some W_78a00.
Proof. vm_refl. Qed.
Lemma D_78a00 : decode_any W_78a00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
