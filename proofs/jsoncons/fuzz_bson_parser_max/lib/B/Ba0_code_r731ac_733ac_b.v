(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8d0b4 : bv 32 := 0xfd010113.
Lemma F_8d0b4 : fetch_word AsanUbsan.M.loaded_segments (0x8d4cc : word) = Some W_8d0b4.
Proof. vm_refl. Qed.
Lemma D_8d0b4 : decode_any W_8d0b4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0b8 : bv 32 := 0x02113423.
Lemma F_8d0b8 : fetch_word AsanUbsan.M.loaded_segments (0x8d4d0 : word) = Some W_8d0b8.
Proof. vm_refl. Qed.
Lemma D_8d0b8 : decode_any W_8d0b8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0bc : bv 32 := 0x02813023.
Lemma F_8d0bc : fetch_word AsanUbsan.M.loaded_segments (0x8d4d4 : word) = Some W_8d0bc.
Proof. vm_refl. Qed.
Lemma D_8d0bc : decode_any W_8d0bc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0c0 : bv 32 := 0x00913c23.
Lemma F_8d0c0 : fetch_word AsanUbsan.M.loaded_segments (0x8d4d8 : word) = Some W_8d0c0.
Proof. vm_refl. Qed.
Lemma D_8d0c0 : decode_any W_8d0c0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0c4 : bv 32 := 0x01213823.
Lemma F_8d0c4 : fetch_word AsanUbsan.M.loaded_segments (0x8d4dc : word) = Some W_8d0c4.
Proof. vm_refl. Qed.
Lemma D_8d0c4 : decode_any W_8d0c4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0c8 : bv 32 := 0x02050e63.
Lemma F_8d0c8 : fetch_word AsanUbsan.M.loaded_segments (0x8d4e0 : word) = Some W_8d0c8.
Proof. vm_refl. Qed.
Lemma D_8d0c8 : decode_any W_8d0c8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0cc : bv 32 := 0x00058413.
Lemma F_8d0cc : fetch_word AsanUbsan.M.loaded_segments (0x8d4e4 : word) = Some W_8d0cc.
Proof. vm_refl. Qed.
Lemma D_8d0cc : decode_any W_8d0cc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0d0 : bv 32 := 0x02058a63.
Lemma F_8d0d0 : fetch_word AsanUbsan.M.loaded_segments (0x8d4e8 : word) = Some W_8d0d0.
Proof. vm_refl. Qed.
Lemma D_8d0d0 : decode_any W_8d0d0 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0d4 : bv 32 := 0x00060493.
Lemma F_8d0d4 : fetch_word AsanUbsan.M.loaded_segments (0x8d4ec : word) = Some W_8d0d4.
Proof. vm_refl. Qed.
Lemma D_8d0d4 : decode_any W_8d0d4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0d8 : bv 32 := 0x00050913.
Lemma F_8d0d8 : fetch_word AsanUbsan.M.loaded_segments (0x8d4f0 : word) = Some W_8d0d8.
Proof. vm_refl. Qed.
Lemma D_8d0d8 : decode_any W_8d0d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0dc : bv 32 := 0x00040593.
Lemma F_8d0dc : fetch_word AsanUbsan.M.loaded_segments (0x8d4f4 : word) = Some W_8d0dc.
Proof. vm_refl. Qed.
Lemma D_8d0dc : decode_any W_8d0dc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0e0 : bv 32 := 0xf90fe0ef.
Lemma F_8d0e0 : fetch_word AsanUbsan.M.loaded_segments (0x8d4f8 : word) = Some W_8d0e0.
Proof. vm_refl. Qed.
Lemma D_8d0e0 : decode_any W_8d0e0 = Some (Jal 1 2090896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0e4 : bv 32 := 0xaaaab5b7.
Lemma F_8d0e4 : fetch_word AsanUbsan.M.loaded_segments (0x8d4fc : word) = Some W_8d0e4.
Proof. vm_refl. Qed.
Lemma D_8d0e4 : decode_any W_8d0e4 = Some (Lui 11 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0e8 : bv 32 := 0xaaa58593.
Lemma F_8d0e8 : fetch_word AsanUbsan.M.loaded_segments (0x8d500 : word) = Some W_8d0e8.
Proof. vm_refl. Qed.
Lemma D_8d0e8 : decode_any W_8d0e8 = Some (OpImm ALU_ADD 11 11 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0ec : bv 32 := 0x00b12623.
Lemma F_8d0ec : fetch_word AsanUbsan.M.loaded_segments (0x8d504 : word) = Some W_8d0ec.
Proof. vm_refl. Qed.
Lemma D_8d0ec : decode_any W_8d0ec = Some (Store SZ4 2 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0f0 : bv 32 := 0x00c10593.
Lemma F_8d0f0 : fetch_word AsanUbsan.M.loaded_segments (0x8d508 : word) = Some W_8d0f0.
Proof. vm_refl. Qed.
Lemma D_8d0f0 : decode_any W_8d0f0 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0f4 : bv 32 := 0xf50fe0ef.
Lemma F_8d0f4 : fetch_word AsanUbsan.M.loaded_segments (0x8d50c : word) = Some W_8d0f4.
Proof. vm_refl. Qed.
Lemma D_8d0f4 : decode_any W_8d0f4 = Some (Jal 1 2090832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0f8 : bv 32 := 0x02051263.
Lemma F_8d0f8 : fetch_word AsanUbsan.M.loaded_segments (0x8d510 : word) = Some W_8d0f8.
Proof. vm_refl. Qed.
Lemma D_8d0f8 : decode_any W_8d0f8 = Some (Branch BC_NE 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d0fc : bv 32 := 0x00040513.
Lemma F_8d0fc : fetch_word AsanUbsan.M.loaded_segments (0x8d514 : word) = Some W_8d0fc.
Proof. vm_refl. Qed.
Lemma D_8d0fc : decode_any W_8d0fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d100 : bv 32 := 0xe70fa0ef.
Lemma F_8d100 : fetch_word AsanUbsan.M.loaded_segments (0x8d518 : word) = Some W_8d100.
Proof. vm_refl. Qed.
Lemma D_8d100 : decode_any W_8d100 = Some (Jal 1 2074224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d104 : bv 32 := 0x02813083.
Lemma F_8d104 : fetch_word AsanUbsan.M.loaded_segments (0x8d51c : word) = Some W_8d104.
Proof. vm_refl. Qed.
Lemma D_8d104 : decode_any W_8d104 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d108 : bv 32 := 0x02013403.
Lemma F_8d108 : fetch_word AsanUbsan.M.loaded_segments (0x8d520 : word) = Some W_8d108.
Proof. vm_refl. Qed.
Lemma D_8d108 : decode_any W_8d108 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d10c : bv 32 := 0x01813483.
Lemma F_8d10c : fetch_word AsanUbsan.M.loaded_segments (0x8d524 : word) = Some W_8d10c.
Proof. vm_refl. Qed.
Lemma D_8d10c : decode_any W_8d10c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d110 : bv 32 := 0x01013903.
Lemma F_8d110 : fetch_word AsanUbsan.M.loaded_segments (0x8d528 : word) = Some W_8d110.
Proof. vm_refl. Qed.
Lemma D_8d110 : decode_any W_8d110 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d114 : bv 32 := 0x03010113.
Lemma F_8d114 : fetch_word AsanUbsan.M.loaded_segments (0x8d52c : word) = Some W_8d114.
Proof. vm_refl. Qed.
Lemma D_8d114 : decode_any W_8d114 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d118 : bv 32 := 0x00008067.
Lemma F_8d118 : fetch_word AsanUbsan.M.loaded_segments (0x8d530 : word) = Some W_8d118.
Proof. vm_refl. Qed.
Lemma D_8d118 : decode_any W_8d118 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d130 : bv 32 := 0xfd010113.
Lemma F_8d130 : fetch_word AsanUbsan.M.loaded_segments (0x8d548 : word) = Some W_8d130.
Proof. vm_refl. Qed.
Lemma D_8d130 : decode_any W_8d130 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d134 : bv 32 := 0x02113423.
Lemma F_8d134 : fetch_word AsanUbsan.M.loaded_segments (0x8d54c : word) = Some W_8d134.
Proof. vm_refl. Qed.
Lemma D_8d134 : decode_any W_8d134 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d138 : bv 32 := 0x02813023.
Lemma F_8d138 : fetch_word AsanUbsan.M.loaded_segments (0x8d550 : word) = Some W_8d138.
Proof. vm_refl. Qed.
Lemma D_8d138 : decode_any W_8d138 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d13c : bv 32 := 0x00913c23.
Lemma F_8d13c : fetch_word AsanUbsan.M.loaded_segments (0x8d554 : word) = Some W_8d13c.
Proof. vm_refl. Qed.
Lemma D_8d13c : decode_any W_8d13c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d140 : bv 32 := 0x01213823.
Lemma F_8d140 : fetch_word AsanUbsan.M.loaded_segments (0x8d558 : word) = Some W_8d140.
Proof. vm_refl. Qed.
Lemma D_8d140 : decode_any W_8d140 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d144 : bv 32 := 0x00058413.
Lemma F_8d144 : fetch_word AsanUbsan.M.loaded_segments (0x8d55c : word) = Some W_8d144.
Proof. vm_refl. Qed.
Lemma D_8d144 : decode_any W_8d144 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d148 : bv 32 := 0x000aa597.
Lemma F_8d148 : fetch_word AsanUbsan.M.loaded_segments (0x8d560 : word) = Some W_8d148.
Proof. vm_refl. Qed.
Lemma D_8d148 : decode_any W_8d148 = Some (Auipc 11 170, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d14c : bv 32 := 0xf405b903.
Lemma F_8d14c : fetch_word AsanUbsan.M.loaded_segments (0x8d564 : word) = Some W_8d14c.
Proof. vm_refl. Qed.
Lemma D_8d14c : decode_any W_8d14c = Some (Load SZ8 true 18 11 3904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d150 : bv 32 := 0x00093583.
Lemma F_8d150 : fetch_word AsanUbsan.M.loaded_segments (0x8d568 : word) = Some W_8d150.
Proof. vm_refl. Qed.
Lemma D_8d150 : decode_any W_8d150 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d154 : bv 32 := 0x00050493.
Lemma F_8d154 : fetch_word AsanUbsan.M.loaded_segments (0x8d56c : word) = Some W_8d154.
Proof. vm_refl. Qed.
Lemma D_8d154 : decode_any W_8d154 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d158 : bv 32 := 0x00059863.
Lemma F_8d158 : fetch_word AsanUbsan.M.loaded_segments (0x8d570 : word) = Some W_8d158.
Proof. vm_refl. Qed.
Lemma D_8d158 : decode_any W_8d158 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d168 : bv 32 := 0xfff58513.
Lemma F_8d168 : fetch_word AsanUbsan.M.loaded_segments (0x8d580 : word) = Some W_8d168.
Proof. vm_refl. Qed.
Lemma D_8d168 : decode_any W_8d168 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d16c : bv 32 := 0x00a5f533.
Lemma F_8d16c : fetch_word AsanUbsan.M.loaded_segments (0x8d584 : word) = Some W_8d16c.
Proof. vm_refl. Qed.
Lemma D_8d16c : decode_any W_8d16c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d170 : bv 32 := 0x08051a63.
Lemma F_8d170 : fetch_word AsanUbsan.M.loaded_segments (0x8d588 : word) = Some W_8d170.
Proof. vm_refl. Qed.
Lemma D_8d170 : decode_any W_8d170 = Some (Branch BC_NE 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d174 : bv 32 := 0x00b484b3.
Lemma F_8d174 : fetch_word AsanUbsan.M.loaded_segments (0x8d58c : word) = Some W_8d174.
Proof. vm_refl. Qed.
Lemma D_8d174 : decode_any W_8d174 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d178 : bv 32 := 0x40b00533.
Lemma F_8d178 : fetch_word AsanUbsan.M.loaded_segments (0x8d590 : word) = Some W_8d178.
Proof. vm_refl. Qed.
Lemma D_8d178 : decode_any W_8d178 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d17c : bv 32 := 0xfff48493.
Lemma F_8d17c : fetch_word AsanUbsan.M.loaded_segments (0x8d594 : word) = Some W_8d17c.
Proof. vm_refl. Qed.
Lemma D_8d17c : decode_any W_8d17c = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d180 : bv 32 := 0x00a4f4b3.
Lemma F_8d180 : fetch_word AsanUbsan.M.loaded_segments (0x8d598 : word) = Some W_8d180.
Proof. vm_refl. Qed.
Lemma D_8d180 : decode_any W_8d180 = Some (Op ALU_AND 9 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d184 : bv 32 := 0x02200513.
Lemma F_8d184 : fetch_word AsanUbsan.M.loaded_segments (0x8d59c : word) = Some W_8d184.
Proof. vm_refl. Qed.
Lemma D_8d184 : decode_any W_8d184 = Some (OpImm ALU_ADD 10 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d188 : bv 32 := 0x00a12623.
Lemma F_8d188 : fetch_word AsanUbsan.M.loaded_segments (0x8d5a0 : word) = Some W_8d188.
Proof. vm_refl. Qed.
Lemma D_8d188 : decode_any W_8d188 = Some (Store SZ4 2 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d18c : bv 32 := 0x00c10613.
Lemma F_8d18c : fetch_word AsanUbsan.M.loaded_segments (0x8d5a4 : word) = Some W_8d18c.
Proof. vm_refl. Qed.
Lemma D_8d18c : decode_any W_8d18c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d190 : bv 32 := 0x00040513.
Lemma F_8d190 : fetch_word AsanUbsan.M.loaded_segments (0x8d5a8 : word) = Some W_8d190.
Proof. vm_refl. Qed.
Lemma D_8d190 : decode_any W_8d190 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d194 : bv 32 := 0x00048593.
Lemma F_8d194 : fetch_word AsanUbsan.M.loaded_segments (0x8d5ac : word) = Some W_8d194.
Proof. vm_refl. Qed.
Lemma D_8d194 : decode_any W_8d194 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d198 : bv 32 := 0x279000ef.
Lemma F_8d198 : fetch_word AsanUbsan.M.loaded_segments (0x8d5b0 : word) = Some W_8d198.
Proof. vm_refl. Qed.
Lemma D_8d198 : decode_any W_8d198 = Some (Jal 1 2680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d19c : bv 32 := 0x00c12683.
Lemma F_8d19c : fetch_word AsanUbsan.M.loaded_segments (0x8d5b4 : word) = Some W_8d19c.
Proof. vm_refl. Qed.
Lemma D_8d19c : decode_any W_8d19c = Some (Load SZ4 true 13 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1a0 : bv 32 := 0x00050713.
Lemma F_8d1a0 : fetch_word AsanUbsan.M.loaded_segments (0x8d5b8 : word) = Some W_8d1a0.
Proof. vm_refl. Qed.
Lemma D_8d1a0 : decode_any W_8d1a0 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1a4 : bv 32 := 0x00300613.
Lemma F_8d1a4 : fetch_word AsanUbsan.M.loaded_segments (0x8d5bc : word) = Some W_8d1a4.
Proof. vm_refl. Qed.
Lemma D_8d1a4 : decode_any W_8d1a4 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1a8 : bv 32 := 0x00000513.
Lemma F_8d1a8 : fetch_word AsanUbsan.M.loaded_segments (0x8d5c0 : word) = Some W_8d1a8.
Proof. vm_refl. Qed.
Lemma D_8d1a8 : decode_any W_8d1a8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1ac : bv 32 := 0x00048593.
Lemma F_8d1ac : fetch_word AsanUbsan.M.loaded_segments (0x8d5c4 : word) = Some W_8d1ac.
Proof. vm_refl. Qed.
Lemma D_8d1ac : decode_any W_8d1ac = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1b0 : bv 32 := 0x00000793.
Lemma F_8d1b0 : fetch_word AsanUbsan.M.loaded_segments (0x8d5c8 : word) = Some W_8d1b0.
Proof. vm_refl. Qed.
Lemma D_8d1b0 : decode_any W_8d1b0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1b4 : bv 32 := 0xeb0fe0ef.
Lemma F_8d1b4 : fetch_word AsanUbsan.M.loaded_segments (0x8d5cc : word) = Some W_8d1b4.
Proof. vm_refl. Qed.
Lemma D_8d1b4 : decode_any W_8d1b4 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1b8 : bv 32 := 0x00050913.
Lemma F_8d1b8 : fetch_word AsanUbsan.M.loaded_segments (0x8d5d0 : word) = Some W_8d1b8.
Proof. vm_refl. Qed.
Lemma D_8d1b8 : decode_any W_8d1b8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1bc : bv 32 := 0x00000593.
Lemma F_8d1bc : fetch_word AsanUbsan.M.loaded_segments (0x8d5d4 : word) = Some W_8d1bc.
Proof. vm_refl. Qed.
Lemma D_8d1bc : decode_any W_8d1bc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1c0 : bv 32 := 0xe84fe0ef.
Lemma F_8d1c0 : fetch_word AsanUbsan.M.loaded_segments (0x8d5d8 : word) = Some W_8d1c0.
Proof. vm_refl. Qed.
Lemma D_8d1c0 : decode_any W_8d1c0 = Some (Jal 1 2090628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1c4 : bv 32 := 0xaaaab537.
Lemma F_8d1c4 : fetch_word AsanUbsan.M.loaded_segments (0x8d5dc : word) = Some W_8d1c4.
Proof. vm_refl. Qed.
Lemma D_8d1c4 : decode_any W_8d1c4 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1c8 : bv 32 := 0xaaa50513.
Lemma F_8d1c8 : fetch_word AsanUbsan.M.loaded_segments (0x8d5e0 : word) = Some W_8d1c8.
Proof. vm_refl. Qed.
Lemma D_8d1c8 : decode_any W_8d1c8 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1cc : bv 32 := 0x00a12423.
Lemma F_8d1cc : fetch_word AsanUbsan.M.loaded_segments (0x8d5e4 : word) = Some W_8d1cc.
Proof. vm_refl. Qed.
Lemma D_8d1cc : decode_any W_8d1cc = Some (Store SZ4 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1d0 : bv 32 := 0x00810593.
Lemma F_8d1d0 : fetch_word AsanUbsan.M.loaded_segments (0x8d5e8 : word) = Some W_8d1d0.
Proof. vm_refl. Qed.
Lemma D_8d1d0 : decode_any W_8d1d0 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1d4 : bv 32 := 0x00090513.
Lemma F_8d1d4 : fetch_word AsanUbsan.M.loaded_segments (0x8d5ec : word) = Some W_8d1d4.
Proof. vm_refl. Qed.
Lemma D_8d1d4 : decode_any W_8d1d4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1d8 : bv 32 := 0xe6cfe0ef.
Lemma F_8d1d8 : fetch_word AsanUbsan.M.loaded_segments (0x8d5f0 : word) = Some W_8d1d8.
Proof. vm_refl. Qed.
Lemma D_8d1d8 : decode_any W_8d1d8 = Some (Jal 1 2090604, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1dc : bv 32 := 0x02051c63.
Lemma F_8d1dc : fetch_word AsanUbsan.M.loaded_segments (0x8d5f4 : word) = Some W_8d1dc.
Proof. vm_refl. Qed.
Lemma D_8d1dc : decode_any W_8d1dc = Some (Branch BC_NE 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1e0 : bv 32 := 0x00048513.
Lemma F_8d1e0 : fetch_word AsanUbsan.M.loaded_segments (0x8d5f8 : word) = Some W_8d1e0.
Proof. vm_refl. Qed.
Lemma D_8d1e0 : decode_any W_8d1e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1e4 : bv 32 := 0xd48fa0ef.
Lemma F_8d1e4 : fetch_word AsanUbsan.M.loaded_segments (0x8d5fc : word) = Some W_8d1e4.
Proof. vm_refl. Qed.
Lemma D_8d1e4 : decode_any W_8d1e4 = Some (Jal 1 2073928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1e8 : bv 32 := 0x00090513.
Lemma F_8d1e8 : fetch_word AsanUbsan.M.loaded_segments (0x8d600 : word) = Some W_8d1e8.
Proof. vm_refl. Qed.
Lemma D_8d1e8 : decode_any W_8d1e8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1ec : bv 32 := 0x02813083.
Lemma F_8d1ec : fetch_word AsanUbsan.M.loaded_segments (0x8d604 : word) = Some W_8d1ec.
Proof. vm_refl. Qed.
Lemma D_8d1ec : decode_any W_8d1ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1f0 : bv 32 := 0x02013403.
Lemma F_8d1f0 : fetch_word AsanUbsan.M.loaded_segments (0x8d608 : word) = Some W_8d1f0.
Proof. vm_refl. Qed.
Lemma D_8d1f0 : decode_any W_8d1f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1f4 : bv 32 := 0x01813483.
Lemma F_8d1f4 : fetch_word AsanUbsan.M.loaded_segments (0x8d60c : word) = Some W_8d1f4.
Proof. vm_refl. Qed.
Lemma D_8d1f4 : decode_any W_8d1f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1f8 : bv 32 := 0x01013903.
Lemma F_8d1f8 : fetch_word AsanUbsan.M.loaded_segments (0x8d610 : word) = Some W_8d1f8.
Proof. vm_refl. Qed.
Lemma D_8d1f8 : decode_any W_8d1f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d1fc : bv 32 := 0x03010113.
Lemma F_8d1fc : fetch_word AsanUbsan.M.loaded_segments (0x8d614 : word) = Some W_8d1fc.
Proof. vm_refl. Qed.
Lemma D_8d1fc : decode_any W_8d1fc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d200 : bv 32 := 0x00008067.
Lemma F_8d200 : fetch_word AsanUbsan.M.loaded_segments (0x8d618 : word) = Some W_8d200.
Proof. vm_refl. Qed.
Lemma D_8d200 : decode_any W_8d200 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
