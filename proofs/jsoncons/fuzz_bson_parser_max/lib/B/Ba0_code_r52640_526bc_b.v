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
Definition W_6ac7c : bv 32 := 0xfe010113.
Lemma F_6ac7c : fetch_word AsanUbsan.M.loaded_segments (0x6b094 : word) = Some W_6ac7c.
Proof. vm_refl. Qed.
Lemma D_6ac7c : decode_any W_6ac7c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac80 : bv 32 := 0x00113c23.
Lemma F_6ac80 : fetch_word AsanUbsan.M.loaded_segments (0x6b098 : word) = Some W_6ac80.
Proof. vm_refl. Qed.
Lemma D_6ac80 : decode_any W_6ac80 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac84 : bv 32 := 0x00813823.
Lemma F_6ac84 : fetch_word AsanUbsan.M.loaded_segments (0x6b09c : word) = Some W_6ac84.
Proof. vm_refl. Qed.
Lemma D_6ac84 : decode_any W_6ac84 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac88 : bv 32 := 0x00913423.
Lemma F_6ac88 : fetch_word AsanUbsan.M.loaded_segments (0x6b0a0 : word) = Some W_6ac88.
Proof. vm_refl. Qed.
Lemma D_6ac88 : decode_any W_6ac88 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac8c : bv 32 := 0x01213023.
Lemma F_6ac8c : fetch_word AsanUbsan.M.loaded_segments (0x6b0a4 : word) = Some W_6ac8c.
Proof. vm_refl. Qed.
Lemma D_6ac8c : decode_any W_6ac8c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac90 : bv 32 := 0x00050413.
Lemma F_6ac90 : fetch_word AsanUbsan.M.loaded_segments (0x6b0a8 : word) = Some W_6ac90.
Proof. vm_refl. Qed.
Lemma D_6ac90 : decode_any W_6ac90 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac94 : bv 32 := 0x038160ef.
Lemma F_6ac94 : fetch_word AsanUbsan.M.loaded_segments (0x6b0ac : word) = Some W_6ac94.
Proof. vm_refl. Qed.
Lemma D_6ac94 : decode_any W_6ac94 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac98 : bv 32 := 0x000ce597.
Lemma F_6ac98 : fetch_word AsanUbsan.M.loaded_segments (0x6b0b0 : word) = Some W_6ac98.
Proof. vm_refl. Qed.
Lemma D_6ac98 : decode_any W_6ac98 = Some (Auipc 11 206, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ac9c : bv 32 := 0x3105b583.
Lemma F_6ac9c : fetch_word AsanUbsan.M.loaded_segments (0x6b0b4 : word) = Some W_6ac9c.
Proof. vm_refl. Qed.
Lemma D_6ac9c : decode_any W_6ac9c = Some (Load SZ8 true 11 11 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aca0 : bv 32 := 0x00050913.
Lemma F_6aca0 : fetch_word AsanUbsan.M.loaded_segments (0x6b0b8 : word) = Some W_6aca0.
Proof. vm_refl. Qed.
Lemma D_6aca0 : decode_any W_6aca0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aca4 : bv 32 := 0x00040513.
Lemma F_6aca4 : fetch_word AsanUbsan.M.loaded_segments (0x6b0bc : word) = Some W_6aca4.
Proof. vm_refl. Qed.
Lemma D_6aca4 : decode_any W_6aca4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6aca8 : bv 32 := 0x000580e7.
Lemma F_6aca8 : fetch_word AsanUbsan.M.loaded_segments (0x6b0c0 : word) = Some W_6aca8.
Proof. vm_refl. Qed.
Lemma D_6aca8 : decode_any W_6aca8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acac : bv 32 := 0x00050493.
Lemma F_6acac : fetch_word AsanUbsan.M.loaded_segments (0x6b0c4 : word) = Some W_6acac.
Proof. vm_refl. Qed.
Lemma D_6acac : decode_any W_6acac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acb0 : bv 32 := 0x02090663.
Lemma F_6acb0 : fetch_word AsanUbsan.M.loaded_segments (0x6b0c8 : word) = Some W_6acb0.
Proof. vm_refl. Qed.
Lemma D_6acb0 : decode_any W_6acb0 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acb4 : bv 32 := 0x019180ef.
Lemma F_6acb4 : fetch_word AsanUbsan.M.loaded_segments (0x6b0cc : word) = Some W_6acb4.
Proof. vm_refl. Qed.
Lemma D_6acb4 : decode_any W_6acb4 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acb8 : bv 32 := 0x00050863.
Lemma F_6acb8 : fetch_word AsanUbsan.M.loaded_segments (0x6b0d0 : word) = Some W_6acb8.
Proof. vm_refl. Qed.
Lemma D_6acb8 : decode_any W_6acb8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acbc : bv 32 := 0x03053603.
Lemma F_6acbc : fetch_word AsanUbsan.M.loaded_segments (0x6b0d4 : word) = Some W_6acbc.
Proof. vm_refl. Qed.
Lemma D_6acbc : decode_any W_6acbc = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acc0 : bv 32 := 0x03853683.
Lemma F_6acc0 : fetch_word AsanUbsan.M.loaded_segments (0x6b0d8 : word) = Some W_6acc0.
Proof. vm_refl. Qed.
Lemma D_6acc0 : decode_any W_6acc0 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acc4 : bv 32 := 0x00c0006f.
Lemma F_6acc4 : fetch_word AsanUbsan.M.loaded_segments (0x6b0dc : word) = Some W_6acc4.
Proof. vm_refl. Qed.
Lemma D_6acc4 : decode_any W_6acc4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acd0 : bv 32 := 0x00040513.
Lemma F_6acd0 : fetch_word AsanUbsan.M.loaded_segments (0x6b0e8 : word) = Some W_6acd0.
Proof. vm_refl. Qed.
Lemma D_6acd0 : decode_any W_6acd0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acd4 : bv 32 := 0x00048593.
Lemma F_6acd4 : fetch_word AsanUbsan.M.loaded_segments (0x6b0ec : word) = Some W_6acd4.
Proof. vm_refl. Qed.
Lemma D_6acd4 : decode_any W_6acd4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acd8 : bv 32 := 0x725250ef.
Lemma F_6acd8 : fetch_word AsanUbsan.M.loaded_segments (0x6b0f0 : word) = Some W_6acd8.
Proof. vm_refl. Qed.
Lemma D_6acd8 : decode_any W_6acd8 = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acdc : bv 32 := 0x00048513.
Lemma F_6acdc : fetch_word AsanUbsan.M.loaded_segments (0x6b0f4 : word) = Some W_6acdc.
Proof. vm_refl. Qed.
Lemma D_6acdc : decode_any W_6acdc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ace0 : bv 32 := 0x01813083.
Lemma F_6ace0 : fetch_word AsanUbsan.M.loaded_segments (0x6b0f8 : word) = Some W_6ace0.
Proof. vm_refl. Qed.
Lemma D_6ace0 : decode_any W_6ace0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ace4 : bv 32 := 0x01013403.
Lemma F_6ace4 : fetch_word AsanUbsan.M.loaded_segments (0x6b0fc : word) = Some W_6ace4.
Proof. vm_refl. Qed.
Lemma D_6ace4 : decode_any W_6ace4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ace8 : bv 32 := 0x00813483.
Lemma F_6ace8 : fetch_word AsanUbsan.M.loaded_segments (0x6b100 : word) = Some W_6ace8.
Proof. vm_refl. Qed.
Lemma D_6ace8 : decode_any W_6ace8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acec : bv 32 := 0x00013903.
Lemma F_6acec : fetch_word AsanUbsan.M.loaded_segments (0x6b104 : word) = Some W_6acec.
Proof. vm_refl. Qed.
Lemma D_6acec : decode_any W_6acec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acf0 : bv 32 := 0x02010113.
Lemma F_6acf0 : fetch_word AsanUbsan.M.loaded_segments (0x6b108 : word) = Some W_6acf0.
Proof. vm_refl. Qed.
Lemma D_6acf0 : decode_any W_6acf0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6acf4 : bv 32 := 0x00008067.
Lemma F_6acf4 : fetch_word AsanUbsan.M.loaded_segments (0x6b10c : word) = Some W_6acf4.
Proof. vm_refl. Qed.
Lemma D_6acf4 : decode_any W_6acf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
