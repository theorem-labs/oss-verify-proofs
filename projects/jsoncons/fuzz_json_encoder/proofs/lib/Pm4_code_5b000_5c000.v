(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5b36c : bv 32 := 0xfe010113.
Lemma F_5b36c : fetch_word Asan.M.loaded_segments (0x5b3bc : word) = Some W_5b36c.
Proof. vm_refl. Qed.
Lemma D_5b36c : decode_any W_5b36c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b370 : bv 32 := 0x00113c23.
Lemma F_5b370 : fetch_word Asan.M.loaded_segments (0x5b3c0 : word) = Some W_5b370.
Proof. vm_refl. Qed.
Lemma D_5b370 : decode_any W_5b370 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b374 : bv 32 := 0x00813823.
Lemma F_5b374 : fetch_word Asan.M.loaded_segments (0x5b3c4 : word) = Some W_5b374.
Proof. vm_refl. Qed.
Lemma D_5b374 : decode_any W_5b374 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b378 : bv 32 := 0x00913423.
Lemma F_5b378 : fetch_word Asan.M.loaded_segments (0x5b3c8 : word) = Some W_5b378.
Proof. vm_refl. Qed.
Lemma D_5b378 : decode_any W_5b378 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b37c : bv 32 := 0x01213023.
Lemma F_5b37c : fetch_word Asan.M.loaded_segments (0x5b3cc : word) = Some W_5b37c.
Proof. vm_refl. Qed.
Lemma D_5b37c : decode_any W_5b37c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b380 : bv 32 := 0x00060413.
Lemma F_5b380 : fetch_word Asan.M.loaded_segments (0x5b3d0 : word) = Some W_5b380.
Proof. vm_refl. Qed.
Lemma D_5b380 : decode_any W_5b380 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b384 : bv 32 := 0x00050493.
Lemma F_5b384 : fetch_word Asan.M.loaded_segments (0x5b3d4 : word) = Some W_5b384.
Proof. vm_refl. Qed.
Lemma D_5b384 : decode_any W_5b384 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b388 : bv 32 := 0xfff50513.
Lemma F_5b388 : fetch_word Asan.M.loaded_segments (0x5b3d8 : word) = Some W_5b388.
Proof. vm_refl. Qed.
Lemma D_5b388 : decode_any W_5b388 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b38c : bv 32 := 0x00a4c633.
Lemma F_5b38c : fetch_word Asan.M.loaded_segments (0x5b3dc : word) = Some W_5b38c.
Proof. vm_refl. Qed.
Lemma D_5b38c : decode_any W_5b38c = Some (Op ALU_XOR 12 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b390 : bv 32 := 0x04c57263.
Lemma F_5b390 : fetch_word Asan.M.loaded_segments (0x5b3e0 : word) = Some W_5b390.
Proof. vm_refl. Qed.
Lemma D_5b390 : decode_any W_5b390 = Some (Branch BC_GEU 10 12 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b394 : bv 32 := 0x00a5f533.
Lemma F_5b394 : fetch_word Asan.M.loaded_segments (0x5b3e4 : word) = Some W_5b394.
Proof. vm_refl. Qed.
Lemma D_5b394 : decode_any W_5b394 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b398 : bv 32 := 0x02051e63.
Lemma F_5b398 : fetch_word Asan.M.loaded_segments (0x5b3e8 : word) = Some W_5b398.
Proof. vm_refl. Qed.
Lemma D_5b398 : decode_any W_5b398 = Some (Branch BC_NE 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b39c : bv 32 := 0x0010b517.
Lemma F_5b39c : fetch_word Asan.M.loaded_segments (0x5b3ec : word) = Some W_5b39c.
Proof. vm_refl. Qed.
Lemma D_5b39c : decode_any W_5b39c = Some (Auipc 10 267, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3a0 : bv 32 := 0x00100713.
Lemma F_5b3a0 : fetch_word Asan.M.loaded_segments (0x5b3f0 : word) = Some W_5b3a0.
Proof. vm_refl. Qed.
Lemma D_5b3a0 : decode_any W_5b3a0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3a4 : bv 32 := 0x4ac50513.
Lemma F_5b3a4 : fetch_word Asan.M.loaded_segments (0x5b3f4 : word) = Some W_5b3a4.
Proof. vm_refl. Qed.
Lemma D_5b3a4 : decode_any W_5b3a4 = Some (OpImm ALU_ADD 10 10 1196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3a8 : bv 32 := 0x00100793.
Lemma F_5b3a8 : fetch_word Asan.M.loaded_segments (0x5b3f8 : word) = Some W_5b3a8.
Proof. vm_refl. Qed.
Lemma D_5b3a8 : decode_any W_5b3a8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3ac : bv 32 := 0x00048613.
Lemma F_5b3ac : fetch_word Asan.M.loaded_segments (0x5b3fc : word) = Some W_5b3ac.
Proof. vm_refl. Qed.
Lemma D_5b3ac : decode_any W_5b3ac = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3b0 : bv 32 := 0x00040693.
Lemma F_5b3b0 : fetch_word Asan.M.loaded_segments (0x5b400 : word) = Some W_5b3b0.
Proof. vm_refl. Qed.
Lemma D_5b3b0 : decode_any W_5b3b0 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3b4 : bv 32 := 0xc24ff0ef.
Lemma F_5b3b4 : fetch_word Asan.M.loaded_segments (0x5b404 : word) = Some W_5b3b4.
Proof. vm_refl. Qed.
Lemma D_5b3b4 : decode_any W_5b3b4 = Some (Jal 1 2094116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3b8 : bv 32 := 0x04050663.
Lemma F_5b3b8 : fetch_word Asan.M.loaded_segments (0x5b408 : word) = Some W_5b3b8.
Proof. vm_refl. Qed.
Lemma D_5b3b8 : decode_any W_5b3b8 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3bc : bv 32 := 0x01813083.
Lemma F_5b3bc : fetch_word Asan.M.loaded_segments (0x5b40c : word) = Some W_5b3bc.
Proof. vm_refl. Qed.
Lemma D_5b3bc : decode_any W_5b3bc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3c0 : bv 32 := 0x01013403.
Lemma F_5b3c0 : fetch_word Asan.M.loaded_segments (0x5b410 : word) = Some W_5b3c0.
Proof. vm_refl. Qed.
Lemma D_5b3c0 : decode_any W_5b3c0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3c4 : bv 32 := 0x00813483.
Lemma F_5b3c4 : fetch_word Asan.M.loaded_segments (0x5b414 : word) = Some W_5b3c4.
Proof. vm_refl. Qed.
Lemma D_5b3c4 : decode_any W_5b3c4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3c8 : bv 32 := 0x00013903.
Lemma F_5b3c8 : fetch_word Asan.M.loaded_segments (0x5b418 : word) = Some W_5b3c8.
Proof. vm_refl. Qed.
Lemma D_5b3c8 : decode_any W_5b3c8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3cc : bv 32 := 0x02010113.
Lemma F_5b3cc : fetch_word Asan.M.loaded_segments (0x5b41c : word) = Some W_5b3cc.
Proof. vm_refl. Qed.
Lemma D_5b3cc : decode_any W_5b3cc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5b3d0 : bv 32 := 0x00008067.
Lemma F_5b3d0 : fetch_word Asan.M.loaded_segments (0x5b420 : word) = Some W_5b3d0.
Proof. vm_refl. Qed.
Lemma D_5b3d0 : decode_any W_5b3d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

