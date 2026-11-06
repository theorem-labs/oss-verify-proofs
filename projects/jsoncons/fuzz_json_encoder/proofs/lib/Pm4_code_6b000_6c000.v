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
Definition W_6b8c8 : bv 32 := 0x0e40006f.
Lemma F_6b8c8 : fetch_word Asan.M.loaded_segments (0x6b918 : word) = Some W_6b8c8.
Proof. vm_refl. Qed.
Lemma D_6b8c8 : decode_any W_6b8c8 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b8ec : bv 32 := 0x1dc0206f.
Lemma F_6b8ec : fetch_word Asan.M.loaded_segments (0x6b93c : word) = Some W_6b8ec.
Proof. vm_refl. Qed.
Lemma D_6b8ec : decode_any W_6b8ec = Some (Jal 0 8668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b94c : bv 32 := 0x4a50706f.
Lemma F_6b94c : fetch_word Asan.M.loaded_segments (0x6b99c : word) = Some W_6b94c.
Proof. vm_refl. Qed.
Lemma D_6b94c : decode_any W_6b94c = Some (Jal 0 31908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9ac : bv 32 := 0x81010113.
Lemma F_6b9ac : fetch_word Asan.M.loaded_segments (0x6b9fc : word) = Some W_6b9ac.
Proof. vm_refl. Qed.
Lemma D_6b9ac : decode_any W_6b9ac = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9b0 : bv 32 := 0x7e113423.
Lemma F_6b9b0 : fetch_word Asan.M.loaded_segments (0x6ba00 : word) = Some W_6b9b0.
Proof. vm_refl. Qed.
Lemma D_6b9b0 : decode_any W_6b9b0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9b4 : bv 32 := 0x7e813023.
Lemma F_6b9b4 : fetch_word Asan.M.loaded_segments (0x6ba04 : word) = Some W_6b9b4.
Proof. vm_refl. Qed.
Lemma D_6b9b4 : decode_any W_6b9b4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9b8 : bv 32 := 0x7c913c23.
Lemma F_6b9b8 : fetch_word Asan.M.loaded_segments (0x6ba08 : word) = Some W_6b9b8.
Proof. vm_refl. Qed.
Lemma D_6b9b8 : decode_any W_6b9b8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9bc : bv 32 := 0x7d213823.
Lemma F_6b9bc : fetch_word Asan.M.loaded_segments (0x6ba0c : word) = Some W_6b9bc.
Proof. vm_refl. Qed.
Lemma D_6b9bc : decode_any W_6b9bc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9c0 : bv 32 := 0x7d313423.
Lemma F_6b9c0 : fetch_word Asan.M.loaded_segments (0x6ba10 : word) = Some W_6b9c0.
Proof. vm_refl. Qed.
Lemma D_6b9c0 : decode_any W_6b9c0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9c4 : bv 32 := 0x7d413023.
Lemma F_6b9c4 : fetch_word Asan.M.loaded_segments (0x6ba14 : word) = Some W_6b9c4.
Proof. vm_refl. Qed.
Lemma D_6b9c4 : decode_any W_6b9c4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9c8 : bv 32 := 0x7b513c23.
Lemma F_6b9c8 : fetch_word Asan.M.loaded_segments (0x6ba18 : word) = Some W_6b9c8.
Proof. vm_refl. Qed.
Lemma D_6b9c8 : decode_any W_6b9c8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9cc : bv 32 := 0x7b613823.
Lemma F_6b9cc : fetch_word Asan.M.loaded_segments (0x6ba1c : word) = Some W_6b9cc.
Proof. vm_refl. Qed.
Lemma D_6b9cc : decode_any W_6b9cc = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9d0 : bv 32 := 0x7f010413.
Lemma F_6b9d0 : fetch_word Asan.M.loaded_segments (0x6ba20 : word) = Some W_6b9d0.
Proof. vm_refl. Qed.
Lemma D_6b9d0 : decode_any W_6b9d0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9d4 : bv 32 := 0xf9010113.
Lemma F_6b9d4 : fetch_word Asan.M.loaded_segments (0x6ba24 : word) = Some W_6b9d4.
Proof. vm_refl. Qed.
Lemma D_6b9d4 : decode_any W_6b9d4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9d8 : bv 32 := 0x00050913.
Lemma F_6b9d8 : fetch_word Asan.M.loaded_segments (0x6ba28 : word) = Some W_6b9d8.
Proof. vm_refl. Qed.
Lemma D_6b9d8 : decode_any W_6b9d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9dc : bv 32 := 0x5551c0ef.
Lemma F_6b9dc : fetch_word Asan.M.loaded_segments (0x6ba2c : word) = Some W_6b9dc.
Proof. vm_refl. Qed.
Lemma D_6b9dc : decode_any W_6b9dc = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9e0 : bv 32 := 0x0a050863.
Lemma F_6b9e0 : fetch_word Asan.M.loaded_segments (0x6ba30 : word) = Some W_6b9e0.
Proof. vm_refl. Qed.
Lemma D_6b9e0 : decode_any W_6b9e0 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9e4 : bv 32 := 0x45d1d0ef.
Lemma F_6b9e4 : fetch_word Asan.M.loaded_segments (0x6ba34 : word) = Some W_6b9e4.
Proof. vm_refl. Qed.
Lemma D_6b9e4 : decode_any W_6b9e4 = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9e8 : bv 32 := 0x000f7597.
Lemma F_6b9e8 : fetch_word Asan.M.loaded_segments (0x6ba38 : word) = Some W_6b9e8.
Proof. vm_refl. Qed.
Lemma D_6b9e8 : decode_any W_6b9e8 = Some (Auipc 11 247, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9ec : bv 32 := 0x0205b583.
Lemma F_6b9ec : fetch_word Asan.M.loaded_segments (0x6ba3c : word) = Some W_6b9ec.
Proof. vm_refl. Qed.
Lemma D_6b9ec : decode_any W_6b9ec = Some (Load SZ8 true 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9f0 : bv 32 := 0x00050493.
Lemma F_6b9f0 : fetch_word Asan.M.loaded_segments (0x6ba40 : word) = Some W_6b9f0.
Proof. vm_refl. Qed.
Lemma D_6b9f0 : decode_any W_6b9f0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9f4 : bv 32 := 0x00090513.
Lemma F_6b9f4 : fetch_word Asan.M.loaded_segments (0x6ba44 : word) = Some W_6b9f4.
Proof. vm_refl. Qed.
Lemma D_6b9f4 : decode_any W_6b9f4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9f8 : bv 32 := 0x000580e7.
Lemma F_6b9f8 : fetch_word Asan.M.loaded_segments (0x6ba48 : word) = Some W_6b9f8.
Proof. vm_refl. Qed.
Lemma D_6b9f8 : decode_any W_6b9f8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b9fc : bv 32 := 0x06048463.
Lemma F_6b9fc : fetch_word Asan.M.loaded_segments (0x6ba4c : word) = Some W_6b9fc.
Proof. vm_refl. Qed.
Lemma D_6b9fc : decode_any W_6b9fc = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba00 : bv 32 := 0x000f5597.
Lemma F_6ba00 : fetch_word Asan.M.loaded_segments (0x6ba50 : word) = Some W_6ba00.
Proof. vm_refl. Qed.
Lemma D_6ba00 : decode_any W_6ba00 = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba04 : bv 32 := 0x1b85b983.
Lemma F_6ba04 : fetch_word Asan.M.loaded_segments (0x6ba54 : word) = Some W_6ba04.
Proof. vm_refl. Qed.
Lemma D_6ba04 : decode_any W_6ba04 = Some (Load SZ8 true 19 11 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba08 : bv 32 := 0x0fb9c583.
Lemma F_6ba08 : fetch_word Asan.M.loaded_segments (0x6ba58 : word) = Some W_6ba08.
Proof. vm_refl. Qed.
Lemma D_6ba08 : decode_any W_6ba08 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba0c : bv 32 := 0x04058c63.
Lemma F_6ba0c : fetch_word Asan.M.loaded_segments (0x6ba5c : word) = Some W_6ba0c.
Proof. vm_refl. Qed.
Lemma D_6ba0c : decode_any W_6ba0c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba10 : bv 32 := 0x00150493.
Lemma F_6ba10 : fetch_word Asan.M.loaded_segments (0x6ba60 : word) = Some W_6ba10.
Proof. vm_refl. Qed.
Lemma D_6ba10 : decode_any W_6ba10 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba14 : bv 32 := 0xfff94593.
Lemma F_6ba14 : fetch_word Asan.M.loaded_segments (0x6ba64 : word) = Some W_6ba14.
Proof. vm_refl. Qed.
Lemma D_6ba14 : decode_any W_6ba14 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba18 : bv 32 := 0x80040a13.
Lemma F_6ba18 : fetch_word Asan.M.loaded_segments (0x6ba68 : word) = Some W_6ba18.
Proof. vm_refl. Qed.
Lemma D_6ba18 : decode_any W_6ba18 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba1c : bv 32 := 0xfa8a0a13.
Lemma F_6ba1c : fetch_word Asan.M.loaded_segments (0x6ba6c : word) = Some W_6ba1c.
Proof. vm_refl. Qed.
Lemma D_6ba1c : decode_any W_6ba1c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba20 : bv 32 := 0x0a95e063.
Lemma F_6ba20 : fetch_word Asan.M.loaded_segments (0x6ba70 : word) = Some W_6ba20.
Proof. vm_refl. Qed.
Lemma D_6ba20 : decode_any W_6ba20 = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba24 : bv 32 := 0x04000593.
Lemma F_6ba24 : fetch_word Asan.M.loaded_segments (0x6ba74 : word) = Some W_6ba24.
Proof. vm_refl. Qed.
Lemma D_6ba24 : decode_any W_6ba24 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba28 : bv 32 := 0x10b57263.
Lemma F_6ba28 : fetch_word Asan.M.loaded_segments (0x6ba78 : word) = Some W_6ba28.
Proof. vm_refl. Qed.
Lemma D_6ba28 : decode_any W_6ba28 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba2c : bv 32 := 0x000f5597.
Lemma F_6ba2c : fetch_word Asan.M.loaded_segments (0x6ba7c : word) = Some W_6ba2c.
Proof. vm_refl. Qed.
Lemma D_6ba2c : decode_any W_6ba2c = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba30 : bv 32 := 0x19c5b583.
Lemma F_6ba30 : fetch_word Asan.M.loaded_segments (0x6ba80 : word) = Some W_6ba30.
Proof. vm_refl. Qed.
Lemma D_6ba30 : decode_any W_6ba30 = Some (Load SZ8 true 11 11 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba34 : bv 32 := 0x0005b603.
Lemma F_6ba34 : fetch_word Asan.M.loaded_segments (0x6ba84 : word) = Some W_6ba34.
Proof. vm_refl. Qed.
Lemma D_6ba34 : decode_any W_6ba34 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba38 : bv 32 := 0x012506b3.
Lemma F_6ba38 : fetch_word Asan.M.loaded_segments (0x6ba88 : word) = Some W_6ba38.
Proof. vm_refl. Qed.
Lemma D_6ba38 : decode_any W_6ba38 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba3c : bv 32 := 0x00395593.
Lemma F_6ba3c : fetch_word Asan.M.loaded_segments (0x6ba8c : word) = Some W_6ba3c.
Proof. vm_refl. Qed.
Lemma D_6ba3c : decode_any W_6ba3c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba40 : bv 32 := 0x0036d713.
Lemma F_6ba40 : fetch_word Asan.M.loaded_segments (0x6ba90 : word) = Some W_6ba40.
Proof. vm_refl. Qed.
Lemma D_6ba40 : decode_any W_6ba40 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba44 : bv 32 := 0x00b605b3.
Lemma F_6ba44 : fetch_word Asan.M.loaded_segments (0x6ba94 : word) = Some W_6ba44.
Proof. vm_refl. Qed.
Lemma D_6ba44 : decode_any W_6ba44 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba48 : bv 32 := 0x00e60633.
Lemma F_6ba48 : fetch_word Asan.M.loaded_segments (0x6ba98 : word) = Some W_6ba48.
Proof. vm_refl. Qed.
Lemma D_6ba48 : decode_any W_6ba48 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba4c : bv 32 := 0xff85f713.
Lemma F_6ba4c : fetch_word Asan.M.loaded_segments (0x6ba9c : word) = Some W_6ba4c.
Proof. vm_refl. Qed.
Lemma D_6ba4c : decode_any W_6ba4c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba50 : bv 32 := 0xff867793.
Lemma F_6ba50 : fetch_word Asan.M.loaded_segments (0x6baa0 : word) = Some W_6ba50.
Proof. vm_refl. Qed.
Lemma D_6ba50 : decode_any W_6ba50 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba54 : bv 32 := 0x00073703.
Lemma F_6ba54 : fetch_word Asan.M.loaded_segments (0x6baa4 : word) = Some W_6ba54.
Proof. vm_refl. Qed.
Lemma D_6ba54 : decode_any W_6ba54 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba58 : bv 32 := 0x0007b783.
Lemma F_6ba58 : fetch_word Asan.M.loaded_segments (0x6baa8 : word) = Some W_6ba58.
Proof. vm_refl. Qed.
Lemma D_6ba58 : decode_any W_6ba58 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba5c : bv 32 := 0x00e7e733.
Lemma F_6ba5c : fetch_word Asan.M.loaded_segments (0x6baac : word) = Some W_6ba5c.
Proof. vm_refl. Qed.
Lemma D_6ba5c : decode_any W_6ba5c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba60 : bv 32 := 0x0c071e63.
Lemma F_6ba60 : fetch_word Asan.M.loaded_segments (0x6bab0 : word) = Some W_6ba60.
Proof. vm_refl. Qed.
Lemma D_6ba60 : decode_any W_6ba60 = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba64 : bv 32 := 0x07010113.
Lemma F_6ba64 : fetch_word Asan.M.loaded_segments (0x6bab4 : word) = Some W_6ba64.
Proof. vm_refl. Qed.
Lemma D_6ba64 : decode_any W_6ba64 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba68 : bv 32 := 0x7e813083.
Lemma F_6ba68 : fetch_word Asan.M.loaded_segments (0x6bab8 : word) = Some W_6ba68.
Proof. vm_refl. Qed.
Lemma D_6ba68 : decode_any W_6ba68 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba6c : bv 32 := 0x7e013403.
Lemma F_6ba6c : fetch_word Asan.M.loaded_segments (0x6babc : word) = Some W_6ba6c.
Proof. vm_refl. Qed.
Lemma D_6ba6c : decode_any W_6ba6c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba70 : bv 32 := 0x7d813483.
Lemma F_6ba70 : fetch_word Asan.M.loaded_segments (0x6bac0 : word) = Some W_6ba70.
Proof. vm_refl. Qed.
Lemma D_6ba70 : decode_any W_6ba70 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba74 : bv 32 := 0x7d013903.
Lemma F_6ba74 : fetch_word Asan.M.loaded_segments (0x6bac4 : word) = Some W_6ba74.
Proof. vm_refl. Qed.
Lemma D_6ba74 : decode_any W_6ba74 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba78 : bv 32 := 0x7c813983.
Lemma F_6ba78 : fetch_word Asan.M.loaded_segments (0x6bac8 : word) = Some W_6ba78.
Proof. vm_refl. Qed.
Lemma D_6ba78 : decode_any W_6ba78 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba7c : bv 32 := 0x7c013a03.
Lemma F_6ba7c : fetch_word Asan.M.loaded_segments (0x6bacc : word) = Some W_6ba7c.
Proof. vm_refl. Qed.
Lemma D_6ba7c : decode_any W_6ba7c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba80 : bv 32 := 0x7b813a83.
Lemma F_6ba80 : fetch_word Asan.M.loaded_segments (0x6bad0 : word) = Some W_6ba80.
Proof. vm_refl. Qed.
Lemma D_6ba80 : decode_any W_6ba80 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba84 : bv 32 := 0x7b013b03.
Lemma F_6ba84 : fetch_word Asan.M.loaded_segments (0x6bad4 : word) = Some W_6ba84.
Proof. vm_refl. Qed.
Lemma D_6ba84 : decode_any W_6ba84 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba88 : bv 32 := 0x7f010113.
Lemma F_6ba88 : fetch_word Asan.M.loaded_segments (0x6bad8 : word) = Some W_6ba88.
Proof. vm_refl. Qed.
Lemma D_6ba88 : decode_any W_6ba88 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ba8c : bv 32 := 0x00008067.
Lemma F_6ba8c : fetch_word Asan.M.loaded_segments (0x6badc : word) = Some W_6ba8c.
Proof. vm_refl. Qed.
Lemma D_6ba8c : decode_any W_6ba8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb2c : bv 32 := 0x00050a93.
Lemma F_6bb2c : fetch_word Asan.M.loaded_segments (0x6bb7c : word) = Some W_6bb2c.
Proof. vm_refl. Qed.
Lemma D_6bb2c : decode_any W_6bb2c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb30 : bv 32 := 0x04049263.
Lemma F_6bb30 : fetch_word Asan.M.loaded_segments (0x6bb80 : word) = Some W_6bb30.
Proof. vm_refl. Qed.
Lemma D_6bb30 : decode_any W_6bb30 = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb3c : bv 32 := 0x00050a93.
Lemma F_6bb3c : fetch_word Asan.M.loaded_segments (0x6bb8c : word) = Some W_6bb3c.
Proof. vm_refl. Qed.
Lemma D_6bb3c : decode_any W_6bb3c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb40 : bv 32 := 0x00060503.
Lemma F_6bb40 : fetch_word Asan.M.loaded_segments (0x6bb90 : word) = Some W_6bb40.
Proof. vm_refl. Qed.
Lemma D_6bb40 : decode_any W_6bb40 = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb44 : bv 32 := 0x0076f693.
Lemma F_6bb44 : fetch_word Asan.M.loaded_segments (0x6bb94 : word) = Some W_6bb44.
Proof. vm_refl. Qed.
Lemma D_6bb44 : decode_any W_6bb44 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb48 : bv 32 := 0x00a03733.
Lemma F_6bb48 : fetch_word Asan.M.loaded_segments (0x6bb98 : word) = Some W_6bb48.
Proof. vm_refl. Qed.
Lemma D_6bb48 : decode_any W_6bb48 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb4c : bv 32 := 0x00a6a533.
Lemma F_6bb4c : fetch_word Asan.M.loaded_segments (0x6bb9c : word) = Some W_6bb4c.
Proof. vm_refl. Qed.
Lemma D_6bb4c : decode_any W_6bb4c = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb50 : bv 32 := 0x00154513.
Lemma F_6bb50 : fetch_word Asan.M.loaded_segments (0x6bba0 : word) = Some W_6bb50.
Proof. vm_refl. Qed.
Lemma D_6bb50 : decode_any W_6bb50 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb54 : bv 32 := 0x00a77533.
Lemma F_6bb54 : fetch_word Asan.M.loaded_segments (0x6bba4 : word) = Some W_6bb54.
Proof. vm_refl. Qed.
Lemma D_6bb54 : decode_any W_6bb54 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb58 : bv 32 := 0x00c5fa63.
Lemma F_6bb58 : fetch_word Asan.M.loaded_segments (0x6bba8 : word) = Some W_6bb58.
Proof. vm_refl. Qed.
Lemma D_6bb58 : decode_any W_6bb58 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb5c : bv 32 := 0x0005c683.
Lemma F_6bb5c : fetch_word Asan.M.loaded_segments (0x6bbac : word) = Some W_6bb5c.
Proof. vm_refl. Qed.
Lemma D_6bb5c : decode_any W_6bb5c = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb60 : bv 32 := 0x00158593.
Lemma F_6bb60 : fetch_word Asan.M.loaded_segments (0x6bbb0 : word) = Some W_6bb60.
Proof. vm_refl. Qed.
Lemma D_6bb60 : decode_any W_6bb60 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb64 : bv 32 := 0x00a6e533.
Lemma F_6bb64 : fetch_word Asan.M.loaded_segments (0x6bbb4 : word) = Some W_6bb64.
Proof. vm_refl. Qed.
Lemma D_6bb64 : decode_any W_6bb64 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb68 : bv 32 := 0xfec59ae3.
Lemma F_6bb68 : fetch_word Asan.M.loaded_segments (0x6bbb8 : word) = Some W_6bb68.
Proof. vm_refl. Qed.
Lemma D_6bb68 : decode_any W_6bb68 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb6c : bv 32 := 0x0ff57513.
Lemma F_6bb6c : fetch_word Asan.M.loaded_segments (0x6bbbc : word) = Some W_6bb6c.
Proof. vm_refl. Qed.
Lemma D_6bb6c : decode_any W_6bb6c = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb70 : bv 32 := 0x0c050463.
Lemma F_6bb70 : fetch_word Asan.M.loaded_segments (0x6bbc0 : word) = Some W_6bb70.
Proof. vm_refl. Qed.
Lemma D_6bb70 : decode_any W_6bb70 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb74 : bv 32 := 0x00090513.
Lemma F_6bb74 : fetch_word Asan.M.loaded_segments (0x6bbc4 : word) = Some W_6bb74.
Proof. vm_refl. Qed.
Lemma D_6bb74 : decode_any W_6bb74 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb78 : bv 32 := 0x00048593.
Lemma F_6bb78 : fetch_word Asan.M.loaded_segments (0x6bbc8 : word) = Some W_6bb78.
Proof. vm_refl. Qed.
Lemma D_6bb78 : decode_any W_6bb78 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb7c : bv 32 := 0x6a1170ef.
Lemma F_6bb7c : fetch_word Asan.M.loaded_segments (0x6bbcc : word) = Some W_6bb7c.
Proof. vm_refl. Qed.
Lemma D_6bb7c : decode_any W_6bb7c = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bb80 : bv 32 := 0x0a050c63.
Lemma F_6bb80 : fetch_word Asan.M.loaded_segments (0x6bbd0 : word) = Some W_6bb80.
Proof. vm_refl. Qed.
Lemma D_6bb80 : decode_any W_6bb80 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc38 : bv 32 := 0x000a8513.
Lemma F_6bc38 : fetch_word Asan.M.loaded_segments (0x6bc88 : word) = Some W_6bc38.
Proof. vm_refl. Qed.
Lemma D_6bc38 : decode_any W_6bc38 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc3c : bv 32 := 0xe29ff06f.
Lemma F_6bc3c : fetch_word Asan.M.loaded_segments (0x6bc8c : word) = Some W_6bc3c.
Proof. vm_refl. Qed.
Lemma D_6bc3c : decode_any W_6bc3c = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc90 : bv 32 := 0x06048a63.
Lemma F_6bc90 : fetch_word Asan.M.loaded_segments (0x6bce0 : word) = Some W_6bc90.
Proof. vm_refl. Qed.
Lemma D_6bc90 : decode_any W_6bc90 = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc94 : bv 32 := 0x000f5597.
Lemma F_6bc94 : fetch_word Asan.M.loaded_segments (0x6bce4 : word) = Some W_6bc94.
Proof. vm_refl. Qed.
Lemma D_6bc94 : decode_any W_6bc94 = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc98 : bv 32 := 0xf245ba83.
Lemma F_6bc98 : fetch_word Asan.M.loaded_segments (0x6bce8 : word) = Some W_6bc98.
Proof. vm_refl. Qed.
Lemma D_6bc98 : decode_any W_6bc98 = Some (Load SZ8 true 21 11 3876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bc9c : bv 32 := 0x0fbac583.
Lemma F_6bc9c : fetch_word Asan.M.loaded_segments (0x6bcec : word) = Some W_6bc9c.
Proof. vm_refl. Qed.
Lemma D_6bc9c : decode_any W_6bc9c = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bca0 : bv 32 := 0x06058263.
Lemma F_6bca0 : fetch_word Asan.M.loaded_segments (0x6bcf0 : word) = Some W_6bca0.
Proof. vm_refl. Qed.
Lemma D_6bca0 : decode_any W_6bca0 = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bca4 : bv 32 := 0x00150493.
Lemma F_6bca4 : fetch_word Asan.M.loaded_segments (0x6bcf4 : word) = Some W_6bca4.
Proof. vm_refl. Qed.
Lemma D_6bca4 : decode_any W_6bca4 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bca8 : bv 32 := 0x0934f463.
Lemma F_6bca8 : fetch_word Asan.M.loaded_segments (0x6bcf8 : word) = Some W_6bca8.
Proof. vm_refl. Qed.
Lemma D_6bca8 : decode_any W_6bca8 = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcac : bv 32 := 0xfff94593.
Lemma F_6bcac : fetch_word Asan.M.loaded_segments (0x6bcfc : word) = Some W_6bcac.
Proof. vm_refl. Qed.
Lemma D_6bcac : decode_any W_6bcac = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcb0 : bv 32 := 0x80040a13.
Lemma F_6bcb0 : fetch_word Asan.M.loaded_segments (0x6bd00 : word) = Some W_6bcb0.
Proof. vm_refl. Qed.
Lemma D_6bcb0 : decode_any W_6bcb0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcb4 : bv 32 := 0xfa8a0a13.
Lemma F_6bcb4 : fetch_word Asan.M.loaded_segments (0x6bd04 : word) = Some W_6bcb4.
Proof. vm_refl. Qed.
Lemma D_6bcb4 : decode_any W_6bcb4 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcb8 : bv 32 := 0x0895e663.
Lemma F_6bcb8 : fetch_word Asan.M.loaded_segments (0x6bd08 : word) = Some W_6bcb8.
Proof. vm_refl. Qed.
Lemma D_6bcb8 : decode_any W_6bcb8 = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcbc : bv 32 := 0xfbf48593.
Lemma F_6bcbc : fetch_word Asan.M.loaded_segments (0x6bd0c : word) = Some W_6bcbc.
Proof. vm_refl. Qed.
Lemma D_6bcbc : decode_any W_6bcbc = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcc0 : bv 32 := 0xfbf00613.
Lemma F_6bcc0 : fetch_word Asan.M.loaded_segments (0x6bd10 : word) = Some W_6bcc0.
Proof. vm_refl. Qed.
Lemma D_6bcc0 : decode_any W_6bcc0 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcc4 : bv 32 := 0x0eb67863.
Lemma F_6bcc4 : fetch_word Asan.M.loaded_segments (0x6bd14 : word) = Some W_6bcc4.
Proof. vm_refl. Qed.
Lemma D_6bcc4 : decode_any W_6bcc4 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcc8 : bv 32 := 0x000f5597.
Lemma F_6bcc8 : fetch_word Asan.M.loaded_segments (0x6bd18 : word) = Some W_6bcc8.
Proof. vm_refl. Qed.
Lemma D_6bcc8 : decode_any W_6bcc8 = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bccc : bv 32 := 0xf005b583.
Lemma F_6bccc : fetch_word Asan.M.loaded_segments (0x6bd1c : word) = Some W_6bccc.
Proof. vm_refl. Qed.
Lemma D_6bccc : decode_any W_6bccc = Some (Load SZ8 true 11 11 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcd0 : bv 32 := 0x009906b3.
Lemma F_6bcd0 : fetch_word Asan.M.loaded_segments (0x6bd20 : word) = Some W_6bcd0.
Proof. vm_refl. Qed.
Lemma D_6bcd0 : decode_any W_6bcd0 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcd4 : bv 32 := 0x0005b603.
Lemma F_6bcd4 : fetch_word Asan.M.loaded_segments (0x6bd24 : word) = Some W_6bcd4.
Proof. vm_refl. Qed.
Lemma D_6bcd4 : decode_any W_6bcd4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcd8 : bv 32 := 0x00395593.
Lemma F_6bcd8 : fetch_word Asan.M.loaded_segments (0x6bd28 : word) = Some W_6bcd8.
Proof. vm_refl. Qed.
Lemma D_6bcd8 : decode_any W_6bcd8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcdc : bv 32 := 0xfff68693.
Lemma F_6bcdc : fetch_word Asan.M.loaded_segments (0x6bd2c : word) = Some W_6bcdc.
Proof. vm_refl. Qed.
Lemma D_6bcdc : decode_any W_6bcdc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bce0 : bv 32 := 0x0036d713.
Lemma F_6bce0 : fetch_word Asan.M.loaded_segments (0x6bd30 : word) = Some W_6bce0.
Proof. vm_refl. Qed.
Lemma D_6bce0 : decode_any W_6bce0 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bce4 : bv 32 := 0x00b605b3.
Lemma F_6bce4 : fetch_word Asan.M.loaded_segments (0x6bd34 : word) = Some W_6bce4.
Proof. vm_refl. Qed.
Lemma D_6bce4 : decode_any W_6bce4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bce8 : bv 32 := 0x00e60633.
Lemma F_6bce8 : fetch_word Asan.M.loaded_segments (0x6bd38 : word) = Some W_6bce8.
Proof. vm_refl. Qed.
Lemma D_6bce8 : decode_any W_6bce8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcec : bv 32 := 0xff85f713.
Lemma F_6bcec : fetch_word Asan.M.loaded_segments (0x6bd3c : word) = Some W_6bcec.
Proof. vm_refl. Qed.
Lemma D_6bcec : decode_any W_6bcec = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcf0 : bv 32 := 0xff867793.
Lemma F_6bcf0 : fetch_word Asan.M.loaded_segments (0x6bd40 : word) = Some W_6bcf0.
Proof. vm_refl. Qed.
Lemma D_6bcf0 : decode_any W_6bcf0 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcf4 : bv 32 := 0x00073703.
Lemma F_6bcf4 : fetch_word Asan.M.loaded_segments (0x6bd44 : word) = Some W_6bcf4.
Proof. vm_refl. Qed.
Lemma D_6bcf4 : decode_any W_6bcf4 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcf8 : bv 32 := 0x0007b783.
Lemma F_6bcf8 : fetch_word Asan.M.loaded_segments (0x6bd48 : word) = Some W_6bcf8.
Proof. vm_refl. Qed.
Lemma D_6bcf8 : decode_any W_6bcf8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bcfc : bv 32 := 0x00e7e733.
Lemma F_6bcfc : fetch_word Asan.M.loaded_segments (0x6bd4c : word) = Some W_6bcfc.
Proof. vm_refl. Qed.
Lemma D_6bcfc : decode_any W_6bcfc = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bd00 : bv 32 := 0x0a071e63.
Lemma F_6bd00 : fetch_word Asan.M.loaded_segments (0x6bd50 : word) = Some W_6bd00.
Proof. vm_refl. Qed.
Lemma D_6bd00 : decode_any W_6bd00 = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdb4 : bv 32 := 0x02049e63.
Lemma F_6bdb4 : fetch_word Asan.M.loaded_segments (0x6be04 : word) = Some W_6bdb4.
Proof. vm_refl. Qed.
Lemma D_6bdb4 : decode_any W_6bdb4 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdf0 : bv 32 := 0x00050b13.
Lemma F_6bdf0 : fetch_word Asan.M.loaded_segments (0x6be40 : word) = Some W_6bdf0.
Proof. vm_refl. Qed.
Lemma D_6bdf0 : decode_any W_6bdf0 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdf4 : bv 32 := 0x00090513.
Lemma F_6bdf4 : fetch_word Asan.M.loaded_segments (0x6be44 : word) = Some W_6bdf4.
Proof. vm_refl. Qed.
Lemma D_6bdf4 : decode_any W_6bdf4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdf8 : bv 32 := 0x00048593.
Lemma F_6bdf8 : fetch_word Asan.M.loaded_segments (0x6be48 : word) = Some W_6bdf8.
Proof. vm_refl. Qed.
Lemma D_6bdf8 : decode_any W_6bdf8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bdfc : bv 32 := 0x421170ef.
Lemma F_6bdfc : fetch_word Asan.M.loaded_segments (0x6be4c : word) = Some W_6bdfc.
Proof. vm_refl. Qed.
Lemma D_6bdfc : decode_any W_6bdfc = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be00 : bv 32 := 0x00050913.
Lemma F_6be00 : fetch_word Asan.M.loaded_segments (0x6be50 : word) = Some W_6be00.
Proof. vm_refl. Qed.
Lemma D_6be00 : decode_any W_6be00 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be04 : bv 32 := 0x000b0513.
Lemma F_6be04 : fetch_word Asan.M.loaded_segments (0x6be54 : word) = Some W_6be04.
Proof. vm_refl. Qed.
Lemma D_6be04 : decode_any W_6be04 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be08 : bv 32 := 0xee090ee3.
Lemma F_6be08 : fetch_word Asan.M.loaded_segments (0x6be58 : word) = Some W_6be08.
Proof. vm_refl. Qed.
Lemma D_6be08 : decode_any W_6be08 = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

