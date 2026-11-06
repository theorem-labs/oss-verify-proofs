(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b9c8 : bv 32 := 0xfe010113.
Lemma F_6b9c8 : fetch_word Asan.M.loaded_segments (0x6ba18 : word) = Some W_6b9c8.
Proof. vm_refl. Qed.
Lemma D_6b9c8 : decode_any W_6b9c8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9cc : bv 32 := 0x00113c23.
Lemma F_6b9cc : fetch_word Asan.M.loaded_segments (0x6ba1c : word) = Some W_6b9cc.
Proof. vm_refl. Qed.
Lemma D_6b9cc : decode_any W_6b9cc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9d0 : bv 32 := 0x00813823.
Lemma F_6b9d0 : fetch_word Asan.M.loaded_segments (0x6ba20 : word) = Some W_6b9d0.
Proof. vm_refl. Qed.
Lemma D_6b9d0 : decode_any W_6b9d0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9d4 : bv 32 := 0x00913423.
Lemma F_6b9d4 : fetch_word Asan.M.loaded_segments (0x6ba24 : word) = Some W_6b9d4.
Proof. vm_refl. Qed.
Lemma D_6b9d4 : decode_any W_6b9d4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9d8 : bv 32 := 0x01213023.
Lemma F_6b9d8 : fetch_word Asan.M.loaded_segments (0x6ba28 : word) = Some W_6b9d8.
Proof. vm_refl. Qed.
Lemma D_6b9d8 : decode_any W_6b9d8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9dc : bv 32 := 0x00050413.
Lemma F_6b9dc : fetch_word Asan.M.loaded_segments (0x6ba2c : word) = Some W_6b9dc.
Proof. vm_refl. Qed.
Lemma D_6b9dc : decode_any W_6b9dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9e0 : bv 32 := 0x038160ef.
Lemma F_6b9e0 : fetch_word Asan.M.loaded_segments (0x6ba30 : word) = Some W_6b9e0.
Proof. vm_refl. Qed.
Lemma D_6b9e0 : decode_any W_6b9e0 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9e4 : bv 32 := 0x000cf597.
Lemma F_6b9e4 : fetch_word Asan.M.loaded_segments (0x6ba34 : word) = Some W_6b9e4.
Proof. vm_refl. Qed.
Lemma D_6b9e4 : decode_any W_6b9e4 = Some (Auipc 11 207, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9e8 : bv 32 := 0x6845b583.
Lemma F_6b9e8 : fetch_word Asan.M.loaded_segments (0x6ba38 : word) = Some W_6b9e8.
Proof. vm_refl. Qed.
Lemma D_6b9e8 : decode_any W_6b9e8 = Some (Load SZ8 true 11 11 1668, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9ec : bv 32 := 0x00050913.
Lemma F_6b9ec : fetch_word Asan.M.loaded_segments (0x6ba3c : word) = Some W_6b9ec.
Proof. vm_refl. Qed.
Lemma D_6b9ec : decode_any W_6b9ec = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9f0 : bv 32 := 0x00040513.
Lemma F_6b9f0 : fetch_word Asan.M.loaded_segments (0x6ba40 : word) = Some W_6b9f0.
Proof. vm_refl. Qed.
Lemma D_6b9f0 : decode_any W_6b9f0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9f4 : bv 32 := 0x000580e7.
Lemma F_6b9f4 : fetch_word Asan.M.loaded_segments (0x6ba44 : word) = Some W_6b9f4.
Proof. vm_refl. Qed.
Lemma D_6b9f4 : decode_any W_6b9f4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9f8 : bv 32 := 0x00050493.
Lemma F_6b9f8 : fetch_word Asan.M.loaded_segments (0x6ba48 : word) = Some W_6b9f8.
Proof. vm_refl. Qed.
Lemma D_6b9f8 : decode_any W_6b9f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9fc : bv 32 := 0x02090663.
Lemma F_6b9fc : fetch_word Asan.M.loaded_segments (0x6ba4c : word) = Some W_6b9fc.
Proof. vm_refl. Qed.
Lemma D_6b9fc : decode_any W_6b9fc = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba00 : bv 32 := 0x019180ef.
Lemma F_6ba00 : fetch_word Asan.M.loaded_segments (0x6ba50 : word) = Some W_6ba00.
Proof. vm_refl. Qed.
Lemma D_6ba00 : decode_any W_6ba00 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba04 : bv 32 := 0x00050863.
Lemma F_6ba04 : fetch_word Asan.M.loaded_segments (0x6ba54 : word) = Some W_6ba04.
Proof. vm_refl. Qed.
Lemma D_6ba04 : decode_any W_6ba04 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba08 : bv 32 := 0x03053603.
Lemma F_6ba08 : fetch_word Asan.M.loaded_segments (0x6ba58 : word) = Some W_6ba08.
Proof. vm_refl. Qed.
Lemma D_6ba08 : decode_any W_6ba08 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba0c : bv 32 := 0x03853683.
Lemma F_6ba0c : fetch_word Asan.M.loaded_segments (0x6ba5c : word) = Some W_6ba0c.
Proof. vm_refl. Qed.
Lemma D_6ba0c : decode_any W_6ba0c = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba10 : bv 32 := 0x00c0006f.
Lemma F_6ba10 : fetch_word Asan.M.loaded_segments (0x6ba60 : word) = Some W_6ba10.
Proof. vm_refl. Qed.
Lemma D_6ba10 : decode_any W_6ba10 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba1c : bv 32 := 0x00040513.
Lemma F_6ba1c : fetch_word Asan.M.loaded_segments (0x6ba6c : word) = Some W_6ba1c.
Proof. vm_refl. Qed.
Lemma D_6ba1c : decode_any W_6ba1c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba20 : bv 32 := 0x00048593.
Lemma F_6ba20 : fetch_word Asan.M.loaded_segments (0x6ba70 : word) = Some W_6ba20.
Proof. vm_refl. Qed.
Lemma D_6ba20 : decode_any W_6ba20 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba24 : bv 32 := 0x725250ef.
Lemma F_6ba24 : fetch_word Asan.M.loaded_segments (0x6ba74 : word) = Some W_6ba24.
Proof. vm_refl. Qed.
Lemma D_6ba24 : decode_any W_6ba24 = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba28 : bv 32 := 0x00048513.
Lemma F_6ba28 : fetch_word Asan.M.loaded_segments (0x6ba78 : word) = Some W_6ba28.
Proof. vm_refl. Qed.
Lemma D_6ba28 : decode_any W_6ba28 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba2c : bv 32 := 0x01813083.
Lemma F_6ba2c : fetch_word Asan.M.loaded_segments (0x6ba7c : word) = Some W_6ba2c.
Proof. vm_refl. Qed.
Lemma D_6ba2c : decode_any W_6ba2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba30 : bv 32 := 0x01013403.
Lemma F_6ba30 : fetch_word Asan.M.loaded_segments (0x6ba80 : word) = Some W_6ba30.
Proof. vm_refl. Qed.
Lemma D_6ba30 : decode_any W_6ba30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba34 : bv 32 := 0x00813483.
Lemma F_6ba34 : fetch_word Asan.M.loaded_segments (0x6ba84 : word) = Some W_6ba34.
Proof. vm_refl. Qed.
Lemma D_6ba34 : decode_any W_6ba34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba38 : bv 32 := 0x00013903.
Lemma F_6ba38 : fetch_word Asan.M.loaded_segments (0x6ba88 : word) = Some W_6ba38.
Proof. vm_refl. Qed.
Lemma D_6ba38 : decode_any W_6ba38 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba3c : bv 32 := 0x02010113.
Lemma F_6ba3c : fetch_word Asan.M.loaded_segments (0x6ba8c : word) = Some W_6ba3c.
Proof. vm_refl. Qed.
Lemma D_6ba3c : decode_any W_6ba3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba40 : bv 32 := 0x00008067.
Lemma F_6ba40 : fetch_word Asan.M.loaded_segments (0x6ba90 : word) = Some W_6ba40.
Proof. vm_refl. Qed.
Lemma D_6ba40 : decode_any W_6ba40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
