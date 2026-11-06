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

Definition W_9b8e0 : bv 32 := 0xfc010113.
Lemma F_9b8e0 : fetch_word Asan.M.loaded_segments (0x9b930 : word) = Some W_9b8e0.
Proof. vm_refl. Qed.
Lemma D_9b8e0 : decode_any W_9b8e0 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8e4 : bv 32 := 0x02113c23.
Lemma F_9b8e4 : fetch_word Asan.M.loaded_segments (0x9b934 : word) = Some W_9b8e4.
Proof. vm_refl. Qed.
Lemma D_9b8e4 : decode_any W_9b8e4 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8e8 : bv 32 := 0x02813823.
Lemma F_9b8e8 : fetch_word Asan.M.loaded_segments (0x9b938 : word) = Some W_9b8e8.
Proof. vm_refl. Qed.
Lemma D_9b8e8 : decode_any W_9b8e8 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8ec : bv 32 := 0x02913423.
Lemma F_9b8ec : fetch_word Asan.M.loaded_segments (0x9b93c : word) = Some W_9b8ec.
Proof. vm_refl. Qed.
Lemma D_9b8ec : decode_any W_9b8ec = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8f0 : bv 32 := 0x03213023.
Lemma F_9b8f0 : fetch_word Asan.M.loaded_segments (0x9b940 : word) = Some W_9b8f0.
Proof. vm_refl. Qed.
Lemma D_9b8f0 : decode_any W_9b8f0 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8f4 : bv 32 := 0x01313c23.
Lemma F_9b8f4 : fetch_word Asan.M.loaded_segments (0x9b944 : word) = Some W_9b8f4.
Proof. vm_refl. Qed.
Lemma D_9b8f4 : decode_any W_9b8f4 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8f8 : bv 32 := 0x01413823.
Lemma F_9b8f8 : fetch_word Asan.M.loaded_segments (0x9b948 : word) = Some W_9b8f8.
Proof. vm_refl. Qed.
Lemma D_9b8f8 : decode_any W_9b8f8 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b8fc : bv 32 := 0x01513423.
Lemma F_9b8fc : fetch_word Asan.M.loaded_segments (0x9b94c : word) = Some W_9b8fc.
Proof. vm_refl. Qed.
Lemma D_9b8fc : decode_any W_9b8fc = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b900 : bv 32 := 0x00058413.
Lemma F_9b900 : fetch_word Asan.M.loaded_segments (0x9b950 : word) = Some W_9b900.
Proof. vm_refl. Qed.
Lemma D_9b900 : decode_any W_9b900 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b904 : bv 32 := 0x0015b593.
Lemma F_9b904 : fetch_word Asan.M.loaded_segments (0x9b954 : word) = Some W_9b904.
Proof. vm_refl. Qed.
Lemma D_9b904 : decode_any W_9b904 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b908 : bv 32 := 0x7ff50293.
Lemma F_9b908 : fetch_word Asan.M.loaded_segments (0x9b958 : word) = Some W_9b908.
Proof. vm_refl. Qed.
Lemma D_9b908 : decode_any W_9b908 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b90c : bv 32 := 0xfff58593.
Lemma F_9b90c : fetch_word Asan.M.loaded_segments (0x9b95c : word) = Some W_9b90c.
Proof. vm_refl. Qed.
Lemma D_9b90c : decode_any W_9b90c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b910 : bv 32 := 0x00d5f333.
Lemma F_9b910 : fetch_word Asan.M.loaded_segments (0x9b960 : word) = Some W_9b910.
Proof. vm_refl. Qed.
Lemma D_9b910 : decode_any W_9b910 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b914 : bv 32 := 0x00100593.
Lemma F_9b914 : fetch_word Asan.M.loaded_segments (0x9b964 : word) = Some W_9b914.
Proof. vm_refl. Qed.
Lemma D_9b914 : decode_any W_9b914 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b918 : bv 32 := 0x0062b4a3.
Lemma F_9b918 : fetch_word Asan.M.loaded_segments (0x9b968 : word) = Some W_9b918.
Proof. vm_refl. Qed.
Lemma D_9b918 : decode_any W_9b918 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b91c : bv 32 := 0x00b40863.
Lemma F_9b91c : fetch_word Asan.M.loaded_segments (0x9b96c : word) = Some W_9b91c.
Proof. vm_refl. Qed.
Lemma D_9b91c : decode_any W_9b91c = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b920 : bv 32 := 0x02041c63.
Lemma F_9b920 : fetch_word Asan.M.loaded_segments (0x9b970 : word) = Some W_9b920.
Proof. vm_refl. Qed.
Lemma D_9b920 : decode_any W_9b920 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b958 : bv 32 := 0x06089463.
Lemma F_9b958 : fetch_word Asan.M.loaded_segments (0x9b9a8 : word) = Some W_9b958.
Proof. vm_refl. Qed.
Lemma D_9b958 : decode_any W_9b958 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9c0 : bv 32 := 0x00060593.
Lemma F_9b9c0 : fetch_word Asan.M.loaded_segments (0x9ba10 : word) = Some W_9b9c0.
Proof. vm_refl. Qed.
Lemma D_9b9c0 : decode_any W_9b9c0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9c4 : bv 32 := 0x00068613.
Lemma F_9b9c4 : fetch_word Asan.M.loaded_segments (0x9ba14 : word) = Some W_9b9c4.
Proof. vm_refl. Qed.
Lemma D_9b9c4 : decode_any W_9b9c4 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9c8 : bv 32 := 0x00078693.
Lemma F_9b9c8 : fetch_word Asan.M.loaded_segments (0x9ba18 : word) = Some W_9b9c8.
Proof. vm_refl. Qed.
Lemma D_9b9c8 : decode_any W_9b9c8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9cc : bv 32 := 0x00080713.
Lemma F_9b9cc : fetch_word Asan.M.loaded_segments (0x9ba1c : word) = Some W_9b9cc.
Proof. vm_refl. Qed.
Lemma D_9b9cc : decode_any W_9b9cc = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9d0 : bv 32 := 0x00040793.
Lemma F_9b9d0 : fetch_word Asan.M.loaded_segments (0x9ba20 : word) = Some W_9b9d0.
Proof. vm_refl. Qed.
Lemma D_9b9d0 : decode_any W_9b9d0 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9d4 : bv 32 := 0x03813083.
Lemma F_9b9d4 : fetch_word Asan.M.loaded_segments (0x9ba24 : word) = Some W_9b9d4.
Proof. vm_refl. Qed.
Lemma D_9b9d4 : decode_any W_9b9d4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9d8 : bv 32 := 0x03013403.
Lemma F_9b9d8 : fetch_word Asan.M.loaded_segments (0x9ba28 : word) = Some W_9b9d8.
Proof. vm_refl. Qed.
Lemma D_9b9d8 : decode_any W_9b9d8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9dc : bv 32 := 0x02813483.
Lemma F_9b9dc : fetch_word Asan.M.loaded_segments (0x9ba2c : word) = Some W_9b9dc.
Proof. vm_refl. Qed.
Lemma D_9b9dc : decode_any W_9b9dc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9e0 : bv 32 := 0x02013903.
Lemma F_9b9e0 : fetch_word Asan.M.loaded_segments (0x9ba30 : word) = Some W_9b9e0.
Proof. vm_refl. Qed.
Lemma D_9b9e0 : decode_any W_9b9e0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9e4 : bv 32 := 0x01813983.
Lemma F_9b9e4 : fetch_word Asan.M.loaded_segments (0x9ba34 : word) = Some W_9b9e4.
Proof. vm_refl. Qed.
Lemma D_9b9e4 : decode_any W_9b9e4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9e8 : bv 32 := 0x01013a03.
Lemma F_9b9e8 : fetch_word Asan.M.loaded_segments (0x9ba38 : word) = Some W_9b9e8.
Proof. vm_refl. Qed.
Lemma D_9b9e8 : decode_any W_9b9e8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9ec : bv 32 := 0x00813a83.
Lemma F_9b9ec : fetch_word Asan.M.loaded_segments (0x9ba3c : word) = Some W_9b9ec.
Proof. vm_refl. Qed.
Lemma D_9b9ec : decode_any W_9b9ec = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9f0 : bv 32 := 0x04010113.
Lemma F_9b9f0 : fetch_word Asan.M.loaded_segments (0x9ba40 : word) = Some W_9b9f0.
Proof. vm_refl. Qed.
Lemma D_9b9f0 : decode_any W_9b9f0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b9f4 : bv 32 := 0x891ff06f.
Lemma F_9b9f4 : fetch_word Asan.M.loaded_segments (0x9ba44 : word) = Some W_9b9f4.
Proof. vm_refl. Qed.
Lemma D_9b9f4 : decode_any W_9b9f4 = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.
