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

Definition W_9b08c : bv 32 := 0xfd010113.
Lemma F_9b08c : fetch_word Asan.M.loaded_segments (0x9b0dc : word) = Some W_9b08c.
Proof. vm_refl. Qed.
Lemma D_9b08c : decode_any W_9b08c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b090 : bv 32 := 0x02113423.
Lemma F_9b090 : fetch_word Asan.M.loaded_segments (0x9b0e0 : word) = Some W_9b090.
Proof. vm_refl. Qed.
Lemma D_9b090 : decode_any W_9b090 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b094 : bv 32 := 0x02813023.
Lemma F_9b094 : fetch_word Asan.M.loaded_segments (0x9b0e4 : word) = Some W_9b094.
Proof. vm_refl. Qed.
Lemma D_9b094 : decode_any W_9b094 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b098 : bv 32 := 0x00913c23.
Lemma F_9b098 : fetch_word Asan.M.loaded_segments (0x9b0e8 : word) = Some W_9b098.
Proof. vm_refl. Qed.
Lemma D_9b098 : decode_any W_9b098 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b09c : bv 32 := 0x01213823.
Lemma F_9b09c : fetch_word Asan.M.loaded_segments (0x9b0ec : word) = Some W_9b09c.
Proof. vm_refl. Qed.
Lemma D_9b09c : decode_any W_9b09c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0a0 : bv 32 := 0x01313423.
Lemma F_9b0a0 : fetch_word Asan.M.loaded_segments (0x9b0f0 : word) = Some W_9b0a0.
Proof. vm_refl. Qed.
Lemma D_9b0a0 : decode_any W_9b0a0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0a4 : bv 32 := 0x00050413.
Lemma F_9b0a4 : fetch_word Asan.M.loaded_segments (0x9b0f4 : word) = Some W_9b0a4.
Proof. vm_refl. Qed.
Lemma D_9b0a4 : decode_any W_9b0a4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0a8 : bv 32 := 0x00000593.
Lemma F_9b0a8 : fetch_word Asan.M.loaded_segments (0x9b0f8 : word) = Some W_9b0a8.
Proof. vm_refl. Qed.
Lemma D_9b0a8 : decode_any W_9b0a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0ac : bv 32 := 0x800004b7.
Lemma F_9b0ac : fetch_word Asan.M.loaded_segments (0x9b0fc : word) = Some W_9b0ac.
Proof. vm_refl. Qed.
Lemma D_9b0ac : decode_any W_9b0ac = Some (Lui 9 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0b0 : bv 32 := 0x00900913.
Lemma F_9b0b0 : fetch_word Asan.M.loaded_segments (0x9b100 : word) = Some W_9b0b0.
Proof. vm_refl. Qed.
Lemma D_9b0b0 : decode_any W_9b0b0 = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0b4 : bv 32 := 0x00052503.
Lemma F_9b0b4 : fetch_word Asan.M.loaded_segments (0x9b104 : word) = Some W_9b0b4.
Proof. vm_refl. Qed.
Lemma D_9b0b4 : decode_any W_9b0b4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0b8 : bv 32 := 0x00055a63.
Lemma F_9b0b8 : fetch_word Asan.M.loaded_segments (0x9b108 : word) = Some W_9b0b8.
Proof. vm_refl. Qed.
Lemma D_9b0b8 : decode_any W_9b0b8 = Some (Branch BC_GE 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0cc : bv 32 := 0x00956633.
Lemma F_9b0cc : fetch_word Asan.M.loaded_segments (0x9b11c : word) = Some W_9b0cc.
Proof. vm_refl. Qed.
Lemma D_9b0cc : decode_any W_9b0cc = Some (Op ALU_OR 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0d0 : bv 32 := 0x160426af.
Lemma F_9b0d0 : fetch_word Asan.M.loaded_segments (0x9b120 : word) = Some W_9b0d0.
Proof. vm_refl. Qed.
Lemma D_9b0d0 : decode_any W_9b0d0 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0d4 : bv 32 := 0x00a69663.
Lemma F_9b0d4 : fetch_word Asan.M.loaded_segments (0x9b124 : word) = Some W_9b0d4.
Proof. vm_refl. Qed.
Lemma D_9b0d4 : decode_any W_9b0d4 = Some (Branch BC_NE 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0d8 : bv 32 := 0x1ac4272f.
Lemma F_9b0d8 : fetch_word Asan.M.loaded_segments (0x9b128 : word) = Some W_9b0d8.
Proof. vm_refl. Qed.
Lemma D_9b0d8 : decode_any W_9b0d8 = Some (Sc AW false true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0dc : bv 32 := 0xfe071ae3.
Lemma F_9b0dc : fetch_word Asan.M.loaded_segments (0x9b12c : word) = Some W_9b0dc.
Proof. vm_refl. Qed.
Lemma D_9b0dc : decode_any W_9b0dc = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b0e0 : bv 32 := 0x02a68063.
Lemma F_9b0e0 : fetch_word Asan.M.loaded_segments (0x9b130 : word) = Some W_9b0e0.
Proof. vm_refl. Qed.
Lemma D_9b0e0 : decode_any W_9b0e0 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b100 : bv 32 := 0x02813083.
Lemma F_9b100 : fetch_word Asan.M.loaded_segments (0x9b150 : word) = Some W_9b100.
Proof. vm_refl. Qed.
Lemma D_9b100 : decode_any W_9b100 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b104 : bv 32 := 0x02013403.
Lemma F_9b104 : fetch_word Asan.M.loaded_segments (0x9b154 : word) = Some W_9b104.
Proof. vm_refl. Qed.
Lemma D_9b104 : decode_any W_9b104 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b108 : bv 32 := 0x01813483.
Lemma F_9b108 : fetch_word Asan.M.loaded_segments (0x9b158 : word) = Some W_9b108.
Proof. vm_refl. Qed.
Lemma D_9b108 : decode_any W_9b108 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b10c : bv 32 := 0x01013903.
Lemma F_9b10c : fetch_word Asan.M.loaded_segments (0x9b15c : word) = Some W_9b10c.
Proof. vm_refl. Qed.
Lemma D_9b10c : decode_any W_9b10c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b110 : bv 32 := 0x00813983.
Lemma F_9b110 : fetch_word Asan.M.loaded_segments (0x9b160 : word) = Some W_9b110.
Proof. vm_refl. Qed.
Lemma D_9b110 : decode_any W_9b110 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b114 : bv 32 := 0x03010113.
Lemma F_9b114 : fetch_word Asan.M.loaded_segments (0x9b164 : word) = Some W_9b114.
Proof. vm_refl. Qed.
Lemma D_9b114 : decode_any W_9b114 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b118 : bv 32 := 0x00008067.
Lemma F_9b118 : fetch_word Asan.M.loaded_segments (0x9b168 : word) = Some W_9b118.
Proof. vm_refl. Qed.
Lemma D_9b118 : decode_any W_9b118 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
