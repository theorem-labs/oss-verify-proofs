(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_59544 : bv 32 := 0x00008067.
Lemma F_59544 : fetch_word Plain.M.loaded_segments (0x59544 : word) = Some W_59544.
Proof. vm_refl. Qed.
Lemma D_59544 : decode_any W_59544 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59548 : bv 32 := 0xfddff06f.
Lemma F_59548 : fetch_word Plain.M.loaded_segments (0x59548 : word) = Some W_59548.
Proof. vm_refl. Qed.
Lemma D_59548 : decode_any W_59548 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

Definition W_59b48 : bv 32 := 0x00050213.
Lemma F_59b48 : fetch_word Plain.M.loaded_segments (0x59b48 : word) = Some W_59b48.
Proof. vm_refl. Qed.
Lemma D_59b48 : decode_any W_59b48 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59b4c : bv 32 := 0x00000513.
Lemma F_59b4c : fetch_word Plain.M.loaded_segments (0x59b4c : word) = Some W_59b4c.
Proof. vm_refl. Qed.
Lemma D_59b4c : decode_any W_59b4c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_59b50 : bv 32 := 0x00008067.
Lemma F_59b50 : fetch_word Plain.M.loaded_segments (0x59b50 : word) = Some W_59b50.
Proof. vm_refl. Qed.
Lemma D_59b50 : decode_any W_59b50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a01c : bv 32 := 0xff010113.
Lemma F_5a01c : fetch_word Plain.M.loaded_segments (0x5a01c : word) = Some W_5a01c.
Proof. vm_refl. Qed.
Lemma D_5a01c : decode_any W_5a01c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a020 : bv 32 := 0x00113423.
Lemma F_5a020 : fetch_word Plain.M.loaded_segments (0x5a020 : word) = Some W_5a020.
Proof. vm_refl. Qed.
Lemma D_5a020 : decode_any W_5a020 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a024 : bv 32 := 0xe30f40ef.
Lemma F_5a024 : fetch_word Plain.M.loaded_segments (0x5a024 : word) = Some W_5a024.
Proof. vm_refl. Qed.
Lemma D_5a024 : decode_any W_5a024 = Some (Jal 1 2049584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a028 : bv 32 := 0x00050593.
Lemma F_5a028 : fetch_word Plain.M.loaded_segments (0x5a028 : word) = Some W_5a028.
Proof. vm_refl. Qed.
Lemma D_5a028 : decode_any W_5a028 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a02c : bv 32 := 0x03900513.
Lemma F_5a02c : fetch_word Plain.M.loaded_segments (0x5a02c : word) = Some W_5a02c.
Proof. vm_refl. Qed.
Lemma D_5a02c : decode_any W_5a02c = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a030 : bv 32 := 0x00000613.
Lemma F_5a030 : fetch_word Plain.M.loaded_segments (0x5a030 : word) = Some W_5a030.
Proof. vm_refl. Qed.
Lemma D_5a030 : decode_any W_5a030 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a034 : bv 32 := 0x00000693.
Lemma F_5a034 : fetch_word Plain.M.loaded_segments (0x5a034 : word) = Some W_5a034.
Proof. vm_refl. Qed.
Lemma D_5a034 : decode_any W_5a034 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a038 : bv 32 := 0x00000713.
Lemma F_5a038 : fetch_word Plain.M.loaded_segments (0x5a038 : word) = Some W_5a038.
Proof. vm_refl. Qed.
Lemma D_5a038 : decode_any W_5a038 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a03c : bv 32 := 0x00000793.
Lemma F_5a03c : fetch_word Plain.M.loaded_segments (0x5a03c : word) = Some W_5a03c.
Proof. vm_refl. Qed.
Lemma D_5a03c : decode_any W_5a03c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a040 : bv 32 := 0x00000813.
Lemma F_5a040 : fetch_word Plain.M.loaded_segments (0x5a040 : word) = Some W_5a040.
Proof. vm_refl. Qed.
Lemma D_5a040 : decode_any W_5a040 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a044 : bv 32 := 0xd04ff0ef.
Lemma F_5a044 : fetch_word Plain.M.loaded_segments (0x5a044 : word) = Some W_5a044.
Proof. vm_refl. Qed.
Lemma D_5a044 : decode_any W_5a044 = Some (Jal 1 2094340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a048 : bv 32 := 0x0005051b.
Lemma F_5a048 : fetch_word Plain.M.loaded_segments (0x5a048 : word) = Some W_5a048.
Proof. vm_refl. Qed.
Lemma D_5a048 : decode_any W_5a048 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a04c : bv 32 := 0x00450593.
Lemma F_5a04c : fetch_word Plain.M.loaded_segments (0x5a04c : word) = Some W_5a04c.
Proof. vm_refl. Qed.
Lemma D_5a04c : decode_any W_5a04c = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a050 : bv 32 := 0x0015b593.
Lemma F_5a050 : fetch_word Plain.M.loaded_segments (0x5a050 : word) = Some W_5a050.
Proof. vm_refl. Qed.
Lemma D_5a050 : decode_any W_5a050 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a054 : bv 32 := 0xfff58593.
Lemma F_5a054 : fetch_word Plain.M.loaded_segments (0x5a054 : word) = Some W_5a054.
Proof. vm_refl. Qed.
Lemma D_5a054 : decode_any W_5a054 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a058 : bv 32 := 0x00a5f533.
Lemma F_5a058 : fetch_word Plain.M.loaded_segments (0x5a058 : word) = Some W_5a058.
Proof. vm_refl. Qed.
Lemma D_5a058 : decode_any W_5a058 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a05c : bv 32 := 0xdc0f10ef.
Lemma F_5a05c : fetch_word Plain.M.loaded_segments (0x5a05c : word) = Some W_5a05c.
Proof. vm_refl. Qed.
Lemma D_5a05c : decode_any W_5a05c = Some (Jal 1 2037184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a060 : bv 32 := 0x0005051b.
Lemma F_5a060 : fetch_word Plain.M.loaded_segments (0x5a060 : word) = Some W_5a060.
Proof. vm_refl. Qed.
Lemma D_5a060 : decode_any W_5a060 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a064 : bv 32 := 0x00813083.
Lemma F_5a064 : fetch_word Plain.M.loaded_segments (0x5a064 : word) = Some W_5a064.
Proof. vm_refl. Qed.
Lemma D_5a064 : decode_any W_5a064 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a068 : bv 32 := 0x01010113.
Lemma F_5a068 : fetch_word Plain.M.loaded_segments (0x5a068 : word) = Some W_5a068.
Proof. vm_refl. Qed.
Lemma D_5a068 : decode_any W_5a068 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a06c : bv 32 := 0x00008067.
Lemma F_5a06c : fetch_word Plain.M.loaded_segments (0x5a06c : word) = Some W_5a06c.
Proof. vm_refl. Qed.
Lemma D_5a06c : decode_any W_5a06c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a07c : bv 32 := 0xff010113.
Lemma F_5a07c : fetch_word Plain.M.loaded_segments (0x5a07c : word) = Some W_5a07c.
Proof. vm_refl. Qed.
Lemma D_5a07c : decode_any W_5a07c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a080 : bv 32 := 0x00113423.
Lemma F_5a080 : fetch_word Plain.M.loaded_segments (0x5a080 : word) = Some W_5a080.
Proof. vm_refl. Qed.
Lemma D_5a080 : decode_any W_5a080 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a084 : bv 32 := 0x00060693.
Lemma F_5a084 : fetch_word Plain.M.loaded_segments (0x5a084 : word) = Some W_5a084.
Proof. vm_refl. Qed.
Lemma D_5a084 : decode_any W_5a084 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a088 : bv 32 := 0x00058613.
Lemma F_5a088 : fetch_word Plain.M.loaded_segments (0x5a088 : word) = Some W_5a088.
Proof. vm_refl. Qed.
Lemma D_5a088 : decode_any W_5a088 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a08c : bv 32 := 0x00050593.
Lemma F_5a08c : fetch_word Plain.M.loaded_segments (0x5a08c : word) = Some W_5a08c.
Proof. vm_refl. Qed.
Lemma D_5a08c : decode_any W_5a08c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a090 : bv 32 := 0x03f00513.
Lemma F_5a090 : fetch_word Plain.M.loaded_segments (0x5a090 : word) = Some W_5a090.
Proof. vm_refl. Qed.
Lemma D_5a090 : decode_any W_5a090 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a094 : bv 32 := 0x00000713.
Lemma F_5a094 : fetch_word Plain.M.loaded_segments (0x5a094 : word) = Some W_5a094.
Proof. vm_refl. Qed.
Lemma D_5a094 : decode_any W_5a094 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a098 : bv 32 := 0x00000793.
Lemma F_5a098 : fetch_word Plain.M.loaded_segments (0x5a098 : word) = Some W_5a098.
Proof. vm_refl. Qed.
Lemma D_5a098 : decode_any W_5a098 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a09c : bv 32 := 0x00000813.
Lemma F_5a09c : fetch_word Plain.M.loaded_segments (0x5a09c : word) = Some W_5a09c.
Proof. vm_refl. Qed.
Lemma D_5a09c : decode_any W_5a09c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a0a0 : bv 32 := 0xca8ff0ef.
Lemma F_5a0a0 : fetch_word Plain.M.loaded_segments (0x5a0a0 : word) = Some W_5a0a0.
Proof. vm_refl. Qed.
Lemma D_5a0a0 : decode_any W_5a0a0 = Some (Jal 1 2094248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a0a4 : bv 32 := 0x00813083.
Lemma F_5a0a4 : fetch_word Plain.M.loaded_segments (0x5a0a4 : word) = Some W_5a0a4.
Proof. vm_refl. Qed.
Lemma D_5a0a4 : decode_any W_5a0a4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a0a8 : bv 32 := 0x01010113.
Lemma F_5a0a8 : fetch_word Plain.M.loaded_segments (0x5a0a8 : word) = Some W_5a0a8.
Proof. vm_refl. Qed.
Lemma D_5a0a8 : decode_any W_5a0a8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a0ac : bv 32 := 0xd70f106f.
Lemma F_5a0ac : fetch_word Plain.M.loaded_segments (0x5a0ac : word) = Some W_5a0ac.
Proof. vm_refl. Qed.
Lemma D_5a0ac : decode_any W_5a0ac = Some (Jal 0 2037104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a0f4 : bv 32 := 0x00008067.
Lemma F_5a0f4 : fetch_word Plain.M.loaded_segments (0x5a0f4 : word) = Some W_5a0f4.
Proof. vm_refl. Qed.
Lemma D_5a0f4 : decode_any W_5a0f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
