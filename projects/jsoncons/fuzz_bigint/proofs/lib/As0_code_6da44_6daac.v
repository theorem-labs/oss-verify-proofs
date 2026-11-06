(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6da44 : bv 32 := 0x00068597.
Lemma F_6da44 : fetch_word Asan.M.loaded_segments (0x6da44 : word) = Some W_6da44.
Proof. vm_refl. Qed.
Lemma D_6da44 : decode_any W_6da44 = Some (Auipc 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da48 : bv 32 := 0xe645b583.
Lemma F_6da48 : fetch_word Asan.M.loaded_segments (0x6da48 : word) = Some W_6da48.
Proof. vm_refl. Qed.
Lemma D_6da48 : decode_any W_6da48 = Some (Load SZ8 true 11 11 3684, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da4c : bv 32 := 0x0905b583.
Lemma F_6da4c : fetch_word Asan.M.loaded_segments (0x6da4c : word) = Some W_6da4c.
Proof. vm_refl. Qed.
Lemma D_6da4c : decode_any W_6da4c = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da50 : bv 32 := 0x00058e63.
Lemma F_6da50 : fetch_word Asan.M.loaded_segments (0x6da50 : word) = Some W_6da50.
Proof. vm_refl. Qed.
Lemma D_6da50 : decode_any W_6da50 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da54 : bv 32 := 0x00100617.
Lemma F_6da54 : fetch_word Asan.M.loaded_segments (0x6da54 : word) = Some W_6da54.
Proof. vm_refl. Qed.
Lemma D_6da54 : decode_any W_6da54 = Some (Auipc 12 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da58 : bv 32 := 0xba460613.
Lemma F_6da58 : fetch_word Asan.M.loaded_segments (0x6da58 : word) = Some W_6da58.
Proof. vm_refl. Qed.
Lemma D_6da58 : decode_any W_6da58 = Some (OpImm ALU_ADD 12 12 2980, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da5c : bv 32 := 0x00a6362f.
Lemma F_6da5c : fetch_word Asan.M.loaded_segments (0x6da5c : word) = Some W_6da5c.
Proof. vm_refl. Qed.
Lemma D_6da5c : decode_any W_6da5c = Some (Amo AMO_ADD AD false false 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da60 : bv 32 := 0x00a60533.
Lemma F_6da60 : fetch_word Asan.M.loaded_segments (0x6da60 : word) = Some W_6da60.
Proof. vm_refl. Qed.
Lemma D_6da60 : decode_any W_6da60 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da64 : bv 32 := 0x01455513.
Lemma F_6da64 : fetch_word Asan.M.loaded_segments (0x6da64 : word) = Some W_6da64.
Proof. vm_refl. Qed.
Lemma D_6da64 : decode_any W_6da64 = Some (ShiftImm ALU_SRL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da68 : bv 32 := 0x00b57463.
Lemma F_6da68 : fetch_word Asan.M.loaded_segments (0x6da68 : word) = Some W_6da68.
Proof. vm_refl. Qed.
Lemma D_6da68 : decode_any W_6da68 = Some (Branch BC_GEU 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da6c : bv 32 := 0x00008067.
Lemma F_6da6c : fetch_word Asan.M.loaded_segments (0x6da6c : word) = Some W_6da6c.
Proof. vm_refl. Qed.
Lemma D_6da6c : decode_any W_6da6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da70 : bv 32 := 0xff010113.
Lemma F_6da70 : fetch_word Asan.M.loaded_segments (0x6da70 : word) = Some W_6da70.
Proof. vm_refl. Qed.
Lemma D_6da70 : decode_any W_6da70 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da74 : bv 32 := 0x00113423.
Lemma F_6da74 : fetch_word Asan.M.loaded_segments (0x6da74 : word) = Some W_6da74.
Proof. vm_refl. Qed.
Lemma D_6da74 : decode_any W_6da74 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da78 : bv 32 := 0xfffa6517.
Lemma F_6da78 : fetch_word Asan.M.loaded_segments (0x6da78 : word) = Some W_6da78.
Proof. vm_refl. Qed.
Lemma D_6da78 : decode_any W_6da78 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da7c : bv 32 := 0xc3e50513.
Lemma F_6da7c : fetch_word Asan.M.loaded_segments (0x6da7c : word) = Some W_6da7c.
Proof. vm_refl. Qed.
Lemma D_6da7c : decode_any W_6da7c = Some (OpImm ALU_ADD 10 10 3134, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da80 : bv 32 := 0x794000ef.
Lemma F_6da80 : fetch_word Asan.M.loaded_segments (0x6da80 : word) = Some W_6da80.
Proof. vm_refl. Qed.
Lemma D_6da80 : decode_any W_6da80 = Some (Jal 1 1940, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da84 : bv 32 := 0x5180b0ef.
Lemma F_6da84 : fetch_word Asan.M.loaded_segments (0x6da84 : word) = Some W_6da84.
Proof. vm_refl. Qed.
Lemma D_6da84 : decode_any W_6da84 = Some (Jal 1 46360, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da88 : bv 32 := 0x00068597.
Lemma F_6da88 : fetch_word Asan.M.loaded_segments (0x6da88 : word) = Some W_6da88.
Proof. vm_refl. Qed.
Lemma D_6da88 : decode_any W_6da88 = Some (Auipc 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da8c : bv 32 := 0xe205b583.
Lemma F_6da8c : fetch_word Asan.M.loaded_segments (0x6da8c : word) = Some W_6da8c.
Proof. vm_refl. Qed.
Lemma D_6da8c : decode_any W_6da8c = Some (Load SZ8 true 11 11 3616, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da90 : bv 32 := 0x0905b583.
Lemma F_6da90 : fetch_word Asan.M.loaded_segments (0x6da90 : word) = Some W_6da90.
Proof. vm_refl. Qed.
Lemma D_6da90 : decode_any W_6da90 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da94 : bv 32 := 0x00058a63.
Lemma F_6da94 : fetch_word Asan.M.loaded_segments (0x6da94 : word) = Some W_6da94.
Proof. vm_refl. Qed.
Lemma D_6da94 : decode_any W_6da94 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da98 : bv 32 := 0x40a00533.
Lemma F_6da98 : fetch_word Asan.M.loaded_segments (0x6da98 : word) = Some W_6da98.
Proof. vm_refl. Qed.
Lemma D_6da98 : decode_any W_6da98 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6da9c : bv 32 := 0x00100597.
Lemma F_6da9c : fetch_word Asan.M.loaded_segments (0x6da9c : word) = Some W_6da9c.
Proof. vm_refl. Qed.
Lemma D_6da9c : decode_any W_6da9c = Some (Auipc 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daa0 : bv 32 := 0xb5c58593.
Lemma F_6daa0 : fetch_word Asan.M.loaded_segments (0x6daa0 : word) = Some W_6daa0.
Proof. vm_refl. Qed.
Lemma D_6daa0 : decode_any W_6daa0 = Some (OpImm ALU_ADD 11 11 2908, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daa4 : bv 32 := 0x00a5b02f.
Lemma F_6daa4 : fetch_word Asan.M.loaded_segments (0x6daa4 : word) = Some W_6daa4.
Proof. vm_refl. Qed.
Lemma D_6daa4 : decode_any W_6daa4 = Some (Amo AMO_ADD AD false false 0 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6daa8 : bv 32 := 0x00008067.
Lemma F_6daa8 : fetch_word Asan.M.loaded_segments (0x6daa8 : word) = Some W_6daa8.
Proof. vm_refl. Qed.
Lemma D_6daa8 : decode_any W_6daa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
