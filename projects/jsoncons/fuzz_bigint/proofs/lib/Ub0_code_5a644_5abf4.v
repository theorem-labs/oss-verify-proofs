(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5a644 : bv 32 := 0x00050213.
Lemma F_5a644 : fetch_word Ubsan.M.loaded_segments (0x5a644 : word) = Some W_5a644.
Proof. vm_refl. Qed.
Lemma D_5a644 : decode_any W_5a644 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a648 : bv 32 := 0x00000513.
Lemma F_5a648 : fetch_word Ubsan.M.loaded_segments (0x5a648 : word) = Some W_5a648.
Proof. vm_refl. Qed.
Lemma D_5a648 : decode_any W_5a648 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a64c : bv 32 := 0x00008067.
Lemma F_5a64c : fetch_word Ubsan.M.loaded_segments (0x5a64c : word) = Some W_5a64c.
Proof. vm_refl. Qed.
Lemma D_5a64c : decode_any W_5a64c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab18 : bv 32 := 0xff010113.
Lemma F_5ab18 : fetch_word Ubsan.M.loaded_segments (0x5ab18 : word) = Some W_5ab18.
Proof. vm_refl. Qed.
Lemma D_5ab18 : decode_any W_5ab18 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab1c : bv 32 := 0x00113423.
Lemma F_5ab1c : fetch_word Ubsan.M.loaded_segments (0x5ab1c : word) = Some W_5ab1c.
Proof. vm_refl. Qed.
Lemma D_5ab1c : decode_any W_5ab1c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab20 : bv 32 := 0xe30f40ef.
Lemma F_5ab20 : fetch_word Ubsan.M.loaded_segments (0x5ab20 : word) = Some W_5ab20.
Proof. vm_refl. Qed.
Lemma D_5ab20 : decode_any W_5ab20 = Some (Jal 1 2049584, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab24 : bv 32 := 0x00050593.
Lemma F_5ab24 : fetch_word Ubsan.M.loaded_segments (0x5ab24 : word) = Some W_5ab24.
Proof. vm_refl. Qed.
Lemma D_5ab24 : decode_any W_5ab24 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab28 : bv 32 := 0x03900513.
Lemma F_5ab28 : fetch_word Ubsan.M.loaded_segments (0x5ab28 : word) = Some W_5ab28.
Proof. vm_refl. Qed.
Lemma D_5ab28 : decode_any W_5ab28 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab2c : bv 32 := 0x00000613.
Lemma F_5ab2c : fetch_word Ubsan.M.loaded_segments (0x5ab2c : word) = Some W_5ab2c.
Proof. vm_refl. Qed.
Lemma D_5ab2c : decode_any W_5ab2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab30 : bv 32 := 0x00000693.
Lemma F_5ab30 : fetch_word Ubsan.M.loaded_segments (0x5ab30 : word) = Some W_5ab30.
Proof. vm_refl. Qed.
Lemma D_5ab30 : decode_any W_5ab30 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab34 : bv 32 := 0x00000713.
Lemma F_5ab34 : fetch_word Ubsan.M.loaded_segments (0x5ab34 : word) = Some W_5ab34.
Proof. vm_refl. Qed.
Lemma D_5ab34 : decode_any W_5ab34 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab38 : bv 32 := 0x00000793.
Lemma F_5ab38 : fetch_word Ubsan.M.loaded_segments (0x5ab38 : word) = Some W_5ab38.
Proof. vm_refl. Qed.
Lemma D_5ab38 : decode_any W_5ab38 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab3c : bv 32 := 0x00000813.
Lemma F_5ab3c : fetch_word Ubsan.M.loaded_segments (0x5ab3c : word) = Some W_5ab3c.
Proof. vm_refl. Qed.
Lemma D_5ab3c : decode_any W_5ab3c = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab40 : bv 32 := 0xd04ff0ef.
Lemma F_5ab40 : fetch_word Ubsan.M.loaded_segments (0x5ab40 : word) = Some W_5ab40.
Proof. vm_refl. Qed.
Lemma D_5ab40 : decode_any W_5ab40 = Some (Jal 1 2094340, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab44 : bv 32 := 0x0005051b.
Lemma F_5ab44 : fetch_word Ubsan.M.loaded_segments (0x5ab44 : word) = Some W_5ab44.
Proof. vm_refl. Qed.
Lemma D_5ab44 : decode_any W_5ab44 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab48 : bv 32 := 0x00450593.
Lemma F_5ab48 : fetch_word Ubsan.M.loaded_segments (0x5ab48 : word) = Some W_5ab48.
Proof. vm_refl. Qed.
Lemma D_5ab48 : decode_any W_5ab48 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab4c : bv 32 := 0x0015b593.
Lemma F_5ab4c : fetch_word Ubsan.M.loaded_segments (0x5ab4c : word) = Some W_5ab4c.
Proof. vm_refl. Qed.
Lemma D_5ab4c : decode_any W_5ab4c = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab50 : bv 32 := 0xfff58593.
Lemma F_5ab50 : fetch_word Ubsan.M.loaded_segments (0x5ab50 : word) = Some W_5ab50.
Proof. vm_refl. Qed.
Lemma D_5ab50 : decode_any W_5ab50 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab54 : bv 32 := 0x00a5f533.
Lemma F_5ab54 : fetch_word Ubsan.M.loaded_segments (0x5ab54 : word) = Some W_5ab54.
Proof. vm_refl. Qed.
Lemma D_5ab54 : decode_any W_5ab54 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab58 : bv 32 := 0xdc0f10ef.
Lemma F_5ab58 : fetch_word Ubsan.M.loaded_segments (0x5ab58 : word) = Some W_5ab58.
Proof. vm_refl. Qed.
Lemma D_5ab58 : decode_any W_5ab58 = Some (Jal 1 2037184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab5c : bv 32 := 0x0005051b.
Lemma F_5ab5c : fetch_word Ubsan.M.loaded_segments (0x5ab5c : word) = Some W_5ab5c.
Proof. vm_refl. Qed.
Lemma D_5ab5c : decode_any W_5ab5c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab60 : bv 32 := 0x00813083.
Lemma F_5ab60 : fetch_word Ubsan.M.loaded_segments (0x5ab60 : word) = Some W_5ab60.
Proof. vm_refl. Qed.
Lemma D_5ab60 : decode_any W_5ab60 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab64 : bv 32 := 0x01010113.
Lemma F_5ab64 : fetch_word Ubsan.M.loaded_segments (0x5ab64 : word) = Some W_5ab64.
Proof. vm_refl. Qed.
Lemma D_5ab64 : decode_any W_5ab64 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab68 : bv 32 := 0x00008067.
Lemma F_5ab68 : fetch_word Ubsan.M.loaded_segments (0x5ab68 : word) = Some W_5ab68.
Proof. vm_refl. Qed.
Lemma D_5ab68 : decode_any W_5ab68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab78 : bv 32 := 0xff010113.
Lemma F_5ab78 : fetch_word Ubsan.M.loaded_segments (0x5ab78 : word) = Some W_5ab78.
Proof. vm_refl. Qed.
Lemma D_5ab78 : decode_any W_5ab78 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab7c : bv 32 := 0x00113423.
Lemma F_5ab7c : fetch_word Ubsan.M.loaded_segments (0x5ab7c : word) = Some W_5ab7c.
Proof. vm_refl. Qed.
Lemma D_5ab7c : decode_any W_5ab7c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab80 : bv 32 := 0x00060693.
Lemma F_5ab80 : fetch_word Ubsan.M.loaded_segments (0x5ab80 : word) = Some W_5ab80.
Proof. vm_refl. Qed.
Lemma D_5ab80 : decode_any W_5ab80 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab84 : bv 32 := 0x00058613.
Lemma F_5ab84 : fetch_word Ubsan.M.loaded_segments (0x5ab84 : word) = Some W_5ab84.
Proof. vm_refl. Qed.
Lemma D_5ab84 : decode_any W_5ab84 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab88 : bv 32 := 0x00050593.
Lemma F_5ab88 : fetch_word Ubsan.M.loaded_segments (0x5ab88 : word) = Some W_5ab88.
Proof. vm_refl. Qed.
Lemma D_5ab88 : decode_any W_5ab88 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab8c : bv 32 := 0x03f00513.
Lemma F_5ab8c : fetch_word Ubsan.M.loaded_segments (0x5ab8c : word) = Some W_5ab8c.
Proof. vm_refl. Qed.
Lemma D_5ab8c : decode_any W_5ab8c = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab90 : bv 32 := 0x00000713.
Lemma F_5ab90 : fetch_word Ubsan.M.loaded_segments (0x5ab90 : word) = Some W_5ab90.
Proof. vm_refl. Qed.
Lemma D_5ab90 : decode_any W_5ab90 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab94 : bv 32 := 0x00000793.
Lemma F_5ab94 : fetch_word Ubsan.M.loaded_segments (0x5ab94 : word) = Some W_5ab94.
Proof. vm_refl. Qed.
Lemma D_5ab94 : decode_any W_5ab94 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab98 : bv 32 := 0x00000813.
Lemma F_5ab98 : fetch_word Ubsan.M.loaded_segments (0x5ab98 : word) = Some W_5ab98.
Proof. vm_refl. Qed.
Lemma D_5ab98 : decode_any W_5ab98 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ab9c : bv 32 := 0xca8ff0ef.
Lemma F_5ab9c : fetch_word Ubsan.M.loaded_segments (0x5ab9c : word) = Some W_5ab9c.
Proof. vm_refl. Qed.
Lemma D_5ab9c : decode_any W_5ab9c = Some (Jal 1 2094248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aba0 : bv 32 := 0x00813083.
Lemma F_5aba0 : fetch_word Ubsan.M.loaded_segments (0x5aba0 : word) = Some W_5aba0.
Proof. vm_refl. Qed.
Lemma D_5aba0 : decode_any W_5aba0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aba4 : bv 32 := 0x01010113.
Lemma F_5aba4 : fetch_word Ubsan.M.loaded_segments (0x5aba4 : word) = Some W_5aba4.
Proof. vm_refl. Qed.
Lemma D_5aba4 : decode_any W_5aba4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5aba8 : bv 32 := 0xd70f106f.
Lemma F_5aba8 : fetch_word Ubsan.M.loaded_segments (0x5aba8 : word) = Some W_5aba8.
Proof. vm_refl. Qed.
Lemma D_5aba8 : decode_any W_5aba8 = Some (Jal 0 2037104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5abf0 : bv 32 := 0x00008067.
Lemma F_5abf0 : fetch_word Ubsan.M.loaded_segments (0x5abf0 : word) = Some W_5abf0.
Proof. vm_refl. Qed.
Lemma D_5abf0 : decode_any W_5abf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
