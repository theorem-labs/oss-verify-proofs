(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6bfe4 : bv 32 := 0x000f5517.
Lemma F_6bfe4 : fetch_word AsanUbsan.M.loaded_segments (0x6bfe4 : word) = Some W_6bfe4.
Proof. vm_refl. Qed.
Lemma D_6bfe4 : decode_any W_6bfe4 = Some (Auipc 10 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfe8 : bv 32 := 0x00100593.
Lemma F_6bfe8 : fetch_word AsanUbsan.M.loaded_segments (0x6bfe8 : word) = Some W_6bfe8.
Proof. vm_refl. Qed.
Lemma D_6bfe8 : decode_any W_6bfe8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bfec : bv 32 := 0x9ab50e23.
Lemma F_6bfec : fetch_word AsanUbsan.M.loaded_segments (0x6bfec : word) = Some W_6bfec.
Proof. vm_refl. Qed.
Lemma D_6bfec : decode_any W_6bfec = Some (Store SZ1 10 11 2492, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bff0 : bv 32 := 0x00008067.
Lemma F_6bff0 : fetch_word AsanUbsan.M.loaded_segments (0x6bff0 : word) = Some W_6bff0.
Proof. vm_refl. Qed.
Lemma D_6bff0 : decode_any W_6bff0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bff4 : bv 32 := 0x000f5517.
Lemma F_6bff4 : fetch_word AsanUbsan.M.loaded_segments (0x6bff4 : word) = Some W_6bff4.
Proof. vm_refl. Qed.
Lemma D_6bff4 : decode_any W_6bff4 = Some (Auipc 10 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bff8 : bv 32 := 0x9ad50503.
Lemma F_6bff8 : fetch_word AsanUbsan.M.loaded_segments (0x6bff8 : word) = Some W_6bff8.
Proof. vm_refl. Qed.
Lemma D_6bff8 : decode_any W_6bff8 = Some (Load SZ1 true 10 10 2477, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bffc : bv 32 := 0x00a03533.
Lemma F_6bffc : fetch_word AsanUbsan.M.loaded_segments (0x6bffc : word) = Some W_6bffc.
Proof. vm_refl. Qed.
Lemma D_6bffc : decode_any W_6bffc = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c000 : bv 32 := 0x00008067.
Lemma F_6c000 : fetch_word AsanUbsan.M.loaded_segments (0x6c000 : word) = Some W_6c000.
Proof. vm_refl. Qed.
Lemma D_6c000 : decode_any W_6c000 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c004 : bv 32 := 0x000f5597.
Lemma F_6c004 : fetch_word AsanUbsan.M.loaded_segments (0x6c004 : word) = Some W_6c004.
Proof. vm_refl. Qed.
Lemma D_6c004 : decode_any W_6c004 = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c008 : bv 32 := 0x98a58ea3.
Lemma F_6c008 : fetch_word AsanUbsan.M.loaded_segments (0x6c008 : word) = Some W_6c008.
Proof. vm_refl. Qed.
Lemma D_6c008 : decode_any W_6c008 = Some (Store SZ1 11 10 2461, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c00c : bv 32 := 0x00008067.
Lemma F_6c00c : fetch_word AsanUbsan.M.loaded_segments (0x6c00c : word) = Some W_6c00c.
Proof. vm_refl. Qed.
Lemma D_6c00c : decode_any W_6c00c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c010 : bv 32 := 0xfffaa517.
Lemma F_6c010 : fetch_word AsanUbsan.M.loaded_segments (0x6c010 : word) = Some W_6c010.
Proof. vm_refl. Qed.
Lemma D_6c010 : decode_any W_6c010 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c014 : bv 32 := 0xbc450513.
Lemma F_6c014 : fetch_word AsanUbsan.M.loaded_segments (0x6c014 : word) = Some W_6c014.
Proof. vm_refl. Qed.
Lemma D_6c014 : decode_any W_6c014 = Some (OpImm ALU_ADD 10 10 3012, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c018 : bv 32 := 0x1f10806f.
Lemma F_6c018 : fetch_word AsanUbsan.M.loaded_segments (0x6c018 : word) = Some W_6c018.
Proof. vm_refl. Qed.
Lemma D_6c018 : decode_any W_6c018 = Some (Jal 0 35312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c01c : bv 32 := 0x000f5517.
Lemma F_6c01c : fetch_word AsanUbsan.M.loaded_segments (0x6c01c : word) = Some W_6c01c.
Proof. vm_refl. Qed.
Lemma D_6c01c : decode_any W_6c01c = Some (Auipc 10 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c020 : bv 32 := 0x98650503.
Lemma F_6c020 : fetch_word AsanUbsan.M.loaded_segments (0x6c020 : word) = Some W_6c020.
Proof. vm_refl. Qed.
Lemma D_6c020 : decode_any W_6c020 = Some (Load SZ1 true 10 10 2438, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c024 : bv 32 := 0x00a03533.
Lemma F_6c024 : fetch_word AsanUbsan.M.loaded_segments (0x6c024 : word) = Some W_6c024.
Proof. vm_refl. Qed.
Lemma D_6c024 : decode_any W_6c024 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c028 : bv 32 := 0x00008067.
Lemma F_6c028 : fetch_word AsanUbsan.M.loaded_segments (0x6c028 : word) = Some W_6c028.
Proof. vm_refl. Qed.
Lemma D_6c028 : decode_any W_6c028 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c02c : bv 32 := 0x000f5597.
Lemma F_6c02c : fetch_word AsanUbsan.M.loaded_segments (0x6c02c : word) = Some W_6c02c.
Proof. vm_refl. Qed.
Lemma D_6c02c : decode_any W_6c02c = Some (Auipc 11 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c030 : bv 32 := 0x96a58b23.
Lemma F_6c030 : fetch_word AsanUbsan.M.loaded_segments (0x6c030 : word) = Some W_6c030.
Proof. vm_refl. Qed.
Lemma D_6c030 : decode_any W_6c030 = Some (Store SZ1 11 10 2422, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c034 : bv 32 := 0x00008067.
Lemma F_6c034 : fetch_word AsanUbsan.M.loaded_segments (0x6c034 : word) = Some W_6c034.
Proof. vm_refl. Qed.
Lemma D_6c034 : decode_any W_6c034 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
