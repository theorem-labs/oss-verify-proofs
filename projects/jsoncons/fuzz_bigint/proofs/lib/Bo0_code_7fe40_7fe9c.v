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

Definition W_7fe40 : bv 32 := 0xfe010113.
Lemma F_7fe40 : fetch_word AsanUbsan.M.loaded_segments (0x7fe40 : word) = Some W_7fe40.
Proof. vm_refl. Qed.
Lemma D_7fe40 : decode_any W_7fe40 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe44 : bv 32 := 0x00113c23.
Lemma F_7fe44 : fetch_word AsanUbsan.M.loaded_segments (0x7fe44 : word) = Some W_7fe44.
Proof. vm_refl. Qed.
Lemma D_7fe44 : decode_any W_7fe44 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe48 : bv 32 := 0x00813823.
Lemma F_7fe48 : fetch_word AsanUbsan.M.loaded_segments (0x7fe48 : word) = Some W_7fe48.
Proof. vm_refl. Qed.
Lemma D_7fe48 : decode_any W_7fe48 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe4c : bv 32 := 0x00060593.
Lemma F_7fe4c : fetch_word AsanUbsan.M.loaded_segments (0x7fe4c : word) = Some W_7fe4c.
Proof. vm_refl. Qed.
Lemma D_7fe4c : decode_any W_7fe4c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe50 : bv 32 := 0x00050413.
Lemma F_7fe50 : fetch_word AsanUbsan.M.loaded_segments (0x7fe50 : word) = Some W_7fe50.
Proof. vm_refl. Qed.
Lemma D_7fe50 : decode_any W_7fe50 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe54 : bv 32 := 0x00d53023.
Lemma F_7fe54 : fetch_word AsanUbsan.M.loaded_segments (0x7fe54 : word) = Some W_7fe54.
Proof. vm_refl. Qed.
Lemma D_7fe54 : decode_any W_7fe54 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe58 : bv 32 := 0x00013423.
Lemma F_7fe58 : fetch_word AsanUbsan.M.loaded_segments (0x7fe58 : word) = Some W_7fe58.
Proof. vm_refl. Qed.
Lemma D_7fe58 : decode_any W_7fe58 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe5c : bv 32 := 0x00130517.
Lemma F_7fe5c : fetch_word AsanUbsan.M.loaded_segments (0x7fe5c : word) = Some W_7fe5c.
Proof. vm_refl. Qed.
Lemma D_7fe5c : decode_any W_7fe5c = Some (Auipc 10 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe60 : bv 32 := 0x7ac50513.
Lemma F_7fe60 : fetch_word AsanUbsan.M.loaded_segments (0x7fe60 : word) = Some W_7fe60.
Proof. vm_refl. Qed.
Lemma D_7fe60 : decode_any W_7fe60 = Some (OpImm ALU_ADD 10 10 1964, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe64 : bv 32 := 0x00810613.
Lemma F_7fe64 : fetch_word AsanUbsan.M.loaded_segments (0x7fe64 : word) = Some W_7fe64.
Proof. vm_refl. Qed.
Lemma D_7fe64 : decode_any W_7fe64 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe68 : bv 32 := 0xcc5fd0ef.
Lemma F_7fe68 : fetch_word AsanUbsan.M.loaded_segments (0x7fe68 : word) = Some W_7fe68.
Proof. vm_refl. Qed.
Lemma D_7fe68 : decode_any W_7fe68 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe6c : bv 32 := 0x00813583.
Lemma F_7fe6c : fetch_word AsanUbsan.M.loaded_segments (0x7fe6c : word) = Some W_7fe6c.
Proof. vm_refl. Qed.
Lemma D_7fe6c : decode_any W_7fe6c = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe70 : bv 32 := 0x00a42623.
Lemma F_7fe70 : fetch_word AsanUbsan.M.loaded_segments (0x7fe70 : word) = Some W_7fe70.
Proof. vm_refl. Qed.
Lemma D_7fe70 : decode_any W_7fe70 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe74 : bv 32 := 0x00059a63.
Lemma F_7fe74 : fetch_word AsanUbsan.M.loaded_segments (0x7fe74 : word) = Some W_7fe74.
Proof. vm_refl. Qed.
Lemma D_7fe74 : decode_any W_7fe74 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe78 : bv 32 := 0x01813083.
Lemma F_7fe78 : fetch_word AsanUbsan.M.loaded_segments (0x7fe78 : word) = Some W_7fe78.
Proof. vm_refl. Qed.
Lemma D_7fe78 : decode_any W_7fe78 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe7c : bv 32 := 0x01013403.
Lemma F_7fe7c : fetch_word AsanUbsan.M.loaded_segments (0x7fe7c : word) = Some W_7fe7c.
Proof. vm_refl. Qed.
Lemma D_7fe7c : decode_any W_7fe7c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe80 : bv 32 := 0x02010113.
Lemma F_7fe80 : fetch_word AsanUbsan.M.loaded_segments (0x7fe80 : word) = Some W_7fe80.
Proof. vm_refl. Qed.
Lemma D_7fe80 : decode_any W_7fe80 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe84 : bv 32 := 0x00008067.
Lemma F_7fe84 : fetch_word AsanUbsan.M.loaded_segments (0x7fe84 : word) = Some W_7fe84.
Proof. vm_refl. Qed.
Lemma D_7fe84 : decode_any W_7fe84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe88 : bv 32 := 0x014000ef.
Lemma F_7fe88 : fetch_word AsanUbsan.M.loaded_segments (0x7fe88 : word) = Some W_7fe88.
Proof. vm_refl. Qed.
Lemma D_7fe88 : decode_any W_7fe88 = Some (Jal 1 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe8c : bv 32 := 0x01813083.
Lemma F_7fe8c : fetch_word AsanUbsan.M.loaded_segments (0x7fe8c : word) = Some W_7fe8c.
Proof. vm_refl. Qed.
Lemma D_7fe8c : decode_any W_7fe8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe90 : bv 32 := 0x01013403.
Lemma F_7fe90 : fetch_word AsanUbsan.M.loaded_segments (0x7fe90 : word) = Some W_7fe90.
Proof. vm_refl. Qed.
Lemma D_7fe90 : decode_any W_7fe90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe94 : bv 32 := 0x02010113.
Lemma F_7fe94 : fetch_word AsanUbsan.M.loaded_segments (0x7fe94 : word) = Some W_7fe94.
Proof. vm_refl. Qed.
Lemma D_7fe94 : decode_any W_7fe94 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fe98 : bv 32 := 0x00008067.
Lemma F_7fe98 : fetch_word AsanUbsan.M.loaded_segments (0x7fe98 : word) = Some W_7fe98.
Proof. vm_refl. Qed.
Lemma D_7fe98 : decode_any W_7fe98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
