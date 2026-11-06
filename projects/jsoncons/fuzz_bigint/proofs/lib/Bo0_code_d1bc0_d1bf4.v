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

Definition W_d1bc0 : bv 32 := 0xff010113.
Lemma F_d1bc0 : fetch_word AsanUbsan.M.loaded_segments (0xd1bc0 : word) = Some W_d1bc0.
Proof. vm_refl. Qed.
Lemma D_d1bc0 : decode_any W_d1bc0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bc4 : bv 32 := 0x00113423.
Lemma F_d1bc4 : fetch_word AsanUbsan.M.loaded_segments (0xd1bc4 : word) = Some W_d1bc4.
Proof. vm_refl. Qed.
Lemma D_d1bc4 : decode_any W_d1bc4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bc8 : bv 32 := 0x00060693.
Lemma F_d1bc8 : fetch_word AsanUbsan.M.loaded_segments (0xd1bc8 : word) = Some W_d1bc8.
Proof. vm_refl. Qed.
Lemma D_d1bc8 : decode_any W_d1bc8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bcc : bv 32 := 0x00058613.
Lemma F_d1bcc : fetch_word AsanUbsan.M.loaded_segments (0xd1bcc : word) = Some W_d1bcc.
Proof. vm_refl. Qed.
Lemma D_d1bcc : decode_any W_d1bcc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bd0 : bv 32 := 0x00050593.
Lemma F_d1bd0 : fetch_word AsanUbsan.M.loaded_segments (0xd1bd0 : word) = Some W_d1bd0.
Proof. vm_refl. Qed.
Lemma D_d1bd0 : decode_any W_d1bd0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bd4 : bv 32 := 0x03f00513.
Lemma F_d1bd4 : fetch_word AsanUbsan.M.loaded_segments (0xd1bd4 : word) = Some W_d1bd4.
Proof. vm_refl. Qed.
Lemma D_d1bd4 : decode_any W_d1bd4 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bd8 : bv 32 := 0x00000713.
Lemma F_d1bd8 : fetch_word AsanUbsan.M.loaded_segments (0xd1bd8 : word) = Some W_d1bd8.
Proof. vm_refl. Qed.
Lemma D_d1bd8 : decode_any W_d1bd8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bdc : bv 32 := 0x00000793.
Lemma F_d1bdc : fetch_word AsanUbsan.M.loaded_segments (0xd1bdc : word) = Some W_d1bdc.
Proof. vm_refl. Qed.
Lemma D_d1bdc : decode_any W_d1bdc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1be0 : bv 32 := 0x00000813.
Lemma F_d1be0 : fetch_word AsanUbsan.M.loaded_segments (0xd1be0 : word) = Some W_d1be0.
Proof. vm_refl. Qed.
Lemma D_d1be0 : decode_any W_d1be0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1be4 : bv 32 := 0xcc8fb0ef.
Lemma F_d1be4 : fetch_word AsanUbsan.M.loaded_segments (0xd1be4 : word) = Some W_d1be4.
Proof. vm_refl. Qed.
Lemma D_d1be4 : decode_any W_d1be4 = Some (Jal 1 2077896, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1be8 : bv 32 := 0x00813083.
Lemma F_d1be8 : fetch_word AsanUbsan.M.loaded_segments (0xd1be8 : word) = Some W_d1be8.
Proof. vm_refl. Qed.
Lemma D_d1be8 : decode_any W_d1be8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bec : bv 32 := 0x01010113.
Lemma F_d1bec : fetch_word AsanUbsan.M.loaded_segments (0xd1bec : word) = Some W_d1bec.
Proof. vm_refl. Qed.
Lemma D_d1bec : decode_any W_d1bec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1bf0 : bv 32 := 0xfe0ec06f.
Lemma F_d1bf0 : fetch_word AsanUbsan.M.loaded_segments (0xd1bf0 : word) = Some W_d1bf0.
Proof. vm_refl. Qed.
Lemma D_d1bf0 : decode_any W_d1bf0 = Some (Jal 0 2017248, 4%Z).
Proof. vm_refl. Qed.
