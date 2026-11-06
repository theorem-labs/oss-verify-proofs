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

Definition W_68c30 : bv 32 := 0xff010113.
Lemma F_68c30 : fetch_word AsanUbsan.M.loaded_segments (0x68c30 : word) = Some W_68c30.
Proof. vm_refl. Qed.
Lemma D_68c30 : decode_any W_68c30 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c34 : bv 32 := 0x00113423.
Lemma F_68c34 : fetch_word AsanUbsan.M.loaded_segments (0x68c34 : word) = Some W_68c34.
Proof. vm_refl. Qed.
Lemma D_68c34 : decode_any W_68c34 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c38 : bv 32 := 0x62d000ef.
Lemma F_68c38 : fetch_word AsanUbsan.M.loaded_segments (0x68c38 : word) = Some W_68c38.
Proof. vm_refl. Qed.
Lemma D_68c38 : decode_any W_68c38 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c3c : bv 32 := 0x00050c63.
Lemma F_68c3c : fetch_word AsanUbsan.M.loaded_segments (0x68c3c : word) = Some W_68c3c.
Proof. vm_refl. Qed.
Lemma D_68c3c : decode_any W_68c3c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c40 : bv 32 := 0x7ff50513.
Lemma F_68c40 : fetch_word AsanUbsan.M.loaded_segments (0x68c40 : word) = Some W_68c40.
Proof. vm_refl. Qed.
Lemma D_68c40 : decode_any W_68c40 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c44 : bv 32 := 0x2f150513.
Lemma F_68c44 : fetch_word AsanUbsan.M.loaded_segments (0x68c44 : word) = Some W_68c44.
Proof. vm_refl. Qed.
Lemma D_68c44 : decode_any W_68c44 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c48 : bv 32 := 0x00813083.
Lemma F_68c48 : fetch_word AsanUbsan.M.loaded_segments (0x68c48 : word) = Some W_68c48.
Proof. vm_refl. Qed.
Lemma D_68c48 : decode_any W_68c48 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c4c : bv 32 := 0x01010113.
Lemma F_68c4c : fetch_word AsanUbsan.M.loaded_segments (0x68c4c : word) = Some W_68c4c.
Proof. vm_refl. Qed.
Lemma D_68c4c : decode_any W_68c4c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c50 : bv 32 := 0x00008067.
Lemma F_68c50 : fetch_word AsanUbsan.M.loaded_segments (0x68c50 : word) = Some W_68c50.
Proof. vm_refl. Qed.
Lemma D_68c50 : decode_any W_68c50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c54 : bv 32 := 0x00077517.
Lemma F_68c54 : fetch_word AsanUbsan.M.loaded_segments (0x68c54 : word) = Some W_68c54.
Proof. vm_refl. Qed.
Lemma D_68c54 : decode_any W_68c54 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c58 : bv 32 := 0x81450513.
Lemma F_68c58 : fetch_word AsanUbsan.M.loaded_segments (0x68c58 : word) = Some W_68c58.
Proof. vm_refl. Qed.
Lemma D_68c58 : decode_any W_68c58 = Some (OpImm ALU_ADD 10 10 2068, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c5c : bv 32 := 0x00813083.
Lemma F_68c5c : fetch_word AsanUbsan.M.loaded_segments (0x68c5c : word) = Some W_68c5c.
Proof. vm_refl. Qed.
Lemma D_68c5c : decode_any W_68c5c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c60 : bv 32 := 0x01010113.
Lemma F_68c60 : fetch_word AsanUbsan.M.loaded_segments (0x68c60 : word) = Some W_68c60.
Proof. vm_refl. Qed.
Lemma D_68c60 : decode_any W_68c60 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_68c64 : bv 32 := 0x00008067.
Lemma F_68c64 : fetch_word AsanUbsan.M.loaded_segments (0x68c64 : word) = Some W_68c64.
Proof. vm_refl. Qed.
Lemma D_68c64 : decode_any W_68c64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
