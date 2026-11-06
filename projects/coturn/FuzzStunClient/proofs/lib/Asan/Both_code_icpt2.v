(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_54c50 : bv 32 := 0x00070783.
Lemma F_54c50 : fetch_word AsanUbsan.M.loaded_segments (0x54c50 : word) = Some W_54c50.
Proof. vm_refl. Qed.
Lemma D_54c50 : decode_any W_54c50 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c54 : bv 32 := 0x007a7813.
Lemma F_54c54 : fetch_word AsanUbsan.M.loaded_segments (0x54c54 : word) = Some W_54c54.
Proof. vm_refl. Qed.
Lemma D_54c54 : decode_any W_54c54 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c58 : bv 32 := 0x00f038b3.
Lemma F_54c58 : fetch_word AsanUbsan.M.loaded_segments (0x54c58 : word) = Some W_54c58.
Proof. vm_refl. Qed.
Lemma D_54c58 : decode_any W_54c58 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c5c : bv 32 := 0x00f827b3.
Lemma F_54c5c : fetch_word AsanUbsan.M.loaded_segments (0x54c5c : word) = Some W_54c5c.
Proof. vm_refl. Qed.
Lemma D_54c5c : decode_any W_54c5c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c60 : bv 32 := 0x0017c793.
Lemma F_54c60 : fetch_word AsanUbsan.M.loaded_segments (0x54c60 : word) = Some W_54c60.
Proof. vm_refl. Qed.
Lemma D_54c60 : decode_any W_54c60 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c64 : bv 32 := 0x00f8f7b3.
Lemma F_54c64 : fetch_word AsanUbsan.M.loaded_segments (0x54c64 : word) = Some W_54c64.
Proof. vm_refl. Qed.
Lemma D_54c64 : decode_any W_54c64 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c68 : bv 32 := 0x00e6fa63.
Lemma F_54c68 : fetch_word AsanUbsan.M.loaded_segments (0x54c68 : word) = Some W_54c68.
Proof. vm_refl. Qed.
Lemma D_54c68 : decode_any W_54c68 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c6c : bv 32 := 0x0006c803.
Lemma F_54c6c : fetch_word AsanUbsan.M.loaded_segments (0x54c6c : word) = Some W_54c6c.
Proof. vm_refl. Qed.
Lemma D_54c6c : decode_any W_54c6c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c70 : bv 32 := 0x00168693.
Lemma F_54c70 : fetch_word AsanUbsan.M.loaded_segments (0x54c70 : word) = Some W_54c70.
Proof. vm_refl. Qed.
Lemma D_54c70 : decode_any W_54c70 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c74 : bv 32 := 0x00f867b3.
Lemma F_54c74 : fetch_word AsanUbsan.M.loaded_segments (0x54c74 : word) = Some W_54c74.
Proof. vm_refl. Qed.
Lemma D_54c74 : decode_any W_54c74 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c78 : bv 32 := 0xfee69ae3.
Lemma F_54c78 : fetch_word AsanUbsan.M.loaded_segments (0x54c78 : word) = Some W_54c78.
Proof. vm_refl. Qed.
Lemma D_54c78 : decode_any W_54c78 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c7c : bv 32 := 0x0ff7f693.
Lemma F_54c7c : fetch_word AsanUbsan.M.loaded_segments (0x54c7c : word) = Some W_54c7c.
Proof. vm_refl. Qed.
Lemma D_54c7c : decode_any W_54c7c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54c80 : bv 32 := 0xc60680e3.
Lemma F_54c80 : fetch_word AsanUbsan.M.loaded_segments (0x54c80 : word) = Some W_54c80.
Proof. vm_refl. Qed.
Lemma D_54c80 : decode_any W_54c80 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.
