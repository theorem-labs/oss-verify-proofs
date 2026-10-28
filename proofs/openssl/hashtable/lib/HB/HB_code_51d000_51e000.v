(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_51d168 : bv 32 := 0xfffff5b7.
Lemma F_51d168 : fetch_word AsanUbsan.M.loaded_segments (0x555ce0 : word) = Some W_51d168.
Proof. vm_refl. Qed.
Lemma D_51d168 : decode_any W_51d168 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d16c : bv 32 := 0x0015859b.
Lemma F_51d16c : fetch_word AsanUbsan.M.loaded_segments (0x555ce4 : word) = Some W_51d16c.
Proof. vm_refl. Qed.
Lemma D_51d16c : decode_any W_51d16c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d170 : bv 32 := 0x02b56663.
Lemma F_51d170 : fetch_word AsanUbsan.M.loaded_segments (0x555ce8 : word) = Some W_51d170.
Proof. vm_refl. Qed.
Lemma D_51d170 : decode_any W_51d170 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d174 : bv 32 := 0xff010113.
Lemma F_51d174 : fetch_word AsanUbsan.M.loaded_segments (0x555cec : word) = Some W_51d174.
Proof. vm_refl. Qed.
Lemma D_51d174 : decode_any W_51d174 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d178 : bv 32 := 0x00113423.
Lemma F_51d178 : fetch_word AsanUbsan.M.loaded_segments (0x555cf0 : word) = Some W_51d178.
Proof. vm_refl. Qed.
Lemma D_51d178 : decode_any W_51d178 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d17c : bv 32 := 0x00813023.
Lemma F_51d17c : fetch_word AsanUbsan.M.loaded_segments (0x555cf4 : word) = Some W_51d17c.
Proof. vm_refl. Qed.
Lemma D_51d17c : decode_any W_51d17c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d180 : bv 32 := 0x40a0043b.
Lemma F_51d180 : fetch_word AsanUbsan.M.loaded_segments (0x555cf8 : word) = Some W_51d180.
Proof. vm_refl. Qed.
Lemma D_51d180 : decode_any W_51d180 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d184 : bv 32 := 0x97dff0ef.
Lemma F_51d184 : fetch_word AsanUbsan.M.loaded_segments (0x555cfc : word) = Some W_51d184.
Proof. vm_refl. Qed.
Lemma D_51d184 : decode_any W_51d184 = Some (Jal 1 2095484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d188 : bv 32 := 0x00852023.
Lemma F_51d188 : fetch_word AsanUbsan.M.loaded_segments (0x555d00 : word) = Some W_51d188.
Proof. vm_refl. Qed.
Lemma D_51d188 : decode_any W_51d188 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d18c : bv 32 := 0xfff00513.
Lemma F_51d18c : fetch_word AsanUbsan.M.loaded_segments (0x555d04 : word) = Some W_51d18c.
Proof. vm_refl. Qed.
Lemma D_51d18c : decode_any W_51d18c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d190 : bv 32 := 0x00813083.
Lemma F_51d190 : fetch_word AsanUbsan.M.loaded_segments (0x555d08 : word) = Some W_51d190.
Proof. vm_refl. Qed.
Lemma D_51d190 : decode_any W_51d190 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d194 : bv 32 := 0x00013403.
Lemma F_51d194 : fetch_word AsanUbsan.M.loaded_segments (0x555d0c : word) = Some W_51d194.
Proof. vm_refl. Qed.
Lemma D_51d194 : decode_any W_51d194 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d198 : bv 32 := 0x01010113.
Lemma F_51d198 : fetch_word AsanUbsan.M.loaded_segments (0x555d10 : word) = Some W_51d198.
Proof. vm_refl. Qed.
Lemma D_51d198 : decode_any W_51d198 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d19c : bv 32 := 0x00008067.
Lemma F_51d19c : fetch_word AsanUbsan.M.loaded_segments (0x555d14 : word) = Some W_51d19c.
Proof. vm_refl. Qed.
Lemma D_51d19c : decode_any W_51d19c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
