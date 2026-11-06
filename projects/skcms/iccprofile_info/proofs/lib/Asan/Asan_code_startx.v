(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8dc24 : bv 32 := 0x0004b503.
Lemma F_8dc24 : fetch_word Asan.M.loaded_segments (0x8dc24 : word) = Some W_8dc24.
Proof. vm_refl. Qed.
Lemma D_8dc24 : decode_any W_8dc24 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc28 : bv 32 := 0x00848493.
Lemma F_8dc28 : fetch_word Asan.M.loaded_segments (0x8dc28 : word) = Some W_8dc28.
Proof. vm_refl. Qed.
Lemma D_8dc28 : decode_any W_8dc28 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dc2c : bv 32 := 0xfe051ce3.
Lemma F_8dc2c : fetch_word Asan.M.loaded_segments (0x8dc2c : word) = Some W_8dc2c.
Proof. vm_refl. Qed.
Lemma D_8dc2c : decode_any W_8dc2c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dce0 : bv 32 := 0x00b53023.
Lemma F_8dce0 : fetch_word Asan.M.loaded_segments (0x8dce0 : word) = Some W_8dce0.
Proof. vm_refl. Qed.
Lemma D_8dce0 : decode_any W_8dce0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dce4 : bv 32 := 0x00158593.
Lemma F_8dce4 : fetch_word Asan.M.loaded_segments (0x8dce4 : word) = Some W_8dce4.
Proof. vm_refl. Qed.
Lemma D_8dce4 : decode_any W_8dce4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dce8 : bv 32 := 0xfff5c683.
Lemma F_8dce8 : fetch_word Asan.M.loaded_segments (0x8dce8 : word) = Some W_8dce8.
Proof. vm_refl. Qed.
Lemma D_8dce8 : decode_any W_8dce8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcec : bv 32 := 0xfec68ae3.
Lemma F_8dcec : fetch_word Asan.M.loaded_segments (0x8dcec : word) = Some W_8dcec.
Proof. vm_refl. Qed.
Lemma D_8dcec : decode_any W_8dcec = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dcf0 : bv 32 := 0xfe069ae3.
Lemma F_8dcf0 : fetch_word Asan.M.loaded_segments (0x8dcf0 : word) = Some W_8dcf0.
Proof. vm_refl. Qed.
Lemma D_8dcf0 : decode_any W_8dcf0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
