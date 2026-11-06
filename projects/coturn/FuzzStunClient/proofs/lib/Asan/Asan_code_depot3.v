(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_74a1c : bv 32 := 0xfe010113.
Lemma F_74a1c : fetch_word Asan.M.loaded_segments (0x74a1c : word) = Some W_74a1c.
Proof. vm_refl. Qed.
Lemma D_74a1c : decode_any W_74a1c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a20 : bv 32 := 0x00113c23.
Lemma F_74a20 : fetch_word Asan.M.loaded_segments (0x74a20 : word) = Some W_74a20.
Proof. vm_refl. Qed.
Lemma D_74a20 : decode_any W_74a20 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a24 : bv 32 := 0x00813823.
Lemma F_74a24 : fetch_word Asan.M.loaded_segments (0x74a24 : word) = Some W_74a24.
Proof. vm_refl. Qed.
Lemma D_74a24 : decode_any W_74a24 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a28 : bv 32 := 0x00060593.
Lemma F_74a28 : fetch_word Asan.M.loaded_segments (0x74a28 : word) = Some W_74a28.
Proof. vm_refl. Qed.
Lemma D_74a28 : decode_any W_74a28 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a2c : bv 32 := 0x00050413.
Lemma F_74a2c : fetch_word Asan.M.loaded_segments (0x74a2c : word) = Some W_74a2c.
Proof. vm_refl. Qed.
Lemma D_74a2c : decode_any W_74a2c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a30 : bv 32 := 0x00d53023.
Lemma F_74a30 : fetch_word Asan.M.loaded_segments (0x74a30 : word) = Some W_74a30.
Proof. vm_refl. Qed.
Lemma D_74a30 : decode_any W_74a30 = Some (Store SZ8 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a34 : bv 32 := 0x00013423.
Lemma F_74a34 : fetch_word Asan.M.loaded_segments (0x74a34 : word) = Some W_74a34.
Proof. vm_refl. Qed.
Lemma D_74a34 : decode_any W_74a34 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a38 : bv 32 := 0x00111517.
Lemma F_74a38 : fetch_word Asan.M.loaded_segments (0x74a38 : word) = Some W_74a38.
Proof. vm_refl. Qed.
Lemma D_74a38 : decode_any W_74a38 = Some (Auipc 10 273, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a3c : bv 32 := 0xa9050513.
Lemma F_74a3c : fetch_word Asan.M.loaded_segments (0x74a3c : word) = Some W_74a3c.
Proof. vm_refl. Qed.
Lemma D_74a3c : decode_any W_74a3c = Some (OpImm ALU_ADD 10 10 2704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a40 : bv 32 := 0x00810613.
Lemma F_74a40 : fetch_word Asan.M.loaded_segments (0x74a40 : word) = Some W_74a40.
Proof. vm_refl. Qed.
Lemma D_74a40 : decode_any W_74a40 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a44 : bv 32 := 0xcc5fd0ef.
Lemma F_74a44 : fetch_word Asan.M.loaded_segments (0x74a44 : word) = Some W_74a44.
Proof. vm_refl. Qed.
Lemma D_74a44 : decode_any W_74a44 = Some (Jal 1 2088132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a48 : bv 32 := 0x00813583.
Lemma F_74a48 : fetch_word Asan.M.loaded_segments (0x74a48 : word) = Some W_74a48.
Proof. vm_refl. Qed.
Lemma D_74a48 : decode_any W_74a48 = Some (Load SZ8 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a4c : bv 32 := 0x00a42623.
Lemma F_74a4c : fetch_word Asan.M.loaded_segments (0x74a4c : word) = Some W_74a4c.
Proof. vm_refl. Qed.
Lemma D_74a4c : decode_any W_74a4c = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a50 : bv 32 := 0x00059a63.
Lemma F_74a50 : fetch_word Asan.M.loaded_segments (0x74a50 : word) = Some W_74a50.
Proof. vm_refl. Qed.
Lemma D_74a50 : decode_any W_74a50 = Some (Branch BC_NE 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a54 : bv 32 := 0x01813083.
Lemma F_74a54 : fetch_word Asan.M.loaded_segments (0x74a54 : word) = Some W_74a54.
Proof. vm_refl. Qed.
Lemma D_74a54 : decode_any W_74a54 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a58 : bv 32 := 0x01013403.
Lemma F_74a58 : fetch_word Asan.M.loaded_segments (0x74a58 : word) = Some W_74a58.
Proof. vm_refl. Qed.
Lemma D_74a58 : decode_any W_74a58 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a5c : bv 32 := 0x02010113.
Lemma F_74a5c : fetch_word Asan.M.loaded_segments (0x74a5c : word) = Some W_74a5c.
Proof. vm_refl. Qed.
Lemma D_74a5c : decode_any W_74a5c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a60 : bv 32 := 0x00008067.
Lemma F_74a60 : fetch_word Asan.M.loaded_segments (0x74a60 : word) = Some W_74a60.
Proof. vm_refl. Qed.
Lemma D_74a60 : decode_any W_74a60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
