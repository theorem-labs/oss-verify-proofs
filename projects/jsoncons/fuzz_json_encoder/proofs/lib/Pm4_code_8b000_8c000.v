(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8b00c : bv 32 := 0xff010113.
Lemma F_8b00c : fetch_word Asan.M.loaded_segments (0x8b05c : word) = Some W_8b00c.
Proof. vm_refl. Qed.
Lemma D_8b00c : decode_any W_8b00c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b010 : bv 32 := 0x00113423.
Lemma F_8b010 : fetch_word Asan.M.loaded_segments (0x8b060 : word) = Some W_8b010.
Proof. vm_refl. Qed.
Lemma D_8b010 : decode_any W_8b010 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b014 : bv 32 := 0x62d000ef.
Lemma F_8b014 : fetch_word Asan.M.loaded_segments (0x8b064 : word) = Some W_8b014.
Proof. vm_refl. Qed.
Lemma D_8b014 : decode_any W_8b014 = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b018 : bv 32 := 0x00050c63.
Lemma F_8b018 : fetch_word Asan.M.loaded_segments (0x8b068 : word) = Some W_8b018.
Proof. vm_refl. Qed.
Lemma D_8b018 : decode_any W_8b018 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b01c : bv 32 := 0x7ff50513.
Lemma F_8b01c : fetch_word Asan.M.loaded_segments (0x8b06c : word) = Some W_8b01c.
Proof. vm_refl. Qed.
Lemma D_8b01c : decode_any W_8b01c = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b020 : bv 32 := 0x2f150513.
Lemma F_8b020 : fetch_word Asan.M.loaded_segments (0x8b070 : word) = Some W_8b020.
Proof. vm_refl. Qed.
Lemma D_8b020 : decode_any W_8b020 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b024 : bv 32 := 0x00813083.
Lemma F_8b024 : fetch_word Asan.M.loaded_segments (0x8b074 : word) = Some W_8b024.
Proof. vm_refl. Qed.
Lemma D_8b024 : decode_any W_8b024 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b028 : bv 32 := 0x01010113.
Lemma F_8b028 : fetch_word Asan.M.loaded_segments (0x8b078 : word) = Some W_8b028.
Proof. vm_refl. Qed.
Lemma D_8b028 : decode_any W_8b028 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8b02c : bv 32 := 0x00008067.
Lemma F_8b02c : fetch_word Asan.M.loaded_segments (0x8b07c : word) = Some W_8b02c.
Proof. vm_refl. Qed.
Lemma D_8b02c : decode_any W_8b02c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be40 : bv 32 := 0xff010113.
Lemma F_8be40 : fetch_word Asan.M.loaded_segments (0x8be90 : word) = Some W_8be40.
Proof. vm_refl. Qed.
Lemma D_8be40 : decode_any W_8be40 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be44 : bv 32 := 0x00113423.
Lemma F_8be44 : fetch_word Asan.M.loaded_segments (0x8be94 : word) = Some W_8be44.
Proof. vm_refl. Qed.
Lemma D_8be44 : decode_any W_8be44 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be48 : bv 32 := 0xe78f80ef.
Lemma F_8be48 : fetch_word Asan.M.loaded_segments (0x8be98 : word) = Some W_8be48.
Proof. vm_refl. Qed.
Lemma D_8be48 : decode_any W_8be48 = Some (Jal 1 2066040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be4c : bv 32 := 0x00050463.
Lemma F_8be4c : fetch_word Asan.M.loaded_segments (0x8be9c : word) = Some W_8be4c.
Proof. vm_refl. Qed.
Lemma D_8be4c : decode_any W_8be4c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be50 : bv 32 := 0x09853503.
Lemma F_8be50 : fetch_word Asan.M.loaded_segments (0x8bea0 : word) = Some W_8be50.
Proof. vm_refl. Qed.
Lemma D_8be50 : decode_any W_8be50 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be54 : bv 32 := 0x00813083.
Lemma F_8be54 : fetch_word Asan.M.loaded_segments (0x8bea4 : word) = Some W_8be54.
Proof. vm_refl. Qed.
Lemma D_8be54 : decode_any W_8be54 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be58 : bv 32 := 0x01010113.
Lemma F_8be58 : fetch_word Asan.M.loaded_segments (0x8bea8 : word) = Some W_8be58.
Proof. vm_refl. Qed.
Lemma D_8be58 : decode_any W_8be58 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8be5c : bv 32 := 0x00008067.
Lemma F_8be5c : fetch_word Asan.M.loaded_segments (0x8beac : word) = Some W_8be5c.
Proof. vm_refl. Qed.
Lemma D_8be5c : decode_any W_8be5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

