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
Definition W_8c004 : bv 32 := 0x02850583.
Lemma F_8c004 : fetch_word Asan.M.loaded_segments (0x8c054 : word) = Some W_8c004.
Proof. vm_refl. Qed.
Lemma D_8c004 : decode_any W_8c004 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c008 : bv 32 := 0x0230000f.
Lemma F_8c008 : fetch_word Asan.M.loaded_segments (0x8c058 : word) = Some W_8c008.
Proof. vm_refl. Qed.
Lemma D_8c008 : decode_any W_8c008 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c00c : bv 32 := 0x02058c63.
Lemma F_8c00c : fetch_word Asan.M.loaded_segments (0x8c05c : word) = Some W_8c00c.
Proof. vm_refl. Qed.
Lemma D_8c00c : decode_any W_8c00c = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c044 : bv 32 := 0x00853583.
Lemma F_8c044 : fetch_word Asan.M.loaded_segments (0x8c094 : word) = Some W_8c044.
Proof. vm_refl. Qed.
Lemma D_8c044 : decode_any W_8c044 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c048 : bv 32 := 0x01053503.
Lemma F_8c048 : fetch_word Asan.M.loaded_segments (0x8c098 : word) = Some W_8c048.
Proof. vm_refl. Qed.
Lemma D_8c048 : decode_any W_8c048 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c04c : bv 32 := 0x00b53533.
Lemma F_8c04c : fetch_word Asan.M.loaded_segments (0x8c09c : word) = Some W_8c04c.
Proof. vm_refl. Qed.
Lemma D_8c04c : decode_any W_8c04c = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c050 : bv 32 := 0x40a00533.
Lemma F_8c050 : fetch_word Asan.M.loaded_segments (0x8c0a0 : word) = Some W_8c050.
Proof. vm_refl. Qed.
Lemma D_8c050 : decode_any W_8c050 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c054 : bv 32 := 0x00b57533.
Lemma F_8c054 : fetch_word Asan.M.loaded_segments (0x8c0a4 : word) = Some W_8c054.
Proof. vm_refl. Qed.
Lemma D_8c054 : decode_any W_8c054 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c058 : bv 32 := 0x00008067.
Lemma F_8c058 : fetch_word Asan.M.loaded_segments (0x8c0a8 : word) = Some W_8c058.
Proof. vm_refl. Qed.
Lemma D_8c058 : decode_any W_8c058 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c05c : bv 32 := 0x02850583.
Lemma F_8c05c : fetch_word Asan.M.loaded_segments (0x8c0ac : word) = Some W_8c05c.
Proof. vm_refl. Qed.
Lemma D_8c05c : decode_any W_8c05c = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c060 : bv 32 := 0x0230000f.
Lemma F_8c060 : fetch_word Asan.M.loaded_segments (0x8c0b0 : word) = Some W_8c060.
Proof. vm_refl. Qed.
Lemma D_8c060 : decode_any W_8c060 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c064 : bv 32 := 0x02058c63.
Lemma F_8c064 : fetch_word Asan.M.loaded_segments (0x8c0b4 : word) = Some W_8c064.
Proof. vm_refl. Qed.
Lemma D_8c064 : decode_any W_8c064 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c09c : bv 32 := 0x00853583.
Lemma F_8c09c : fetch_word Asan.M.loaded_segments (0x8c0ec : word) = Some W_8c09c.
Proof. vm_refl. Qed.
Lemma D_8c09c : decode_any W_8c09c = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c0a0 : bv 32 := 0x01053503.
Lemma F_8c0a0 : fetch_word Asan.M.loaded_segments (0x8c0f0 : word) = Some W_8c0a0.
Proof. vm_refl. Qed.
Lemma D_8c0a0 : decode_any W_8c0a0 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c0a4 : bv 32 := 0x00b535b3.
Lemma F_8c0a4 : fetch_word Asan.M.loaded_segments (0x8c0f4 : word) = Some W_8c0a4.
Proof. vm_refl. Qed.
Lemma D_8c0a4 : decode_any W_8c0a4 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c0a8 : bv 32 := 0x40b005b3.
Lemma F_8c0a8 : fetch_word Asan.M.loaded_segments (0x8c0f8 : word) = Some W_8c0a8.
Proof. vm_refl. Qed.
Lemma D_8c0a8 : decode_any W_8c0a8 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c0ac : bv 32 := 0x00a5f533.
Lemma F_8c0ac : fetch_word Asan.M.loaded_segments (0x8c0fc : word) = Some W_8c0ac.
Proof. vm_refl. Qed.
Lemma D_8c0ac : decode_any W_8c0ac = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8c0b0 : bv 32 := 0x00008067.
Lemma F_8c0b0 : fetch_word Asan.M.loaded_segments (0x8c100 : word) = Some W_8c0b0.
Proof. vm_refl. Qed.
Lemma D_8c0b0 : decode_any W_8c0b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

