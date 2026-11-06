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
Definition W_84354 : bv 32 := 0xfb010113.
Lemma F_84354 : fetch_word Asan.M.loaded_segments (0x843a4 : word) = Some W_84354.
Proof. vm_refl. Qed.
Lemma D_84354 : decode_any W_84354 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84358 : bv 32 := 0x04113423.
Lemma F_84358 : fetch_word Asan.M.loaded_segments (0x843a8 : word) = Some W_84358.
Proof. vm_refl. Qed.
Lemma D_84358 : decode_any W_84358 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8435c : bv 32 := 0x04813023.
Lemma F_8435c : fetch_word Asan.M.loaded_segments (0x843ac : word) = Some W_8435c.
Proof. vm_refl. Qed.
Lemma D_8435c : decode_any W_8435c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84360 : bv 32 := 0x000dd517.
Lemma F_84360 : fetch_word Asan.M.loaded_segments (0x843b0 : word) = Some W_84360.
Proof. vm_refl. Qed.
Lemma D_84360 : decode_any W_84360 = Some (Auipc 10 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84364 : bv 32 := 0x8a853503.
Lemma F_84364 : fetch_word Asan.M.loaded_segments (0x843b4 : word) = Some W_84364.
Proof. vm_refl. Qed.
Lemma D_84364 : decode_any W_84364 = Some (Load SZ8 true 10 10 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84368 : bv 32 := 0x0a051463.
Lemma F_84368 : fetch_word Asan.M.loaded_segments (0x843b8 : word) = Some W_84368.
Proof. vm_refl. Qed.
Lemma D_84368 : decode_any W_84368 = Some (Branch BC_NE 10 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84410 : bv 32 := 0x00000513.
Lemma F_84410 : fetch_word Asan.M.loaded_segments (0x84460 : word) = Some W_84410.
Proof. vm_refl. Qed.
Lemma D_84410 : decode_any W_84410 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84414 : bv 32 := 0x04813083.
Lemma F_84414 : fetch_word Asan.M.loaded_segments (0x84464 : word) = Some W_84414.
Proof. vm_refl. Qed.
Lemma D_84414 : decode_any W_84414 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84418 : bv 32 := 0x04013403.
Lemma F_84418 : fetch_word Asan.M.loaded_segments (0x84468 : word) = Some W_84418.
Proof. vm_refl. Qed.
Lemma D_84418 : decode_any W_84418 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8441c : bv 32 := 0x05010113.
Lemma F_8441c : fetch_word Asan.M.loaded_segments (0x8446c : word) = Some W_8441c.
Proof. vm_refl. Qed.
Lemma D_8441c : decode_any W_8441c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_84420 : bv 32 := 0x00008067.
Lemma F_84420 : fetch_word Asan.M.loaded_segments (0x84470 : word) = Some W_84420.
Proof. vm_refl. Qed.
Lemma D_84420 : decode_any W_84420 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_844c0 : bv 32 := 0x000e5517.
Lemma F_844c0 : fetch_word Asan.M.loaded_segments (0x84510 : word) = Some W_844c0.
Proof. vm_refl. Qed.
Lemma D_844c0 : decode_any W_844c0 = Some (Auipc 10 229, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_844c4 : bv 32 := 0x25050513.
Lemma F_844c4 : fetch_word Asan.M.loaded_segments (0x84514 : word) = Some W_844c4.
Proof. vm_refl. Qed.
Lemma D_844c4 : decode_any W_844c4 = Some (OpImm ALU_ADD 10 10 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_844c8 : bv 32 := 0x00054583.
Lemma F_844c8 : fetch_word Asan.M.loaded_segments (0x84518 : word) = Some W_844c8.
Proof. vm_refl. Qed.
Lemma D_844c8 : decode_any W_844c8 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_844cc : bv 32 := 0x00058663.
Lemma F_844cc : fetch_word Asan.M.loaded_segments (0x8451c : word) = Some W_844cc.
Proof. vm_refl. Qed.
Lemma D_844cc : decode_any W_844cc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_844d0 : bv 32 := 0x00452503.
Lemma F_844d0 : fetch_word Asan.M.loaded_segments (0x84520 : word) = Some W_844d0.
Proof. vm_refl. Qed.
Lemma D_844d0 : decode_any W_844d0 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_844d4 : bv 32 := 0x1a8d106f.
Lemma F_844d4 : fetch_word Asan.M.loaded_segments (0x84524 : word) = Some W_844d4.
Proof. vm_refl. Qed.
Lemma D_844d4 : decode_any W_844d4 = Some (Jal 0 856488, 4%Z).
Proof. vm_refl. Qed.

