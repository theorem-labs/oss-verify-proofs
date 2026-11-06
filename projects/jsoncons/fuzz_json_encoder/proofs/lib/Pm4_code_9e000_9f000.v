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
Definition W_9e128 : bv 32 := 0xfe010113.
Lemma F_9e128 : fetch_word Asan.M.loaded_segments (0x9e178 : word) = Some W_9e128.
Proof. vm_refl. Qed.
Lemma D_9e128 : decode_any W_9e128 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e12c : bv 32 := 0x00113c23.
Lemma F_9e12c : fetch_word Asan.M.loaded_segments (0x9e17c : word) = Some W_9e12c.
Proof. vm_refl. Qed.
Lemma D_9e12c : decode_any W_9e12c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e130 : bv 32 := 0x00813823.
Lemma F_9e130 : fetch_word Asan.M.loaded_segments (0x9e180 : word) = Some W_9e130.
Proof. vm_refl. Qed.
Lemma D_9e130 : decode_any W_9e130 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e134 : bv 32 := 0x00913423.
Lemma F_9e134 : fetch_word Asan.M.loaded_segments (0x9e184 : word) = Some W_9e134.
Proof. vm_refl. Qed.
Lemma D_9e134 : decode_any W_9e134 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e138 : bv 32 := 0x01213023.
Lemma F_9e138 : fetch_word Asan.M.loaded_segments (0x9e188 : word) = Some W_9e138.
Proof. vm_refl. Qed.
Lemma D_9e138 : decode_any W_9e138 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e13c : bv 32 := 0x00060413.
Lemma F_9e13c : fetch_word Asan.M.loaded_segments (0x9e18c : word) = Some W_9e13c.
Proof. vm_refl. Qed.
Lemma D_9e13c : decode_any W_9e13c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e140 : bv 32 := 0x00058493.
Lemma F_9e140 : fetch_word Asan.M.loaded_segments (0x9e190 : word) = Some W_9e140.
Proof. vm_refl. Qed.
Lemma D_9e140 : decode_any W_9e140 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e144 : bv 32 := 0x00058513.
Lemma F_9e144 : fetch_word Asan.M.loaded_segments (0x9e194 : word) = Some W_9e144.
Proof. vm_refl. Qed.
Lemma D_9e144 : decode_any W_9e144 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e148 : bv 32 := 0x00060593.
Lemma F_9e148 : fetch_word Asan.M.loaded_segments (0x9e198 : word) = Some W_9e148.
Proof. vm_refl. Qed.
Lemma D_9e148 : decode_any W_9e148 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e14c : bv 32 := 0x00068613.
Lemma F_9e14c : fetch_word Asan.M.loaded_segments (0x9e19c : word) = Some W_9e14c.
Proof. vm_refl. Qed.
Lemma D_9e14c : decode_any W_9e14c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e150 : bv 32 := 0xf19f70ef.
Lemma F_9e150 : fetch_word Asan.M.loaded_segments (0x9e1a0 : word) = Some W_9e150.
Proof. vm_refl. Qed.
Lemma D_9e150 : decode_any W_9e150 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e154 : bv 32 := 0x00050e63.
Lemma F_9e154 : fetch_word Asan.M.loaded_segments (0x9e1a4 : word) = Some W_9e154.
Proof. vm_refl. Qed.
Lemma D_9e154 : decode_any W_9e154 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e158 : bv 32 := 0x01813083.
Lemma F_9e158 : fetch_word Asan.M.loaded_segments (0x9e1a8 : word) = Some W_9e158.
Proof. vm_refl. Qed.
Lemma D_9e158 : decode_any W_9e158 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e15c : bv 32 := 0x01013403.
Lemma F_9e15c : fetch_word Asan.M.loaded_segments (0x9e1ac : word) = Some W_9e15c.
Proof. vm_refl. Qed.
Lemma D_9e15c : decode_any W_9e15c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e160 : bv 32 := 0x00813483.
Lemma F_9e160 : fetch_word Asan.M.loaded_segments (0x9e1b0 : word) = Some W_9e160.
Proof. vm_refl. Qed.
Lemma D_9e160 : decode_any W_9e160 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e164 : bv 32 := 0x00013903.
Lemma F_9e164 : fetch_word Asan.M.loaded_segments (0x9e1b4 : word) = Some W_9e164.
Proof. vm_refl. Qed.
Lemma D_9e164 : decode_any W_9e164 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e168 : bv 32 := 0x02010113.
Lemma F_9e168 : fetch_word Asan.M.loaded_segments (0x9e1b8 : word) = Some W_9e168.
Proof. vm_refl. Qed.
Lemma D_9e168 : decode_any W_9e168 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e16c : bv 32 := 0x00008067.
Lemma F_9e16c : fetch_word Asan.M.loaded_segments (0x9e1bc : word) = Some W_9e16c.
Proof. vm_refl. Qed.
Lemma D_9e16c : decode_any W_9e16c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e274 : bv 32 := 0x00058513.
Lemma F_9e274 : fetch_word Asan.M.loaded_segments (0x9e2c4 : word) = Some W_9e274.
Proof. vm_refl. Qed.
Lemma D_9e274 : decode_any W_9e274 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e278 : bv 32 := 0x00060593.
Lemma F_9e278 : fetch_word Asan.M.loaded_segments (0x9e2c8 : word) = Some W_9e278.
Proof. vm_refl. Qed.
Lemma D_9e278 : decode_any W_9e278 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e27c : bv 32 := 0x00068613.
Lemma F_9e27c : fetch_word Asan.M.loaded_segments (0x9e2cc : word) = Some W_9e27c.
Proof. vm_refl. Qed.
Lemma D_9e27c : decode_any W_9e27c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e280 : bv 32 := 0xc65f706f.
Lemma F_9e280 : fetch_word Asan.M.loaded_segments (0x9e2d0 : word) = Some W_9e280.
Proof. vm_refl. Qed.
Lemma D_9e280 : decode_any W_9e280 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.

