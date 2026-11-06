(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9ea00 : bv 32 := 0xfe010113.
Lemma F_9ea00 : fetch_word AsanUbsan.M.loaded_segments (0x9ea48 : word) = Some W_9ea00.
Proof. vm_refl. Qed.
Lemma D_9ea00 : decode_any W_9ea00 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea04 : bv 32 := 0x00113c23.
Lemma F_9ea04 : fetch_word AsanUbsan.M.loaded_segments (0x9ea4c : word) = Some W_9ea04.
Proof. vm_refl. Qed.
Lemma D_9ea04 : decode_any W_9ea04 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea08 : bv 32 := 0x00813823.
Lemma F_9ea08 : fetch_word AsanUbsan.M.loaded_segments (0x9ea50 : word) = Some W_9ea08.
Proof. vm_refl. Qed.
Lemma D_9ea08 : decode_any W_9ea08 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea0c : bv 32 := 0x00913423.
Lemma F_9ea0c : fetch_word AsanUbsan.M.loaded_segments (0x9ea54 : word) = Some W_9ea0c.
Proof. vm_refl. Qed.
Lemma D_9ea0c : decode_any W_9ea0c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea10 : bv 32 := 0x01213023.
Lemma F_9ea10 : fetch_word AsanUbsan.M.loaded_segments (0x9ea58 : word) = Some W_9ea10.
Proof. vm_refl. Qed.
Lemma D_9ea10 : decode_any W_9ea10 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea14 : bv 32 := 0x00060413.
Lemma F_9ea14 : fetch_word AsanUbsan.M.loaded_segments (0x9ea5c : word) = Some W_9ea14.
Proof. vm_refl. Qed.
Lemma D_9ea14 : decode_any W_9ea14 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea18 : bv 32 := 0x00058493.
Lemma F_9ea18 : fetch_word AsanUbsan.M.loaded_segments (0x9ea60 : word) = Some W_9ea18.
Proof. vm_refl. Qed.
Lemma D_9ea18 : decode_any W_9ea18 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea1c : bv 32 := 0x00058513.
Lemma F_9ea1c : fetch_word AsanUbsan.M.loaded_segments (0x9ea64 : word) = Some W_9ea1c.
Proof. vm_refl. Qed.
Lemma D_9ea1c : decode_any W_9ea1c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea20 : bv 32 := 0x00060593.
Lemma F_9ea20 : fetch_word AsanUbsan.M.loaded_segments (0x9ea68 : word) = Some W_9ea20.
Proof. vm_refl. Qed.
Lemma D_9ea20 : decode_any W_9ea20 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea24 : bv 32 := 0x00068613.
Lemma F_9ea24 : fetch_word AsanUbsan.M.loaded_segments (0x9ea6c : word) = Some W_9ea24.
Proof. vm_refl. Qed.
Lemma D_9ea24 : decode_any W_9ea24 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea28 : bv 32 := 0xf19f70ef.
Lemma F_9ea28 : fetch_word AsanUbsan.M.loaded_segments (0x9ea70 : word) = Some W_9ea28.
Proof. vm_refl. Qed.
Lemma D_9ea28 : decode_any W_9ea28 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea2c : bv 32 := 0x00050e63.
Lemma F_9ea2c : fetch_word AsanUbsan.M.loaded_segments (0x9ea74 : word) = Some W_9ea2c.
Proof. vm_refl. Qed.
Lemma D_9ea2c : decode_any W_9ea2c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea30 : bv 32 := 0x01813083.
Lemma F_9ea30 : fetch_word AsanUbsan.M.loaded_segments (0x9ea78 : word) = Some W_9ea30.
Proof. vm_refl. Qed.
Lemma D_9ea30 : decode_any W_9ea30 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea34 : bv 32 := 0x01013403.
Lemma F_9ea34 : fetch_word AsanUbsan.M.loaded_segments (0x9ea7c : word) = Some W_9ea34.
Proof. vm_refl. Qed.
Lemma D_9ea34 : decode_any W_9ea34 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea38 : bv 32 := 0x00813483.
Lemma F_9ea38 : fetch_word AsanUbsan.M.loaded_segments (0x9ea80 : word) = Some W_9ea38.
Proof. vm_refl. Qed.
Lemma D_9ea38 : decode_any W_9ea38 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea3c : bv 32 := 0x00013903.
Lemma F_9ea3c : fetch_word AsanUbsan.M.loaded_segments (0x9ea84 : word) = Some W_9ea3c.
Proof. vm_refl. Qed.
Lemma D_9ea3c : decode_any W_9ea3c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea40 : bv 32 := 0x02010113.
Lemma F_9ea40 : fetch_word AsanUbsan.M.loaded_segments (0x9ea88 : word) = Some W_9ea40.
Proof. vm_refl. Qed.
Lemma D_9ea40 : decode_any W_9ea40 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ea44 : bv 32 := 0x00008067.
Lemma F_9ea44 : fetch_word AsanUbsan.M.loaded_segments (0x9ea8c : word) = Some W_9ea44.
Proof. vm_refl. Qed.
Lemma D_9ea44 : decode_any W_9ea44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eb4c : bv 32 := 0x00058513.
Lemma F_9eb4c : fetch_word AsanUbsan.M.loaded_segments (0x9eb94 : word) = Some W_9eb4c.
Proof. vm_refl. Qed.
Lemma D_9eb4c : decode_any W_9eb4c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eb50 : bv 32 := 0x00060593.
Lemma F_9eb50 : fetch_word AsanUbsan.M.loaded_segments (0x9eb98 : word) = Some W_9eb50.
Proof. vm_refl. Qed.
Lemma D_9eb50 : decode_any W_9eb50 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eb54 : bv 32 := 0x00068613.
Lemma F_9eb54 : fetch_word AsanUbsan.M.loaded_segments (0x9eb9c : word) = Some W_9eb54.
Proof. vm_refl. Qed.
Lemma D_9eb54 : decode_any W_9eb54 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eb58 : bv 32 := 0xc65f706f.
Lemma F_9eb58 : fetch_word AsanUbsan.M.loaded_segments (0x9eba0 : word) = Some W_9eb58.
Proof. vm_refl. Qed.
Lemma D_9eb58 : decode_any W_9eb58 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.

