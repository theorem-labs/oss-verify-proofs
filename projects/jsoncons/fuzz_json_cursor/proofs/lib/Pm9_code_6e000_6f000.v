(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6ea08 : bv 32 := 0x104240ef.
Lemma F_6ea08 : fetch_word AsanUbsan.M.loaded_segments (0x6ea50 : word) = Some W_6ea08.
Proof. vm_refl. Qed.
Lemma D_6ea08 : decode_any W_6ea08 = Some (Jal 1 147716, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea0c : bv 32 := 0x00150b93.
Lemma F_6ea0c : fetch_word AsanUbsan.M.loaded_segments (0x6ea54 : word) = Some W_6ea0c.
Proof. vm_refl. Qed.
Lemma D_6ea0c : decode_any W_6ea0c = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea10 : bv 32 := 0xfffb4513.
Lemma F_6ea10 : fetch_word AsanUbsan.M.loaded_segments (0x6ea58 : word) = Some W_6ea10.
Proof. vm_refl. Qed.
Lemma D_6ea10 : decode_any W_6ea10 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea14 : bv 32 := 0x25756e63.
Lemma F_6ea14 : fetch_word AsanUbsan.M.loaded_segments (0x6ea5c : word) = Some W_6ea14.
Proof. vm_refl. Qed.
Lemma D_6ea14 : decode_any W_6ea14 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea18 : bv 32 := 0xfbfb8513.
Lemma F_6ea18 : fetch_word AsanUbsan.M.loaded_segments (0x6ea60 : word) = Some W_6ea18.
Proof. vm_refl. Qed.
Lemma D_6ea18 : decode_any W_6ea18 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea1c : bv 32 := 0xfbf00593.
Lemma F_6ea1c : fetch_word AsanUbsan.M.loaded_segments (0x6ea64 : word) = Some W_6ea1c.
Proof. vm_refl. Qed.
Lemma D_6ea1c : decode_any W_6ea1c = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea20 : bv 32 := 0x2ca5f063.
Lemma F_6ea20 : fetch_word AsanUbsan.M.loaded_segments (0x6ea68 : word) = Some W_6ea20.
Proof. vm_refl. Qed.
Lemma D_6ea20 : decode_any W_6ea20 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea24 : bv 32 := 0x000e6517.
Lemma F_6ea24 : fetch_word AsanUbsan.M.loaded_segments (0x6ea6c : word) = Some W_6ea24.
Proof. vm_refl. Qed.
Lemma D_6ea24 : decode_any W_6ea24 = Some (Auipc 10 230, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea28 : bv 32 := 0xa9453503.
Lemma F_6ea28 : fetch_word AsanUbsan.M.loaded_segments (0x6ea70 : word) = Some W_6ea28.
Proof. vm_refl. Qed.
Lemma D_6ea28 : decode_any W_6ea28 = Some (Load SZ8 true 10 10 2708, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea2c : bv 32 := 0x017b0633.
Lemma F_6ea2c : fetch_word AsanUbsan.M.loaded_segments (0x6ea74 : word) = Some W_6ea2c.
Proof. vm_refl. Qed.
Lemma D_6ea2c : decode_any W_6ea2c = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea30 : bv 32 := 0x00053583.
Lemma F_6ea30 : fetch_word AsanUbsan.M.loaded_segments (0x6ea78 : word) = Some W_6ea30.
Proof. vm_refl. Qed.
Lemma D_6ea30 : decode_any W_6ea30 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea34 : bv 32 := 0x003b5513.
Lemma F_6ea34 : fetch_word AsanUbsan.M.loaded_segments (0x6ea7c : word) = Some W_6ea34.
Proof. vm_refl. Qed.
Lemma D_6ea34 : decode_any W_6ea34 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea38 : bv 32 := 0xfff60613.
Lemma F_6ea38 : fetch_word AsanUbsan.M.loaded_segments (0x6ea80 : word) = Some W_6ea38.
Proof. vm_refl. Qed.
Lemma D_6ea38 : decode_any W_6ea38 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea3c : bv 32 := 0x00365693.
Lemma F_6ea3c : fetch_word AsanUbsan.M.loaded_segments (0x6ea84 : word) = Some W_6ea3c.
Proof. vm_refl. Qed.
Lemma D_6ea3c : decode_any W_6ea3c = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea40 : bv 32 := 0x00a58533.
Lemma F_6ea40 : fetch_word AsanUbsan.M.loaded_segments (0x6ea88 : word) = Some W_6ea40.
Proof. vm_refl. Qed.
Lemma D_6ea40 : decode_any W_6ea40 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea44 : bv 32 := 0x00d585b3.
Lemma F_6ea44 : fetch_word AsanUbsan.M.loaded_segments (0x6ea8c : word) = Some W_6ea44.
Proof. vm_refl. Qed.
Lemma D_6ea44 : decode_any W_6ea44 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea48 : bv 32 := 0xff857693.
Lemma F_6ea48 : fetch_word AsanUbsan.M.loaded_segments (0x6ea90 : word) = Some W_6ea48.
Proof. vm_refl. Qed.
Lemma D_6ea48 : decode_any W_6ea48 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea4c : bv 32 := 0xff85f713.
Lemma F_6ea4c : fetch_word AsanUbsan.M.loaded_segments (0x6ea94 : word) = Some W_6ea4c.
Proof. vm_refl. Qed.
Lemma D_6ea4c : decode_any W_6ea4c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea50 : bv 32 := 0x0006b683.
Lemma F_6ea50 : fetch_word AsanUbsan.M.loaded_segments (0x6ea98 : word) = Some W_6ea50.
Proof. vm_refl. Qed.
Lemma D_6ea50 : decode_any W_6ea50 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea54 : bv 32 := 0x00073703.
Lemma F_6ea54 : fetch_word AsanUbsan.M.loaded_segments (0x6ea9c : word) = Some W_6ea54.
Proof. vm_refl. Qed.
Lemma D_6ea54 : decode_any W_6ea54 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea58 : bv 32 := 0x00d766b3.
Lemma F_6ea58 : fetch_word AsanUbsan.M.loaded_segments (0x6eaa0 : word) = Some W_6ea58.
Proof. vm_refl. Qed.
Lemma D_6ea58 : decode_any W_6ea58 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea5c : bv 32 := 0xf00688e3.
Lemma F_6ea5c : fetch_word AsanUbsan.M.loaded_segments (0x6eaa4 : word) = Some W_6ea5c.
Proof. vm_refl. Qed.
Lemma D_6ea5c : decode_any W_6ea5c = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea94 : bv 32 := 0x000b0513.
Lemma F_6ea94 : fetch_word AsanUbsan.M.loaded_segments (0x6eadc : word) = Some W_6ea94.
Proof. vm_refl. Qed.
Lemma D_6ea94 : decode_any W_6ea94 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea98 : bv 32 := 0x000b8593.
Lemma F_6ea98 : fetch_word AsanUbsan.M.loaded_segments (0x6eae0 : word) = Some W_6ea98.
Proof. vm_refl. Qed.
Lemma D_6ea98 : decode_any W_6ea98 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ea9c : bv 32 := 0x77d130ef.
Lemma F_6ea9c : fetch_word AsanUbsan.M.loaded_segments (0x6eae4 : word) = Some W_6ea9c.
Proof. vm_refl. Qed.
Lemma D_6ea9c : decode_any W_6ea9c = Some (Jal 1 81788, 4%Z).
Proof. vm_refl. Qed.

Definition W_6eaa0 : bv 32 := 0xec0506e3.
Lemma F_6eaa0 : fetch_word AsanUbsan.M.loaded_segments (0x6eae8 : word) = Some W_6eaa0.
Proof. vm_refl. Qed.
Lemma D_6eaa0 : decode_any W_6eaa0 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ece0 : bv 32 := 0xda0b9ae3.
Lemma F_6ece0 : fetch_word AsanUbsan.M.loaded_segments (0x6ed28 : word) = Some W_6ece0.
Proof. vm_refl. Qed.
Lemma D_6ece0 : decode_any W_6ece0 = Some (Branch BC_NE 23 0 7604, 4%Z).
Proof. vm_refl. Qed.

