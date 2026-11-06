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
Definition W_735f0 : bv 32 := 0xfe010113.
Lemma F_735f0 : fetch_word Asan.M.loaded_segments (0x73640 : word) = Some W_735f0.
Proof. vm_refl. Qed.
Lemma D_735f0 : decode_any W_735f0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735f4 : bv 32 := 0x00113c23.
Lemma F_735f4 : fetch_word Asan.M.loaded_segments (0x73644 : word) = Some W_735f4.
Proof. vm_refl. Qed.
Lemma D_735f4 : decode_any W_735f4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735f8 : bv 32 := 0x00813823.
Lemma F_735f8 : fetch_word Asan.M.loaded_segments (0x73648 : word) = Some W_735f8.
Proof. vm_refl. Qed.
Lemma D_735f8 : decode_any W_735f8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_735fc : bv 32 := 0x00913423.
Lemma F_735fc : fetch_word Asan.M.loaded_segments (0x7364c : word) = Some W_735fc.
Proof. vm_refl. Qed.
Lemma D_735fc : decode_any W_735fc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73600 : bv 32 := 0x01213023.
Lemma F_73600 : fetch_word Asan.M.loaded_segments (0x73650 : word) = Some W_73600.
Proof. vm_refl. Qed.
Lemma D_73600 : decode_any W_73600 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73604 : bv 32 := 0x00050413.
Lemma F_73604 : fetch_word Asan.M.loaded_segments (0x73654 : word) = Some W_73604.
Proof. vm_refl. Qed.
Lemma D_73604 : decode_any W_73604 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73608 : bv 32 := 0x038160ef.
Lemma F_73608 : fetch_word Asan.M.loaded_segments (0x73658 : word) = Some W_73608.
Proof. vm_refl. Qed.
Lemma D_73608 : decode_any W_73608 = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7360c : bv 32 := 0x000ef597.
Lemma F_7360c : fetch_word Asan.M.loaded_segments (0x7365c : word) = Some W_7360c.
Proof. vm_refl. Qed.
Lemma D_7360c : decode_any W_7360c = Some (Auipc 11 239, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73610 : bv 32 := 0x4e45b583.
Lemma F_73610 : fetch_word Asan.M.loaded_segments (0x73660 : word) = Some W_73610.
Proof. vm_refl. Qed.
Lemma D_73610 : decode_any W_73610 = Some (Load SZ8 true 11 11 1252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73614 : bv 32 := 0x00050913.
Lemma F_73614 : fetch_word Asan.M.loaded_segments (0x73664 : word) = Some W_73614.
Proof. vm_refl. Qed.
Lemma D_73614 : decode_any W_73614 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73618 : bv 32 := 0x00040513.
Lemma F_73618 : fetch_word Asan.M.loaded_segments (0x73668 : word) = Some W_73618.
Proof. vm_refl. Qed.
Lemma D_73618 : decode_any W_73618 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7361c : bv 32 := 0x000580e7.
Lemma F_7361c : fetch_word Asan.M.loaded_segments (0x7366c : word) = Some W_7361c.
Proof. vm_refl. Qed.
Lemma D_7361c : decode_any W_7361c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73620 : bv 32 := 0x00050493.
Lemma F_73620 : fetch_word Asan.M.loaded_segments (0x73670 : word) = Some W_73620.
Proof. vm_refl. Qed.
Lemma D_73620 : decode_any W_73620 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73624 : bv 32 := 0x02090663.
Lemma F_73624 : fetch_word Asan.M.loaded_segments (0x73674 : word) = Some W_73624.
Proof. vm_refl. Qed.
Lemma D_73624 : decode_any W_73624 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73628 : bv 32 := 0x019180ef.
Lemma F_73628 : fetch_word Asan.M.loaded_segments (0x73678 : word) = Some W_73628.
Proof. vm_refl. Qed.
Lemma D_73628 : decode_any W_73628 = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7362c : bv 32 := 0x00050863.
Lemma F_7362c : fetch_word Asan.M.loaded_segments (0x7367c : word) = Some W_7362c.
Proof. vm_refl. Qed.
Lemma D_7362c : decode_any W_7362c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73630 : bv 32 := 0x03053603.
Lemma F_73630 : fetch_word Asan.M.loaded_segments (0x73680 : word) = Some W_73630.
Proof. vm_refl. Qed.
Lemma D_73630 : decode_any W_73630 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73634 : bv 32 := 0x03853683.
Lemma F_73634 : fetch_word Asan.M.loaded_segments (0x73684 : word) = Some W_73634.
Proof. vm_refl. Qed.
Lemma D_73634 : decode_any W_73634 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73638 : bv 32 := 0x00c0006f.
Lemma F_73638 : fetch_word Asan.M.loaded_segments (0x73688 : word) = Some W_73638.
Proof. vm_refl. Qed.
Lemma D_73638 : decode_any W_73638 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73644 : bv 32 := 0x00040513.
Lemma F_73644 : fetch_word Asan.M.loaded_segments (0x73694 : word) = Some W_73644.
Proof. vm_refl. Qed.
Lemma D_73644 : decode_any W_73644 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73648 : bv 32 := 0x00048593.
Lemma F_73648 : fetch_word Asan.M.loaded_segments (0x73698 : word) = Some W_73648.
Proof. vm_refl. Qed.
Lemma D_73648 : decode_any W_73648 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7364c : bv 32 := 0x725250ef.
Lemma F_7364c : fetch_word Asan.M.loaded_segments (0x7369c : word) = Some W_7364c.
Proof. vm_refl. Qed.
Lemma D_7364c : decode_any W_7364c = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73650 : bv 32 := 0x00048513.
Lemma F_73650 : fetch_word Asan.M.loaded_segments (0x736a0 : word) = Some W_73650.
Proof. vm_refl. Qed.
Lemma D_73650 : decode_any W_73650 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73654 : bv 32 := 0x01813083.
Lemma F_73654 : fetch_word Asan.M.loaded_segments (0x736a4 : word) = Some W_73654.
Proof. vm_refl. Qed.
Lemma D_73654 : decode_any W_73654 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73658 : bv 32 := 0x01013403.
Lemma F_73658 : fetch_word Asan.M.loaded_segments (0x736a8 : word) = Some W_73658.
Proof. vm_refl. Qed.
Lemma D_73658 : decode_any W_73658 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7365c : bv 32 := 0x00813483.
Lemma F_7365c : fetch_word Asan.M.loaded_segments (0x736ac : word) = Some W_7365c.
Proof. vm_refl. Qed.
Lemma D_7365c : decode_any W_7365c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73660 : bv 32 := 0x00013903.
Lemma F_73660 : fetch_word Asan.M.loaded_segments (0x736b0 : word) = Some W_73660.
Proof. vm_refl. Qed.
Lemma D_73660 : decode_any W_73660 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73664 : bv 32 := 0x02010113.
Lemma F_73664 : fetch_word Asan.M.loaded_segments (0x736b4 : word) = Some W_73664.
Proof. vm_refl. Qed.
Lemma D_73664 : decode_any W_73664 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73668 : bv 32 := 0x00008067.
Lemma F_73668 : fetch_word Asan.M.loaded_segments (0x736b8 : word) = Some W_73668.
Proof. vm_refl. Qed.
Lemma D_73668 : decode_any W_73668 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

