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
Definition W_a3508 : bv 32 := 0xfc010113.
Lemma F_a3508 : fetch_word Asan.M.loaded_segments (0xa3558 : word) = Some W_a3508.
Proof. vm_refl. Qed.
Lemma D_a3508 : decode_any W_a3508 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a350c : bv 32 := 0x02113c23.
Lemma F_a350c : fetch_word Asan.M.loaded_segments (0xa355c : word) = Some W_a350c.
Proof. vm_refl. Qed.
Lemma D_a350c : decode_any W_a350c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3510 : bv 32 := 0x02813823.
Lemma F_a3510 : fetch_word Asan.M.loaded_segments (0xa3560 : word) = Some W_a3510.
Proof. vm_refl. Qed.
Lemma D_a3510 : decode_any W_a3510 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3514 : bv 32 := 0x02913423.
Lemma F_a3514 : fetch_word Asan.M.loaded_segments (0xa3564 : word) = Some W_a3514.
Proof. vm_refl. Qed.
Lemma D_a3514 : decode_any W_a3514 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3518 : bv 32 := 0x03213023.
Lemma F_a3518 : fetch_word Asan.M.loaded_segments (0xa3568 : word) = Some W_a3518.
Proof. vm_refl. Qed.
Lemma D_a3518 : decode_any W_a3518 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a351c : bv 32 := 0x01313c23.
Lemma F_a351c : fetch_word Asan.M.loaded_segments (0xa356c : word) = Some W_a351c.
Proof. vm_refl. Qed.
Lemma D_a351c : decode_any W_a351c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3520 : bv 32 := 0x01413823.
Lemma F_a3520 : fetch_word Asan.M.loaded_segments (0xa3570 : word) = Some W_a3520.
Proof. vm_refl. Qed.
Lemma D_a3520 : decode_any W_a3520 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3524 : bv 32 := 0x01513423.
Lemma F_a3524 : fetch_word Asan.M.loaded_segments (0xa3574 : word) = Some W_a3524.
Proof. vm_refl. Qed.
Lemma D_a3524 : decode_any W_a3524 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3528 : bv 32 := 0x00058413.
Lemma F_a3528 : fetch_word Asan.M.loaded_segments (0xa3578 : word) = Some W_a3528.
Proof. vm_refl. Qed.
Lemma D_a3528 : decode_any W_a3528 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a352c : bv 32 := 0x0015b593.
Lemma F_a352c : fetch_word Asan.M.loaded_segments (0xa357c : word) = Some W_a352c.
Proof. vm_refl. Qed.
Lemma D_a352c : decode_any W_a352c = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3530 : bv 32 := 0x7ff50293.
Lemma F_a3530 : fetch_word Asan.M.loaded_segments (0xa3580 : word) = Some W_a3530.
Proof. vm_refl. Qed.
Lemma D_a3530 : decode_any W_a3530 = Some (OpImm ALU_ADD 5 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3534 : bv 32 := 0xfff58593.
Lemma F_a3534 : fetch_word Asan.M.loaded_segments (0xa3584 : word) = Some W_a3534.
Proof. vm_refl. Qed.
Lemma D_a3534 : decode_any W_a3534 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3538 : bv 32 := 0x00d5f333.
Lemma F_a3538 : fetch_word Asan.M.loaded_segments (0xa3588 : word) = Some W_a3538.
Proof. vm_refl. Qed.
Lemma D_a3538 : decode_any W_a3538 = Some (Op ALU_AND 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a353c : bv 32 := 0x00100593.
Lemma F_a353c : fetch_word Asan.M.loaded_segments (0xa358c : word) = Some W_a353c.
Proof. vm_refl. Qed.
Lemma D_a353c : decode_any W_a353c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3540 : bv 32 := 0x0062b4a3.
Lemma F_a3540 : fetch_word Asan.M.loaded_segments (0xa3590 : word) = Some W_a3540.
Proof. vm_refl. Qed.
Lemma D_a3540 : decode_any W_a3540 = Some (Store SZ8 5 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3544 : bv 32 := 0x00b40863.
Lemma F_a3544 : fetch_word Asan.M.loaded_segments (0xa3594 : word) = Some W_a3544.
Proof. vm_refl. Qed.
Lemma D_a3544 : decode_any W_a3544 = Some (Branch BC_EQ 8 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3548 : bv 32 := 0x02041c63.
Lemma F_a3548 : fetch_word Asan.M.loaded_segments (0xa3598 : word) = Some W_a3548.
Proof. vm_refl. Qed.
Lemma D_a3548 : decode_any W_a3548 = Some (Branch BC_NE 8 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3580 : bv 32 := 0x06089463.
Lemma F_a3580 : fetch_word Asan.M.loaded_segments (0xa35d0 : word) = Some W_a3580.
Proof. vm_refl. Qed.
Lemma D_a3580 : decode_any W_a3580 = Some (Branch BC_NE 17 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35e8 : bv 32 := 0x00060593.
Lemma F_a35e8 : fetch_word Asan.M.loaded_segments (0xa3638 : word) = Some W_a35e8.
Proof. vm_refl. Qed.
Lemma D_a35e8 : decode_any W_a35e8 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35ec : bv 32 := 0x00068613.
Lemma F_a35ec : fetch_word Asan.M.loaded_segments (0xa363c : word) = Some W_a35ec.
Proof. vm_refl. Qed.
Lemma D_a35ec : decode_any W_a35ec = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35f0 : bv 32 := 0x00078693.
Lemma F_a35f0 : fetch_word Asan.M.loaded_segments (0xa3640 : word) = Some W_a35f0.
Proof. vm_refl. Qed.
Lemma D_a35f0 : decode_any W_a35f0 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35f4 : bv 32 := 0x00080713.
Lemma F_a35f4 : fetch_word Asan.M.loaded_segments (0xa3644 : word) = Some W_a35f4.
Proof. vm_refl. Qed.
Lemma D_a35f4 : decode_any W_a35f4 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35f8 : bv 32 := 0x00040793.
Lemma F_a35f8 : fetch_word Asan.M.loaded_segments (0xa3648 : word) = Some W_a35f8.
Proof. vm_refl. Qed.
Lemma D_a35f8 : decode_any W_a35f8 = Some (OpImm ALU_ADD 15 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35fc : bv 32 := 0x03813083.
Lemma F_a35fc : fetch_word Asan.M.loaded_segments (0xa364c : word) = Some W_a35fc.
Proof. vm_refl. Qed.
Lemma D_a35fc : decode_any W_a35fc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3600 : bv 32 := 0x03013403.
Lemma F_a3600 : fetch_word Asan.M.loaded_segments (0xa3650 : word) = Some W_a3600.
Proof. vm_refl. Qed.
Lemma D_a3600 : decode_any W_a3600 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3604 : bv 32 := 0x02813483.
Lemma F_a3604 : fetch_word Asan.M.loaded_segments (0xa3654 : word) = Some W_a3604.
Proof. vm_refl. Qed.
Lemma D_a3604 : decode_any W_a3604 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3608 : bv 32 := 0x02013903.
Lemma F_a3608 : fetch_word Asan.M.loaded_segments (0xa3658 : word) = Some W_a3608.
Proof. vm_refl. Qed.
Lemma D_a3608 : decode_any W_a3608 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a360c : bv 32 := 0x01813983.
Lemma F_a360c : fetch_word Asan.M.loaded_segments (0xa365c : word) = Some W_a360c.
Proof. vm_refl. Qed.
Lemma D_a360c : decode_any W_a360c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3610 : bv 32 := 0x01013a03.
Lemma F_a3610 : fetch_word Asan.M.loaded_segments (0xa3660 : word) = Some W_a3610.
Proof. vm_refl. Qed.
Lemma D_a3610 : decode_any W_a3610 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3614 : bv 32 := 0x00813a83.
Lemma F_a3614 : fetch_word Asan.M.loaded_segments (0xa3664 : word) = Some W_a3614.
Proof. vm_refl. Qed.
Lemma D_a3614 : decode_any W_a3614 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3618 : bv 32 := 0x04010113.
Lemma F_a3618 : fetch_word Asan.M.loaded_segments (0xa3668 : word) = Some W_a3618.
Proof. vm_refl. Qed.
Lemma D_a3618 : decode_any W_a3618 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a361c : bv 32 := 0x891ff06f.
Lemma F_a361c : fetch_word Asan.M.loaded_segments (0xa366c : word) = Some W_a361c.
Proof. vm_refl. Qed.
Lemma D_a361c : decode_any W_a361c = Some (Jal 0 2095248, 4%Z).
Proof. vm_refl. Qed.

