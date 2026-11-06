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

Definition W_9c5d4 : bv 32 := 0xfe010113.
Lemma F_9c5d4 : fetch_word AsanUbsan.M.loaded_segments (0x9c61c : word) = Some W_9c5d4.
Proof. vm_refl. Qed.
Lemma D_9c5d4 : decode_any W_9c5d4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5d8 : bv 32 := 0x00113c23.
Lemma F_9c5d8 : fetch_word AsanUbsan.M.loaded_segments (0x9c620 : word) = Some W_9c5d8.
Proof. vm_refl. Qed.
Lemma D_9c5d8 : decode_any W_9c5d8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5dc : bv 32 := 0x00813823.
Lemma F_9c5dc : fetch_word AsanUbsan.M.loaded_segments (0x9c624 : word) = Some W_9c5dc.
Proof. vm_refl. Qed.
Lemma D_9c5dc : decode_any W_9c5dc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5e0 : bv 32 := 0x00913423.
Lemma F_9c5e0 : fetch_word AsanUbsan.M.loaded_segments (0x9c628 : word) = Some W_9c5e0.
Proof. vm_refl. Qed.
Lemma D_9c5e0 : decode_any W_9c5e0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5e4 : bv 32 := 0x01213023.
Lemma F_9c5e4 : fetch_word AsanUbsan.M.loaded_segments (0x9c62c : word) = Some W_9c5e4.
Proof. vm_refl. Qed.
Lemma D_9c5e4 : decode_any W_9c5e4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5e8 : bv 32 := 0x00058413.
Lemma F_9c5e8 : fetch_word AsanUbsan.M.loaded_segments (0x9c630 : word) = Some W_9c5e8.
Proof. vm_refl. Qed.
Lemma D_9c5e8 : decode_any W_9c5e8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5ec : bv 32 := 0x000b8597.
Lemma F_9c5ec : fetch_word AsanUbsan.M.loaded_segments (0x9c634 : word) = Some W_9c5ec.
Proof. vm_refl. Qed.
Lemma D_9c5ec : decode_any W_9c5ec = Some (Auipc 11 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5f0 : bv 32 := 0xeac5b903.
Lemma F_9c5f0 : fetch_word AsanUbsan.M.loaded_segments (0x9c638 : word) = Some W_9c5f0.
Proof. vm_refl. Qed.
Lemma D_9c5f0 : decode_any W_9c5f0 = Some (Load SZ8 true 18 11 3756, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5f4 : bv 32 := 0x00093583.
Lemma F_9c5f4 : fetch_word AsanUbsan.M.loaded_segments (0x9c63c : word) = Some W_9c5f4.
Proof. vm_refl. Qed.
Lemma D_9c5f4 : decode_any W_9c5f4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5f8 : bv 32 := 0x00050493.
Lemma F_9c5f8 : fetch_word AsanUbsan.M.loaded_segments (0x9c640 : word) = Some W_9c5f8.
Proof. vm_refl. Qed.
Lemma D_9c5f8 : decode_any W_9c5f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c5fc : bv 32 := 0x00059863.
Lemma F_9c5fc : fetch_word AsanUbsan.M.loaded_segments (0x9c644 : word) = Some W_9c5fc.
Proof. vm_refl. Qed.
Lemma D_9c5fc : decode_any W_9c5fc = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c60c : bv 32 := 0xfff58513.
Lemma F_9c60c : fetch_word AsanUbsan.M.loaded_segments (0x9c654 : word) = Some W_9c60c.
Proof. vm_refl. Qed.
Lemma D_9c60c : decode_any W_9c60c = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c610 : bv 32 := 0x00a5f533.
Lemma F_9c610 : fetch_word AsanUbsan.M.loaded_segments (0x9c658 : word) = Some W_9c610.
Proof. vm_refl. Qed.
Lemma D_9c610 : decode_any W_9c610 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c614 : bv 32 := 0x04051a63.
Lemma F_9c614 : fetch_word AsanUbsan.M.loaded_segments (0x9c65c : word) = Some W_9c614.
Proof. vm_refl. Qed.
Lemma D_9c614 : decode_any W_9c614 = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c618 : bv 32 := 0x00b484b3.
Lemma F_9c618 : fetch_word AsanUbsan.M.loaded_segments (0x9c660 : word) = Some W_9c618.
Proof. vm_refl. Qed.
Lemma D_9c618 : decode_any W_9c618 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c61c : bv 32 := 0x40b005b3.
Lemma F_9c61c : fetch_word AsanUbsan.M.loaded_segments (0x9c664 : word) = Some W_9c61c.
Proof. vm_refl. Qed.
Lemma D_9c61c : decode_any W_9c61c = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c620 : bv 32 := 0xfff48513.
Lemma F_9c620 : fetch_word AsanUbsan.M.loaded_segments (0x9c668 : word) = Some W_9c620.
Proof. vm_refl. Qed.
Lemma D_9c620 : decode_any W_9c620 = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c624 : bv 32 := 0x00b57533.
Lemma F_9c624 : fetch_word AsanUbsan.M.loaded_segments (0x9c66c : word) = Some W_9c624.
Proof. vm_refl. Qed.
Lemma D_9c624 : decode_any W_9c624 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c628 : bv 32 := 0x00b475b3.
Lemma F_9c628 : fetch_word AsanUbsan.M.loaded_segments (0x9c670 : word) = Some W_9c628.
Proof. vm_refl. Qed.
Lemma D_9c628 : decode_any W_9c628 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c62c : bv 32 := 0x02b57263.
Lemma F_9c62c : fetch_word AsanUbsan.M.loaded_segments (0x9c674 : word) = Some W_9c62c.
Proof. vm_refl. Qed.
Lemma D_9c62c : decode_any W_9c62c = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c630 : bv 32 := 0x40a585b3.
Lemma F_9c630 : fetch_word AsanUbsan.M.loaded_segments (0x9c678 : word) = Some W_9c630.
Proof. vm_refl. Qed.
Lemma D_9c630 : decode_any W_9c630 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c634 : bv 32 := 0x00400613.
Lemma F_9c634 : fetch_word AsanUbsan.M.loaded_segments (0x9c67c : word) = Some W_9c634.
Proof. vm_refl. Qed.
Lemma D_9c634 : decode_any W_9c634 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c638 : bv 32 := 0x01813083.
Lemma F_9c638 : fetch_word AsanUbsan.M.loaded_segments (0x9c680 : word) = Some W_9c638.
Proof. vm_refl. Qed.
Lemma D_9c638 : decode_any W_9c638 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c63c : bv 32 := 0x01013403.
Lemma F_9c63c : fetch_word AsanUbsan.M.loaded_segments (0x9c684 : word) = Some W_9c63c.
Proof. vm_refl. Qed.
Lemma D_9c63c : decode_any W_9c63c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c640 : bv 32 := 0x00813483.
Lemma F_9c640 : fetch_word AsanUbsan.M.loaded_segments (0x9c688 : word) = Some W_9c640.
Proof. vm_refl. Qed.
Lemma D_9c640 : decode_any W_9c640 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c644 : bv 32 := 0x00013903.
Lemma F_9c644 : fetch_word AsanUbsan.M.loaded_segments (0x9c68c : word) = Some W_9c644.
Proof. vm_refl. Qed.
Lemma D_9c644 : decode_any W_9c644 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c648 : bv 32 := 0x02010113.
Lemma F_9c648 : fetch_word AsanUbsan.M.loaded_segments (0x9c690 : word) = Some W_9c648.
Proof. vm_refl. Qed.
Lemma D_9c648 : decode_any W_9c648 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c64c : bv 32 := 0xbb1f606f.
Lemma F_9c64c : fetch_word AsanUbsan.M.loaded_segments (0x9c694 : word) = Some W_9c64c.
Proof. vm_refl. Qed.
Lemma D_9c64c : decode_any W_9c64c = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c650 : bv 32 := 0x01813083.
Lemma F_9c650 : fetch_word AsanUbsan.M.loaded_segments (0x9c698 : word) = Some W_9c650.
Proof. vm_refl. Qed.
Lemma D_9c650 : decode_any W_9c650 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c654 : bv 32 := 0x01013403.
Lemma F_9c654 : fetch_word AsanUbsan.M.loaded_segments (0x9c69c : word) = Some W_9c654.
Proof. vm_refl. Qed.
Lemma D_9c654 : decode_any W_9c654 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c658 : bv 32 := 0x00813483.
Lemma F_9c658 : fetch_word AsanUbsan.M.loaded_segments (0x9c6a0 : word) = Some W_9c658.
Proof. vm_refl. Qed.
Lemma D_9c658 : decode_any W_9c658 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c65c : bv 32 := 0x00013903.
Lemma F_9c65c : fetch_word AsanUbsan.M.loaded_segments (0x9c6a4 : word) = Some W_9c65c.
Proof. vm_refl. Qed.
Lemma D_9c65c : decode_any W_9c65c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c660 : bv 32 := 0x02010113.
Lemma F_9c660 : fetch_word AsanUbsan.M.loaded_segments (0x9c6a8 : word) = Some W_9c660.
Proof. vm_refl. Qed.
Lemma D_9c660 : decode_any W_9c660 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c664 : bv 32 := 0x00008067.
Lemma F_9c664 : fetch_word AsanUbsan.M.loaded_segments (0x9c6ac : word) = Some W_9c664.
Proof. vm_refl. Qed.
Lemma D_9c664 : decode_any W_9c664 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

