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

Definition W_8f09c : bv 32 := 0x000c5597.
Lemma F_8f09c : fetch_word AsanUbsan.M.loaded_segments (0x8f0e4 : word) = Some W_8f09c.
Proof. vm_refl. Qed.
Lemma D_8f09c : decode_any W_8f09c = Some (Auipc 11 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0a0 : bv 32 := 0x40c5b583.
Lemma F_8f0a0 : fetch_word AsanUbsan.M.loaded_segments (0x8f0e8 : word) = Some W_8f0a0.
Proof. vm_refl. Qed.
Lemma D_8f0a0 : decode_any W_8f0a0 = Some (Load SZ8 true 11 11 1036, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0a4 : bv 32 := 0x0905b583.
Lemma F_8f0a4 : fetch_word AsanUbsan.M.loaded_segments (0x8f0ec : word) = Some W_8f0a4.
Proof. vm_refl. Qed.
Lemma D_8f0a4 : decode_any W_8f0a4 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0a8 : bv 32 := 0x00058e63.
Lemma F_8f0a8 : fetch_word AsanUbsan.M.loaded_segments (0x8f0f0 : word) = Some W_8f0a8.
Proof. vm_refl. Qed.
Lemma D_8f0a8 : decode_any W_8f0a8 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0c4 : bv 32 := 0x00008067.
Lemma F_8f0c4 : fetch_word AsanUbsan.M.loaded_segments (0x8f10c : word) = Some W_8f0c4.
Proof. vm_refl. Qed.
Lemma D_8f0c4 : decode_any W_8f0c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0e0 : bv 32 := 0x000c5597.
Lemma F_8f0e0 : fetch_word AsanUbsan.M.loaded_segments (0x8f128 : word) = Some W_8f0e0.
Proof. vm_refl. Qed.
Lemma D_8f0e0 : decode_any W_8f0e0 = Some (Auipc 11 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0e4 : bv 32 := 0x3c85b583.
Lemma F_8f0e4 : fetch_word AsanUbsan.M.loaded_segments (0x8f12c : word) = Some W_8f0e4.
Proof. vm_refl. Qed.
Lemma D_8f0e4 : decode_any W_8f0e4 = Some (Load SZ8 true 11 11 968, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0e8 : bv 32 := 0x0905b583.
Lemma F_8f0e8 : fetch_word AsanUbsan.M.loaded_segments (0x8f130 : word) = Some W_8f0e8.
Proof. vm_refl. Qed.
Lemma D_8f0e8 : decode_any W_8f0e8 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f0ec : bv 32 := 0x00058a63.
Lemma F_8f0ec : fetch_word AsanUbsan.M.loaded_segments (0x8f134 : word) = Some W_8f0ec.
Proof. vm_refl. Qed.
Lemma D_8f0ec : decode_any W_8f0ec = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f100 : bv 32 := 0x00008067.
Lemma F_8f100 : fetch_word AsanUbsan.M.loaded_segments (0x8f148 : word) = Some W_8f100.
Proof. vm_refl. Qed.
Lemma D_8f100 : decode_any W_8f100 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f610 : bv 32 := 0xfe010113.
Lemma F_8f610 : fetch_word AsanUbsan.M.loaded_segments (0x8f658 : word) = Some W_8f610.
Proof. vm_refl. Qed.
Lemma D_8f610 : decode_any W_8f610 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f614 : bv 32 := 0x00113c23.
Lemma F_8f614 : fetch_word AsanUbsan.M.loaded_segments (0x8f65c : word) = Some W_8f614.
Proof. vm_refl. Qed.
Lemma D_8f614 : decode_any W_8f614 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f618 : bv 32 := 0x00813823.
Lemma F_8f618 : fetch_word AsanUbsan.M.loaded_segments (0x8f660 : word) = Some W_8f618.
Proof. vm_refl. Qed.
Lemma D_8f618 : decode_any W_8f618 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f61c : bv 32 := 0x00913423.
Lemma F_8f61c : fetch_word AsanUbsan.M.loaded_segments (0x8f664 : word) = Some W_8f61c.
Proof. vm_refl. Qed.
Lemma D_8f61c : decode_any W_8f61c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f620 : bv 32 := 0x01213023.
Lemma F_8f620 : fetch_word AsanUbsan.M.loaded_segments (0x8f668 : word) = Some W_8f620.
Proof. vm_refl. Qed.
Lemma D_8f620 : decode_any W_8f620 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f624 : bv 32 := 0x00058413.
Lemma F_8f624 : fetch_word AsanUbsan.M.loaded_segments (0x8f66c : word) = Some W_8f624.
Proof. vm_refl. Qed.
Lemma D_8f624 : decode_any W_8f624 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f628 : bv 32 := 0x00050493.
Lemma F_8f628 : fetch_word AsanUbsan.M.loaded_segments (0x8f670 : word) = Some W_8f628.
Proof. vm_refl. Qed.
Lemma D_8f628 : decode_any W_8f628 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f62c : bv 32 := 0x09c000ef.
Lemma F_8f62c : fetch_word AsanUbsan.M.loaded_segments (0x8f674 : word) = Some W_8f62c.
Proof. vm_refl. Qed.
Lemma D_8f62c : decode_any W_8f62c = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f630 : bv 32 := 0x00160517.
Lemma F_8f630 : fetch_word AsanUbsan.M.loaded_segments (0x8f678 : word) = Some W_8f630.
Proof. vm_refl. Qed.
Lemma D_8f630 : decode_any W_8f630 = Some (Auipc 10 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f634 : bv 32 := 0x14850913.
Lemma F_8f634 : fetch_word AsanUbsan.M.loaded_segments (0x8f67c : word) = Some W_8f634.
Proof. vm_refl. Qed.
Lemma D_8f634 : decode_any W_8f634 = Some (OpImm ALU_ADD 18 10 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f638 : bv 32 := 0x00093603.
Lemma F_8f638 : fetch_word AsanUbsan.M.loaded_segments (0x8f680 : word) = Some W_8f638.
Proof. vm_refl. Qed.
Lemma D_8f638 : decode_any W_8f638 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f63c : bv 32 := 0x06060a63.
Lemma F_8f63c : fetch_word AsanUbsan.M.loaded_segments (0x8f684 : word) = Some W_8f63c.
Proof. vm_refl. Qed.
Lemma D_8f63c : decode_any W_8f63c = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6b0 : bv 32 := 0x01813083.
Lemma F_8f6b0 : fetch_word AsanUbsan.M.loaded_segments (0x8f6f8 : word) = Some W_8f6b0.
Proof. vm_refl. Qed.
Lemma D_8f6b0 : decode_any W_8f6b0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6b4 : bv 32 := 0x01013403.
Lemma F_8f6b4 : fetch_word AsanUbsan.M.loaded_segments (0x8f6fc : word) = Some W_8f6b4.
Proof. vm_refl. Qed.
Lemma D_8f6b4 : decode_any W_8f6b4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6b8 : bv 32 := 0x00813483.
Lemma F_8f6b8 : fetch_word AsanUbsan.M.loaded_segments (0x8f700 : word) = Some W_8f6b8.
Proof. vm_refl. Qed.
Lemma D_8f6b8 : decode_any W_8f6b8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6bc : bv 32 := 0x00013903.
Lemma F_8f6bc : fetch_word AsanUbsan.M.loaded_segments (0x8f704 : word) = Some W_8f6bc.
Proof. vm_refl. Qed.
Lemma D_8f6bc : decode_any W_8f6bc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6c0 : bv 32 := 0x02010113.
Lemma F_8f6c0 : fetch_word AsanUbsan.M.loaded_segments (0x8f708 : word) = Some W_8f6c0.
Proof. vm_refl. Qed.
Lemma D_8f6c0 : decode_any W_8f6c0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6c4 : bv 32 := 0x00008067.
Lemma F_8f6c4 : fetch_word AsanUbsan.M.loaded_segments (0x8f70c : word) = Some W_8f6c4.
Proof. vm_refl. Qed.
Lemma D_8f6c4 : decode_any W_8f6c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6c8 : bv 32 := 0x00008067.
Lemma F_8f6c8 : fetch_word AsanUbsan.M.loaded_segments (0x8f710 : word) = Some W_8f6c8.
Proof. vm_refl. Qed.
Lemma D_8f6c8 : decode_any W_8f6c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6cc : bv 32 := 0xfe010113.
Lemma F_8f6cc : fetch_word AsanUbsan.M.loaded_segments (0x8f714 : word) = Some W_8f6cc.
Proof. vm_refl. Qed.
Lemma D_8f6cc : decode_any W_8f6cc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6d0 : bv 32 := 0x00113c23.
Lemma F_8f6d0 : fetch_word AsanUbsan.M.loaded_segments (0x8f718 : word) = Some W_8f6d0.
Proof. vm_refl. Qed.
Lemma D_8f6d0 : decode_any W_8f6d0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6d4 : bv 32 := 0x00813823.
Lemma F_8f6d4 : fetch_word AsanUbsan.M.loaded_segments (0x8f71c : word) = Some W_8f6d4.
Proof. vm_refl. Qed.
Lemma D_8f6d4 : decode_any W_8f6d4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6d8 : bv 32 := 0x00913423.
Lemma F_8f6d8 : fetch_word AsanUbsan.M.loaded_segments (0x8f720 : word) = Some W_8f6d8.
Proof. vm_refl. Qed.
Lemma D_8f6d8 : decode_any W_8f6d8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6dc : bv 32 := 0x00050413.
Lemma F_8f6dc : fetch_word AsanUbsan.M.loaded_segments (0x8f724 : word) = Some W_8f6dc.
Proof. vm_refl. Qed.
Lemma D_8f6dc : decode_any W_8f6dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6e0 : bv 32 := 0x098000ef.
Lemma F_8f6e0 : fetch_word AsanUbsan.M.loaded_segments (0x8f728 : word) = Some W_8f6e0.
Proof. vm_refl. Qed.
Lemma D_8f6e0 : decode_any W_8f6e0 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f6e4 : bv 32 := 0x00050e63.
Lemma F_8f6e4 : fetch_word AsanUbsan.M.loaded_segments (0x8f72c : word) = Some W_8f6e4.
Proof. vm_refl. Qed.
Lemma D_8f6e4 : decode_any W_8f6e4 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f700 : bv 32 := 0x00040513.
Lemma F_8f700 : fetch_word AsanUbsan.M.loaded_segments (0x8f748 : word) = Some W_8f700.
Proof. vm_refl. Qed.
Lemma D_8f700 : decode_any W_8f700 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f704 : bv 32 := 0x07c000ef.
Lemma F_8f704 : fetch_word AsanUbsan.M.loaded_segments (0x8f74c : word) = Some W_8f704.
Proof. vm_refl. Qed.
Lemma D_8f704 : decode_any W_8f704 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f708 : bv 32 := 0x00160517.
Lemma F_8f708 : fetch_word AsanUbsan.M.loaded_segments (0x8f750 : word) = Some W_8f708.
Proof. vm_refl. Qed.
Lemma D_8f708 : decode_any W_8f708 = Some (Auipc 10 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f70c : bv 32 := 0x07050493.
Lemma F_8f70c : fetch_word AsanUbsan.M.loaded_segments (0x8f754 : word) = Some W_8f70c.
Proof. vm_refl. Qed.
Lemma D_8f70c : decode_any W_8f70c = Some (OpImm ALU_ADD 9 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f710 : bv 32 := 0x0084b583.
Lemma F_8f710 : fetch_word AsanUbsan.M.loaded_segments (0x8f758 : word) = Some W_8f710.
Proof. vm_refl. Qed.
Lemma D_8f710 : decode_any W_8f710 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f714 : bv 32 := 0x04058663.
Lemma F_8f714 : fetch_word AsanUbsan.M.loaded_segments (0x8f75c : word) = Some W_8f714.
Proof. vm_refl. Qed.
Lemma D_8f714 : decode_any W_8f714 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f760 : bv 32 := 0x00000513.
Lemma F_8f760 : fetch_word AsanUbsan.M.loaded_segments (0x8f7a8 : word) = Some W_8f760.
Proof. vm_refl. Qed.
Lemma D_8f760 : decode_any W_8f760 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f764 : bv 32 := 0x01813083.
Lemma F_8f764 : fetch_word AsanUbsan.M.loaded_segments (0x8f7ac : word) = Some W_8f764.
Proof. vm_refl. Qed.
Lemma D_8f764 : decode_any W_8f764 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f768 : bv 32 := 0x01013403.
Lemma F_8f768 : fetch_word AsanUbsan.M.loaded_segments (0x8f7b0 : word) = Some W_8f768.
Proof. vm_refl. Qed.
Lemma D_8f768 : decode_any W_8f768 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f76c : bv 32 := 0x00813483.
Lemma F_8f76c : fetch_word AsanUbsan.M.loaded_segments (0x8f7b4 : word) = Some W_8f76c.
Proof. vm_refl. Qed.
Lemma D_8f76c : decode_any W_8f76c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f770 : bv 32 := 0x02010113.
Lemma F_8f770 : fetch_word AsanUbsan.M.loaded_segments (0x8f7b8 : word) = Some W_8f770.
Proof. vm_refl. Qed.
Lemma D_8f770 : decode_any W_8f770 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f774 : bv 32 := 0x00008067.
Lemma F_8f774 : fetch_word AsanUbsan.M.loaded_segments (0x8f7bc : word) = Some W_8f774.
Proof. vm_refl. Qed.
Lemma D_8f774 : decode_any W_8f774 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f778 : bv 32 := 0x00000513.
Lemma F_8f778 : fetch_word AsanUbsan.M.loaded_segments (0x8f7c0 : word) = Some W_8f778.
Proof. vm_refl. Qed.
Lemma D_8f778 : decode_any W_8f778 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f77c : bv 32 := 0x00008067.
Lemma F_8f77c : fetch_word AsanUbsan.M.loaded_segments (0x8f7c4 : word) = Some W_8f77c.
Proof. vm_refl. Qed.
Lemma D_8f77c : decode_any W_8f77c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f780 : bv 32 := 0x00008067.
Lemma F_8f780 : fetch_word AsanUbsan.M.loaded_segments (0x8f7c8 : word) = Some W_8f780.
Proof. vm_refl. Qed.
Lemma D_8f780 : decode_any W_8f780 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

