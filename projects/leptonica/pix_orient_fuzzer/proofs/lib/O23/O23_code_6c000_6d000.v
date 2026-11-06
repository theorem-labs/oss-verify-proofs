(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_6c5e0 : bv 32 := 0xff010113.
Lemma F_6c5e0 : fetch_word Plain.M.loaded_segments (0x6c638 : word) = Some W_6c5e0.
Proof. vm_refl. Qed.
Lemma D_6c5e0 : decode_any W_6c5e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5e4 : bv 32 := 0x00113423.
Lemma F_6c5e4 : fetch_word Plain.M.loaded_segments (0x6c63c : word) = Some W_6c5e4.
Proof. vm_refl. Qed.
Lemma D_6c5e4 : decode_any W_6c5e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5e8 : bv 32 := 0x00813023.
Lemma F_6c5e8 : fetch_word Plain.M.loaded_segments (0x6c640 : word) = Some W_6c5e8.
Proof. vm_refl. Qed.
Lemma D_6c5e8 : decode_any W_6c5e8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5ec : bv 32 := 0x080000ef.
Lemma F_6c5ec : fetch_word Plain.M.loaded_segments (0x6c644 : word) = Some W_6c5ec.
Proof. vm_refl. Qed.
Lemma D_6c5ec : decode_any W_6c5ec = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5f0 : bv 32 := 0x02050863.
Lemma F_6c5f0 : fetch_word Plain.M.loaded_segments (0x6c648 : word) = Some W_6c5f0.
Proof. vm_refl. Qed.
Lemma D_6c5f0 : decode_any W_6c5f0 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5f4 : bv 32 := 0x00456603.
Lemma F_6c5f4 : fetch_word Plain.M.loaded_segments (0x6c64c : word) = Some W_6c5f4.
Proof. vm_refl. Qed.
Lemma D_6c5f4 : decode_any W_6c5f4 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5f8 : bv 32 := 0x01056683.
Lemma F_6c5f8 : fetch_word Plain.M.loaded_segments (0x6c650 : word) = Some W_6c5f8.
Proof. vm_refl. Qed.
Lemma D_6c5f8 : decode_any W_6c5f8 = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c5fc : bv 32 := 0x03853583.
Lemma F_6c5fc : fetch_word Plain.M.loaded_segments (0x6c654 : word) = Some W_6c5fc.
Proof. vm_refl. Qed.
Lemma D_6c5fc : decode_any W_6c5fc = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c600 : bv 32 := 0x02c68633.
Lemma F_6c600 : fetch_word Plain.M.loaded_segments (0x6c658 : word) = Some W_6c600.
Proof. vm_refl. Qed.
Lemma D_6c600 : decode_any W_6c600 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c604 : bv 32 := 0x00261613.
Lemma F_6c604 : fetch_word Plain.M.loaded_segments (0x6c65c : word) = Some W_6c604.
Proof. vm_refl. Qed.
Lemma D_6c604 : decode_any W_6c604 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c608 : bv 32 := 0x00050413.
Lemma F_6c608 : fetch_word Plain.M.loaded_segments (0x6c660 : word) = Some W_6c608.
Proof. vm_refl. Qed.
Lemma D_6c608 : decode_any W_6c608 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c60c : bv 32 := 0x00058513.
Lemma F_6c60c : fetch_word Plain.M.loaded_segments (0x6c664 : word) = Some W_6c60c.
Proof. vm_refl. Qed.
Lemma D_6c60c : decode_any W_6c60c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c610 : bv 32 := 0x00000593.
Lemma F_6c610 : fetch_word Plain.M.loaded_segments (0x6c668 : word) = Some W_6c610.
Proof. vm_refl. Qed.
Lemma D_6c610 : decode_any W_6c610 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c614 : bv 32 := 0x3c59d0ef.
Lemma F_6c614 : fetch_word Plain.M.loaded_segments (0x6c66c : word) = Some W_6c614.
Proof. vm_refl. Qed.
Lemma D_6c614 : decode_any W_6c614 = Some (Jal 1 646084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c618 : bv 32 := 0x00040513.
Lemma F_6c618 : fetch_word Plain.M.loaded_segments (0x6c670 : word) = Some W_6c618.
Proof. vm_refl. Qed.
Lemma D_6c618 : decode_any W_6c618 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c61c : bv 32 := 0x0400006f.
Lemma F_6c61c : fetch_word Plain.M.loaded_segments (0x6c674 : word) = Some W_6c61c.
Proof. vm_refl. Qed.
Lemma D_6c61c : decode_any W_6c61c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c620 : bv 32 := 0x000a6517.
Lemma F_6c620 : fetch_word Plain.M.loaded_segments (0x6c678 : word) = Some W_6c620.
Proof. vm_refl. Qed.
Lemma D_6c620 : decode_any W_6c620 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c624 : bv 32 := 0xf5053503.
Lemma F_6c624 : fetch_word Plain.M.loaded_segments (0x6c67c : word) = Some W_6c624.
Proof. vm_refl. Qed.
Lemma D_6c624 : decode_any W_6c624 = Some (Load SZ8 true 10 10 3920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c628 : bv 32 := 0x00052503.
Lemma F_6c628 : fetch_word Plain.M.loaded_segments (0x6c680 : word) = Some W_6c628.
Proof. vm_refl. Qed.
Lemma D_6c628 : decode_any W_6c628 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c62c : bv 32 := 0x00500593.
Lemma F_6c62c : fetch_word Plain.M.loaded_segments (0x6c684 : word) = Some W_6c62c.
Proof. vm_refl. Qed.
Lemma D_6c62c : decode_any W_6c62c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c630 : bv 32 := 0x02a5c463.
Lemma F_6c630 : fetch_word Plain.M.loaded_segments (0x6c688 : word) = Some W_6c630.
Proof. vm_refl. Qed.
Lemma D_6c630 : decode_any W_6c630 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c634 : bv 32 := 0xfffa6517.
Lemma F_6c634 : fetch_word Plain.M.loaded_segments (0x6c68c : word) = Some W_6c634.
Proof. vm_refl. Qed.
Lemma D_6c634 : decode_any W_6c634 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c638 : bv 32 := 0xfffa9597.
Lemma F_6c638 : fetch_word Plain.M.loaded_segments (0x6c690 : word) = Some W_6c638.
Proof. vm_refl. Qed.
Lemma D_6c638 : decode_any W_6c638 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c63c : bv 32 := 0x04e50513.
Lemma F_6c63c : fetch_word Plain.M.loaded_segments (0x6c694 : word) = Some W_6c63c.
Proof. vm_refl. Qed.
Lemma D_6c63c : decode_any W_6c63c = Some (OpImm ALU_ADD 10 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c640 : bv 32 := 0xb7058593.
Lemma F_6c640 : fetch_word Plain.M.loaded_segments (0x6c698 : word) = Some W_6c640.
Proof. vm_refl. Qed.
Lemma D_6c640 : decode_any W_6c640 = Some (OpImm ALU_ADD 11 11 2928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c644 : bv 32 := 0x00000613.
Lemma F_6c644 : fetch_word Plain.M.loaded_segments (0x6c69c : word) = Some W_6c644.
Proof. vm_refl. Qed.
Lemma D_6c644 : decode_any W_6c644 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c648 : bv 32 := 0x00813083.
Lemma F_6c648 : fetch_word Plain.M.loaded_segments (0x6c6a0 : word) = Some W_6c648.
Proof. vm_refl. Qed.
Lemma D_6c648 : decode_any W_6c648 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c64c : bv 32 := 0x00013403.
Lemma F_6c64c : fetch_word Plain.M.loaded_segments (0x6c6a4 : word) = Some W_6c64c.
Proof. vm_refl. Qed.
Lemma D_6c64c : decode_any W_6c64c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c650 : bv 32 := 0x01010113.
Lemma F_6c650 : fetch_word Plain.M.loaded_segments (0x6c6a8 : word) = Some W_6c650.
Proof. vm_refl. Qed.
Lemma D_6c650 : decode_any W_6c650 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c654 : bv 32 := 0xa71f606f.
Lemma F_6c654 : fetch_word Plain.M.loaded_segments (0x6c6ac : word) = Some W_6c654.
Proof. vm_refl. Qed.
Lemma D_6c654 : decode_any W_6c654 = Some (Jal 0 2058864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c65c : bv 32 := 0x00813083.
Lemma F_6c65c : fetch_word Plain.M.loaded_segments (0x6c6b4 : word) = Some W_6c65c.
Proof. vm_refl. Qed.
Lemma D_6c65c : decode_any W_6c65c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c660 : bv 32 := 0x00013403.
Lemma F_6c660 : fetch_word Plain.M.loaded_segments (0x6c6b8 : word) = Some W_6c660.
Proof. vm_refl. Qed.
Lemma D_6c660 : decode_any W_6c660 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c664 : bv 32 := 0x01010113.
Lemma F_6c664 : fetch_word Plain.M.loaded_segments (0x6c6bc : word) = Some W_6c664.
Proof. vm_refl. Qed.
Lemma D_6c664 : decode_any W_6c664 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c668 : bv 32 := 0x00008067.
Lemma F_6c668 : fetch_word Plain.M.loaded_segments (0x6c6c0 : word) = Some W_6c668.
Proof. vm_refl. Qed.
Lemma D_6c668 : decode_any W_6c668 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c66c : bv 32 := 0xfd010113.
Lemma F_6c66c : fetch_word Plain.M.loaded_segments (0x6c6c4 : word) = Some W_6c66c.
Proof. vm_refl. Qed.
Lemma D_6c66c : decode_any W_6c66c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c670 : bv 32 := 0x02113423.
Lemma F_6c670 : fetch_word Plain.M.loaded_segments (0x6c6c8 : word) = Some W_6c670.
Proof. vm_refl. Qed.
Lemma D_6c670 : decode_any W_6c670 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c674 : bv 32 := 0x02813023.
Lemma F_6c674 : fetch_word Plain.M.loaded_segments (0x6c6cc : word) = Some W_6c674.
Proof. vm_refl. Qed.
Lemma D_6c674 : decode_any W_6c674 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c678 : bv 32 := 0x00913c23.
Lemma F_6c678 : fetch_word Plain.M.loaded_segments (0x6c6d0 : word) = Some W_6c678.
Proof. vm_refl. Qed.
Lemma D_6c678 : decode_any W_6c678 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c67c : bv 32 := 0x01213823.
Lemma F_6c67c : fetch_word Plain.M.loaded_segments (0x6c6d4 : word) = Some W_6c67c.
Proof. vm_refl. Qed.
Lemma D_6c67c : decode_any W_6c67c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c680 : bv 32 := 0x00058493.
Lemma F_6c680 : fetch_word Plain.M.loaded_segments (0x6c6d8 : word) = Some W_6c680.
Proof. vm_refl. Qed.
Lemma D_6c680 : decode_any W_6c680 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c684 : bv 32 := 0x124000ef.
Lemma F_6c684 : fetch_word Plain.M.loaded_segments (0x6c6dc : word) = Some W_6c684.
Proof. vm_refl. Qed.
Lemma D_6c684 : decode_any W_6c684 = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c688 : bv 32 := 0x02050e63.
Lemma F_6c688 : fetch_word Plain.M.loaded_segments (0x6c6e0 : word) = Some W_6c688.
Proof. vm_refl. Qed.
Lemma D_6c688 : decode_any W_6c688 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c68c : bv 32 := 0x00050413.
Lemma F_6c68c : fetch_word Plain.M.loaded_segments (0x6c6e4 : word) = Some W_6c68c.
Proof. vm_refl. Qed.
Lemma D_6c68c : decode_any W_6c68c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c690 : bv 32 := 0x01052503.
Lemma F_6c690 : fetch_word Plain.M.loaded_segments (0x6c6e8 : word) = Some W_6c690.
Proof. vm_refl. Qed.
Lemma D_6c690 : decode_any W_6c690 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c694 : bv 32 := 0x000a7597.
Lemma F_6c694 : fetch_word Plain.M.loaded_segments (0x6c6ec : word) = Some W_6c694.
Proof. vm_refl. Qed.
Lemma D_6c694 : decode_any W_6c694 = Some (Auipc 11 167, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c698 : bv 32 := 0x0e458913.
Lemma F_6c698 : fetch_word Plain.M.loaded_segments (0x6c6f0 : word) = Some W_6c698.
Proof. vm_refl. Qed.
Lemma D_6c698 : decode_any W_6c698 = Some (OpImm ALU_ADD 18 11 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c69c : bv 32 := 0x00093583.
Lemma F_6c69c : fetch_word Plain.M.loaded_segments (0x6c6f4 : word) = Some W_6c69c.
Proof. vm_refl. Qed.
Lemma D_6c69c : decode_any W_6c69c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6a0 : bv 32 := 0x02a48533.
Lemma F_6c6a0 : fetch_word Plain.M.loaded_segments (0x6c6f8 : word) = Some W_6c6a0.
Proof. vm_refl. Qed.
Lemma D_6c6a0 : decode_any W_6c6a0 = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6a4 : bv 32 := 0x00251513.
Lemma F_6c6a4 : fetch_word Plain.M.loaded_segments (0x6c6fc : word) = Some W_6c6a4.
Proof. vm_refl. Qed.
Lemma D_6c6a4 : decode_any W_6c6a4 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6a8 : bv 32 := 0x000580e7.
Lemma F_6c6a8 : fetch_word Plain.M.loaded_segments (0x6c700 : word) = Some W_6c6a8.
Proof. vm_refl. Qed.
Lemma D_6c6a8 : decode_any W_6c6a8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6ac : bv 32 := 0x04050c63.
Lemma F_6c6ac : fetch_word Plain.M.loaded_segments (0x6c704 : word) = Some W_6c6ac.
Proof. vm_refl. Qed.
Lemma D_6c6ac : decode_any W_6c6ac = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6b0 : bv 32 := 0x02a43c23.
Lemma F_6c6b0 : fetch_word Plain.M.loaded_segments (0x6c708 : word) = Some W_6c6b0.
Proof. vm_refl. Qed.
Lemma D_6c6b0 : decode_any W_6c6b0 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6b4 : bv 32 := 0x00040513.
Lemma F_6c6b4 : fetch_word Plain.M.loaded_segments (0x6c70c : word) = Some W_6c6b4.
Proof. vm_refl. Qed.
Lemma D_6c6b4 : decode_any W_6c6b4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6b8 : bv 32 := 0x00000593.
Lemma F_6c6b8 : fetch_word Plain.M.loaded_segments (0x6c710 : word) = Some W_6c6b8.
Proof. vm_refl. Qed.
Lemma D_6c6b8 : decode_any W_6c6b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6bc : bv 32 := 0x608020ef.
Lemma F_6c6bc : fetch_word Plain.M.loaded_segments (0x6c714 : word) = Some W_6c6bc.
Proof. vm_refl. Qed.
Lemma D_6c6bc : decode_any W_6c6bc = Some (Jal 1 9736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6c0 : bv 32 := 0x0cc0006f.
Lemma F_6c6c0 : fetch_word Plain.M.loaded_segments (0x6c718 : word) = Some W_6c6c0.
Proof. vm_refl. Qed.
Lemma D_6c6c0 : decode_any W_6c6c0 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6c4 : bv 32 := 0x000a6517.
Lemma F_6c6c4 : fetch_word Plain.M.loaded_segments (0x6c71c : word) = Some W_6c6c4.
Proof. vm_refl. Qed.
Lemma D_6c6c4 : decode_any W_6c6c4 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6c8 : bv 32 := 0xeac53503.
Lemma F_6c6c8 : fetch_word Plain.M.loaded_segments (0x6c720 : word) = Some W_6c6c8.
Proof. vm_refl. Qed.
Lemma D_6c6c8 : decode_any W_6c6c8 = Some (Load SZ8 true 10 10 3756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6cc : bv 32 := 0x00052503.
Lemma F_6c6cc : fetch_word Plain.M.loaded_segments (0x6c724 : word) = Some W_6c6cc.
Proof. vm_refl. Qed.
Lemma D_6c6cc : decode_any W_6c6cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6d0 : bv 32 := 0x00500593.
Lemma F_6c6d0 : fetch_word Plain.M.loaded_segments (0x6c728 : word) = Some W_6c6d0.
Proof. vm_refl. Qed.
Lemma D_6c6d0 : decode_any W_6c6d0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6d4 : bv 32 := 0x0aa5ca63.
Lemma F_6c6d4 : fetch_word Plain.M.loaded_segments (0x6c72c : word) = Some W_6c6d4.
Proof. vm_refl. Qed.
Lemma D_6c6d4 : decode_any W_6c6d4 = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6d8 : bv 32 := 0xfffa6517.
Lemma F_6c6d8 : fetch_word Plain.M.loaded_segments (0x6c730 : word) = Some W_6c6d8.
Proof. vm_refl. Qed.
Lemma D_6c6d8 : decode_any W_6c6d8 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6dc : bv 32 := 0xfffa7597.
Lemma F_6c6dc : fetch_word Plain.M.loaded_segments (0x6c734 : word) = Some W_6c6dc.
Proof. vm_refl. Qed.
Lemma D_6c6dc : decode_any W_6c6dc = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6e0 : bv 32 := 0xfaa50513.
Lemma F_6c6e0 : fetch_word Plain.M.loaded_segments (0x6c738 : word) = Some W_6c6e0.
Proof. vm_refl. Qed.
Lemma D_6c6e0 : decode_any W_6c6e0 = Some (OpImm ALU_ADD 10 10 4010, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6e4 : bv 32 := 0x53158593.
Lemma F_6c6e4 : fetch_word Plain.M.loaded_segments (0x6c73c : word) = Some W_6c6e4.
Proof. vm_refl. Qed.
Lemma D_6c6e4 : decode_any W_6c6e4 = Some (OpImm ALU_ADD 11 11 1329, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6e8 : bv 32 := 0x00000613.
Lemma F_6c6e8 : fetch_word Plain.M.loaded_segments (0x6c740 : word) = Some W_6c6e8.
Proof. vm_refl. Qed.
Lemma D_6c6e8 : decode_any W_6c6e8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6ec : bv 32 := 0x02813083.
Lemma F_6c6ec : fetch_word Plain.M.loaded_segments (0x6c744 : word) = Some W_6c6ec.
Proof. vm_refl. Qed.
Lemma D_6c6ec : decode_any W_6c6ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6f0 : bv 32 := 0x02013403.
Lemma F_6c6f0 : fetch_word Plain.M.loaded_segments (0x6c748 : word) = Some W_6c6f0.
Proof. vm_refl. Qed.
Lemma D_6c6f0 : decode_any W_6c6f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6f4 : bv 32 := 0x01813483.
Lemma F_6c6f4 : fetch_word Plain.M.loaded_segments (0x6c74c : word) = Some W_6c6f4.
Proof. vm_refl. Qed.
Lemma D_6c6f4 : decode_any W_6c6f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6f8 : bv 32 := 0x01013903.
Lemma F_6c6f8 : fetch_word Plain.M.loaded_segments (0x6c750 : word) = Some W_6c6f8.
Proof. vm_refl. Qed.
Lemma D_6c6f8 : decode_any W_6c6f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c6fc : bv 32 := 0x03010113.
Lemma F_6c6fc : fetch_word Plain.M.loaded_segments (0x6c754 : word) = Some W_6c6fc.
Proof. vm_refl. Qed.
Lemma D_6c6fc : decode_any W_6c6fc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c700 : bv 32 := 0x9c5f606f.
Lemma F_6c700 : fetch_word Plain.M.loaded_segments (0x6c758 : word) = Some W_6c700.
Proof. vm_refl. Qed.
Lemma D_6c700 : decode_any W_6c700 = Some (Jal 0 2058692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c704 : bv 32 := 0x01440513.
Lemma F_6c704 : fetch_word Plain.M.loaded_segments (0x6c75c : word) = Some W_6c704.
Proof. vm_refl. Qed.
Lemma D_6c704 : decode_any W_6c704 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c708 : bv 32 := 0xfff00593.
Lemma F_6c708 : fetch_word Plain.M.loaded_segments (0x6c760 : word) = Some W_6c708.
Proof. vm_refl. Qed.
Lemma D_6c708 : decode_any W_6c708 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c70c : bv 32 := 0x06b5252f.
Lemma F_6c70c : fetch_word Plain.M.loaded_segments (0x6c764 : word) = Some W_6c70c.
Proof. vm_refl. Qed.
Lemma D_6c70c : decode_any W_6c70c = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c710 : bv 32 := 0x00100593.
Lemma F_6c710 : fetch_word Plain.M.loaded_segments (0x6c768 : word) = Some W_6c710.
Proof. vm_refl. Qed.
Lemma D_6c710 : decode_any W_6c710 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c714 : bv 32 := 0x04b51063.
Lemma F_6c714 : fetch_word Plain.M.loaded_segments (0x6c76c : word) = Some W_6c714.
Proof. vm_refl. Qed.
Lemma D_6c714 : decode_any W_6c714 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c718 : bv 32 := 0x03843503.
Lemma F_6c718 : fetch_word Plain.M.loaded_segments (0x6c770 : word) = Some W_6c718.
Proof. vm_refl. Qed.
Lemma D_6c718 : decode_any W_6c718 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c71c : bv 32 := 0x00050663.
Lemma F_6c71c : fetch_word Plain.M.loaded_segments (0x6c774 : word) = Some W_6c71c.
Proof. vm_refl. Qed.
Lemma D_6c71c : decode_any W_6c71c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c728 : bv 32 := 0x02843503.
Lemma F_6c728 : fetch_word Plain.M.loaded_segments (0x6c780 : word) = Some W_6c728.
Proof. vm_refl. Qed.
Lemma D_6c728 : decode_any W_6c728 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c72c : bv 32 := 0x00050463.
Lemma F_6c72c : fetch_word Plain.M.loaded_segments (0x6c784 : word) = Some W_6c72c.
Proof. vm_refl. Qed.
Lemma D_6c72c : decode_any W_6c72c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c734 : bv 32 := 0x03043503.
Lemma F_6c734 : fetch_word Plain.M.loaded_segments (0x6c78c : word) = Some W_6c734.
Proof. vm_refl. Qed.
Lemma D_6c734 : decode_any W_6c734 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c738 : bv 32 := 0x00a13423.
Lemma F_6c738 : fetch_word Plain.M.loaded_segments (0x6c790 : word) = Some W_6c738.
Proof. vm_refl. Qed.
Lemma D_6c738 : decode_any W_6c738 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c73c : bv 32 := 0x00050863.
Lemma F_6c73c : fetch_word Plain.M.loaded_segments (0x6c794 : word) = Some W_6c73c.
Proof. vm_refl. Qed.
Lemma D_6c73c : decode_any W_6c73c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c74c : bv 32 := 0x00040513.
Lemma F_6c74c : fetch_word Plain.M.loaded_segments (0x6c7a4 : word) = Some W_6c74c.
Proof. vm_refl. Qed.
Lemma D_6c74c : decode_any W_6c74c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c750 : bv 32 := 0x3cd8d0ef.
Lemma F_6c750 : fetch_word Plain.M.loaded_segments (0x6c7a8 : word) = Some W_6c750.
Proof. vm_refl. Qed.
Lemma D_6c750 : decode_any W_6c750 = Some (Jal 1 580556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c754 : bv 32 := 0x000a6517.
Lemma F_6c754 : fetch_word Plain.M.loaded_segments (0x6c7ac : word) = Some W_6c754.
Proof. vm_refl. Qed.
Lemma D_6c754 : decode_any W_6c754 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c758 : bv 32 := 0xe1c53503.
Lemma F_6c758 : fetch_word Plain.M.loaded_segments (0x6c7b0 : word) = Some W_6c758.
Proof. vm_refl. Qed.
Lemma D_6c758 : decode_any W_6c758 = Some (Load SZ8 true 10 10 3612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c75c : bv 32 := 0x00052503.
Lemma F_6c75c : fetch_word Plain.M.loaded_segments (0x6c7b4 : word) = Some W_6c75c.
Proof. vm_refl. Qed.
Lemma D_6c75c : decode_any W_6c75c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c760 : bv 32 := 0x00500593.
Lemma F_6c760 : fetch_word Plain.M.loaded_segments (0x6c7b8 : word) = Some W_6c760.
Proof. vm_refl. Qed.
Lemma D_6c760 : decode_any W_6c760 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c764 : bv 32 := 0x02a5c263.
Lemma F_6c764 : fetch_word Plain.M.loaded_segments (0x6c7bc : word) = Some W_6c764.
Proof. vm_refl. Qed.
Lemma D_6c764 : decode_any W_6c764 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c768 : bv 32 := 0xfffaf517.
Lemma F_6c768 : fetch_word Plain.M.loaded_segments (0x6c7c0 : word) = Some W_6c768.
Proof. vm_refl. Qed.
Lemma D_6c768 : decode_any W_6c768 = Some (Auipc 10 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c76c : bv 32 := 0xfffa7597.
Lemma F_6c76c : fetch_word Plain.M.loaded_segments (0x6c7c4 : word) = Some W_6c76c.
Proof. vm_refl. Qed.
Lemma D_6c76c : decode_any W_6c76c = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c770 : bv 32 := 0x19450513.
Lemma F_6c770 : fetch_word Plain.M.loaded_segments (0x6c7c8 : word) = Some W_6c770.
Proof. vm_refl. Qed.
Lemma D_6c770 : decode_any W_6c770 = Some (OpImm ALU_ADD 10 10 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c774 : bv 32 := 0x4a158593.
Lemma F_6c774 : fetch_word Plain.M.loaded_segments (0x6c7cc : word) = Some W_6c774.
Proof. vm_refl. Qed.
Lemma D_6c774 : decode_any W_6c774 = Some (OpImm ALU_ADD 11 11 1185, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c778 : bv 32 := 0x00000613.
Lemma F_6c778 : fetch_word Plain.M.loaded_segments (0x6c7d0 : word) = Some W_6c778.
Proof. vm_refl. Qed.
Lemma D_6c778 : decode_any W_6c778 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c77c : bv 32 := 0x949f60ef.
Lemma F_6c77c : fetch_word Plain.M.loaded_segments (0x6c7d4 : word) = Some W_6c77c.
Proof. vm_refl. Qed.
Lemma D_6c77c : decode_any W_6c77c = Some (Jal 1 2058568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c780 : bv 32 := 0x00050413.
Lemma F_6c780 : fetch_word Plain.M.loaded_segments (0x6c7d8 : word) = Some W_6c780.
Proof. vm_refl. Qed.
Lemma D_6c780 : decode_any W_6c780 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c784 : bv 32 := 0x0080006f.
Lemma F_6c784 : fetch_word Plain.M.loaded_segments (0x6c7dc : word) = Some W_6c784.
Proof. vm_refl. Qed.
Lemma D_6c784 : decode_any W_6c784 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c78c : bv 32 := 0x00040513.
Lemma F_6c78c : fetch_word Plain.M.loaded_segments (0x6c7e4 : word) = Some W_6c78c.
Proof. vm_refl. Qed.
Lemma D_6c78c : decode_any W_6c78c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c790 : bv 32 := 0x02813083.
Lemma F_6c790 : fetch_word Plain.M.loaded_segments (0x6c7e8 : word) = Some W_6c790.
Proof. vm_refl. Qed.
Lemma D_6c790 : decode_any W_6c790 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c794 : bv 32 := 0x02013403.
Lemma F_6c794 : fetch_word Plain.M.loaded_segments (0x6c7ec : word) = Some W_6c794.
Proof. vm_refl. Qed.
Lemma D_6c794 : decode_any W_6c794 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c798 : bv 32 := 0x01813483.
Lemma F_6c798 : fetch_word Plain.M.loaded_segments (0x6c7f0 : word) = Some W_6c798.
Proof. vm_refl. Qed.
Lemma D_6c798 : decode_any W_6c798 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c79c : bv 32 := 0x01013903.
Lemma F_6c79c : fetch_word Plain.M.loaded_segments (0x6c7f4 : word) = Some W_6c79c.
Proof. vm_refl. Qed.
Lemma D_6c79c : decode_any W_6c79c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7a0 : bv 32 := 0x03010113.
Lemma F_6c7a0 : fetch_word Plain.M.loaded_segments (0x6c7f8 : word) = Some W_6c7a0.
Proof. vm_refl. Qed.
Lemma D_6c7a0 : decode_any W_6c7a0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7a4 : bv 32 := 0x00008067.
Lemma F_6c7a4 : fetch_word Plain.M.loaded_segments (0x6c7fc : word) = Some W_6c7a4.
Proof. vm_refl. Qed.
Lemma D_6c7a4 : decode_any W_6c7a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7a8 : bv 32 := 0xfd010113.
Lemma F_6c7a8 : fetch_word Plain.M.loaded_segments (0x6c800 : word) = Some W_6c7a8.
Proof. vm_refl. Qed.
Lemma D_6c7a8 : decode_any W_6c7a8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7ac : bv 32 := 0x02113423.
Lemma F_6c7ac : fetch_word Plain.M.loaded_segments (0x6c804 : word) = Some W_6c7ac.
Proof. vm_refl. Qed.
Lemma D_6c7ac : decode_any W_6c7ac = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7b0 : bv 32 := 0x02813023.
Lemma F_6c7b0 : fetch_word Plain.M.loaded_segments (0x6c808 : word) = Some W_6c7b0.
Proof. vm_refl. Qed.
Lemma D_6c7b0 : decode_any W_6c7b0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7b4 : bv 32 := 0x00913c23.
Lemma F_6c7b4 : fetch_word Plain.M.loaded_segments (0x6c80c : word) = Some W_6c7b4.
Proof. vm_refl. Qed.
Lemma D_6c7b4 : decode_any W_6c7b4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7b8 : bv 32 := 0x01213823.
Lemma F_6c7b8 : fetch_word Plain.M.loaded_segments (0x6c810 : word) = Some W_6c7b8.
Proof. vm_refl. Qed.
Lemma D_6c7b8 : decode_any W_6c7b8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7bc : bv 32 := 0x01313423.
Lemma F_6c7bc : fetch_word Plain.M.loaded_segments (0x6c814 : word) = Some W_6c7bc.
Proof. vm_refl. Qed.
Lemma D_6c7bc : decode_any W_6c7bc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7c0 : bv 32 := 0x01413023.
Lemma F_6c7c0 : fetch_word Plain.M.loaded_segments (0x6c818 : word) = Some W_6c7c0.
Proof. vm_refl. Qed.
Lemma D_6c7c0 : decode_any W_6c7c0 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7c4 : bv 32 := 0x02000693.
Lemma F_6c7c4 : fetch_word Plain.M.loaded_segments (0x6c81c : word) = Some W_6c7c4.
Proof. vm_refl. Qed.
Lemma D_6c7c4 : decode_any W_6c7c4 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7c8 : bv 32 := 0x14c6ea63.
Lemma F_6c7c8 : fetch_word Plain.M.loaded_segments (0x6c820 : word) = Some W_6c7c8.
Proof. vm_refl. Qed.
Lemma D_6c7c8 : decode_any W_6c7c8 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7cc : bv 32 := 0x101016b7.
Lemma F_6c7cc : fetch_word Plain.M.loaded_segments (0x6c824 : word) = Some W_6c7cc.
Proof. vm_refl. Qed.
Lemma D_6c7cc : decode_any W_6c7cc = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7d0 : bv 32 := 0x00469693.
Lemma F_6c7d0 : fetch_word Plain.M.loaded_segments (0x6c828 : word) = Some W_6c7d0.
Proof. vm_refl. Qed.
Lemma D_6c7d0 : decode_any W_6c7d0 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7d4 : bv 32 := 0x11668693.
Lemma F_6c7d4 : fetch_word Plain.M.loaded_segments (0x6c82c : word) = Some W_6c7d4.
Proof. vm_refl. Qed.
Lemma D_6c7d4 : decode_any W_6c7d4 = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7d8 : bv 32 := 0x00c6d6b3.
Lemma F_6c7d8 : fetch_word Plain.M.loaded_segments (0x6c830 : word) = Some W_6c7d8.
Proof. vm_refl. Qed.
Lemma D_6c7d8 : decode_any W_6c7d8 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7dc : bv 32 := 0x0016f693.
Lemma F_6c7dc : fetch_word Plain.M.loaded_segments (0x6c834 : word) = Some W_6c7dc.
Proof. vm_refl. Qed.
Lemma D_6c7dc : decode_any W_6c7dc = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7e0 : bv 32 := 0x12068e63.
Lemma F_6c7e0 : fetch_word Plain.M.loaded_segments (0x6c838 : word) = Some W_6c7e0.
Proof. vm_refl. Qed.
Lemma D_6c7e0 : decode_any W_6c7e0 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7e4 : bv 32 := 0x06a05a63.
Lemma F_6c7e4 : fetch_word Plain.M.loaded_segments (0x6c83c : word) = Some W_6c7e4.
Proof. vm_refl. Qed.
Lemma D_6c7e4 : decode_any W_6c7e4 = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7e8 : bv 32 := 0x08b05c63.
Lemma F_6c7e8 : fetch_word Plain.M.loaded_segments (0x6c840 : word) = Some W_6c7e8.
Proof. vm_refl. Qed.
Lemma D_6c7e8 : decode_any W_6c7e8 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7ec : bv 32 := 0x02a606b3.
Lemma F_6c7ec : fetch_word Plain.M.loaded_segments (0x6c844 : word) = Some W_6c7ec.
Proof. vm_refl. Qed.
Lemma D_6c7ec : decode_any W_6c7ec = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7f0 : bv 32 := 0x20000737.
Lemma F_6c7f0 : fetch_word Plain.M.loaded_segments (0x6c848 : word) = Some W_6c7f0.
Proof. vm_refl. Qed.
Lemma D_6c7f0 : decode_any W_6c7f0 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7f4 : bv 32 := 0xfe17071b.
Lemma F_6c7f4 : fetch_word Plain.M.loaded_segments (0x6c84c : word) = Some W_6c7f4.
Proof. vm_refl. Qed.
Lemma D_6c7f4 : decode_any W_6c7f4 = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c7f8 : bv 32 := 0x0ae6e863.
Lemma F_6c7f8 : fetch_word Plain.M.loaded_segments (0x6c850 : word) = Some W_6c7f8.
Proof. vm_refl. Qed.
Lemma D_6c7f8 : decode_any W_6c7f8 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8a8 : bv 32 := 0x01f68693.
Lemma F_6c8a8 : fetch_word Plain.M.loaded_segments (0x6c900 : word) = Some W_6c8a8.
Proof. vm_refl. Qed.
Lemma D_6c8a8 : decode_any W_6c8a8 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8ac : bv 32 := 0x0056d413.
Lemma F_6c8ac : fetch_word Plain.M.loaded_segments (0x6c904 : word) = Some W_6c8ac.
Proof. vm_refl. Qed.
Lemma D_6c8ac : decode_any W_6c8ac = Some (ShiftImm ALU_SRL 8 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8b0 : bv 32 := 0x02b406b3.
Lemma F_6c8b0 : fetch_word Plain.M.loaded_segments (0x6c908 : word) = Some W_6c8b0.
Proof. vm_refl. Qed.
Lemma D_6c8b0 : decode_any W_6c8b0 = Some (Mul M_MUL 13 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8b4 : bv 32 := 0x00269693.
Lemma F_6c8b4 : fetch_word Plain.M.loaded_segments (0x6c90c : word) = Some W_6c8b4.
Proof. vm_refl. Qed.
Lemma D_6c8b4 : decode_any W_6c8b4 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8b8 : bv 32 := 0x01f6d713.
Lemma F_6c8b8 : fetch_word Plain.M.loaded_segments (0x6c910 : word) = Some W_6c8b8.
Proof. vm_refl. Qed.
Lemma D_6c8b8 : decode_any W_6c8b8 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c8bc : bv 32 := 0x0a070463.
Lemma F_6c8bc : fetch_word Plain.M.loaded_segments (0x6c914 : word) = Some W_6c8bc.
Proof. vm_refl. Qed.
Lemma D_6c8bc : decode_any W_6c8bc = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c91c : bv 32 := 0x000a6517.
Lemma F_6c91c : fetch_word Plain.M.loaded_segments (0x6c974 : word) = Some W_6c91c.
Proof. vm_refl. Qed.
Lemma D_6c91c : decode_any W_6c91c = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c920 : bv 32 := 0xc5453503.
Lemma F_6c920 : fetch_word Plain.M.loaded_segments (0x6c978 : word) = Some W_6c920.
Proof. vm_refl. Qed.
Lemma D_6c920 : decode_any W_6c920 = Some (Load SZ8 true 10 10 3156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c924 : bv 32 := 0x00052503.
Lemma F_6c924 : fetch_word Plain.M.loaded_segments (0x6c97c : word) = Some W_6c924.
Proof. vm_refl. Qed.
Lemma D_6c924 : decode_any W_6c924 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c928 : bv 32 := 0x00500593.
Lemma F_6c928 : fetch_word Plain.M.loaded_segments (0x6c980 : word) = Some W_6c928.
Proof. vm_refl. Qed.
Lemma D_6c928 : decode_any W_6c928 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c92c : bv 32 := 0x0ca5c663.
Lemma F_6c92c : fetch_word Plain.M.loaded_segments (0x6c984 : word) = Some W_6c92c.
Proof. vm_refl. Qed.
Lemma D_6c92c : decode_any W_6c92c = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c930 : bv 32 := 0xfffa6517.
Lemma F_6c930 : fetch_word Plain.M.loaded_segments (0x6c988 : word) = Some W_6c930.
Proof. vm_refl. Qed.
Lemma D_6c930 : decode_any W_6c930 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c934 : bv 32 := 0xfffa9597.
Lemma F_6c934 : fetch_word Plain.M.loaded_segments (0x6c98c : word) = Some W_6c934.
Proof. vm_refl. Qed.
Lemma D_6c934 : decode_any W_6c934 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c938 : bv 32 := 0x44450513.
Lemma F_6c938 : fetch_word Plain.M.loaded_segments (0x6c990 : word) = Some W_6c938.
Proof. vm_refl. Qed.
Lemma D_6c938 : decode_any W_6c938 = Some (OpImm ALU_ADD 10 10 1092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c93c : bv 32 := 0x0a058593.
Lemma F_6c93c : fetch_word Plain.M.loaded_segments (0x6c994 : word) = Some W_6c93c.
Proof. vm_refl. Qed.
Lemma D_6c93c : decode_any W_6c93c = Some (OpImm ALU_ADD 11 11 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c940 : bv 32 := 0x00000613.
Lemma F_6c940 : fetch_word Plain.M.loaded_segments (0x6c998 : word) = Some W_6c940.
Proof. vm_refl. Qed.
Lemma D_6c940 : decode_any W_6c940 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c944 : bv 32 := 0x02813083.
Lemma F_6c944 : fetch_word Plain.M.loaded_segments (0x6c99c : word) = Some W_6c944.
Proof. vm_refl. Qed.
Lemma D_6c944 : decode_any W_6c944 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c948 : bv 32 := 0x02013403.
Lemma F_6c948 : fetch_word Plain.M.loaded_segments (0x6c9a0 : word) = Some W_6c948.
Proof. vm_refl. Qed.
Lemma D_6c948 : decode_any W_6c948 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c94c : bv 32 := 0x01813483.
Lemma F_6c94c : fetch_word Plain.M.loaded_segments (0x6c9a4 : word) = Some W_6c94c.
Proof. vm_refl. Qed.
Lemma D_6c94c : decode_any W_6c94c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c950 : bv 32 := 0x01013903.
Lemma F_6c950 : fetch_word Plain.M.loaded_segments (0x6c9a8 : word) = Some W_6c950.
Proof. vm_refl. Qed.
Lemma D_6c950 : decode_any W_6c950 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c954 : bv 32 := 0x00813983.
Lemma F_6c954 : fetch_word Plain.M.loaded_segments (0x6c9ac : word) = Some W_6c954.
Proof. vm_refl. Qed.
Lemma D_6c954 : decode_any W_6c954 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c958 : bv 32 := 0x00013a03.
Lemma F_6c958 : fetch_word Plain.M.loaded_segments (0x6c9b0 : word) = Some W_6c958.
Proof. vm_refl. Qed.
Lemma D_6c958 : decode_any W_6c958 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c95c : bv 32 := 0x03010113.
Lemma F_6c95c : fetch_word Plain.M.loaded_segments (0x6c9b4 : word) = Some W_6c95c.
Proof. vm_refl. Qed.
Lemma D_6c95c : decode_any W_6c95c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c960 : bv 32 := 0xf64f606f.
Lemma F_6c960 : fetch_word Plain.M.loaded_segments (0x6c9b8 : word) = Some W_6c960.
Proof. vm_refl. Qed.
Lemma D_6c960 : decode_any W_6c960 = Some (Jal 0 2058084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c964 : bv 32 := 0x04000737.
Lemma F_6c964 : fetch_word Plain.M.loaded_segments (0x6c9bc : word) = Some W_6c964.
Proof. vm_refl. Qed.
Lemma D_6c964 : decode_any W_6c964 = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c968 : bv 32 := 0x0017071b.
Lemma F_6c968 : fetch_word Plain.M.loaded_segments (0x6c9c0 : word) = Some W_6c968.
Proof. vm_refl. Qed.
Lemma D_6c968 : decode_any W_6c968 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c96c : bv 32 := 0x02e6e663.
Lemma F_6c96c : fetch_word Plain.M.loaded_segments (0x6c9c4 : word) = Some W_6c96c.
Proof. vm_refl. Qed.
Lemma D_6c96c : decode_any W_6c96c = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c970 : bv 32 := 0x000a6517.
Lemma F_6c970 : fetch_word Plain.M.loaded_segments (0x6c9c8 : word) = Some W_6c970.
Proof. vm_refl. Qed.
Lemma D_6c970 : decode_any W_6c970 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c974 : bv 32 := 0xc0053503.
Lemma F_6c974 : fetch_word Plain.M.loaded_segments (0x6c9cc : word) = Some W_6c974.
Proof. vm_refl. Qed.
Lemma D_6c974 : decode_any W_6c974 = Some (Load SZ8 true 10 10 3072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c978 : bv 32 := 0x00052503.
Lemma F_6c978 : fetch_word Plain.M.loaded_segments (0x6c9d0 : word) = Some W_6c978.
Proof. vm_refl. Qed.
Lemma D_6c978 : decode_any W_6c978 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c97c : bv 32 := 0x00500593.
Lemma F_6c97c : fetch_word Plain.M.loaded_segments (0x6c9d4 : word) = Some W_6c97c.
Proof. vm_refl. Qed.
Lemma D_6c97c : decode_any W_6c97c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c980 : bv 32 := 0x06a5cc63.
Lemma F_6c980 : fetch_word Plain.M.loaded_segments (0x6c9d8 : word) = Some W_6c980.
Proof. vm_refl. Qed.
Lemma D_6c980 : decode_any W_6c980 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c984 : bv 32 := 0xfffa5517.
Lemma F_6c984 : fetch_word Plain.M.loaded_segments (0x6c9dc : word) = Some W_6c984.
Proof. vm_refl. Qed.
Lemma D_6c984 : decode_any W_6c984 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c988 : bv 32 := 0xfffa9597.
Lemma F_6c988 : fetch_word Plain.M.loaded_segments (0x6c9e0 : word) = Some W_6c988.
Proof. vm_refl. Qed.
Lemma D_6c988 : decode_any W_6c988 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c98c : bv 32 := 0x5ca50513.
Lemma F_6c98c : fetch_word Plain.M.loaded_segments (0x6c9e4 : word) = Some W_6c98c.
Proof. vm_refl. Qed.
Lemma D_6c98c : decode_any W_6c98c = Some (OpImm ALU_ADD 10 10 1482, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c990 : bv 32 := 0x04c58593.
Lemma F_6c990 : fetch_word Plain.M.loaded_segments (0x6c9e8 : word) = Some W_6c990.
Proof. vm_refl. Qed.
Lemma D_6c990 : decode_any W_6c990 = Some (OpImm ALU_ADD 11 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c994 : bv 32 := 0x0600006f.
Lemma F_6c994 : fetch_word Plain.M.loaded_segments (0x6c9ec : word) = Some W_6c994.
Proof. vm_refl. Qed.
Lemma D_6c994 : decode_any W_6c994 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c998 : bv 32 := 0x000056b7.
Lemma F_6c998 : fetch_word Plain.M.loaded_segments (0x6c9f0 : word) = Some W_6c998.
Proof. vm_refl. Qed.
Lemma D_6c998 : decode_any W_6c998 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c99c : bv 32 := 0xe216869b.
Lemma F_6c99c : fetch_word Plain.M.loaded_segments (0x6c9f4 : word) = Some W_6c99c.
Proof. vm_refl. Qed.
Lemma D_6c99c : decode_any W_6c99c = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9a0 : bv 32 := 0x02d56663.
Lemma F_6c9a0 : fetch_word Plain.M.loaded_segments (0x6c9f8 : word) = Some W_6c9a0.
Proof. vm_refl. Qed.
Lemma D_6c9a0 : decode_any W_6c9a0 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9a4 : bv 32 := 0x000a6517.
Lemma F_6c9a4 : fetch_word Plain.M.loaded_segments (0x6c9fc : word) = Some W_6c9a4.
Proof. vm_refl. Qed.
Lemma D_6c9a4 : decode_any W_6c9a4 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9a8 : bv 32 := 0xbcc53503.
Lemma F_6c9a8 : fetch_word Plain.M.loaded_segments (0x6ca00 : word) = Some W_6c9a8.
Proof. vm_refl. Qed.
Lemma D_6c9a8 : decode_any W_6c9a8 = Some (Load SZ8 true 10 10 3020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9ac : bv 32 := 0x00052503.
Lemma F_6c9ac : fetch_word Plain.M.loaded_segments (0x6ca04 : word) = Some W_6c9ac.
Proof. vm_refl. Qed.
Lemma D_6c9ac : decode_any W_6c9ac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9b0 : bv 32 := 0x00500593.
Lemma F_6c9b0 : fetch_word Plain.M.loaded_segments (0x6ca08 : word) = Some W_6c9b0.
Proof. vm_refl. Qed.
Lemma D_6c9b0 : decode_any W_6c9b0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9b4 : bv 32 := 0x04a5c263.
Lemma F_6c9b4 : fetch_word Plain.M.loaded_segments (0x6ca0c : word) = Some W_6c9b4.
Proof. vm_refl. Qed.
Lemma D_6c9b4 : decode_any W_6c9b4 = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9b8 : bv 32 := 0xfffb0517.
Lemma F_6c9b8 : fetch_word Plain.M.loaded_segments (0x6ca10 : word) = Some W_6c9b8.
Proof. vm_refl. Qed.
Lemma D_6c9b8 : decode_any W_6c9b8 = Some (Auipc 10 1048496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9bc : bv 32 := 0xfffa9597.
Lemma F_6c9bc : fetch_word Plain.M.loaded_segments (0x6ca14 : word) = Some W_6c9bc.
Proof. vm_refl. Qed.
Lemma D_6c9bc : decode_any W_6c9bc = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9c0 : bv 32 := 0xe0150513.
Lemma F_6c9c0 : fetch_word Plain.M.loaded_segments (0x6ca18 : word) = Some W_6c9c0.
Proof. vm_refl. Qed.
Lemma D_6c9c0 : decode_any W_6c9c0 = Some (OpImm ALU_ADD 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9c4 : bv 32 := 0x01858593.
Lemma F_6c9c4 : fetch_word Plain.M.loaded_segments (0x6ca1c : word) = Some W_6c9c4.
Proof. vm_refl. Qed.
Lemma D_6c9c4 : decode_any W_6c9c4 = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9c8 : bv 32 := 0x02c0006f.
Lemma F_6c9c8 : fetch_word Plain.M.loaded_segments (0x6ca20 : word) = Some W_6c9c8.
Proof. vm_refl. Qed.
Lemma D_6c9c8 : decode_any W_6c9c8 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9cc : bv 32 := 0x04d5e863.
Lemma F_6c9cc : fetch_word Plain.M.loaded_segments (0x6ca24 : word) = Some W_6c9cc.
Proof. vm_refl. Qed.
Lemma D_6c9cc : decode_any W_6c9cc = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9d0 : bv 32 := 0x000a6517.
Lemma F_6c9d0 : fetch_word Plain.M.loaded_segments (0x6ca28 : word) = Some W_6c9d0.
Proof. vm_refl. Qed.
Lemma D_6c9d0 : decode_any W_6c9d0 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9d4 : bv 32 := 0xba053503.
Lemma F_6c9d4 : fetch_word Plain.M.loaded_segments (0x6ca2c : word) = Some W_6c9d4.
Proof. vm_refl. Qed.
Lemma D_6c9d4 : decode_any W_6c9d4 = Some (Load SZ8 true 10 10 2976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9d8 : bv 32 := 0x00052503.
Lemma F_6c9d8 : fetch_word Plain.M.loaded_segments (0x6ca30 : word) = Some W_6c9d8.
Proof. vm_refl. Qed.
Lemma D_6c9d8 : decode_any W_6c9d8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9dc : bv 32 := 0x00500593.
Lemma F_6c9dc : fetch_word Plain.M.loaded_segments (0x6ca34 : word) = Some W_6c9dc.
Proof. vm_refl. Qed.
Lemma D_6c9dc : decode_any W_6c9dc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9e0 : bv 32 := 0x00a5cc63.
Lemma F_6c9e0 : fetch_word Plain.M.loaded_segments (0x6ca38 : word) = Some W_6c9e0.
Proof. vm_refl. Qed.
Lemma D_6c9e0 : decode_any W_6c9e0 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9e4 : bv 32 := 0xfffac517.
Lemma F_6c9e4 : fetch_word Plain.M.loaded_segments (0x6ca3c : word) = Some W_6c9e4.
Proof. vm_refl. Qed.
Lemma D_6c9e4 : decode_any W_6c9e4 = Some (Auipc 10 1048492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9e8 : bv 32 := 0xfffa9597.
Lemma F_6c9e8 : fetch_word Plain.M.loaded_segments (0x6ca40 : word) = Some W_6c9e8.
Proof. vm_refl. Qed.
Lemma D_6c9e8 : decode_any W_6c9e8 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9ec : bv 32 := 0x12250513.
Lemma F_6c9ec : fetch_word Plain.M.loaded_segments (0x6ca44 : word) = Some W_6c9ec.
Proof. vm_refl. Qed.
Lemma D_6c9ec : decode_any W_6c9ec = Some (OpImm ALU_ADD 10 10 290, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9f0 : bv 32 := 0xfec58593.
Lemma F_6c9f0 : fetch_word Plain.M.loaded_segments (0x6ca48 : word) = Some W_6c9f0.
Proof. vm_refl. Qed.
Lemma D_6c9f0 : decode_any W_6c9f0 = Some (OpImm ALU_ADD 11 11 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9f4 : bv 32 := 0xe34f60ef.
Lemma F_6c9f4 : fetch_word Plain.M.loaded_segments (0x6ca4c : word) = Some W_6c9f4.
Proof. vm_refl. Qed.
Lemma D_6c9f4 : decode_any W_6c9f4 = Some (Jal 1 2057780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9f8 : bv 32 := 0x00000513.
Lemma F_6c9f8 : fetch_word Plain.M.loaded_segments (0x6ca50 : word) = Some W_6c9f8.
Proof. vm_refl. Qed.
Lemma D_6c9f8 : decode_any W_6c9f8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6c9fc : bv 32 := 0x02813083.
Lemma F_6c9fc : fetch_word Plain.M.loaded_segments (0x6ca54 : word) = Some W_6c9fc.
Proof. vm_refl. Qed.
Lemma D_6c9fc : decode_any W_6c9fc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca00 : bv 32 := 0x02013403.
Lemma F_6ca00 : fetch_word Plain.M.loaded_segments (0x6ca58 : word) = Some W_6ca00.
Proof. vm_refl. Qed.
Lemma D_6ca00 : decode_any W_6ca00 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca04 : bv 32 := 0x01813483.
Lemma F_6ca04 : fetch_word Plain.M.loaded_segments (0x6ca5c : word) = Some W_6ca04.
Proof. vm_refl. Qed.
Lemma D_6ca04 : decode_any W_6ca04 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca08 : bv 32 := 0x01013903.
Lemma F_6ca08 : fetch_word Plain.M.loaded_segments (0x6ca60 : word) = Some W_6ca08.
Proof. vm_refl. Qed.
Lemma D_6ca08 : decode_any W_6ca08 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca0c : bv 32 := 0x00813983.
Lemma F_6ca0c : fetch_word Plain.M.loaded_segments (0x6ca64 : word) = Some W_6ca0c.
Proof. vm_refl. Qed.
Lemma D_6ca0c : decode_any W_6ca0c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca10 : bv 32 := 0x00013a03.
Lemma F_6ca10 : fetch_word Plain.M.loaded_segments (0x6ca68 : word) = Some W_6ca10.
Proof. vm_refl. Qed.
Lemma D_6ca10 : decode_any W_6ca10 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca14 : bv 32 := 0x03010113.
Lemma F_6ca14 : fetch_word Plain.M.loaded_segments (0x6ca6c : word) = Some W_6ca14.
Proof. vm_refl. Qed.
Lemma D_6ca14 : decode_any W_6ca14 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca18 : bv 32 := 0x00008067.
Lemma F_6ca18 : fetch_word Plain.M.loaded_segments (0x6ca70 : word) = Some W_6ca18.
Proof. vm_refl. Qed.
Lemma D_6ca18 : decode_any W_6ca18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca1c : bv 32 := 0x00050993.
Lemma F_6ca1c : fetch_word Plain.M.loaded_segments (0x6ca74 : word) = Some W_6ca1c.
Proof. vm_refl. Qed.
Lemma D_6ca1c : decode_any W_6ca1c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca20 : bv 32 := 0x00058913.
Lemma F_6ca20 : fetch_word Plain.M.loaded_segments (0x6ca78 : word) = Some W_6ca20.
Proof. vm_refl. Qed.
Lemma D_6ca20 : decode_any W_6ca20 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca24 : bv 32 := 0x00060a13.
Lemma F_6ca24 : fetch_word Plain.M.loaded_segments (0x6ca7c : word) = Some W_6ca24.
Proof. vm_refl. Qed.
Lemma D_6ca24 : decode_any W_6ca24 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca28 : bv 32 := 0x00100513.
Lemma F_6ca28 : fetch_word Plain.M.loaded_segments (0x6ca80 : word) = Some W_6ca28.
Proof. vm_refl. Qed.
Lemma D_6ca28 : decode_any W_6ca28 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca2c : bv 32 := 0x04000593.
Lemma F_6ca2c : fetch_word Plain.M.loaded_segments (0x6ca84 : word) = Some W_6ca2c.
Proof. vm_refl. Qed.
Lemma D_6ca2c : decode_any W_6ca2c = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca30 : bv 32 := 0x00100493.
Lemma F_6ca30 : fetch_word Plain.M.loaded_segments (0x6ca88 : word) = Some W_6ca30.
Proof. vm_refl. Qed.
Lemma D_6ca30 : decode_any W_6ca30 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca34 : bv 32 := 0x7b08d0ef.
Lemma F_6ca34 : fetch_word Plain.M.loaded_segments (0x6ca8c : word) = Some W_6ca34.
Proof. vm_refl. Qed.
Lemma D_6ca34 : decode_any W_6ca34 = Some (Jal 1 579504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca38 : bv 32 := 0x02050463.
Lemma F_6ca38 : fetch_word Plain.M.loaded_segments (0x6ca90 : word) = Some W_6ca38.
Proof. vm_refl. Qed.
Lemma D_6ca38 : decode_any W_6ca38 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca3c : bv 32 := 0xfe8a059b.
Lemma F_6ca3c : fetch_word Plain.M.loaded_segments (0x6ca94 : word) = Some W_6ca3c.
Proof. vm_refl. Qed.
Lemma D_6ca3c : decode_any W_6ca3c = Some (OpImm32 11 20 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca40 : bv 32 := 0xff75f593.
Lemma F_6ca40 : fetch_word Plain.M.loaded_segments (0x6ca98 : word) = Some W_6ca40.
Proof. vm_refl. Qed.
Lemma D_6ca40 : decode_any W_6ca40 = Some (OpImm ALU_AND 11 11 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca44 : bv 32 := 0x01352023.
Lemma F_6ca44 : fetch_word Plain.M.loaded_segments (0x6ca9c : word) = Some W_6ca44.
Proof. vm_refl. Qed.
Lemma D_6ca44 : decode_any W_6ca44 = Some (Store SZ4 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca48 : bv 32 := 0x01252223.
Lemma F_6ca48 : fetch_word Plain.M.loaded_segments (0x6caa0 : word) = Some W_6ca48.
Proof. vm_refl. Qed.
Lemma D_6ca48 : decode_any W_6ca48 = Some (Store SZ4 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca4c : bv 32 := 0x01452423.
Lemma F_6ca4c : fetch_word Plain.M.loaded_segments (0x6caa4 : word) = Some W_6ca4c.
Proof. vm_refl. Qed.
Lemma D_6ca4c : decode_any W_6ca4c = Some (Store SZ4 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca50 : bv 32 := 0x00852823.
Lemma F_6ca50 : fetch_word Plain.M.loaded_segments (0x6caa8 : word) = Some W_6ca50.
Proof. vm_refl. Qed.
Lemma D_6ca50 : decode_any W_6ca50 = Some (Store SZ4 10 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca54 : bv 32 := 0x02058a63.
Lemma F_6ca54 : fetch_word Plain.M.loaded_segments (0x6caac : word) = Some W_6ca54.
Proof. vm_refl. Qed.
Lemma D_6ca54 : decode_any W_6ca54 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca58 : bv 32 := 0x00100593.
Lemma F_6ca58 : fetch_word Plain.M.loaded_segments (0x6cab0 : word) = Some W_6ca58.
Proof. vm_refl. Qed.
Lemma D_6ca58 : decode_any W_6ca58 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca5c : bv 32 := 0x0300006f.
Lemma F_6ca5c : fetch_word Plain.M.loaded_segments (0x6cab4 : word) = Some W_6ca5c.
Proof. vm_refl. Qed.
Lemma D_6ca5c : decode_any W_6ca5c = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca60 : bv 32 := 0x000a6517.
Lemma F_6ca60 : fetch_word Plain.M.loaded_segments (0x6cab8 : word) = Some W_6ca60.
Proof. vm_refl. Qed.
Lemma D_6ca60 : decode_any W_6ca60 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca64 : bv 32 := 0xb1053503.
Lemma F_6ca64 : fetch_word Plain.M.loaded_segments (0x6cabc : word) = Some W_6ca64.
Proof. vm_refl. Qed.
Lemma D_6ca64 : decode_any W_6ca64 = Some (Load SZ8 true 10 10 2832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca68 : bv 32 := 0x00052503.
Lemma F_6ca68 : fetch_word Plain.M.loaded_segments (0x6cac0 : word) = Some W_6ca68.
Proof. vm_refl. Qed.
Lemma D_6ca68 : decode_any W_6ca68 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca6c : bv 32 := 0x00500593.
Lemma F_6ca6c : fetch_word Plain.M.loaded_segments (0x6cac4 : word) = Some W_6ca6c.
Proof. vm_refl. Qed.
Lemma D_6ca6c : decode_any W_6ca6c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca70 : bv 32 := 0xf8a5c4e3.
Lemma F_6ca70 : fetch_word Plain.M.loaded_segments (0x6cac8 : word) = Some W_6ca70.
Proof. vm_refl. Qed.
Lemma D_6ca70 : decode_any W_6ca70 = Some (Branch BC_LT 11 10 8072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca74 : bv 32 := 0xfffa6517.
Lemma F_6ca74 : fetch_word Plain.M.loaded_segments (0x6cacc : word) = Some W_6ca74.
Proof. vm_refl. Qed.
Lemma D_6ca74 : decode_any W_6ca74 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca78 : bv 32 := 0xfffa9597.
Lemma F_6ca78 : fetch_word Plain.M.loaded_segments (0x6cad0 : word) = Some W_6ca78.
Proof. vm_refl. Qed.
Lemma D_6ca78 : decode_any W_6ca78 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca7c : bv 32 := 0xc0e50513.
Lemma F_6ca7c : fetch_word Plain.M.loaded_segments (0x6cad4 : word) = Some W_6ca7c.
Proof. vm_refl. Qed.
Lemma D_6ca7c : decode_any W_6ca7c = Some (OpImm ALU_ADD 10 10 3086, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca80 : bv 32 := 0xf5c58593.
Lemma F_6ca80 : fetch_word Plain.M.loaded_segments (0x6cad8 : word) = Some W_6ca80.
Proof. vm_refl. Qed.
Lemma D_6ca80 : decode_any W_6ca80 = Some (OpImm ALU_ADD 11 11 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca84 : bv 32 := 0xebdff06f.
Lemma F_6ca84 : fetch_word Plain.M.loaded_segments (0x6cadc : word) = Some W_6ca84.
Proof. vm_refl. Qed.
Lemma D_6ca84 : decode_any W_6ca84 = Some (Jal 0 2096828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca88 : bv 32 := 0x00300593.
Lemma F_6ca88 : fetch_word Plain.M.loaded_segments (0x6cae0 : word) = Some W_6ca88.
Proof. vm_refl. Qed.
Lemma D_6ca88 : decode_any W_6ca88 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca8c : bv 32 := 0x00b52623.
Lemma F_6ca8c : fetch_word Plain.M.loaded_segments (0x6cae4 : word) = Some W_6ca8c.
Proof. vm_refl. Qed.
Lemma D_6ca8c : decode_any W_6ca8c = Some (Store SZ4 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca90 : bv 32 := 0x0310000f.
Lemma F_6ca90 : fetch_word Plain.M.loaded_segments (0x6cae8 : word) = Some W_6ca90.
Proof. vm_refl. Qed.
Lemma D_6ca90 : decode_any W_6ca90 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca94 : bv 32 := 0x00952a23.
Lemma F_6ca94 : fetch_word Plain.M.loaded_segments (0x6caec : word) = Some W_6ca94.
Proof. vm_refl. Qed.
Lemma D_6ca94 : decode_any W_6ca94 = Some (Store SZ4 10 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca98 : bv 32 := 0x0330000f.
Lemma F_6ca98 : fetch_word Plain.M.loaded_segments (0x6caf0 : word) = Some W_6ca98.
Proof. vm_refl. Qed.
Lemma D_6ca98 : decode_any W_6ca98 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ca9c : bv 32 := 0x02052023.
Lemma F_6ca9c : fetch_word Plain.M.loaded_segments (0x6caf4 : word) = Some W_6ca9c.
Proof. vm_refl. Qed.
Lemma D_6ca9c : decode_any W_6ca9c = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caa0 : bv 32 := 0xf5dff06f.
Lemma F_6caa0 : fetch_word Plain.M.loaded_segments (0x6caf8 : word) = Some W_6caa0.
Proof. vm_refl. Qed.
Lemma D_6caa0 : decode_any W_6caa0 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caa4 : bv 32 := 0x00050663.
Lemma F_6caa4 : fetch_word Plain.M.loaded_segments (0x6cafc : word) = Some W_6caa4.
Proof. vm_refl. Qed.
Lemma D_6caa4 : decode_any W_6caa4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caa8 : bv 32 := 0x01052503.
Lemma F_6caa8 : fetch_word Plain.M.loaded_segments (0x6cb00 : word) = Some W_6caa8.
Proof. vm_refl. Qed.
Lemma D_6caa8 : decode_any W_6caa8 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6caac : bv 32 := 0x00008067.
Lemma F_6caac : fetch_word Plain.M.loaded_segments (0x6cb04 : word) = Some W_6caac.
Proof. vm_refl. Qed.
Lemma D_6caac : decode_any W_6caac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbb0 : bv 32 := 0xff010113.
Lemma F_6cbb0 : fetch_word Plain.M.loaded_segments (0x6cc08 : word) = Some W_6cbb0.
Proof. vm_refl. Qed.
Lemma D_6cbb0 : decode_any W_6cbb0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbb4 : bv 32 := 0x00113423.
Lemma F_6cbb4 : fetch_word Plain.M.loaded_segments (0x6cc0c : word) = Some W_6cbb4.
Proof. vm_refl. Qed.
Lemma D_6cbb4 : decode_any W_6cbb4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbb8 : bv 32 := 0x00813023.
Lemma F_6cbb8 : fetch_word Plain.M.loaded_segments (0x6cc10 : word) = Some W_6cbb8.
Proof. vm_refl. Qed.
Lemma D_6cbb8 : decode_any W_6cbb8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbbc : bv 32 := 0x02050c63.
Lemma F_6cbbc : fetch_word Plain.M.loaded_segments (0x6cc14 : word) = Some W_6cbbc.
Proof. vm_refl. Qed.
Lemma D_6cbbc : decode_any W_6cbbc = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbc0 : bv 32 := 0x0a8000ef.
Lemma F_6cbc0 : fetch_word Plain.M.loaded_segments (0x6cc18 : word) = Some W_6cbc0.
Proof. vm_refl. Qed.
Lemma D_6cbc0 : decode_any W_6cbc0 = Some (Jal 1 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbc4 : bv 32 := 0x04050c63.
Lemma F_6cbc4 : fetch_word Plain.M.loaded_segments (0x6cc1c : word) = Some W_6cbc4.
Proof. vm_refl. Qed.
Lemma D_6cbc4 : decode_any W_6cbc4 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbc8 : bv 32 := 0x00456603.
Lemma F_6cbc8 : fetch_word Plain.M.loaded_segments (0x6cc20 : word) = Some W_6cbc8.
Proof. vm_refl. Qed.
Lemma D_6cbc8 : decode_any W_6cbc8 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbcc : bv 32 := 0x01056683.
Lemma F_6cbcc : fetch_word Plain.M.loaded_segments (0x6cc24 : word) = Some W_6cbcc.
Proof. vm_refl. Qed.
Lemma D_6cbcc : decode_any W_6cbcc = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbd0 : bv 32 := 0x03853583.
Lemma F_6cbd0 : fetch_word Plain.M.loaded_segments (0x6cc28 : word) = Some W_6cbd0.
Proof. vm_refl. Qed.
Lemma D_6cbd0 : decode_any W_6cbd0 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbd4 : bv 32 := 0x02c68633.
Lemma F_6cbd4 : fetch_word Plain.M.loaded_segments (0x6cc2c : word) = Some W_6cbd4.
Proof. vm_refl. Qed.
Lemma D_6cbd4 : decode_any W_6cbd4 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbd8 : bv 32 := 0x00261613.
Lemma F_6cbd8 : fetch_word Plain.M.loaded_segments (0x6cc30 : word) = Some W_6cbd8.
Proof. vm_refl. Qed.
Lemma D_6cbd8 : decode_any W_6cbd8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbdc : bv 32 := 0x00050413.
Lemma F_6cbdc : fetch_word Plain.M.loaded_segments (0x6cc34 : word) = Some W_6cbdc.
Proof. vm_refl. Qed.
Lemma D_6cbdc : decode_any W_6cbdc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbe0 : bv 32 := 0x00058513.
Lemma F_6cbe0 : fetch_word Plain.M.loaded_segments (0x6cc38 : word) = Some W_6cbe0.
Proof. vm_refl. Qed.
Lemma D_6cbe0 : decode_any W_6cbe0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbe4 : bv 32 := 0x00000593.
Lemma F_6cbe4 : fetch_word Plain.M.loaded_segments (0x6cc3c : word) = Some W_6cbe4.
Proof. vm_refl. Qed.
Lemma D_6cbe4 : decode_any W_6cbe4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbe8 : bv 32 := 0x5f09d0ef.
Lemma F_6cbe8 : fetch_word Plain.M.loaded_segments (0x6cc40 : word) = Some W_6cbe8.
Proof. vm_refl. Qed.
Lemma D_6cbe8 : decode_any W_6cbe8 = Some (Jal 1 644592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbec : bv 32 := 0x00040513.
Lemma F_6cbec : fetch_word Plain.M.loaded_segments (0x6cc44 : word) = Some W_6cbec.
Proof. vm_refl. Qed.
Lemma D_6cbec : decode_any W_6cbec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cbf0 : bv 32 := 0x0680006f.
Lemma F_6cbf0 : fetch_word Plain.M.loaded_segments (0x6cc48 : word) = Some W_6cbf0.
Proof. vm_refl. Qed.
Lemma D_6cbf0 : decode_any W_6cbf0 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc1c : bv 32 := 0x000a6517.
Lemma F_6cc1c : fetch_word Plain.M.loaded_segments (0x6cc74 : word) = Some W_6cc1c.
Proof. vm_refl. Qed.
Lemma D_6cc1c : decode_any W_6cc1c = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc20 : bv 32 := 0x95453503.
Lemma F_6cc20 : fetch_word Plain.M.loaded_segments (0x6cc78 : word) = Some W_6cc20.
Proof. vm_refl. Qed.
Lemma D_6cc20 : decode_any W_6cc20 = Some (Load SZ8 true 10 10 2388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc24 : bv 32 := 0x00052503.
Lemma F_6cc24 : fetch_word Plain.M.loaded_segments (0x6cc7c : word) = Some W_6cc24.
Proof. vm_refl. Qed.
Lemma D_6cc24 : decode_any W_6cc24 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc28 : bv 32 := 0x00500593.
Lemma F_6cc28 : fetch_word Plain.M.loaded_segments (0x6cc80 : word) = Some W_6cc28.
Proof. vm_refl. Qed.
Lemma D_6cc28 : decode_any W_6cc28 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc2c : bv 32 := 0x02a5c463.
Lemma F_6cc2c : fetch_word Plain.M.loaded_segments (0x6cc84 : word) = Some W_6cc2c.
Proof. vm_refl. Qed.
Lemma D_6cc2c : decode_any W_6cc2c = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc30 : bv 32 := 0xfffa6517.
Lemma F_6cc30 : fetch_word Plain.M.loaded_segments (0x6cc88 : word) = Some W_6cc30.
Proof. vm_refl. Qed.
Lemma D_6cc30 : decode_any W_6cc30 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc34 : bv 32 := 0xfffac597.
Lemma F_6cc34 : fetch_word Plain.M.loaded_segments (0x6cc8c : word) = Some W_6cc34.
Proof. vm_refl. Qed.
Lemma D_6cc34 : decode_any W_6cc34 = Some (Auipc 11 1048492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc38 : bv 32 := 0xa5250513.
Lemma F_6cc38 : fetch_word Plain.M.loaded_segments (0x6cc90 : word) = Some W_6cc38.
Proof. vm_refl. Qed.
Lemma D_6cc38 : decode_any W_6cc38 = Some (OpImm ALU_ADD 10 10 2642, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc3c : bv 32 := 0x5eb58593.
Lemma F_6cc3c : fetch_word Plain.M.loaded_segments (0x6cc94 : word) = Some W_6cc3c.
Proof. vm_refl. Qed.
Lemma D_6cc3c : decode_any W_6cc3c = Some (OpImm ALU_ADD 11 11 1515, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc40 : bv 32 := 0x00000613.
Lemma F_6cc40 : fetch_word Plain.M.loaded_segments (0x6cc98 : word) = Some W_6cc40.
Proof. vm_refl. Qed.
Lemma D_6cc40 : decode_any W_6cc40 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc44 : bv 32 := 0x00813083.
Lemma F_6cc44 : fetch_word Plain.M.loaded_segments (0x6cc9c : word) = Some W_6cc44.
Proof. vm_refl. Qed.
Lemma D_6cc44 : decode_any W_6cc44 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc48 : bv 32 := 0x00013403.
Lemma F_6cc48 : fetch_word Plain.M.loaded_segments (0x6cca0 : word) = Some W_6cc48.
Proof. vm_refl. Qed.
Lemma D_6cc48 : decode_any W_6cc48 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc4c : bv 32 := 0x01010113.
Lemma F_6cc4c : fetch_word Plain.M.loaded_segments (0x6cca4 : word) = Some W_6cc4c.
Proof. vm_refl. Qed.
Lemma D_6cc4c : decode_any W_6cc4c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc50 : bv 32 := 0xc74f606f.
Lemma F_6cc50 : fetch_word Plain.M.loaded_segments (0x6cca8 : word) = Some W_6cc50.
Proof. vm_refl. Qed.
Lemma D_6cc50 : decode_any W_6cc50 = Some (Jal 0 2057332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc58 : bv 32 := 0x00813083.
Lemma F_6cc58 : fetch_word Plain.M.loaded_segments (0x6ccb0 : word) = Some W_6cc58.
Proof. vm_refl. Qed.
Lemma D_6cc58 : decode_any W_6cc58 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc5c : bv 32 := 0x00013403.
Lemma F_6cc5c : fetch_word Plain.M.loaded_segments (0x6ccb4 : word) = Some W_6cc5c.
Proof. vm_refl. Qed.
Lemma D_6cc5c : decode_any W_6cc5c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc60 : bv 32 := 0x01010113.
Lemma F_6cc60 : fetch_word Plain.M.loaded_segments (0x6ccb8 : word) = Some W_6cc60.
Proof. vm_refl. Qed.
Lemma D_6cc60 : decode_any W_6cc60 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc64 : bv 32 := 0x00008067.
Lemma F_6cc64 : fetch_word Plain.M.loaded_segments (0x6ccbc : word) = Some W_6cc64.
Proof. vm_refl. Qed.
Lemma D_6cc64 : decode_any W_6cc64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc68 : bv 32 := 0xfe010113.
Lemma F_6cc68 : fetch_word Plain.M.loaded_segments (0x6ccc0 : word) = Some W_6cc68.
Proof. vm_refl. Qed.
Lemma D_6cc68 : decode_any W_6cc68 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc6c : bv 32 := 0x00113c23.
Lemma F_6cc6c : fetch_word Plain.M.loaded_segments (0x6ccc4 : word) = Some W_6cc6c.
Proof. vm_refl. Qed.
Lemma D_6cc6c : decode_any W_6cc6c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc70 : bv 32 := 0x00813823.
Lemma F_6cc70 : fetch_word Plain.M.loaded_segments (0x6ccc8 : word) = Some W_6cc70.
Proof. vm_refl. Qed.
Lemma D_6cc70 : decode_any W_6cc70 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc74 : bv 32 := 0x00913423.
Lemma F_6cc74 : fetch_word Plain.M.loaded_segments (0x6cccc : word) = Some W_6cc74.
Proof. vm_refl. Qed.
Lemma D_6cc74 : decode_any W_6cc74 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc78 : bv 32 := 0x02050a63.
Lemma F_6cc78 : fetch_word Plain.M.loaded_segments (0x6ccd0 : word) = Some W_6cc78.
Proof. vm_refl. Qed.
Lemma D_6cc78 : decode_any W_6cc78 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc7c : bv 32 := 0x00050493.
Lemma F_6cc7c : fetch_word Plain.M.loaded_segments (0x6ccd4 : word) = Some W_6cc7c.
Proof. vm_refl. Qed.
Lemma D_6cc7c : decode_any W_6cc7c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc80 : bv 32 := 0x00052503.
Lemma F_6cc80 : fetch_word Plain.M.loaded_segments (0x6ccd8 : word) = Some W_6cc80.
Proof. vm_refl. Qed.
Lemma D_6cc80 : decode_any W_6cc80 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc84 : bv 32 := 0x0044a583.
Lemma F_6cc84 : fetch_word Plain.M.loaded_segments (0x6ccdc : word) = Some W_6cc84.
Proof. vm_refl. Qed.
Lemma D_6cc84 : decode_any W_6cc84 = Some (Load SZ4 true 11 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc88 : bv 32 := 0x0084a603.
Lemma F_6cc88 : fetch_word Plain.M.loaded_segments (0x6cce0 : word) = Some W_6cc88.
Proof. vm_refl. Qed.
Lemma D_6cc88 : decode_any W_6cc88 = Some (Load SZ4 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc8c : bv 32 := 0x9e1ff0ef.
Lemma F_6cc8c : fetch_word Plain.M.loaded_segments (0x6cce4 : word) = Some W_6cc8c.
Proof. vm_refl. Qed.
Lemma D_6cc8c : decode_any W_6cc8c = Some (Jal 1 2095584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc90 : bv 32 := 0x04050263.
Lemma F_6cc90 : fetch_word Plain.M.loaded_segments (0x6cce8 : word) = Some W_6cc90.
Proof. vm_refl. Qed.
Lemma D_6cc90 : decode_any W_6cc90 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc94 : bv 32 := 0x00050413.
Lemma F_6cc94 : fetch_word Plain.M.loaded_segments (0x6ccec : word) = Some W_6cc94.
Proof. vm_refl. Qed.
Lemma D_6cc94 : decode_any W_6cc94 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc98 : bv 32 := 0x08a48063.
Lemma F_6cc98 : fetch_word Plain.M.loaded_segments (0x6ccf0 : word) = Some W_6cc98.
Proof. vm_refl. Qed.
Lemma D_6cc98 : decode_any W_6cc98 = Some (Branch BC_EQ 9 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cc9c : bv 32 := 0x00c4a503.
Lemma F_6cc9c : fetch_word Plain.M.loaded_segments (0x6ccf4 : word) = Some W_6cc9c.
Proof. vm_refl. Qed.
Lemma D_6cc9c : decode_any W_6cc9c = Some (Load SZ4 true 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cca0 : bv 32 := 0x08a05463.
Lemma F_6cca0 : fetch_word Plain.M.loaded_segments (0x6ccf8 : word) = Some W_6cca0.
Proof. vm_refl. Qed.
Lemma D_6cca0 : decode_any W_6cca0 = Some (Branch BC_GE 0 10 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cca4 : bv 32 := 0x00a42623.
Lemma F_6cca4 : fetch_word Plain.M.loaded_segments (0x6ccfc : word) = Some W_6cca4.
Proof. vm_refl. Qed.
Lemma D_6cca4 : decode_any W_6cca4 = Some (Store SZ4 8 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cca8 : bv 32 := 0x0ac0006f.
Lemma F_6cca8 : fetch_word Plain.M.loaded_segments (0x6cd00 : word) = Some W_6cca8.
Proof. vm_refl. Qed.
Lemma D_6cca8 : decode_any W_6cca8 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccd4 : bv 32 := 0x000a6517.
Lemma F_6ccd4 : fetch_word Plain.M.loaded_segments (0x6cd2c : word) = Some W_6ccd4.
Proof. vm_refl. Qed.
Lemma D_6ccd4 : decode_any W_6ccd4 = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccd8 : bv 32 := 0x89c53503.
Lemma F_6ccd8 : fetch_word Plain.M.loaded_segments (0x6cd30 : word) = Some W_6ccd8.
Proof. vm_refl. Qed.
Lemma D_6ccd8 : decode_any W_6ccd8 = Some (Load SZ8 true 10 10 2204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccdc : bv 32 := 0x00052503.
Lemma F_6ccdc : fetch_word Plain.M.loaded_segments (0x6cd34 : word) = Some W_6ccdc.
Proof. vm_refl. Qed.
Lemma D_6ccdc : decode_any W_6ccdc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cce0 : bv 32 := 0x00500593.
Lemma F_6cce0 : fetch_word Plain.M.loaded_segments (0x6cd38 : word) = Some W_6cce0.
Proof. vm_refl. Qed.
Lemma D_6cce0 : decode_any W_6cce0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cce4 : bv 32 := 0x02a5c663.
Lemma F_6cce4 : fetch_word Plain.M.loaded_segments (0x6cd3c : word) = Some W_6cce4.
Proof. vm_refl. Qed.
Lemma D_6cce4 : decode_any W_6cce4 = Some (Branch BC_LT 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cce8 : bv 32 := 0xfffa6517.
Lemma F_6cce8 : fetch_word Plain.M.loaded_segments (0x6cd40 : word) = Some W_6cce8.
Proof. vm_refl. Qed.
Lemma D_6cce8 : decode_any W_6cce8 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccec : bv 32 := 0xfffaf597.
Lemma F_6ccec : fetch_word Plain.M.loaded_segments (0x6cd44 : word) = Some W_6ccec.
Proof. vm_refl. Qed.
Lemma D_6ccec : decode_any W_6ccec = Some (Auipc 11 1048495, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccf0 : bv 32 := 0x99a50513.
Lemma F_6ccf0 : fetch_word Plain.M.loaded_segments (0x6cd48 : word) = Some W_6ccf0.
Proof. vm_refl. Qed.
Lemma D_6ccf0 : decode_any W_6ccf0 = Some (OpImm ALU_ADD 10 10 2458, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccf4 : bv 32 := 0xc2d58593.
Lemma F_6ccf4 : fetch_word Plain.M.loaded_segments (0x6cd4c : word) = Some W_6ccf4.
Proof. vm_refl. Qed.
Lemma D_6ccf4 : decode_any W_6ccf4 = Some (OpImm ALU_ADD 11 11 3117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccf8 : bv 32 := 0x00000613.
Lemma F_6ccf8 : fetch_word Plain.M.loaded_segments (0x6cd50 : word) = Some W_6ccf8.
Proof. vm_refl. Qed.
Lemma D_6ccf8 : decode_any W_6ccf8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6ccfc : bv 32 := 0x01813083.
Lemma F_6ccfc : fetch_word Plain.M.loaded_segments (0x6cd54 : word) = Some W_6ccfc.
Proof. vm_refl. Qed.
Lemma D_6ccfc : decode_any W_6ccfc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd00 : bv 32 := 0x01013403.
Lemma F_6cd00 : fetch_word Plain.M.loaded_segments (0x6cd58 : word) = Some W_6cd00.
Proof. vm_refl. Qed.
Lemma D_6cd00 : decode_any W_6cd00 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd04 : bv 32 := 0x00813483.
Lemma F_6cd04 : fetch_word Plain.M.loaded_segments (0x6cd5c : word) = Some W_6cd04.
Proof. vm_refl. Qed.
Lemma D_6cd04 : decode_any W_6cd04 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd08 : bv 32 := 0x02010113.
Lemma F_6cd08 : fetch_word Plain.M.loaded_segments (0x6cd60 : word) = Some W_6cd08.
Proof. vm_refl. Qed.
Lemma D_6cd08 : decode_any W_6cd08 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd0c : bv 32 := 0xbb8f606f.
Lemma F_6cd0c : fetch_word Plain.M.loaded_segments (0x6cd64 : word) = Some W_6cd0c.
Proof. vm_refl. Qed.
Lemma D_6cd0c : decode_any W_6cd0c = Some (Jal 0 2057144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd54 : bv 32 := 0x0184b503.
Lemma F_6cd54 : fetch_word Plain.M.loaded_segments (0x6cdac : word) = Some W_6cd54.
Proof. vm_refl. Qed.
Lemma D_6cd54 : decode_any W_6cd54 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd58 : bv 32 := 0x00a43c23.
Lemma F_6cd58 : fetch_word Plain.M.loaded_segments (0x6cdb0 : word) = Some W_6cd58.
Proof. vm_refl. Qed.
Lemma D_6cd58 : decode_any W_6cd58 = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd5c : bv 32 := 0x00040513.
Lemma F_6cd5c : fetch_word Plain.M.loaded_segments (0x6cdb4 : word) = Some W_6cd5c.
Proof. vm_refl. Qed.
Lemma D_6cd5c : decode_any W_6cd5c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd60 : bv 32 := 0x00048593.
Lemma F_6cd60 : fetch_word Plain.M.loaded_segments (0x6cdb8 : word) = Some W_6cd60.
Proof. vm_refl. Qed.
Lemma D_6cd60 : decode_any W_6cd60 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd64 : bv 32 := 0x214000ef.
Lemma F_6cd64 : fetch_word Plain.M.loaded_segments (0x6cdbc : word) = Some W_6cd64.
Proof. vm_refl. Qed.
Lemma D_6cd64 : decode_any W_6cd64 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd68 : bv 32 := 0x0284b583.
Lemma F_6cd68 : fetch_word Plain.M.loaded_segments (0x6cdc0 : word) = Some W_6cd68.
Proof. vm_refl. Qed.
Lemma D_6cd68 : decode_any W_6cd68 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd6c : bv 32 := 0x02840513.
Lemma F_6cd6c : fetch_word Plain.M.loaded_segments (0x6cdc4 : word) = Some W_6cd6c.
Proof. vm_refl. Qed.
Lemma D_6cd6c : decode_any W_6cd6c = Some (OpImm ALU_ADD 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd70 : bv 32 := 0x88df60ef.
Lemma F_6cd70 : fetch_word Plain.M.loaded_segments (0x6cdc8 : word) = Some W_6cd70.
Proof. vm_refl. Qed.
Lemma D_6cd70 : decode_any W_6cd70 = Some (Jal 1 2058380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd74 : bv 32 := 0x0204a503.
Lemma F_6cd74 : fetch_word Plain.M.loaded_segments (0x6cdcc : word) = Some W_6cd74.
Proof. vm_refl. Qed.
Lemma D_6cd74 : decode_any W_6cd74 = Some (Load SZ4 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd78 : bv 32 := 0x02a42023.
Lemma F_6cd78 : fetch_word Plain.M.loaded_segments (0x6cdd0 : word) = Some W_6cd78.
Proof. vm_refl. Qed.
Lemma D_6cd78 : decode_any W_6cd78 = Some (Store SZ4 8 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd7c : bv 32 := 0x00040513.
Lemma F_6cd7c : fetch_word Plain.M.loaded_segments (0x6cdd4 : word) = Some W_6cd7c.
Proof. vm_refl. Qed.
Lemma D_6cd7c : decode_any W_6cd7c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd80 : bv 32 := 0x00000593.
Lemma F_6cd80 : fetch_word Plain.M.loaded_segments (0x6cdd8 : word) = Some W_6cd80.
Proof. vm_refl. Qed.
Lemma D_6cd80 : decode_any W_6cd80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd84 : bv 32 := 0x741010ef.
Lemma F_6cd84 : fetch_word Plain.M.loaded_segments (0x6cddc : word) = Some W_6cd84.
Proof. vm_refl. Qed.
Lemma D_6cd84 : decode_any W_6cd84 = Some (Jal 1 8000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd88 : bv 32 := 0x00040513.
Lemma F_6cd88 : fetch_word Plain.M.loaded_segments (0x6cde0 : word) = Some W_6cd88.
Proof. vm_refl. Qed.
Lemma D_6cd88 : decode_any W_6cd88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd8c : bv 32 := 0x01813083.
Lemma F_6cd8c : fetch_word Plain.M.loaded_segments (0x6cde4 : word) = Some W_6cd8c.
Proof. vm_refl. Qed.
Lemma D_6cd8c : decode_any W_6cd8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd90 : bv 32 := 0x01013403.
Lemma F_6cd90 : fetch_word Plain.M.loaded_segments (0x6cde8 : word) = Some W_6cd90.
Proof. vm_refl. Qed.
Lemma D_6cd90 : decode_any W_6cd90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd94 : bv 32 := 0x00813483.
Lemma F_6cd94 : fetch_word Plain.M.loaded_segments (0x6cdec : word) = Some W_6cd94.
Proof. vm_refl. Qed.
Lemma D_6cd94 : decode_any W_6cd94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd98 : bv 32 := 0x02010113.
Lemma F_6cd98 : fetch_word Plain.M.loaded_segments (0x6cdf0 : word) = Some W_6cd98.
Proof. vm_refl. Qed.
Lemma D_6cd98 : decode_any W_6cd98 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cd9c : bv 32 := 0x00008067.
Lemma F_6cd9c : fetch_word Plain.M.loaded_segments (0x6cdf4 : word) = Some W_6cd9c.
Proof. vm_refl. Qed.
Lemma D_6cd9c : decode_any W_6cd9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda0 : bv 32 := 0x00058463.
Lemma F_6cda0 : fetch_word Plain.M.loaded_segments (0x6cdf8 : word) = Some W_6cda0.
Proof. vm_refl. Qed.
Lemma D_6cda0 : decode_any W_6cda0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda4 : bv 32 := 0x0005a023.
Lemma F_6cda4 : fetch_word Plain.M.loaded_segments (0x6cdfc : word) = Some W_6cda4.
Proof. vm_refl. Qed.
Lemma D_6cda4 : decode_any W_6cda4 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cda8 : bv 32 := 0x00060463.
Lemma F_6cda8 : fetch_word Plain.M.loaded_segments (0x6ce00 : word) = Some W_6cda8.
Proof. vm_refl. Qed.
Lemma D_6cda8 : decode_any W_6cda8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdac : bv 32 := 0x00062023.
Lemma F_6cdac : fetch_word Plain.M.loaded_segments (0x6ce04 : word) = Some W_6cdac.
Proof. vm_refl. Qed.
Lemma D_6cdac : decode_any W_6cdac = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb0 : bv 32 := 0x00068463.
Lemma F_6cdb0 : fetch_word Plain.M.loaded_segments (0x6ce08 : word) = Some W_6cdb0.
Proof. vm_refl. Qed.
Lemma D_6cdb0 : decode_any W_6cdb0 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb4 : bv 32 := 0x0006a023.
Lemma F_6cdb4 : fetch_word Plain.M.loaded_segments (0x6ce0c : word) = Some W_6cdb4.
Proof. vm_refl. Qed.
Lemma D_6cdb4 : decode_any W_6cdb4 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdb8 : bv 32 := 0x02050a63.
Lemma F_6cdb8 : fetch_word Plain.M.loaded_segments (0x6ce10 : word) = Some W_6cdb8.
Proof. vm_refl. Qed.
Lemma D_6cdb8 : decode_any W_6cdb8 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdbc : bv 32 := 0x00058663.
Lemma F_6cdbc : fetch_word Plain.M.loaded_segments (0x6ce14 : word) = Some W_6cdbc.
Proof. vm_refl. Qed.
Lemma D_6cdbc : decode_any W_6cdbc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc0 : bv 32 := 0x00052703.
Lemma F_6cdc0 : fetch_word Plain.M.loaded_segments (0x6ce18 : word) = Some W_6cdc0.
Proof. vm_refl. Qed.
Lemma D_6cdc0 : decode_any W_6cdc0 = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc4 : bv 32 := 0x00e5a023.
Lemma F_6cdc4 : fetch_word Plain.M.loaded_segments (0x6ce1c : word) = Some W_6cdc4.
Proof. vm_refl. Qed.
Lemma D_6cdc4 : decode_any W_6cdc4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdc8 : bv 32 := 0x00060663.
Lemma F_6cdc8 : fetch_word Plain.M.loaded_segments (0x6ce20 : word) = Some W_6cdc8.
Proof. vm_refl. Qed.
Lemma D_6cdc8 : decode_any W_6cdc8 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdcc : bv 32 := 0x00452583.
Lemma F_6cdcc : fetch_word Plain.M.loaded_segments (0x6ce24 : word) = Some W_6cdcc.
Proof. vm_refl. Qed.
Lemma D_6cdcc : decode_any W_6cdcc = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd0 : bv 32 := 0x00b62023.
Lemma F_6cdd0 : fetch_word Plain.M.loaded_segments (0x6ce28 : word) = Some W_6cdd0.
Proof. vm_refl. Qed.
Lemma D_6cdd0 : decode_any W_6cdd0 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd4 : bv 32 := 0x00000593.
Lemma F_6cdd4 : fetch_word Plain.M.loaded_segments (0x6ce2c : word) = Some W_6cdd4.
Proof. vm_refl. Qed.
Lemma D_6cdd4 : decode_any W_6cdd4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cdd8 : bv 32 := 0x00068663.
Lemma F_6cdd8 : fetch_word Plain.M.loaded_segments (0x6ce30 : word) = Some W_6cdd8.
Proof. vm_refl. Qed.
Lemma D_6cdd8 : decode_any W_6cdd8 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cddc : bv 32 := 0x00852503.
Lemma F_6cddc : fetch_word Plain.M.loaded_segments (0x6ce34 : word) = Some W_6cddc.
Proof. vm_refl. Qed.
Lemma D_6cddc : decode_any W_6cddc = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde0 : bv 32 := 0x00a6a023.
Lemma F_6cde0 : fetch_word Plain.M.loaded_segments (0x6ce38 : word) = Some W_6cde0.
Proof. vm_refl. Qed.
Lemma D_6cde0 : decode_any W_6cde0 = Some (Store SZ4 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde4 : bv 32 := 0x00058513.
Lemma F_6cde4 : fetch_word Plain.M.loaded_segments (0x6ce3c : word) = Some W_6cde4.
Proof. vm_refl. Qed.
Lemma D_6cde4 : decode_any W_6cde4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cde8 : bv 32 := 0x00008067.
Lemma F_6cde8 : fetch_word Plain.M.loaded_segments (0x6ce40 : word) = Some W_6cde8.
Proof. vm_refl. Qed.
Lemma D_6cde8 : decode_any W_6cde8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef0 : bv 32 := 0x02058063.
Lemma F_6cef0 : fetch_word Plain.M.loaded_segments (0x6cf48 : word) = Some W_6cef0.
Proof. vm_refl. Qed.
Lemma D_6cef0 : decode_any W_6cef0 = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef4 : bv 32 := 0x04050463.
Lemma F_6cef4 : fetch_word Plain.M.loaded_segments (0x6cf4c : word) = Some W_6cef4.
Proof. vm_refl. Qed.
Lemma D_6cef4 : decode_any W_6cef4 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cef8 : bv 32 := 0x06a58c63.
Lemma F_6cef8 : fetch_word Plain.M.loaded_segments (0x6cf50 : word) = Some W_6cef8.
Proof. vm_refl. Qed.
Lemma D_6cef8 : decode_any W_6cef8 = Some (Branch BC_EQ 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cefc : bv 32 := 0x00050613.
Lemma F_6cefc : fetch_word Plain.M.loaded_segments (0x6cf54 : word) = Some W_6cefc.
Proof. vm_refl. Qed.
Lemma D_6cefc : decode_any W_6cefc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf00 : bv 32 := 0x00000513.
Lemma F_6cf00 : fetch_word Plain.M.loaded_segments (0x6cf58 : word) = Some W_6cf00.
Proof. vm_refl. Qed.
Lemma D_6cf00 : decode_any W_6cf00 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf04 : bv 32 := 0x0185b583.
Lemma F_6cf04 : fetch_word Plain.M.loaded_segments (0x6cf5c : word) = Some W_6cf04.
Proof. vm_refl. Qed.
Lemma D_6cf04 : decode_any W_6cf04 = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf08 : bv 32 := 0x00b63c23.
Lemma F_6cf08 : fetch_word Plain.M.loaded_segments (0x6cf60 : word) = Some W_6cf08.
Proof. vm_refl. Qed.
Lemma D_6cf08 : decode_any W_6cf08 = Some (Store SZ8 12 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf0c : bv 32 := 0x00008067.
Lemma F_6cf0c : fetch_word Plain.M.loaded_segments (0x6cf64 : word) = Some W_6cf0c.
Proof. vm_refl. Qed.
Lemma D_6cf0c : decode_any W_6cf0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf78 : bv 32 := 0xfd010113.
Lemma F_6cf78 : fetch_word Plain.M.loaded_segments (0x6cfd0 : word) = Some W_6cf78.
Proof. vm_refl. Qed.
Lemma D_6cf78 : decode_any W_6cf78 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf7c : bv 32 := 0x02113423.
Lemma F_6cf7c : fetch_word Plain.M.loaded_segments (0x6cfd4 : word) = Some W_6cf7c.
Proof. vm_refl. Qed.
Lemma D_6cf7c : decode_any W_6cf7c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf80 : bv 32 := 0x02813023.
Lemma F_6cf80 : fetch_word Plain.M.loaded_segments (0x6cfd8 : word) = Some W_6cf80.
Proof. vm_refl. Qed.
Lemma D_6cf80 : decode_any W_6cf80 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf84 : bv 32 := 0x00913c23.
Lemma F_6cf84 : fetch_word Plain.M.loaded_segments (0x6cfdc : word) = Some W_6cf84.
Proof. vm_refl. Qed.
Lemma D_6cf84 : decode_any W_6cf84 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf88 : bv 32 := 0x0e058063.
Lemma F_6cf88 : fetch_word Plain.M.loaded_segments (0x6cfe0 : word) = Some W_6cf88.
Proof. vm_refl. Qed.
Lemma D_6cf88 : decode_any W_6cf88 = Some (Branch BC_EQ 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf8c : bv 32 := 0x10050263.
Lemma F_6cf8c : fetch_word Plain.M.loaded_segments (0x6cfe4 : word) = Some W_6cf8c.
Proof. vm_refl. Qed.
Lemma D_6cf8c : decode_any W_6cf8c = Some (Branch BC_EQ 10 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf90 : bv 32 := 0x0ca58863.
Lemma F_6cf90 : fetch_word Plain.M.loaded_segments (0x6cfe8 : word) = Some W_6cf90.
Proof. vm_refl. Qed.
Lemma D_6cf90 : decode_any W_6cf90 = Some (Branch BC_EQ 11 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf94 : bv 32 := 0x0085a603.
Lemma F_6cf94 : fetch_word Plain.M.loaded_segments (0x6cfec : word) = Some W_6cf94.
Proof. vm_refl. Qed.
Lemma D_6cf94 : decode_any W_6cf94 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf98 : bv 32 := 0x00852683.
Lemma F_6cf98 : fetch_word Plain.M.loaded_segments (0x6cff0 : word) = Some W_6cf98.
Proof. vm_refl. Qed.
Lemma D_6cf98 : decode_any W_6cf98 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cf9c : bv 32 := 0x10d61e63.
Lemma F_6cf9c : fetch_word Plain.M.loaded_segments (0x6cff4 : word) = Some W_6cf9c.
Proof. vm_refl. Qed.
Lemma D_6cf9c : decode_any W_6cf9c = Some (Branch BC_NE 12 13 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfa0 : bv 32 := 0x03053603.
Lemma F_6cfa0 : fetch_word Plain.M.loaded_segments (0x6cff8 : word) = Some W_6cfa0.
Proof. vm_refl. Qed.
Lemma D_6cfa0 : decode_any W_6cfa0 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfa4 : bv 32 := 0x00c13823.
Lemma F_6cfa4 : fetch_word Plain.M.loaded_segments (0x6cffc : word) = Some W_6cfa4.
Proof. vm_refl. Qed.
Lemma D_6cfa4 : decode_any W_6cfa4 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfa8 : bv 32 := 0x02060063.
Lemma F_6cfa8 : fetch_word Plain.M.loaded_segments (0x6d000 : word) = Some W_6cfa8.
Proof. vm_refl. Qed.
Lemma D_6cfa8 : decode_any W_6cfa8 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfc8 : bv 32 := 0x0305b403.
Lemma F_6cfc8 : fetch_word Plain.M.loaded_segments (0x6d020 : word) = Some W_6cfc8.
Proof. vm_refl. Qed.
Lemma D_6cfc8 : decode_any W_6cfc8 = Some (Load SZ8 true 8 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfcc : bv 32 := 0x08040a63.
Lemma F_6cfcc : fetch_word Plain.M.loaded_segments (0x6d024 : word) = Some W_6cfcc.
Proof. vm_refl. Qed.
Lemma D_6cfcc : decode_any W_6cfcc = Some (Branch BC_EQ 8 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfd0 : bv 32 := 0x00050493.
Lemma F_6cfd0 : fetch_word Plain.M.loaded_segments (0x6d028 : word) = Some W_6cfd0.
Proof. vm_refl. Qed.
Lemma D_6cfd0 : decode_any W_6cfd0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfd4 : bv 32 := 0x00c10613.
Lemma F_6cfd4 : fetch_word Plain.M.loaded_segments (0x6d02c : word) = Some W_6cfd4.
Proof. vm_refl. Qed.
Lemma D_6cfd4 : decode_any W_6cfd4 = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfd8 : bv 32 := 0x00040513.
Lemma F_6cfd8 : fetch_word Plain.M.loaded_segments (0x6d030 : word) = Some W_6cfd8.
Proof. vm_refl. Qed.
Lemma D_6cfd8 : decode_any W_6cfd8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfdc : bv 32 := 0x00000593.
Lemma F_6cfdc : fetch_word Plain.M.loaded_segments (0x6d034 : word) = Some W_6cfdc.
Proof. vm_refl. Qed.
Lemma D_6cfdc : decode_any W_6cfdc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfe0 : bv 32 := 0x6a9030ef.
Lemma F_6cfe0 : fetch_word Plain.M.loaded_segments (0x6d038 : word) = Some W_6cfe0.
Proof. vm_refl. Qed.
Lemma D_6cfe0 : decode_any W_6cfe0 = Some (Jal 1 16040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfe4 : bv 32 := 0x00c12503.
Lemma F_6cfe4 : fetch_word Plain.M.loaded_segments (0x6d03c : word) = Some W_6cfe4.
Proof. vm_refl. Qed.
Lemma D_6cfe4 : decode_any W_6cfe4 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfe8 : bv 32 := 0x10050663.
Lemma F_6cfe8 : fetch_word Plain.M.loaded_segments (0x6d040 : word) = Some W_6cfe8.
Proof. vm_refl. Qed.
Lemma D_6cfe8 : decode_any W_6cfe8 = Some (Branch BC_EQ 10 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cfec : bv 32 := 0x00040513.
Lemma F_6cfec : fetch_word Plain.M.loaded_segments (0x6d044 : word) = Some W_6cfec.
Proof. vm_refl. Qed.
Lemma D_6cfec : decode_any W_6cfec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cff0 : bv 32 := 0x59d030ef.
Lemma F_6cff0 : fetch_word Plain.M.loaded_segments (0x6d048 : word) = Some W_6cff0.
Proof. vm_refl. Qed.
Lemma D_6cff0 : decode_any W_6cff0 = Some (Jal 1 15772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cff4 : bv 32 := 0x12050463.
Lemma F_6cff4 : fetch_word Plain.M.loaded_segments (0x6d04c : word) = Some W_6cff4.
Proof. vm_refl. Qed.
Lemma D_6cff4 : decode_any W_6cff4 = Some (Branch BC_EQ 10 0 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cff8 : bv 32 := 0x00048593.
Lemma F_6cff8 : fetch_word Plain.M.loaded_segments (0x6d050 : word) = Some W_6cff8.
Proof. vm_refl. Qed.
Lemma D_6cff8 : decode_any W_6cff8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6cffc : bv 32 := 0x0304b603.
Lemma F_6cffc : fetch_word Plain.M.loaded_segments (0x6d054 : word) = Some W_6cffc.
Proof. vm_refl. Qed.
Lemma D_6cffc : decode_any W_6cffc = Some (Load SZ8 true 12 9 48, 4%Z).
Proof. vm_refl. Qed.
