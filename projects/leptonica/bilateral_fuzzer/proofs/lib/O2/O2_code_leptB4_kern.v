(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2c5a4 : bv 32 := 0xfd010113.
Lemma F_2c5a4 : fetch_word Plain.M.loaded_segments (0x2c5fc : word) = Some W_2c5a4.
Proof. vm_refl. Qed.
Lemma D_2c5a4 : decode_any W_2c5a4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5a8 : bv 32 := 0x02113423.
Lemma F_2c5a8 : fetch_word Plain.M.loaded_segments (0x2c600 : word) = Some W_2c5a8.
Proof. vm_refl. Qed.
Lemma D_2c5a8 : decode_any W_2c5a8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5ac : bv 32 := 0x02813023.
Lemma F_2c5ac : fetch_word Plain.M.loaded_segments (0x2c604 : word) = Some W_2c5ac.
Proof. vm_refl. Qed.
Lemma D_2c5ac : decode_any W_2c5ac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5b0 : bv 32 := 0x00913c23.
Lemma F_2c5b0 : fetch_word Plain.M.loaded_segments (0x2c608 : word) = Some W_2c5b0.
Proof. vm_refl. Qed.
Lemma D_2c5b0 : decode_any W_2c5b0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5b4 : bv 32 := 0x01213823.
Lemma F_2c5b4 : fetch_word Plain.M.loaded_segments (0x2c60c : word) = Some W_2c5b4.
Proof. vm_refl. Qed.
Lemma D_2c5b4 : decode_any W_2c5b4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5b8 : bv 32 := 0x01313423.
Lemma F_2c5b8 : fetch_word Plain.M.loaded_segments (0x2c610 : word) = Some W_2c5b8.
Proof. vm_refl. Qed.
Lemma D_2c5b8 : decode_any W_2c5b8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5bc : bv 32 := 0x01413023.
Lemma F_2c5bc : fetch_word Plain.M.loaded_segments (0x2c614 : word) = Some W_2c5bc.
Proof. vm_refl. Qed.
Lemma D_2c5bc : decode_any W_2c5bc = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5c0 : bv 32 := 0x06b05463.
Lemma F_2c5c0 : fetch_word Plain.M.loaded_segments (0x2c618 : word) = Some W_2c5c0.
Proof. vm_refl. Qed.
Lemma D_2c5c0 : decode_any W_2c5c0 = Some (Branch BC_GE 0 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5c4 : bv 32 := 0x08a05663.
Lemma F_2c5c4 : fetch_word Plain.M.loaded_segments (0x2c61c : word) = Some W_2c5c4.
Proof. vm_refl. Qed.
Lemma D_2c5c4 : decode_any W_2c5c4 = Some (Branch BC_GE 0 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5c8 : bv 32 := 0x00058413.
Lemma F_2c5c8 : fetch_word Plain.M.loaded_segments (0x2c620 : word) = Some W_2c5c8.
Proof. vm_refl. Qed.
Lemma D_2c5c8 : decode_any W_2c5c8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5cc : bv 32 := 0x02a585b3.
Lemma F_2c5cc : fetch_word Plain.M.loaded_segments (0x2c624 : word) = Some W_2c5cc.
Proof. vm_refl. Qed.
Lemma D_2c5cc : decode_any W_2c5cc = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5d0 : bv 32 := 0x01d5d593.
Lemma F_2c5d0 : fetch_word Plain.M.loaded_segments (0x2c628 : word) = Some W_2c5d0.
Proof. vm_refl. Qed.
Lemma D_2c5d0 : decode_any W_2c5d0 = Some (ShiftImm ALU_SRL 11 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c5d4 : bv 32 := 0x0a058263.
Lemma F_2c5d4 : fetch_word Plain.M.loaded_segments (0x2c62c : word) = Some W_2c5d4.
Proof. vm_refl. Qed.
Lemma D_2c5d4 : decode_any W_2c5d4 = Some (Branch BC_EQ 11 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c678 : bv 32 := 0xfffe85b7.
Lemma F_2c678 : fetch_word Plain.M.loaded_segments (0x2c6d0 : word) = Some W_2c678.
Proof. vm_refl. Qed.
Lemma D_2c678 : decode_any W_2c678 = Some (Lui 11 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c67c : bv 32 := 0x95f5849b.
Lemma F_2c67c : fetch_word Plain.M.loaded_segments (0x2c6d4 : word) = Some W_2c67c.
Proof. vm_refl. Qed.
Lemma D_2c67c : decode_any W_2c67c = Some (OpImm32 9 11 2399, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c680 : bv 32 := 0x00050913.
Lemma F_2c680 : fetch_word Plain.M.loaded_segments (0x2c6d8 : word) = Some W_2c680.
Proof. vm_refl. Qed.
Lemma D_2c680 : decode_any W_2c680 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c684 : bv 32 := 0x00100513.
Lemma F_2c684 : fetch_word Plain.M.loaded_segments (0x2c6dc : word) = Some W_2c684.
Proof. vm_refl. Qed.
Lemma D_2c684 : decode_any W_2c684 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c688 : bv 32 := 0x01800593.
Lemma F_2c688 : fetch_word Plain.M.loaded_segments (0x2c6e0 : word) = Some W_2c688.
Proof. vm_refl. Qed.
Lemma D_2c688 : decode_any W_2c688 = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c68c : bv 32 := 0x7f1020ef.
Lemma F_2c68c : fetch_word Plain.M.loaded_segments (0x2c6e4 : word) = Some W_2c68c.
Proof. vm_refl. Qed.
Lemma D_2c68c : decode_any W_2c68c = Some (Jal 1 12272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c690 : bv 32 := 0x009405bb.
Lemma F_2c690 : fetch_word Plain.M.loaded_segments (0x2c6e8 : word) = Some W_2c690.
Proof. vm_refl. Qed.
Lemma D_2c690 : decode_any W_2c690 = Some (Op32 ALU_ADD 11 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c694 : bv 32 := 0x01252023.
Lemma F_2c694 : fetch_word Plain.M.loaded_segments (0x2c6ec : word) = Some W_2c694.
Proof. vm_refl. Qed.
Lemma D_2c694 : decode_any W_2c694 = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c698 : bv 32 := 0x00852223.
Lemma F_2c698 : fetch_word Plain.M.loaded_segments (0x2c6f0 : word) = Some W_2c698.
Proof. vm_refl. Qed.
Lemma D_2c698 : decode_any W_2c698 = Some (Store SZ4 10 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c69c : bv 32 := 0x02b4e463.
Lemma F_2c69c : fetch_word Plain.M.loaded_segments (0x2c6f4 : word) = Some W_2c69c.
Proof. vm_refl. Qed.
Lemma D_2c69c : decode_any W_2c69c = Some (Branch BC_LTU 9 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c6c4 : bv 32 := 0x009905bb.
Lemma F_2c6c4 : fetch_word Plain.M.loaded_segments (0x2c71c : word) = Some W_2c6c4.
Proof. vm_refl. Qed.
Lemma D_2c6c4 : decode_any W_2c6c4 = Some (Op32 ALU_ADD 11 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c6c8 : bv 32 := 0x0ab4ee63.
Lemma F_2c6c8 : fetch_word Plain.M.loaded_segments (0x2c720 : word) = Some W_2c6c8.
Proof. vm_refl. Qed.
Lemma D_2c6c8 : decode_any W_2c6c8 = Some (Branch BC_LTU 9 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c764 : bv 32 := 0x02813083.
Lemma F_2c764 : fetch_word Plain.M.loaded_segments (0x2c7bc : word) = Some W_2c764.
Proof. vm_refl. Qed.
Lemma D_2c764 : decode_any W_2c764 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c768 : bv 32 := 0x02013403.
Lemma F_2c768 : fetch_word Plain.M.loaded_segments (0x2c7c0 : word) = Some W_2c768.
Proof. vm_refl. Qed.
Lemma D_2c768 : decode_any W_2c768 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c76c : bv 32 := 0x01813483.
Lemma F_2c76c : fetch_word Plain.M.loaded_segments (0x2c7c4 : word) = Some W_2c76c.
Proof. vm_refl. Qed.
Lemma D_2c76c : decode_any W_2c76c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c770 : bv 32 := 0x01013903.
Lemma F_2c770 : fetch_word Plain.M.loaded_segments (0x2c7c8 : word) = Some W_2c770.
Proof. vm_refl. Qed.
Lemma D_2c770 : decode_any W_2c770 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c774 : bv 32 := 0x00813983.
Lemma F_2c774 : fetch_word Plain.M.loaded_segments (0x2c7cc : word) = Some W_2c774.
Proof. vm_refl. Qed.
Lemma D_2c774 : decode_any W_2c774 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c778 : bv 32 := 0x00013a03.
Lemma F_2c778 : fetch_word Plain.M.loaded_segments (0x2c7d0 : word) = Some W_2c778.
Proof. vm_refl. Qed.
Lemma D_2c778 : decode_any W_2c778 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c77c : bv 32 := 0x03010113.
Lemma F_2c77c : fetch_word Plain.M.loaded_segments (0x2c7d4 : word) = Some W_2c77c.
Proof. vm_refl. Qed.
Lemma D_2c77c : decode_any W_2c77c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c780 : bv 32 := 0x00008067.
Lemma F_2c780 : fetch_word Plain.M.loaded_segments (0x2c7d8 : word) = Some W_2c780.
Proof. vm_refl. Qed.
Lemma D_2c780 : decode_any W_2c780 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c784 : bv 32 := 0x00050993.
Lemma F_2c784 : fetch_word Plain.M.loaded_segments (0x2c7dc : word) = Some W_2c784.
Proof. vm_refl. Qed.
Lemma D_2c784 : decode_any W_2c784 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c788 : bv 32 := 0x00800593.
Lemma F_2c788 : fetch_word Plain.M.loaded_segments (0x2c7e0 : word) = Some W_2c788.
Proof. vm_refl. Qed.
Lemma D_2c788 : decode_any W_2c788 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c78c : bv 32 := 0x00090513.
Lemma F_2c78c : fetch_word Plain.M.loaded_segments (0x2c7e4 : word) = Some W_2c78c.
Proof. vm_refl. Qed.
Lemma D_2c78c : decode_any W_2c78c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c790 : bv 32 := 0x6ed020ef.
Lemma F_2c790 : fetch_word Plain.M.loaded_segments (0x2c7e8 : word) = Some W_2c790.
Proof. vm_refl. Qed.
Lemma D_2c790 : decode_any W_2c790 = Some (Jal 1 12012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c794 : bv 32 := 0x00050493.
Lemma F_2c794 : fetch_word Plain.M.loaded_segments (0x2c7ec : word) = Some W_2c794.
Proof. vm_refl. Qed.
Lemma D_2c794 : decode_any W_2c794 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c798 : bv 32 := 0x00391913.
Lemma F_2c798 : fetch_word Plain.M.loaded_segments (0x2c7f0 : word) = Some W_2c798.
Proof. vm_refl. Qed.
Lemma D_2c798 : decode_any W_2c798 = Some (ShiftImm ALU_SLL 18 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c79c : bv 32 := 0x01250933.
Lemma F_2c79c : fetch_word Plain.M.loaded_segments (0x2c7f4 : word) = Some W_2c79c.
Proof. vm_refl. Qed.
Lemma D_2c79c : decode_any W_2c79c = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7a0 : bv 32 := 0x00050a13.
Lemma F_2c7a0 : fetch_word Plain.M.loaded_segments (0x2c7f8 : word) = Some W_2c7a0.
Proof. vm_refl. Qed.
Lemma D_2c7a0 : decode_any W_2c7a0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7a4 : bv 32 := 0x00400593.
Lemma F_2c7a4 : fetch_word Plain.M.loaded_segments (0x2c7fc : word) = Some W_2c7a4.
Proof. vm_refl. Qed.
Lemma D_2c7a4 : decode_any W_2c7a4 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7a8 : bv 32 := 0x00040513.
Lemma F_2c7a8 : fetch_word Plain.M.loaded_segments (0x2c800 : word) = Some W_2c7a8.
Proof. vm_refl. Qed.
Lemma D_2c7a8 : decode_any W_2c7a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7ac : bv 32 := 0x6d1020ef.
Lemma F_2c7ac : fetch_word Plain.M.loaded_segments (0x2c804 : word) = Some W_2c7ac.
Proof. vm_refl. Qed.
Lemma D_2c7ac : decode_any W_2c7ac = Some (Jal 1 11984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7b0 : bv 32 := 0x00aa3023.
Lemma F_2c7b0 : fetch_word Plain.M.loaded_segments (0x2c808 : word) = Some W_2c7b0.
Proof. vm_refl. Qed.
Lemma D_2c7b0 : decode_any W_2c7b0 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7b4 : bv 32 := 0x008a0a13.
Lemma F_2c7b4 : fetch_word Plain.M.loaded_segments (0x2c80c : word) = Some W_2c7b4.
Proof. vm_refl. Qed.
Lemma D_2c7b4 : decode_any W_2c7b4 = Some (OpImm ALU_ADD 20 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7b8 : bv 32 := 0xff2a16e3.
Lemma F_2c7b8 : fetch_word Plain.M.loaded_segments (0x2c810 : word) = Some W_2c7b8.
Proof. vm_refl. Qed.
Lemma D_2c7b8 : decode_any W_2c7b8 = Some (Branch BC_NE 20 18 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7bc : bv 32 := 0x00098513.
Lemma F_2c7bc : fetch_word Plain.M.loaded_segments (0x2c814 : word) = Some W_2c7bc.
Proof. vm_refl. Qed.
Lemma D_2c7bc : decode_any W_2c7bc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7c0 : bv 32 := 0x0099b823.
Lemma F_2c7c0 : fetch_word Plain.M.loaded_segments (0x2c818 : word) = Some W_2c7c0.
Proof. vm_refl. Qed.
Lemma D_2c7c0 : decode_any W_2c7c0 = Some (Store SZ8 19 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7c4 : bv 32 := 0xfa1ff06f.
Lemma F_2c7c4 : fetch_word Plain.M.loaded_segments (0x2c81c : word) = Some W_2c7c4.
Proof. vm_refl. Qed.
Lemma D_2c7c4 : decode_any W_2c7c4 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_2c7c8 : bv 32 := 0xfd010113.
Lemma F_2c7c8 : fetch_word Plain.M.loaded_segments (0x2c820 : word) = Some W_2c7c8.
Proof. vm_refl. Qed.
Lemma D_2c7c8 : decode_any W_2c7c8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7cc : bv 32 := 0x02113423.
Lemma F_2c7cc : fetch_word Plain.M.loaded_segments (0x2c824 : word) = Some W_2c7cc.
Proof. vm_refl. Qed.
Lemma D_2c7cc : decode_any W_2c7cc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7d0 : bv 32 := 0x02813023.
Lemma F_2c7d0 : fetch_word Plain.M.loaded_segments (0x2c828 : word) = Some W_2c7d0.
Proof. vm_refl. Qed.
Lemma D_2c7d0 : decode_any W_2c7d0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7d4 : bv 32 := 0x00913c23.
Lemma F_2c7d4 : fetch_word Plain.M.loaded_segments (0x2c82c : word) = Some W_2c7d4.
Proof. vm_refl. Qed.
Lemma D_2c7d4 : decode_any W_2c7d4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7d8 : bv 32 := 0x01213823.
Lemma F_2c7d8 : fetch_word Plain.M.loaded_segments (0x2c830 : word) = Some W_2c7d8.
Proof. vm_refl. Qed.
Lemma D_2c7d8 : decode_any W_2c7d8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7dc : bv 32 := 0x01313423.
Lemma F_2c7dc : fetch_word Plain.M.loaded_segments (0x2c834 : word) = Some W_2c7dc.
Proof. vm_refl. Qed.
Lemma D_2c7dc : decode_any W_2c7dc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7e0 : bv 32 := 0x04050c63.
Lemma F_2c7e0 : fetch_word Plain.M.loaded_segments (0x2c838 : word) = Some W_2c7e0.
Proof. vm_refl. Qed.
Lemma D_2c7e0 : decode_any W_2c7e0 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7e4 : bv 32 := 0x00050413.
Lemma F_2c7e4 : fetch_word Plain.M.loaded_segments (0x2c83c : word) = Some W_2c7e4.
Proof. vm_refl. Qed.
Lemma D_2c7e4 : decode_any W_2c7e4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7e8 : bv 32 := 0x00053483.
Lemma F_2c7e8 : fetch_word Plain.M.loaded_segments (0x2c840 : word) = Some W_2c7e8.
Proof. vm_refl. Qed.
Lemma D_2c7e8 : decode_any W_2c7e8 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7ec : bv 32 := 0x08048663.
Lemma F_2c7ec : fetch_word Plain.M.loaded_segments (0x2c844 : word) = Some W_2c7ec.
Proof. vm_refl. Qed.
Lemma D_2c7ec : decode_any W_2c7ec = Some (Branch BC_EQ 9 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7f0 : bv 32 := 0x0004a503.
Lemma F_2c7f0 : fetch_word Plain.M.loaded_segments (0x2c848 : word) = Some W_2c7f0.
Proof. vm_refl. Qed.
Lemma D_2c7f0 : decode_any W_2c7f0 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7f4 : bv 32 := 0x02a05663.
Lemma F_2c7f4 : fetch_word Plain.M.loaded_segments (0x2c84c : word) = Some W_2c7f4.
Proof. vm_refl. Qed.
Lemma D_2c7f4 : decode_any W_2c7f4 = Some (Branch BC_GE 0 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7f8 : bv 32 := 0x00000913.
Lemma F_2c7f8 : fetch_word Plain.M.loaded_segments (0x2c850 : word) = Some W_2c7f8.
Proof. vm_refl. Qed.
Lemma D_2c7f8 : decode_any W_2c7f8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c7fc : bv 32 := 0x00000993.
Lemma F_2c7fc : fetch_word Plain.M.loaded_segments (0x2c854 : word) = Some W_2c7fc.
Proof. vm_refl. Qed.
Lemma D_2c7fc : decode_any W_2c7fc = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c800 : bv 32 := 0x0104b503.
Lemma F_2c800 : fetch_word Plain.M.loaded_segments (0x2c858 : word) = Some W_2c800.
Proof. vm_refl. Qed.
Lemma D_2c800 : decode_any W_2c800 = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c804 : bv 32 := 0x01250533.
Lemma F_2c804 : fetch_word Plain.M.loaded_segments (0x2c85c : word) = Some W_2c804.
Proof. vm_refl. Qed.
Lemma D_2c804 : decode_any W_2c804 = Some (Op ALU_ADD 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c808 : bv 32 := 0x00053503.
Lemma F_2c808 : fetch_word Plain.M.loaded_segments (0x2c860 : word) = Some W_2c808.
Proof. vm_refl. Qed.
Lemma D_2c808 : decode_any W_2c808 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c80c : bv 32 := 0x7a9020ef.
Lemma F_2c80c : fetch_word Plain.M.loaded_segments (0x2c864 : word) = Some W_2c80c.
Proof. vm_refl. Qed.
Lemma D_2c80c : decode_any W_2c80c = Some (Jal 1 12200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c810 : bv 32 := 0x0004a503.
Lemma F_2c810 : fetch_word Plain.M.loaded_segments (0x2c868 : word) = Some W_2c810.
Proof. vm_refl. Qed.
Lemma D_2c810 : decode_any W_2c810 = Some (Load SZ4 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c814 : bv 32 := 0x00198993.
Lemma F_2c814 : fetch_word Plain.M.loaded_segments (0x2c86c : word) = Some W_2c814.
Proof. vm_refl. Qed.
Lemma D_2c814 : decode_any W_2c814 = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c818 : bv 32 := 0x00890913.
Lemma F_2c818 : fetch_word Plain.M.loaded_segments (0x2c870 : word) = Some W_2c818.
Proof. vm_refl. Qed.
Lemma D_2c818 : decode_any W_2c818 = Some (OpImm ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c81c : bv 32 := 0xfea9c2e3.
Lemma F_2c81c : fetch_word Plain.M.loaded_segments (0x2c874 : word) = Some W_2c81c.
Proof. vm_refl. Qed.
Lemma D_2c81c : decode_any W_2c81c = Some (Branch BC_LT 19 10 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c820 : bv 32 := 0x0104b503.
Lemma F_2c820 : fetch_word Plain.M.loaded_segments (0x2c878 : word) = Some W_2c820.
Proof. vm_refl. Qed.
Lemma D_2c820 : decode_any W_2c820 = Some (Load SZ8 true 10 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c824 : bv 32 := 0x791020ef.
Lemma F_2c824 : fetch_word Plain.M.loaded_segments (0x2c87c : word) = Some W_2c824.
Proof. vm_refl. Qed.
Lemma D_2c824 : decode_any W_2c824 = Some (Jal 1 12176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c828 : bv 32 := 0x00048513.
Lemma F_2c828 : fetch_word Plain.M.loaded_segments (0x2c880 : word) = Some W_2c828.
Proof. vm_refl. Qed.
Lemma D_2c828 : decode_any W_2c828 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c82c : bv 32 := 0x789020ef.
Lemma F_2c82c : fetch_word Plain.M.loaded_segments (0x2c884 : word) = Some W_2c82c.
Proof. vm_refl. Qed.
Lemma D_2c82c : decode_any W_2c82c = Some (Jal 1 12168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c830 : bv 32 := 0x00043023.
Lemma F_2c830 : fetch_word Plain.M.loaded_segments (0x2c888 : word) = Some W_2c830.
Proof. vm_refl. Qed.
Lemma D_2c830 : decode_any W_2c830 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c834 : bv 32 := 0x0440006f.
Lemma F_2c834 : fetch_word Plain.M.loaded_segments (0x2c88c : word) = Some W_2c834.
Proof. vm_refl. Qed.
Lemma D_2c834 : decode_any W_2c834 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c878 : bv 32 := 0x02813083.
Lemma F_2c878 : fetch_word Plain.M.loaded_segments (0x2c8d0 : word) = Some W_2c878.
Proof. vm_refl. Qed.
Lemma D_2c878 : decode_any W_2c878 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c87c : bv 32 := 0x02013403.
Lemma F_2c87c : fetch_word Plain.M.loaded_segments (0x2c8d4 : word) = Some W_2c87c.
Proof. vm_refl. Qed.
Lemma D_2c87c : decode_any W_2c87c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c880 : bv 32 := 0x01813483.
Lemma F_2c880 : fetch_word Plain.M.loaded_segments (0x2c8d8 : word) = Some W_2c880.
Proof. vm_refl. Qed.
Lemma D_2c880 : decode_any W_2c880 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c884 : bv 32 := 0x01013903.
Lemma F_2c884 : fetch_word Plain.M.loaded_segments (0x2c8dc : word) = Some W_2c884.
Proof. vm_refl. Qed.
Lemma D_2c884 : decode_any W_2c884 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c888 : bv 32 := 0x00813983.
Lemma F_2c888 : fetch_word Plain.M.loaded_segments (0x2c8e0 : word) = Some W_2c888.
Proof. vm_refl. Qed.
Lemma D_2c888 : decode_any W_2c888 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c88c : bv 32 := 0x03010113.
Lemma F_2c88c : fetch_word Plain.M.loaded_segments (0x2c8e4 : word) = Some W_2c88c.
Proof. vm_refl. Qed.
Lemma D_2c88c : decode_any W_2c88c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2c890 : bv 32 := 0x00008067.
Lemma F_2c890 : fetch_word Plain.M.loaded_segments (0x2c8e8 : word) = Some W_2c890.
Proof. vm_refl. Qed.
Lemma D_2c890 : decode_any W_2c890 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
