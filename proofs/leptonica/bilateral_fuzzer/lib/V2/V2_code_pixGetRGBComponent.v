(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1b5fc : bv 32 := 0xfa010113.
Lemma F_1b5fc : fetch_word Ubsan.M.loaded_segments (0x1b5fc : word) = Some W_1b5fc.
Proof. vm_refl. Qed.
Lemma D_1b5fc : decode_any W_1b5fc = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b600 : bv 32 := 0x04113c23.
Lemma F_1b600 : fetch_word Ubsan.M.loaded_segments (0x1b600 : word) = Some W_1b600.
Proof. vm_refl. Qed.
Lemma D_1b600 : decode_any W_1b600 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b604 : bv 32 := 0x04813823.
Lemma F_1b604 : fetch_word Ubsan.M.loaded_segments (0x1b604 : word) = Some W_1b604.
Proof. vm_refl. Qed.
Lemma D_1b604 : decode_any W_1b604 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b608 : bv 32 := 0x04913423.
Lemma F_1b608 : fetch_word Ubsan.M.loaded_segments (0x1b608 : word) = Some W_1b608.
Proof. vm_refl. Qed.
Lemma D_1b608 : decode_any W_1b608 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b60c : bv 32 := 0x05213023.
Lemma F_1b60c : fetch_word Ubsan.M.loaded_segments (0x1b60c : word) = Some W_1b60c.
Proof. vm_refl. Qed.
Lemma D_1b60c : decode_any W_1b60c = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b610 : bv 32 := 0x03313c23.
Lemma F_1b610 : fetch_word Ubsan.M.loaded_segments (0x1b610 : word) = Some W_1b610.
Proof. vm_refl. Qed.
Lemma D_1b610 : decode_any W_1b610 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b614 : bv 32 := 0x03413823.
Lemma F_1b614 : fetch_word Ubsan.M.loaded_segments (0x1b614 : word) = Some W_1b614.
Proof. vm_refl. Qed.
Lemma D_1b614 : decode_any W_1b614 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b618 : bv 32 := 0x03513423.
Lemma F_1b618 : fetch_word Ubsan.M.loaded_segments (0x1b618 : word) = Some W_1b618.
Proof. vm_refl. Qed.
Lemma D_1b618 : decode_any W_1b618 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b61c : bv 32 := 0x03613023.
Lemma F_1b61c : fetch_word Ubsan.M.loaded_segments (0x1b61c : word) = Some W_1b61c.
Proof. vm_refl. Qed.
Lemma D_1b61c : decode_any W_1b61c = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b620 : bv 32 := 0x01713c23.
Lemma F_1b620 : fetch_word Ubsan.M.loaded_segments (0x1b620 : word) = Some W_1b620.
Proof. vm_refl. Qed.
Lemma D_1b620 : decode_any W_1b620 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b624 : bv 32 := 0x01813823.
Lemma F_1b624 : fetch_word Ubsan.M.loaded_segments (0x1b624 : word) = Some W_1b624.
Proof. vm_refl. Qed.
Lemma D_1b624 : decode_any W_1b624 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b628 : bv 32 := 0x04050663.
Lemma F_1b628 : fetch_word Ubsan.M.loaded_segments (0x1b628 : word) = Some W_1b628.
Proof. vm_refl. Qed.
Lemma D_1b628 : decode_any W_1b628 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b62c : bv 32 := 0x00058993.
Lemma F_1b62c : fetch_word Ubsan.M.loaded_segments (0x1b62c : word) = Some W_1b62c.
Proof. vm_refl. Qed.
Lemma D_1b62c : decode_any W_1b62c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b630 : bv 32 := 0x00050913.
Lemma F_1b630 : fetch_word Ubsan.M.loaded_segments (0x1b630 : word) = Some W_1b630.
Proof. vm_refl. Qed.
Lemma D_1b630 : decode_any W_1b630 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b634 : bv 32 := 0xbbcff0ef.
Lemma F_1b634 : fetch_word Ubsan.M.loaded_segments (0x1b634 : word) = Some W_1b634.
Proof. vm_refl. Qed.
Lemma D_1b634 : decode_any W_1b634 = Some (Jal 1 2094012, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b638 : bv 32 := 0x06050263.
Lemma F_1b638 : fetch_word Ubsan.M.loaded_segments (0x1b638 : word) = Some W_1b638.
Proof. vm_refl. Qed.
Lemma D_1b638 : decode_any W_1b638 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b63c : bv 32 := 0x00090513.
Lemma F_1b63c : fetch_word Ubsan.M.loaded_segments (0x1b63c : word) = Some W_1b63c.
Proof. vm_refl. Qed.
Lemma D_1b63c : decode_any W_1b63c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b640 : bv 32 := 0x00098593.
Lemma F_1b640 : fetch_word Ubsan.M.loaded_segments (0x1b640 : word) = Some W_1b640.
Proof. vm_refl. Qed.
Lemma D_1b640 : decode_any W_1b640 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b644 : bv 32 := 0x05813083.
Lemma F_1b644 : fetch_word Ubsan.M.loaded_segments (0x1b644 : word) = Some W_1b644.
Proof. vm_refl. Qed.
Lemma D_1b644 : decode_any W_1b644 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b648 : bv 32 := 0x05013403.
Lemma F_1b648 : fetch_word Ubsan.M.loaded_segments (0x1b648 : word) = Some W_1b648.
Proof. vm_refl. Qed.
Lemma D_1b648 : decode_any W_1b648 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b64c : bv 32 := 0x04813483.
Lemma F_1b64c : fetch_word Ubsan.M.loaded_segments (0x1b64c : word) = Some W_1b64c.
Proof. vm_refl. Qed.
Lemma D_1b64c : decode_any W_1b64c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b650 : bv 32 := 0x04013903.
Lemma F_1b650 : fetch_word Ubsan.M.loaded_segments (0x1b650 : word) = Some W_1b650.
Proof. vm_refl. Qed.
Lemma D_1b650 : decode_any W_1b650 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b654 : bv 32 := 0x03813983.
Lemma F_1b654 : fetch_word Ubsan.M.loaded_segments (0x1b654 : word) = Some W_1b654.
Proof. vm_refl. Qed.
Lemma D_1b654 : decode_any W_1b654 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b658 : bv 32 := 0x03013a03.
Lemma F_1b658 : fetch_word Ubsan.M.loaded_segments (0x1b658 : word) = Some W_1b658.
Proof. vm_refl. Qed.
Lemma D_1b658 : decode_any W_1b658 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b65c : bv 32 := 0x02813a83.
Lemma F_1b65c : fetch_word Ubsan.M.loaded_segments (0x1b65c : word) = Some W_1b65c.
Proof. vm_refl. Qed.
Lemma D_1b65c : decode_any W_1b65c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b660 : bv 32 := 0x02013b03.
Lemma F_1b660 : fetch_word Ubsan.M.loaded_segments (0x1b660 : word) = Some W_1b660.
Proof. vm_refl. Qed.
Lemma D_1b660 : decode_any W_1b660 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b664 : bv 32 := 0x01813b83.
Lemma F_1b664 : fetch_word Ubsan.M.loaded_segments (0x1b664 : word) = Some W_1b664.
Proof. vm_refl. Qed.
Lemma D_1b664 : decode_any W_1b664 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b668 : bv 32 := 0x01013c03.
Lemma F_1b668 : fetch_word Ubsan.M.loaded_segments (0x1b668 : word) = Some W_1b668.
Proof. vm_refl. Qed.
Lemma D_1b668 : decode_any W_1b668 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b66c : bv 32 := 0x06010113.
Lemma F_1b66c : fetch_word Ubsan.M.loaded_segments (0x1b66c : word) = Some W_1b66c.
Proof. vm_refl. Qed.
Lemma D_1b66c : decode_any W_1b66c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b670 : bv 32 := 0x6d00106f.
Lemma F_1b670 : fetch_word Ubsan.M.loaded_segments (0x1b670 : word) = Some W_1b670.
Proof. vm_refl. Qed.
Lemma D_1b670 : decode_any W_1b670 = Some (Jal 0 5840, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b674 : bv 32 := 0x0002a517.
Lemma F_1b674 : fetch_word Ubsan.M.loaded_segments (0x1b674 : word) = Some W_1b674.
Proof. vm_refl. Qed.
Lemma D_1b674 : decode_any W_1b674 = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b678 : bv 32 := 0x82453503.
Lemma F_1b678 : fetch_word Ubsan.M.loaded_segments (0x1b678 : word) = Some W_1b678.
Proof. vm_refl. Qed.
Lemma D_1b678 : decode_any W_1b678 = Some (Load SZ8 true 10 10 2084, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b67c : bv 32 := 0x00052503.
Lemma F_1b67c : fetch_word Ubsan.M.loaded_segments (0x1b67c : word) = Some W_1b67c.
Proof. vm_refl. Qed.
Lemma D_1b67c : decode_any W_1b67c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b680 : bv 32 := 0x00500593.
Lemma F_1b680 : fetch_word Ubsan.M.loaded_segments (0x1b680 : word) = Some W_1b680.
Proof. vm_refl. Qed.
Lemma D_1b680 : decode_any W_1b680 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b684 : bv 32 := 0x28a5cc63.
Lemma F_1b684 : fetch_word Ubsan.M.loaded_segments (0x1b684 : word) = Some W_1b684.
Proof. vm_refl. Qed.
Lemma D_1b684 : decode_any W_1b684 = Some (Branch BC_LT 11 10 664, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b688 : bv 32 := 0xffff5517.
Lemma F_1b688 : fetch_word Ubsan.M.loaded_segments (0x1b688 : word) = Some W_1b688.
Proof. vm_refl. Qed.
Lemma D_1b688 : decode_any W_1b688 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b68c : bv 32 := 0xffff5597.
Lemma F_1b68c : fetch_word Ubsan.M.loaded_segments (0x1b68c : word) = Some W_1b68c.
Proof. vm_refl. Qed.
Lemma D_1b68c : decode_any W_1b68c = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b690 : bv 32 := 0xc2c50513.
Lemma F_1b690 : fetch_word Ubsan.M.loaded_segments (0x1b690 : word) = Some W_1b690.
Proof. vm_refl. Qed.
Lemma D_1b690 : decode_any W_1b690 = Some (OpImm ALU_ADD 10 10 3116, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b694 : bv 32 := 0x29658593.
Lemma F_1b694 : fetch_word Ubsan.M.loaded_segments (0x1b694 : word) = Some W_1b694.
Proof. vm_refl. Qed.
Lemma D_1b694 : decode_any W_1b694 = Some (OpImm ALU_ADD 11 11 662, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b698 : bv 32 := 0x0680006f.
Lemma F_1b698 : fetch_word Ubsan.M.loaded_segments (0x1b698 : word) = Some W_1b698.
Proof. vm_refl. Qed.
Lemma D_1b698 : decode_any W_1b698 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b69c : bv 32 := 0x00090513.
Lemma F_1b69c : fetch_word Ubsan.M.loaded_segments (0x1b69c : word) = Some W_1b69c.
Proof. vm_refl. Qed.
Lemma D_1b69c : decode_any W_1b69c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6a0 : bv 32 := 0xa2cff0ef.
Lemma F_1b6a0 : fetch_word Ubsan.M.loaded_segments (0x1b6a0 : word) = Some W_1b6a0.
Proof. vm_refl. Qed.
Lemma D_1b6a0 : decode_any W_1b6a0 = Some (Jal 1 2093612, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6a4 : bv 32 := 0x02000593.
Lemma F_1b6a4 : fetch_word Ubsan.M.loaded_segments (0x1b6a4 : word) = Some W_1b6a4.
Proof. vm_refl. Qed.
Lemma D_1b6a4 : decode_any W_1b6a4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6a8 : bv 32 := 0x02b51a63.
Lemma F_1b6a8 : fetch_word Ubsan.M.loaded_segments (0x1b6a8 : word) = Some W_1b6a8.
Proof. vm_refl. Qed.
Lemma D_1b6a8 : decode_any W_1b6a8 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6ac : bv 32 := 0x00400513.
Lemma F_1b6ac : fetch_word Ubsan.M.loaded_segments (0x1b6ac : word) = Some W_1b6ac.
Proof. vm_refl. Qed.
Lemma D_1b6ac : decode_any W_1b6ac = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6b0 : bv 32 := 0x08a9e263.
Lemma F_1b6b0 : fetch_word Ubsan.M.loaded_segments (0x1b6b0 : word) = Some W_1b6b0.
Proof. vm_refl. Qed.
Lemma D_1b6b0 : decode_any W_1b6b0 = Some (Branch BC_LTU 19 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6b4 : bv 32 := 0x00029517.
Lemma F_1b6b4 : fetch_word Ubsan.M.loaded_segments (0x1b6b4 : word) = Some W_1b6b4.
Proof. vm_refl. Qed.
Lemma D_1b6b4 : decode_any W_1b6b4 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6b8 : bv 32 := 0x7e453503.
Lemma F_1b6b8 : fetch_word Ubsan.M.loaded_segments (0x1b6b8 : word) = Some W_1b6b8.
Proof. vm_refl. Qed.
Lemma D_1b6b8 : decode_any W_1b6b8 = Some (Load SZ8 true 10 10 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6bc : bv 32 := 0x00052503.
Lemma F_1b6bc : fetch_word Ubsan.M.loaded_segments (0x1b6bc : word) = Some W_1b6bc.
Proof. vm_refl. Qed.
Lemma D_1b6bc : decode_any W_1b6bc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6c0 : bv 32 := 0x00500593.
Lemma F_1b6c0 : fetch_word Ubsan.M.loaded_segments (0x1b6c0 : word) = Some W_1b6c0.
Proof. vm_refl. Qed.
Lemma D_1b6c0 : decode_any W_1b6c0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6c4 : bv 32 := 0x24a5cc63.
Lemma F_1b6c4 : fetch_word Ubsan.M.loaded_segments (0x1b6c4 : word) = Some W_1b6c4.
Proof. vm_refl. Qed.
Lemma D_1b6c4 : decode_any W_1b6c4 = Some (Branch BC_LT 11 10 600, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6c8 : bv 32 := 0xffff5517.
Lemma F_1b6c8 : fetch_word Ubsan.M.loaded_segments (0x1b6c8 : word) = Some W_1b6c8.
Proof. vm_refl. Qed.
Lemma D_1b6c8 : decode_any W_1b6c8 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6cc : bv 32 := 0xffff5597.
Lemma F_1b6cc : fetch_word Ubsan.M.loaded_segments (0x1b6cc : word) = Some W_1b6cc.
Proof. vm_refl. Qed.
Lemma D_1b6cc : decode_any W_1b6cc = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6d0 : bv 32 := 0x3ae50513.
Lemma F_1b6d0 : fetch_word Ubsan.M.loaded_segments (0x1b6d0 : word) = Some W_1b6d0.
Proof. vm_refl. Qed.
Lemma D_1b6d0 : decode_any W_1b6d0 = Some (OpImm ALU_ADD 10 10 942, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6d4 : bv 32 := 0x25658593.
Lemma F_1b6d4 : fetch_word Ubsan.M.loaded_segments (0x1b6d4 : word) = Some W_1b6d4.
Proof. vm_refl. Qed.
Lemma D_1b6d4 : decode_any W_1b6d4 = Some (OpImm ALU_ADD 11 11 598, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6d8 : bv 32 := 0x0280006f.
Lemma F_1b6d8 : fetch_word Ubsan.M.loaded_segments (0x1b6d8 : word) = Some W_1b6d8.
Proof. vm_refl. Qed.
Lemma D_1b6d8 : decode_any W_1b6d8 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6dc : bv 32 := 0x00029517.
Lemma F_1b6dc : fetch_word Ubsan.M.loaded_segments (0x1b6dc : word) = Some W_1b6dc.
Proof. vm_refl. Qed.
Lemma D_1b6dc : decode_any W_1b6dc = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6e0 : bv 32 := 0x7bc53503.
Lemma F_1b6e0 : fetch_word Ubsan.M.loaded_segments (0x1b6e0 : word) = Some W_1b6e0.
Proof. vm_refl. Qed.
Lemma D_1b6e0 : decode_any W_1b6e0 = Some (Load SZ8 true 10 10 1980, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6e4 : bv 32 := 0x00052503.
Lemma F_1b6e4 : fetch_word Ubsan.M.loaded_segments (0x1b6e4 : word) = Some W_1b6e4.
Proof. vm_refl. Qed.
Lemma D_1b6e4 : decode_any W_1b6e4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6e8 : bv 32 := 0x00500593.
Lemma F_1b6e8 : fetch_word Ubsan.M.loaded_segments (0x1b6e8 : word) = Some W_1b6e8.
Proof. vm_refl. Qed.
Lemma D_1b6e8 : decode_any W_1b6e8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6ec : bv 32 := 0x22a5c863.
Lemma F_1b6ec : fetch_word Ubsan.M.loaded_segments (0x1b6ec : word) = Some W_1b6ec.
Proof. vm_refl. Qed.
Lemma D_1b6ec : decode_any W_1b6ec = Some (Branch BC_LT 11 10 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6f0 : bv 32 := 0xffff5517.
Lemma F_1b6f0 : fetch_word Ubsan.M.loaded_segments (0x1b6f0 : word) = Some W_1b6f0.
Proof. vm_refl. Qed.
Lemma D_1b6f0 : decode_any W_1b6f0 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6f4 : bv 32 := 0xffff5597.
Lemma F_1b6f4 : fetch_word Ubsan.M.loaded_segments (0x1b6f4 : word) = Some W_1b6f4.
Proof. vm_refl. Qed.
Lemma D_1b6f4 : decode_any W_1b6f4 = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6f8 : bv 32 := 0x44150513.
Lemma F_1b6f8 : fetch_word Ubsan.M.loaded_segments (0x1b6f8 : word) = Some W_1b6f8.
Proof. vm_refl. Qed.
Lemma D_1b6f8 : decode_any W_1b6f8 = Some (OpImm ALU_ADD 10 10 1089, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b6fc : bv 32 := 0x22e58593.
Lemma F_1b6fc : fetch_word Ubsan.M.loaded_segments (0x1b6fc : word) = Some W_1b6fc.
Proof. vm_refl. Qed.
Lemma D_1b6fc : decode_any W_1b6fc = Some (OpImm ALU_ADD 11 11 558, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b700 : bv 32 := 0x00000613.
Lemma F_1b700 : fetch_word Ubsan.M.loaded_segments (0x1b700 : word) = Some W_1b700.
Proof. vm_refl. Qed.
Lemma D_1b700 : decode_any W_1b700 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b704 : bv 32 := 0x05813083.
Lemma F_1b704 : fetch_word Ubsan.M.loaded_segments (0x1b704 : word) = Some W_1b704.
Proof. vm_refl. Qed.
Lemma D_1b704 : decode_any W_1b704 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b708 : bv 32 := 0x05013403.
Lemma F_1b708 : fetch_word Ubsan.M.loaded_segments (0x1b708 : word) = Some W_1b708.
Proof. vm_refl. Qed.
Lemma D_1b708 : decode_any W_1b708 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b70c : bv 32 := 0x04813483.
Lemma F_1b70c : fetch_word Ubsan.M.loaded_segments (0x1b70c : word) = Some W_1b70c.
Proof. vm_refl. Qed.
Lemma D_1b70c : decode_any W_1b70c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b710 : bv 32 := 0x04013903.
Lemma F_1b710 : fetch_word Ubsan.M.loaded_segments (0x1b710 : word) = Some W_1b710.
Proof. vm_refl. Qed.
Lemma D_1b710 : decode_any W_1b710 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b714 : bv 32 := 0x03813983.
Lemma F_1b714 : fetch_word Ubsan.M.loaded_segments (0x1b714 : word) = Some W_1b714.
Proof. vm_refl. Qed.
Lemma D_1b714 : decode_any W_1b714 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b718 : bv 32 := 0x03013a03.
Lemma F_1b718 : fetch_word Ubsan.M.loaded_segments (0x1b718 : word) = Some W_1b718.
Proof. vm_refl. Qed.
Lemma D_1b718 : decode_any W_1b718 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b71c : bv 32 := 0x02813a83.
Lemma F_1b71c : fetch_word Ubsan.M.loaded_segments (0x1b71c : word) = Some W_1b71c.
Proof. vm_refl. Qed.
Lemma D_1b71c : decode_any W_1b71c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b720 : bv 32 := 0x02013b03.
Lemma F_1b720 : fetch_word Ubsan.M.loaded_segments (0x1b720 : word) = Some W_1b720.
Proof. vm_refl. Qed.
Lemma D_1b720 : decode_any W_1b720 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b724 : bv 32 := 0x01813b83.
Lemma F_1b724 : fetch_word Ubsan.M.loaded_segments (0x1b724 : word) = Some W_1b724.
Proof. vm_refl. Qed.
Lemma D_1b724 : decode_any W_1b724 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b728 : bv 32 := 0x01013c03.
Lemma F_1b728 : fetch_word Ubsan.M.loaded_segments (0x1b728 : word) = Some W_1b728.
Proof. vm_refl. Qed.
Lemma D_1b728 : decode_any W_1b728 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b72c : bv 32 := 0x06010113.
Lemma F_1b72c : fetch_word Ubsan.M.loaded_segments (0x1b72c : word) = Some W_1b72c.
Proof. vm_refl. Qed.
Lemma D_1b72c : decode_any W_1b72c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b730 : bv 32 := 0xf94fc06f.
Lemma F_1b730 : fetch_word Ubsan.M.loaded_segments (0x1b730 : word) = Some W_1b730.
Proof. vm_refl. Qed.
Lemma D_1b730 : decode_any W_1b730 = Some (Jal 0 2082708, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b734 : bv 32 := 0x00c10593.
Lemma F_1b734 : fetch_word Ubsan.M.loaded_segments (0x1b734 : word) = Some W_1b734.
Proof. vm_refl. Qed.
Lemma D_1b734 : decode_any W_1b734 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b738 : bv 32 := 0x00810613.
Lemma F_1b738 : fetch_word Ubsan.M.loaded_segments (0x1b738 : word) = Some W_1b738.
Proof. vm_refl. Qed.
Lemma D_1b738 : decode_any W_1b738 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b73c : bv 32 := 0x00090513.
Lemma F_1b73c : fetch_word Ubsan.M.loaded_segments (0x1b73c : word) = Some W_1b73c.
Proof. vm_refl. Qed.
Lemma D_1b73c : decode_any W_1b73c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b740 : bv 32 := 0x00000693.
Lemma F_1b740 : fetch_word Ubsan.M.loaded_segments (0x1b740 : word) = Some W_1b740.
Proof. vm_refl. Qed.
Lemma D_1b740 : decode_any W_1b740 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b744 : bv 32 := 0xbf4fe0ef.
Lemma F_1b744 : fetch_word Ubsan.M.loaded_segments (0x1b744 : word) = Some W_1b744.
Proof. vm_refl. Qed.
Lemma D_1b744 : decode_any W_1b744 = Some (Jal 1 2089972, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b748 : bv 32 := 0x00c12503.
Lemma F_1b748 : fetch_word Ubsan.M.loaded_segments (0x1b748 : word) = Some W_1b748.
Proof. vm_refl. Qed.
Lemma D_1b748 : decode_any W_1b748 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b74c : bv 32 := 0x00812583.
Lemma F_1b74c : fetch_word Ubsan.M.loaded_segments (0x1b74c : word) = Some W_1b74c.
Proof. vm_refl. Qed.
Lemma D_1b74c : decode_any W_1b74c = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b750 : bv 32 := 0x00800613.
Lemma F_1b750 : fetch_word Ubsan.M.loaded_segments (0x1b750 : word) = Some W_1b750.
Proof. vm_refl. Qed.
Lemma D_1b750 : decode_any W_1b750 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b754 : bv 32 := 0xb7dfd0ef.
Lemma F_1b754 : fetch_word Ubsan.M.loaded_segments (0x1b754 : word) = Some W_1b754.
Proof. vm_refl. Qed.
Lemma D_1b754 : decode_any W_1b754 = Some (Jal 1 2087804, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b758 : bv 32 := 0x18050a63.
Lemma F_1b758 : fetch_word Ubsan.M.loaded_segments (0x1b758 : word) = Some W_1b758.
Proof. vm_refl. Qed.
Lemma D_1b758 : decode_any W_1b758 = Some (Branch BC_EQ 10 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b75c : bv 32 := 0x00050a13.
Lemma F_1b75c : fetch_word Ubsan.M.loaded_segments (0x1b75c : word) = Some W_1b75c.
Proof. vm_refl. Qed.
Lemma D_1b75c : decode_any W_1b75c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b760 : bv 32 := 0x00090593.
Lemma F_1b760 : fetch_word Ubsan.M.loaded_segments (0x1b760 : word) = Some W_1b760.
Proof. vm_refl. Qed.
Lemma D_1b760 : decode_any W_1b760 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b764 : bv 32 := 0xc90fe0ef.
Lemma F_1b764 : fetch_word Ubsan.M.loaded_segments (0x1b764 : word) = Some W_1b764.
Proof. vm_refl. Qed.
Lemma D_1b764 : decode_any W_1b764 = Some (Jal 1 2090128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b768 : bv 32 := 0x00090513.
Lemma F_1b768 : fetch_word Ubsan.M.loaded_segments (0x1b768 : word) = Some W_1b768.
Proof. vm_refl. Qed.
Lemma D_1b768 : decode_any W_1b768 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b76c : bv 32 := 0x874fe0ef.
Lemma F_1b76c : fetch_word Ubsan.M.loaded_segments (0x1b76c : word) = Some W_1b76c.
Proof. vm_refl. Qed.
Lemma D_1b76c : decode_any W_1b76c = Some (Jal 1 2089076, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b770 : bv 32 := 0x00050413.
Lemma F_1b770 : fetch_word Ubsan.M.loaded_segments (0x1b770 : word) = Some W_1b770.
Proof. vm_refl. Qed.
Lemma D_1b770 : decode_any W_1b770 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b774 : bv 32 := 0x000a0513.
Lemma F_1b774 : fetch_word Ubsan.M.loaded_segments (0x1b774 : word) = Some W_1b774.
Proof. vm_refl. Qed.
Lemma D_1b774 : decode_any W_1b774 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b778 : bv 32 := 0x868fe0ef.
Lemma F_1b778 : fetch_word Ubsan.M.loaded_segments (0x1b778 : word) = Some W_1b778.
Proof. vm_refl. Qed.
Lemma D_1b778 : decode_any W_1b778 = Some (Jal 1 2089064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b77c : bv 32 := 0x00050493.
Lemma F_1b77c : fetch_word Ubsan.M.loaded_segments (0x1b77c : word) = Some W_1b77c.
Proof. vm_refl. Qed.
Lemma D_1b77c : decode_any W_1b77c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b780 : bv 32 := 0x00090513.
Lemma F_1b780 : fetch_word Ubsan.M.loaded_segments (0x1b780 : word) = Some W_1b780.
Proof. vm_refl. Qed.
Lemma D_1b780 : decode_any W_1b780 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b784 : bv 32 := 0xa20ff0ef.
Lemma F_1b784 : fetch_word Ubsan.M.loaded_segments (0x1b784 : word) = Some W_1b784.
Proof. vm_refl. Qed.
Lemma D_1b784 : decode_any W_1b784 = Some (Jal 1 2093600, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b788 : bv 32 := 0x00050913.
Lemma F_1b788 : fetch_word Ubsan.M.loaded_segments (0x1b788 : word) = Some W_1b788.
Proof. vm_refl. Qed.
Lemma D_1b788 : decode_any W_1b788 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b78c : bv 32 := 0x000a0a93.
Lemma F_1b78c : fetch_word Ubsan.M.loaded_segments (0x1b78c : word) = Some W_1b78c.
Proof. vm_refl. Qed.
Lemma D_1b78c : decode_any W_1b78c = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b790 : bv 32 := 0x000a0513.
Lemma F_1b790 : fetch_word Ubsan.M.loaded_segments (0x1b790 : word) = Some W_1b790.
Proof. vm_refl. Qed.
Lemma D_1b790 : decode_any W_1b790 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b794 : bv 32 := 0xa10ff0ef.
Lemma F_1b794 : fetch_word Ubsan.M.loaded_segments (0x1b794 : word) = Some W_1b794.
Proof. vm_refl. Qed.
Lemma D_1b794 : decode_any W_1b794 = Some (Jal 1 2093584, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b798 : bv 32 := 0x00812583.
Lemma F_1b798 : fetch_word Ubsan.M.loaded_segments (0x1b798 : word) = Some W_1b798.
Proof. vm_refl. Qed.
Lemma D_1b798 : decode_any W_1b798 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b79c : bv 32 := 0x1ab05a63.
Lemma F_1b79c : fetch_word Ubsan.M.loaded_segments (0x1b79c : word) = Some W_1b79c.
Proof. vm_refl. Qed.
Lemma D_1b79c : decode_any W_1b79c = Some (Branch BC_GE 0 11 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7a0 : bv 32 := 0x00000593.
Lemma F_1b7a0 : fetch_word Ubsan.M.loaded_segments (0x1b7a0 : word) = Some W_1b7a0.
Proof. vm_refl. Qed.
Lemma D_1b7a0 : decode_any W_1b7a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7a4 : bv 32 := 0x00000613.
Lemma F_1b7a4 : fetch_word Ubsan.M.loaded_segments (0x1b7a4 : word) = Some W_1b7a4.
Proof. vm_refl. Qed.
Lemma D_1b7a4 : decode_any W_1b7a4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7a8 : bv 32 := 0x00000693.
Lemma F_1b7a8 : fetch_word Ubsan.M.loaded_segments (0x1b7a8 : word) = Some W_1b7a8.
Proof. vm_refl. Qed.
Lemma D_1b7a8 : decode_any W_1b7a8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7ac : bv 32 := 0x02099993.
Lemma F_1b7ac : fetch_word Ubsan.M.loaded_segments (0x1b7ac : word) = Some W_1b7ac.
Proof. vm_refl. Qed.
Lemma D_1b7ac : decode_any W_1b7ac = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7b0 : bv 32 := 0x01203733.
Lemma F_1b7b0 : fetch_word Ubsan.M.loaded_segments (0x1b7b0 : word) = Some W_1b7b0.
Proof. vm_refl. Qed.
Lemma D_1b7b0 : decode_any W_1b7b0 = Some (Op ALU_SLTU 14 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7b4 : bv 32 := 0x00a037b3.
Lemma F_1b7b4 : fetch_word Ubsan.M.loaded_segments (0x1b7b4 : word) = Some W_1b7b4.
Proof. vm_refl. Qed.
Lemma D_1b7b4 : decode_any W_1b7b4 = Some (Op ALU_SLTU 15 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7b8 : bv 32 := 0x0209d813.
Lemma F_1b7b8 : fetch_word Ubsan.M.loaded_segments (0x1b7b8 : word) = Some W_1b7b8.
Proof. vm_refl. Qed.
Lemma D_1b7b8 : decode_any W_1b7b8 = Some (ShiftImm ALU_SRL 16 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7bc : bv 32 := 0x010908b3.
Lemma F_1b7bc : fetch_word Ubsan.M.loaded_segments (0x1b7bc : word) = Some W_1b7bc.
Proof. vm_refl. Qed.
Lemma D_1b7bc : decode_any W_1b7bc = Some (Op ALU_ADD 17 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7c0 : bv 32 := 0x00300293.
Lemma F_1b7c0 : fetch_word Ubsan.M.loaded_segments (0x1b7c0 : word) = Some W_1b7c0.
Proof. vm_refl. Qed.
Lemma D_1b7c0 : decode_any W_1b7c0 = Some (OpImm ALU_ADD 5 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7c4 : bv 32 := 0x000a8313.
Lemma F_1b7c4 : fetch_word Ubsan.M.loaded_segments (0x1b7c4 : word) = Some W_1b7c4.
Proof. vm_refl. Qed.
Lemma D_1b7c4 : decode_any W_1b7c4 = Some (OpImm ALU_ADD 6 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7c8 : bv 32 := 0x0180006f.
Lemma F_1b7c8 : fetch_word Ubsan.M.loaded_segments (0x1b7c8 : word) = Some W_1b7c8.
Proof. vm_refl. Qed.
Lemma D_1b7c8 : decode_any W_1b7c8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7cc : bv 32 := 0x00812383.
Lemma F_1b7cc : fetch_word Ubsan.M.loaded_segments (0x1b7cc : word) = Some W_1b7cc.
Proof. vm_refl. Qed.
Lemma D_1b7cc : decode_any W_1b7cc = Some (Load SZ4 true 7 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7d0 : bv 32 := 0x0016869b.
Lemma F_1b7d0 : fetch_word Ubsan.M.loaded_segments (0x1b7d0 : word) = Some W_1b7d0.
Proof. vm_refl. Qed.
Lemma D_1b7d0 : decode_any W_1b7d0 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7d4 : bv 32 := 0x0096063b.
Lemma F_1b7d4 : fetch_word Ubsan.M.loaded_segments (0x1b7d4 : word) = Some W_1b7d4.
Proof. vm_refl. Qed.
Lemma D_1b7d4 : decode_any W_1b7d4 = Some (Op32 ALU_ADD 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7d8 : bv 32 := 0x008585bb.
Lemma F_1b7d8 : fetch_word Ubsan.M.loaded_segments (0x1b7d8 : word) = Some W_1b7d8.
Proof. vm_refl. Qed.
Lemma D_1b7d8 : decode_any W_1b7d8 = Some (Op32 ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7dc : bv 32 := 0x1076d463.
Lemma F_1b7dc : fetch_word Ubsan.M.loaded_segments (0x1b7dc : word) = Some W_1b7dc.
Proof. vm_refl. Qed.
Lemma D_1b7dc : decode_any W_1b7dc = Some (Branch BC_GE 13 7 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7e0 : bv 32 := 0x02868e33.
Lemma F_1b7e0 : fetch_word Ubsan.M.loaded_segments (0x1b7e0 : word) = Some W_1b7e0.
Proof. vm_refl. Qed.
Lemma D_1b7e0 : decode_any W_1b7e0 = Some (Mul M_MUL 28 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7e4 : bv 32 := 0x028683bb.
Lemma F_1b7e4 : fetch_word Ubsan.M.loaded_segments (0x1b7e4 : word) = Some W_1b7e4.
Proof. vm_refl. Qed.
Lemma D_1b7e4 : decode_any W_1b7e4 = Some (Mul32 M_MUL 7 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7e8 : bv 32 := 0x17c39863.
Lemma F_1b7e8 : fetch_word Ubsan.M.loaded_segments (0x1b7e8 : word) = Some W_1b7e8.
Proof. vm_refl. Qed.
Lemma D_1b7e8 : decode_any W_1b7e8 = Some (Branch BC_NE 7 28 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7ec : bv 32 := 0x000e0e1b.
Lemma F_1b7ec : fetch_word Ubsan.M.loaded_segments (0x1b7ec : word) = Some W_1b7ec.
Proof. vm_refl. Qed.
Lemma D_1b7ec : decode_any W_1b7ec = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7f0 : bv 32 := 0x002e1393.
Lemma F_1b7f0 : fetch_word Ubsan.M.loaded_segments (0x1b7f0 : word) = Some W_1b7f0.
Proof. vm_refl. Qed.
Lemma D_1b7f0 : decode_any W_1b7f0 = Some (ShiftImm ALU_SLL 7 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7f4 : bv 32 := 0x007903b3.
Lemma F_1b7f4 : fetch_word Ubsan.M.loaded_segments (0x1b7f4 : word) = Some W_1b7f4.
Proof. vm_refl. Qed.
Lemma D_1b7f4 : decode_any W_1b7f4 = Some (Op ALU_ADD 7 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7f8 : bv 32 := 0x0013be93.
Lemma F_1b7f8 : fetch_word Ubsan.M.loaded_segments (0x1b7f8 : word) = Some W_1b7f8.
Proof. vm_refl. Qed.
Lemma D_1b7f8 : decode_any W_1b7f8 = Some (OpImm ALU_SLTU 29 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b7fc : bv 32 := 0x15d70e63.
Lemma F_1b7fc : fetch_word Ubsan.M.loaded_segments (0x1b7fc : word) = Some W_1b7fc.
Proof. vm_refl. Qed.
Lemma D_1b7fc : decode_any W_1b7fc = Some (Branch BC_EQ 14 29 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b800 : bv 32 := 0x0123beb3.
Lemma F_1b800 : fetch_word Ubsan.M.loaded_segments (0x1b800 : word) = Some W_1b800.
Proof. vm_refl. Qed.
Lemma D_1b800 : decode_any W_1b800 = Some (Op ALU_SLTU 29 7 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b804 : bv 32 := 0x000e2e13.
Lemma F_1b804 : fetch_word Ubsan.M.loaded_segments (0x1b804 : word) = Some W_1b804.
Proof. vm_refl. Qed.
Lemma D_1b804 : decode_any W_1b804 = Some (OpImm ALU_SLT 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b808 : bv 32 := 0x01cece33.
Lemma F_1b808 : fetch_word Ubsan.M.loaded_segments (0x1b808 : word) = Some W_1b808.
Proof. vm_refl. Qed.
Lemma D_1b808 : decode_any W_1b808 = Some (Op ALU_XOR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b80c : bv 32 := 0x001e4e13.
Lemma F_1b80c : fetch_word Ubsan.M.loaded_segments (0x1b80c : word) = Some W_1b80c.
Proof. vm_refl. Qed.
Lemma D_1b80c : decode_any W_1b80c = Some (OpImm ALU_XOR 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b810 : bv 32 := 0x140e0463.
Lemma F_1b810 : fetch_word Ubsan.M.loaded_segments (0x1b810 : word) = Some W_1b810.
Proof. vm_refl. Qed.
Lemma D_1b810 : decode_any W_1b810 = Some (Branch BC_EQ 28 0 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b814 : bv 32 := 0x02968eb3.
Lemma F_1b814 : fetch_word Ubsan.M.loaded_segments (0x1b814 : word) = Some W_1b814.
Proof. vm_refl. Qed.
Lemma D_1b814 : decode_any W_1b814 = Some (Mul M_MUL 29 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b818 : bv 32 := 0x02968e3b.
Lemma F_1b818 : fetch_word Ubsan.M.loaded_segments (0x1b818 : word) = Some W_1b818.
Proof. vm_refl. Qed.
Lemma D_1b818 : decode_any W_1b818 = Some (Mul32 M_MUL 28 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b81c : bv 32 := 0x13de1e63.
Lemma F_1b81c : fetch_word Ubsan.M.loaded_segments (0x1b81c : word) = Some W_1b81c.
Proof. vm_refl. Qed.
Lemma D_1b81c : decode_any W_1b81c = Some (Branch BC_NE 28 29 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b820 : bv 32 := 0x000e8e9b.
Lemma F_1b820 : fetch_word Ubsan.M.loaded_segments (0x1b820 : word) = Some W_1b820.
Proof. vm_refl. Qed.
Lemma D_1b820 : decode_any W_1b820 = Some (OpImm32 29 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b824 : bv 32 := 0x002e9e13.
Lemma F_1b824 : fetch_word Ubsan.M.loaded_segments (0x1b824 : word) = Some W_1b824.
Proof. vm_refl. Qed.
Lemma D_1b824 : decode_any W_1b824 = Some (ShiftImm ALU_SLL 28 29 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b828 : bv 32 := 0x01c50e33.
Lemma F_1b828 : fetch_word Ubsan.M.loaded_segments (0x1b828 : word) = Some W_1b828.
Proof. vm_refl. Qed.
Lemma D_1b828 : decode_any W_1b828 = Some (Op ALU_ADD 28 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b82c : bv 32 := 0x001e3f13.
Lemma F_1b82c : fetch_word Ubsan.M.loaded_segments (0x1b82c : word) = Some W_1b82c.
Proof. vm_refl. Qed.
Lemma D_1b82c : decode_any W_1b82c = Some (OpImm ALU_SLTU 30 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b830 : bv 32 := 0x13e78463.
Lemma F_1b830 : fetch_word Ubsan.M.loaded_segments (0x1b830 : word) = Some W_1b830.
Proof. vm_refl. Qed.
Lemma D_1b830 : decode_any W_1b830 = Some (Branch BC_EQ 15 30 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b834 : bv 32 := 0x00ae3f33.
Lemma F_1b834 : fetch_word Ubsan.M.loaded_segments (0x1b834 : word) = Some W_1b834.
Proof. vm_refl. Qed.
Lemma D_1b834 : decode_any W_1b834 = Some (Op ALU_SLTU 30 28 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b838 : bv 32 := 0x000eae93.
Lemma F_1b838 : fetch_word Ubsan.M.loaded_segments (0x1b838 : word) = Some W_1b838.
Proof. vm_refl. Qed.
Lemma D_1b838 : decode_any W_1b838 = Some (OpImm ALU_SLT 29 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b83c : bv 32 := 0x01df4eb3.
Lemma F_1b83c : fetch_word Ubsan.M.loaded_segments (0x1b83c : word) = Some W_1b83c.
Proof. vm_refl. Qed.
Lemma D_1b83c : decode_any W_1b83c = Some (Op ALU_XOR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b840 : bv 32 := 0x001ece93.
Lemma F_1b840 : fetch_word Ubsan.M.loaded_segments (0x1b840 : word) = Some W_1b840.
Proof. vm_refl. Qed.
Lemma D_1b840 : decode_any W_1b840 = Some (OpImm ALU_XOR 29 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b844 : bv 32 := 0x100e8a63.
Lemma F_1b844 : fetch_word Ubsan.M.loaded_segments (0x1b844 : word) = Some W_1b844.
Proof. vm_refl. Qed.
Lemma D_1b844 : decode_any W_1b844 = Some (Branch BC_EQ 29 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b848 : bv 32 := 0x00c12e83.
Lemma F_1b848 : fetch_word Ubsan.M.loaded_segments (0x1b848 : word) = Some W_1b848.
Proof. vm_refl. Qed.
Lemma D_1b848 : decode_any W_1b848 = Some (Load SZ4 true 29 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b84c : bv 32 := 0xf9d050e3.
Lemma F_1b84c : fetch_word Ubsan.M.loaded_segments (0x1b84c : word) = Some W_1b84c.
Proof. vm_refl. Qed.
Lemma D_1b84c : decode_any W_1b84c = Some (Branch BC_GE 0 29 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b850 : bv 32 := 0x00000e93.
Lemma F_1b850 : fetch_word Ubsan.M.loaded_segments (0x1b850 : word) = Some W_1b850.
Proof. vm_refl. Qed.
Lemma D_1b850 : decode_any W_1b850 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b854 : bv 32 := 0x00000f13.
Lemma F_1b854 : fetch_word Ubsan.M.loaded_segments (0x1b854 : word) = Some W_1b854.
Proof. vm_refl. Qed.
Lemma D_1b854 : decode_any W_1b854 = Some (OpImm ALU_ADD 30 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b858 : bv 32 := 0x00261f93.
Lemma F_1b858 : fetch_word Ubsan.M.loaded_segments (0x1b858 : word) = Some W_1b858.
Proof. vm_refl. Qed.
Lemma D_1b858 : decode_any W_1b858 = Some (ShiftImm ALU_SLL 31 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b85c : bv 32 := 0x00259a13.
Lemma F_1b85c : fetch_word Ubsan.M.loaded_segments (0x1b85c : word) = Some W_1b85c.
Proof. vm_refl. Qed.
Lemma D_1b85c : decode_any W_1b85c = Some (ShiftImm ALU_SLL 20 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b860 : bv 32 := 0x01f50fb3.
Lemma F_1b860 : fetch_word Ubsan.M.loaded_segments (0x1b860 : word) = Some W_1b860.
Proof. vm_refl. Qed.
Lemma D_1b860 : decode_any W_1b860 = Some (Op ALU_ADD 31 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b864 : bv 32 := 0x014909b3.
Lemma F_1b864 : fetch_word Ubsan.M.loaded_segments (0x1b864 : word) = Some W_1b864.
Proof. vm_refl. Qed.
Lemma D_1b864 : decode_any W_1b864 = Some (Op ALU_ADD 19 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b868 : bv 32 := 0x01488a33.
Lemma F_1b868 : fetch_word Ubsan.M.loaded_segments (0x1b868 : word) = Some W_1b868.
Proof. vm_refl. Qed.
Lemma D_1b868 : decode_any W_1b868 = Some (Op ALU_ADD 20 17 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b86c : bv 32 := 0x01380ab3.
Lemma F_1b86c : fetch_word Ubsan.M.loaded_segments (0x1b86c : word) = Some W_1b86c.
Proof. vm_refl. Qed.
Lemma D_1b86c : decode_any W_1b86c = Some (Op ALU_ADD 21 16 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b870 : bv 32 := 0x000f8b13.
Lemma F_1b870 : fetch_word Ubsan.M.loaded_segments (0x1b870 : word) = Some W_1b870.
Proof. vm_refl. Qed.
Lemma D_1b870 : decode_any W_1b870 = Some (OpImm ALU_ADD 22 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b874 : bv 32 := 0x01d98c33.
Lemma F_1b874 : fetch_word Ubsan.M.loaded_segments (0x1b874 : word) = Some W_1b874.
Proof. vm_refl. Qed.
Lemma D_1b874 : decode_any W_1b874 = Some (Op ALU_ADD 24 19 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b878 : bv 32 := 0x0e7c6063.
Lemma F_1b878 : fetch_word Ubsan.M.loaded_segments (0x1b878 : word) = Some W_1b878.
Proof. vm_refl. Qed.
Lemma D_1b878 : decode_any W_1b878 = Some (Branch BC_LTU 24 7 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b87c : bv 32 := 0x001c3b93.
Lemma F_1b87c : fetch_word Ubsan.M.loaded_segments (0x1b87c : word) = Some W_1b87c.
Proof. vm_refl. Qed.
Lemma D_1b87c : decode_any W_1b87c = Some (OpImm ALU_SLTU 23 24 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b880 : bv 32 := 0x01774bb3.
Lemma F_1b880 : fetch_word Ubsan.M.loaded_segments (0x1b880 : word) = Some W_1b880.
Proof. vm_refl. Qed.
Lemma D_1b880 : decode_any W_1b880 = Some (Op ALU_XOR 23 14 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b884 : bv 32 := 0x0c0b8a63.
Lemma F_1b884 : fetch_word Ubsan.M.loaded_segments (0x1b884 : word) = Some W_1b884.
Proof. vm_refl. Qed.
Lemma D_1b884 : decode_any W_1b884 = Some (Branch BC_EQ 23 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b888 : bv 32 := 0x01da0bb3.
Lemma F_1b888 : fetch_word Ubsan.M.loaded_segments (0x1b888 : word) = Some W_1b888.
Proof. vm_refl. Qed.
Lemma D_1b888 : decode_any W_1b888 = Some (Op ALU_ADD 23 20 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b88c : bv 32 := 0x0d8be663.
Lemma F_1b88c : fetch_word Ubsan.M.loaded_segments (0x1b88c : word) = Some W_1b88c.
Proof. vm_refl. Qed.
Lemma D_1b88c : decode_any W_1b88c = Some (Branch BC_LTU 23 24 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b890 : bv 32 := 0x01da8c33.
Lemma F_1b890 : fetch_word Ubsan.M.loaded_segments (0x1b890 : word) = Some W_1b890.
Proof. vm_refl. Qed.
Lemma D_1b890 : decode_any W_1b890 = Some (Op ALU_ADD 24 21 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b894 : bv 32 := 0x001c3c13.
Lemma F_1b894 : fetch_word Ubsan.M.loaded_segments (0x1b894 : word) = Some W_1b894.
Proof. vm_refl. Qed.
Lemma D_1b894 : decode_any W_1b894 = Some (OpImm ALU_SLTU 24 24 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b898 : bv 32 := 0x01874c33.
Lemma F_1b898 : fetch_word Ubsan.M.loaded_segments (0x1b898 : word) = Some W_1b898.
Proof. vm_refl. Qed.
Lemma D_1b898 : decode_any W_1b898 = Some (Op ALU_XOR 24 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b89c : bv 32 := 0x0a0c0e63.
Lemma F_1b89c : fetch_word Ubsan.M.loaded_segments (0x1b89c : word) = Some W_1b89c.
Proof. vm_refl. Qed.
Lemma D_1b89c : decode_any W_1b89c = Some (Branch BC_EQ 24 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8a0 : bv 32 := 0x0a5b8c63.
Lemma F_1b8a0 : fetch_word Ubsan.M.loaded_segments (0x1b8a0 : word) = Some W_1b8a0.
Proof. vm_refl. Qed.
Lemma D_1b8a0 : decode_any W_1b8a0 = Some (Branch BC_EQ 23 5 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8a4 : bv 32 := 0x0bcb6a63.
Lemma F_1b8a4 : fetch_word Ubsan.M.loaded_segments (0x1b8a4 : word) = Some W_1b8a4.
Proof. vm_refl. Qed.
Lemma D_1b8a4 : decode_any W_1b8a4 = Some (Branch BC_LTU 22 28 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8a8 : bv 32 := 0x001b3c13.
Lemma F_1b8a8 : fetch_word Ubsan.M.loaded_segments (0x1b8a8 : word) = Some W_1b8a8.
Proof. vm_refl. Qed.
Lemma D_1b8a8 : decode_any W_1b8a8 = Some (OpImm ALU_SLTU 24 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8ac : bv 32 := 0x0187cc33.
Lemma F_1b8ac : fetch_word Ubsan.M.loaded_segments (0x1b8ac : word) = Some W_1b8ac.
Proof. vm_refl. Qed.
Lemma D_1b8ac : decode_any W_1b8ac = Some (Op ALU_XOR 24 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8b0 : bv 32 := 0x0a0c0463.
Lemma F_1b8b0 : fetch_word Ubsan.M.loaded_segments (0x1b8b0 : word) = Some W_1b8b0.
Proof. vm_refl. Qed.
Lemma D_1b8b0 : decode_any W_1b8b0 = Some (Branch BC_EQ 24 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8b4 : bv 32 := 0x01ef8c33.
Lemma F_1b8b4 : fetch_word Ubsan.M.loaded_segments (0x1b8b4 : word) = Some W_1b8b4.
Proof. vm_refl. Qed.
Lemma D_1b8b4 : decode_any W_1b8b4 = Some (Op ALU_ADD 24 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8b8 : bv 32 := 0x0a5c0063.
Lemma F_1b8b8 : fetch_word Ubsan.M.loaded_segments (0x1b8b8 : word) = Some W_1b8b8.
Proof. vm_refl. Qed.
Lemma D_1b8b8 : decode_any W_1b8b8 = Some (Branch BC_EQ 24 5 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8bc : bv 32 := 0x003bcb93.
Lemma F_1b8bc : fetch_word Ubsan.M.loaded_segments (0x1b8bc : word) = Some W_1b8bc.
Proof. vm_refl. Qed.
Lemma D_1b8bc : decode_any W_1b8bc = Some (OpImm ALU_XOR 23 23 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8c0 : bv 32 := 0x000bcb83.
Lemma F_1b8c0 : fetch_word Ubsan.M.loaded_segments (0x1b8c0 : word) = Some W_1b8c0.
Proof. vm_refl. Qed.
Lemma D_1b8c0 : decode_any W_1b8c0 = Some (Load SZ1 false 23 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8c4 : bv 32 := 0x003b4c13.
Lemma F_1b8c4 : fetch_word Ubsan.M.loaded_segments (0x1b8c4 : word) = Some W_1b8c4.
Proof. vm_refl. Qed.
Lemma D_1b8c4 : decode_any W_1b8c4 = Some (OpImm ALU_XOR 24 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8c8 : bv 32 := 0x017c0023.
Lemma F_1b8c8 : fetch_word Ubsan.M.loaded_segments (0x1b8c8 : word) = Some W_1b8c8.
Proof. vm_refl. Qed.
Lemma D_1b8c8 : decode_any W_1b8c8 = Some (Store SZ1 24 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8cc : bv 32 := 0x00c12b83.
Lemma F_1b8cc : fetch_word Ubsan.M.loaded_segments (0x1b8cc : word) = Some W_1b8cc.
Proof. vm_refl. Qed.
Lemma D_1b8cc : decode_any W_1b8cc = Some (Load SZ4 true 23 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8d0 : bv 32 := 0x001f0f13.
Lemma F_1b8d0 : fetch_word Ubsan.M.loaded_segments (0x1b8d0 : word) = Some W_1b8d0.
Proof. vm_refl. Qed.
Lemma D_1b8d0 : decode_any W_1b8d0 = Some (OpImm ALU_ADD 30 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8d4 : bv 32 := 0x001b0b13.
Lemma F_1b8d4 : fetch_word Ubsan.M.loaded_segments (0x1b8d4 : word) = Some W_1b8d4.
Proof. vm_refl. Qed.
Lemma D_1b8d4 : decode_any W_1b8d4 = Some (OpImm ALU_ADD 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8d8 : bv 32 := 0x004e8e93.
Lemma F_1b8d8 : fetch_word Ubsan.M.loaded_segments (0x1b8d8 : word) = Some W_1b8d8.
Proof. vm_refl. Qed.
Lemma D_1b8d8 : decode_any W_1b8d8 = Some (OpImm ALU_ADD 29 29 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8dc : bv 32 := 0xf97f4ce3.
Lemma F_1b8dc : fetch_word Ubsan.M.loaded_segments (0x1b8dc : word) = Some W_1b8dc.
Proof. vm_refl. Qed.
Lemma D_1b8dc : decode_any W_1b8dc = Some (Branch BC_LT 30 23 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8e0 : bv 32 := 0xeedff06f.
Lemma F_1b8e0 : fetch_word Ubsan.M.loaded_segments (0x1b8e0 : word) = Some W_1b8e0.
Proof. vm_refl. Qed.
Lemma D_1b8e0 : decode_any W_1b8e0 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8e4 : bv 32 := 0x00030513.
Lemma F_1b8e4 : fetch_word Ubsan.M.loaded_segments (0x1b8e4 : word) = Some W_1b8e4.
Proof. vm_refl. Qed.
Lemma D_1b8e4 : decode_any W_1b8e4 = Some (OpImm ALU_ADD 10 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8e8 : bv 32 := 0x0380006f.
Lemma F_1b8e8 : fetch_word Ubsan.M.loaded_segments (0x1b8e8 : word) = Some W_1b8e8.
Proof. vm_refl. Qed.
Lemma D_1b8e8 : decode_any W_1b8e8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8ec : bv 32 := 0x00029517.
Lemma F_1b8ec : fetch_word Ubsan.M.loaded_segments (0x1b8ec : word) = Some W_1b8ec.
Proof. vm_refl. Qed.
Lemma D_1b8ec : decode_any W_1b8ec = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8f0 : bv 32 := 0x5ac53503.
Lemma F_1b8f0 : fetch_word Ubsan.M.loaded_segments (0x1b8f0 : word) = Some W_1b8f0.
Proof. vm_refl. Qed.
Lemma D_1b8f0 : decode_any W_1b8f0 = Some (Load SZ8 true 10 10 1452, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8f4 : bv 32 := 0x00052503.
Lemma F_1b8f4 : fetch_word Ubsan.M.loaded_segments (0x1b8f4 : word) = Some W_1b8f4.
Proof. vm_refl. Qed.
Lemma D_1b8f4 : decode_any W_1b8f4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8f8 : bv 32 := 0x00500593.
Lemma F_1b8f8 : fetch_word Ubsan.M.loaded_segments (0x1b8f8 : word) = Some W_1b8f8.
Proof. vm_refl. Qed.
Lemma D_1b8f8 : decode_any W_1b8f8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b8fc : bv 32 := 0x02a5c063.
Lemma F_1b8fc : fetch_word Ubsan.M.loaded_segments (0x1b8fc : word) = Some W_1b8fc.
Proof. vm_refl. Qed.
Lemma D_1b8fc : decode_any W_1b8fc = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b900 : bv 32 := 0xffff5517.
Lemma F_1b900 : fetch_word Ubsan.M.loaded_segments (0x1b900 : word) = Some W_1b900.
Proof. vm_refl. Qed.
Lemma D_1b900 : decode_any W_1b900 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b904 : bv 32 := 0xffff5597.
Lemma F_1b904 : fetch_word Ubsan.M.loaded_segments (0x1b904 : word) = Some W_1b904.
Proof. vm_refl. Qed.
Lemma D_1b904 : decode_any W_1b904 = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b908 : bv 32 := 0xe6550513.
Lemma F_1b908 : fetch_word Ubsan.M.loaded_segments (0x1b908 : word) = Some W_1b908.
Proof. vm_refl. Qed.
Lemma D_1b908 : decode_any W_1b908 = Some (OpImm ALU_ADD 10 10 3685, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b90c : bv 32 := 0x01e58593.
Lemma F_1b90c : fetch_word Ubsan.M.loaded_segments (0x1b90c : word) = Some W_1b90c.
Proof. vm_refl. Qed.
Lemma D_1b90c : decode_any W_1b90c = Some (OpImm ALU_ADD 11 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b910 : bv 32 := 0x00000613.
Lemma F_1b910 : fetch_word Ubsan.M.loaded_segments (0x1b910 : word) = Some W_1b910.
Proof. vm_refl. Qed.
Lemma D_1b910 : decode_any W_1b910 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b914 : bv 32 := 0xdb0fc0ef.
Lemma F_1b914 : fetch_word Ubsan.M.loaded_segments (0x1b914 : word) = Some W_1b914.
Proof. vm_refl. Qed.
Lemma D_1b914 : decode_any W_1b914 = Some (Jal 1 2082224, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b918 : bv 32 := 0x0080006f.
Lemma F_1b918 : fetch_word Ubsan.M.loaded_segments (0x1b918 : word) = Some W_1b918.
Proof. vm_refl. Qed.
Lemma D_1b918 : decode_any W_1b918 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b91c : bv 32 := 0x00000513.
Lemma F_1b91c : fetch_word Ubsan.M.loaded_segments (0x1b91c : word) = Some W_1b91c.
Proof. vm_refl. Qed.
Lemma D_1b91c : decode_any W_1b91c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b920 : bv 32 := 0x05813083.
Lemma F_1b920 : fetch_word Ubsan.M.loaded_segments (0x1b920 : word) = Some W_1b920.
Proof. vm_refl. Qed.
Lemma D_1b920 : decode_any W_1b920 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b924 : bv 32 := 0x05013403.
Lemma F_1b924 : fetch_word Ubsan.M.loaded_segments (0x1b924 : word) = Some W_1b924.
Proof. vm_refl. Qed.
Lemma D_1b924 : decode_any W_1b924 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b928 : bv 32 := 0x04813483.
Lemma F_1b928 : fetch_word Ubsan.M.loaded_segments (0x1b928 : word) = Some W_1b928.
Proof. vm_refl. Qed.
Lemma D_1b928 : decode_any W_1b928 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b92c : bv 32 := 0x04013903.
Lemma F_1b92c : fetch_word Ubsan.M.loaded_segments (0x1b92c : word) = Some W_1b92c.
Proof. vm_refl. Qed.
Lemma D_1b92c : decode_any W_1b92c = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b930 : bv 32 := 0x03813983.
Lemma F_1b930 : fetch_word Ubsan.M.loaded_segments (0x1b930 : word) = Some W_1b930.
Proof. vm_refl. Qed.
Lemma D_1b930 : decode_any W_1b930 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b934 : bv 32 := 0x03013a03.
Lemma F_1b934 : fetch_word Ubsan.M.loaded_segments (0x1b934 : word) = Some W_1b934.
Proof. vm_refl. Qed.
Lemma D_1b934 : decode_any W_1b934 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b938 : bv 32 := 0x02813a83.
Lemma F_1b938 : fetch_word Ubsan.M.loaded_segments (0x1b938 : word) = Some W_1b938.
Proof. vm_refl. Qed.
Lemma D_1b938 : decode_any W_1b938 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b93c : bv 32 := 0x02013b03.
Lemma F_1b93c : fetch_word Ubsan.M.loaded_segments (0x1b93c : word) = Some W_1b93c.
Proof. vm_refl. Qed.
Lemma D_1b93c : decode_any W_1b93c = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b940 : bv 32 := 0x01813b83.
Lemma F_1b940 : fetch_word Ubsan.M.loaded_segments (0x1b940 : word) = Some W_1b940.
Proof. vm_refl. Qed.
Lemma D_1b940 : decode_any W_1b940 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b944 : bv 32 := 0x01013c03.
Lemma F_1b944 : fetch_word Ubsan.M.loaded_segments (0x1b944 : word) = Some W_1b944.
Proof. vm_refl. Qed.
Lemma D_1b944 : decode_any W_1b944 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b948 : bv 32 := 0x06010113.
Lemma F_1b948 : fetch_word Ubsan.M.loaded_segments (0x1b948 : word) = Some W_1b948.
Proof. vm_refl. Qed.
Lemma D_1b948 : decode_any W_1b948 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b94c : bv 32 := 0x00008067.
Lemma F_1b94c : fetch_word Ubsan.M.loaded_segments (0x1b94c : word) = Some W_1b94c.
Proof. vm_refl. Qed.
Lemma D_1b94c : decode_any W_1b94c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b950 : bv 32 := 0x000a8513.
Lemma F_1b950 : fetch_word Ubsan.M.loaded_segments (0x1b950 : word) = Some W_1b950.
Proof. vm_refl. Qed.
Lemma D_1b950 : decode_any W_1b950 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b954 : bv 32 := 0xfcdff06f.
Lemma F_1b954 : fetch_word Ubsan.M.loaded_segments (0x1b954 : word) = Some W_1b954.
Proof. vm_refl. Qed.
Lemma D_1b954 : decode_any W_1b954 = Some (Jal 0 2097100, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b958 : bv 32 := 0xc0001073.
Lemma F_1b958 : fetch_word Ubsan.M.loaded_segments (0x1b958 : word) = Some W_1b958.
Proof. vm_refl. Qed.
Lemma D_1b958 : decode_any W_1b958 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
