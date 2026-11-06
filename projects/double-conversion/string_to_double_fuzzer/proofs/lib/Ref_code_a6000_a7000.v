(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a662c : bv 32 := 0x0ff5f593.
Lemma F_a662c : fetch_word PSEGS (0xa662c : word) = Some W_a662c.
Proof. vm_refl. Qed.
Lemma D_a662c : decode_any W_a662c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6630 : bv 32 := 0x00757693.
Lemma F_a6630 : fetch_word PSEGS (0xa6630 : word) = Some W_a6630.
Proof. vm_refl. Qed.
Lemma D_a6630 : decode_any W_a6630 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6634 : bv 32 := 0x00c03733.
Lemma F_a6634 : fetch_word PSEGS (0xa6634 : word) = Some W_a6634.
Proof. vm_refl. Qed.
Lemma D_a6634 : decode_any W_a6634 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6638 : bv 32 := 0x02068c63.
Lemma F_a6638 : fetch_word PSEGS (0xa6638 : word) = Some W_a6638.
Proof. vm_refl. Qed.
Lemma D_a6638 : decode_any W_a6638 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a663c : bv 32 := 0x02060a63.
Lemma F_a663c : fetch_word PSEGS (0xa663c : word) = Some W_a663c.
Proof. vm_refl. Qed.
Lemma D_a663c : decode_any W_a663c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6640 : bv 32 := 0x00150793.
Lemma F_a6640 : fetch_word PSEGS (0xa6640 : word) = Some W_a6640.
Proof. vm_refl. Qed.
Lemma D_a6640 : decode_any W_a6640 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6644 : bv 32 := 0x00100813.
Lemma F_a6644 : fetch_word PSEGS (0xa6644 : word) = Some W_a6644.
Proof. vm_refl. Qed.
Lemma D_a6644 : decode_any W_a6644 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6648 : bv 32 := 0x00054703.
Lemma F_a6648 : fetch_word PSEGS (0xa6648 : word) = Some W_a6648.
Proof. vm_refl. Qed.
Lemma D_a6648 : decode_any W_a6648 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a664c : bv 32 := 0x00060693.
Lemma F_a664c : fetch_word PSEGS (0xa664c : word) = Some W_a664c.
Proof. vm_refl. Qed.
Lemma D_a664c : decode_any W_a664c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6650 : bv 32 := 0x06b70e63.
Lemma F_a6650 : fetch_word PSEGS (0xa6650 : word) = Some W_a6650.
Proof. vm_refl. Qed.
Lemma D_a6650 : decode_any W_a6650 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6654 : bv 32 := 0x00150513.
Lemma F_a6654 : fetch_word PSEGS (0xa6654 : word) = Some W_a6654.
Proof. vm_refl. Qed.
Lemma D_a6654 : decode_any W_a6654 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6658 : bv 32 := 0xfff68613.
Lemma F_a6658 : fetch_word PSEGS (0xa6658 : word) = Some W_a6658.
Proof. vm_refl. Qed.
Lemma D_a6658 : decode_any W_a6658 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a665c : bv 32 := 0x0077f893.
Lemma F_a665c : fetch_word PSEGS (0xa665c : word) = Some W_a665c.
Proof. vm_refl. Qed.
Lemma D_a665c : decode_any W_a665c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6660 : bv 32 := 0x00c03733.
Lemma F_a6660 : fetch_word PSEGS (0xa6660 : word) = Some W_a6660.
Proof. vm_refl. Qed.
Lemma D_a6660 : decode_any W_a6660 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6664 : bv 32 := 0x00088663.
Lemma F_a6664 : fetch_word PSEGS (0xa6664 : word) = Some W_a6664.
Proof. vm_refl. Qed.
Lemma D_a6664 : decode_any W_a6664 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6668 : bv 32 := 0x00178793.
Lemma F_a6668 : fetch_word PSEGS (0xa6668 : word) = Some W_a6668.
Proof. vm_refl. Qed.
Lemma D_a6668 : decode_any W_a6668 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a666c : bv 32 := 0xfd069ee3.
Lemma F_a666c : fetch_word PSEGS (0xa666c : word) = Some W_a666c.
Proof. vm_refl. Qed.
Lemma D_a666c : decode_any W_a666c = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6670 : bv 32 := 0x06070863.
Lemma F_a6670 : fetch_word PSEGS (0xa6670 : word) = Some W_a6670.
Proof. vm_refl. Qed.
Lemma D_a6670 : decode_any W_a6670 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6674 : bv 32 := 0x00054683.
Lemma F_a6674 : fetch_word PSEGS (0xa6674 : word) = Some W_a6674.
Proof. vm_refl. Qed.
Lemma D_a6674 : decode_any W_a6674 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6678 : bv 32 := 0x04b68663.
Lemma F_a6678 : fetch_word PSEGS (0xa6678 : word) = Some W_a6678.
Proof. vm_refl. Qed.
Lemma D_a6678 : decode_any W_a6678 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a667c : bv 32 := 0x00800693.
Lemma F_a667c : fetch_word PSEGS (0xa667c : word) = Some W_a667c.
Proof. vm_refl. Qed.
Lemma D_a667c : decode_any W_a667c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6680 : bv 32 := 0x04d66263.
Lemma F_a6680 : fetch_word PSEGS (0xa6680 : word) = Some W_a6680.
Proof. vm_refl. Qed.
Lemma D_a6680 : decode_any W_a6680 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6684 : bv 32 := 0xfff6d697.
Lemma F_a6684 : fetch_word PSEGS (0xa6684 : word) = Some W_a6684.
Proof. vm_refl. Qed.
Lemma D_a6684 : decode_any W_a6684 = Some (Auipc 13 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6688 : bv 32 := 0xd046b683.
Lemma F_a6688 : fetch_word PSEGS (0xa6688 : word) = Some W_a6688.
Proof. vm_refl. Qed.
Lemma D_a6688 : decode_any W_a6688 = Some (Load SZ8 true 13 13 3332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a668c : bv 32 := 0xfff6d717.
Lemma F_a668c : fetch_word PSEGS (0xa668c : word) = Some W_a668c.
Proof. vm_refl. Qed.
Lemma D_a668c : decode_any W_a668c = Some (Auipc 14 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6690 : bv 32 := 0xcec73703.
Lemma F_a6690 : fetch_word PSEGS (0xa6690 : word) = Some W_a6690.
Proof. vm_refl. Qed.
Lemma D_a6690 : decode_any W_a6690 = Some (Load SZ8 true 14 14 3308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6694 : bv 32 := 0x00168793.
Lemma F_a6694 : fetch_word PSEGS (0xa6694 : word) = Some W_a6694.
Proof. vm_refl. Qed.
Lemma D_a6694 : decode_any W_a6694 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6698 : bv 32 := 0x02f587b3.
Lemma F_a6698 : fetch_word PSEGS (0xa6698 : word) = Some W_a6698.
Proof. vm_refl. Qed.
Lemma D_a6698 : decode_any W_a6698 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a669c : bv 32 := 0x00700813.
Lemma F_a669c : fetch_word PSEGS (0xa669c : word) = Some W_a669c.
Proof. vm_refl. Qed.
Lemma D_a669c : decode_any W_a669c = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66a0 : bv 32 := 0x00053883.
Lemma F_a66a0 : fetch_word PSEGS (0xa66a0 : word) = Some W_a66a0.
Proof. vm_refl. Qed.
Lemma D_a66a0 : decode_any W_a66a0 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66a4 : bv 32 := 0x00f8c8b3.
Lemma F_a66a4 : fetch_word PSEGS (0xa66a4 : word) = Some W_a66a4.
Proof. vm_refl. Qed.
Lemma D_a66a4 : decode_any W_a66a4 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66a8 : bv 32 := 0x411682b3.
Lemma F_a66a8 : fetch_word PSEGS (0xa66a8 : word) = Some W_a66a8.
Proof. vm_refl. Qed.
Lemma D_a66a8 : decode_any W_a66a8 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66ac : bv 32 := 0x0112e8b3.
Lemma F_a66ac : fetch_word PSEGS (0xa66ac : word) = Some W_a66ac.
Proof. vm_refl. Qed.
Lemma D_a66ac : decode_any W_a66ac = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66b0 : bv 32 := 0x00e8f8b3.
Lemma F_a66b0 : fetch_word PSEGS (0xa66b0 : word) = Some W_a66b0.
Proof. vm_refl. Qed.
Lemma D_a66b0 : decode_any W_a66b0 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66b4 : bv 32 := 0x02e89a63.
Lemma F_a66b4 : fetch_word PSEGS (0xa66b4 : word) = Some W_a66b4.
Proof. vm_refl. Qed.
Lemma D_a66b4 : decode_any W_a66b4 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66b8 : bv 32 := 0xff860613.
Lemma F_a66b8 : fetch_word PSEGS (0xa66b8 : word) = Some W_a66b8.
Proof. vm_refl. Qed.
Lemma D_a66b8 : decode_any W_a66b8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66bc : bv 32 := 0x00850513.
Lemma F_a66bc : fetch_word PSEGS (0xa66bc : word) = Some W_a66bc.
Proof. vm_refl. Qed.
Lemma D_a66bc : decode_any W_a66bc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66c0 : bv 32 := 0xfec860e3.
Lemma F_a66c0 : fetch_word PSEGS (0xa66c0 : word) = Some W_a66c0.
Proof. vm_refl. Qed.
Lemma D_a66c0 : decode_any W_a66c0 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66c4 : bv 32 := 0x00060693.
Lemma F_a66c4 : fetch_word PSEGS (0xa66c4 : word) = Some W_a66c4.
Proof. vm_refl. Qed.
Lemma D_a66c4 : decode_any W_a66c4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66c8 : bv 32 := 0x00060c63.
Lemma F_a66c8 : fetch_word PSEGS (0xa66c8 : word) = Some W_a66c8.
Proof. vm_refl. Qed.
Lemma D_a66c8 : decode_any W_a66c8 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66cc : bv 32 := 0x00054603.
Lemma F_a66cc : fetch_word PSEGS (0xa66cc : word) = Some W_a66cc.
Proof. vm_refl. Qed.
Lemma D_a66cc : decode_any W_a66cc = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66d0 : bv 32 := 0x00b60a63.
Lemma F_a66d0 : fetch_word PSEGS (0xa66d0 : word) = Some W_a66d0.
Proof. vm_refl. Qed.
Lemma D_a66d0 : decode_any W_a66d0 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66d4 : bv 32 := 0xfff68693.
Lemma F_a66d4 : fetch_word PSEGS (0xa66d4 : word) = Some W_a66d4.
Proof. vm_refl. Qed.
Lemma D_a66d4 : decode_any W_a66d4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66d8 : bv 32 := 0x00150513.
Lemma F_a66d8 : fetch_word PSEGS (0xa66d8 : word) = Some W_a66d8.
Proof. vm_refl. Qed.
Lemma D_a66d8 : decode_any W_a66d8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66dc : bv 32 := 0xfe0698e3.
Lemma F_a66dc : fetch_word PSEGS (0xa66dc : word) = Some W_a66dc.
Proof. vm_refl. Qed.
Lemma D_a66dc : decode_any W_a66dc = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66e4 : bv 32 := 0x00008067.
Lemma F_a66e4 : fetch_word PSEGS (0xa66e4 : word) = Some W_a66e4.
Proof. vm_refl. Qed.
Lemma D_a66e4 : decode_any W_a66e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66e8 : bv 32 := 0x00060693.
Lemma F_a66e8 : fetch_word PSEGS (0xa66e8 : word) = Some W_a66e8.
Proof. vm_refl. Qed.
Lemma D_a66e8 : decode_any W_a66e8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66ec : bv 32 := 0x00054603.
Lemma F_a66ec : fetch_word PSEGS (0xa66ec : word) = Some W_a66ec.
Proof. vm_refl. Qed.
Lemma D_a66ec : decode_any W_a66ec = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66f0 : bv 32 := 0xfeb612e3.
Lemma F_a66f0 : fetch_word PSEGS (0xa66f0 : word) = Some W_a66f0.
Proof. vm_refl. Qed.
Lemma D_a66f0 : decode_any W_a66f0 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a66f4 : bv 32 := 0xff1ff06f.
Lemma F_a66f4 : fetch_word PSEGS (0xa66f4 : word) = Some W_a66f4.
Proof. vm_refl. Qed.
Lemma D_a66f4 : decode_any W_a66f4 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6728 : bv 32 := 0x0035f693.
Lemma F_a6728 : fetch_word PSEGS (0xa6728 : word) = Some W_a6728.
Proof. vm_refl. Qed.
Lemma D_a6728 : decode_any W_a6728 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a672c : bv 32 := 0x10068863.
Lemma F_a672c : fetch_word PSEGS (0xa672c : word) = Some W_a672c.
Proof. vm_refl. Qed.
Lemma D_a672c : decode_any W_a672c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6730 : bv 32 := 0x02060e63.
Lemma F_a6730 : fetch_word PSEGS (0xa6730 : word) = Some W_a6730.
Proof. vm_refl. Qed.
Lemma D_a6730 : decode_any W_a6730 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6734 : bv 32 := 0x00158713.
Lemma F_a6734 : fetch_word PSEGS (0xa6734 : word) = Some W_a6734.
Proof. vm_refl. Qed.
Lemma D_a6734 : decode_any W_a6734 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6738 : bv 32 := 0x00100793.
Lemma F_a6738 : fetch_word PSEGS (0xa6738 : word) = Some W_a6738.
Proof. vm_refl. Qed.
Lemma D_a6738 : decode_any W_a6738 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a673c : bv 32 := 0x00050693.
Lemma F_a673c : fetch_word PSEGS (0xa673c : word) = Some W_a673c.
Proof. vm_refl. Qed.
Lemma D_a673c : decode_any W_a673c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6740 : bv 32 := 0x0005c883.
Lemma F_a6740 : fetch_word PSEGS (0xa6740 : word) = Some W_a6740.
Proof. vm_refl. Qed.
Lemma D_a6740 : decode_any W_a6740 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6744 : bv 32 := 0x00060813.
Lemma F_a6744 : fetch_word PSEGS (0xa6744 : word) = Some W_a6744.
Proof. vm_refl. Qed.
Lemma D_a6744 : decode_any W_a6744 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6748 : bv 32 := 0x00158593.
Lemma F_a6748 : fetch_word PSEGS (0xa6748 : word) = Some W_a6748.
Proof. vm_refl. Qed.
Lemma D_a6748 : decode_any W_a6748 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a674c : bv 32 := 0x00377293.
Lemma F_a674c : fetch_word PSEGS (0xa674c : word) = Some W_a674c.
Proof. vm_refl. Qed.
Lemma D_a674c : decode_any W_a674c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6750 : bv 32 := 0x01168023.
Lemma F_a6750 : fetch_word PSEGS (0xa6750 : word) = Some W_a6750.
Proof. vm_refl. Qed.
Lemma D_a6750 : decode_any W_a6750 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6754 : bv 32 := 0x00168693.
Lemma F_a6754 : fetch_word PSEGS (0xa6754 : word) = Some W_a6754.
Proof. vm_refl. Qed.
Lemma D_a6754 : decode_any W_a6754 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6758 : bv 32 := 0xfff60613.
Lemma F_a6758 : fetch_word PSEGS (0xa6758 : word) = Some W_a6758.
Proof. vm_refl. Qed.
Lemma D_a6758 : decode_any W_a6758 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a675c : bv 32 := 0x00028a63.
Lemma F_a675c : fetch_word PSEGS (0xa675c : word) = Some W_a675c.
Proof. vm_refl. Qed.
Lemma D_a675c : decode_any W_a675c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6760 : bv 32 := 0x00170713.
Lemma F_a6760 : fetch_word PSEGS (0xa6760 : word) = Some W_a6760.
Proof. vm_refl. Qed.
Lemma D_a6760 : decode_any W_a6760 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6764 : bv 32 := 0xfcf81ee3.
Lemma F_a6764 : fetch_word PSEGS (0xa6764 : word) = Some W_a6764.
Proof. vm_refl. Qed.
Lemma D_a6764 : decode_any W_a6764 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6768 : bv 32 := 0x0080006f.
Lemma F_a6768 : fetch_word PSEGS (0xa6768 : word) = Some W_a6768.
Proof. vm_refl. Qed.
Lemma D_a6768 : decode_any W_a6768 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a676c : bv 32 := 0x00050693.
Lemma F_a676c : fetch_word PSEGS (0xa676c : word) = Some W_a676c.
Proof. vm_refl. Qed.
Lemma D_a676c : decode_any W_a676c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6770 : bv 32 := 0x0036f793.
Lemma F_a6770 : fetch_word PSEGS (0xa6770 : word) = Some W_a6770.
Proof. vm_refl. Qed.
Lemma D_a6770 : decode_any W_a6770 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6774 : bv 32 := 0x0c078a63.
Lemma F_a6774 : fetch_word PSEGS (0xa6774 : word) = Some W_a6774.
Proof. vm_refl. Qed.
Lemma D_a6774 : decode_any W_a6774 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6778 : bv 32 := 0x02000713.
Lemma F_a6778 : fetch_word PSEGS (0xa6778 : word) = Some W_a6778.
Proof. vm_refl. Qed.
Lemma D_a6778 : decode_any W_a6778 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a677c : bv 32 := 0x02e67063.
Lemma F_a677c : fetch_word PSEGS (0xa677c : word) = Some W_a677c.
Proof. vm_refl. Qed.
Lemma D_a677c : decode_any W_a677c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6780 : bv 32 := 0x01000713.
Lemma F_a6780 : fetch_word PSEGS (0xa6780 : word) = Some W_a6780.
Proof. vm_refl. Qed.
Lemma D_a6780 : decode_any W_a6780 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6784 : bv 32 := 0x24e67863.
Lemma F_a6784 : fetch_word PSEGS (0xa6784 : word) = Some W_a6784.
Proof. vm_refl. Qed.
Lemma D_a6784 : decode_any W_a6784 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6788 : bv 32 := 0x00867713.
Lemma F_a6788 : fetch_word PSEGS (0xa6788 : word) = Some W_a6788.
Proof. vm_refl. Qed.
Lemma D_a6788 : decode_any W_a6788 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a678c : bv 32 := 0x2c071e63.
Lemma F_a678c : fetch_word PSEGS (0xa678c : word) = Some W_a678c.
Proof. vm_refl. Qed.
Lemma D_a678c : decode_any W_a678c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6790 : bv 32 := 0x00467713.
Lemma F_a6790 : fetch_word PSEGS (0xa6790 : word) = Some W_a6790.
Proof. vm_refl. Qed.
Lemma D_a6790 : decode_any W_a6790 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6794 : bv 32 := 0x32071463.
Lemma F_a6794 : fetch_word PSEGS (0xa6794 : word) = Some W_a6794.
Proof. vm_refl. Qed.
Lemma D_a6794 : decode_any W_a6794 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6798 : bv 32 := 0x3500006f.
Lemma F_a6798 : fetch_word PSEGS (0xa6798 : word) = Some W_a6798.
Proof. vm_refl. Qed.
Lemma D_a6798 : decode_any W_a6798 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a679c : bv 32 := 0x0005a703.
Lemma F_a679c : fetch_word PSEGS (0xa679c : word) = Some W_a679c.
Proof. vm_refl. Qed.
Lemma D_a679c : decode_any W_a679c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67a0 : bv 32 := 0x00300813.
Lemma F_a67a0 : fetch_word PSEGS (0xa67a0 : word) = Some W_a67a0.
Proof. vm_refl. Qed.
Lemma D_a67a0 : decode_any W_a67a0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67a4 : bv 32 := 0x11078e63.
Lemma F_a67a4 : fetch_word PSEGS (0xa67a4 : word) = Some W_a67a4.
Proof. vm_refl. Qed.
Lemma D_a67a4 : decode_any W_a67a4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67a8 : bv 32 := 0x00200813.
Lemma F_a67a8 : fetch_word PSEGS (0xa67a8 : word) = Some W_a67a8.
Proof. vm_refl. Qed.
Lemma D_a67a8 : decode_any W_a67a8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67ac : bv 32 := 0x19079c63.
Lemma F_a67ac : fetch_word PSEGS (0xa67ac : word) = Some W_a67ac.
Proof. vm_refl. Qed.
Lemma D_a67ac : decode_any W_a67ac = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67b0 : bv 32 := 0x00875793.
Lemma F_a67b0 : fetch_word PSEGS (0xa67b0 : word) = Some W_a67b0.
Proof. vm_refl. Qed.
Lemma D_a67b0 : decode_any W_a67b0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67b4 : bv 32 := 0xffe60613.
Lemma F_a67b4 : fetch_word PSEGS (0xa67b4 : word) = Some W_a67b4.
Proof. vm_refl. Qed.
Lemma D_a67b4 : decode_any W_a67b4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67b8 : bv 32 := 0x00e68023.
Lemma F_a67b8 : fetch_word PSEGS (0xa67b8 : word) = Some W_a67b8.
Proof. vm_refl. Qed.
Lemma D_a67b8 : decode_any W_a67b8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67bc : bv 32 := 0x00f680a3.
Lemma F_a67bc : fetch_word PSEGS (0xa67bc : word) = Some W_a67bc.
Proof. vm_refl. Qed.
Lemma D_a67bc : decode_any W_a67bc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67c0 : bv 32 := 0x00268693.
Lemma F_a67c0 : fetch_word PSEGS (0xa67c0 : word) = Some W_a67c0.
Proof. vm_refl. Qed.
Lemma D_a67c0 : decode_any W_a67c0 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67c4 : bv 32 := 0x01058593.
Lemma F_a67c4 : fetch_word PSEGS (0xa67c4 : word) = Some W_a67c4.
Proof. vm_refl. Qed.
Lemma D_a67c4 : decode_any W_a67c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67c8 : bv 32 := 0x01100793.
Lemma F_a67c8 : fetch_word PSEGS (0xa67c8 : word) = Some W_a67c8.
Proof. vm_refl. Qed.
Lemma D_a67c8 : decode_any W_a67c8 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67cc : bv 32 := 0x0107581b.
Lemma F_a67cc : fetch_word PSEGS (0xa67cc : word) = Some W_a67cc.
Proof. vm_refl. Qed.
Lemma D_a67cc : decode_any W_a67cc = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67d0 : bv 32 := 0xff45a883.
Lemma F_a67d0 : fetch_word PSEGS (0xa67d0 : word) = Some W_a67d0.
Proof. vm_refl. Qed.
Lemma D_a67d0 : decode_any W_a67d0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67d4 : bv 32 := 0xff85a283.
Lemma F_a67d4 : fetch_word PSEGS (0xa67d4 : word) = Some W_a67d4.
Proof. vm_refl. Qed.
Lemma D_a67d4 : decode_any W_a67d4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67d8 : bv 32 := 0xffc5a303.
Lemma F_a67d8 : fetch_word PSEGS (0xa67d8 : word) = Some W_a67d8.
Proof. vm_refl. Qed.
Lemma D_a67d8 : decode_any W_a67d8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67dc : bv 32 := 0x0005a703.
Lemma F_a67dc : fetch_word PSEGS (0xa67dc : word) = Some W_a67dc.
Proof. vm_refl. Qed.
Lemma D_a67dc : decode_any W_a67dc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67e0 : bv 32 := 0x01089393.
Lemma F_a67e0 : fetch_word PSEGS (0xa67e0 : word) = Some W_a67e0.
Proof. vm_refl. Qed.
Lemma D_a67e0 : decode_any W_a67e0 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67e4 : bv 32 := 0x0108d89b.
Lemma F_a67e4 : fetch_word PSEGS (0xa67e4 : word) = Some W_a67e4.
Proof. vm_refl. Qed.
Lemma D_a67e4 : decode_any W_a67e4 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67e8 : bv 32 := 0x0103e833.
Lemma F_a67e8 : fetch_word PSEGS (0xa67e8 : word) = Some W_a67e8.
Proof. vm_refl. Qed.
Lemma D_a67e8 : decode_any W_a67e8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67ec : bv 32 := 0x01029393.
Lemma F_a67ec : fetch_word PSEGS (0xa67ec : word) = Some W_a67ec.
Proof. vm_refl. Qed.
Lemma D_a67ec : decode_any W_a67ec = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67f0 : bv 32 := 0x0102d29b.
Lemma F_a67f0 : fetch_word PSEGS (0xa67f0 : word) = Some W_a67f0.
Proof. vm_refl. Qed.
Lemma D_a67f0 : decode_any W_a67f0 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67f4 : bv 32 := 0x0113e8b3.
Lemma F_a67f4 : fetch_word PSEGS (0xa67f4 : word) = Some W_a67f4.
Proof. vm_refl. Qed.
Lemma D_a67f4 : decode_any W_a67f4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67f8 : bv 32 := 0x01031393.
Lemma F_a67f8 : fetch_word PSEGS (0xa67f8 : word) = Some W_a67f8.
Proof. vm_refl. Qed.
Lemma D_a67f8 : decode_any W_a67f8 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a67fc : bv 32 := 0x0103531b.
Lemma F_a67fc : fetch_word PSEGS (0xa67fc : word) = Some W_a67fc.
Proof. vm_refl. Qed.
Lemma D_a67fc : decode_any W_a67fc = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6800 : bv 32 := 0x0053e2b3.
Lemma F_a6800 : fetch_word PSEGS (0xa6800 : word) = Some W_a6800.
Proof. vm_refl. Qed.
Lemma D_a6800 : decode_any W_a6800 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6804 : bv 32 := 0x01071393.
Lemma F_a6804 : fetch_word PSEGS (0xa6804 : word) = Some W_a6804.
Proof. vm_refl. Qed.
Lemma D_a6804 : decode_any W_a6804 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6808 : bv 32 := 0x0063e333.
Lemma F_a6808 : fetch_word PSEGS (0xa6808 : word) = Some W_a6808.
Proof. vm_refl. Qed.
Lemma D_a6808 : decode_any W_a6808 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a680c : bv 32 := 0xff060613.
Lemma F_a680c : fetch_word PSEGS (0xa680c : word) = Some W_a680c.
Proof. vm_refl. Qed.
Lemma D_a680c : decode_any W_a680c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6810 : bv 32 := 0x0106a023.
Lemma F_a6810 : fetch_word PSEGS (0xa6810 : word) = Some W_a6810.
Proof. vm_refl. Qed.
Lemma D_a6810 : decode_any W_a6810 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6814 : bv 32 := 0x0116a223.
Lemma F_a6814 : fetch_word PSEGS (0xa6814 : word) = Some W_a6814.
Proof. vm_refl. Qed.
Lemma D_a6814 : decode_any W_a6814 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6818 : bv 32 := 0x0056a423.
Lemma F_a6818 : fetch_word PSEGS (0xa6818 : word) = Some W_a6818.
Proof. vm_refl. Qed.
Lemma D_a6818 : decode_any W_a6818 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a681c : bv 32 := 0x0066a623.
Lemma F_a681c : fetch_word PSEGS (0xa681c : word) = Some W_a681c.
Proof. vm_refl. Qed.
Lemma D_a681c : decode_any W_a681c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6820 : bv 32 := 0x01068693.
Lemma F_a6820 : fetch_word PSEGS (0xa6820 : word) = Some W_a6820.
Proof. vm_refl. Qed.
Lemma D_a6820 : decode_any W_a6820 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6824 : bv 32 := 0x01058593.
Lemma F_a6824 : fetch_word PSEGS (0xa6824 : word) = Some W_a6824.
Proof. vm_refl. Qed.
Lemma D_a6824 : decode_any W_a6824 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6828 : bv 32 := 0xfac7e2e3.
Lemma F_a6828 : fetch_word PSEGS (0xa6828 : word) = Some W_a6828.
Proof. vm_refl. Qed.
Lemma D_a6828 : decode_any W_a6828 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a682c : bv 32 := 0xff258593.
Lemma F_a682c : fetch_word PSEGS (0xa682c : word) = Some W_a682c.
Proof. vm_refl. Qed.
Lemma D_a682c : decode_any W_a682c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6830 : bv 32 := 0x01000713.
Lemma F_a6830 : fetch_word PSEGS (0xa6830 : word) = Some W_a6830.
Proof. vm_refl. Qed.
Lemma D_a6830 : decode_any W_a6830 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6834 : bv 32 := 0xf4e66ae3.
Lemma F_a6834 : fetch_word PSEGS (0xa6834 : word) = Some W_a6834.
Proof. vm_refl. Qed.
Lemma D_a6834 : decode_any W_a6834 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6838 : bv 32 := 0x19c0006f.
Lemma F_a6838 : fetch_word PSEGS (0xa6838 : word) = Some W_a6838.
Proof. vm_refl. Qed.
Lemma D_a6838 : decode_any W_a6838 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a683c : bv 32 := 0x00050693.
Lemma F_a683c : fetch_word PSEGS (0xa683c : word) = Some W_a683c.
Proof. vm_refl. Qed.
Lemma D_a683c : decode_any W_a683c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6840 : bv 32 := 0x00357793.
Lemma F_a6840 : fetch_word PSEGS (0xa6840 : word) = Some W_a6840.
Proof. vm_refl. Qed.
Lemma D_a6840 : decode_any W_a6840 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6844 : bv 32 := 0xf2079ae3.
Lemma F_a6844 : fetch_word PSEGS (0xa6844 : word) = Some W_a6844.
Proof. vm_refl. Qed.
Lemma D_a6844 : decode_any W_a6844 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6848 : bv 32 := 0x01000713.
Lemma F_a6848 : fetch_word PSEGS (0xa6848 : word) = Some W_a6848.
Proof. vm_refl. Qed.
Lemma D_a6848 : decode_any W_a6848 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a684c : bv 32 := 0x02e66c63.
Lemma F_a684c : fetch_word PSEGS (0xa684c : word) = Some W_a684c.
Proof. vm_refl. Qed.
Lemma D_a684c : decode_any W_a684c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6850 : bv 32 := 0x00f00713.
Lemma F_a6850 : fetch_word PSEGS (0xa6850 : word) = Some W_a6850.
Proof. vm_refl. Qed.
Lemma D_a6850 : decode_any W_a6850 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6854 : bv 32 := 0x0005a783.
Lemma F_a6854 : fetch_word PSEGS (0xa6854 : word) = Some W_a6854.
Proof. vm_refl. Qed.
Lemma D_a6854 : decode_any W_a6854 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6858 : bv 32 := 0x0045a803.
Lemma F_a6858 : fetch_word PSEGS (0xa6858 : word) = Some W_a6858.
Proof. vm_refl. Qed.
Lemma D_a6858 : decode_any W_a6858 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a685c : bv 32 := 0x0085a883.
Lemma F_a685c : fetch_word PSEGS (0xa685c : word) = Some W_a685c.
Proof. vm_refl. Qed.
Lemma D_a685c : decode_any W_a685c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6860 : bv 32 := 0x00c5a283.
Lemma F_a6860 : fetch_word PSEGS (0xa6860 : word) = Some W_a6860.
Proof. vm_refl. Qed.
Lemma D_a6860 : decode_any W_a6860 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6864 : bv 32 := 0x01058593.
Lemma F_a6864 : fetch_word PSEGS (0xa6864 : word) = Some W_a6864.
Proof. vm_refl. Qed.
Lemma D_a6864 : decode_any W_a6864 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6868 : bv 32 := 0xff060613.
Lemma F_a6868 : fetch_word PSEGS (0xa6868 : word) = Some W_a6868.
Proof. vm_refl. Qed.
Lemma D_a6868 : decode_any W_a6868 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a686c : bv 32 := 0x00f6a023.
Lemma F_a686c : fetch_word PSEGS (0xa686c : word) = Some W_a686c.
Proof. vm_refl. Qed.
Lemma D_a686c : decode_any W_a686c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6870 : bv 32 := 0x0106a223.
Lemma F_a6870 : fetch_word PSEGS (0xa6870 : word) = Some W_a6870.
Proof. vm_refl. Qed.
Lemma D_a6870 : decode_any W_a6870 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6874 : bv 32 := 0x0116a423.
Lemma F_a6874 : fetch_word PSEGS (0xa6874 : word) = Some W_a6874.
Proof. vm_refl. Qed.
Lemma D_a6874 : decode_any W_a6874 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6878 : bv 32 := 0x0056a623.
Lemma F_a6878 : fetch_word PSEGS (0xa6878 : word) = Some W_a6878.
Proof. vm_refl. Qed.
Lemma D_a6878 : decode_any W_a6878 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a687c : bv 32 := 0x01068693.
Lemma F_a687c : fetch_word PSEGS (0xa687c : word) = Some W_a687c.
Proof. vm_refl. Qed.
Lemma D_a687c : decode_any W_a687c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6880 : bv 32 := 0xfcc76ae3.
Lemma F_a6880 : fetch_word PSEGS (0xa6880 : word) = Some W_a6880.
Proof. vm_refl. Qed.
Lemma D_a6880 : decode_any W_a6880 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6884 : bv 32 := 0x00800713.
Lemma F_a6884 : fetch_word PSEGS (0xa6884 : word) = Some W_a6884.
Proof. vm_refl. Qed.
Lemma D_a6884 : decode_any W_a6884 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6888 : bv 32 := 0x00e66e63.
Lemma F_a6888 : fetch_word PSEGS (0xa6888 : word) = Some W_a6888.
Proof. vm_refl. Qed.
Lemma D_a6888 : decode_any W_a6888 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a688c : bv 32 := 0x0005a703.
Lemma F_a688c : fetch_word PSEGS (0xa688c : word) = Some W_a688c.
Proof. vm_refl. Qed.
Lemma D_a688c : decode_any W_a688c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6890 : bv 32 := 0x0045a783.
Lemma F_a6890 : fetch_word PSEGS (0xa6890 : word) = Some W_a6890.
Proof. vm_refl. Qed.
Lemma D_a6890 : decode_any W_a6890 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6894 : bv 32 := 0x00e6a023.
Lemma F_a6894 : fetch_word PSEGS (0xa6894 : word) = Some W_a6894.
Proof. vm_refl. Qed.
Lemma D_a6894 : decode_any W_a6894 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6898 : bv 32 := 0x00f6a223.
Lemma F_a6898 : fetch_word PSEGS (0xa6898 : word) = Some W_a6898.
Proof. vm_refl. Qed.
Lemma D_a6898 : decode_any W_a6898 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a689c : bv 32 := 0x00868693.
Lemma F_a689c : fetch_word PSEGS (0xa689c : word) = Some W_a689c.
Proof. vm_refl. Qed.
Lemma D_a689c : decode_any W_a689c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68a0 : bv 32 := 0x00858593.
Lemma F_a68a0 : fetch_word PSEGS (0xa68a0 : word) = Some W_a68a0.
Proof. vm_refl. Qed.
Lemma D_a68a0 : decode_any W_a68a0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68a4 : bv 32 := 0x00467713.
Lemma F_a68a4 : fetch_word PSEGS (0xa68a4 : word) = Some W_a68a4.
Proof. vm_refl. Qed.
Lemma D_a68a4 : decode_any W_a68a4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68a8 : bv 32 := 0x24070063.
Lemma F_a68a8 : fetch_word PSEGS (0xa68a8 : word) = Some W_a68a8.
Proof. vm_refl. Qed.
Lemma D_a68a8 : decode_any W_a68a8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68ac : bv 32 := 0x0005a703.
Lemma F_a68ac : fetch_word PSEGS (0xa68ac : word) = Some W_a68ac.
Proof. vm_refl. Qed.
Lemma D_a68ac : decode_any W_a68ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68b0 : bv 32 := 0x00458593.
Lemma F_a68b0 : fetch_word PSEGS (0xa68b0 : word) = Some W_a68b0.
Proof. vm_refl. Qed.
Lemma D_a68b0 : decode_any W_a68b0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68b4 : bv 32 := 0x00e6a023.
Lemma F_a68b4 : fetch_word PSEGS (0xa68b4 : word) = Some W_a68b4.
Proof. vm_refl. Qed.
Lemma D_a68b4 : decode_any W_a68b4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68b8 : bv 32 := 0x00468693.
Lemma F_a68b8 : fetch_word PSEGS (0xa68b8 : word) = Some W_a68b8.
Proof. vm_refl. Qed.
Lemma D_a68b8 : decode_any W_a68b8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68bc : bv 32 := 0x22c0006f.
Lemma F_a68bc : fetch_word PSEGS (0xa68bc : word) = Some W_a68bc.
Proof. vm_refl. Qed.
Lemma D_a68bc : decode_any W_a68bc = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68c0 : bv 32 := 0x00e68023.
Lemma F_a68c0 : fetch_word PSEGS (0xa68c0 : word) = Some W_a68c0.
Proof. vm_refl. Qed.
Lemma D_a68c0 : decode_any W_a68c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68c4 : bv 32 := 0x00168693.
Lemma F_a68c4 : fetch_word PSEGS (0xa68c4 : word) = Some W_a68c4.
Proof. vm_refl. Qed.
Lemma D_a68c4 : decode_any W_a68c4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68c8 : bv 32 := 0xfff60613.
Lemma F_a68c8 : fetch_word PSEGS (0xa68c8 : word) = Some W_a68c8.
Proof. vm_refl. Qed.
Lemma D_a68c8 : decode_any W_a68c8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68cc : bv 32 := 0x01058593.
Lemma F_a68cc : fetch_word PSEGS (0xa68cc : word) = Some W_a68cc.
Proof. vm_refl. Qed.
Lemma D_a68cc : decode_any W_a68cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68d0 : bv 32 := 0x01200793.
Lemma F_a68d0 : fetch_word PSEGS (0xa68d0 : word) = Some W_a68d0.
Proof. vm_refl. Qed.
Lemma D_a68d0 : decode_any W_a68d0 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68d4 : bv 32 := 0x0087581b.
Lemma F_a68d4 : fetch_word PSEGS (0xa68d4 : word) = Some W_a68d4.
Proof. vm_refl. Qed.
Lemma D_a68d4 : decode_any W_a68d4 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68d8 : bv 32 := 0xff45a883.
Lemma F_a68d8 : fetch_word PSEGS (0xa68d8 : word) = Some W_a68d8.
Proof. vm_refl. Qed.
Lemma D_a68d8 : decode_any W_a68d8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68dc : bv 32 := 0xff85a283.
Lemma F_a68dc : fetch_word PSEGS (0xa68dc : word) = Some W_a68dc.
Proof. vm_refl. Qed.
Lemma D_a68dc : decode_any W_a68dc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68e0 : bv 32 := 0xffc5a303.
Lemma F_a68e0 : fetch_word PSEGS (0xa68e0 : word) = Some W_a68e0.
Proof. vm_refl. Qed.
Lemma D_a68e0 : decode_any W_a68e0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68e4 : bv 32 := 0x0005a703.
Lemma F_a68e4 : fetch_word PSEGS (0xa68e4 : word) = Some W_a68e4.
Proof. vm_refl. Qed.
Lemma D_a68e4 : decode_any W_a68e4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68e8 : bv 32 := 0x01889393.
Lemma F_a68e8 : fetch_word PSEGS (0xa68e8 : word) = Some W_a68e8.
Proof. vm_refl. Qed.
Lemma D_a68e8 : decode_any W_a68e8 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68ec : bv 32 := 0x0088d89b.
Lemma F_a68ec : fetch_word PSEGS (0xa68ec : word) = Some W_a68ec.
Proof. vm_refl. Qed.
Lemma D_a68ec : decode_any W_a68ec = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68f0 : bv 32 := 0x0103e833.
Lemma F_a68f0 : fetch_word PSEGS (0xa68f0 : word) = Some W_a68f0.
Proof. vm_refl. Qed.
Lemma D_a68f0 : decode_any W_a68f0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68f4 : bv 32 := 0x01829393.
Lemma F_a68f4 : fetch_word PSEGS (0xa68f4 : word) = Some W_a68f4.
Proof. vm_refl. Qed.
Lemma D_a68f4 : decode_any W_a68f4 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68f8 : bv 32 := 0x0082d29b.
Lemma F_a68f8 : fetch_word PSEGS (0xa68f8 : word) = Some W_a68f8.
Proof. vm_refl. Qed.
Lemma D_a68f8 : decode_any W_a68f8 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a68fc : bv 32 := 0x0113e8b3.
Lemma F_a68fc : fetch_word PSEGS (0xa68fc : word) = Some W_a68fc.
Proof. vm_refl. Qed.
Lemma D_a68fc : decode_any W_a68fc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6900 : bv 32 := 0x01831393.
Lemma F_a6900 : fetch_word PSEGS (0xa6900 : word) = Some W_a6900.
Proof. vm_refl. Qed.
Lemma D_a6900 : decode_any W_a6900 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6904 : bv 32 := 0x0083531b.
Lemma F_a6904 : fetch_word PSEGS (0xa6904 : word) = Some W_a6904.
Proof. vm_refl. Qed.
Lemma D_a6904 : decode_any W_a6904 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6908 : bv 32 := 0x0053e2b3.
Lemma F_a6908 : fetch_word PSEGS (0xa6908 : word) = Some W_a6908.
Proof. vm_refl. Qed.
Lemma D_a6908 : decode_any W_a6908 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a690c : bv 32 := 0x01871393.
Lemma F_a690c : fetch_word PSEGS (0xa690c : word) = Some W_a690c.
Proof. vm_refl. Qed.
Lemma D_a690c : decode_any W_a690c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6910 : bv 32 := 0x0063e333.
Lemma F_a6910 : fetch_word PSEGS (0xa6910 : word) = Some W_a6910.
Proof. vm_refl. Qed.
Lemma D_a6910 : decode_any W_a6910 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6914 : bv 32 := 0xff060613.
Lemma F_a6914 : fetch_word PSEGS (0xa6914 : word) = Some W_a6914.
Proof. vm_refl. Qed.
Lemma D_a6914 : decode_any W_a6914 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6918 : bv 32 := 0x0106a023.
Lemma F_a6918 : fetch_word PSEGS (0xa6918 : word) = Some W_a6918.
Proof. vm_refl. Qed.
Lemma D_a6918 : decode_any W_a6918 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a691c : bv 32 := 0x0116a223.
Lemma F_a691c : fetch_word PSEGS (0xa691c : word) = Some W_a691c.
Proof. vm_refl. Qed.
Lemma D_a691c : decode_any W_a691c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6920 : bv 32 := 0x0056a423.
Lemma F_a6920 : fetch_word PSEGS (0xa6920 : word) = Some W_a6920.
Proof. vm_refl. Qed.
Lemma D_a6920 : decode_any W_a6920 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6924 : bv 32 := 0x0066a623.
Lemma F_a6924 : fetch_word PSEGS (0xa6924 : word) = Some W_a6924.
Proof. vm_refl. Qed.
Lemma D_a6924 : decode_any W_a6924 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6928 : bv 32 := 0x01068693.
Lemma F_a6928 : fetch_word PSEGS (0xa6928 : word) = Some W_a6928.
Proof. vm_refl. Qed.
Lemma D_a6928 : decode_any W_a6928 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a692c : bv 32 := 0x01058593.
Lemma F_a692c : fetch_word PSEGS (0xa692c : word) = Some W_a692c.
Proof. vm_refl. Qed.
Lemma D_a692c : decode_any W_a692c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6930 : bv 32 := 0xfac7e2e3.
Lemma F_a6930 : fetch_word PSEGS (0xa6930 : word) = Some W_a6930.
Proof. vm_refl. Qed.
Lemma D_a6930 : decode_any W_a6930 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6934 : bv 32 := 0xff158593.
Lemma F_a6934 : fetch_word PSEGS (0xa6934 : word) = Some W_a6934.
Proof. vm_refl. Qed.
Lemma D_a6934 : decode_any W_a6934 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6938 : bv 32 := 0x01000713.
Lemma F_a6938 : fetch_word PSEGS (0xa6938 : word) = Some W_a6938.
Proof. vm_refl. Qed.
Lemma D_a6938 : decode_any W_a6938 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a693c : bv 32 := 0xe4e666e3.
Lemma F_a693c : fetch_word PSEGS (0xa693c : word) = Some W_a693c.
Proof. vm_refl. Qed.
Lemma D_a693c : decode_any W_a693c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6940 : bv 32 := 0x0940006f.
Lemma F_a6940 : fetch_word PSEGS (0xa6940 : word) = Some W_a6940.
Proof. vm_refl. Qed.
Lemma D_a6940 : decode_any W_a6940 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6944 : bv 32 := 0x00875793.
Lemma F_a6944 : fetch_word PSEGS (0xa6944 : word) = Some W_a6944.
Proof. vm_refl. Qed.
Lemma D_a6944 : decode_any W_a6944 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6948 : bv 32 := 0x01075813.
Lemma F_a6948 : fetch_word PSEGS (0xa6948 : word) = Some W_a6948.
Proof. vm_refl. Qed.
Lemma D_a6948 : decode_any W_a6948 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a694c : bv 32 := 0xffd60613.
Lemma F_a694c : fetch_word PSEGS (0xa694c : word) = Some W_a694c.
Proof. vm_refl. Qed.
Lemma D_a694c : decode_any W_a694c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6950 : bv 32 := 0x00e68023.
Lemma F_a6950 : fetch_word PSEGS (0xa6950 : word) = Some W_a6950.
Proof. vm_refl. Qed.
Lemma D_a6950 : decode_any W_a6950 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6954 : bv 32 := 0x00f680a3.
Lemma F_a6954 : fetch_word PSEGS (0xa6954 : word) = Some W_a6954.
Proof. vm_refl. Qed.
Lemma D_a6954 : decode_any W_a6954 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6958 : bv 32 := 0x01068123.
Lemma F_a6958 : fetch_word PSEGS (0xa6958 : word) = Some W_a6958.
Proof. vm_refl. Qed.
Lemma D_a6958 : decode_any W_a6958 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a695c : bv 32 := 0x00368693.
Lemma F_a695c : fetch_word PSEGS (0xa695c : word) = Some W_a695c.
Proof. vm_refl. Qed.
Lemma D_a695c : decode_any W_a695c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6960 : bv 32 := 0x01058593.
Lemma F_a6960 : fetch_word PSEGS (0xa6960 : word) = Some W_a6960.
Proof. vm_refl. Qed.
Lemma D_a6960 : decode_any W_a6960 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6964 : bv 32 := 0x01000793.
Lemma F_a6964 : fetch_word PSEGS (0xa6964 : word) = Some W_a6964.
Proof. vm_refl. Qed.
Lemma D_a6964 : decode_any W_a6964 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6968 : bv 32 := 0x0187581b.
Lemma F_a6968 : fetch_word PSEGS (0xa6968 : word) = Some W_a6968.
Proof. vm_refl. Qed.
Lemma D_a6968 : decode_any W_a6968 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a696c : bv 32 := 0xff45a883.
Lemma F_a696c : fetch_word PSEGS (0xa696c : word) = Some W_a696c.
Proof. vm_refl. Qed.
Lemma D_a696c : decode_any W_a696c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6970 : bv 32 := 0xff85a283.
Lemma F_a6970 : fetch_word PSEGS (0xa6970 : word) = Some W_a6970.
Proof. vm_refl. Qed.
Lemma D_a6970 : decode_any W_a6970 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6974 : bv 32 := 0xffc5a303.
Lemma F_a6974 : fetch_word PSEGS (0xa6974 : word) = Some W_a6974.
Proof. vm_refl. Qed.
Lemma D_a6974 : decode_any W_a6974 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6978 : bv 32 := 0x0005a703.
Lemma F_a6978 : fetch_word PSEGS (0xa6978 : word) = Some W_a6978.
Proof. vm_refl. Qed.
Lemma D_a6978 : decode_any W_a6978 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a697c : bv 32 := 0x00889393.
Lemma F_a697c : fetch_word PSEGS (0xa697c : word) = Some W_a697c.
Proof. vm_refl. Qed.
Lemma D_a697c : decode_any W_a697c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6980 : bv 32 := 0x0188d89b.
Lemma F_a6980 : fetch_word PSEGS (0xa6980 : word) = Some W_a6980.
Proof. vm_refl. Qed.
Lemma D_a6980 : decode_any W_a6980 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6984 : bv 32 := 0x0103e833.
Lemma F_a6984 : fetch_word PSEGS (0xa6984 : word) = Some W_a6984.
Proof. vm_refl. Qed.
Lemma D_a6984 : decode_any W_a6984 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6988 : bv 32 := 0x00829393.
Lemma F_a6988 : fetch_word PSEGS (0xa6988 : word) = Some W_a6988.
Proof. vm_refl. Qed.
Lemma D_a6988 : decode_any W_a6988 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a698c : bv 32 := 0x0182d29b.
Lemma F_a698c : fetch_word PSEGS (0xa698c : word) = Some W_a698c.
Proof. vm_refl. Qed.
Lemma D_a698c : decode_any W_a698c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6990 : bv 32 := 0x0113e8b3.
Lemma F_a6990 : fetch_word PSEGS (0xa6990 : word) = Some W_a6990.
Proof. vm_refl. Qed.
Lemma D_a6990 : decode_any W_a6990 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6994 : bv 32 := 0x00831393.
Lemma F_a6994 : fetch_word PSEGS (0xa6994 : word) = Some W_a6994.
Proof. vm_refl. Qed.
Lemma D_a6994 : decode_any W_a6994 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6998 : bv 32 := 0x0183531b.
Lemma F_a6998 : fetch_word PSEGS (0xa6998 : word) = Some W_a6998.
Proof. vm_refl. Qed.
Lemma D_a6998 : decode_any W_a6998 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a699c : bv 32 := 0x0053e2b3.
Lemma F_a699c : fetch_word PSEGS (0xa699c : word) = Some W_a699c.
Proof. vm_refl. Qed.
Lemma D_a699c : decode_any W_a699c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69a0 : bv 32 := 0x00871393.
Lemma F_a69a0 : fetch_word PSEGS (0xa69a0 : word) = Some W_a69a0.
Proof. vm_refl. Qed.
Lemma D_a69a0 : decode_any W_a69a0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69a4 : bv 32 := 0x0063e333.
Lemma F_a69a4 : fetch_word PSEGS (0xa69a4 : word) = Some W_a69a4.
Proof. vm_refl. Qed.
Lemma D_a69a4 : decode_any W_a69a4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69a8 : bv 32 := 0xff060613.
Lemma F_a69a8 : fetch_word PSEGS (0xa69a8 : word) = Some W_a69a8.
Proof. vm_refl. Qed.
Lemma D_a69a8 : decode_any W_a69a8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69ac : bv 32 := 0x0106a023.
Lemma F_a69ac : fetch_word PSEGS (0xa69ac : word) = Some W_a69ac.
Proof. vm_refl. Qed.
Lemma D_a69ac : decode_any W_a69ac = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69b0 : bv 32 := 0x0116a223.
Lemma F_a69b0 : fetch_word PSEGS (0xa69b0 : word) = Some W_a69b0.
Proof. vm_refl. Qed.
Lemma D_a69b0 : decode_any W_a69b0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69b4 : bv 32 := 0x0056a423.
Lemma F_a69b4 : fetch_word PSEGS (0xa69b4 : word) = Some W_a69b4.
Proof. vm_refl. Qed.
Lemma D_a69b4 : decode_any W_a69b4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69b8 : bv 32 := 0x0066a623.
Lemma F_a69b8 : fetch_word PSEGS (0xa69b8 : word) = Some W_a69b8.
Proof. vm_refl. Qed.
Lemma D_a69b8 : decode_any W_a69b8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69bc : bv 32 := 0x01068693.
Lemma F_a69bc : fetch_word PSEGS (0xa69bc : word) = Some W_a69bc.
Proof. vm_refl. Qed.
Lemma D_a69bc : decode_any W_a69bc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69c0 : bv 32 := 0x01058593.
Lemma F_a69c0 : fetch_word PSEGS (0xa69c0 : word) = Some W_a69c0.
Proof. vm_refl. Qed.
Lemma D_a69c0 : decode_any W_a69c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69c4 : bv 32 := 0xfac7e2e3.
Lemma F_a69c4 : fetch_word PSEGS (0xa69c4 : word) = Some W_a69c4.
Proof. vm_refl. Qed.
Lemma D_a69c4 : decode_any W_a69c4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69c8 : bv 32 := 0xff358593.
Lemma F_a69c8 : fetch_word PSEGS (0xa69c8 : word) = Some W_a69c8.
Proof. vm_refl. Qed.
Lemma D_a69c8 : decode_any W_a69c8 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69cc : bv 32 := 0x01000713.
Lemma F_a69cc : fetch_word PSEGS (0xa69cc : word) = Some W_a69cc.
Proof. vm_refl. Qed.
Lemma D_a69cc : decode_any W_a69cc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69d0 : bv 32 := 0xdae66ce3.
Lemma F_a69d0 : fetch_word PSEGS (0xa69d0 : word) = Some W_a69d0.
Proof. vm_refl. Qed.
Lemma D_a69d0 : decode_any W_a69d0 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69d4 : bv 32 := 0x0005c703.
Lemma F_a69d4 : fetch_word PSEGS (0xa69d4 : word) = Some W_a69d4.
Proof. vm_refl. Qed.
Lemma D_a69d4 : decode_any W_a69d4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69d8 : bv 32 := 0x0015c783.
Lemma F_a69d8 : fetch_word PSEGS (0xa69d8 : word) = Some W_a69d8.
Proof. vm_refl. Qed.
Lemma D_a69d8 : decode_any W_a69d8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69dc : bv 32 := 0x0025c803.
Lemma F_a69dc : fetch_word PSEGS (0xa69dc : word) = Some W_a69dc.
Proof. vm_refl. Qed.
Lemma D_a69dc : decode_any W_a69dc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69e0 : bv 32 := 0x0035c883.
Lemma F_a69e0 : fetch_word PSEGS (0xa69e0 : word) = Some W_a69e0.
Proof. vm_refl. Qed.
Lemma D_a69e0 : decode_any W_a69e0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69e4 : bv 32 := 0x0045c283.
Lemma F_a69e4 : fetch_word PSEGS (0xa69e4 : word) = Some W_a69e4.
Proof. vm_refl. Qed.
Lemma D_a69e4 : decode_any W_a69e4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69e8 : bv 32 := 0x0055c303.
Lemma F_a69e8 : fetch_word PSEGS (0xa69e8 : word) = Some W_a69e8.
Proof. vm_refl. Qed.
Lemma D_a69e8 : decode_any W_a69e8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69ec : bv 32 := 0x0065c383.
Lemma F_a69ec : fetch_word PSEGS (0xa69ec : word) = Some W_a69ec.
Proof. vm_refl. Qed.
Lemma D_a69ec : decode_any W_a69ec = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69f0 : bv 32 := 0x0075ce03.
Lemma F_a69f0 : fetch_word PSEGS (0xa69f0 : word) = Some W_a69f0.
Proof. vm_refl. Qed.
Lemma D_a69f0 : decode_any W_a69f0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69f4 : bv 32 := 0x00e68023.
Lemma F_a69f4 : fetch_word PSEGS (0xa69f4 : word) = Some W_a69f4.
Proof. vm_refl. Qed.
Lemma D_a69f4 : decode_any W_a69f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69f8 : bv 32 := 0x00f680a3.
Lemma F_a69f8 : fetch_word PSEGS (0xa69f8 : word) = Some W_a69f8.
Proof. vm_refl. Qed.
Lemma D_a69f8 : decode_any W_a69f8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a69fc : bv 32 := 0x01068123.
Lemma F_a69fc : fetch_word PSEGS (0xa69fc : word) = Some W_a69fc.
Proof. vm_refl. Qed.
Lemma D_a69fc : decode_any W_a69fc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a00 : bv 32 := 0x011681a3.
Lemma F_a6a00 : fetch_word PSEGS (0xa6a00 : word) = Some W_a6a00.
Proof. vm_refl. Qed.
Lemma D_a6a00 : decode_any W_a6a00 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a04 : bv 32 := 0x0085c703.
Lemma F_a6a04 : fetch_word PSEGS (0xa6a04 : word) = Some W_a6a04.
Proof. vm_refl. Qed.
Lemma D_a6a04 : decode_any W_a6a04 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a08 : bv 32 := 0x0095c783.
Lemma F_a6a08 : fetch_word PSEGS (0xa6a08 : word) = Some W_a6a08.
Proof. vm_refl. Qed.
Lemma D_a6a08 : decode_any W_a6a08 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a0c : bv 32 := 0x00a5c803.
Lemma F_a6a0c : fetch_word PSEGS (0xa6a0c : word) = Some W_a6a0c.
Proof. vm_refl. Qed.
Lemma D_a6a0c : decode_any W_a6a0c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a10 : bv 32 := 0x00b5c883.
Lemma F_a6a10 : fetch_word PSEGS (0xa6a10 : word) = Some W_a6a10.
Proof. vm_refl. Qed.
Lemma D_a6a10 : decode_any W_a6a10 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a14 : bv 32 := 0x00568223.
Lemma F_a6a14 : fetch_word PSEGS (0xa6a14 : word) = Some W_a6a14.
Proof. vm_refl. Qed.
Lemma D_a6a14 : decode_any W_a6a14 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a18 : bv 32 := 0x006682a3.
Lemma F_a6a18 : fetch_word PSEGS (0xa6a18 : word) = Some W_a6a18.
Proof. vm_refl. Qed.
Lemma D_a6a18 : decode_any W_a6a18 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a1c : bv 32 := 0x00768323.
Lemma F_a6a1c : fetch_word PSEGS (0xa6a1c : word) = Some W_a6a1c.
Proof. vm_refl. Qed.
Lemma D_a6a1c : decode_any W_a6a1c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a20 : bv 32 := 0x01c683a3.
Lemma F_a6a20 : fetch_word PSEGS (0xa6a20 : word) = Some W_a6a20.
Proof. vm_refl. Qed.
Lemma D_a6a20 : decode_any W_a6a20 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a24 : bv 32 := 0x00c5c283.
Lemma F_a6a24 : fetch_word PSEGS (0xa6a24 : word) = Some W_a6a24.
Proof. vm_refl. Qed.
Lemma D_a6a24 : decode_any W_a6a24 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a28 : bv 32 := 0x00d5c303.
Lemma F_a6a28 : fetch_word PSEGS (0xa6a28 : word) = Some W_a6a28.
Proof. vm_refl. Qed.
Lemma D_a6a28 : decode_any W_a6a28 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a2c : bv 32 := 0x00e5c383.
Lemma F_a6a2c : fetch_word PSEGS (0xa6a2c : word) = Some W_a6a2c.
Proof. vm_refl. Qed.
Lemma D_a6a2c : decode_any W_a6a2c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a30 : bv 32 := 0x00f5ce03.
Lemma F_a6a30 : fetch_word PSEGS (0xa6a30 : word) = Some W_a6a30.
Proof. vm_refl. Qed.
Lemma D_a6a30 : decode_any W_a6a30 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a34 : bv 32 := 0x01058593.
Lemma F_a6a34 : fetch_word PSEGS (0xa6a34 : word) = Some W_a6a34.
Proof. vm_refl. Qed.
Lemma D_a6a34 : decode_any W_a6a34 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a38 : bv 32 := 0x00e68423.
Lemma F_a6a38 : fetch_word PSEGS (0xa6a38 : word) = Some W_a6a38.
Proof. vm_refl. Qed.
Lemma D_a6a38 : decode_any W_a6a38 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a3c : bv 32 := 0x00f684a3.
Lemma F_a6a3c : fetch_word PSEGS (0xa6a3c : word) = Some W_a6a3c.
Proof. vm_refl. Qed.
Lemma D_a6a3c : decode_any W_a6a3c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a40 : bv 32 := 0x01068523.
Lemma F_a6a40 : fetch_word PSEGS (0xa6a40 : word) = Some W_a6a40.
Proof. vm_refl. Qed.
Lemma D_a6a40 : decode_any W_a6a40 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a44 : bv 32 := 0x011685a3.
Lemma F_a6a44 : fetch_word PSEGS (0xa6a44 : word) = Some W_a6a44.
Proof. vm_refl. Qed.
Lemma D_a6a44 : decode_any W_a6a44 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a48 : bv 32 := 0x01068713.
Lemma F_a6a48 : fetch_word PSEGS (0xa6a48 : word) = Some W_a6a48.
Proof. vm_refl. Qed.
Lemma D_a6a48 : decode_any W_a6a48 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a4c : bv 32 := 0x00568623.
Lemma F_a6a4c : fetch_word PSEGS (0xa6a4c : word) = Some W_a6a4c.
Proof. vm_refl. Qed.
Lemma D_a6a4c : decode_any W_a6a4c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a50 : bv 32 := 0x006686a3.
Lemma F_a6a50 : fetch_word PSEGS (0xa6a50 : word) = Some W_a6a50.
Proof. vm_refl. Qed.
Lemma D_a6a50 : decode_any W_a6a50 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a54 : bv 32 := 0x00768723.
Lemma F_a6a54 : fetch_word PSEGS (0xa6a54 : word) = Some W_a6a54.
Proof. vm_refl. Qed.
Lemma D_a6a54 : decode_any W_a6a54 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a58 : bv 32 := 0x01c687a3.
Lemma F_a6a58 : fetch_word PSEGS (0xa6a58 : word) = Some W_a6a58.
Proof. vm_refl. Qed.
Lemma D_a6a58 : decode_any W_a6a58 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a5c : bv 32 := 0x00070693.
Lemma F_a6a5c : fetch_word PSEGS (0xa6a5c : word) = Some W_a6a5c.
Proof. vm_refl. Qed.
Lemma D_a6a5c : decode_any W_a6a5c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a60 : bv 32 := 0x00867713.
Lemma F_a6a60 : fetch_word PSEGS (0xa6a60 : word) = Some W_a6a60.
Proof. vm_refl. Qed.
Lemma D_a6a60 : decode_any W_a6a60 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a64 : bv 32 := 0xd20706e3.
Lemma F_a6a64 : fetch_word PSEGS (0xa6a64 : word) = Some W_a6a64.
Proof. vm_refl. Qed.
Lemma D_a6a64 : decode_any W_a6a64 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a68 : bv 32 := 0x0005c703.
Lemma F_a6a68 : fetch_word PSEGS (0xa6a68 : word) = Some W_a6a68.
Proof. vm_refl. Qed.
Lemma D_a6a68 : decode_any W_a6a68 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a6c : bv 32 := 0x0015c783.
Lemma F_a6a6c : fetch_word PSEGS (0xa6a6c : word) = Some W_a6a6c.
Proof. vm_refl. Qed.
Lemma D_a6a6c : decode_any W_a6a6c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a70 : bv 32 := 0x0025c803.
Lemma F_a6a70 : fetch_word PSEGS (0xa6a70 : word) = Some W_a6a70.
Proof. vm_refl. Qed.
Lemma D_a6a70 : decode_any W_a6a70 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a74 : bv 32 := 0x0035c883.
Lemma F_a6a74 : fetch_word PSEGS (0xa6a74 : word) = Some W_a6a74.
Proof. vm_refl. Qed.
Lemma D_a6a74 : decode_any W_a6a74 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a78 : bv 32 := 0x0045c283.
Lemma F_a6a78 : fetch_word PSEGS (0xa6a78 : word) = Some W_a6a78.
Proof. vm_refl. Qed.
Lemma D_a6a78 : decode_any W_a6a78 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a7c : bv 32 := 0x0055c303.
Lemma F_a6a7c : fetch_word PSEGS (0xa6a7c : word) = Some W_a6a7c.
Proof. vm_refl. Qed.
Lemma D_a6a7c : decode_any W_a6a7c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a80 : bv 32 := 0x0065c383.
Lemma F_a6a80 : fetch_word PSEGS (0xa6a80 : word) = Some W_a6a80.
Proof. vm_refl. Qed.
Lemma D_a6a80 : decode_any W_a6a80 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a84 : bv 32 := 0x0075ce03.
Lemma F_a6a84 : fetch_word PSEGS (0xa6a84 : word) = Some W_a6a84.
Proof. vm_refl. Qed.
Lemma D_a6a84 : decode_any W_a6a84 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a88 : bv 32 := 0x00858593.
Lemma F_a6a88 : fetch_word PSEGS (0xa6a88 : word) = Some W_a6a88.
Proof. vm_refl. Qed.
Lemma D_a6a88 : decode_any W_a6a88 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a8c : bv 32 := 0x00e68023.
Lemma F_a6a8c : fetch_word PSEGS (0xa6a8c : word) = Some W_a6a8c.
Proof. vm_refl. Qed.
Lemma D_a6a8c : decode_any W_a6a8c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a90 : bv 32 := 0x00f680a3.
Lemma F_a6a90 : fetch_word PSEGS (0xa6a90 : word) = Some W_a6a90.
Proof. vm_refl. Qed.
Lemma D_a6a90 : decode_any W_a6a90 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a94 : bv 32 := 0x01068123.
Lemma F_a6a94 : fetch_word PSEGS (0xa6a94 : word) = Some W_a6a94.
Proof. vm_refl. Qed.
Lemma D_a6a94 : decode_any W_a6a94 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a98 : bv 32 := 0x011681a3.
Lemma F_a6a98 : fetch_word PSEGS (0xa6a98 : word) = Some W_a6a98.
Proof. vm_refl. Qed.
Lemma D_a6a98 : decode_any W_a6a98 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6a9c : bv 32 := 0x00868713.
Lemma F_a6a9c : fetch_word PSEGS (0xa6a9c : word) = Some W_a6a9c.
Proof. vm_refl. Qed.
Lemma D_a6a9c : decode_any W_a6a9c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6aa0 : bv 32 := 0x00568223.
Lemma F_a6aa0 : fetch_word PSEGS (0xa6aa0 : word) = Some W_a6aa0.
Proof. vm_refl. Qed.
Lemma D_a6aa0 : decode_any W_a6aa0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6aa4 : bv 32 := 0x006682a3.
Lemma F_a6aa4 : fetch_word PSEGS (0xa6aa4 : word) = Some W_a6aa4.
Proof. vm_refl. Qed.
Lemma D_a6aa4 : decode_any W_a6aa4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6aa8 : bv 32 := 0x00768323.
Lemma F_a6aa8 : fetch_word PSEGS (0xa6aa8 : word) = Some W_a6aa8.
Proof. vm_refl. Qed.
Lemma D_a6aa8 : decode_any W_a6aa8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6aac : bv 32 := 0x01c683a3.
Lemma F_a6aac : fetch_word PSEGS (0xa6aac : word) = Some W_a6aac.
Proof. vm_refl. Qed.
Lemma D_a6aac : decode_any W_a6aac = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ab0 : bv 32 := 0x00070693.
Lemma F_a6ab0 : fetch_word PSEGS (0xa6ab0 : word) = Some W_a6ab0.
Proof. vm_refl. Qed.
Lemma D_a6ab0 : decode_any W_a6ab0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ab4 : bv 32 := 0x00467713.
Lemma F_a6ab4 : fetch_word PSEGS (0xa6ab4 : word) = Some W_a6ab4.
Proof. vm_refl. Qed.
Lemma D_a6ab4 : decode_any W_a6ab4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ab8 : bv 32 := 0x02070863.
Lemma F_a6ab8 : fetch_word PSEGS (0xa6ab8 : word) = Some W_a6ab8.
Proof. vm_refl. Qed.
Lemma D_a6ab8 : decode_any W_a6ab8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6abc : bv 32 := 0x0005c703.
Lemma F_a6abc : fetch_word PSEGS (0xa6abc : word) = Some W_a6abc.
Proof. vm_refl. Qed.
Lemma D_a6abc : decode_any W_a6abc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ac0 : bv 32 := 0x0015c783.
Lemma F_a6ac0 : fetch_word PSEGS (0xa6ac0 : word) = Some W_a6ac0.
Proof. vm_refl. Qed.
Lemma D_a6ac0 : decode_any W_a6ac0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ac4 : bv 32 := 0x0025c803.
Lemma F_a6ac4 : fetch_word PSEGS (0xa6ac4 : word) = Some W_a6ac4.
Proof. vm_refl. Qed.
Lemma D_a6ac4 : decode_any W_a6ac4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ac8 : bv 32 := 0x0035c883.
Lemma F_a6ac8 : fetch_word PSEGS (0xa6ac8 : word) = Some W_a6ac8.
Proof. vm_refl. Qed.
Lemma D_a6ac8 : decode_any W_a6ac8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6acc : bv 32 := 0x00458593.
Lemma F_a6acc : fetch_word PSEGS (0xa6acc : word) = Some W_a6acc.
Proof. vm_refl. Qed.
Lemma D_a6acc : decode_any W_a6acc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ad0 : bv 32 := 0x00468293.
Lemma F_a6ad0 : fetch_word PSEGS (0xa6ad0 : word) = Some W_a6ad0.
Proof. vm_refl. Qed.
Lemma D_a6ad0 : decode_any W_a6ad0 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ad4 : bv 32 := 0x00e68023.
Lemma F_a6ad4 : fetch_word PSEGS (0xa6ad4 : word) = Some W_a6ad4.
Proof. vm_refl. Qed.
Lemma D_a6ad4 : decode_any W_a6ad4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ad8 : bv 32 := 0x00f680a3.
Lemma F_a6ad8 : fetch_word PSEGS (0xa6ad8 : word) = Some W_a6ad8.
Proof. vm_refl. Qed.
Lemma D_a6ad8 : decode_any W_a6ad8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6adc : bv 32 := 0x01068123.
Lemma F_a6adc : fetch_word PSEGS (0xa6adc : word) = Some W_a6adc.
Proof. vm_refl. Qed.
Lemma D_a6adc : decode_any W_a6adc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ae0 : bv 32 := 0x011681a3.
Lemma F_a6ae0 : fetch_word PSEGS (0xa6ae0 : word) = Some W_a6ae0.
Proof. vm_refl. Qed.
Lemma D_a6ae0 : decode_any W_a6ae0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ae4 : bv 32 := 0x00028693.
Lemma F_a6ae4 : fetch_word PSEGS (0xa6ae4 : word) = Some W_a6ae4.
Proof. vm_refl. Qed.
Lemma D_a6ae4 : decode_any W_a6ae4 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ae8 : bv 32 := 0x00267713.
Lemma F_a6ae8 : fetch_word PSEGS (0xa6ae8 : word) = Some W_a6ae8.
Proof. vm_refl. Qed.
Lemma D_a6ae8 : decode_any W_a6ae8 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6aec : bv 32 := 0x00071863.
Lemma F_a6aec : fetch_word PSEGS (0xa6aec : word) = Some W_a6aec.
Proof. vm_refl. Qed.
Lemma D_a6aec : decode_any W_a6aec = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6af0 : bv 32 := 0x00167613.
Lemma F_a6af0 : fetch_word PSEGS (0xa6af0 : word) = Some W_a6af0.
Proof. vm_refl. Qed.
Lemma D_a6af0 : decode_any W_a6af0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6af4 : bv 32 := 0x02061663.
Lemma F_a6af4 : fetch_word PSEGS (0xa6af4 : word) = Some W_a6af4.
Proof. vm_refl. Qed.
Lemma D_a6af4 : decode_any W_a6af4 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6af8 : bv 32 := 0x00008067.
Lemma F_a6af8 : fetch_word PSEGS (0xa6af8 : word) = Some W_a6af8.
Proof. vm_refl. Qed.
Lemma D_a6af8 : decode_any W_a6af8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6afc : bv 32 := 0x0005c703.
Lemma F_a6afc : fetch_word PSEGS (0xa6afc : word) = Some W_a6afc.
Proof. vm_refl. Qed.
Lemma D_a6afc : decode_any W_a6afc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b00 : bv 32 := 0x0015c783.
Lemma F_a6b00 : fetch_word PSEGS (0xa6b00 : word) = Some W_a6b00.
Proof. vm_refl. Qed.
Lemma D_a6b00 : decode_any W_a6b00 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b04 : bv 32 := 0x00258593.
Lemma F_a6b04 : fetch_word PSEGS (0xa6b04 : word) = Some W_a6b04.
Proof. vm_refl. Qed.
Lemma D_a6b04 : decode_any W_a6b04 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b08 : bv 32 := 0x00268813.
Lemma F_a6b08 : fetch_word PSEGS (0xa6b08 : word) = Some W_a6b08.
Proof. vm_refl. Qed.
Lemma D_a6b08 : decode_any W_a6b08 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b0c : bv 32 := 0x00e68023.
Lemma F_a6b0c : fetch_word PSEGS (0xa6b0c : word) = Some W_a6b0c.
Proof. vm_refl. Qed.
Lemma D_a6b0c : decode_any W_a6b0c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b10 : bv 32 := 0x00f680a3.
Lemma F_a6b10 : fetch_word PSEGS (0xa6b10 : word) = Some W_a6b10.
Proof. vm_refl. Qed.
Lemma D_a6b10 : decode_any W_a6b10 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b14 : bv 32 := 0x00080693.
Lemma F_a6b14 : fetch_word PSEGS (0xa6b14 : word) = Some W_a6b14.
Proof. vm_refl. Qed.
Lemma D_a6b14 : decode_any W_a6b14 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b18 : bv 32 := 0x00167613.
Lemma F_a6b18 : fetch_word PSEGS (0xa6b18 : word) = Some W_a6b18.
Proof. vm_refl. Qed.
Lemma D_a6b18 : decode_any W_a6b18 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b1c : bv 32 := 0xfc060ee3.
Lemma F_a6b1c : fetch_word PSEGS (0xa6b1c : word) = Some W_a6b1c.
Proof. vm_refl. Qed.
Lemma D_a6b1c : decode_any W_a6b1c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b20 : bv 32 := 0x0005c583.
Lemma F_a6b20 : fetch_word PSEGS (0xa6b20 : word) = Some W_a6b20.
Proof. vm_refl. Qed.
Lemma D_a6b20 : decode_any W_a6b20 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b24 : bv 32 := 0x00b68023.
Lemma F_a6b24 : fetch_word PSEGS (0xa6b24 : word) = Some W_a6b24.
Proof. vm_refl. Qed.
Lemma D_a6b24 : decode_any W_a6b24 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6b28 : bv 32 := 0x00008067.
Lemma F_a6b28 : fetch_word PSEGS (0xa6b28 : word) = Some W_a6b28.
Proof. vm_refl. Qed.
Lemma D_a6b28 : decode_any W_a6b28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ca8 : bv 32 := 0x0e060a63.
Lemma F_a6ca8 : fetch_word PSEGS (0xa6ca8 : word) = Some W_a6ca8.
Proof. vm_refl. Qed.
Lemma D_a6ca8 : decode_any W_a6ca8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cac : bv 32 := 0x00b50023.
Lemma F_a6cac : fetch_word PSEGS (0xa6cac : word) = Some W_a6cac.
Proof. vm_refl. Qed.
Lemma D_a6cac : decode_any W_a6cac = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cb0 : bv 32 := 0x00c506b3.
Lemma F_a6cb0 : fetch_word PSEGS (0xa6cb0 : word) = Some W_a6cb0.
Proof. vm_refl. Qed.
Lemma D_a6cb0 : decode_any W_a6cb0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cb4 : bv 32 := 0x00300713.
Lemma F_a6cb4 : fetch_word PSEGS (0xa6cb4 : word) = Some W_a6cb4.
Proof. vm_refl. Qed.
Lemma D_a6cb4 : decode_any W_a6cb4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cb8 : bv 32 := 0xfeb68fa3.
Lemma F_a6cb8 : fetch_word PSEGS (0xa6cb8 : word) = Some W_a6cb8.
Proof. vm_refl. Qed.
Lemma D_a6cb8 : decode_any W_a6cb8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cbc : bv 32 := 0x0ee66063.
Lemma F_a6cbc : fetch_word PSEGS (0xa6cbc : word) = Some W_a6cbc.
Proof. vm_refl. Qed.
Lemma D_a6cbc : decode_any W_a6cbc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cc0 : bv 32 := 0x00b500a3.
Lemma F_a6cc0 : fetch_word PSEGS (0xa6cc0 : word) = Some W_a6cc0.
Proof. vm_refl. Qed.
Lemma D_a6cc0 : decode_any W_a6cc0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cc4 : bv 32 := 0x00b50123.
Lemma F_a6cc4 : fetch_word PSEGS (0xa6cc4 : word) = Some W_a6cc4.
Proof. vm_refl. Qed.
Lemma D_a6cc4 : decode_any W_a6cc4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cc8 : bv 32 := 0x00700713.
Lemma F_a6cc8 : fetch_word PSEGS (0xa6cc8 : word) = Some W_a6cc8.
Proof. vm_refl. Qed.
Lemma D_a6cc8 : decode_any W_a6cc8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ccc : bv 32 := 0xfeb68ea3.
Lemma F_a6ccc : fetch_word PSEGS (0xa6ccc : word) = Some W_a6ccc.
Proof. vm_refl. Qed.
Lemma D_a6ccc : decode_any W_a6ccc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cd0 : bv 32 := 0xfeb68f23.
Lemma F_a6cd0 : fetch_word PSEGS (0xa6cd0 : word) = Some W_a6cd0.
Proof. vm_refl. Qed.
Lemma D_a6cd0 : decode_any W_a6cd0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cd4 : bv 32 := 0x0ce66463.
Lemma F_a6cd4 : fetch_word PSEGS (0xa6cd4 : word) = Some W_a6cd4.
Proof. vm_refl. Qed.
Lemma D_a6cd4 : decode_any W_a6cd4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cd8 : bv 32 := 0x00b501a3.
Lemma F_a6cd8 : fetch_word PSEGS (0xa6cd8 : word) = Some W_a6cd8.
Proof. vm_refl. Qed.
Lemma D_a6cd8 : decode_any W_a6cd8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cdc : bv 32 := 0x00900793.
Lemma F_a6cdc : fetch_word PSEGS (0xa6cdc : word) = Some W_a6cdc.
Proof. vm_refl. Qed.
Lemma D_a6cdc : decode_any W_a6cdc = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ce0 : bv 32 := 0xfeb68e23.
Lemma F_a6ce0 : fetch_word PSEGS (0xa6ce0 : word) = Some W_a6ce0.
Proof. vm_refl. Qed.
Lemma D_a6ce0 : decode_any W_a6ce0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ce4 : bv 32 := 0x0af66c63.
Lemma F_a6ce4 : fetch_word PSEGS (0xa6ce4 : word) = Some W_a6ce4.
Proof. vm_refl. Qed.
Lemma D_a6ce4 : decode_any W_a6ce4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ce8 : bv 32 := 0x40a006bb.
Lemma F_a6ce8 : fetch_word PSEGS (0xa6ce8 : word) = Some W_a6ce8.
Proof. vm_refl. Qed.
Lemma D_a6ce8 : decode_any W_a6ce8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cec : bv 32 := 0x03859813.
Lemma F_a6cec : fetch_word PSEGS (0xa6cec : word) = Some W_a6cec.
Proof. vm_refl. Qed.
Lemma D_a6cec : decode_any W_a6cec = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cf0 : bv 32 := 0x101015b7.
Lemma F_a6cf0 : fetch_word PSEGS (0xa6cf0 : word) = Some W_a6cf0.
Proof. vm_refl. Qed.
Lemma D_a6cf0 : decode_any W_a6cf0 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cf4 : bv 32 := 0x0036f693.
Lemma F_a6cf4 : fetch_word PSEGS (0xa6cf4 : word) = Some W_a6cf4.
Proof. vm_refl. Qed.
Lemma D_a6cf4 : decode_any W_a6cf4 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cf8 : bv 32 := 0x00459713.
Lemma F_a6cf8 : fetch_word PSEGS (0xa6cf8 : word) = Some W_a6cf8.
Proof. vm_refl. Qed.
Lemma D_a6cf8 : decode_any W_a6cf8 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6cfc : bv 32 := 0x40d60633.
Lemma F_a6cfc : fetch_word PSEGS (0xa6cfc : word) = Some W_a6cfc.
Proof. vm_refl. Qed.
Lemma D_a6cfc : decode_any W_a6cfc = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d00 : bv 32 := 0x00d505b3.
Lemma F_a6d00 : fetch_word PSEGS (0xa6d00 : word) = Some W_a6d00.
Proof. vm_refl. Qed.
Lemma D_a6d00 : decode_any W_a6d00 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d04 : bv 32 := 0x10070693.
Lemma F_a6d04 : fetch_word PSEGS (0xa6d04 : word) = Some W_a6d04.
Proof. vm_refl. Qed.
Lemma D_a6d04 : decode_any W_a6d04 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d08 : bv 32 := 0xffc67713.
Lemma F_a6d08 : fetch_word PSEGS (0xa6d08 : word) = Some W_a6d08.
Proof. vm_refl. Qed.
Lemma D_a6d08 : decode_any W_a6d08 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d0c : bv 32 := 0x02d83633.
Lemma F_a6d0c : fetch_word PSEGS (0xa6d0c : word) = Some W_a6d0c.
Proof. vm_refl. Qed.
Lemma D_a6d0c : decode_any W_a6d0c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d10 : bv 32 := 0x00c5a023.
Lemma F_a6d10 : fetch_word PSEGS (0xa6d10 : word) = Some W_a6d10.
Proof. vm_refl. Qed.
Lemma D_a6d10 : decode_any W_a6d10 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d14 : bv 32 := 0x00e586b3.
Lemma F_a6d14 : fetch_word PSEGS (0xa6d14 : word) = Some W_a6d14.
Proof. vm_refl. Qed.
Lemma D_a6d14 : decode_any W_a6d14 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d18 : bv 32 := 0xfec6ae23.
Lemma F_a6d18 : fetch_word PSEGS (0xa6d18 : word) = Some W_a6d18.
Proof. vm_refl. Qed.
Lemma D_a6d18 : decode_any W_a6d18 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d1c : bv 32 := 0x08f76063.
Lemma F_a6d1c : fetch_word PSEGS (0xa6d1c : word) = Some W_a6d1c.
Proof. vm_refl. Qed.
Lemma D_a6d1c : decode_any W_a6d1c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d20 : bv 32 := 0x00c5a223.
Lemma F_a6d20 : fetch_word PSEGS (0xa6d20 : word) = Some W_a6d20.
Proof. vm_refl. Qed.
Lemma D_a6d20 : decode_any W_a6d20 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d24 : bv 32 := 0x00c5a423.
Lemma F_a6d24 : fetch_word PSEGS (0xa6d24 : word) = Some W_a6d24.
Proof. vm_refl. Qed.
Lemma D_a6d24 : decode_any W_a6d24 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d28 : bv 32 := 0x01900793.
Lemma F_a6d28 : fetch_word PSEGS (0xa6d28 : word) = Some W_a6d28.
Proof. vm_refl. Qed.
Lemma D_a6d28 : decode_any W_a6d28 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d2c : bv 32 := 0xfec6aa23.
Lemma F_a6d2c : fetch_word PSEGS (0xa6d2c : word) = Some W_a6d2c.
Proof. vm_refl. Qed.
Lemma D_a6d2c : decode_any W_a6d2c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d30 : bv 32 := 0xfec6ac23.
Lemma F_a6d30 : fetch_word PSEGS (0xa6d30 : word) = Some W_a6d30.
Proof. vm_refl. Qed.
Lemma D_a6d30 : decode_any W_a6d30 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d34 : bv 32 := 0x06f76463.
Lemma F_a6d34 : fetch_word PSEGS (0xa6d34 : word) = Some W_a6d34.
Proof. vm_refl. Qed.
Lemma D_a6d34 : decode_any W_a6d34 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d38 : bv 32 := 0x00c5a623.
Lemma F_a6d38 : fetch_word PSEGS (0xa6d38 : word) = Some W_a6d38.
Proof. vm_refl. Qed.
Lemma D_a6d38 : decode_any W_a6d38 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d3c : bv 32 := 0x00c5a823.
Lemma F_a6d3c : fetch_word PSEGS (0xa6d3c : word) = Some W_a6d3c.
Proof. vm_refl. Qed.
Lemma D_a6d3c : decode_any W_a6d3c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d40 : bv 32 := 0x00c5aa23.
Lemma F_a6d40 : fetch_word PSEGS (0xa6d40 : word) = Some W_a6d40.
Proof. vm_refl. Qed.
Lemma D_a6d40 : decode_any W_a6d40 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d44 : bv 32 := 0x00c5ac23.
Lemma F_a6d44 : fetch_word PSEGS (0xa6d44 : word) = Some W_a6d44.
Proof. vm_refl. Qed.
Lemma D_a6d44 : decode_any W_a6d44 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d48 : bv 32 := 0x0045f793.
Lemma F_a6d48 : fetch_word PSEGS (0xa6d48 : word) = Some W_a6d48.
Proof. vm_refl. Qed.
Lemma D_a6d48 : decode_any W_a6d48 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d4c : bv 32 := 0x02000813.
Lemma F_a6d4c : fetch_word PSEGS (0xa6d4c : word) = Some W_a6d4c.
Proof. vm_refl. Qed.
Lemma D_a6d4c : decode_any W_a6d4c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d50 : bv 32 := 0x01878793.
Lemma F_a6d50 : fetch_word PSEGS (0xa6d50 : word) = Some W_a6d50.
Proof. vm_refl. Qed.
Lemma D_a6d50 : decode_any W_a6d50 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d54 : bv 32 := 0x40f70733.
Lemma F_a6d54 : fetch_word PSEGS (0xa6d54 : word) = Some W_a6d54.
Proof. vm_refl. Qed.
Lemma D_a6d54 : decode_any W_a6d54 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d58 : bv 32 := 0xfec6a223.
Lemma F_a6d58 : fetch_word PSEGS (0xa6d58 : word) = Some W_a6d58.
Proof. vm_refl. Qed.
Lemma D_a6d58 : decode_any W_a6d58 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d5c : bv 32 := 0xfec6a423.
Lemma F_a6d5c : fetch_word PSEGS (0xa6d5c : word) = Some W_a6d5c.
Proof. vm_refl. Qed.
Lemma D_a6d5c : decode_any W_a6d5c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d60 : bv 32 := 0xfec6a623.
Lemma F_a6d60 : fetch_word PSEGS (0xa6d60 : word) = Some W_a6d60.
Proof. vm_refl. Qed.
Lemma D_a6d60 : decode_any W_a6d60 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d64 : bv 32 := 0xfec6a823.
Lemma F_a6d64 : fetch_word PSEGS (0xa6d64 : word) = Some W_a6d64.
Proof. vm_refl. Qed.
Lemma D_a6d64 : decode_any W_a6d64 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d68 : bv 32 := 0x03076a63.
Lemma F_a6d68 : fetch_word PSEGS (0xa6d68 : word) = Some W_a6d68.
Proof. vm_refl. Qed.
Lemma D_a6d68 : decode_any W_a6d68 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d6c : bv 32 := 0x02061613.
Lemma F_a6d6c : fetch_word PSEGS (0xa6d6c : word) = Some W_a6d6c.
Proof. vm_refl. Qed.
Lemma D_a6d6c : decode_any W_a6d6c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d70 : bv 32 := 0x00f585b3.
Lemma F_a6d70 : fetch_word PSEGS (0xa6d70 : word) = Some W_a6d70.
Proof. vm_refl. Qed.
Lemma D_a6d70 : decode_any W_a6d70 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d74 : bv 32 := 0x02065693.
Lemma F_a6d74 : fetch_word PSEGS (0xa6d74 : word) = Some W_a6d74.
Proof. vm_refl. Qed.
Lemma D_a6d74 : decode_any W_a6d74 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d78 : bv 32 := 0x00d66633.
Lemma F_a6d78 : fetch_word PSEGS (0xa6d78 : word) = Some W_a6d78.
Proof. vm_refl. Qed.
Lemma D_a6d78 : decode_any W_a6d78 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d7c : bv 32 := 0x01f00693.
Lemma F_a6d7c : fetch_word PSEGS (0xa6d7c : word) = Some W_a6d7c.
Proof. vm_refl. Qed.
Lemma D_a6d7c : decode_any W_a6d7c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d80 : bv 32 := 0x00c5b023.
Lemma F_a6d80 : fetch_word PSEGS (0xa6d80 : word) = Some W_a6d80.
Proof. vm_refl. Qed.
Lemma D_a6d80 : decode_any W_a6d80 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d84 : bv 32 := 0x00c5b423.
Lemma F_a6d84 : fetch_word PSEGS (0xa6d84 : word) = Some W_a6d84.
Proof. vm_refl. Qed.
Lemma D_a6d84 : decode_any W_a6d84 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d88 : bv 32 := 0x00c5b823.
Lemma F_a6d88 : fetch_word PSEGS (0xa6d88 : word) = Some W_a6d88.
Proof. vm_refl. Qed.
Lemma D_a6d88 : decode_any W_a6d88 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d8c : bv 32 := 0x00c5bc23.
Lemma F_a6d8c : fetch_word PSEGS (0xa6d8c : word) = Some W_a6d8c.
Proof. vm_refl. Qed.
Lemma D_a6d8c : decode_any W_a6d8c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d90 : bv 32 := 0xfe070713.
Lemma F_a6d90 : fetch_word PSEGS (0xa6d90 : word) = Some W_a6d90.
Proof. vm_refl. Qed.
Lemma D_a6d90 : decode_any W_a6d90 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d94 : bv 32 := 0x02058593.
Lemma F_a6d94 : fetch_word PSEGS (0xa6d94 : word) = Some W_a6d94.
Proof. vm_refl. Qed.
Lemma D_a6d94 : decode_any W_a6d94 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d98 : bv 32 := 0xfee6e4e3.
Lemma F_a6d98 : fetch_word PSEGS (0xa6d98 : word) = Some W_a6d98.
Proof. vm_refl. Qed.
Lemma D_a6d98 : decode_any W_a6d98 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6d9c : bv 32 := 0x00008067.
Lemma F_a6d9c : fetch_word PSEGS (0xa6d9c : word) = Some W_a6d9c.
Proof. vm_refl. Qed.
Lemma D_a6d9c : decode_any W_a6d9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6da0 : bv 32 := 0xff010113.
Lemma F_a6da0 : fetch_word PSEGS (0xa6da0 : word) = Some W_a6da0.
Proof. vm_refl. Qed.
Lemma D_a6da0 : decode_any W_a6da0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6da4 : bv 32 := 0x00113423.
Lemma F_a6da4 : fetch_word PSEGS (0xa6da4 : word) = Some W_a6da4.
Proof. vm_refl. Qed.
Lemma D_a6da4 : decode_any W_a6da4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6da8 : bv 32 := 0x00813023.
Lemma F_a6da8 : fetch_word PSEGS (0xa6da8 : word) = Some W_a6da8.
Proof. vm_refl. Qed.
Lemma D_a6da8 : decode_any W_a6da8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dac : bv 32 := 0x00058413.
Lemma F_a6dac : fetch_word PSEGS (0xa6dac : word) = Some W_a6dac.
Proof. vm_refl. Qed.
Lemma D_a6dac : decode_any W_a6dac = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6db0 : bv 32 := 0x02c000ef.
Lemma F_a6db0 : fetch_word PSEGS (0xa6db0 : word) = Some W_a6db0.
Proof. vm_refl. Qed.
Lemma D_a6db0 : decode_any W_a6db0 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6db4 : bv 32 := 0x00054583.
Lemma F_a6db4 : fetch_word PSEGS (0xa6db4 : word) = Some W_a6db4.
Proof. vm_refl. Qed.
Lemma D_a6db4 : decode_any W_a6db4 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6db8 : bv 32 := 0x0ff47613.
Lemma F_a6db8 : fetch_word PSEGS (0xa6db8 : word) = Some W_a6db8.
Proof. vm_refl. Qed.
Lemma D_a6db8 : decode_any W_a6db8 = Some (OpImm ALU_AND 12 8 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dbc : bv 32 := 0x00c5c5b3.
Lemma F_a6dbc : fetch_word PSEGS (0xa6dbc : word) = Some W_a6dbc.
Proof. vm_refl. Qed.
Lemma D_a6dbc : decode_any W_a6dbc = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dc0 : bv 32 := 0x00b035b3.
Lemma F_a6dc0 : fetch_word PSEGS (0xa6dc0 : word) = Some W_a6dc0.
Proof. vm_refl. Qed.
Lemma D_a6dc0 : decode_any W_a6dc0 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dc4 : bv 32 := 0xfff58593.
Lemma F_a6dc4 : fetch_word PSEGS (0xa6dc4 : word) = Some W_a6dc4.
Proof. vm_refl. Qed.
Lemma D_a6dc4 : decode_any W_a6dc4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dc8 : bv 32 := 0x00a5f533.
Lemma F_a6dc8 : fetch_word PSEGS (0xa6dc8 : word) = Some W_a6dc8.
Proof. vm_refl. Qed.
Lemma D_a6dc8 : decode_any W_a6dc8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dcc : bv 32 := 0x00813083.
Lemma F_a6dcc : fetch_word PSEGS (0xa6dcc : word) = Some W_a6dcc.
Proof. vm_refl. Qed.
Lemma D_a6dcc : decode_any W_a6dcc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dd0 : bv 32 := 0x00013403.
Lemma F_a6dd0 : fetch_word PSEGS (0xa6dd0 : word) = Some W_a6dd0.
Proof. vm_refl. Qed.
Lemma D_a6dd0 : decode_any W_a6dd0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dd4 : bv 32 := 0x01010113.
Lemma F_a6dd4 : fetch_word PSEGS (0xa6dd4 : word) = Some W_a6dd4.
Proof. vm_refl. Qed.
Lemma D_a6dd4 : decode_any W_a6dd4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ddc : bv 32 := 0xff010113.
Lemma F_a6ddc : fetch_word PSEGS (0xa6ddc : word) = Some W_a6ddc.
Proof. vm_refl. Qed.
Lemma D_a6ddc : decode_any W_a6ddc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6de0 : bv 32 := 0x00113423.
Lemma F_a6de0 : fetch_word PSEGS (0xa6de0 : word) = Some W_a6de0.
Proof. vm_refl. Qed.
Lemma D_a6de0 : decode_any W_a6de0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6de4 : bv 32 := 0x00813023.
Lemma F_a6de4 : fetch_word PSEGS (0xa6de4 : word) = Some W_a6de4.
Proof. vm_refl. Qed.
Lemma D_a6de4 : decode_any W_a6de4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6de8 : bv 32 := 0x0ff5f593.
Lemma F_a6de8 : fetch_word PSEGS (0xa6de8 : word) = Some W_a6de8.
Proof. vm_refl. Qed.
Lemma D_a6de8 : decode_any W_a6de8 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6dec : bv 32 := 0x08058663.
Lemma F_a6dec : fetch_word PSEGS (0xa6dec : word) = Some W_a6dec.
Proof. vm_refl. Qed.
Lemma D_a6dec : decode_any W_a6dec = Some (Branch BC_EQ 11 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e20 : bv 32 := 0x00053703.
Lemma F_a6e20 : fetch_word PSEGS (0xa6e20 : word) = Some W_a6e20.
Proof. vm_refl. Qed.
Lemma D_a6e20 : decode_any W_a6e20 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e24 : bv 32 := 0xfff6c697.
Lemma F_a6e24 : fetch_word PSEGS (0xa6e24 : word) = Some W_a6e24.
Proof. vm_refl. Qed.
Lemma D_a6e24 : decode_any W_a6e24 = Some (Auipc 13 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e28 : bv 32 := 0x5546b683.
Lemma F_a6e28 : fetch_word PSEGS (0xa6e28 : word) = Some W_a6e28.
Proof. vm_refl. Qed.
Lemma D_a6e28 : decode_any W_a6e28 = Some (Load SZ8 true 13 13 1364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e2c : bv 32 := 0x40e607b3.
Lemma F_a6e2c : fetch_word PSEGS (0xa6e2c : word) = Some W_a6e2c.
Proof. vm_refl. Qed.
Lemma D_a6e2c : decode_any W_a6e2c = Some (Op ALU_SUB 15 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e30 : bv 32 := 0x00e7e7b3.
Lemma F_a6e30 : fetch_word PSEGS (0xa6e30 : word) = Some W_a6e30.
Proof. vm_refl. Qed.
Lemma D_a6e30 : decode_any W_a6e30 = Some (Op ALU_OR 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e34 : bv 32 := 0x00d7f7b3.
Lemma F_a6e34 : fetch_word PSEGS (0xa6e34 : word) = Some W_a6e34.
Proof. vm_refl. Qed.
Lemma D_a6e34 : decode_any W_a6e34 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e38 : bv 32 := 0x04d79e63.
Lemma F_a6e38 : fetch_word PSEGS (0xa6e38 : word) = Some W_a6e38.
Proof. vm_refl. Qed.
Lemma D_a6e38 : decode_any W_a6e38 = Some (Branch BC_NE 15 13 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e3c : bv 32 := 0x00160793.
Lemma F_a6e3c : fetch_word PSEGS (0xa6e3c : word) = Some W_a6e3c.
Proof. vm_refl. Qed.
Lemma D_a6e3c : decode_any W_a6e3c = Some (OpImm ALU_ADD 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e40 : bv 32 := 0x02f587b3.
Lemma F_a6e40 : fetch_word PSEGS (0xa6e40 : word) = Some W_a6e40.
Proof. vm_refl. Qed.
Lemma D_a6e40 : decode_any W_a6e40 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e44 : bv 32 := 0x00f74733.
Lemma F_a6e44 : fetch_word PSEGS (0xa6e44 : word) = Some W_a6e44.
Proof. vm_refl. Qed.
Lemma D_a6e44 : decode_any W_a6e44 = Some (Op ALU_XOR 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e48 : bv 32 := 0x40e60833.
Lemma F_a6e48 : fetch_word PSEGS (0xa6e48 : word) = Some W_a6e48.
Proof. vm_refl. Qed.
Lemma D_a6e48 : decode_any W_a6e48 = Some (Op ALU_SUB 16 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e4c : bv 32 := 0x00e86733.
Lemma F_a6e4c : fetch_word PSEGS (0xa6e4c : word) = Some W_a6e4c.
Proof. vm_refl. Qed.
Lemma D_a6e4c : decode_any W_a6e4c = Some (Op ALU_OR 14 16 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e50 : bv 32 := 0x00d77733.
Lemma F_a6e50 : fetch_word PSEGS (0xa6e50 : word) = Some W_a6e50.
Proof. vm_refl. Qed.
Lemma D_a6e50 : decode_any W_a6e50 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e54 : bv 32 := 0x04d71063.
Lemma F_a6e54 : fetch_word PSEGS (0xa6e54 : word) = Some W_a6e54.
Proof. vm_refl. Qed.
Lemma D_a6e54 : decode_any W_a6e54 = Some (Branch BC_NE 14 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e58 : bv 32 := 0x00853703.
Lemma F_a6e58 : fetch_word PSEGS (0xa6e58 : word) = Some W_a6e58.
Proof. vm_refl. Qed.
Lemma D_a6e58 : decode_any W_a6e58 = Some (Load SZ8 true 14 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e5c : bv 32 := 0x00850813.
Lemma F_a6e5c : fetch_word PSEGS (0xa6e5c : word) = Some W_a6e5c.
Proof. vm_refl. Qed.
Lemma D_a6e5c : decode_any W_a6e5c = Some (OpImm ALU_ADD 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e60 : bv 32 := 0x40e60533.
Lemma F_a6e60 : fetch_word PSEGS (0xa6e60 : word) = Some W_a6e60.
Proof. vm_refl. Qed.
Lemma D_a6e60 : decode_any W_a6e60 = Some (Op ALU_SUB 10 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e64 : bv 32 := 0x00e56533.
Lemma F_a6e64 : fetch_word PSEGS (0xa6e64 : word) = Some W_a6e64.
Proof. vm_refl. Qed.
Lemma D_a6e64 : decode_any W_a6e64 = Some (Op ALU_OR 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e68 : bv 32 := 0x00d578b3.
Lemma F_a6e68 : fetch_word PSEGS (0xa6e68 : word) = Some W_a6e68.
Proof. vm_refl. Qed.
Lemma D_a6e68 : decode_any W_a6e68 = Some (Op ALU_AND 17 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e6c : bv 32 := 0x00080513.
Lemma F_a6e6c : fetch_word PSEGS (0xa6e6c : word) = Some W_a6e6c.
Proof. vm_refl. Qed.
Lemma D_a6e6c : decode_any W_a6e6c = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e70 : bv 32 := 0xfcd88ae3.
Lemma F_a6e70 : fetch_word PSEGS (0xa6e70 : word) = Some W_a6e70.
Proof. vm_refl. Qed.
Lemma D_a6e70 : decode_any W_a6e70 = Some (Branch BC_EQ 17 13 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e74 : bv 32 := 0x0240006f.
Lemma F_a6e74 : fetch_word PSEGS (0xa6e74 : word) = Some W_a6e74.
Proof. vm_refl. Qed.
Lemma D_a6e74 : decode_any W_a6e74 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e78 : bv 32 := 0x00050413.
Lemma F_a6e78 : fetch_word PSEGS (0xa6e78 : word) = Some W_a6e78.
Proof. vm_refl. Qed.
Lemma D_a6e78 : decode_any W_a6e78 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e7c : bv 32 := 0x278000ef.
Lemma F_a6e7c : fetch_word PSEGS (0xa6e7c : word) = Some W_a6e7c.
Proof. vm_refl. Qed.
Lemma D_a6e7c : decode_any W_a6e7c = Some (Jal 1 632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e80 : bv 32 := 0x00a40533.
Lemma F_a6e80 : fetch_word PSEGS (0xa6e80 : word) = Some W_a6e80.
Proof. vm_refl. Qed.
Lemma D_a6e80 : decode_any W_a6e80 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e84 : bv 32 := 0x00813083.
Lemma F_a6e84 : fetch_word PSEGS (0xa6e84 : word) = Some W_a6e84.
Proof. vm_refl. Qed.
Lemma D_a6e84 : decode_any W_a6e84 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e88 : bv 32 := 0x00013403.
Lemma F_a6e88 : fetch_word PSEGS (0xa6e88 : word) = Some W_a6e88.
Proof. vm_refl. Qed.
Lemma D_a6e88 : decode_any W_a6e88 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e8c : bv 32 := 0x01010113.
Lemma F_a6e8c : fetch_word PSEGS (0xa6e8c : word) = Some W_a6e8c.
Proof. vm_refl. Qed.
Lemma D_a6e8c : decode_any W_a6e8c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e90 : bv 32 := 0x00008067.
Lemma F_a6e90 : fetch_word PSEGS (0xa6e90 : word) = Some W_a6e90.
Proof. vm_refl. Qed.
Lemma D_a6e90 : decode_any W_a6e90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e94 : bv 32 := 0x00050813.
Lemma F_a6e94 : fetch_word PSEGS (0xa6e94 : word) = Some W_a6e94.
Proof. vm_refl. Qed.
Lemma D_a6e94 : decode_any W_a6e94 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e98 : bv 32 := 0xfff80513.
Lemma F_a6e98 : fetch_word PSEGS (0xa6e98 : word) = Some W_a6e98.
Proof. vm_refl. Qed.
Lemma D_a6e98 : decode_any W_a6e98 = Some (OpImm ALU_ADD 10 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6e9c : bv 32 := 0x00154603.
Lemma F_a6e9c : fetch_word PSEGS (0xa6e9c : word) = Some W_a6e9c.
Proof. vm_refl. Qed.
Lemma D_a6e9c : decode_any W_a6e9c = Some (Load SZ1 false 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ea0 : bv 32 := 0x00150513.
Lemma F_a6ea0 : fetch_word PSEGS (0xa6ea0 : word) = Some W_a6ea0.
Proof. vm_refl. Qed.
Lemma D_a6ea0 : decode_any W_a6ea0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ea4 : bv 32 := 0x00060463.
Lemma F_a6ea4 : fetch_word PSEGS (0xa6ea4 : word) = Some W_a6ea4.
Proof. vm_refl. Qed.
Lemma D_a6ea4 : decode_any W_a6ea4 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ea8 : bv 32 := 0xfeb61ae3.
Lemma F_a6ea8 : fetch_word PSEGS (0xa6ea8 : word) = Some W_a6ea8.
Proof. vm_refl. Qed.
Lemma D_a6ea8 : decode_any W_a6ea8 = Some (Branch BC_NE 12 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6eac : bv 32 := 0x00813083.
Lemma F_a6eac : fetch_word PSEGS (0xa6eac : word) = Some W_a6eac.
Proof. vm_refl. Qed.
Lemma D_a6eac : decode_any W_a6eac = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6eb0 : bv 32 := 0x00013403.
Lemma F_a6eb0 : fetch_word PSEGS (0xa6eb0 : word) = Some W_a6eb0.
Proof. vm_refl. Qed.
Lemma D_a6eb0 : decode_any W_a6eb0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6eb4 : bv 32 := 0x01010113.
Lemma F_a6eb4 : fetch_word PSEGS (0xa6eb4 : word) = Some W_a6eb4.
Proof. vm_refl. Qed.
Lemma D_a6eb4 : decode_any W_a6eb4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6eb8 : bv 32 := 0x00008067.
Lemma F_a6eb8 : fetch_word PSEGS (0xa6eb8 : word) = Some W_a6eb8.
Proof. vm_refl. Qed.
Lemma D_a6eb8 : decode_any W_a6eb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ebc : bv 32 := 0x00054603.
Lemma F_a6ebc : fetch_word PSEGS (0xa6ebc : word) = Some W_a6ebc.
Proof. vm_refl. Qed.
Lemma D_a6ebc : decode_any W_a6ebc = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ec0 : bv 32 := 0x0005c683.
Lemma F_a6ec0 : fetch_word PSEGS (0xa6ec0 : word) = Some W_a6ec0.
Proof. vm_refl. Qed.
Lemma D_a6ec0 : decode_any W_a6ec0 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ec4 : bv 32 := 0x02060463.
Lemma F_a6ec4 : fetch_word PSEGS (0xa6ec4 : word) = Some W_a6ec4.
Proof. vm_refl. Qed.
Lemma D_a6ec4 : decode_any W_a6ec4 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ec8 : bv 32 := 0x02d61263.
Lemma F_a6ec8 : fetch_word PSEGS (0xa6ec8 : word) = Some W_a6ec8.
Proof. vm_refl. Qed.
Lemma D_a6ec8 : decode_any W_a6ec8 = Some (Branch BC_NE 12 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ecc : bv 32 := 0x00158593.
Lemma F_a6ecc : fetch_word PSEGS (0xa6ecc : word) = Some W_a6ecc.
Proof. vm_refl. Qed.
Lemma D_a6ecc : decode_any W_a6ecc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ed0 : bv 32 := 0x00150513.
Lemma F_a6ed0 : fetch_word PSEGS (0xa6ed0 : word) = Some W_a6ed0.
Proof. vm_refl. Qed.
Lemma D_a6ed0 : decode_any W_a6ed0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ed4 : bv 32 := 0x00054603.
Lemma F_a6ed4 : fetch_word PSEGS (0xa6ed4 : word) = Some W_a6ed4.
Proof. vm_refl. Qed.
Lemma D_a6ed4 : decode_any W_a6ed4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ed8 : bv 32 := 0x0005c683.
Lemma F_a6ed8 : fetch_word PSEGS (0xa6ed8 : word) = Some W_a6ed8.
Proof. vm_refl. Qed.
Lemma D_a6ed8 : decode_any W_a6ed8 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6edc : bv 32 := 0x00060863.
Lemma F_a6edc : fetch_word PSEGS (0xa6edc : word) = Some W_a6edc.
Proof. vm_refl. Qed.
Lemma D_a6edc : decode_any W_a6edc = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ee0 : bv 32 := 0x00158593.
Lemma F_a6ee0 : fetch_word PSEGS (0xa6ee0 : word) = Some W_a6ee0.
Proof. vm_refl. Qed.
Lemma D_a6ee0 : decode_any W_a6ee0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ee4 : bv 32 := 0x00150513.
Lemma F_a6ee4 : fetch_word PSEGS (0xa6ee4 : word) = Some W_a6ee4.
Proof. vm_refl. Qed.
Lemma D_a6ee4 : decode_any W_a6ee4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ee8 : bv 32 := 0xfed606e3.
Lemma F_a6ee8 : fetch_word PSEGS (0xa6ee8 : word) = Some W_a6ee8.
Proof. vm_refl. Qed.
Lemma D_a6ee8 : decode_any W_a6ee8 = Some (Branch BC_EQ 12 13 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6eec : bv 32 := 0x40d60533.
Lemma F_a6eec : fetch_word PSEGS (0xa6eec : word) = Some W_a6eec.
Proof. vm_refl. Qed.
Lemma D_a6eec : decode_any W_a6eec = Some (Op ALU_SUB 10 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ef0 : bv 32 := 0x00008067.
Lemma F_a6ef0 : fetch_word PSEGS (0xa6ef0 : word) = Some W_a6ef0.
Proof. vm_refl. Qed.
Lemma D_a6ef0 : decode_any W_a6ef0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ef4 : bv 32 := 0xff010113.
Lemma F_a6ef4 : fetch_word PSEGS (0xa6ef4 : word) = Some W_a6ef4.
Proof. vm_refl. Qed.
Lemma D_a6ef4 : decode_any W_a6ef4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ef8 : bv 32 := 0x00113423.
Lemma F_a6ef8 : fetch_word PSEGS (0xa6ef8 : word) = Some W_a6ef8.
Proof. vm_refl. Qed.
Lemma D_a6ef8 : decode_any W_a6ef8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6efc : bv 32 := 0x00813023.
Lemma F_a6efc : fetch_word PSEGS (0xa6efc : word) = Some W_a6efc.
Proof. vm_refl. Qed.
Lemma D_a6efc : decode_any W_a6efc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f00 : bv 32 := 0x00050413.
Lemma F_a6f00 : fetch_word PSEGS (0xa6f00 : word) = Some W_a6f00.
Proof. vm_refl. Qed.
Lemma D_a6f00 : decode_any W_a6f00 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f04 : bv 32 := 0x018000ef.
Lemma F_a6f04 : fetch_word PSEGS (0xa6f04 : word) = Some W_a6f04.
Proof. vm_refl. Qed.
Lemma D_a6f04 : decode_any W_a6f04 = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f08 : bv 32 := 0x00040513.
Lemma F_a6f08 : fetch_word PSEGS (0xa6f08 : word) = Some W_a6f08.
Proof. vm_refl. Qed.
Lemma D_a6f08 : decode_any W_a6f08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f0c : bv 32 := 0x00813083.
Lemma F_a6f0c : fetch_word PSEGS (0xa6f0c : word) = Some W_a6f0c.
Proof. vm_refl. Qed.
Lemma D_a6f0c : decode_any W_a6f0c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f10 : bv 32 := 0x00013403.
Lemma F_a6f10 : fetch_word PSEGS (0xa6f10 : word) = Some W_a6f10.
Proof. vm_refl. Qed.
Lemma D_a6f10 : decode_any W_a6f10 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f14 : bv 32 := 0x01010113.
Lemma F_a6f14 : fetch_word PSEGS (0xa6f14 : word) = Some W_a6f14.
Proof. vm_refl. Qed.
Lemma D_a6f14 : decode_any W_a6f14 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f18 : bv 32 := 0x00008067.
Lemma F_a6f18 : fetch_word PSEGS (0xa6f18 : word) = Some W_a6f18.
Proof. vm_refl. Qed.
Lemma D_a6f18 : decode_any W_a6f18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f1c : bv 32 := 0x00a5c633.
Lemma F_a6f1c : fetch_word PSEGS (0xa6f1c : word) = Some W_a6f1c.
Proof. vm_refl. Qed.
Lemma D_a6f1c : decode_any W_a6f1c = Some (Op ALU_XOR 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f20 : bv 32 := 0x00767613.
Lemma F_a6f20 : fetch_word PSEGS (0xa6f20 : word) = Some W_a6f20.
Proof. vm_refl. Qed.
Lemma D_a6f20 : decode_any W_a6f20 = Some (OpImm ALU_AND 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f24 : bv 32 := 0x00060a63.
Lemma F_a6f24 : fetch_word PSEGS (0xa6f24 : word) = Some W_a6f24.
Proof. vm_refl. Qed.
Lemma D_a6f24 : decode_any W_a6f24 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f28 : bv 32 := 0x0005c603.
Lemma F_a6f28 : fetch_word PSEGS (0xa6f28 : word) = Some W_a6f28.
Proof. vm_refl. Qed.
Lemma D_a6f28 : decode_any W_a6f28 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f2c : bv 32 := 0x00c50023.
Lemma F_a6f2c : fetch_word PSEGS (0xa6f2c : word) = Some W_a6f2c.
Proof. vm_refl. Qed.
Lemma D_a6f2c : decode_any W_a6f2c = Some (Store SZ1 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f30 : bv 32 := 0x08061263.
Lemma F_a6f30 : fetch_word PSEGS (0xa6f30 : word) = Some W_a6f30.
Proof. vm_refl. Qed.
Lemma D_a6f30 : decode_any W_a6f30 = Some (Branch BC_NE 12 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f34 : bv 32 := 0x0a40006f.
Lemma F_a6f34 : fetch_word PSEGS (0xa6f34 : word) = Some W_a6f34.
Proof. vm_refl. Qed.
Lemma D_a6f34 : decode_any W_a6f34 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f38 : bv 32 := 0x0075f613.
Lemma F_a6f38 : fetch_word PSEGS (0xa6f38 : word) = Some W_a6f38.
Proof. vm_refl. Qed.
Lemma D_a6f38 : decode_any W_a6f38 = Some (OpImm ALU_AND 12 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f3c : bv 32 := 0x02060463.
Lemma F_a6f3c : fetch_word PSEGS (0xa6f3c : word) = Some W_a6f3c.
Proof. vm_refl. Qed.
Lemma D_a6f3c : decode_any W_a6f3c = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f40 : bv 32 := 0x00158613.
Lemma F_a6f40 : fetch_word PSEGS (0xa6f40 : word) = Some W_a6f40.
Proof. vm_refl. Qed.
Lemma D_a6f40 : decode_any W_a6f40 = Some (OpImm ALU_ADD 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f44 : bv 32 := 0x0005c683.
Lemma F_a6f44 : fetch_word PSEGS (0xa6f44 : word) = Some W_a6f44.
Proof. vm_refl. Qed.
Lemma D_a6f44 : decode_any W_a6f44 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f48 : bv 32 := 0x00d50023.
Lemma F_a6f48 : fetch_word PSEGS (0xa6f48 : word) = Some W_a6f48.
Proof. vm_refl. Qed.
Lemma D_a6f48 : decode_any W_a6f48 = Some (Store SZ1 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f4c : bv 32 := 0x08068663.
Lemma F_a6f4c : fetch_word PSEGS (0xa6f4c : word) = Some W_a6f4c.
Proof. vm_refl. Qed.
Lemma D_a6f4c : decode_any W_a6f4c = Some (Branch BC_EQ 13 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f50 : bv 32 := 0x00158593.
Lemma F_a6f50 : fetch_word PSEGS (0xa6f50 : word) = Some W_a6f50.
Proof. vm_refl. Qed.
Lemma D_a6f50 : decode_any W_a6f50 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f54 : bv 32 := 0x00150513.
Lemma F_a6f54 : fetch_word PSEGS (0xa6f54 : word) = Some W_a6f54.
Proof. vm_refl. Qed.
Lemma D_a6f54 : decode_any W_a6f54 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f58 : bv 32 := 0x00767693.
Lemma F_a6f58 : fetch_word PSEGS (0xa6f58 : word) = Some W_a6f58.
Proof. vm_refl. Qed.
Lemma D_a6f58 : decode_any W_a6f58 = Some (OpImm ALU_AND 13 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f5c : bv 32 := 0x00160613.
Lemma F_a6f5c : fetch_word PSEGS (0xa6f5c : word) = Some W_a6f5c.
Proof. vm_refl. Qed.
Lemma D_a6f5c : decode_any W_a6f5c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f60 : bv 32 := 0xfe0692e3.
Lemma F_a6f60 : fetch_word PSEGS (0xa6f60 : word) = Some W_a6f60.
Proof. vm_refl. Qed.
Lemma D_a6f60 : decode_any W_a6f60 = Some (Branch BC_NE 13 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f64 : bv 32 := 0xfff6c617.
Lemma F_a6f64 : fetch_word PSEGS (0xa6f64 : word) = Some W_a6f64.
Proof. vm_refl. Qed.
Lemma D_a6f64 : decode_any W_a6f64 = Some (Auipc 12 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f68 : bv 32 := 0x42463683.
Lemma F_a6f68 : fetch_word PSEGS (0xa6f68 : word) = Some W_a6f68.
Proof. vm_refl. Qed.
Lemma D_a6f68 : decode_any W_a6f68 = Some (Load SZ8 true 13 12 1060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f6c : bv 32 := 0x0005b603.
Lemma F_a6f6c : fetch_word PSEGS (0xa6f6c : word) = Some W_a6f6c.
Proof. vm_refl. Qed.
Lemma D_a6f6c : decode_any W_a6f6c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f70 : bv 32 := 0xfff6c717.
Lemma F_a6f70 : fetch_word PSEGS (0xa6f70 : word) = Some W_a6f70.
Proof. vm_refl. Qed.
Lemma D_a6f70 : decode_any W_a6f70 = Some (Auipc 14 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f74 : bv 32 := 0x40873703.
Lemma F_a6f74 : fetch_word PSEGS (0xa6f74 : word) = Some W_a6f74.
Proof. vm_refl. Qed.
Lemma D_a6f74 : decode_any W_a6f74 = Some (Load SZ8 true 14 14 1032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f78 : bv 32 := 0x40c687b3.
Lemma F_a6f78 : fetch_word PSEGS (0xa6f78 : word) = Some W_a6f78.
Proof. vm_refl. Qed.
Lemma D_a6f78 : decode_any W_a6f78 = Some (Op ALU_SUB 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f7c : bv 32 := 0x00c7e7b3.
Lemma F_a6f7c : fetch_word PSEGS (0xa6f7c : word) = Some W_a6f7c.
Proof. vm_refl. Qed.
Lemma D_a6f7c : decode_any W_a6f7c = Some (Op ALU_OR 15 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f80 : bv 32 := 0x00e7f7b3.
Lemma F_a6f80 : fetch_word PSEGS (0xa6f80 : word) = Some W_a6f80.
Proof. vm_refl. Qed.
Lemma D_a6f80 : decode_any W_a6f80 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f84 : bv 32 := 0x02e79263.
Lemma F_a6f84 : fetch_word PSEGS (0xa6f84 : word) = Some W_a6f84.
Proof. vm_refl. Qed.
Lemma D_a6f84 : decode_any W_a6f84 = Some (Branch BC_NE 15 14 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f88 : bv 32 := 0x00c53023.
Lemma F_a6f88 : fetch_word PSEGS (0xa6f88 : word) = Some W_a6f88.
Proof. vm_refl. Qed.
Lemma D_a6f88 : decode_any W_a6f88 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f8c : bv 32 := 0x0085b603.
Lemma F_a6f8c : fetch_word PSEGS (0xa6f8c : word) = Some W_a6f8c.
Proof. vm_refl. Qed.
Lemma D_a6f8c : decode_any W_a6f8c = Some (Load SZ8 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f90 : bv 32 := 0x00858593.
Lemma F_a6f90 : fetch_word PSEGS (0xa6f90 : word) = Some W_a6f90.
Proof. vm_refl. Qed.
Lemma D_a6f90 : decode_any W_a6f90 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f94 : bv 32 := 0x40c687b3.
Lemma F_a6f94 : fetch_word PSEGS (0xa6f94 : word) = Some W_a6f94.
Proof. vm_refl. Qed.
Lemma D_a6f94 : decode_any W_a6f94 = Some (Op ALU_SUB 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f98 : bv 32 := 0x00c7e7b3.
Lemma F_a6f98 : fetch_word PSEGS (0xa6f98 : word) = Some W_a6f98.
Proof. vm_refl. Qed.
Lemma D_a6f98 : decode_any W_a6f98 = Some (Op ALU_OR 15 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6f9c : bv 32 := 0x00e7f7b3.
Lemma F_a6f9c : fetch_word PSEGS (0xa6f9c : word) = Some W_a6f9c.
Proof. vm_refl. Qed.
Lemma D_a6f9c : decode_any W_a6f9c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fa0 : bv 32 := 0x00850513.
Lemma F_a6fa0 : fetch_word PSEGS (0xa6fa0 : word) = Some W_a6fa0.
Proof. vm_refl. Qed.
Lemma D_a6fa0 : decode_any W_a6fa0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fa4 : bv 32 := 0xfee782e3.
Lemma F_a6fa4 : fetch_word PSEGS (0xa6fa4 : word) = Some W_a6fa4.
Proof. vm_refl. Qed.
Lemma D_a6fa4 : decode_any W_a6fa4 = Some (Branch BC_EQ 15 14 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fa8 : bv 32 := 0x0ff67613.
Lemma F_a6fa8 : fetch_word PSEGS (0xa6fa8 : word) = Some W_a6fa8.
Proof. vm_refl. Qed.
Lemma D_a6fa8 : decode_any W_a6fa8 = Some (OpImm ALU_AND 12 12 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fac : bv 32 := 0x00c50023.
Lemma F_a6fac : fetch_word PSEGS (0xa6fac : word) = Some W_a6fac.
Proof. vm_refl. Qed.
Lemma D_a6fac : decode_any W_a6fac = Some (Store SZ1 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fb0 : bv 32 := 0x02060463.
Lemma F_a6fb0 : fetch_word PSEGS (0xa6fb0 : word) = Some W_a6fb0.
Proof. vm_refl. Qed.
Lemma D_a6fb0 : decode_any W_a6fb0 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fb4 : bv 32 := 0x00158613.
Lemma F_a6fb4 : fetch_word PSEGS (0xa6fb4 : word) = Some W_a6fb4.
Proof. vm_refl. Qed.
Lemma D_a6fb4 : decode_any W_a6fb4 = Some (OpImm ALU_ADD 12 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fb8 : bv 32 := 0x00064683.
Lemma F_a6fb8 : fetch_word PSEGS (0xa6fb8 : word) = Some W_a6fb8.
Proof. vm_refl. Qed.
Lemma D_a6fb8 : decode_any W_a6fb8 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fbc : bv 32 := 0x00150593.
Lemma F_a6fbc : fetch_word PSEGS (0xa6fbc : word) = Some W_a6fbc.
Proof. vm_refl. Qed.
Lemma D_a6fbc : decode_any W_a6fbc = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fc0 : bv 32 := 0x00d500a3.
Lemma F_a6fc0 : fetch_word PSEGS (0xa6fc0 : word) = Some W_a6fc0.
Proof. vm_refl. Qed.
Lemma D_a6fc0 : decode_any W_a6fc0 = Some (Store SZ1 10 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fc4 : bv 32 := 0x00160613.
Lemma F_a6fc4 : fetch_word PSEGS (0xa6fc4 : word) = Some W_a6fc4.
Proof. vm_refl. Qed.
Lemma D_a6fc4 : decode_any W_a6fc4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fc8 : bv 32 := 0x00058513.
Lemma F_a6fc8 : fetch_word PSEGS (0xa6fc8 : word) = Some W_a6fc8.
Proof. vm_refl. Qed.
Lemma D_a6fc8 : decode_any W_a6fc8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fcc : bv 32 := 0xfe0696e3.
Lemma F_a6fcc : fetch_word PSEGS (0xa6fcc : word) = Some W_a6fcc.
Proof. vm_refl. Qed.
Lemma D_a6fcc : decode_any W_a6fcc = Some (Branch BC_NE 13 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fd0 : bv 32 := 0x00058513.
Lemma F_a6fd0 : fetch_word PSEGS (0xa6fd0 : word) = Some W_a6fd0.
Proof. vm_refl. Qed.
Lemma D_a6fd0 : decode_any W_a6fd0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fd4 : bv 32 := 0x00008067.
Lemma F_a6fd4 : fetch_word PSEGS (0xa6fd4 : word) = Some W_a6fd4.
Proof. vm_refl. Qed.
Lemma D_a6fd4 : decode_any W_a6fd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fd8 : bv 32 := 0x00008067.
Lemma F_a6fd8 : fetch_word PSEGS (0xa6fd8 : word) = Some W_a6fd8.
Proof. vm_refl. Qed.
Lemma D_a6fd8 : decode_any W_a6fd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fdc : bv 32 := 0xfb010113.
Lemma F_a6fdc : fetch_word PSEGS (0xa6fdc : word) = Some W_a6fdc.
Proof. vm_refl. Qed.
Lemma D_a6fdc : decode_any W_a6fdc = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fe0 : bv 32 := 0x04113423.
Lemma F_a6fe0 : fetch_word PSEGS (0xa6fe0 : word) = Some W_a6fe0.
Proof. vm_refl. Qed.
Lemma D_a6fe0 : decode_any W_a6fe0 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fe4 : bv 32 := 0x04813023.
Lemma F_a6fe4 : fetch_word PSEGS (0xa6fe4 : word) = Some W_a6fe4.
Proof. vm_refl. Qed.
Lemma D_a6fe4 : decode_any W_a6fe4 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fe8 : bv 32 := 0x02913c23.
Lemma F_a6fe8 : fetch_word PSEGS (0xa6fe8 : word) = Some W_a6fe8.
Proof. vm_refl. Qed.
Lemma D_a6fe8 : decode_any W_a6fe8 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6fec : bv 32 := 0x03213823.
Lemma F_a6fec : fetch_word PSEGS (0xa6fec : word) = Some W_a6fec.
Proof. vm_refl. Qed.
Lemma D_a6fec : decode_any W_a6fec = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ff0 : bv 32 := 0x03313423.
Lemma F_a6ff0 : fetch_word PSEGS (0xa6ff0 : word) = Some W_a6ff0.
Proof. vm_refl. Qed.
Lemma D_a6ff0 : decode_any W_a6ff0 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ff4 : bv 32 := 0x00058493.
Lemma F_a6ff4 : fetch_word PSEGS (0xa6ff4 : word) = Some W_a6ff4.
Proof. vm_refl. Qed.
Lemma D_a6ff4 : decode_any W_a6ff4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ff8 : bv 32 := 0x0000b597.
Lemma F_a6ff8 : fetch_word PSEGS (0xa6ff8 : word) = Some W_a6ff8.
Proof. vm_refl. Qed.
Lemma D_a6ff8 : decode_any W_a6ff8 = Some (Auipc 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a6ffc : bv 32 := 0xbb85b903.
Lemma F_a6ffc : fetch_word PSEGS (0xa6ffc : word) = Some W_a6ffc.
Proof. vm_refl. Qed.
Lemma D_a6ffc : decode_any W_a6ffc = Some (Load SZ8 true 18 11 3000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7000 : bv 32 := 0x00093583.
Lemma F_a7000 : fetch_word PSEGS (0xa7000 : word) = Some W_a7000.
Proof. vm_refl. Qed.
Lemma D_a7000 : decode_any W_a7000 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7004 : bv 32 := 0x02b13023.
Lemma F_a7004 : fetch_word PSEGS (0xa7004 : word) = Some W_a7004.
Proof. vm_refl. Qed.
Lemma D_a7004 : decode_any W_a7004 = Some (Store SZ8 2 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7008 : bv 32 := 0x0004c583.
Lemma F_a7008 : fetch_word PSEGS (0xa7008 : word) = Some W_a7008.
Proof. vm_refl. Qed.
Lemma D_a7008 : decode_any W_a7008 = Some (Load SZ1 false 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a700c : bv 32 := 0x00050413.
Lemma F_a700c : fetch_word PSEGS (0xa700c : word) = Some W_a700c.
Proof. vm_refl. Qed.
Lemma D_a700c : decode_any W_a700c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7010 : bv 32 := 0x08058e63.
Lemma F_a7010 : fetch_word PSEGS (0xa7010 : word) = Some W_a7010.
Proof. vm_refl. Qed.
Lemma D_a7010 : decode_any W_a7010 = Some (Branch BC_EQ 11 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7014 : bv 32 := 0x0014c503.
Lemma F_a7014 : fetch_word PSEGS (0xa7014 : word) = Some W_a7014.
Proof. vm_refl. Qed.
Lemma D_a7014 : decode_any W_a7014 = Some (Load SZ1 false 10 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7018 : bv 32 := 0x08050a63.
Lemma F_a7018 : fetch_word PSEGS (0xa7018 : word) = Some W_a7018.
Proof. vm_refl. Qed.
Lemma D_a7018 : decode_any W_a7018 = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a701c : bv 32 := 0x00010513.
Lemma F_a701c : fetch_word PSEGS (0xa701c : word) = Some W_a701c.
Proof. vm_refl. Qed.
Lemma D_a701c : decode_any W_a701c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7020 : bv 32 := 0x02000613.
Lemma F_a7020 : fetch_word PSEGS (0xa7020 : word) = Some W_a7020.
Proof. vm_refl. Qed.
Lemma D_a7020 : decode_any W_a7020 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7024 : bv 32 := 0x00010993.
Lemma F_a7024 : fetch_word PSEGS (0xa7024 : word) = Some W_a7024.
Proof. vm_refl. Qed.
Lemma D_a7024 : decode_any W_a7024 = Some (OpImm ALU_ADD 19 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7028 : bv 32 := 0x00000593.
Lemma F_a7028 : fetch_word PSEGS (0xa7028 : word) = Some W_a7028.
Proof. vm_refl. Qed.
Lemma D_a7028 : decode_any W_a7028 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a702c : bv 32 := 0xc7dff0ef.
Lemma F_a702c : fetch_word PSEGS (0xa702c : word) = Some W_a702c.
Proof. vm_refl. Qed.
Lemma D_a702c : decode_any W_a702c = Some (Jal 1 2096252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7030 : bv 32 := 0x0004c503.
Lemma F_a7030 : fetch_word PSEGS (0xa7030 : word) = Some W_a7030.
Proof. vm_refl. Qed.
Lemma D_a7030 : decode_any W_a7030 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7034 : bv 32 := 0x02050a63.
Lemma F_a7034 : fetch_word PSEGS (0xa7034 : word) = Some W_a7034.
Proof. vm_refl. Qed.
Lemma D_a7034 : decode_any W_a7034 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7038 : bv 32 := 0x00148493.
Lemma F_a7038 : fetch_word PSEGS (0xa7038 : word) = Some W_a7038.
Proof. vm_refl. Qed.
Lemma D_a7038 : decode_any W_a7038 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a703c : bv 32 := 0x00100593.
Lemma F_a703c : fetch_word PSEGS (0xa703c : word) = Some W_a703c.
Proof. vm_refl. Qed.
Lemma D_a703c : decode_any W_a703c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7040 : bv 32 := 0x00355613.
Lemma F_a7040 : fetch_word PSEGS (0xa7040 : word) = Some W_a7040.
Proof. vm_refl. Qed.
Lemma D_a7040 : decode_any W_a7040 = Some (ShiftImm ALU_SRL 12 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7044 : bv 32 := 0xff867613.
Lemma F_a7044 : fetch_word PSEGS (0xa7044 : word) = Some W_a7044.
Proof. vm_refl. Qed.
Lemma D_a7044 : decode_any W_a7044 = Some (OpImm ALU_AND 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7048 : bv 32 := 0x00c98633.
Lemma F_a7048 : fetch_word PSEGS (0xa7048 : word) = Some W_a7048.
Proof. vm_refl. Qed.
Lemma D_a7048 : decode_any W_a7048 = Some (Op ALU_ADD 12 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a704c : bv 32 := 0x00063683.
Lemma F_a704c : fetch_word PSEGS (0xa704c : word) = Some W_a704c.
Proof. vm_refl. Qed.
Lemma D_a704c : decode_any W_a704c = Some (Load SZ8 true 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7050 : bv 32 := 0x00a59733.
Lemma F_a7050 : fetch_word PSEGS (0xa7050 : word) = Some W_a7050.
Proof. vm_refl. Qed.
Lemma D_a7050 : decode_any W_a7050 = Some (Op ALU_SLL 14 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7054 : bv 32 := 0x0004c503.
Lemma F_a7054 : fetch_word PSEGS (0xa7054 : word) = Some W_a7054.
Proof. vm_refl. Qed.
Lemma D_a7054 : decode_any W_a7054 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7058 : bv 32 := 0x00e6e6b3.
Lemma F_a7058 : fetch_word PSEGS (0xa7058 : word) = Some W_a7058.
Proof. vm_refl. Qed.
Lemma D_a7058 : decode_any W_a7058 = Some (Op ALU_OR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a705c : bv 32 := 0x00d63023.
Lemma F_a705c : fetch_word PSEGS (0xa705c : word) = Some W_a705c.
Proof. vm_refl. Qed.
Lemma D_a705c : decode_any W_a705c = Some (Store SZ8 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7060 : bv 32 := 0x00148493.
Lemma F_a7060 : fetch_word PSEGS (0xa7060 : word) = Some W_a7060.
Proof. vm_refl. Qed.
Lemma D_a7060 : decode_any W_a7060 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7064 : bv 32 := 0xfc051ee3.
Lemma F_a7064 : fetch_word PSEGS (0xa7064 : word) = Some W_a7064.
Proof. vm_refl. Qed.
Lemma D_a7064 : decode_any W_a7064 = Some (Branch BC_NE 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7068 : bv 32 := 0x00044603.
Lemma F_a7068 : fetch_word PSEGS (0xa7068 : word) = Some W_a7068.
Proof. vm_refl. Qed.
Lemma D_a7068 : decode_any W_a7068 = Some (Load SZ1 false 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a706c : bv 32 := 0x00040513.
Lemma F_a706c : fetch_word PSEGS (0xa706c : word) = Some W_a706c.
Proof. vm_refl. Qed.
Lemma D_a706c : decode_any W_a706c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7070 : bv 32 := 0x04060263.
Lemma F_a7070 : fetch_word PSEGS (0xa7070 : word) = Some W_a7070.
Proof. vm_refl. Qed.
Lemma D_a7070 : decode_any W_a7070 = Some (Branch BC_EQ 12 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7074 : bv 32 := 0x00010593.
Lemma F_a7074 : fetch_word PSEGS (0xa7074 : word) = Some W_a7074.
Proof. vm_refl. Qed.
Lemma D_a7074 : decode_any W_a7074 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7078 : bv 32 := 0x00040693.
Lemma F_a7078 : fetch_word PSEGS (0xa7078 : word) = Some W_a7078.
Proof. vm_refl. Qed.
Lemma D_a7078 : decode_any W_a7078 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a707c : bv 32 := 0x00365513.
Lemma F_a707c : fetch_word PSEGS (0xa707c : word) = Some W_a707c.
Proof. vm_refl. Qed.
Lemma D_a707c : decode_any W_a707c = Some (ShiftImm ALU_SRL 10 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7080 : bv 32 := 0xff857513.
Lemma F_a7080 : fetch_word PSEGS (0xa7080 : word) = Some W_a7080.
Proof. vm_refl. Qed.
Lemma D_a7080 : decode_any W_a7080 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7084 : bv 32 := 0x00a58533.
Lemma F_a7084 : fetch_word PSEGS (0xa7084 : word) = Some W_a7084.
Proof. vm_refl. Qed.
Lemma D_a7084 : decode_any W_a7084 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7088 : bv 32 := 0x00053503.
Lemma F_a7088 : fetch_word PSEGS (0xa7088 : word) = Some W_a7088.
Proof. vm_refl. Qed.
Lemma D_a7088 : decode_any W_a7088 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a708c : bv 32 := 0x00c55533.
Lemma F_a708c : fetch_word PSEGS (0xa708c : word) = Some W_a708c.
Proof. vm_refl. Qed.
Lemma D_a708c : decode_any W_a708c = Some (Op ALU_SRL 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7090 : bv 32 := 0x00157513.
Lemma F_a7090 : fetch_word PSEGS (0xa7090 : word) = Some W_a7090.
Proof. vm_refl. Qed.
Lemma D_a7090 : decode_any W_a7090 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7094 : bv 32 := 0x04051663.
Lemma F_a7094 : fetch_word PSEGS (0xa7094 : word) = Some W_a7094.
Proof. vm_refl. Qed.
Lemma D_a7094 : decode_any W_a7094 = Some (Branch BC_NE 10 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7098 : bv 32 := 0x0016c603.
Lemma F_a7098 : fetch_word PSEGS (0xa7098 : word) = Some W_a7098.
Proof. vm_refl. Qed.
Lemma D_a7098 : decode_any W_a7098 = Some (Load SZ1 false 12 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a709c : bv 32 := 0x00168513.
Lemma F_a709c : fetch_word PSEGS (0xa709c : word) = Some W_a709c.
Proof. vm_refl. Qed.
Lemma D_a709c : decode_any W_a709c = Some (OpImm ALU_ADD 10 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70a0 : bv 32 := 0x00050693.
Lemma F_a70a0 : fetch_word PSEGS (0xa70a0 : word) = Some W_a70a0.
Proof. vm_refl. Qed.
Lemma D_a70a0 : decode_any W_a70a0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70a4 : bv 32 := 0xfc061ce3.
Lemma F_a70a4 : fetch_word PSEGS (0xa70a4 : word) = Some W_a70a4.
Proof. vm_refl. Qed.
Lemma D_a70a4 : decode_any W_a70a4 = Some (Branch BC_NE 12 0 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70a8 : bv 32 := 0x00c0006f.
Lemma F_a70a8 : fetch_word PSEGS (0xa70a8 : word) = Some W_a70a8.
Proof. vm_refl. Qed.
Lemma D_a70a8 : decode_any W_a70a8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70ac : bv 32 := 0x00040513.
Lemma F_a70ac : fetch_word PSEGS (0xa70ac : word) = Some W_a70ac.
Proof. vm_refl. Qed.
Lemma D_a70ac : decode_any W_a70ac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70b0 : bv 32 := 0xd2dff0ef.
Lemma F_a70b0 : fetch_word PSEGS (0xa70b0 : word) = Some W_a70b0.
Proof. vm_refl. Qed.
Lemma D_a70b0 : decode_any W_a70b0 = Some (Jal 1 2096428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70b4 : bv 32 := 0x00093583.
Lemma F_a70b4 : fetch_word PSEGS (0xa70b4 : word) = Some W_a70b4.
Proof. vm_refl. Qed.
Lemma D_a70b4 : decode_any W_a70b4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70b8 : bv 32 := 0x02013603.
Lemma F_a70b8 : fetch_word PSEGS (0xa70b8 : word) = Some W_a70b8.
Proof. vm_refl. Qed.
Lemma D_a70b8 : decode_any W_a70b8 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70bc : bv 32 := 0x02c59a63.
Lemma F_a70bc : fetch_word PSEGS (0xa70bc : word) = Some W_a70bc.
Proof. vm_refl. Qed.
Lemma D_a70bc : decode_any W_a70bc = Some (Branch BC_NE 11 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70c0 : bv 32 := 0x40850533.
Lemma F_a70c0 : fetch_word PSEGS (0xa70c0 : word) = Some W_a70c0.
Proof. vm_refl. Qed.
Lemma D_a70c0 : decode_any W_a70c0 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70c4 : bv 32 := 0x04813083.
Lemma F_a70c4 : fetch_word PSEGS (0xa70c4 : word) = Some W_a70c4.
Proof. vm_refl. Qed.
Lemma D_a70c4 : decode_any W_a70c4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70c8 : bv 32 := 0x04013403.
Lemma F_a70c8 : fetch_word PSEGS (0xa70c8 : word) = Some W_a70c8.
Proof. vm_refl. Qed.
Lemma D_a70c8 : decode_any W_a70c8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70cc : bv 32 := 0x03813483.
Lemma F_a70cc : fetch_word PSEGS (0xa70cc : word) = Some W_a70cc.
Proof. vm_refl. Qed.
Lemma D_a70cc : decode_any W_a70cc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70d0 : bv 32 := 0x03013903.
Lemma F_a70d0 : fetch_word PSEGS (0xa70d0 : word) = Some W_a70d0.
Proof. vm_refl. Qed.
Lemma D_a70d0 : decode_any W_a70d0 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70d4 : bv 32 := 0x02813983.
Lemma F_a70d4 : fetch_word PSEGS (0xa70d4 : word) = Some W_a70d4.
Proof. vm_refl. Qed.
Lemma D_a70d4 : decode_any W_a70d4 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70d8 : bv 32 := 0x05010113.
Lemma F_a70d8 : fetch_word PSEGS (0xa70d8 : word) = Some W_a70d8.
Proof. vm_refl. Qed.
Lemma D_a70d8 : decode_any W_a70d8 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70dc : bv 32 := 0x00008067.
Lemma F_a70dc : fetch_word PSEGS (0xa70dc : word) = Some W_a70dc.
Proof. vm_refl. Qed.
Lemma D_a70dc : decode_any W_a70dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70e0 : bv 32 := 0x00068513.
Lemma F_a70e0 : fetch_word PSEGS (0xa70e0 : word) = Some W_a70e0.
Proof. vm_refl. Qed.
Lemma D_a70e0 : decode_any W_a70e0 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70e4 : bv 32 := 0x00093583.
Lemma F_a70e4 : fetch_word PSEGS (0xa70e4 : word) = Some W_a70e4.
Proof. vm_refl. Qed.
Lemma D_a70e4 : decode_any W_a70e4 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70e8 : bv 32 := 0x02013603.
Lemma F_a70e8 : fetch_word PSEGS (0xa70e8 : word) = Some W_a70e8.
Proof. vm_refl. Qed.
Lemma D_a70e8 : decode_any W_a70e8 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70ec : bv 32 := 0xfcc58ae3.
Lemma F_a70ec : fetch_word PSEGS (0xa70ec : word) = Some W_a70ec.
Proof. vm_refl. Qed.
Lemma D_a70ec : decode_any W_a70ec = Some (Branch BC_EQ 11 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70f0 : bv 32 := 0x95cef0ef.
Lemma F_a70f0 : fetch_word PSEGS (0xa70f0 : word) = Some W_a70f0.
Proof. vm_refl. Qed.
Lemma D_a70f0 : decode_any W_a70f0 = Some (Jal 1 2027868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70f4 : bv 32 := 0x00757593.
Lemma F_a70f4 : fetch_word PSEGS (0xa70f4 : word) = Some W_a70f4.
Proof. vm_refl. Qed.
Lemma D_a70f4 : decode_any W_a70f4 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70f8 : bv 32 := 0x00050613.
Lemma F_a70f8 : fetch_word PSEGS (0xa70f8 : word) = Some W_a70f8.
Proof. vm_refl. Qed.
Lemma D_a70f8 : decode_any W_a70f8 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a70fc : bv 32 := 0x02058a63.
Lemma F_a70fc : fetch_word PSEGS (0xa70fc : word) = Some W_a70fc.
Proof. vm_refl. Qed.
Lemma D_a70fc : decode_any W_a70fc = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7100 : bv 32 := 0x00054583.
Lemma F_a7100 : fetch_word PSEGS (0xa7100 : word) = Some W_a7100.
Proof. vm_refl. Qed.
Lemma D_a7100 : decode_any W_a7100 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7104 : bv 32 := 0x06058c63.
Lemma F_a7104 : fetch_word PSEGS (0xa7104 : word) = Some W_a7104.
Proof. vm_refl. Qed.
Lemma D_a7104 : decode_any W_a7104 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7108 : bv 32 := 0x00150613.
Lemma F_a7108 : fetch_word PSEGS (0xa7108 : word) = Some W_a7108.
Proof. vm_refl. Qed.
Lemma D_a7108 : decode_any W_a7108 = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a710c : bv 32 := 0x00050593.
Lemma F_a710c : fetch_word PSEGS (0xa710c : word) = Some W_a710c.
Proof. vm_refl. Qed.
Lemma D_a710c : decode_any W_a710c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7110 : bv 32 := 0x00158693.
Lemma F_a7110 : fetch_word PSEGS (0xa7110 : word) = Some W_a7110.
Proof. vm_refl. Qed.
Lemma D_a7110 : decode_any W_a7110 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7114 : bv 32 := 0x0076f693.
Lemma F_a7114 : fetch_word PSEGS (0xa7114 : word) = Some W_a7114.
Proof. vm_refl. Qed.
Lemma D_a7114 : decode_any W_a7114 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7118 : bv 32 := 0x00068c63.
Lemma F_a7118 : fetch_word PSEGS (0xa7118 : word) = Some W_a7118.
Proof. vm_refl. Qed.
Lemma D_a7118 : decode_any W_a7118 = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a711c : bv 32 := 0x00064683.
Lemma F_a711c : fetch_word PSEGS (0xa711c : word) = Some W_a711c.
Proof. vm_refl. Qed.
Lemma D_a711c : decode_any W_a711c = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7120 : bv 32 := 0x00160613.
Lemma F_a7120 : fetch_word PSEGS (0xa7120 : word) = Some W_a7120.
Proof. vm_refl. Qed.
Lemma D_a7120 : decode_any W_a7120 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7124 : bv 32 := 0x00158593.
Lemma F_a7124 : fetch_word PSEGS (0xa7124 : word) = Some W_a7124.
Proof. vm_refl. Qed.
Lemma D_a7124 : decode_any W_a7124 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7128 : bv 32 := 0xfe0694e3.
Lemma F_a7128 : fetch_word PSEGS (0xa7128 : word) = Some W_a7128.
Proof. vm_refl. Qed.
Lemma D_a7128 : decode_any W_a7128 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a712c : bv 32 := 0x0480006f.
Lemma F_a712c : fetch_word PSEGS (0xa712c : word) = Some W_a712c.
Proof. vm_refl. Qed.
Lemma D_a712c : decode_any W_a712c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7130 : bv 32 := 0xfff6c597.
Lemma F_a7130 : fetch_word PSEGS (0xa7130 : word) = Some W_a7130.
Proof. vm_refl. Qed.
Lemma D_a7130 : decode_any W_a7130 = Some (Auipc 11 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7134 : bv 32 := 0xfff6c717.
Lemma F_a7134 : fetch_word PSEGS (0xa7134 : word) = Some W_a7134.
Proof. vm_refl. Qed.
Lemma D_a7134 : decode_any W_a7134 = Some (Auipc 14 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7138 : bv 32 := 0x2585b683.
Lemma F_a7138 : fetch_word PSEGS (0xa7138 : word) = Some W_a7138.
Proof. vm_refl. Qed.
Lemma D_a7138 : decode_any W_a7138 = Some (Load SZ8 true 13 11 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a713c : bv 32 := 0x24473703.
Lemma F_a713c : fetch_word PSEGS (0xa713c : word) = Some W_a713c.
Proof. vm_refl. Qed.
Lemma D_a713c : decode_any W_a713c = Some (Load SZ8 true 14 14 580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7140 : bv 32 := 0xff760593.
Lemma F_a7140 : fetch_word PSEGS (0xa7140 : word) = Some W_a7140.
Proof. vm_refl. Qed.
Lemma D_a7140 : decode_any W_a7140 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7144 : bv 32 := 0xff860613.
Lemma F_a7144 : fetch_word PSEGS (0xa7144 : word) = Some W_a7144.
Proof. vm_refl. Qed.
Lemma D_a7144 : decode_any W_a7144 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7148 : bv 32 := 0x00863783.
Lemma F_a7148 : fetch_word PSEGS (0xa7148 : word) = Some W_a7148.
Proof. vm_refl. Qed.
Lemma D_a7148 : decode_any W_a7148 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a714c : bv 32 := 0x00860613.
Lemma F_a714c : fetch_word PSEGS (0xa714c : word) = Some W_a714c.
Proof. vm_refl. Qed.
Lemma D_a714c : decode_any W_a714c = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7150 : bv 32 := 0x40f68833.
Lemma F_a7150 : fetch_word PSEGS (0xa7150 : word) = Some W_a7150.
Proof. vm_refl. Qed.
Lemma D_a7150 : decode_any W_a7150 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7154 : bv 32 := 0x00f867b3.
Lemma F_a7154 : fetch_word PSEGS (0xa7154 : word) = Some W_a7154.
Proof. vm_refl. Qed.
Lemma D_a7154 : decode_any W_a7154 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7158 : bv 32 := 0x00e7f7b3.
Lemma F_a7158 : fetch_word PSEGS (0xa7158 : word) = Some W_a7158.
Proof. vm_refl. Qed.
Lemma D_a7158 : decode_any W_a7158 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a715c : bv 32 := 0x00858593.
Lemma F_a715c : fetch_word PSEGS (0xa715c : word) = Some W_a715c.
Proof. vm_refl. Qed.
Lemma D_a715c : decode_any W_a715c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7160 : bv 32 := 0xfee784e3.
Lemma F_a7160 : fetch_word PSEGS (0xa7160 : word) = Some W_a7160.
Proof. vm_refl. Qed.
Lemma D_a7160 : decode_any W_a7160 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7164 : bv 32 := 0x00064683.
Lemma F_a7164 : fetch_word PSEGS (0xa7164 : word) = Some W_a7164.
Proof. vm_refl. Qed.
Lemma D_a7164 : decode_any W_a7164 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7168 : bv 32 := 0x00160613.
Lemma F_a7168 : fetch_word PSEGS (0xa7168 : word) = Some W_a7168.
Proof. vm_refl. Qed.
Lemma D_a7168 : decode_any W_a7168 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a716c : bv 32 := 0x00158593.
Lemma F_a716c : fetch_word PSEGS (0xa716c : word) = Some W_a716c.
Proof. vm_refl. Qed.
Lemma D_a716c : decode_any W_a716c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7170 : bv 32 := 0xfe069ae3.
Lemma F_a7170 : fetch_word PSEGS (0xa7170 : word) = Some W_a7170.
Proof. vm_refl. Qed.
Lemma D_a7170 : decode_any W_a7170 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7174 : bv 32 := 0x40a58533.
Lemma F_a7174 : fetch_word PSEGS (0xa7174 : word) = Some W_a7174.
Proof. vm_refl. Qed.
Lemma D_a7174 : decode_any W_a7174 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7178 : bv 32 := 0x00008067.
Lemma F_a7178 : fetch_word PSEGS (0xa7178 : word) = Some W_a7178.
Proof. vm_refl. Qed.
Lemma D_a7178 : decode_any W_a7178 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a717c : bv 32 := 0x40a50533.
Lemma F_a717c : fetch_word PSEGS (0xa717c : word) = Some W_a717c.
Proof. vm_refl. Qed.
Lemma D_a717c : decode_any W_a717c = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7180 : bv 32 := 0x00008067.
Lemma F_a7180 : fetch_word PSEGS (0xa7180 : word) = Some W_a7180.
Proof. vm_refl. Qed.
Lemma D_a7180 : decode_any W_a7180 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7184 : bv 32 := 0xfe010113.
Lemma F_a7184 : fetch_word PSEGS (0xa7184 : word) = Some W_a7184.
Proof. vm_refl. Qed.
Lemma D_a7184 : decode_any W_a7184 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7188 : bv 32 := 0x00113c23.
Lemma F_a7188 : fetch_word PSEGS (0xa7188 : word) = Some W_a7188.
Proof. vm_refl. Qed.
Lemma D_a7188 : decode_any W_a7188 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a718c : bv 32 := 0x00813823.
Lemma F_a718c : fetch_word PSEGS (0xa718c : word) = Some W_a718c.
Proof. vm_refl. Qed.
Lemma D_a718c : decode_any W_a718c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7190 : bv 32 := 0x00913423.
Lemma F_a7190 : fetch_word PSEGS (0xa7190 : word) = Some W_a7190.
Proof. vm_refl. Qed.
Lemma D_a7190 : decode_any W_a7190 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7194 : bv 32 := 0x00058413.
Lemma F_a7194 : fetch_word PSEGS (0xa7194 : word) = Some W_a7194.
Proof. vm_refl. Qed.
Lemma D_a7194 : decode_any W_a7194 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7198 : bv 32 := 0x00050493.
Lemma F_a7198 : fetch_word PSEGS (0xa7198 : word) = Some W_a7198.
Proof. vm_refl. Qed.
Lemma D_a7198 : decode_any W_a7198 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a719c : bv 32 := 0x00000593.
Lemma F_a719c : fetch_word PSEGS (0xa719c : word) = Some W_a719c.
Proof. vm_refl. Qed.
Lemma D_a719c : decode_any W_a719c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71a0 : bv 32 := 0x00040613.
Lemma F_a71a0 : fetch_word PSEGS (0xa71a0 : word) = Some W_a71a0.
Proof. vm_refl. Qed.
Lemma D_a71a0 : decode_any W_a71a0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71a4 : bv 32 := 0xc88ff0ef.
Lemma F_a71a4 : fetch_word PSEGS (0xa71a4 : word) = Some W_a71a4.
Proof. vm_refl. Qed.
Lemma D_a71a4 : decode_any W_a71a4 = Some (Jal 1 2094216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71a8 : bv 32 := 0x00050463.
Lemma F_a71a8 : fetch_word PSEGS (0xa71a8 : word) = Some W_a71a8.
Proof. vm_refl. Qed.
Lemma D_a71a8 : decode_any W_a71a8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71ac : bv 32 := 0x40950433.
Lemma F_a71ac : fetch_word PSEGS (0xa71ac : word) = Some W_a71ac.
Proof. vm_refl. Qed.
Lemma D_a71ac : decode_any W_a71ac = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71b0 : bv 32 := 0x00040513.
Lemma F_a71b0 : fetch_word PSEGS (0xa71b0 : word) = Some W_a71b0.
Proof. vm_refl. Qed.
Lemma D_a71b0 : decode_any W_a71b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71b4 : bv 32 := 0x01813083.
Lemma F_a71b4 : fetch_word PSEGS (0xa71b4 : word) = Some W_a71b4.
Proof. vm_refl. Qed.
Lemma D_a71b4 : decode_any W_a71b4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.
