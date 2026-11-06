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
Definition W_1968c : bv 32 := 0x00058463.
Lemma F_1968c : fetch_word Plain.M.loaded_segments (0x196e4 : word) = Some W_1968c.
Proof. vm_refl. Qed.
Lemma D_1968c : decode_any W_1968c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19690 : bv 32 := 0x0005a023.
Lemma F_19690 : fetch_word Plain.M.loaded_segments (0x196e8 : word) = Some W_19690.
Proof. vm_refl. Qed.
Lemma D_19690 : decode_any W_19690 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19694 : bv 32 := 0x00060463.
Lemma F_19694 : fetch_word Plain.M.loaded_segments (0x196ec : word) = Some W_19694.
Proof. vm_refl. Qed.
Lemma D_19694 : decode_any W_19694 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19698 : bv 32 := 0x00062023.
Lemma F_19698 : fetch_word Plain.M.loaded_segments (0x196f0 : word) = Some W_19698.
Proof. vm_refl. Qed.
Lemma D_19698 : decode_any W_19698 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1969c : bv 32 := 0x00068463.
Lemma F_1969c : fetch_word Plain.M.loaded_segments (0x196f4 : word) = Some W_1969c.
Proof. vm_refl. Qed.
Lemma D_1969c : decode_any W_1969c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a4 : bv 32 := 0x02050a63.
Lemma F_196a4 : fetch_word Plain.M.loaded_segments (0x196fc : word) = Some W_196a4.
Proof. vm_refl. Qed.
Lemma D_196a4 : decode_any W_196a4 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196a8 : bv 32 := 0x00058663.
Lemma F_196a8 : fetch_word Plain.M.loaded_segments (0x19700 : word) = Some W_196a8.
Proof. vm_refl. Qed.
Lemma D_196a8 : decode_any W_196a8 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196ac : bv 32 := 0x00052703.
Lemma F_196ac : fetch_word Plain.M.loaded_segments (0x19704 : word) = Some W_196ac.
Proof. vm_refl. Qed.
Lemma D_196ac : decode_any W_196ac = Some (Load SZ4 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b0 : bv 32 := 0x00e5a023.
Lemma F_196b0 : fetch_word Plain.M.loaded_segments (0x19708 : word) = Some W_196b0.
Proof. vm_refl. Qed.
Lemma D_196b0 : decode_any W_196b0 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b4 : bv 32 := 0x00060663.
Lemma F_196b4 : fetch_word Plain.M.loaded_segments (0x1970c : word) = Some W_196b4.
Proof. vm_refl. Qed.
Lemma D_196b4 : decode_any W_196b4 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196b8 : bv 32 := 0x00452583.
Lemma F_196b8 : fetch_word Plain.M.loaded_segments (0x19710 : word) = Some W_196b8.
Proof. vm_refl. Qed.
Lemma D_196b8 : decode_any W_196b8 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196bc : bv 32 := 0x00b62023.
Lemma F_196bc : fetch_word Plain.M.loaded_segments (0x19714 : word) = Some W_196bc.
Proof. vm_refl. Qed.
Lemma D_196bc : decode_any W_196bc = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c0 : bv 32 := 0x00000593.
Lemma F_196c0 : fetch_word Plain.M.loaded_segments (0x19718 : word) = Some W_196c0.
Proof. vm_refl. Qed.
Lemma D_196c0 : decode_any W_196c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196c4 : bv 32 := 0x00068663.
Lemma F_196c4 : fetch_word Plain.M.loaded_segments (0x1971c : word) = Some W_196c4.
Proof. vm_refl. Qed.
Lemma D_196c4 : decode_any W_196c4 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d0 : bv 32 := 0x00058513.
Lemma F_196d0 : fetch_word Plain.M.loaded_segments (0x19728 : word) = Some W_196d0.
Proof. vm_refl. Qed.
Lemma D_196d0 : decode_any W_196d0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_196d4 : bv 32 := 0x00008067.
Lemma F_196d4 : fetch_word Plain.M.loaded_segments (0x1972c : word) = Some W_196d4.
Proof. vm_refl. Qed.
Lemma D_196d4 : decode_any W_196d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6bc : bv 32 := 0xfa010113.
Lemma F_1b6bc : fetch_word Plain.M.loaded_segments (0x1b714 : word) = Some W_1b6bc.
Proof. vm_refl. Qed.
Lemma D_1b6bc : decode_any W_1b6bc = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6c0 : bv 32 := 0x04113c23.
Lemma F_1b6c0 : fetch_word Plain.M.loaded_segments (0x1b718 : word) = Some W_1b6c0.
Proof. vm_refl. Qed.
Lemma D_1b6c0 : decode_any W_1b6c0 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6c4 : bv 32 := 0x04813823.
Lemma F_1b6c4 : fetch_word Plain.M.loaded_segments (0x1b71c : word) = Some W_1b6c4.
Proof. vm_refl. Qed.
Lemma D_1b6c4 : decode_any W_1b6c4 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6c8 : bv 32 := 0x04913423.
Lemma F_1b6c8 : fetch_word Plain.M.loaded_segments (0x1b720 : word) = Some W_1b6c8.
Proof. vm_refl. Qed.
Lemma D_1b6c8 : decode_any W_1b6c8 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6cc : bv 32 := 0x05213023.
Lemma F_1b6cc : fetch_word Plain.M.loaded_segments (0x1b724 : word) = Some W_1b6cc.
Proof. vm_refl. Qed.
Lemma D_1b6cc : decode_any W_1b6cc = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6d0 : bv 32 := 0x03313c23.
Lemma F_1b6d0 : fetch_word Plain.M.loaded_segments (0x1b728 : word) = Some W_1b6d0.
Proof. vm_refl. Qed.
Lemma D_1b6d0 : decode_any W_1b6d0 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6d4 : bv 32 := 0x03413823.
Lemma F_1b6d4 : fetch_word Plain.M.loaded_segments (0x1b72c : word) = Some W_1b6d4.
Proof. vm_refl. Qed.
Lemma D_1b6d4 : decode_any W_1b6d4 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6d8 : bv 32 := 0x03513423.
Lemma F_1b6d8 : fetch_word Plain.M.loaded_segments (0x1b730 : word) = Some W_1b6d8.
Proof. vm_refl. Qed.
Lemma D_1b6d8 : decode_any W_1b6d8 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6dc : bv 32 := 0x03613023.
Lemma F_1b6dc : fetch_word Plain.M.loaded_segments (0x1b734 : word) = Some W_1b6dc.
Proof. vm_refl. Qed.
Lemma D_1b6dc : decode_any W_1b6dc = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6e0 : bv 32 := 0x01713c23.
Lemma F_1b6e0 : fetch_word Plain.M.loaded_segments (0x1b738 : word) = Some W_1b6e0.
Proof. vm_refl. Qed.
Lemma D_1b6e0 : decode_any W_1b6e0 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6e4 : bv 32 := 0x1a050a63.
Lemma F_1b6e4 : fetch_word Plain.M.loaded_segments (0x1b73c : word) = Some W_1b6e4.
Proof. vm_refl. Qed.
Lemma D_1b6e4 : decode_any W_1b6e4 = Some (Branch BC_EQ 10 0 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6e8 : bv 32 := 0x00070913.
Lemma F_1b6e8 : fetch_word Plain.M.loaded_segments (0x1b740 : word) = Some W_1b6e8.
Proof. vm_refl. Qed.
Lemma D_1b6e8 : decode_any W_1b6e8 = Some (OpImm ALU_ADD 18 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6ec : bv 32 := 0x00068413.
Lemma F_1b6ec : fetch_word Plain.M.loaded_segments (0x1b744 : word) = Some W_1b6ec.
Proof. vm_refl. Qed.
Lemma D_1b6ec : decode_any W_1b6ec = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6f0 : bv 32 := 0x00060a13.
Lemma F_1b6f0 : fetch_word Plain.M.loaded_segments (0x1b748 : word) = Some W_1b6f0.
Proof. vm_refl. Qed.
Lemma D_1b6f0 : decode_any W_1b6f0 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6f4 : bv 32 := 0x00058993.
Lemma F_1b6f4 : fetch_word Plain.M.loaded_segments (0x1b74c : word) = Some W_1b6f4.
Proof. vm_refl. Qed.
Lemma D_1b6f4 : decode_any W_1b6f4 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6f8 : bv 32 := 0x01410593.
Lemma F_1b6f8 : fetch_word Plain.M.loaded_segments (0x1b750 : word) = Some W_1b6f8.
Proof. vm_refl. Qed.
Lemma D_1b6f8 : decode_any W_1b6f8 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6fc : bv 32 := 0x01010613.
Lemma F_1b6fc : fetch_word Plain.M.loaded_segments (0x1b754 : word) = Some W_1b6fc.
Proof. vm_refl. Qed.
Lemma D_1b6fc : decode_any W_1b6fc = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b700 : bv 32 := 0x00050493.
Lemma F_1b700 : fetch_word Plain.M.loaded_segments (0x1b758 : word) = Some W_1b700.
Proof. vm_refl. Qed.
Lemma D_1b700 : decode_any W_1b700 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b704 : bv 32 := 0x00000693.
Lemma F_1b704 : fetch_word Plain.M.loaded_segments (0x1b75c : word) = Some W_1b704.
Proof. vm_refl. Qed.
Lemma D_1b704 : decode_any W_1b704 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b708 : bv 32 := 0xf85fd0ef.
Lemma F_1b708 : fetch_word Plain.M.loaded_segments (0x1b760 : word) = Some W_1b708.
Proof. vm_refl. Qed.
Lemma D_1b708 : decode_any W_1b708 = Some (Jal 1 2088836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b70c : bv 32 := 0x01412503.
Lemma F_1b70c : fetch_word Plain.M.loaded_segments (0x1b764 : word) = Some W_1b70c.
Proof. vm_refl. Qed.
Lemma D_1b70c : decode_any W_1b70c = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b710 : bv 32 := 0x15354a63.
Lemma F_1b710 : fetch_word Plain.M.loaded_segments (0x1b768 : word) = Some W_1b710.
Proof. vm_refl. Qed.
Lemma D_1b710 : decode_any W_1b710 = Some (Branch BC_LT 10 19 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b714 : bv 32 := 0x15454863.
Lemma F_1b714 : fetch_word Plain.M.loaded_segments (0x1b76c : word) = Some W_1b714.
Proof. vm_refl. Qed.
Lemma D_1b714 : decode_any W_1b714 = Some (Branch BC_LT 10 20 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b718 : bv 32 := 0x01012503.
Lemma F_1b718 : fetch_word Plain.M.loaded_segments (0x1b770 : word) = Some W_1b718.
Proof. vm_refl. Qed.
Lemma D_1b718 : decode_any W_1b718 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b71c : bv 32 := 0x14854463.
Lemma F_1b71c : fetch_word Plain.M.loaded_segments (0x1b774 : word) = Some W_1b71c.
Proof. vm_refl. Qed.
Lemma D_1b71c : decode_any W_1b71c = Some (Branch BC_LT 10 8 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b720 : bv 32 := 0x15254263.
Lemma F_1b720 : fetch_word Plain.M.loaded_segments (0x1b778 : word) = Some W_1b720.
Proof. vm_refl. Qed.
Lemma D_1b720 : decode_any W_1b720 = Some (Branch BC_LT 10 18 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b724 : bv 32 := 0x00048513.
Lemma F_1b724 : fetch_word Plain.M.loaded_segments (0x1b77c : word) = Some W_1b724.
Proof. vm_refl. Qed.
Lemma D_1b724 : decode_any W_1b724 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b728 : bv 32 := 0x00098593.
Lemma F_1b728 : fetch_word Plain.M.loaded_segments (0x1b780 : word) = Some W_1b728.
Proof. vm_refl. Qed.
Lemma D_1b728 : decode_any W_1b728 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b72c : bv 32 := 0x000a0613.
Lemma F_1b72c : fetch_word Plain.M.loaded_segments (0x1b784 : word) = Some W_1b72c.
Proof. vm_refl. Qed.
Lemma D_1b72c : decode_any W_1b72c = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b730 : bv 32 := 0x00040693.
Lemma F_1b730 : fetch_word Plain.M.loaded_segments (0x1b788 : word) = Some W_1b730.
Proof. vm_refl. Qed.
Lemma D_1b730 : decode_any W_1b730 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b734 : bv 32 := 0x00090713.
Lemma F_1b734 : fetch_word Plain.M.loaded_segments (0x1b78c : word) = Some W_1b734.
Proof. vm_refl. Qed.
Lemma D_1b734 : decode_any W_1b734 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b738 : bv 32 := 0x00000793.
Lemma F_1b738 : fetch_word Plain.M.loaded_segments (0x1b790 : word) = Some W_1b738.
Proof. vm_refl. Qed.
Lemma D_1b738 : decode_any W_1b738 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b73c : bv 32 := 0xcc5ff0ef.
Lemma F_1b73c : fetch_word Plain.M.loaded_segments (0x1b794 : word) = Some W_1b73c.
Proof. vm_refl. Qed.
Lemma D_1b73c : decode_any W_1b73c = Some (Jal 1 2096324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b740 : bv 32 := 0x00050493.
Lemma F_1b740 : fetch_word Plain.M.loaded_segments (0x1b798 : word) = Some W_1b740.
Proof. vm_refl. Qed.
Lemma D_1b740 : decode_any W_1b740 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b744 : bv 32 := 0x05305263.
Lemma F_1b744 : fetch_word Plain.M.loaded_segments (0x1b79c : word) = Some W_1b744.
Proof. vm_refl. Qed.
Lemma D_1b744 : decode_any W_1b744 = Some (Branch BC_GE 0 19 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b748 : bv 32 := 0xfff98a9b.
Lemma F_1b748 : fetch_word Plain.M.loaded_segments (0x1b7a0 : word) = Some W_1b748.
Proof. vm_refl. Qed.
Lemma D_1b748 : decode_any W_1b748 = Some (OpImm32 21 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b74c : bv 32 := 0xfff00b93.
Lemma F_1b74c : fetch_word Plain.M.loaded_segments (0x1b7a4 : word) = Some W_1b74c.
Proof. vm_refl. Qed.
Lemma D_1b74c : decode_any W_1b74c = Some (OpImm ALU_ADD 23 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b750 : bv 32 := 0x00098b13.
Lemma F_1b750 : fetch_word Plain.M.loaded_segments (0x1b7a8 : word) = Some W_1b750.
Proof. vm_refl. Qed.
Lemma D_1b750 : decode_any W_1b750 = Some (OpImm ALU_ADD 22 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b754 : bv 32 := 0x01012703.
Lemma F_1b754 : fetch_word Plain.M.loaded_segments (0x1b7ac : word) = Some W_1b754.
Proof. vm_refl. Qed.
Lemma D_1b754 : decode_any W_1b754 = Some (Load SZ4 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b758 : bv 32 := 0x00100693.
Lemma F_1b758 : fetch_word Plain.M.loaded_segments (0x1b7b0 : word) = Some W_1b758.
Proof. vm_refl. Qed.
Lemma D_1b758 : decode_any W_1b758 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b75c : bv 32 := 0x00c00793.
Lemma F_1b75c : fetch_word Plain.M.loaded_segments (0x1b7b4 : word) = Some W_1b75c.
Proof. vm_refl. Qed.
Lemma D_1b75c : decode_any W_1b75c = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b760 : bv 32 := 0x00813023.
Lemma F_1b760 : fetch_word Plain.M.loaded_segments (0x1b7b8 : word) = Some W_1b760.
Proof. vm_refl. Qed.
Lemma D_1b760 : decode_any W_1b760 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b764 : bv 32 := 0x00048513.
Lemma F_1b764 : fetch_word Plain.M.loaded_segments (0x1b7bc : word) = Some W_1b764.
Proof. vm_refl. Qed.
Lemma D_1b764 : decode_any W_1b764 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b768 : bv 32 := 0x000a8593.
Lemma F_1b768 : fetch_word Plain.M.loaded_segments (0x1b7c0 : word) = Some W_1b768.
Proof. vm_refl. Qed.
Lemma D_1b768 : decode_any W_1b768 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b76c : bv 32 := 0x00040613.
Lemma F_1b76c : fetch_word Plain.M.loaded_segments (0x1b7c4 : word) = Some W_1b76c.
Proof. vm_refl. Qed.
Lemma D_1b76c : decode_any W_1b76c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b770 : bv 32 := 0x00048813.
Lemma F_1b770 : fetch_word Plain.M.loaded_segments (0x1b7c8 : word) = Some W_1b770.
Proof. vm_refl. Qed.
Lemma D_1b770 : decode_any W_1b770 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b774 : bv 32 := 0x000b0893.
Lemma F_1b774 : fetch_word Plain.M.loaded_segments (0x1b7cc : word) = Some W_1b774.
Proof. vm_refl. Qed.
Lemma D_1b774 : decode_any W_1b774 = Some (OpImm ALU_ADD 17 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b778 : bv 32 := 0x475070ef.
Lemma F_1b778 : fetch_word Plain.M.loaded_segments (0x1b7d0 : word) = Some W_1b778.
Proof. vm_refl. Qed.
Lemma D_1b778 : decode_any W_1b778 = Some (Jal 1 31860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b77c : bv 32 := 0xfffa8a9b.
Lemma F_1b77c : fetch_word Plain.M.loaded_segments (0x1b7d4 : word) = Some W_1b77c.
Proof. vm_refl. Qed.
Lemma D_1b77c : decode_any W_1b77c = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b780 : bv 32 := 0x001b0b1b.
Lemma F_1b780 : fetch_word Plain.M.loaded_segments (0x1b7d8 : word) = Some W_1b780.
Proof. vm_refl. Qed.
Lemma D_1b780 : decode_any W_1b780 = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b784 : bv 32 := 0xfd7a98e3.
Lemma F_1b784 : fetch_word Plain.M.loaded_segments (0x1b7dc : word) = Some W_1b784.
Proof. vm_refl. Qed.
Lemma D_1b784 : decode_any W_1b784 = Some (Branch BC_NE 21 23 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b788 : bv 32 := 0x013a0abb.
Lemma F_1b788 : fetch_word Plain.M.loaded_segments (0x1b7e0 : word) = Some W_1b788.
Proof. vm_refl. Qed.
Lemma D_1b788 : decode_any W_1b788 = Some (Op32 ALU_ADD 21 20 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b78c : bv 32 := 0x05405063.
Lemma F_1b78c : fetch_word Plain.M.loaded_segments (0x1b7e4 : word) = Some W_1b78c.
Proof. vm_refl. Qed.
Lemma D_1b78c : decode_any W_1b78c = Some (Branch BC_GE 0 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b790 : bv 32 := 0xfff98a13.
Lemma F_1b790 : fetch_word Plain.M.loaded_segments (0x1b7e8 : word) = Some W_1b790.
Proof. vm_refl. Qed.
Lemma D_1b790 : decode_any W_1b790 = Some (OpImm ALU_ADD 20 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b794 : bv 32 := 0x01412503.
Lemma F_1b794 : fetch_word Plain.M.loaded_segments (0x1b7ec : word) = Some W_1b794.
Proof. vm_refl. Qed.
Lemma D_1b794 : decode_any W_1b794 = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b798 : bv 32 := 0x01012703.
Lemma F_1b798 : fetch_word Plain.M.loaded_segments (0x1b7f0 : word) = Some W_1b798.
Proof. vm_refl. Qed.
Lemma D_1b798 : decode_any W_1b798 = Some (Load SZ4 true 14 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b79c : bv 32 := 0x00a985bb.
Lemma F_1b79c : fetch_word Plain.M.loaded_segments (0x1b7f4 : word) = Some W_1b79c.
Proof. vm_refl. Qed.
Lemma D_1b79c : decode_any W_1b79c = Some (Op32 ALU_ADD 11 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7a0 : bv 32 := 0x00aa08bb.
Lemma F_1b7a0 : fetch_word Plain.M.loaded_segments (0x1b7f8 : word) = Some W_1b7a0.
Proof. vm_refl. Qed.
Lemma D_1b7a0 : decode_any W_1b7a0 = Some (Op32 ALU_ADD 17 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7a4 : bv 32 := 0x00100693.
Lemma F_1b7a4 : fetch_word Plain.M.loaded_segments (0x1b7fc : word) = Some W_1b7a4.
Proof. vm_refl. Qed.
Lemma D_1b7a4 : decode_any W_1b7a4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7a8 : bv 32 := 0x00c00793.
Lemma F_1b7a8 : fetch_word Plain.M.loaded_segments (0x1b800 : word) = Some W_1b7a8.
Proof. vm_refl. Qed.
Lemma D_1b7a8 : decode_any W_1b7a8 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7ac : bv 32 := 0x00813023.
Lemma F_1b7ac : fetch_word Plain.M.loaded_segments (0x1b804 : word) = Some W_1b7ac.
Proof. vm_refl. Qed.
Lemma D_1b7ac : decode_any W_1b7ac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7b0 : bv 32 := 0x00048513.
Lemma F_1b7b0 : fetch_word Plain.M.loaded_segments (0x1b808 : word) = Some W_1b7b0.
Proof. vm_refl. Qed.
Lemma D_1b7b0 : decode_any W_1b7b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7b4 : bv 32 := 0x00040613.
Lemma F_1b7b4 : fetch_word Plain.M.loaded_segments (0x1b80c : word) = Some W_1b7b4.
Proof. vm_refl. Qed.
Lemma D_1b7b4 : decode_any W_1b7b4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7b8 : bv 32 := 0x00048813.
Lemma F_1b7b8 : fetch_word Plain.M.loaded_segments (0x1b810 : word) = Some W_1b7b8.
Proof. vm_refl. Qed.
Lemma D_1b7b8 : decode_any W_1b7b8 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7bc : bv 32 := 0x431070ef.
Lemma F_1b7bc : fetch_word Plain.M.loaded_segments (0x1b814 : word) = Some W_1b7bc.
Proof. vm_refl. Qed.
Lemma D_1b7bc : decode_any W_1b7bc = Some (Jal 1 31792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7c0 : bv 32 := 0x0019899b.
Lemma F_1b7c0 : fetch_word Plain.M.loaded_segments (0x1b818 : word) = Some W_1b7c0.
Proof. vm_refl. Qed.
Lemma D_1b7c0 : decode_any W_1b7c0 = Some (OpImm32 19 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7c4 : bv 32 := 0xfffa0a13.
Lemma F_1b7c4 : fetch_word Plain.M.loaded_segments (0x1b81c : word) = Some W_1b7c4.
Proof. vm_refl. Qed.
Lemma D_1b7c4 : decode_any W_1b7c4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7c8 : bv 32 := 0xfd5996e3.
Lemma F_1b7c8 : fetch_word Plain.M.loaded_segments (0x1b820 : word) = Some W_1b7c8.
Proof. vm_refl. Qed.
Lemma D_1b7c8 : decode_any W_1b7c8 = Some (Branch BC_NE 19 21 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7cc : bv 32 := 0x04805463.
Lemma F_1b7cc : fetch_word Plain.M.loaded_segments (0x1b824 : word) = Some W_1b7cc.
Proof. vm_refl. Qed.
Lemma D_1b7cc : decode_any W_1b7cc = Some (Branch BC_GE 0 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7d0 : bv 32 := 0xfff4099b.
Lemma F_1b7d0 : fetch_word Plain.M.loaded_segments (0x1b828 : word) = Some W_1b7d0.
Proof. vm_refl. Qed.
Lemma D_1b7d0 : decode_any W_1b7d0 = Some (OpImm32 19 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7d4 : bv 32 := 0xfff00a13.
Lemma F_1b7d4 : fetch_word Plain.M.loaded_segments (0x1b82c : word) = Some W_1b7d4.
Proof. vm_refl. Qed.
Lemma D_1b7d4 : decode_any W_1b7d4 = Some (OpImm ALU_ADD 20 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7d8 : bv 32 := 0x00040b13.
Lemma F_1b7d8 : fetch_word Plain.M.loaded_segments (0x1b830 : word) = Some W_1b7d8.
Proof. vm_refl. Qed.
Lemma D_1b7d8 : decode_any W_1b7d8 = Some (OpImm ALU_ADD 22 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7dc : bv 32 := 0x01412503.
Lemma F_1b7dc : fetch_word Plain.M.loaded_segments (0x1b834 : word) = Some W_1b7dc.
Proof. vm_refl. Qed.
Lemma D_1b7dc : decode_any W_1b7dc = Some (Load SZ4 true 10 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7e0 : bv 32 := 0x00aa86bb.
Lemma F_1b7e0 : fetch_word Plain.M.loaded_segments (0x1b838 : word) = Some W_1b7e0.
Proof. vm_refl. Qed.
Lemma D_1b7e0 : decode_any W_1b7e0 = Some (Op32 ALU_ADD 13 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7e4 : bv 32 := 0x00100713.
Lemma F_1b7e4 : fetch_word Plain.M.loaded_segments (0x1b83c : word) = Some W_1b7e4.
Proof. vm_refl. Qed.
Lemma D_1b7e4 : decode_any W_1b7e4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7e8 : bv 32 := 0x00c00793.
Lemma F_1b7e8 : fetch_word Plain.M.loaded_segments (0x1b840 : word) = Some W_1b7e8.
Proof. vm_refl. Qed.
Lemma D_1b7e8 : decode_any W_1b7e8 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7ec : bv 32 := 0x01613023.
Lemma F_1b7ec : fetch_word Plain.M.loaded_segments (0x1b844 : word) = Some W_1b7ec.
Proof. vm_refl. Qed.
Lemma D_1b7ec : decode_any W_1b7ec = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7f0 : bv 32 := 0x00048513.
Lemma F_1b7f0 : fetch_word Plain.M.loaded_segments (0x1b848 : word) = Some W_1b7f0.
Proof. vm_refl. Qed.
Lemma D_1b7f0 : decode_any W_1b7f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7f4 : bv 32 := 0x00000593.
Lemma F_1b7f4 : fetch_word Plain.M.loaded_segments (0x1b84c : word) = Some W_1b7f4.
Proof. vm_refl. Qed.
Lemma D_1b7f4 : decode_any W_1b7f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7f8 : bv 32 := 0x00098613.
Lemma F_1b7f8 : fetch_word Plain.M.loaded_segments (0x1b850 : word) = Some W_1b7f8.
Proof. vm_refl. Qed.
Lemma D_1b7f8 : decode_any W_1b7f8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7fc : bv 32 := 0x00048813.
Lemma F_1b7fc : fetch_word Plain.M.loaded_segments (0x1b854 : word) = Some W_1b7fc.
Proof. vm_refl. Qed.
Lemma D_1b7fc : decode_any W_1b7fc = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b800 : bv 32 := 0x00000893.
Lemma F_1b800 : fetch_word Plain.M.loaded_segments (0x1b858 : word) = Some W_1b800.
Proof. vm_refl. Qed.
Lemma D_1b800 : decode_any W_1b800 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b804 : bv 32 := 0x3e9070ef.
Lemma F_1b804 : fetch_word Plain.M.loaded_segments (0x1b85c : word) = Some W_1b804.
Proof. vm_refl. Qed.
Lemma D_1b804 : decode_any W_1b804 = Some (Jal 1 31720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b808 : bv 32 := 0xfff9899b.
Lemma F_1b808 : fetch_word Plain.M.loaded_segments (0x1b860 : word) = Some W_1b808.
Proof. vm_refl. Qed.
Lemma D_1b808 : decode_any W_1b808 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b80c : bv 32 := 0x001b0b1b.
Lemma F_1b80c : fetch_word Plain.M.loaded_segments (0x1b864 : word) = Some W_1b80c.
Proof. vm_refl. Qed.
Lemma D_1b80c : decode_any W_1b80c = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b810 : bv 32 := 0xfd4996e3.
Lemma F_1b810 : fetch_word Plain.M.loaded_segments (0x1b868 : word) = Some W_1b810.
Proof. vm_refl. Qed.
Lemma D_1b810 : decode_any W_1b810 = Some (Branch BC_NE 19 20 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b814 : bv 32 := 0x0d205e63.
Lemma F_1b814 : fetch_word Plain.M.loaded_segments (0x1b86c : word) = Some W_1b814.
Proof. vm_refl. Qed.
Lemma D_1b814 : decode_any W_1b814 = Some (Branch BC_GE 0 18 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b818 : bv 32 := 0xfff40993.
Lemma F_1b818 : fetch_word Plain.M.loaded_segments (0x1b870 : word) = Some W_1b818.
Proof. vm_refl. Qed.
Lemma D_1b818 : decode_any W_1b818 = Some (OpImm ALU_ADD 19 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b81c : bv 32 := 0x0089093b.
Lemma F_1b81c : fetch_word Plain.M.loaded_segments (0x1b874 : word) = Some W_1b81c.
Proof. vm_refl. Qed.
Lemma D_1b81c : decode_any W_1b81c = Some (Op32 ALU_ADD 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b820 : bv 32 := 0x01012503.
Lemma F_1b820 : fetch_word Plain.M.loaded_segments (0x1b878 : word) = Some W_1b820.
Proof. vm_refl. Qed.
Lemma D_1b820 : decode_any W_1b820 = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b824 : bv 32 := 0x01412583.
Lemma F_1b824 : fetch_word Plain.M.loaded_segments (0x1b87c : word) = Some W_1b824.
Proof. vm_refl. Qed.
Lemma D_1b824 : decode_any W_1b824 = Some (Load SZ4 true 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b828 : bv 32 := 0x00a4063b.
Lemma F_1b828 : fetch_word Plain.M.loaded_segments (0x1b880 : word) = Some W_1b828.
Proof. vm_refl. Qed.
Lemma D_1b828 : decode_any W_1b828 = Some (Op32 ALU_ADD 12 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b82c : bv 32 := 0x00ba86bb.
Lemma F_1b82c : fetch_word Plain.M.loaded_segments (0x1b884 : word) = Some W_1b82c.
Proof. vm_refl. Qed.
Lemma D_1b82c : decode_any W_1b82c = Some (Op32 ALU_ADD 13 21 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b830 : bv 32 := 0x00a9853b.
Lemma F_1b830 : fetch_word Plain.M.loaded_segments (0x1b888 : word) = Some W_1b830.
Proof. vm_refl. Qed.
Lemma D_1b830 : decode_any W_1b830 = Some (Op32 ALU_ADD 10 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b834 : bv 32 := 0x00100713.
Lemma F_1b834 : fetch_word Plain.M.loaded_segments (0x1b88c : word) = Some W_1b834.
Proof. vm_refl. Qed.
Lemma D_1b834 : decode_any W_1b834 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b838 : bv 32 := 0x00c00793.
Lemma F_1b838 : fetch_word Plain.M.loaded_segments (0x1b890 : word) = Some W_1b838.
Proof. vm_refl. Qed.
Lemma D_1b838 : decode_any W_1b838 = Some (OpImm ALU_ADD 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b83c : bv 32 := 0x00a13023.
Lemma F_1b83c : fetch_word Plain.M.loaded_segments (0x1b894 : word) = Some W_1b83c.
Proof. vm_refl. Qed.
Lemma D_1b83c : decode_any W_1b83c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b840 : bv 32 := 0x00048513.
Lemma F_1b840 : fetch_word Plain.M.loaded_segments (0x1b898 : word) = Some W_1b840.
Proof. vm_refl. Qed.
Lemma D_1b840 : decode_any W_1b840 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b844 : bv 32 := 0x00000593.
Lemma F_1b844 : fetch_word Plain.M.loaded_segments (0x1b89c : word) = Some W_1b844.
Proof. vm_refl. Qed.
Lemma D_1b844 : decode_any W_1b844 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b848 : bv 32 := 0x00048813.
Lemma F_1b848 : fetch_word Plain.M.loaded_segments (0x1b8a0 : word) = Some W_1b848.
Proof. vm_refl. Qed.
Lemma D_1b848 : decode_any W_1b848 = Some (OpImm ALU_ADD 16 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b84c : bv 32 := 0x00000893.
Lemma F_1b84c : fetch_word Plain.M.loaded_segments (0x1b8a4 : word) = Some W_1b84c.
Proof. vm_refl. Qed.
Lemma D_1b84c : decode_any W_1b84c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b850 : bv 32 := 0x39d070ef.
Lemma F_1b850 : fetch_word Plain.M.loaded_segments (0x1b8a8 : word) = Some W_1b850.
Proof. vm_refl. Qed.
Lemma D_1b850 : decode_any W_1b850 = Some (Jal 1 31644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b854 : bv 32 := 0x0014041b.
Lemma F_1b854 : fetch_word Plain.M.loaded_segments (0x1b8ac : word) = Some W_1b854.
Proof. vm_refl. Qed.
Lemma D_1b854 : decode_any W_1b854 = Some (OpImm32 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b858 : bv 32 := 0xfff98993.
Lemma F_1b858 : fetch_word Plain.M.loaded_segments (0x1b8b0 : word) = Some W_1b858.
Proof. vm_refl. Qed.
Lemma D_1b858 : decode_any W_1b858 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b85c : bv 32 := 0xfd2412e3.
Lemma F_1b85c : fetch_word Plain.M.loaded_segments (0x1b8b4 : word) = Some W_1b85c.
Proof. vm_refl. Qed.
Lemma D_1b85c : decode_any W_1b85c = Some (Branch BC_NE 8 18 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b860 : bv 32 := 0x0900006f.
Lemma F_1b860 : fetch_word Plain.M.loaded_segments (0x1b8b8 : word) = Some W_1b860.
Proof. vm_refl. Qed.
Lemma D_1b860 : decode_any W_1b860 = Some (Jal 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8f0 : bv 32 := 0x00048513.
Lemma F_1b8f0 : fetch_word Plain.M.loaded_segments (0x1b948 : word) = Some W_1b8f0.
Proof. vm_refl. Qed.
Lemma D_1b8f0 : decode_any W_1b8f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8f4 : bv 32 := 0x05813083.
Lemma F_1b8f4 : fetch_word Plain.M.loaded_segments (0x1b94c : word) = Some W_1b8f4.
Proof. vm_refl. Qed.
Lemma D_1b8f4 : decode_any W_1b8f4 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8f8 : bv 32 := 0x05013403.
Lemma F_1b8f8 : fetch_word Plain.M.loaded_segments (0x1b950 : word) = Some W_1b8f8.
Proof. vm_refl. Qed.
Lemma D_1b8f8 : decode_any W_1b8f8 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8fc : bv 32 := 0x04813483.
Lemma F_1b8fc : fetch_word Plain.M.loaded_segments (0x1b954 : word) = Some W_1b8fc.
Proof. vm_refl. Qed.
Lemma D_1b8fc : decode_any W_1b8fc = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b900 : bv 32 := 0x04013903.
Lemma F_1b900 : fetch_word Plain.M.loaded_segments (0x1b958 : word) = Some W_1b900.
Proof. vm_refl. Qed.
Lemma D_1b900 : decode_any W_1b900 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b904 : bv 32 := 0x03813983.
Lemma F_1b904 : fetch_word Plain.M.loaded_segments (0x1b95c : word) = Some W_1b904.
Proof. vm_refl. Qed.
Lemma D_1b904 : decode_any W_1b904 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b908 : bv 32 := 0x03013a03.
Lemma F_1b908 : fetch_word Plain.M.loaded_segments (0x1b960 : word) = Some W_1b908.
Proof. vm_refl. Qed.
Lemma D_1b908 : decode_any W_1b908 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b90c : bv 32 := 0x02813a83.
Lemma F_1b90c : fetch_word Plain.M.loaded_segments (0x1b964 : word) = Some W_1b90c.
Proof. vm_refl. Qed.
Lemma D_1b90c : decode_any W_1b90c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b910 : bv 32 := 0x02013b03.
Lemma F_1b910 : fetch_word Plain.M.loaded_segments (0x1b968 : word) = Some W_1b910.
Proof. vm_refl. Qed.
Lemma D_1b910 : decode_any W_1b910 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b914 : bv 32 := 0x01813b83.
Lemma F_1b914 : fetch_word Plain.M.loaded_segments (0x1b96c : word) = Some W_1b914.
Proof. vm_refl. Qed.
Lemma D_1b914 : decode_any W_1b914 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b918 : bv 32 := 0x06010113.
Lemma F_1b918 : fetch_word Plain.M.loaded_segments (0x1b970 : word) = Some W_1b918.
Proof. vm_refl. Qed.
Lemma D_1b918 : decode_any W_1b918 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b91c : bv 32 := 0x00008067.
Lemma F_1b91c : fetch_word Plain.M.loaded_segments (0x1b974 : word) = Some W_1b91c.
Proof. vm_refl. Qed.
Lemma D_1b91c : decode_any W_1b91c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
