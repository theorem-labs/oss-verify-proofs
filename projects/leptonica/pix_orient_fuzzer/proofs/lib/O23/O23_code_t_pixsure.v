(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_635fc : bv 32 := 0x02050e63.
Lemma F_635fc : fetch_word Plain.M.loaded_segments (0x63654 : word) = Some W_635fc.
Proof. vm_refl. Qed.
Lemma D_635fc : decode_any W_635fc = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63600 : bv 32 := 0xfe010113.
Lemma F_63600 : fetch_word Plain.M.loaded_segments (0x63658 : word) = Some W_63600.
Proof. vm_refl. Qed.
Lemma D_63600 : decode_any W_63600 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63604 : bv 32 := 0x00113c23.
Lemma F_63604 : fetch_word Plain.M.loaded_segments (0x6365c : word) = Some W_63604.
Proof. vm_refl. Qed.
Lemma D_63604 : decode_any W_63604 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63608 : bv 32 := 0x00813823.
Lemma F_63608 : fetch_word Plain.M.loaded_segments (0x63660 : word) = Some W_63608.
Proof. vm_refl. Qed.
Lemma D_63608 : decode_any W_63608 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6360c : bv 32 := 0x00913423.
Lemma F_6360c : fetch_word Plain.M.loaded_segments (0x63664 : word) = Some W_6360c.
Proof. vm_refl. Qed.
Lemma D_6360c : decode_any W_6360c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63610 : bv 32 := 0x00058493.
Lemma F_63610 : fetch_word Plain.M.loaded_segments (0x63668 : word) = Some W_63610.
Proof. vm_refl. Qed.
Lemma D_63610 : decode_any W_63610 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63614 : bv 32 := 0x00050413.
Lemma F_63614 : fetch_word Plain.M.loaded_segments (0x6366c : word) = Some W_63614.
Proof. vm_refl. Qed.
Lemma D_63614 : decode_any W_63614 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63618 : bv 32 := 0x00053503.
Lemma F_63618 : fetch_word Plain.M.loaded_segments (0x63670 : word) = Some W_63618.
Proof. vm_refl. Qed.
Lemma D_63618 : decode_any W_63618 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6361c : bv 32 := 0x00050463.
Lemma F_6361c : fetch_word Plain.M.loaded_segments (0x63674 : word) = Some W_6361c.
Proof. vm_refl. Qed.
Lemma D_6361c : decode_any W_6361c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63624 : bv 32 := 0x04048063.
Lemma F_63624 : fetch_word Plain.M.loaded_segments (0x6367c : word) = Some W_63624.
Proof. vm_refl. Qed.
Lemma D_63624 : decode_any W_63624 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63664 : bv 32 := 0x00000593.
Lemma F_63664 : fetch_word Plain.M.loaded_segments (0x636bc : word) = Some W_63664.
Proof. vm_refl. Qed.
Lemma D_63664 : decode_any W_63664 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63668 : bv 32 := 0x00000513.
Lemma F_63668 : fetch_word Plain.M.loaded_segments (0x636c0 : word) = Some W_63668.
Proof. vm_refl. Qed.
Lemma D_63668 : decode_any W_63668 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6366c : bv 32 := 0x00b43023.
Lemma F_6366c : fetch_word Plain.M.loaded_segments (0x636c4 : word) = Some W_6366c.
Proof. vm_refl. Qed.
Lemma D_6366c : decode_any W_6366c = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63670 : bv 32 := 0x01813083.
Lemma F_63670 : fetch_word Plain.M.loaded_segments (0x636c8 : word) = Some W_63670.
Proof. vm_refl. Qed.
Lemma D_63670 : decode_any W_63670 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63674 : bv 32 := 0x01013403.
Lemma F_63674 : fetch_word Plain.M.loaded_segments (0x636cc : word) = Some W_63674.
Proof. vm_refl. Qed.
Lemma D_63674 : decode_any W_63674 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63678 : bv 32 := 0x00813483.
Lemma F_63678 : fetch_word Plain.M.loaded_segments (0x636d0 : word) = Some W_63678.
Proof. vm_refl. Qed.
Lemma D_63678 : decode_any W_63678 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6367c : bv 32 := 0x02010113.
Lemma F_6367c : fetch_word Plain.M.loaded_segments (0x636d4 : word) = Some W_6367c.
Proof. vm_refl. Qed.
Lemma D_6367c : decode_any W_6367c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63680 : bv 32 := 0x00008067.
Lemma F_63680 : fetch_word Plain.M.loaded_segments (0x636d8 : word) = Some W_63680.
Proof. vm_refl. Qed.
Lemma D_63680 : decode_any W_63680 = Some (Jalr 0 1 0, 4%Z).
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
Definition W_6d428 : bv 32 := 0xfd010113.
Lemma F_6d428 : fetch_word Plain.M.loaded_segments (0x6d480 : word) = Some W_6d428.
Proof. vm_refl. Qed.
Lemma D_6d428 : decode_any W_6d428 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d42c : bv 32 := 0x02113423.
Lemma F_6d42c : fetch_word Plain.M.loaded_segments (0x6d484 : word) = Some W_6d42c.
Proof. vm_refl. Qed.
Lemma D_6d42c : decode_any W_6d42c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d430 : bv 32 := 0x02813023.
Lemma F_6d430 : fetch_word Plain.M.loaded_segments (0x6d488 : word) = Some W_6d430.
Proof. vm_refl. Qed.
Lemma D_6d430 : decode_any W_6d430 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d434 : bv 32 := 0x00913c23.
Lemma F_6d434 : fetch_word Plain.M.loaded_segments (0x6d48c : word) = Some W_6d434.
Proof. vm_refl. Qed.
Lemma D_6d434 : decode_any W_6d434 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d438 : bv 32 := 0x01213823.
Lemma F_6d438 : fetch_word Plain.M.loaded_segments (0x6d490 : word) = Some W_6d438.
Proof. vm_refl. Qed.
Lemma D_6d438 : decode_any W_6d438 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d43c : bv 32 := 0x01313423.
Lemma F_6d43c : fetch_word Plain.M.loaded_segments (0x6d494 : word) = Some W_6d43c.
Proof. vm_refl. Qed.
Lemma D_6d43c : decode_any W_6d43c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d440 : bv 32 := 0x00050413.
Lemma F_6d440 : fetch_word Plain.M.loaded_segments (0x6d498 : word) = Some W_6d440.
Proof. vm_refl. Qed.
Lemma D_6d440 : decode_any W_6d440 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d444 : bv 32 := 0x06058063.
Lemma F_6d444 : fetch_word Plain.M.loaded_segments (0x6d49c : word) = Some W_6d444.
Proof. vm_refl. Qed.
Lemma D_6d444 : decode_any W_6d444 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d448 : bv 32 := 0x00058493.
Lemma F_6d448 : fetch_word Plain.M.loaded_segments (0x6d4a0 : word) = Some W_6d448.
Proof. vm_refl. Qed.
Lemma D_6d448 : decode_any W_6d448 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d44c : bv 32 := 0x18858e63.
Lemma F_6d44c : fetch_word Plain.M.loaded_segments (0x6d4a4 : word) = Some W_6d44c.
Proof. vm_refl. Qed.
Lemma D_6d44c : decode_any W_6d44c = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d450 : bv 32 := 0x0044a503.
Lemma F_6d450 : fetch_word Plain.M.loaded_segments (0x6d4a8 : word) = Some W_6d450.
Proof. vm_refl. Qed.
Lemma D_6d450 : decode_any W_6d450 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d454 : bv 32 := 0x0104a583.
Lemma F_6d454 : fetch_word Plain.M.loaded_segments (0x6d4ac : word) = Some W_6d454.
Proof. vm_refl. Qed.
Lemma D_6d454 : decode_any W_6d454 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d458 : bv 32 := 0x02a58533.
Lemma F_6d458 : fetch_word Plain.M.loaded_segments (0x6d4b0 : word) = Some W_6d458.
Proof. vm_refl. Qed.
Lemma D_6d458 : decode_any W_6d458 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d45c : bv 32 := 0x0025191b.
Lemma F_6d45c : fetch_word Plain.M.loaded_segments (0x6d4b4 : word) = Some W_6d45c.
Proof. vm_refl. Qed.
Lemma D_6d45c : decode_any W_6d45c = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d460 : bv 32 := 0x08040463.
Lemma F_6d460 : fetch_word Plain.M.loaded_segments (0x6d4b8 : word) = Some W_6d460.
Proof. vm_refl. Qed.
Lemma D_6d460 : decode_any W_6d460 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d49c : bv 32 := 0x00000613.
Lemma F_6d49c : fetch_word Plain.M.loaded_segments (0x6d4f4 : word) = Some W_6d49c.
Proof. vm_refl. Qed.
Lemma D_6d49c : decode_any W_6d49c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4a0 : bv 32 := 0x02c0006f.
Lemma F_6d4a0 : fetch_word Plain.M.loaded_segments (0x6d4f8 : word) = Some W_6d4a0.
Proof. vm_refl. Qed.
Lemma D_6d4a0 : decode_any W_6d4a0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4cc : bv 32 := 0x02813083.
Lemma F_6d4cc : fetch_word Plain.M.loaded_segments (0x6d524 : word) = Some W_6d4cc.
Proof. vm_refl. Qed.
Lemma D_6d4cc : decode_any W_6d4cc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4d0 : bv 32 := 0x02013403.
Lemma F_6d4d0 : fetch_word Plain.M.loaded_segments (0x6d528 : word) = Some W_6d4d0.
Proof. vm_refl. Qed.
Lemma D_6d4d0 : decode_any W_6d4d0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4d4 : bv 32 := 0x01813483.
Lemma F_6d4d4 : fetch_word Plain.M.loaded_segments (0x6d52c : word) = Some W_6d4d4.
Proof. vm_refl. Qed.
Lemma D_6d4d4 : decode_any W_6d4d4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4d8 : bv 32 := 0x01013903.
Lemma F_6d4d8 : fetch_word Plain.M.loaded_segments (0x6d530 : word) = Some W_6d4d8.
Proof. vm_refl. Qed.
Lemma D_6d4d8 : decode_any W_6d4d8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4dc : bv 32 := 0x00813983.
Lemma F_6d4dc : fetch_word Plain.M.loaded_segments (0x6d534 : word) = Some W_6d4dc.
Proof. vm_refl. Qed.
Lemma D_6d4dc : decode_any W_6d4dc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4e0 : bv 32 := 0x03010113.
Lemma F_6d4e0 : fetch_word Plain.M.loaded_segments (0x6d538 : word) = Some W_6d4e0.
Proof. vm_refl. Qed.
Lemma D_6d4e0 : decode_any W_6d4e0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4e4 : bv 32 := 0xbe1f506f.
Lemma F_6d4e4 : fetch_word Plain.M.loaded_segments (0x6d53c : word) = Some W_6d4e4.
Proof. vm_refl. Qed.
Lemma D_6d4e4 : decode_any W_6d4e4 = Some (Jal 0 2055136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4e8 : bv 32 := 0x00048513.
Lemma F_6d4e8 : fetch_word Plain.M.loaded_segments (0x6d540 : word) = Some W_6d4e8.
Proof. vm_refl. Qed.
Lemma D_6d4e8 : decode_any W_6d4e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4ec : bv 32 := 0xf7cff0ef.
Lemma F_6d4ec : fetch_word Plain.M.loaded_segments (0x6d544 : word) = Some W_6d4ec.
Proof. vm_refl. Qed.
Lemma D_6d4ec : decode_any W_6d4ec = Some (Jal 1 2094972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4f0 : bv 32 := 0x04050263.
Lemma F_6d4f0 : fetch_word Plain.M.loaded_segments (0x6d548 : word) = Some W_6d4f0.
Proof. vm_refl. Qed.
Lemma D_6d4f0 : decode_any W_6d4f0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4f4 : bv 32 := 0x00050413.
Lemma F_6d4f4 : fetch_word Plain.M.loaded_segments (0x6d54c : word) = Some W_6d4f4.
Proof. vm_refl. Qed.
Lemma D_6d4f4 : decode_any W_6d4f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4f8 : bv 32 := 0x00456583.
Lemma F_6d4f8 : fetch_word Plain.M.loaded_segments (0x6d550 : word) = Some W_6d4f8.
Proof. vm_refl. Qed.
Lemma D_6d4f8 : decode_any W_6d4f8 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4fc : bv 32 := 0x01056603.
Lemma F_6d4fc : fetch_word Plain.M.loaded_segments (0x6d554 : word) = Some W_6d4fc.
Proof. vm_refl. Qed.
Lemma D_6d4fc : decode_any W_6d4fc = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d500 : bv 32 := 0x03853503.
Lemma F_6d500 : fetch_word Plain.M.loaded_segments (0x6d558 : word) = Some W_6d500.
Proof. vm_refl. Qed.
Lemma D_6d500 : decode_any W_6d500 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d504 : bv 32 := 0x02b60633.
Lemma F_6d504 : fetch_word Plain.M.loaded_segments (0x6d55c : word) = Some W_6d504.
Proof. vm_refl. Qed.
Lemma D_6d504 : decode_any W_6d504 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d508 : bv 32 := 0x00261613.
Lemma F_6d508 : fetch_word Plain.M.loaded_segments (0x6d560 : word) = Some W_6d508.
Proof. vm_refl. Qed.
Lemma D_6d508 : decode_any W_6d508 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d50c : bv 32 := 0x00000593.
Lemma F_6d50c : fetch_word Plain.M.loaded_segments (0x6d564 : word) = Some W_6d50c.
Proof. vm_refl. Qed.
Lemma D_6d50c : decode_any W_6d50c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d510 : bv 32 := 0x4c99c0ef.
Lemma F_6d510 : fetch_word Plain.M.loaded_segments (0x6d568 : word) = Some W_6d510.
Proof. vm_refl. Qed.
Lemma D_6d510 : decode_any W_6d510 = Some (Jal 1 642248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d514 : bv 32 := 0x0c40006f.
Lemma F_6d514 : fetch_word Plain.M.loaded_segments (0x6d56c : word) = Some W_6d514.
Proof. vm_refl. Qed.
Lemma D_6d514 : decode_any W_6d514 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d534 : bv 32 := 0x000a5517.
Lemma F_6d534 : fetch_word Plain.M.loaded_segments (0x6d58c : word) = Some W_6d534.
Proof. vm_refl. Qed.
Lemma D_6d534 : decode_any W_6d534 = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d538 : bv 32 := 0x03c53983.
Lemma F_6d538 : fetch_word Plain.M.loaded_segments (0x6d590 : word) = Some W_6d538.
Proof. vm_refl. Qed.
Lemma D_6d538 : decode_any W_6d538 = Some (Load SZ8 true 19 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d53c : bv 32 := 0x0009a503.
Lemma F_6d53c : fetch_word Plain.M.loaded_segments (0x6d594 : word) = Some W_6d53c.
Proof. vm_refl. Qed.
Lemma D_6d53c : decode_any W_6d53c = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d540 : bv 32 := 0x00600593.
Lemma F_6d540 : fetch_word Plain.M.loaded_segments (0x6d598 : word) = Some W_6d540.
Proof. vm_refl. Qed.
Lemma D_6d540 : decode_any W_6d540 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d544 : bv 32 := 0x04b55263.
Lemma F_6d544 : fetch_word Plain.M.loaded_segments (0x6d59c : word) = Some W_6d544.
Proof. vm_refl. Qed.
Lemma D_6d544 : decode_any W_6d544 = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d548 : bv 32 := 0xfffa5517.
Lemma F_6d548 : fetch_word Plain.M.loaded_segments (0x6d5a0 : word) = Some W_6d548.
Proof. vm_refl. Qed.
Lemma D_6d548 : decode_any W_6d548 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d54c : bv 32 := 0xfffac597.
Lemma F_6d54c : fetch_word Plain.M.loaded_segments (0x6d5a4 : word) = Some W_6d54c.
Proof. vm_refl. Qed.
Lemma D_6d54c : decode_any W_6d54c = Some (Auipc 11 1048492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d550 : bv 32 := 0x13a50513.
Lemma F_6d550 : fetch_word Plain.M.loaded_segments (0x6d5a8 : word) = Some W_6d550.
Proof. vm_refl. Qed.
Lemma D_6d550 : decode_any W_6d550 = Some (OpImm ALU_ADD 10 10 314, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d554 : bv 32 := 0xcd358593.
Lemma F_6d554 : fetch_word Plain.M.loaded_segments (0x6d5ac : word) = Some W_6d554.
Proof. vm_refl. Qed.
Lemma D_6d554 : decode_any W_6d554 = Some (OpImm ALU_ADD 11 11 3283, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d558 : bv 32 := 0x00000613.
Lemma F_6d558 : fetch_word Plain.M.loaded_segments (0x6d5b0 : word) = Some W_6d558.
Proof. vm_refl. Qed.
Lemma D_6d558 : decode_any W_6d558 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d55c : bv 32 := 0xb69f50ef.
Lemma F_6d55c : fetch_word Plain.M.loaded_segments (0x6d5b4 : word) = Some W_6d55c.
Proof. vm_refl. Qed.
Lemma D_6d55c : decode_any W_6d55c = Some (Jal 1 2055016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d560 : bv 32 := 0x00050413.
Lemma F_6d560 : fetch_word Plain.M.loaded_segments (0x6d5b8 : word) = Some W_6d560.
Proof. vm_refl. Qed.
Lemma D_6d560 : decode_any W_6d560 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d564 : bv 32 := 0x06051a63.
Lemma F_6d564 : fetch_word Plain.M.loaded_segments (0x6d5bc : word) = Some W_6d564.
Proof. vm_refl. Qed.
Lemma D_6d564 : decode_any W_6d564 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d568 : bv 32 := 0x0009a503.
Lemma F_6d568 : fetch_word Plain.M.loaded_segments (0x6d5c0 : word) = Some W_6d568.
Proof. vm_refl. Qed.
Lemma D_6d568 : decode_any W_6d568 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d56c : bv 32 := 0x00500593.
Lemma F_6d56c : fetch_word Plain.M.loaded_segments (0x6d5c4 : word) = Some W_6d56c.
Proof. vm_refl. Qed.
Lemma D_6d56c : decode_any W_6d56c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d570 : bv 32 := 0x00a5cc63.
Lemma F_6d570 : fetch_word Plain.M.loaded_segments (0x6d5c8 : word) = Some W_6d570.
Proof. vm_refl. Qed.
Lemma D_6d570 : decode_any W_6d570 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d574 : bv 32 := 0xfffa5517.
Lemma F_6d574 : fetch_word Plain.M.loaded_segments (0x6d5cc : word) = Some W_6d574.
Proof. vm_refl. Qed.
Lemma D_6d574 : decode_any W_6d574 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d578 : bv 32 := 0xfffab597.
Lemma F_6d578 : fetch_word Plain.M.loaded_segments (0x6d5d0 : word) = Some W_6d578.
Proof. vm_refl. Qed.
Lemma D_6d578 : decode_any W_6d578 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d57c : bv 32 := 0x10e50513.
Lemma F_6d57c : fetch_word Plain.M.loaded_segments (0x6d5d4 : word) = Some W_6d57c.
Proof. vm_refl. Qed.
Lemma D_6d57c : decode_any W_6d57c = Some (OpImm ALU_ADD 10 10 270, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d580 : bv 32 := 0x5c358593.
Lemma F_6d580 : fetch_word Plain.M.loaded_segments (0x6d5d8 : word) = Some W_6d580.
Proof. vm_refl. Qed.
Lemma D_6d580 : decode_any W_6d580 = Some (OpImm ALU_ADD 11 11 1475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d584 : bv 32 := 0xf19ff06f.
Lemma F_6d584 : fetch_word Plain.M.loaded_segments (0x6d5dc : word) = Some W_6d584.
Proof. vm_refl. Qed.
Lemma D_6d584 : decode_any W_6d584 = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5d8 : bv 32 := 0x03843503.
Lemma F_6d5d8 : fetch_word Plain.M.loaded_segments (0x6d630 : word) = Some W_6d5d8.
Proof. vm_refl. Qed.
Lemma D_6d5d8 : decode_any W_6d5d8 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5dc : bv 32 := 0x0384b583.
Lemma F_6d5dc : fetch_word Plain.M.loaded_segments (0x6d634 : word) = Some W_6d5dc.
Proof. vm_refl. Qed.
Lemma D_6d5dc : decode_any W_6d5dc = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e0 : bv 32 := 0x00090613.
Lemma F_6d5e0 : fetch_word Plain.M.loaded_segments (0x6d638 : word) = Some W_6d5e0.
Proof. vm_refl. Qed.
Lemma D_6d5e0 : decode_any W_6d5e0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e4 : bv 32 := 0x6749c0ef.
Lemma F_6d5e4 : fetch_word Plain.M.loaded_segments (0x6d63c : word) = Some W_6d5e4.
Proof. vm_refl. Qed.
Lemma D_6d5e4 : decode_any W_6d5e4 = Some (Jal 1 640628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e8 : bv 32 := 0x00040513.
Lemma F_6d5e8 : fetch_word Plain.M.loaded_segments (0x6d640 : word) = Some W_6d5e8.
Proof. vm_refl. Qed.
Lemma D_6d5e8 : decode_any W_6d5e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5ec : bv 32 := 0x02813083.
Lemma F_6d5ec : fetch_word Plain.M.loaded_segments (0x6d644 : word) = Some W_6d5ec.
Proof. vm_refl. Qed.
Lemma D_6d5ec : decode_any W_6d5ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f0 : bv 32 := 0x02013403.
Lemma F_6d5f0 : fetch_word Plain.M.loaded_segments (0x6d648 : word) = Some W_6d5f0.
Proof. vm_refl. Qed.
Lemma D_6d5f0 : decode_any W_6d5f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f4 : bv 32 := 0x01813483.
Lemma F_6d5f4 : fetch_word Plain.M.loaded_segments (0x6d64c : word) = Some W_6d5f4.
Proof. vm_refl. Qed.
Lemma D_6d5f4 : decode_any W_6d5f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f8 : bv 32 := 0x01013903.
Lemma F_6d5f8 : fetch_word Plain.M.loaded_segments (0x6d650 : word) = Some W_6d5f8.
Proof. vm_refl. Qed.
Lemma D_6d5f8 : decode_any W_6d5f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5fc : bv 32 := 0x00813983.
Lemma F_6d5fc : fetch_word Plain.M.loaded_segments (0x6d654 : word) = Some W_6d5fc.
Proof. vm_refl. Qed.
Lemma D_6d5fc : decode_any W_6d5fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d600 : bv 32 := 0x03010113.
Lemma F_6d600 : fetch_word Plain.M.loaded_segments (0x6d658 : word) = Some W_6d600.
Proof. vm_refl. Qed.
Lemma D_6d600 : decode_any W_6d600 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d604 : bv 32 := 0x00008067.
Lemma F_6d604 : fetch_word Plain.M.loaded_segments (0x6d65c : word) = Some W_6d604.
Proof. vm_refl. Qed.
Lemma D_6d604 : decode_any W_6d604 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
