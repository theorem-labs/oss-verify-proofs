(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushU23.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6f748 : bv 32 := 0x0a050463.
Lemma F_6f748 : fetch_word Ubsan.M.loaded_segments (0x6f748 : word) = Some W_6f748.
Proof. vm_refl. Qed.
Lemma D_6f748 : decode_any W_6f748 = Some (Branch BC_EQ 10 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f74c : bv 32 := 0xf00007d3.
Lemma F_6f74c : fetch_word Ubsan.M.loaded_segments (0x6f74c : word) = Some W_6f74c.
Proof. vm_refl. Qed.
Lemma D_6f74c : decode_any W_6f74c = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f750 : bv 32 := 0xa0f505d3.
Lemma F_6f750 : fetch_word Ubsan.M.loaded_segments (0x6f750 : word) = Some W_6f750.
Proof. vm_refl. Qed.
Lemma D_6f750 : decode_any W_6f750 = Some (Fcmp F_LE FMT_S 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f754 : bv 32 := 0x0c059463.
Lemma F_6f754 : fetch_word Ubsan.M.loaded_segments (0x6f754 : word) = Some W_6f754.
Proof. vm_refl. Qed.
Lemma D_6f754 : decode_any W_6f754 = Some (Branch BC_NE 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f758 : bv 32 := 0xa0f585d3.
Lemma F_6f758 : fetch_word Ubsan.M.loaded_segments (0x6f758 : word) = Some W_6f758.
Proof. vm_refl. Qed.
Lemma D_6f758 : decode_any W_6f758 = Some (Fcmp F_LE FMT_S 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f75c : bv 32 := 0x0c059063.
Lemma F_6f75c : fetch_word Ubsan.M.loaded_segments (0x6f75c : word) = Some W_6f75c.
Proof. vm_refl. Qed.
Lemma D_6f75c : decode_any W_6f75c = Some (Branch BC_NE 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f760 : bv 32 := 0x00757593.
Lemma F_6f760 : fetch_word Ubsan.M.loaded_segments (0x6f760 : word) = Some W_6f760.
Proof. vm_refl. Qed.
Lemma D_6f760 : decode_any W_6f760 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f764 : bv 32 := 0x0e059663.
Lemma F_6f764 : fetch_word Ubsan.M.loaded_segments (0x6f764 : word) = Some W_6f764.
Proof. vm_refl. Qed.
Lemma D_6f764 : decode_any W_6f764 = Some (Branch BC_NE 11 0 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f768 : bv 32 := 0x01852583.
Lemma F_6f768 : fetch_word Ubsan.M.loaded_segments (0x6f768 : word) = Some W_6f768.
Proof. vm_refl. Qed.
Lemma D_6f768 : decode_any W_6f768 = Some (Load SZ4 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f76c : bv 32 := 0xfffaf617.
Lemma F_6f76c : fetch_word Ubsan.M.loaded_segments (0x6f76c : word) = Some W_6f76c.
Proof. vm_refl. Qed.
Lemma D_6f76c : decode_any W_6f76c = Some (Auipc 12 1048495, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f770 : bv 32 := 0x59c63787.
Lemma F_6f770 : fetch_word Ubsan.M.loaded_segments (0x6f770 : word) = Some W_6f770.
Proof. vm_refl. Qed.
Lemma D_6f770 : decode_any W_6f770 = Some (FLoad FMT_D 15 12 1436, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f774 : bv 32 := 0xfffaf617.
Lemma F_6f774 : fetch_word Ubsan.M.loaded_segments (0x6f774 : word) = Some W_6f774.
Proof. vm_refl. Qed.
Lemma D_6f774 : decode_any W_6f774 = Some (Auipc 12 1048495, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f778 : bv 32 := 0x35c63707.
Lemma F_6f778 : fetch_word Ubsan.M.loaded_segments (0x6f778 : word) = Some W_6f778.
Proof. vm_refl. Qed.
Lemma D_6f778 : decode_any W_6f778 = Some (FLoad FMT_D 14 12 860, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f77c : bv 32 := 0x42050653.
Lemma F_6f77c : fetch_word Ubsan.M.loaded_segments (0x6f77c : word) = Some W_6f77c.
Proof. vm_refl. Qed.
Lemma D_6f77c : decode_any W_6f77c = Some (Fcvt FC_D FC_S 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f780 : bv 32 := 0xd005f553.
Lemma F_6f780 : fetch_word Ubsan.M.loaded_segments (0x6f780 : word) = Some W_6f780.
Proof. vm_refl. Qed.
Lemma D_6f780 : decode_any W_6f780 = Some (Fcvt FC_S FC_W 10 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f784 : bv 32 := 0xfffaf597.
Lemma F_6f784 : fetch_word Ubsan.M.loaded_segments (0x6f784 : word) = Some W_6f784.
Proof. vm_refl. Qed.
Lemma D_6f784 : decode_any W_6f784 = Some (Auipc 11 1048495, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f788 : bv 32 := 0x3b45b687.
Lemma F_6f788 : fetch_word Ubsan.M.loaded_segments (0x6f788 : word) = Some W_6f788.
Proof. vm_refl. Qed.
Lemma D_6f788 : decode_any W_6f788 = Some (FLoad FMT_D 13 11 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f78c : bv 32 := 0x42050553.
Lemma F_6f78c : fetch_word Ubsan.M.loaded_segments (0x6f78c : word) = Some W_6f78c.
Proof. vm_refl. Qed.
Lemma D_6f78c : decode_any W_6f78c = Some (Fcvt FC_D FC_S 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f790 : bv 32 := 0x7aa67643.
Lemma F_6f790 : fetch_word Ubsan.M.loaded_segments (0x6f790 : word) = Some W_6f790.
Proof. vm_refl. Qed.
Lemma D_6f790 : decode_any W_6f790 = Some (Fma F_MADD FMT_D 12 12 10 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f794 : bv 32 := 0x2ae60553.
Lemma F_6f794 : fetch_word Ubsan.M.loaded_segments (0x6f794 : word) = Some W_6f794.
Proof. vm_refl. Qed.
Lemma D_6f794 : decode_any W_6f794 = Some (Fminmax F_MIN FMT_D 10 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f798 : bv 32 := 0xa2a695d3.
Lemma F_6f798 : fetch_word Ubsan.M.loaded_segments (0x6f798 : word) = Some W_6f798.
Proof. vm_refl. Qed.
Lemma D_6f798 : decode_any W_6f798 = Some (Fcmp F_LT FMT_D 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f79c : bv 32 := 0x0a058a63.
Lemma F_6f79c : fetch_word Ubsan.M.loaded_segments (0x6f79c : word) = Some W_6f79c.
Proof. vm_refl. Qed.
Lemma D_6f79c : decode_any W_6f79c = Some (Branch BC_EQ 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7a0 : bv 32 := 0xfffaf597.
Lemma F_6f7a0 : fetch_word Ubsan.M.loaded_segments (0x6f7a0 : word) = Some W_6f7a0.
Proof. vm_refl. Qed.
Lemma D_6f7a0 : decode_any W_6f7a0 = Some (Auipc 11 1048495, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7a4 : bv 32 := 0x4805b607.
Lemma F_6f7a4 : fetch_word Ubsan.M.loaded_segments (0x6f7a4 : word) = Some W_6f7a4.
Proof. vm_refl. Qed.
Lemma D_6f7a4 : decode_any W_6f7a4 = Some (FLoad FMT_D 12 11 1152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7a8 : bv 32 := 0xa2c515d3.
Lemma F_6f7a8 : fetch_word Ubsan.M.loaded_segments (0x6f7a8 : word) = Some W_6f7a8.
Proof. vm_refl. Qed.
Lemma D_6f7a8 : decode_any W_6f7a8 = Some (Fcmp F_LT FMT_D 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7ac : bv 32 := 0x0a058263.
Lemma F_6f7ac : fetch_word Ubsan.M.loaded_segments (0x6f7ac : word) = Some W_6f7ac.
Proof. vm_refl. Qed.
Lemma D_6f7ac : decode_any W_6f7ac = Some (Branch BC_EQ 11 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7b0 : bv 32 := 0x01c52583.
Lemma F_6f7b0 : fetch_word Ubsan.M.loaded_segments (0x6f7b0 : word) = Some W_6f7b0.
Proof. vm_refl. Qed.
Lemma D_6f7b0 : decode_any W_6f7b0 = Some (Load SZ4 true 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7b4 : bv 32 := 0x420585d3.
Lemma F_6f7b4 : fetch_word Ubsan.M.loaded_segments (0x6f7b4 : word) = Some W_6f7b4.
Proof. vm_refl. Qed.
Lemma D_6f7b4 : decode_any W_6f7b4 = Some (Fcvt FC_D FC_S 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7b8 : bv 32 := 0xd005f053.
Lemma F_6f7b8 : fetch_word Ubsan.M.loaded_segments (0x6f7b8 : word) = Some W_6f7b8.
Proof. vm_refl. Qed.
Lemma D_6f7b8 : decode_any W_6f7b8 = Some (Fcvt FC_S FC_W 0 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7bc : bv 32 := 0x42000053.
Lemma F_6f7bc : fetch_word Ubsan.M.loaded_segments (0x6f7bc : word) = Some W_6f7bc.
Proof. vm_refl. Qed.
Lemma D_6f7bc : decode_any W_6f7bc = Some (Fcvt FC_D FC_S 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7c0 : bv 32 := 0x7a05f7c3.
Lemma F_6f7c0 : fetch_word Ubsan.M.loaded_segments (0x6f7c0 : word) = Some W_6f7c0.
Proof. vm_refl. Qed.
Lemma D_6f7c0 : decode_any W_6f7c0 = Some (Fma F_MADD FMT_D 15 11 0 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7c4 : bv 32 := 0xc21515d3.
Lemma F_6f7c4 : fetch_word Ubsan.M.loaded_segments (0x6f7c4 : word) = Some W_6f7c4.
Proof. vm_refl. Qed.
Lemma D_6f7c4 : decode_any W_6f7c4 = Some (Fcvt FC_WU FC_D 11 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7c8 : bv 32 := 0x2ae787d3.
Lemma F_6f7c8 : fetch_word Ubsan.M.loaded_segments (0x6f7c8 : word) = Some W_6f7c8.
Proof. vm_refl. Qed.
Lemma D_6f7c8 : decode_any W_6f7c8 = Some (Fminmax F_MIN FMT_D 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7cc : bv 32 := 0xa2f69653.
Lemma F_6f7cc : fetch_word Ubsan.M.loaded_segments (0x6f7cc : word) = Some W_6f7cc.
Proof. vm_refl. Qed.
Lemma D_6f7cc : decode_any W_6f7cc = Some (Fcmp F_LT FMT_D 12 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7d0 : bv 32 := 0x00b52c23.
Lemma F_6f7d0 : fetch_word Ubsan.M.loaded_segments (0x6f7d0 : word) = Some W_6f7d0.
Proof. vm_refl. Qed.
Lemma D_6f7d0 : decode_any W_6f7d0 = Some (Store SZ4 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7d4 : bv 32 := 0x06060e63.
Lemma F_6f7d4 : fetch_word Ubsan.M.loaded_segments (0x6f7d4 : word) = Some W_6f7d4.
Proof. vm_refl. Qed.
Lemma D_6f7d4 : decode_any W_6f7d4 = Some (Branch BC_EQ 12 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7d8 : bv 32 := 0xa2c795d3.
Lemma F_6f7d8 : fetch_word Ubsan.M.loaded_segments (0x6f7d8 : word) = Some W_6f7d8.
Proof. vm_refl. Qed.
Lemma D_6f7d8 : decode_any W_6f7d8 = Some (Fcmp F_LT FMT_D 11 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7dc : bv 32 := 0x06058a63.
Lemma F_6f7dc : fetch_word Ubsan.M.loaded_segments (0x6f7dc : word) = Some W_6f7dc.
Proof. vm_refl. Qed.
Lemma D_6f7dc : decode_any W_6f7dc = Some (Branch BC_EQ 11 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7e0 : bv 32 := 0xc2179653.
Lemma F_6f7e0 : fetch_word Ubsan.M.loaded_segments (0x6f7e0 : word) = Some W_6f7e0.
Proof. vm_refl. Qed.
Lemma D_6f7e0 : decode_any W_6f7e0 = Some (Fcvt FC_WU FC_D 12 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7e4 : bv 32 := 0x00c52e23.
Lemma F_6f7e4 : fetch_word Ubsan.M.loaded_segments (0x6f7e4 : word) = Some W_6f7e4.
Proof. vm_refl. Qed.
Lemma D_6f7e4 : decode_any W_6f7e4 = Some (Store SZ4 10 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7e8 : bv 32 := 0x00000513.
Lemma F_6f7e8 : fetch_word Ubsan.M.loaded_segments (0x6f7e8 : word) = Some W_6f7e8.
Proof. vm_refl. Qed.
Lemma D_6f7e8 : decode_any W_6f7e8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7ec : bv 32 := 0x00008067.
Lemma F_6f7ec : fetch_word Ubsan.M.loaded_segments (0x6f7ec : word) = Some W_6f7ec.
Proof. vm_refl. Qed.
Lemma D_6f7ec : decode_any W_6f7ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7f0 : bv 32 := 0x000b7517.
Lemma F_6f7f0 : fetch_word Ubsan.M.loaded_segments (0x6f7f0 : word) = Some W_6f7f0.
Proof. vm_refl. Qed.
Lemma D_6f7f0 : decode_any W_6f7f0 = Some (Auipc 10 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7f4 : bv 32 := 0x28053503.
Lemma F_6f7f4 : fetch_word Ubsan.M.loaded_segments (0x6f7f4 : word) = Some W_6f7f4.
Proof. vm_refl. Qed.
Lemma D_6f7f4 : decode_any W_6f7f4 = Some (Load SZ8 true 10 10 640, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7f8 : bv 32 := 0x00052503.
Lemma F_6f7f8 : fetch_word Ubsan.M.loaded_segments (0x6f7f8 : word) = Some W_6f7f8.
Proof. vm_refl. Qed.
Lemma D_6f7f8 : decode_any W_6f7f8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f7fc : bv 32 := 0x00500593.
Lemma F_6f7fc : fetch_word Ubsan.M.loaded_segments (0x6f7fc : word) = Some W_6f7fc.
Proof. vm_refl. Qed.
Lemma D_6f7fc : decode_any W_6f7fc = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f800 : bv 32 := 0x04a5c463.
Lemma F_6f800 : fetch_word Ubsan.M.loaded_segments (0x6f800 : word) = Some W_6f800.
Proof. vm_refl. Qed.
Lemma D_6f800 : decode_any W_6f800 = Some (Branch BC_LT 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f804 : bv 32 := 0xfffa2517.
Lemma F_6f804 : fetch_word Ubsan.M.loaded_segments (0x6f804 : word) = Some W_6f804.
Proof. vm_refl. Qed.
Lemma D_6f804 : decode_any W_6f804 = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f808 : bv 32 := 0xfffae597.
Lemma F_6f808 : fetch_word Ubsan.M.loaded_segments (0x6f808 : word) = Some W_6f808.
Proof. vm_refl. Qed.
Lemma D_6f808 : decode_any W_6f808 = Some (Auipc 11 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f80c : bv 32 := 0x84750513.
Lemma F_6f80c : fetch_word Ubsan.M.loaded_segments (0x6f80c : word) = Some W_6f80c.
Proof. vm_refl. Qed.
Lemma D_6f80c : decode_any W_6f80c = Some (OpImm ALU_ADD 10 10 2119, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f810 : bv 32 := 0xdd958593.
Lemma F_6f810 : fetch_word Ubsan.M.loaded_segments (0x6f810 : word) = Some W_6f810.
Proof. vm_refl. Qed.
Lemma D_6f810 : decode_any W_6f810 = Some (OpImm ALU_ADD 11 11 3545, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f814 : bv 32 := 0x00100613.
Lemma F_6f814 : fetch_word Ubsan.M.loaded_segments (0x6f814 : word) = Some W_6f814.
Proof. vm_refl. Qed.
Lemma D_6f814 : decode_any W_6f814 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f818 : bv 32 := 0xe59f306f.
Lemma F_6f818 : fetch_word Ubsan.M.loaded_segments (0x6f818 : word) = Some W_6f818.
Proof. vm_refl. Qed.
Lemma D_6f818 : decode_any W_6f818 = Some (Jal 0 2047576, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f81c : bv 32 := 0x000b7517.
Lemma F_6f81c : fetch_word Ubsan.M.loaded_segments (0x6f81c : word) = Some W_6f81c.
Proof. vm_refl. Qed.
Lemma D_6f81c : decode_any W_6f81c = Some (Auipc 10 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f820 : bv 32 := 0x25453503.
Lemma F_6f820 : fetch_word Ubsan.M.loaded_segments (0x6f820 : word) = Some W_6f820.
Proof. vm_refl. Qed.
Lemma D_6f820 : decode_any W_6f820 = Some (Load SZ8 true 10 10 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f824 : bv 32 := 0x00052503.
Lemma F_6f824 : fetch_word Ubsan.M.loaded_segments (0x6f824 : word) = Some W_6f824.
Proof. vm_refl. Qed.
Lemma D_6f824 : decode_any W_6f824 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f828 : bv 32 := 0x00500593.
Lemma F_6f828 : fetch_word Ubsan.M.loaded_segments (0x6f828 : word) = Some W_6f828.
Proof. vm_refl. Qed.
Lemma D_6f828 : decode_any W_6f828 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f82c : bv 32 := 0x00a5ce63.
Lemma F_6f82c : fetch_word Ubsan.M.loaded_segments (0x6f82c : word) = Some W_6f82c.
Proof. vm_refl. Qed.
Lemma D_6f82c : decode_any W_6f82c = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f830 : bv 32 := 0xfffa6517.
Lemma F_6f830 : fetch_word Ubsan.M.loaded_segments (0x6f830 : word) = Some W_6f830.
Proof. vm_refl. Qed.
Lemma D_6f830 : decode_any W_6f830 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f834 : bv 32 := 0xfffae597.
Lemma F_6f834 : fetch_word Ubsan.M.loaded_segments (0x6f834 : word) = Some W_6f834.
Proof. vm_refl. Qed.
Lemma D_6f834 : decode_any W_6f834 = Some (Auipc 11 1048494, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f838 : bv 32 := 0x9ff50513.
Lemma F_6f838 : fetch_word Ubsan.M.loaded_segments (0x6f838 : word) = Some W_6f838.
Proof. vm_refl. Qed.
Lemma D_6f838 : decode_any W_6f838 = Some (OpImm ALU_ADD 10 10 2559, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f83c : bv 32 := 0xdad58593.
Lemma F_6f83c : fetch_word Ubsan.M.loaded_segments (0x6f83c : word) = Some W_6f83c.
Proof. vm_refl. Qed.
Lemma D_6f83c : decode_any W_6f83c = Some (OpImm ALU_ADD 11 11 3501, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f840 : bv 32 := 0x00100613.
Lemma F_6f840 : fetch_word Ubsan.M.loaded_segments (0x6f840 : word) = Some W_6f840.
Proof. vm_refl. Qed.
Lemma D_6f840 : decode_any W_6f840 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f844 : bv 32 := 0xe2df306f.
Lemma F_6f844 : fetch_word Ubsan.M.loaded_segments (0x6f844 : word) = Some W_6f844.
Proof. vm_refl. Qed.
Lemma D_6f844 : decode_any W_6f844 = Some (Jal 0 2047532, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f848 : bv 32 := 0x00100513.
Lemma F_6f848 : fetch_word Ubsan.M.loaded_segments (0x6f848 : word) = Some W_6f848.
Proof. vm_refl. Qed.
Lemma D_6f848 : decode_any W_6f848 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f84c : bv 32 := 0x00008067.
Lemma F_6f84c : fetch_word Ubsan.M.loaded_segments (0x6f84c : word) = Some W_6f84c.
Proof. vm_refl. Qed.
Lemma D_6f84c : decode_any W_6f84c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f850 : bv 32 := 0xc0001073.
Lemma F_6f850 : fetch_word Ubsan.M.loaded_segments (0x6f850 : word) = Some W_6f850.
Proof. vm_refl. Qed.
Lemma D_6f850 : decode_any W_6f850 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
