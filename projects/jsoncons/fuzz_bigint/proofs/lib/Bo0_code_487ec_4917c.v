(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_487ec : bv 32 := 0xf7010113.
Lemma F_487ec : fetch_word AsanUbsan.M.loaded_segments (0x487ec : word) = Some W_487ec.
Proof. vm_refl. Qed.
Lemma D_487ec : decode_any W_487ec = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_487f0 : bv 32 := 0x08113423.
Lemma F_487f0 : fetch_word AsanUbsan.M.loaded_segments (0x487f0 : word) = Some W_487f0.
Proof. vm_refl. Qed.
Lemma D_487f0 : decode_any W_487f0 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_487f4 : bv 32 := 0x08813023.
Lemma F_487f4 : fetch_word AsanUbsan.M.loaded_segments (0x487f4 : word) = Some W_487f4.
Proof. vm_refl. Qed.
Lemma D_487f4 : decode_any W_487f4 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_487f8 : bv 32 := 0x06913c23.
Lemma F_487f8 : fetch_word AsanUbsan.M.loaded_segments (0x487f8 : word) = Some W_487f8.
Proof. vm_refl. Qed.
Lemma D_487f8 : decode_any W_487f8 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_487fc : bv 32 := 0x07213823.
Lemma F_487fc : fetch_word AsanUbsan.M.loaded_segments (0x487fc : word) = Some W_487fc.
Proof. vm_refl. Qed.
Lemma D_487fc : decode_any W_487fc = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_48800 : bv 32 := 0x07313423.
Lemma F_48800 : fetch_word AsanUbsan.M.loaded_segments (0x48800 : word) = Some W_48800.
Proof. vm_refl. Qed.
Lemma D_48800 : decode_any W_48800 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_48804 : bv 32 := 0x07413023.
Lemma F_48804 : fetch_word AsanUbsan.M.loaded_segments (0x48804 : word) = Some W_48804.
Proof. vm_refl. Qed.
Lemma D_48804 : decode_any W_48804 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48808 : bv 32 := 0x05513c23.
Lemma F_48808 : fetch_word AsanUbsan.M.loaded_segments (0x48808 : word) = Some W_48808.
Proof. vm_refl. Qed.
Lemma D_48808 : decode_any W_48808 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4880c : bv 32 := 0x05613823.
Lemma F_4880c : fetch_word AsanUbsan.M.loaded_segments (0x4880c : word) = Some W_4880c.
Proof. vm_refl. Qed.
Lemma D_4880c : decode_any W_4880c = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_48810 : bv 32 := 0x05713423.
Lemma F_48810 : fetch_word AsanUbsan.M.loaded_segments (0x48810 : word) = Some W_48810.
Proof. vm_refl. Qed.
Lemma D_48810 : decode_any W_48810 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48814 : bv 32 := 0x05813023.
Lemma F_48814 : fetch_word AsanUbsan.M.loaded_segments (0x48814 : word) = Some W_48814.
Proof. vm_refl. Qed.
Lemma D_48814 : decode_any W_48814 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48818 : bv 32 := 0x03913c23.
Lemma F_48818 : fetch_word AsanUbsan.M.loaded_segments (0x48818 : word) = Some W_48818.
Proof. vm_refl. Qed.
Lemma D_48818 : decode_any W_48818 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4881c : bv 32 := 0x03a13823.
Lemma F_4881c : fetch_word AsanUbsan.M.loaded_segments (0x4881c : word) = Some W_4881c.
Proof. vm_refl. Qed.
Lemma D_4881c : decode_any W_4881c = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48820 : bv 32 := 0x03b13423.
Lemma F_48820 : fetch_word AsanUbsan.M.loaded_segments (0x48820 : word) = Some W_48820.
Proof. vm_refl. Qed.
Lemma D_48820 : decode_any W_48820 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48824 : bv 32 := 0x00058493.
Lemma F_48824 : fetch_word AsanUbsan.M.loaded_segments (0x48824 : word) = Some W_48824.
Proof. vm_refl. Qed.
Lemma D_48824 : decode_any W_48824 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48828 : bv 32 := 0x00050c93.
Lemma F_48828 : fetch_word AsanUbsan.M.loaded_segments (0x48828 : word) = Some W_48828.
Proof. vm_refl. Qed.
Lemma D_48828 : decode_any W_48828 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4882c : bv 32 := 0x238210ef.
Lemma F_4882c : fetch_word AsanUbsan.M.loaded_segments (0x4882c : word) = Some W_4882c.
Proof. vm_refl. Qed.
Lemma D_4882c : decode_any W_4882c = Some (Jal 1 135736, 4%Z).
Proof. vm_refl. Qed.

Definition W_48830 : bv 32 := 0x26050463.
Lemma F_48830 : fetch_word AsanUbsan.M.loaded_segments (0x48830 : word) = Some W_48830.
Proof. vm_refl. Qed.
Lemma D_48830 : decode_any W_48830 = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_48834 : bv 32 := 0x00050913.
Lemma F_48834 : fetch_word AsanUbsan.M.loaded_segments (0x48834 : word) = Some W_48834.
Proof. vm_refl. Qed.
Lemma D_48834 : decode_any W_48834 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48838 : bv 32 := 0x3f0210ef.
Lemma F_48838 : fetch_word AsanUbsan.M.loaded_segments (0x48838 : word) = Some W_48838.
Proof. vm_refl. Qed.
Lemma D_48838 : decode_any W_48838 = Some (Jal 1 136176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4883c : bv 32 := 0x00050993.
Lemma F_4883c : fetch_word AsanUbsan.M.loaded_segments (0x4883c : word) = Some W_4883c.
Proof. vm_refl. Qed.
Lemma D_4883c : decode_any W_4883c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48840 : bv 32 := 0x00090513.
Lemma F_48840 : fetch_word AsanUbsan.M.loaded_segments (0x48840 : word) = Some W_48840.
Proof. vm_refl. Qed.
Lemma D_48840 : decode_any W_48840 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48844 : bv 32 := 0x43c210ef.
Lemma F_48844 : fetch_word AsanUbsan.M.loaded_segments (0x48844 : word) = Some W_48844.
Proof. vm_refl. Qed.
Lemma D_48844 : decode_any W_48844 = Some (Jal 1 136252, 4%Z).
Proof. vm_refl. Qed.

Definition W_48848 : bv 32 := 0x2499e863.
Lemma F_48848 : fetch_word AsanUbsan.M.loaded_segments (0x48848 : word) = Some W_48848.
Proof. vm_refl. Qed.
Lemma D_48848 : decode_any W_48848 = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_4884c : bv 32 := 0x00050913.
Lemma F_4884c : fetch_word AsanUbsan.M.loaded_segments (0x4884c : word) = Some W_4884c.
Proof. vm_refl. Qed.
Lemma D_4884c : decode_any W_4884c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48850 : bv 32 := 0x24a4e463.
Lemma F_48850 : fetch_word AsanUbsan.M.loaded_segments (0x48850 : word) = Some W_48850.
Proof. vm_refl. Qed.
Lemma D_48850 : decode_any W_48850 = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_48854 : bv 32 := 0x00000d13.
Lemma F_48854 : fetch_word AsanUbsan.M.loaded_segments (0x48854 : word) = Some W_48854.
Proof. vm_refl. Qed.
Lemma D_48854 : decode_any W_48854 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48858 : bv 32 := 0x00001437.
Lemma F_48858 : fetch_word AsanUbsan.M.loaded_segments (0x48858 : word) = Some W_48858.
Proof. vm_refl. Qed.
Lemma D_48858 : decode_any W_48858 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4885c : bv 32 := 0x0008e517.
Lemma F_4885c : fetch_word AsanUbsan.M.loaded_segments (0x4885c : word) = Some W_4885c.
Proof. vm_refl. Qed.
Lemma D_4885c : decode_any W_4885c = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48860 : bv 32 := 0x0008e597.
Lemma F_48860 : fetch_word AsanUbsan.M.loaded_segments (0x48860 : word) = Some W_48860.
Proof. vm_refl. Qed.
Lemma D_48860 : decode_any W_48860 = Some (Auipc 11 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48864 : bv 32 := 0x0008e617.
Lemma F_48864 : fetch_word AsanUbsan.M.loaded_segments (0x48864 : word) = Some W_48864.
Proof. vm_refl. Qed.
Lemma D_48864 : decode_any W_48864 = Some (Auipc 12 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48868 : bv 32 := 0x0008e697.
Lemma F_48868 : fetch_word AsanUbsan.M.loaded_segments (0x48868 : word) = Some W_48868.
Proof. vm_refl. Qed.
Lemma D_48868 : decode_any W_48868 = Some (Auipc 13 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_4886c : bv 32 := 0x0008e717.
Lemma F_4886c : fetch_word AsanUbsan.M.loaded_segments (0x4886c : word) = Some W_4886c.
Proof. vm_refl. Qed.
Lemma D_4886c : decode_any W_4886c = Some (Auipc 14 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48870 : bv 32 := 0xfffc8797.
Lemma F_48870 : fetch_word AsanUbsan.M.loaded_segments (0x48870 : word) = Some W_48870.
Proof. vm_refl. Qed.
Lemma D_48870 : decode_any W_48870 = Some (Auipc 15 1048520, 4%Z).
Proof. vm_refl. Qed.

Definition W_48874 : bv 32 := 0x008c8433.
Lemma F_48874 : fetch_word AsanUbsan.M.loaded_segments (0x48874 : word) = Some W_48874.
Proof. vm_refl. Qed.
Lemma D_48874 : decode_any W_48874 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48878 : bv 32 := 0xc6c53b03.
Lemma F_48878 : fetch_word AsanUbsan.M.loaded_segments (0x48878 : word) = Some W_48878.
Proof. vm_refl. Qed.
Lemma D_48878 : decode_any W_48878 = Some (Load SZ8 true 22 10 3180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4887c : bv 32 := 0xc705b503.
Lemma F_4887c : fetch_word AsanUbsan.M.loaded_segments (0x4887c : word) = Some W_4887c.
Proof. vm_refl. Qed.
Lemma D_4887c : decode_any W_4887c = Some (Load SZ8 true 10 11 3184, 4%Z).
Proof. vm_refl. Qed.

Definition W_48880 : bv 32 := 0x00a13c23.
Lemma F_48880 : fetch_word AsanUbsan.M.loaded_segments (0x48880 : word) = Some W_48880.
Proof. vm_refl. Qed.
Lemma D_48880 : decode_any W_48880 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48884 : bv 32 := 0xc7463503.
Lemma F_48884 : fetch_word AsanUbsan.M.loaded_segments (0x48884 : word) = Some W_48884.
Proof. vm_refl. Qed.
Lemma D_48884 : decode_any W_48884 = Some (Load SZ8 true 10 12 3188, 4%Z).
Proof. vm_refl. Qed.

Definition W_48888 : bv 32 := 0x00a13823.
Lemma F_48888 : fetch_word AsanUbsan.M.loaded_segments (0x48888 : word) = Some W_48888.
Proof. vm_refl. Qed.
Lemma D_48888 : decode_any W_48888 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4888c : bv 32 := 0xc786b503.
Lemma F_4888c : fetch_word AsanUbsan.M.loaded_segments (0x4888c : word) = Some W_4888c.
Proof. vm_refl. Qed.
Lemma D_4888c : decode_any W_4888c = Some (Load SZ8 true 10 13 3192, 4%Z).
Proof. vm_refl. Qed.

Definition W_48890 : bv 32 := 0x00a13423.
Lemma F_48890 : fetch_word AsanUbsan.M.loaded_segments (0x48890 : word) = Some W_48890.
Proof. vm_refl. Qed.
Lemma D_48890 : decode_any W_48890 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48894 : bv 32 := 0xc5473503.
Lemma F_48894 : fetch_word AsanUbsan.M.loaded_segments (0x48894 : word) = Some W_48894.
Proof. vm_refl. Qed.
Lemma D_48894 : decode_any W_48894 = Some (Load SZ8 true 10 14 3156, 4%Z).
Proof. vm_refl. Qed.

Definition W_48898 : bv 32 := 0x00a13023.
Lemma F_48898 : fetch_word AsanUbsan.M.loaded_segments (0x48898 : word) = Some W_48898.
Proof. vm_refl. Qed.
Lemma D_48898 : decode_any W_48898 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4889c : bv 32 := 0xae07bb83.
Lemma F_4889c : fetch_word AsanUbsan.M.loaded_segments (0x4889c : word) = Some W_4889c.
Proof. vm_refl. Qed.
Lemma D_4889c : decode_any W_4889c = Some (Load SZ8 true 23 15 2784, 4%Z).
Proof. vm_refl. Qed.

Definition W_488a0 : bv 32 := 0x00100393.
Lemma F_488a0 : fetch_word AsanUbsan.M.loaded_segments (0x488a0 : word) = Some W_488a0.
Proof. vm_refl. Qed.
Lemma D_488a0 : decode_any W_488a0 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_488a4 : bv 32 := 0x00600e13.
Lemma F_488a4 : fetch_word AsanUbsan.M.loaded_segments (0x488a4 : word) = Some W_488a4.
Proof. vm_refl. Qed.
Lemma D_488a4 : decode_any W_488a4 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_488a8 : bv 32 := 0x00000a13.
Lemma F_488a8 : fetch_word AsanUbsan.M.loaded_segments (0x488a8 : word) = Some W_488a8.
Proof. vm_refl. Qed.
Lemma D_488a8 : decode_any W_488a8 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_488ac : bv 32 := 0x0100006f.
Lemma F_488ac : fetch_word AsanUbsan.M.loaded_segments (0x488ac : word) = Some W_488ac.
Proof. vm_refl. Qed.
Lemma D_488ac : decode_any W_488ac = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_488b0 : bv 32 := 0x001a0a13.
Lemma F_488b0 : fetch_word AsanUbsan.M.loaded_segments (0x488b0 : word) = Some W_488b0.
Proof. vm_refl. Qed.
Lemma D_488b0 : decode_any W_488b0 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_488b4 : bv 32 := 0x00b00513.
Lemma F_488b4 : fetch_word AsanUbsan.M.loaded_segments (0x488b4 : word) = Some W_488b4.
Proof. vm_refl. Qed.
Lemma D_488b4 : decode_any W_488b4 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_488b8 : bv 32 := 0x1caa0e63.
Lemma F_488b8 : fetch_word AsanUbsan.M.loaded_segments (0x488b8 : word) = Some W_488b8.
Proof. vm_refl. Qed.
Lemma D_488b8 : decode_any W_488b8 = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_488bc : bv 32 := 0x00000d93.
Lemma F_488bc : fetch_word AsanUbsan.M.loaded_segments (0x488bc : word) = Some W_488bc.
Proof. vm_refl. Qed.
Lemma D_488bc : decode_any W_488bc = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_488c0 : bv 32 := 0x058cb503.
Lemma F_488c0 : fetch_word AsanUbsan.M.loaded_segments (0x488c0 : word) = Some W_488c0.
Proof. vm_refl. Qed.
Lemma D_488c0 : decode_any W_488c0 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_488c4 : bv 32 := 0x00a00593.
Lemma F_488c4 : fetch_word AsanUbsan.M.loaded_segments (0x488c4 : word) = Some W_488c4.
Proof. vm_refl. Qed.
Lemma D_488c4 : decode_any W_488c4 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_488c8 : bv 32 := 0x414585bb.
Lemma F_488c8 : fetch_word AsanUbsan.M.loaded_segments (0x488c8 : word) = Some W_488c8.
Proof. vm_refl. Qed.
Lemma D_488c8 : decode_any W_488c8 = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_488cc : bv 32 := 0x006a0a93.
Lemma F_488cc : fetch_word AsanUbsan.M.loaded_segments (0x488cc : word) = Some W_488cc.
Proof. vm_refl. Qed.
Lemma D_488cc : decode_any W_488cc = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_488d0 : bv 32 := 0xfff00613.
Lemma F_488d0 : fetch_word AsanUbsan.M.loaded_segments (0x488d0 : word) = Some W_488d0.
Proof. vm_refl. Qed.
Lemma D_488d0 : decode_any W_488d0 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_488d4 : bv 32 := 0x00b615b3.
Lemma F_488d4 : fetch_word AsanUbsan.M.loaded_segments (0x488d4 : word) = Some W_488d4.
Proof. vm_refl. Qed.
Lemma D_488d4 : decode_any W_488d4 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_488d8 : bv 32 := 0x3ff5f593.
Lemma F_488d8 : fetch_word AsanUbsan.M.loaded_segments (0x488d8 : word) = Some W_488d8.
Proof. vm_refl. Qed.
Lemma D_488d8 : decode_any W_488d8 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_488dc : bv 32 := 0xff150613.
Lemma F_488dc : fetch_word AsanUbsan.M.loaded_segments (0x488dc : word) = Some W_488dc.
Proof. vm_refl. Qed.
Lemma D_488dc : decode_any W_488dc = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_488e0 : bv 32 := 0x414509b3.
Lemma F_488e0 : fetch_word AsanUbsan.M.loaded_segments (0x488e0 : word) = Some W_488e0.
Proof. vm_refl. Qed.
Lemma D_488e0 : decode_any W_488e0 = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_488e4 : bv 32 := 0x00c59c33.
Lemma F_488e4 : fetch_word AsanUbsan.M.loaded_segments (0x488e4 : word) = Some W_488e4.
Proof. vm_refl. Qed.
Lemma D_488e4 : decode_any W_488e4 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_488e8 : bv 32 := 0xffa98993.
Lemma F_488e8 : fetch_word AsanUbsan.M.loaded_segments (0x488e8 : word) = Some W_488e8.
Proof. vm_refl. Qed.
Lemma D_488e8 : decode_any W_488e8 = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_488ec : bv 32 := 0x01840c33.
Lemma F_488ec : fetch_word AsanUbsan.M.loaded_segments (0x488ec : word) = Some W_488ec.
Proof. vm_refl. Qed.
Lemma D_488ec : decode_any W_488ec = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_488f0 : bv 32 := 0x04000513.
Lemma F_488f0 : fetch_word AsanUbsan.M.loaded_segments (0x488f0 : word) = Some W_488f0.
Proof. vm_refl. Qed.
Lemma D_488f0 : decode_any W_488f0 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_488f4 : bv 32 := 0x01451533.
Lemma F_488f4 : fetch_word AsanUbsan.M.loaded_segments (0x488f4 : word) = Some W_488f4.
Proof. vm_refl. Qed.
Lemma D_488f4 : decode_any W_488f4 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_488f8 : bv 32 := 0x02a13023.
Lemma F_488f8 : fetch_word AsanUbsan.M.loaded_segments (0x488f8 : word) = Some W_488f8.
Proof. vm_refl. Qed.
Lemma D_488f8 : decode_any W_488f8 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_488fc : bv 32 := 0x0240006f.
Lemma F_488fc : fetch_word AsanUbsan.M.loaded_segments (0x488fc : word) = Some W_488fc.
Proof. vm_refl. Qed.
Lemma D_488fc : decode_any W_488fc = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_48900 : bv 32 := 0x0f500613.
Lemma F_48900 : fetch_word AsanUbsan.M.loaded_segments (0x48900 : word) = Some W_48900.
Proof. vm_refl. Qed.
Lemma D_48900 : decode_any W_48900 = Some (OpImm ALU_ADD 12 0 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_48904 : bv 32 := 0x02013583.
Lemma F_48904 : fetch_word AsanUbsan.M.loaded_segments (0x48904 : word) = Some W_48904.
Proof. vm_refl. Qed.
Lemma D_48904 : decode_any W_48904 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48908 : bv 32 := 0x0f1180ef.
Lemma F_48908 : fetch_word AsanUbsan.M.loaded_segments (0x48908 : word) = Some W_48908.
Proof. vm_refl. Qed.
Lemma D_48908 : decode_any W_48908 = Some (Jal 1 100592, 4%Z).
Proof. vm_refl. Qed.

Definition W_4890c : bv 32 := 0x00600e13.
Lemma F_4890c : fetch_word AsanUbsan.M.loaded_segments (0x4890c : word) = Some W_4890c.
Proof. vm_refl. Qed.
Lemma D_4890c : decode_any W_4890c = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_48910 : bv 32 := 0x00100393.
Lemma F_48910 : fetch_word AsanUbsan.M.loaded_segments (0x48910 : word) = Some W_48910.
Proof. vm_refl. Qed.
Lemma D_48910 : decode_any W_48910 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48914 : bv 32 := 0x001d8d93.
Lemma F_48914 : fetch_word AsanUbsan.M.loaded_segments (0x48914 : word) = Some W_48914.
Proof. vm_refl. Qed.
Lemma D_48914 : decode_any W_48914 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48918 : bv 32 := 0x013dd533.
Lemma F_48918 : fetch_word AsanUbsan.M.loaded_segments (0x48918 : word) = Some W_48918.
Proof. vm_refl. Qed.
Lemma D_48918 : decode_any W_48918 = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4891c : bv 32 := 0xf8051ae3.
Lemma F_4891c : fetch_word AsanUbsan.M.loaded_segments (0x4891c : word) = Some W_4891c.
Proof. vm_refl. Qed.
Lemma D_4891c : decode_any W_4891c = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_48920 : bv 32 := 0x01bc05b3.
Lemma F_48920 : fetch_word AsanUbsan.M.loaded_segments (0x48920 : word) = Some W_48920.
Proof. vm_refl. Qed.
Lemma D_48920 : decode_any W_48920 = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_48924 : bv 32 := 0x0005c503.
Lemma F_48924 : fetch_word AsanUbsan.M.loaded_segments (0x48924 : word) = Some W_48924.
Proof. vm_refl. Qed.
Lemma D_48924 : decode_any W_48924 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48928 : bv 32 := 0xfe0506e3.
Lemma F_48928 : fetch_word AsanUbsan.M.loaded_segments (0x48928 : word) = Some W_48928.
Proof. vm_refl. Qed.
Lemma D_48928 : decode_any W_48928 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_4892c : bv 32 := 0x058cb503.
Lemma F_4892c : fetch_word AsanUbsan.M.loaded_segments (0x4892c : word) = Some W_4892c.
Proof. vm_refl. Qed.
Lemma D_4892c : decode_any W_4892c = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48930 : bv 32 := 0xffb50613.
Lemma F_48930 : fetch_word AsanUbsan.M.loaded_segments (0x48930 : word) = Some W_48930.
Proof. vm_refl. Qed.
Lemma D_48930 : decode_any W_48930 = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_48934 : bv 32 := 0x00aa1533.
Lemma F_48934 : fetch_word AsanUbsan.M.loaded_segments (0x48934 : word) = Some W_48934.
Proof. vm_refl. Qed.
Lemma D_48934 : decode_any W_48934 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48938 : bv 32 := 0x00c39633.
Lemma F_48938 : fetch_word AsanUbsan.M.loaded_segments (0x48938 : word) = Some W_48938.
Proof. vm_refl. Qed.
Lemma D_48938 : decode_any W_48938 = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4893c : bv 32 := 0x00a40533.
Lemma F_4893c : fetch_word AsanUbsan.M.loaded_segments (0x4893c : word) = Some W_4893c.
Proof. vm_refl. Qed.
Lemma D_4893c : decode_any W_4893c = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48940 : bv 32 := 0x00c50533.
Lemma F_48940 : fetch_word AsanUbsan.M.loaded_segments (0x48940 : word) = Some W_48940.
Proof. vm_refl. Qed.
Lemma D_48940 : decode_any W_48940 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48944 : bv 32 := 0x015d9633.
Lemma F_48944 : fetch_word AsanUbsan.M.loaded_segments (0x48944 : word) = Some W_48944.
Proof. vm_refl. Qed.
Lemma D_48944 : decode_any W_48944 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_48948 : bv 32 := 0x00c50533.
Lemma F_48948 : fetch_word AsanUbsan.M.loaded_segments (0x48948 : word) = Some W_48948.
Proof. vm_refl. Qed.
Lemma D_48948 : decode_any W_48948 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4894c : bv 32 := 0x01853603.
Lemma F_4894c : fetch_word AsanUbsan.M.loaded_segments (0x4894c : word) = Some W_4894c.
Proof. vm_refl. Qed.
Lemma D_4894c : decode_any W_4894c = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48950 : bv 32 := 0xfcc972e3.
Lemma F_48950 : fetch_word AsanUbsan.M.loaded_segments (0x48950 : word) = Some W_48950.
Proof. vm_refl. Qed.
Lemma D_48950 : decode_any W_48950 = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_48954 : bv 32 := 0xfc9670e3.
Lemma F_48954 : fetch_word AsanUbsan.M.loaded_segments (0x48954 : word) = Some W_48954.
Proof. vm_refl. Qed.
Lemma D_48954 : decode_any W_48954 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_48958 : bv 32 := 0x01a58023.
Lemma F_48958 : fetch_word AsanUbsan.M.loaded_segments (0x48958 : word) = Some W_48958.
Proof. vm_refl. Qed.
Lemma D_48958 : decode_any W_48958 = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4895c : bv 32 := 0x000b3583.
Lemma F_4895c : fetch_word AsanUbsan.M.loaded_segments (0x4895c : word) = Some W_4895c.
Proof. vm_refl. Qed.
Lemma D_4895c : decode_any W_4895c = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48960 : bv 32 := 0xfff58613.
Lemma F_48960 : fetch_word AsanUbsan.M.loaded_segments (0x48960 : word) = Some W_48960.
Proof. vm_refl. Qed.
Lemma D_48960 : decode_any W_48960 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48964 : bv 32 := 0x00c5b6b3.
Lemma F_48964 : fetch_word AsanUbsan.M.loaded_segments (0x48964 : word) = Some W_48964.
Proof. vm_refl. Qed.
Lemma D_48964 : decode_any W_48964 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48968 : bv 32 := 0xfff68693.
Lemma F_48968 : fetch_word AsanUbsan.M.loaded_segments (0x48968 : word) = Some W_48968.
Proof. vm_refl. Qed.
Lemma D_48968 : decode_any W_48968 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4896c : bv 32 := 0x00c6f6b3.
Lemma F_4896c : fetch_word AsanUbsan.M.loaded_segments (0x4896c : word) = Some W_4896c.
Proof. vm_refl. Qed.
Lemma D_4896c : decode_any W_4896c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48970 : bv 32 := 0x02a6fc63.
Lemma F_48970 : fetch_word AsanUbsan.M.loaded_segments (0x48970 : word) = Some W_48970.
Proof. vm_refl. Qed.
Lemma D_48970 : decode_any W_48970 = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_48974 : bv 32 := 0x01813683.
Lemma F_48974 : fetch_word AsanUbsan.M.loaded_segments (0x48974 : word) = Some W_48974.
Proof. vm_refl. Qed.
Lemma D_48974 : decode_any W_48974 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48978 : bv 32 := 0x0006b803.
Lemma F_48978 : fetch_word AsanUbsan.M.loaded_segments (0x48978 : word) = Some W_48978.
Proof. vm_refl. Qed.
Lemma D_48978 : decode_any W_48978 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4897c : bv 32 := 0x01013683.
Lemma F_4897c : fetch_word AsanUbsan.M.loaded_segments (0x4897c : word) = Some W_4897c.
Proof. vm_refl. Qed.
Lemma D_4897c : decode_any W_4897c = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48980 : bv 32 := 0x0006b683.
Lemma F_48980 : fetch_word AsanUbsan.M.loaded_segments (0x48980 : word) = Some W_48980.
Proof. vm_refl. Qed.
Lemma D_48980 : decode_any W_48980 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48984 : bv 32 := 0xfff80793.
Lemma F_48984 : fetch_word AsanUbsan.M.loaded_segments (0x48984 : word) = Some W_48984.
Proof. vm_refl. Qed.
Lemma D_48984 : decode_any W_48984 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48988 : bv 32 := 0x00a7f463.
Lemma F_48988 : fetch_word AsanUbsan.M.loaded_segments (0x48988 : word) = Some W_48988.
Proof. vm_refl. Qed.
Lemma D_48988 : decode_any W_48988 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4898c : bv 32 := 0x00a6fe63.
Lemma F_4898c : fetch_word AsanUbsan.M.loaded_segments (0x4898c : word) = Some W_4898c.
Proof. vm_refl. Qed.
Lemma D_4898c : decode_any W_4898c = Some (Branch BC_GEU 13 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_48990 : bv 32 := 0x00813703.
Lemma F_48990 : fetch_word AsanUbsan.M.loaded_segments (0x48990 : word) = Some W_48990.
Proof. vm_refl. Qed.
Lemma D_48990 : decode_any W_48990 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48994 : bv 32 := 0x00073283.
Lemma F_48994 : fetch_word AsanUbsan.M.loaded_segments (0x48994 : word) = Some W_48994.
Proof. vm_refl. Qed.
Lemma D_48994 : decode_any W_48994 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48998 : bv 32 := 0x0032d713.
Lemma F_48998 : fetch_word AsanUbsan.M.loaded_segments (0x48998 : word) = Some W_48998.
Proof. vm_refl. Qed.
Lemma D_48998 : decode_any W_48998 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4899c : bv 32 := 0x00b708b3.
Lemma F_4899c : fetch_word AsanUbsan.M.loaded_segments (0x4899c : word) = Some W_4899c.
Proof. vm_refl. Qed.
Lemma D_4899c : decode_any W_4899c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_489a0 : bv 32 := 0x02a2e863.
Lemma F_489a0 : fetch_word AsanUbsan.M.loaded_segments (0x489a0 : word) = Some W_489a0.
Proof. vm_refl. Qed.
Lemma D_489a0 : decode_any W_489a0 = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_489a4 : bv 32 := 0x02a8f663.
Lemma F_489a4 : fetch_word AsanUbsan.M.loaded_segments (0x489a4 : word) = Some W_489a4.
Proof. vm_refl. Qed.
Lemma D_489a4 : decode_any W_489a4 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_489a8 : bv 32 := 0xf54e6ce3.
Lemma F_489a8 : fetch_word AsanUbsan.M.loaded_segments (0x489a8 : word) = Some W_489a8.
Proof. vm_refl. Qed.
Lemma D_489a8 : decode_any W_489a8 = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_489ac : bv 32 := 0x00355513.
Lemma F_489ac : fetch_word AsanUbsan.M.loaded_segments (0x489ac : word) = Some W_489ac.
Proof. vm_refl. Qed.
Lemma D_489ac : decode_any W_489ac = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_489b0 : bv 32 := 0x00a585b3.
Lemma F_489b0 : fetch_word AsanUbsan.M.loaded_segments (0x489b0 : word) = Some W_489b0.
Proof. vm_refl. Qed.
Lemma D_489b0 : decode_any W_489b0 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_489b4 : bv 32 := 0x00100513.
Lemma F_489b4 : fetch_word AsanUbsan.M.loaded_segments (0x489b4 : word) = Some W_489b4.
Proof. vm_refl. Qed.
Lemma D_489b4 : decode_any W_489b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_489b8 : bv 32 := 0x0175b023.
Lemma F_489b8 : fetch_word AsanUbsan.M.loaded_segments (0x489b8 : word) = Some W_489b8.
Proof. vm_refl. Qed.
Lemma D_489b8 : decode_any W_489b8 = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_489bc : bv 32 := 0x01455633.
Lemma F_489bc : fetch_word AsanUbsan.M.loaded_segments (0x489bc : word) = Some W_489bc.
Proof. vm_refl. Qed.
Lemma D_489bc : decode_any W_489bc = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_489c0 : bv 32 := 0x00858593.
Lemma F_489c0 : fetch_word AsanUbsan.M.loaded_segments (0x489c0 : word) = Some W_489c0.
Proof. vm_refl. Qed.
Lemma D_489c0 : decode_any W_489c0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_489c4 : bv 32 := 0x00150513.
Lemma F_489c4 : fetch_word AsanUbsan.M.loaded_segments (0x489c4 : word) = Some W_489c4.
Proof. vm_refl. Qed.
Lemma D_489c4 : decode_any W_489c4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_489c8 : bv 32 := 0xfe0608e3.
Lemma F_489c8 : fetch_word AsanUbsan.M.loaded_segments (0x489c8 : word) = Some W_489c8.
Proof. vm_refl. Qed.
Lemma D_489c8 : decode_any W_489c8 = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_489cc : bv 32 := 0xf49ff06f.
Lemma F_489cc : fetch_word AsanUbsan.M.loaded_segments (0x489cc : word) = Some W_489cc.
Proof. vm_refl. Qed.
Lemma D_489cc : decode_any W_489cc = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_489d0 : bv 32 := 0x00013283.
Lemma F_489d0 : fetch_word AsanUbsan.M.loaded_segments (0x489d0 : word) = Some W_489d0.
Proof. vm_refl. Qed.
Lemma D_489d0 : decode_any W_489d0 = Some (Load SZ8 true 5 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_489d4 : bv 32 := 0x04e2c283.
Lemma F_489d4 : fetch_word AsanUbsan.M.loaded_segments (0x489d4 : word) = Some W_489d4.
Proof. vm_refl. Qed.
Lemma D_489d4 : decode_any W_489d4 = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_489d8 : bv 32 := 0x08029e63.
Lemma F_489d8 : fetch_word AsanUbsan.M.loaded_segments (0x489d8 : word) = Some W_489d8.
Proof. vm_refl. Qed.
Lemma D_489d8 : decode_any W_489d8 = Some (Branch BC_NE 5 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_489dc : bv 32 := 0x04080063.
Lemma F_489dc : fetch_word AsanUbsan.M.loaded_segments (0x489dc : word) = Some W_489dc.
Proof. vm_refl. Qed.
Lemma D_489dc : decode_any W_489dc = Some (Branch BC_EQ 16 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_489e0 : bv 32 := 0x00385813.
Lemma F_489e0 : fetch_word AsanUbsan.M.loaded_segments (0x489e0 : word) = Some W_489e0.
Proof. vm_refl. Qed.
Lemma D_489e0 : decode_any W_489e0 = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_489e4 : bv 32 := 0x00c80833.
Lemma F_489e4 : fetch_word AsanUbsan.M.loaded_segments (0x489e4 : word) = Some W_489e4.
Proof. vm_refl. Qed.
Lemma D_489e4 : decode_any W_489e4 = Some (Op ALU_ADD 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_489e8 : bv 32 := 0x06a87063.
Lemma F_489e8 : fetch_word AsanUbsan.M.loaded_segments (0x489e8 : word) = Some W_489e8.
Proof. vm_refl. Qed.
Lemma D_489e8 : decode_any W_489e8 = Some (Branch BC_GEU 16 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_489ec : bv 32 := 0x00158813.
Lemma F_489ec : fetch_word AsanUbsan.M.loaded_segments (0x489ec : word) = Some W_489ec.
Proof. vm_refl. Qed.
Lemma D_489ec : decode_any W_489ec = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_489f0 : bv 32 := 0x00a7e863.
Lemma F_489f0 : fetch_word AsanUbsan.M.loaded_segments (0x489f0 : word) = Some W_489f0.
Proof. vm_refl. Qed.
Lemma D_489f0 : decode_any W_489f0 = Some (Branch BC_LTU 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_489f4 : bv 32 := 0x0036d793.
Lemma F_489f4 : fetch_word AsanUbsan.M.loaded_segments (0x489f4 : word) = Some W_489f4.
Proof. vm_refl. Qed.
Lemma D_489f4 : decode_any W_489f4 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_489f8 : bv 32 := 0x010787b3.
Lemma F_489f8 : fetch_word AsanUbsan.M.loaded_segments (0x489f8 : word) = Some W_489f8.
Proof. vm_refl. Qed.
Lemma D_489f8 : decode_any W_489f8 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_489fc : bv 32 := 0xfaf576e3.
Lemma F_489fc : fetch_word AsanUbsan.M.loaded_segments (0x489fc : word) = Some W_489fc.
Proof. vm_refl. Qed.
Lemma D_489fc : decode_any W_489fc = Some (Branch BC_GEU 10 15 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a00 : bv 32 := 0x00168693.
Lemma F_48a00 : fetch_word AsanUbsan.M.loaded_segments (0x48a00 : word) = Some W_48a00.
Proof. vm_refl. Qed.
Lemma D_48a00 : decode_any W_48a00 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a04 : bv 32 := 0x06d56863.
Lemma F_48a04 : fetch_word AsanUbsan.M.loaded_segments (0x48a04 : word) = Some W_48a04.
Proof. vm_refl. Qed.
Lemma D_48a04 : decode_any W_48a04 = Some (Branch BC_LTU 10 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a08 : bv 32 := 0x01070733.
Lemma F_48a08 : fetch_word AsanUbsan.M.loaded_segments (0x48a08 : word) = Some W_48a08.
Proof. vm_refl. Qed.
Lemma D_48a08 : decode_any W_48a08 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a0c : bv 32 := 0x00375713.
Lemma F_48a0c : fetch_word AsanUbsan.M.loaded_segments (0x48a0c : word) = Some W_48a0c.
Proof. vm_refl. Qed.
Lemma D_48a0c : decode_any W_48a0c = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a10 : bv 32 := 0x00c70633.
Lemma F_48a10 : fetch_word AsanUbsan.M.loaded_segments (0x48a10 : word) = Some W_48a10.
Proof. vm_refl. Qed.
Lemma D_48a10 : decode_any W_48a10 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a14 : bv 32 := 0xf8a67ae3.
Lemma F_48a14 : fetch_word AsanUbsan.M.loaded_segments (0x48a14 : word) = Some W_48a14.
Proof. vm_refl. Qed.
Lemma D_48a14 : decode_any W_48a14 = Some (Branch BC_GEU 12 10 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a18 : bv 32 := 0x05c0006f.
Lemma F_48a18 : fetch_word AsanUbsan.M.loaded_segments (0x48a18 : word) = Some W_48a18.
Proof. vm_refl. Qed.
Lemma D_48a18 : decode_any W_48a18 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a1c : bv 32 := 0x04058463.
Lemma F_48a1c : fetch_word AsanUbsan.M.loaded_segments (0x48a1c : word) = Some W_48a1c.
Proof. vm_refl. Qed.
Lemma D_48a1c : decode_any W_48a1c = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a20 : bv 32 := 0x00365693.
Lemma F_48a20 : fetch_word AsanUbsan.M.loaded_segments (0x48a20 : word) = Some W_48a20.
Proof. vm_refl. Qed.
Lemma D_48a20 : decode_any W_48a20 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a24 : bv 32 := 0x00b686b3.
Lemma F_48a24 : fetch_word AsanUbsan.M.loaded_segments (0x48a24 : word) = Some W_48a24.
Proof. vm_refl. Qed.
Lemma D_48a24 : decode_any W_48a24 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a28 : bv 32 := 0x00068663.
Lemma F_48a28 : fetch_word AsanUbsan.M.loaded_segments (0x48a28 : word) = Some W_48a28.
Proof. vm_refl. Qed.
Lemma D_48a28 : decode_any W_48a28 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a2c : bv 32 := 0x00168693.
Lemma F_48a2c : fetch_word AsanUbsan.M.loaded_segments (0x48a2c : word) = Some W_48a2c.
Proof. vm_refl. Qed.
Lemma D_48a2c : decode_any W_48a2c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a30 : bv 32 := 0x04d56263.
Lemma F_48a30 : fetch_word AsanUbsan.M.loaded_segments (0x48a30 : word) = Some W_48a30.
Proof. vm_refl. Qed.
Lemma D_48a30 : decode_any W_48a30 = Some (Branch BC_LTU 10 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a34 : bv 32 := 0x00188893.
Lemma F_48a34 : fetch_word AsanUbsan.M.loaded_segments (0x48a34 : word) = Some W_48a34.
Proof. vm_refl. Qed.
Lemma D_48a34 : decode_any W_48a34 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a38 : bv 32 := 0x0038d693.
Lemma F_48a38 : fetch_word AsanUbsan.M.loaded_segments (0x48a38 : word) = Some W_48a38.
Proof. vm_refl. Qed.
Lemma D_48a38 : decode_any W_48a38 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a3c : bv 32 := 0x00c68633.
Lemma F_48a3c : fetch_word AsanUbsan.M.loaded_segments (0x48a3c : word) = Some W_48a3c.
Proof. vm_refl. Qed.
Lemma D_48a3c : decode_any W_48a3c = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a40 : bv 32 := 0xf6a674e3.
Lemma F_48a40 : fetch_word AsanUbsan.M.loaded_segments (0x48a40 : word) = Some W_48a40.
Proof. vm_refl. Qed.
Lemma D_48a40 : decode_any W_48a40 = Some (Branch BC_GEU 12 10 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a44 : bv 32 := 0x0300006f.
Lemma F_48a44 : fetch_word AsanUbsan.M.loaded_segments (0x48a44 : word) = Some W_48a44.
Proof. vm_refl. Qed.
Lemma D_48a44 : decode_any W_48a44 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a48 : bv 32 := 0xf60580e3.
Lemma F_48a48 : fetch_word AsanUbsan.M.loaded_segments (0x48a48 : word) = Some W_48a48.
Proof. vm_refl. Qed.
Lemma D_48a48 : decode_any W_48a48 = Some (Branch BC_EQ 11 0 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a4c : bv 32 := 0x00365613.
Lemma F_48a4c : fetch_word AsanUbsan.M.loaded_segments (0x48a4c : word) = Some W_48a4c.
Proof. vm_refl. Qed.
Lemma D_48a4c : decode_any W_48a4c = Some (ShiftImm ALU_SRL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a50 : bv 32 := 0x00b60633.
Lemma F_48a50 : fetch_word AsanUbsan.M.loaded_segments (0x48a50 : word) = Some W_48a50.
Proof. vm_refl. Qed.
Lemma D_48a50 : decode_any W_48a50 = Some (Op ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a54 : bv 32 := 0xf4060ae3.
Lemma F_48a54 : fetch_word AsanUbsan.M.loaded_segments (0x48a54 : word) = Some W_48a54.
Proof. vm_refl. Qed.
Lemma D_48a54 : decode_any W_48a54 = Some (Branch BC_EQ 12 0 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a58 : bv 32 := 0x00160613.
Lemma F_48a58 : fetch_word AsanUbsan.M.loaded_segments (0x48a58 : word) = Some W_48a58.
Proof. vm_refl. Qed.
Lemma D_48a58 : decode_any W_48a58 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a5c : bv 32 := 0xf4c576e3.
Lemma F_48a5c : fetch_word AsanUbsan.M.loaded_segments (0x48a5c : word) = Some W_48a5c.
Proof. vm_refl. Qed.
Lemma D_48a5c : decode_any W_48a5c = Some (Branch BC_GEU 10 12 8012, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a60 : bv 32 := 0x0140006f.
Lemma F_48a60 : fetch_word AsanUbsan.M.loaded_segments (0x48a60 : word) = Some W_48a60.
Proof. vm_refl. Qed.
Lemma D_48a60 : decode_any W_48a60 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a64 : bv 32 := 0x00170713.
Lemma F_48a64 : fetch_word AsanUbsan.M.loaded_segments (0x48a64 : word) = Some W_48a64.
Proof. vm_refl. Qed.
Lemma D_48a64 : decode_any W_48a64 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a68 : bv 32 := 0x00375713.
Lemma F_48a68 : fetch_word AsanUbsan.M.loaded_segments (0x48a68 : word) = Some W_48a68.
Proof. vm_refl. Qed.
Lemma D_48a68 : decode_any W_48a68 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a6c : bv 32 := 0xfff70713.
Lemma F_48a6c : fetch_word AsanUbsan.M.loaded_segments (0x48a6c : word) = Some W_48a6c.
Proof. vm_refl. Qed.
Lemma D_48a6c : decode_any W_48a6c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a70 : bv 32 := 0xf2a77ce3.
Lemma F_48a70 : fetch_word AsanUbsan.M.loaded_segments (0x48a70 : word) = Some W_48a70.
Proof. vm_refl. Qed.
Lemma D_48a70 : decode_any W_48a70 = Some (Branch BC_GEU 14 10 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a74 : bv 32 := 0xfffd9517.
Lemma F_48a74 : fetch_word AsanUbsan.M.loaded_segments (0x48a74 : word) = Some W_48a74.
Proof. vm_refl. Qed.
Lemma D_48a74 : decode_any W_48a74 = Some (Auipc 10 1048537, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a78 : bv 32 := 0xfffcf597.
Lemma F_48a78 : fetch_word AsanUbsan.M.loaded_segments (0x48a78 : word) = Some W_48a78.
Proof. vm_refl. Qed.
Lemma D_48a78 : decode_any W_48a78 = Some (Auipc 11 1048527, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a7c : bv 32 := 0x92650513.
Lemma F_48a7c : fetch_word AsanUbsan.M.loaded_segments (0x48a7c : word) = Some W_48a7c.
Proof. vm_refl. Qed.
Lemma D_48a7c : decode_any W_48a7c = Some (OpImm ALU_ADD 10 10 2342, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a80 : bv 32 := 0xde858613.
Lemma F_48a80 : fetch_word AsanUbsan.M.loaded_segments (0x48a80 : word) = Some W_48a80.
Proof. vm_refl. Qed.
Lemma D_48a80 : decode_any W_48a80 = Some (OpImm ALU_ADD 12 11 3560, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a84 : bv 32 := 0x17700593.
Lemma F_48a84 : fetch_word AsanUbsan.M.loaded_segments (0x48a84 : word) = Some W_48a84.
Proof. vm_refl. Qed.
Lemma D_48a84 : decode_any W_48a84 = Some (OpImm ALU_ADD 11 0 375, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a88 : bv 32 := 0x00000693.
Lemma F_48a88 : fetch_word AsanUbsan.M.loaded_segments (0x48a88 : word) = Some W_48a88.
Proof. vm_refl. Qed.
Lemma D_48a88 : decode_any W_48a88 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a8c : bv 32 := 0x00000713.
Lemma F_48a8c : fetch_word AsanUbsan.M.loaded_segments (0x48a8c : word) = Some W_48a8c.
Proof. vm_refl. Qed.
Lemma D_48a8c : decode_any W_48a8c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a90 : bv 32 := 0x059300ef.
Lemma F_48a90 : fetch_word AsanUbsan.M.loaded_segments (0x48a90 : word) = Some W_48a90.
Proof. vm_refl. Qed.
Lemma D_48a90 : decode_any W_48a90 = Some (Jal 1 198744, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a94 : bv 32 := 0x060c8023.
Lemma F_48a94 : fetch_word AsanUbsan.M.loaded_segments (0x48a94 : word) = Some W_48a94.
Proof. vm_refl. Qed.
Lemma D_48a94 : decode_any W_48a94 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a98 : bv 32 := 0x08813083.
Lemma F_48a98 : fetch_word AsanUbsan.M.loaded_segments (0x48a98 : word) = Some W_48a98.
Proof. vm_refl. Qed.
Lemma D_48a98 : decode_any W_48a98 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_48a9c : bv 32 := 0x08013403.
Lemma F_48a9c : fetch_word AsanUbsan.M.loaded_segments (0x48a9c : word) = Some W_48a9c.
Proof. vm_refl. Qed.
Lemma D_48a9c : decode_any W_48a9c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_48aa0 : bv 32 := 0x07813483.
Lemma F_48aa0 : fetch_word AsanUbsan.M.loaded_segments (0x48aa0 : word) = Some W_48aa0.
Proof. vm_refl. Qed.
Lemma D_48aa0 : decode_any W_48aa0 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_48aa4 : bv 32 := 0x07013903.
Lemma F_48aa4 : fetch_word AsanUbsan.M.loaded_segments (0x48aa4 : word) = Some W_48aa4.
Proof. vm_refl. Qed.
Lemma D_48aa4 : decode_any W_48aa4 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_48aa8 : bv 32 := 0x06813983.
Lemma F_48aa8 : fetch_word AsanUbsan.M.loaded_segments (0x48aa8 : word) = Some W_48aa8.
Proof. vm_refl. Qed.
Lemma D_48aa8 : decode_any W_48aa8 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_48aac : bv 32 := 0x06013a03.
Lemma F_48aac : fetch_word AsanUbsan.M.loaded_segments (0x48aac : word) = Some W_48aac.
Proof. vm_refl. Qed.
Lemma D_48aac : decode_any W_48aac = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ab0 : bv 32 := 0x05813a83.
Lemma F_48ab0 : fetch_word AsanUbsan.M.loaded_segments (0x48ab0 : word) = Some W_48ab0.
Proof. vm_refl. Qed.
Lemma D_48ab0 : decode_any W_48ab0 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ab4 : bv 32 := 0x05013b03.
Lemma F_48ab4 : fetch_word AsanUbsan.M.loaded_segments (0x48ab4 : word) = Some W_48ab4.
Proof. vm_refl. Qed.
Lemma D_48ab4 : decode_any W_48ab4 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ab8 : bv 32 := 0x04813b83.
Lemma F_48ab8 : fetch_word AsanUbsan.M.loaded_segments (0x48ab8 : word) = Some W_48ab8.
Proof. vm_refl. Qed.
Lemma D_48ab8 : decode_any W_48ab8 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48abc : bv 32 := 0x04013c03.
Lemma F_48abc : fetch_word AsanUbsan.M.loaded_segments (0x48abc : word) = Some W_48abc.
Proof. vm_refl. Qed.
Lemma D_48abc : decode_any W_48abc = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ac0 : bv 32 := 0x03813c83.
Lemma F_48ac0 : fetch_word AsanUbsan.M.loaded_segments (0x48ac0 : word) = Some W_48ac0.
Proof. vm_refl. Qed.
Lemma D_48ac0 : decode_any W_48ac0 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ac4 : bv 32 := 0x03013d03.
Lemma F_48ac4 : fetch_word AsanUbsan.M.loaded_segments (0x48ac4 : word) = Some W_48ac4.
Proof. vm_refl. Qed.
Lemma D_48ac4 : decode_any W_48ac4 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ac8 : bv 32 := 0x02813d83.
Lemma F_48ac8 : fetch_word AsanUbsan.M.loaded_segments (0x48ac8 : word) = Some W_48ac8.
Proof. vm_refl. Qed.
Lemma D_48ac8 : decode_any W_48ac8 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48acc : bv 32 := 0x09010113.
Lemma F_48acc : fetch_word AsanUbsan.M.loaded_segments (0x48acc : word) = Some W_48acc.
Proof. vm_refl. Qed.
Lemma D_48acc : decode_any W_48acc = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ad0 : bv 32 := 0x00008067.
Lemma F_48ad0 : fetch_word AsanUbsan.M.loaded_segments (0x48ad0 : word) = Some W_48ad0.
Proof. vm_refl. Qed.
Lemma D_48ad0 : decode_any W_48ad0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ad4 : bv 32 := 0x00100593.
Lemma F_48ad4 : fetch_word AsanUbsan.M.loaded_segments (0x48ad4 : word) = Some W_48ad4.
Proof. vm_refl. Qed.
Lemma D_48ad4 : decode_any W_48ad4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ad8 : bv 32 := 0x06b50023.
Lemma F_48ad8 : fetch_word AsanUbsan.M.loaded_segments (0x48ad8 : word) = Some W_48ad8.
Proof. vm_refl. Qed.
Lemma D_48ad8 : decode_any W_48ad8 = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48adc : bv 32 := 0x00008067.
Lemma F_48adc : fetch_word AsanUbsan.M.loaded_segments (0x48adc : word) = Some W_48adc.
Proof. vm_refl. Qed.
Lemma D_48adc : decode_any W_48adc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ae0 : bv 32 := 0xf9010113.
Lemma F_48ae0 : fetch_word AsanUbsan.M.loaded_segments (0x48ae0 : word) = Some W_48ae0.
Proof. vm_refl. Qed.
Lemma D_48ae0 : decode_any W_48ae0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ae4 : bv 32 := 0x06113423.
Lemma F_48ae4 : fetch_word AsanUbsan.M.loaded_segments (0x48ae4 : word) = Some W_48ae4.
Proof. vm_refl. Qed.
Lemma D_48ae4 : decode_any W_48ae4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ae8 : bv 32 := 0x06813023.
Lemma F_48ae8 : fetch_word AsanUbsan.M.loaded_segments (0x48ae8 : word) = Some W_48ae8.
Proof. vm_refl. Qed.
Lemma D_48ae8 : decode_any W_48ae8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48aec : bv 32 := 0x04913c23.
Lemma F_48aec : fetch_word AsanUbsan.M.loaded_segments (0x48aec : word) = Some W_48aec.
Proof. vm_refl. Qed.
Lemma D_48aec : decode_any W_48aec = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48af0 : bv 32 := 0x05213823.
Lemma F_48af0 : fetch_word AsanUbsan.M.loaded_segments (0x48af0 : word) = Some W_48af0.
Proof. vm_refl. Qed.
Lemma D_48af0 : decode_any W_48af0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_48af4 : bv 32 := 0x05313423.
Lemma F_48af4 : fetch_word AsanUbsan.M.loaded_segments (0x48af4 : word) = Some W_48af4.
Proof. vm_refl. Qed.
Lemma D_48af4 : decode_any W_48af4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48af8 : bv 32 := 0x05413023.
Lemma F_48af8 : fetch_word AsanUbsan.M.loaded_segments (0x48af8 : word) = Some W_48af8.
Proof. vm_refl. Qed.
Lemma D_48af8 : decode_any W_48af8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48afc : bv 32 := 0x03513c23.
Lemma F_48afc : fetch_word AsanUbsan.M.loaded_segments (0x48afc : word) = Some W_48afc.
Proof. vm_refl. Qed.
Lemma D_48afc : decode_any W_48afc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b00 : bv 32 := 0x03613823.
Lemma F_48b00 : fetch_word AsanUbsan.M.loaded_segments (0x48b00 : word) = Some W_48b00.
Proof. vm_refl. Qed.
Lemma D_48b00 : decode_any W_48b00 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b04 : bv 32 := 0x03713423.
Lemma F_48b04 : fetch_word AsanUbsan.M.loaded_segments (0x48b04 : word) = Some W_48b04.
Proof. vm_refl. Qed.
Lemma D_48b04 : decode_any W_48b04 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b08 : bv 32 := 0x03813023.
Lemma F_48b08 : fetch_word AsanUbsan.M.loaded_segments (0x48b08 : word) = Some W_48b08.
Proof. vm_refl. Qed.
Lemma D_48b08 : decode_any W_48b08 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b0c : bv 32 := 0x01913c23.
Lemma F_48b0c : fetch_word AsanUbsan.M.loaded_segments (0x48b0c : word) = Some W_48b0c.
Proof. vm_refl. Qed.
Lemma D_48b0c : decode_any W_48b0c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b10 : bv 32 := 0x01a13823.
Lemma F_48b10 : fetch_word AsanUbsan.M.loaded_segments (0x48b10 : word) = Some W_48b10.
Proof. vm_refl. Qed.
Lemma D_48b10 : decode_any W_48b10 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b14 : bv 32 := 0x01b13423.
Lemma F_48b14 : fetch_word AsanUbsan.M.loaded_segments (0x48b14 : word) = Some W_48b14.
Proof. vm_refl. Qed.
Lemma D_48b14 : decode_any W_48b14 = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b18 : bv 32 := 0x00060413.
Lemma F_48b18 : fetch_word AsanUbsan.M.loaded_segments (0x48b18 : word) = Some W_48b18.
Proof. vm_refl. Qed.
Lemma D_48b18 : decode_any W_48b18 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b1c : bv 32 := 0x00058493.
Lemma F_48b1c : fetch_word AsanUbsan.M.loaded_segments (0x48b1c : word) = Some W_48b1c.
Proof. vm_refl. Qed.
Lemma D_48b1c : decode_any W_48b1c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b20 : bv 32 := 0x00050a93.
Lemma F_48b20 : fetch_word AsanUbsan.M.loaded_segments (0x48b20 : word) = Some W_48b20.
Proof. vm_refl. Qed.
Lemma D_48b20 : decode_any W_48b20 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b24 : bv 32 := 0x00000993.
Lemma F_48b24 : fetch_word AsanUbsan.M.loaded_segments (0x48b24 : word) = Some W_48b24.
Proof. vm_refl. Qed.
Lemma D_48b24 : decode_any W_48b24 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b28 : bv 32 := 0x00001937.
Lemma F_48b28 : fetch_word AsanUbsan.M.loaded_segments (0x48b28 : word) = Some W_48b28.
Proof. vm_refl. Qed.
Lemma D_48b28 : decode_any W_48b28 = Some (Lui 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b2c : bv 32 := 0x00b00b93.
Lemma F_48b2c : fetch_word AsanUbsan.M.loaded_segments (0x48b2c : word) = Some W_48b2c.
Proof. vm_refl. Qed.
Lemma D_48b2c : decode_any W_48b2c = Some (OpImm ALU_ADD 23 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b30 : bv 32 := 0x01250933.
Lemma F_48b30 : fetch_word AsanUbsan.M.loaded_segments (0x48b30 : word) = Some W_48b30.
Proof. vm_refl. Qed.
Lemma D_48b30 : decode_any W_48b30 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b34 : bv 32 := 0x00100c93.
Lemma F_48b34 : fetch_word AsanUbsan.M.loaded_segments (0x48b34 : word) = Some W_48b34.
Proof. vm_refl. Qed.
Lemma D_48b34 : decode_any W_48b34 = Some (OpImm ALU_ADD 25 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b38 : bv 32 := 0x00c0006f.
Lemma F_48b38 : fetch_word AsanUbsan.M.loaded_segments (0x48b38 : word) = Some W_48b38.
Proof. vm_refl. Qed.
Lemma D_48b38 : decode_any W_48b38 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b3c : bv 32 := 0x00198993.
Lemma F_48b3c : fetch_word AsanUbsan.M.loaded_segments (0x48b3c : word) = Some W_48b3c.
Proof. vm_refl. Qed.
Lemma D_48b3c : decode_any W_48b3c = Some (OpImm ALU_ADD 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b40 : bv 32 := 0x09798663.
Lemma F_48b40 : fetch_word AsanUbsan.M.loaded_segments (0x48b40 : word) = Some W_48b40.
Proof. vm_refl. Qed.
Lemma D_48b40 : decode_any W_48b40 = Some (Branch BC_EQ 19 23 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b44 : bv 32 := 0x00000d13.
Lemma F_48b44 : fetch_word AsanUbsan.M.loaded_segments (0x48b44 : word) = Some W_48b44.
Proof. vm_refl. Qed.
Lemma D_48b44 : decode_any W_48b44 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b48 : bv 32 := 0x058ab503.
Lemma F_48b48 : fetch_word AsanUbsan.M.loaded_segments (0x48b48 : word) = Some W_48b48.
Proof. vm_refl. Qed.
Lemma D_48b48 : decode_any W_48b48 = Some (Load SZ8 true 10 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b4c : bv 32 := 0x00a00593.
Lemma F_48b4c : fetch_word AsanUbsan.M.loaded_segments (0x48b4c : word) = Some W_48b4c.
Proof. vm_refl. Qed.
Lemma D_48b4c : decode_any W_48b4c = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b50 : bv 32 := 0x413585bb.
Lemma F_48b50 : fetch_word AsanUbsan.M.loaded_segments (0x48b50 : word) = Some W_48b50.
Proof. vm_refl. Qed.
Lemma D_48b50 : decode_any W_48b50 = Some (Op32 ALU_SUB 11 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b54 : bv 32 := 0x00698d93.
Lemma F_48b54 : fetch_word AsanUbsan.M.loaded_segments (0x48b54 : word) = Some W_48b54.
Proof. vm_refl. Qed.
Lemma D_48b54 : decode_any W_48b54 = Some (OpImm ALU_ADD 27 19 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b58 : bv 32 := 0xfff00613.
Lemma F_48b58 : fetch_word AsanUbsan.M.loaded_segments (0x48b58 : word) = Some W_48b58.
Proof. vm_refl. Qed.
Lemma D_48b58 : decode_any W_48b58 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b5c : bv 32 := 0x00b615b3.
Lemma F_48b5c : fetch_word AsanUbsan.M.loaded_segments (0x48b5c : word) = Some W_48b5c.
Proof. vm_refl. Qed.
Lemma D_48b5c : decode_any W_48b5c = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b60 : bv 32 := 0x3ff5f593.
Lemma F_48b60 : fetch_word AsanUbsan.M.loaded_segments (0x48b60 : word) = Some W_48b60.
Proof. vm_refl. Qed.
Lemma D_48b60 : decode_any W_48b60 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b64 : bv 32 := 0xff150613.
Lemma F_48b64 : fetch_word AsanUbsan.M.loaded_segments (0x48b64 : word) = Some W_48b64.
Proof. vm_refl. Qed.
Lemma D_48b64 : decode_any W_48b64 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b68 : bv 32 := 0x41350a33.
Lemma F_48b68 : fetch_word AsanUbsan.M.loaded_segments (0x48b68 : word) = Some W_48b68.
Proof. vm_refl. Qed.
Lemma D_48b68 : decode_any W_48b68 = Some (Op ALU_SUB 20 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b6c : bv 32 := 0x00c59c33.
Lemma F_48b6c : fetch_word AsanUbsan.M.loaded_segments (0x48b6c : word) = Some W_48b6c.
Proof. vm_refl. Qed.
Lemma D_48b6c : decode_any W_48b6c = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b70 : bv 32 := 0xffaa0a13.
Lemma F_48b70 : fetch_word AsanUbsan.M.loaded_segments (0x48b70 : word) = Some W_48b70.
Proof. vm_refl. Qed.
Lemma D_48b70 : decode_any W_48b70 = Some (OpImm ALU_ADD 20 20 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b74 : bv 32 := 0x01890c33.
Lemma F_48b74 : fetch_word AsanUbsan.M.loaded_segments (0x48b74 : word) = Some W_48b74.
Proof. vm_refl. Qed.
Lemma D_48b74 : decode_any W_48b74 = Some (Op ALU_ADD 24 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b78 : bv 32 := 0x04000513.
Lemma F_48b78 : fetch_word AsanUbsan.M.loaded_segments (0x48b78 : word) = Some W_48b78.
Proof. vm_refl. Qed.
Lemma D_48b78 : decode_any W_48b78 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b7c : bv 32 := 0x01351b33.
Lemma F_48b7c : fetch_word AsanUbsan.M.loaded_segments (0x48b7c : word) = Some W_48b7c.
Proof. vm_refl. Qed.
Lemma D_48b7c : decode_any W_48b7c = Some (Op ALU_SLL 22 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b80 : bv 32 := 0x0100006f.
Lemma F_48b80 : fetch_word AsanUbsan.M.loaded_segments (0x48b80 : word) = Some W_48b80.
Proof. vm_refl. Qed.
Lemma D_48b80 : decode_any W_48b80 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b84 : bv 32 := 0x001d0d13.
Lemma F_48b84 : fetch_word AsanUbsan.M.loaded_segments (0x48b84 : word) = Some W_48b84.
Proof. vm_refl. Qed.
Lemma D_48b84 : decode_any W_48b84 = Some (OpImm ALU_ADD 26 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b88 : bv 32 := 0x014d5533.
Lemma F_48b88 : fetch_word AsanUbsan.M.loaded_segments (0x48b88 : word) = Some W_48b88.
Proof. vm_refl. Qed.
Lemma D_48b88 : decode_any W_48b88 = Some (Op ALU_SRL 10 26 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b8c : bv 32 := 0xfa0518e3.
Lemma F_48b8c : fetch_word AsanUbsan.M.loaded_segments (0x48b8c : word) = Some W_48b8c.
Proof. vm_refl. Qed.
Lemma D_48b8c : decode_any W_48b8c = Some (Branch BC_NE 10 0 8112, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b90 : bv 32 := 0x01ac0533.
Lemma F_48b90 : fetch_word AsanUbsan.M.loaded_segments (0x48b90 : word) = Some W_48b90.
Proof. vm_refl. Qed.
Lemma D_48b90 : decode_any W_48b90 = Some (Op ALU_ADD 10 24 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b94 : bv 32 := 0x00054503.
Lemma F_48b94 : fetch_word AsanUbsan.M.loaded_segments (0x48b94 : word) = Some W_48b94.
Proof. vm_refl. Qed.
Lemma D_48b94 : decode_any W_48b94 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b98 : bv 32 := 0xfe0506e3.
Lemma F_48b98 : fetch_word AsanUbsan.M.loaded_segments (0x48b98 : word) = Some W_48b98.
Proof. vm_refl. Qed.
Lemma D_48b98 : decode_any W_48b98 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_48b9c : bv 32 := 0x058ab503.
Lemma F_48b9c : fetch_word AsanUbsan.M.loaded_segments (0x48b9c : word) = Some W_48b9c.
Proof. vm_refl. Qed.
Lemma D_48b9c : decode_any W_48b9c = Some (Load SZ8 true 10 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ba0 : bv 32 := 0xffb50593.
Lemma F_48ba0 : fetch_word AsanUbsan.M.loaded_segments (0x48ba0 : word) = Some W_48ba0.
Proof. vm_refl. Qed.
Lemma D_48ba0 : decode_any W_48ba0 = Some (OpImm ALU_ADD 11 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ba4 : bv 32 := 0x00a99533.
Lemma F_48ba4 : fetch_word AsanUbsan.M.loaded_segments (0x48ba4 : word) = Some W_48ba4.
Proof. vm_refl. Qed.
Lemma D_48ba4 : decode_any W_48ba4 = Some (Op ALU_SLL 10 19 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ba8 : bv 32 := 0x00bc95b3.
Lemma F_48ba8 : fetch_word AsanUbsan.M.loaded_segments (0x48ba8 : word) = Some W_48ba8.
Proof. vm_refl. Qed.
Lemma D_48ba8 : decode_any W_48ba8 = Some (Op ALU_SLL 11 25 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bac : bv 32 := 0x00a90533.
Lemma F_48bac : fetch_word AsanUbsan.M.loaded_segments (0x48bac : word) = Some W_48bac.
Proof. vm_refl. Qed.
Lemma D_48bac : decode_any W_48bac = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bb0 : bv 32 := 0x00b50533.
Lemma F_48bb0 : fetch_word AsanUbsan.M.loaded_segments (0x48bb0 : word) = Some W_48bb0.
Proof. vm_refl. Qed.
Lemma D_48bb0 : decode_any W_48bb0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bb4 : bv 32 := 0x01bd15b3.
Lemma F_48bb4 : fetch_word AsanUbsan.M.loaded_segments (0x48bb4 : word) = Some W_48bb4.
Proof. vm_refl. Qed.
Lemma D_48bb4 : decode_any W_48bb4 = Some (Op ALU_SLL 11 26 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bb8 : bv 32 := 0x00b50533.
Lemma F_48bb8 : fetch_word AsanUbsan.M.loaded_segments (0x48bb8 : word) = Some W_48bb8.
Proof. vm_refl. Qed.
Lemma D_48bb8 : decode_any W_48bb8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bbc : bv 32 := 0x00ab05b3.
Lemma F_48bbc : fetch_word AsanUbsan.M.loaded_segments (0x48bbc : word) = Some W_48bbc.
Proof. vm_refl. Qed.
Lemma D_48bbc : decode_any W_48bbc = Some (Op ALU_ADD 11 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bc0 : bv 32 := 0x00040613.
Lemma F_48bc0 : fetch_word AsanUbsan.M.loaded_segments (0x48bc0 : word) = Some W_48bc0.
Proof. vm_refl. Qed.
Lemma D_48bc0 : decode_any W_48bc0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bc4 : bv 32 := 0x000480e7.
Lemma F_48bc4 : fetch_word AsanUbsan.M.loaded_segments (0x48bc4 : word) = Some W_48bc4.
Proof. vm_refl. Qed.
Lemma D_48bc4 : decode_any W_48bc4 = Some (Jalr 1 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bc8 : bv 32 := 0xfbdff06f.
Lemma F_48bc8 : fetch_word AsanUbsan.M.loaded_segments (0x48bc8 : word) = Some W_48bc8.
Proof. vm_refl. Qed.
Lemma D_48bc8 : decode_any W_48bc8 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bcc : bv 32 := 0x06813083.
Lemma F_48bcc : fetch_word AsanUbsan.M.loaded_segments (0x48bcc : word) = Some W_48bcc.
Proof. vm_refl. Qed.
Lemma D_48bcc : decode_any W_48bcc = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bd0 : bv 32 := 0x06013403.
Lemma F_48bd0 : fetch_word AsanUbsan.M.loaded_segments (0x48bd0 : word) = Some W_48bd0.
Proof. vm_refl. Qed.
Lemma D_48bd0 : decode_any W_48bd0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bd4 : bv 32 := 0x05813483.
Lemma F_48bd4 : fetch_word AsanUbsan.M.loaded_segments (0x48bd4 : word) = Some W_48bd4.
Proof. vm_refl. Qed.
Lemma D_48bd4 : decode_any W_48bd4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bd8 : bv 32 := 0x05013903.
Lemma F_48bd8 : fetch_word AsanUbsan.M.loaded_segments (0x48bd8 : word) = Some W_48bd8.
Proof. vm_refl. Qed.
Lemma D_48bd8 : decode_any W_48bd8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bdc : bv 32 := 0x04813983.
Lemma F_48bdc : fetch_word AsanUbsan.M.loaded_segments (0x48bdc : word) = Some W_48bdc.
Proof. vm_refl. Qed.
Lemma D_48bdc : decode_any W_48bdc = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48be0 : bv 32 := 0x04013a03.
Lemma F_48be0 : fetch_word AsanUbsan.M.loaded_segments (0x48be0 : word) = Some W_48be0.
Proof. vm_refl. Qed.
Lemma D_48be0 : decode_any W_48be0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48be4 : bv 32 := 0x03813a83.
Lemma F_48be4 : fetch_word AsanUbsan.M.loaded_segments (0x48be4 : word) = Some W_48be4.
Proof. vm_refl. Qed.
Lemma D_48be4 : decode_any W_48be4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_48be8 : bv 32 := 0x03013b03.
Lemma F_48be8 : fetch_word AsanUbsan.M.loaded_segments (0x48be8 : word) = Some W_48be8.
Proof. vm_refl. Qed.
Lemma D_48be8 : decode_any W_48be8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bec : bv 32 := 0x02813b83.
Lemma F_48bec : fetch_word AsanUbsan.M.loaded_segments (0x48bec : word) = Some W_48bec.
Proof. vm_refl. Qed.
Lemma D_48bec : decode_any W_48bec = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bf0 : bv 32 := 0x02013c03.
Lemma F_48bf0 : fetch_word AsanUbsan.M.loaded_segments (0x48bf0 : word) = Some W_48bf0.
Proof. vm_refl. Qed.
Lemma D_48bf0 : decode_any W_48bf0 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bf4 : bv 32 := 0x01813c83.
Lemma F_48bf4 : fetch_word AsanUbsan.M.loaded_segments (0x48bf4 : word) = Some W_48bf4.
Proof. vm_refl. Qed.
Lemma D_48bf4 : decode_any W_48bf4 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bf8 : bv 32 := 0x01013d03.
Lemma F_48bf8 : fetch_word AsanUbsan.M.loaded_segments (0x48bf8 : word) = Some W_48bf8.
Proof. vm_refl. Qed.
Lemma D_48bf8 : decode_any W_48bf8 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48bfc : bv 32 := 0x00813d83.
Lemma F_48bfc : fetch_word AsanUbsan.M.loaded_segments (0x48bfc : word) = Some W_48bfc.
Proof. vm_refl. Qed.
Lemma D_48bfc : decode_any W_48bfc = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c00 : bv 32 := 0x07010113.
Lemma F_48c00 : fetch_word AsanUbsan.M.loaded_segments (0x48c00 : word) = Some W_48c00.
Proof. vm_refl. Qed.
Lemma D_48c00 : decode_any W_48c00 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c04 : bv 32 := 0x00008067.
Lemma F_48c04 : fetch_word AsanUbsan.M.loaded_segments (0x48c04 : word) = Some W_48c04.
Proof. vm_refl. Qed.
Lemma D_48c04 : decode_any W_48c04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c08 : bv 32 := 0xff010113.
Lemma F_48c08 : fetch_word AsanUbsan.M.loaded_segments (0x48c08 : word) = Some W_48c08.
Proof. vm_refl. Qed.
Lemma D_48c08 : decode_any W_48c08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c0c : bv 32 := 0x00113423.
Lemma F_48c0c : fetch_word AsanUbsan.M.loaded_segments (0x48c0c : word) = Some W_48c0c.
Proof. vm_refl. Qed.
Lemma D_48c0c : decode_any W_48c0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c10 : bv 32 := 0x00813023.
Lemma F_48c10 : fetch_word AsanUbsan.M.loaded_segments (0x48c10 : word) = Some W_48c10.
Proof. vm_refl. Qed.
Lemma D_48c10 : decode_any W_48c10 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c14 : bv 32 := 0x00050413.
Lemma F_48c14 : fetch_word AsanUbsan.M.loaded_segments (0x48c14 : word) = Some W_48c14.
Proof. vm_refl. Qed.
Lemma D_48c14 : decode_any W_48c14 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c18 : bv 32 := 0x0008e517.
Lemma F_48c18 : fetch_word AsanUbsan.M.loaded_segments (0x48c18 : word) = Some W_48c18.
Proof. vm_refl. Qed.
Lemma D_48c18 : decode_any W_48c18 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c1c : bv 32 := 0x66850513.
Lemma F_48c1c : fetch_word AsanUbsan.M.loaded_segments (0x48c1c : word) = Some W_48c1c.
Proof. vm_refl. Qed.
Lemma D_48c1c : decode_any W_48c1c = Some (OpImm ALU_ADD 10 10 1640, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c20 : bv 32 := 0x270050ef.
Lemma F_48c20 : fetch_word AsanUbsan.M.loaded_segments (0x48c20 : word) = Some W_48c20.
Proof. vm_refl. Qed.
Lemma D_48c20 : decode_any W_48c20 = Some (Jal 1 21104, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c24 : bv 32 := 0x00853023.
Lemma F_48c24 : fetch_word AsanUbsan.M.loaded_segments (0x48c24 : word) = Some W_48c24.
Proof. vm_refl. Qed.
Lemma D_48c24 : decode_any W_48c24 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c28 : bv 32 := 0x00813083.
Lemma F_48c28 : fetch_word AsanUbsan.M.loaded_segments (0x48c28 : word) = Some W_48c28.
Proof. vm_refl. Qed.
Lemma D_48c28 : decode_any W_48c28 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c2c : bv 32 := 0x00013403.
Lemma F_48c2c : fetch_word AsanUbsan.M.loaded_segments (0x48c2c : word) = Some W_48c2c.
Proof. vm_refl. Qed.
Lemma D_48c2c : decode_any W_48c2c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c30 : bv 32 := 0x01010113.
Lemma F_48c30 : fetch_word AsanUbsan.M.loaded_segments (0x48c30 : word) = Some W_48c30.
Proof. vm_refl. Qed.
Lemma D_48c30 : decode_any W_48c30 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c34 : bv 32 := 0x00008067.
Lemma F_48c34 : fetch_word AsanUbsan.M.loaded_segments (0x48c34 : word) = Some W_48c34.
Proof. vm_refl. Qed.
Lemma D_48c34 : decode_any W_48c34 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c38 : bv 32 := 0xfe010113.
Lemma F_48c38 : fetch_word AsanUbsan.M.loaded_segments (0x48c38 : word) = Some W_48c38.
Proof. vm_refl. Qed.
Lemma D_48c38 : decode_any W_48c38 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c3c : bv 32 := 0x00113c23.
Lemma F_48c3c : fetch_word AsanUbsan.M.loaded_segments (0x48c3c : word) = Some W_48c3c.
Proof. vm_refl. Qed.
Lemma D_48c3c : decode_any W_48c3c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c40 : bv 32 := 0x00813823.
Lemma F_48c40 : fetch_word AsanUbsan.M.loaded_segments (0x48c40 : word) = Some W_48c40.
Proof. vm_refl. Qed.
Lemma D_48c40 : decode_any W_48c40 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c44 : bv 32 := 0x00913423.
Lemma F_48c44 : fetch_word AsanUbsan.M.loaded_segments (0x48c44 : word) = Some W_48c44.
Proof. vm_refl. Qed.
Lemma D_48c44 : decode_any W_48c44 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c48 : bv 32 := 0x01213023.
Lemma F_48c48 : fetch_word AsanUbsan.M.loaded_segments (0x48c48 : word) = Some W_48c48.
Proof. vm_refl. Qed.
Lemma D_48c48 : decode_any W_48c48 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c4c : bv 32 := 0x02010413.
Lemma F_48c4c : fetch_word AsanUbsan.M.loaded_segments (0x48c4c : word) = Some W_48c4c.
Proof. vm_refl. Qed.
Lemma D_48c4c : decode_any W_48c4c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c50 : bv 32 := 0x0008e517.
Lemma F_48c50 : fetch_word AsanUbsan.M.loaded_segments (0x48c50 : word) = Some W_48c50.
Proof. vm_refl. Qed.
Lemma D_48c50 : decode_any W_48c50 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c54 : bv 32 := 0x63050513.
Lemma F_48c54 : fetch_word AsanUbsan.M.loaded_segments (0x48c54 : word) = Some W_48c54.
Proof. vm_refl. Qed.
Lemma D_48c54 : decode_any W_48c54 = Some (OpImm ALU_ADD 10 10 1584, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c58 : bv 32 := 0x238050ef.
Lemma F_48c58 : fetch_word AsanUbsan.M.loaded_segments (0x48c58 : word) = Some W_48c58.
Proof. vm_refl. Qed.
Lemma D_48c58 : decode_any W_48c58 = Some (Jal 1 21048, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c5c : bv 32 := 0x00053483.
Lemma F_48c5c : fetch_word AsanUbsan.M.loaded_segments (0x48c5c : word) = Some W_48c5c.
Proof. vm_refl. Qed.
Lemma D_48c5c : decode_any W_48c5c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c60 : bv 32 := 0x08048863.
Lemma F_48c60 : fetch_word AsanUbsan.M.loaded_segments (0x48c60 : word) = Some W_48c60.
Proof. vm_refl. Qed.
Lemma D_48c60 : decode_any W_48c60 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c64 : bv 32 := 0x0604c503.
Lemma F_48c64 : fetch_word AsanUbsan.M.loaded_segments (0x48c64 : word) = Some W_48c64.
Proof. vm_refl. Qed.
Lemma D_48c64 : decode_any W_48c64 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c68 : bv 32 := 0x0584b903.
Lemma F_48c68 : fetch_word AsanUbsan.M.loaded_segments (0x48c68 : word) = Some W_48c68.
Proof. vm_refl. Qed.
Lemma D_48c68 : decode_any W_48c68 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c6c : bv 32 := 0x00050863.
Lemma F_48c6c : fetch_word AsanUbsan.M.loaded_segments (0x48c6c : word) = Some W_48c6c.
Proof. vm_refl. Qed.
Lemma D_48c6c : decode_any W_48c6c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c70 : bv 32 := 0x00048513.
Lemma F_48c70 : fetch_word AsanUbsan.M.loaded_segments (0x48c70 : word) = Some W_48c70.
Proof. vm_refl. Qed.
Lemma D_48c70 : decode_any W_48c70 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c74 : bv 32 := 0x00040593.
Lemma F_48c74 : fetch_word AsanUbsan.M.loaded_segments (0x48c74 : word) = Some W_48c74.
Proof. vm_refl. Qed.
Lemma D_48c74 : decode_any W_48c74 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c78 : bv 32 := 0xb75ff0ef.
Lemma F_48c78 : fetch_word AsanUbsan.M.loaded_segments (0x48c78 : word) = Some W_48c78.
Proof. vm_refl. Qed.
Lemma D_48c78 : decode_any W_48c78 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c7c : bv 32 := 0xff990593.
Lemma F_48c7c : fetch_word AsanUbsan.M.loaded_segments (0x48c7c : word) = Some W_48c7c.
Proof. vm_refl. Qed.
Lemma D_48c7c : decode_any W_48c7c = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c80 : bv 32 := 0x00100513.
Lemma F_48c80 : fetch_word AsanUbsan.M.loaded_segments (0x48c80 : word) = Some W_48c80.
Proof. vm_refl. Qed.
Lemma D_48c80 : decode_any W_48c80 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c84 : bv 32 := 0x00b51533.
Lemma F_48c84 : fetch_word AsanUbsan.M.loaded_segments (0x48c84 : word) = Some W_48c84.
Proof. vm_refl. Qed.
Lemma D_48c84 : decode_any W_48c84 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c88 : bv 32 := 0x0005061b.
Lemma F_48c88 : fetch_word AsanUbsan.M.loaded_segments (0x48c88 : word) = Some W_48c88.
Proof. vm_refl. Qed.
Lemma D_48c88 : decode_any W_48c88 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c8c : bv 32 := 0x08c05263.
Lemma F_48c8c : fetch_word AsanUbsan.M.loaded_segments (0x48c8c : word) = Some W_48c8c.
Proof. vm_refl. Qed.
Lemma D_48c8c : decode_any W_48c8c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c90 : bv 32 := 0x000016b7.
Lemma F_48c90 : fetch_word AsanUbsan.M.loaded_segments (0x48c90 : word) = Some W_48c90.
Proof. vm_refl. Qed.
Lemma D_48c90 : decode_any W_48c90 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c94 : bv 32 := 0xff190613.
Lemma F_48c94 : fetch_word AsanUbsan.M.loaded_segments (0x48c94 : word) = Some W_48c94.
Proof. vm_refl. Qed.
Lemma D_48c94 : decode_any W_48c94 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c98 : bv 32 := 0x20000713.
Lemma F_48c98 : fetch_word AsanUbsan.M.loaded_segments (0x48c98 : word) = Some W_48c98.
Proof. vm_refl. Qed.
Lemma D_48c98 : decode_any W_48c98 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_48c9c : bv 32 := 0xfff00793.
Lemma F_48c9c : fetch_word AsanUbsan.M.loaded_segments (0x48c9c : word) = Some W_48c9c.
Proof. vm_refl. Qed.
Lemma D_48c9c : decode_any W_48c9c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ca0 : bv 32 := 0x00c71733.
Lemma F_48ca0 : fetch_word AsanUbsan.M.loaded_segments (0x48ca0 : word) = Some W_48ca0.
Proof. vm_refl. Qed.
Lemma D_48ca0 : decode_any W_48ca0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ca4 : bv 32 := 0x0084b603.
Lemma F_48ca4 : fetch_word AsanUbsan.M.loaded_segments (0x48ca4 : word) = Some W_48ca4.
Proof. vm_refl. Qed.
Lemma D_48ca4 : decode_any W_48ca4 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ca8 : bv 32 := 0x00b797b3.
Lemma F_48ca8 : fetch_word AsanUbsan.M.loaded_segments (0x48ca8 : word) = Some W_48ca8.
Proof. vm_refl. Qed.
Lemma D_48ca8 : decode_any W_48ca8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cac : bv 32 := 0xfff50813.
Lemma F_48cac : fetch_word AsanUbsan.M.loaded_segments (0x48cac : word) = Some W_48cac.
Proof. vm_refl. Qed.
Lemma D_48cac : decode_any W_48cac = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cb0 : bv 32 := 0x00d485b3.
Lemma F_48cb0 : fetch_word AsanUbsan.M.loaded_segments (0x48cb0 : word) = Some W_48cb0.
Proof. vm_refl. Qed.
Lemma D_48cb0 : decode_any W_48cb0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cb4 : bv 32 := 0x00e586b3.
Lemma F_48cb4 : fetch_word AsanUbsan.M.loaded_segments (0x48cb4 : word) = Some W_48cb4.
Proof. vm_refl. Qed.
Lemma D_48cb4 : decode_any W_48cb4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cb8 : bv 32 := 0xfff7c713.
Lemma F_48cb8 : fetch_word AsanUbsan.M.loaded_segments (0x48cb8 : word) = Some W_48cb8.
Proof. vm_refl. Qed.
Lemma D_48cb8 : decode_any W_48cb8 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cbc : bv 32 := 0x02081813.
Lemma F_48cbc : fetch_word AsanUbsan.M.loaded_segments (0x48cbc : word) = Some W_48cbc.
Proof. vm_refl. Qed.
Lemma D_48cbc : decode_any W_48cbc = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cc0 : bv 32 := 0x02085793.
Lemma F_48cc0 : fetch_word AsanUbsan.M.loaded_segments (0x48cc0 : word) = Some W_48cc0.
Proof. vm_refl. Qed.
Lemma D_48cc0 : decode_any W_48cc0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cc4 : bv 32 := 0x00f607b3.
Lemma F_48cc4 : fetch_word AsanUbsan.M.loaded_segments (0x48cc4 : word) = Some W_48cc4.
Proof. vm_refl. Qed.
Lemma D_48cc4 : decode_any W_48cc4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cc8 : bv 32 := 0x00178813.
Lemma F_48cc8 : fetch_word AsanUbsan.M.loaded_segments (0x48cc8 : word) = Some W_48cc8.
Proof. vm_refl. Qed.
Lemma D_48cc8 : decode_any W_48cc8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ccc : bv 32 := 0x00e678b3.
Lemma F_48ccc : fetch_word AsanUbsan.M.loaded_segments (0x48ccc : word) = Some W_48ccc.
Proof. vm_refl. Qed.
Lemma D_48ccc : decode_any W_48ccc = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cd0 : bv 32 := 0x011687b3.
Lemma F_48cd0 : fetch_word AsanUbsan.M.loaded_segments (0x48cd0 : word) = Some W_48cd0.
Proof. vm_refl. Qed.
Lemma D_48cd0 : decode_any W_48cd0 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cd4 : bv 32 := 0x0007c283.
Lemma F_48cd4 : fetch_word AsanUbsan.M.loaded_segments (0x48cd4 : word) = Some W_48cd4.
Proof. vm_refl. Qed.
Lemma D_48cd4 : decode_any W_48cd4 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cd8 : bv 32 := 0x06028663.
Lemma F_48cd8 : fetch_word AsanUbsan.M.loaded_segments (0x48cd8 : word) = Some W_48cd8.
Proof. vm_refl. Qed.
Lemma D_48cd8 : decode_any W_48cd8 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cdc : bv 32 := 0xfff5051b.
Lemma F_48cdc : fetch_word AsanUbsan.M.loaded_segments (0x48cdc : word) = Some W_48cdc.
Proof. vm_refl. Qed.
Lemma D_48cdc : decode_any W_48cdc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ce0 : bv 32 := 0x00160613.
Lemma F_48ce0 : fetch_word AsanUbsan.M.loaded_segments (0x48ce0 : word) = Some W_48ce0.
Proof. vm_refl. Qed.
Lemma D_48ce0 : decode_any W_48ce0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ce4 : bv 32 := 0xfe0514e3.
Lemma F_48ce4 : fetch_word AsanUbsan.M.loaded_segments (0x48ce4 : word) = Some W_48ce4.
Proof. vm_refl. Qed.
Lemma D_48ce4 : decode_any W_48ce4 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ce8 : bv 32 := 0x0104b423.
Lemma F_48ce8 : fetch_word AsanUbsan.M.loaded_segments (0x48ce8 : word) = Some W_48ce8.
Proof. vm_refl. Qed.
Lemma D_48ce8 : decode_any W_48ce8 = Some (Store SZ8 9 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cec : bv 32 := 0x0400006f.
Lemma F_48cec : fetch_word AsanUbsan.M.loaded_segments (0x48cec : word) = Some W_48cec.
Proof. vm_refl. Qed.
Lemma D_48cec : decode_any W_48cec = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cf0 : bv 32 := 0x0008e517.
Lemma F_48cf0 : fetch_word AsanUbsan.M.loaded_segments (0x48cf0 : word) = Some W_48cf0.
Proof. vm_refl. Qed.
Lemma D_48cf0 : decode_any W_48cf0 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cf4 : bv 32 := 0x83053503.
Lemma F_48cf4 : fetch_word AsanUbsan.M.loaded_segments (0x48cf4 : word) = Some W_48cf4.
Proof. vm_refl. Qed.
Lemma D_48cf4 : decode_any W_48cf4 = Some (Load SZ8 true 10 10 2096, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cf8 : bv 32 := 0x00052503.
Lemma F_48cf8 : fetch_word AsanUbsan.M.loaded_segments (0x48cf8 : word) = Some W_48cf8.
Proof. vm_refl. Qed.
Lemma D_48cf8 : decode_any W_48cf8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48cfc : bv 32 := 0x02050863.
Lemma F_48cfc : fetch_word AsanUbsan.M.loaded_segments (0x48cfc : word) = Some W_48cfc.
Proof. vm_refl. Qed.
Lemma D_48cfc : decode_any W_48cfc = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d00 : bv 32 := 0x565200ef.
Lemma F_48d00 : fetch_word AsanUbsan.M.loaded_segments (0x48d00 : word) = Some W_48d00.
Proof. vm_refl. Qed.
Lemma D_48d00 : decode_any W_48d00 = Some (Jal 1 134500, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d04 : bv 32 := 0x02050463.
Lemma F_48d04 : fetch_word AsanUbsan.M.loaded_segments (0x48d04 : word) = Some W_48d04.
Proof. vm_refl. Qed.
Lemma D_48d04 : decode_any W_48d04 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d08 : bv 32 := 0x02850583.
Lemma F_48d08 : fetch_word AsanUbsan.M.loaded_segments (0x48d08 : word) = Some W_48d08.
Proof. vm_refl. Qed.
Lemma D_48d08 : decode_any W_48d08 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d0c : bv 32 := 0x0a058063.
Lemma F_48d0c : fetch_word AsanUbsan.M.loaded_segments (0x48d0c : word) = Some W_48d0c.
Proof. vm_refl. Qed.
Lemma D_48d0c : decode_any W_48d0c = Some (Branch BC_EQ 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d10 : bv 32 := 0x00000513.
Lemma F_48d10 : fetch_word AsanUbsan.M.loaded_segments (0x48d10 : word) = Some W_48d10.
Proof. vm_refl. Qed.
Lemma D_48d10 : decode_any W_48d10 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d14 : bv 32 := 0x01813083.
Lemma F_48d14 : fetch_word AsanUbsan.M.loaded_segments (0x48d14 : word) = Some W_48d14.
Proof. vm_refl. Qed.
Lemma D_48d14 : decode_any W_48d14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d18 : bv 32 := 0x01013403.
Lemma F_48d18 : fetch_word AsanUbsan.M.loaded_segments (0x48d18 : word) = Some W_48d18.
Proof. vm_refl. Qed.
Lemma D_48d18 : decode_any W_48d18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d1c : bv 32 := 0x00813483.
Lemma F_48d1c : fetch_word AsanUbsan.M.loaded_segments (0x48d1c : word) = Some W_48d1c.
Proof. vm_refl. Qed.
Lemma D_48d1c : decode_any W_48d1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d20 : bv 32 := 0x00013903.
Lemma F_48d20 : fetch_word AsanUbsan.M.loaded_segments (0x48d20 : word) = Some W_48d20.
Proof. vm_refl. Qed.
Lemma D_48d20 : decode_any W_48d20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d24 : bv 32 := 0x02010113.
Lemma F_48d24 : fetch_word AsanUbsan.M.loaded_segments (0x48d24 : word) = Some W_48d24.
Proof. vm_refl. Qed.
Lemma D_48d24 : decode_any W_48d24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d28 : bv 32 := 0x00008067.
Lemma F_48d28 : fetch_word AsanUbsan.M.loaded_segments (0x48d28 : word) = Some W_48d28.
Proof. vm_refl. Qed.
Lemma D_48d28 : decode_any W_48d28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d2c : bv 32 := 0x01813083.
Lemma F_48d2c : fetch_word AsanUbsan.M.loaded_segments (0x48d2c : word) = Some W_48d2c.
Proof. vm_refl. Qed.
Lemma D_48d2c : decode_any W_48d2c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d30 : bv 32 := 0x01013403.
Lemma F_48d30 : fetch_word AsanUbsan.M.loaded_segments (0x48d30 : word) = Some W_48d30.
Proof. vm_refl. Qed.
Lemma D_48d30 : decode_any W_48d30 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d34 : bv 32 := 0x00813483.
Lemma F_48d34 : fetch_word AsanUbsan.M.loaded_segments (0x48d34 : word) = Some W_48d34.
Proof. vm_refl. Qed.
Lemma D_48d34 : decode_any W_48d34 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d38 : bv 32 := 0x00013903.
Lemma F_48d38 : fetch_word AsanUbsan.M.loaded_segments (0x48d38 : word) = Some W_48d38.
Proof. vm_refl. Qed.
Lemma D_48d38 : decode_any W_48d38 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d3c : bv 32 := 0x02010113.
Lemma F_48d3c : fetch_word AsanUbsan.M.loaded_segments (0x48d3c : word) = Some W_48d3c.
Proof. vm_refl. Qed.
Lemma D_48d3c : decode_any W_48d3c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d40 : bv 32 := 0x00008067.
Lemma F_48d40 : fetch_word AsanUbsan.M.loaded_segments (0x48d40 : word) = Some W_48d40.
Proof. vm_refl. Qed.
Lemma D_48d40 : decode_any W_48d40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d44 : bv 32 := 0x00160613.
Lemma F_48d44 : fetch_word AsanUbsan.M.loaded_segments (0x48d44 : word) = Some W_48d44.
Proof. vm_refl. Qed.
Lemma D_48d44 : decode_any W_48d44 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d48 : bv 32 := 0x00100513.
Lemma F_48d48 : fetch_word AsanUbsan.M.loaded_segments (0x48d48 : word) = Some W_48d48.
Proof. vm_refl. Qed.
Lemma D_48d48 : decode_any W_48d48 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d4c : bv 32 := 0xffb90693.
Lemma F_48d4c : fetch_word AsanUbsan.M.loaded_segments (0x48d4c : word) = Some W_48d4c.
Proof. vm_refl. Qed.
Lemma D_48d4c : decode_any W_48d4c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d50 : bv 32 := 0x00789893.
Lemma F_48d50 : fetch_word AsanUbsan.M.loaded_segments (0x48d50 : word) = Some W_48d50.
Proof. vm_refl. Qed.
Lemma D_48d50 : decode_any W_48d50 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d54 : bv 32 := 0x00c4b423.
Lemma F_48d54 : fetch_word AsanUbsan.M.loaded_segments (0x48d54 : word) = Some W_48d54.
Proof. vm_refl. Qed.
Lemma D_48d54 : decode_any W_48d54 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d58 : bv 32 := 0x00a78023.
Lemma F_48d58 : fetch_word AsanUbsan.M.loaded_segments (0x48d58 : word) = Some W_48d58.
Proof. vm_refl. Qed.
Lemma D_48d58 : decode_any W_48d58 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d5c : bv 32 := 0x00d51633.
Lemma F_48d5c : fetch_word AsanUbsan.M.loaded_segments (0x48d5c : word) = Some W_48d5c.
Proof. vm_refl. Qed.
Lemma D_48d5c : decode_any W_48d5c = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d60 : bv 32 := 0x01251533.
Lemma F_48d60 : fetch_word AsanUbsan.M.loaded_segments (0x48d60 : word) = Some W_48d60.
Proof. vm_refl. Qed.
Lemma D_48d60 : decode_any W_48d60 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d64 : bv 32 := 0x00c585b3.
Lemma F_48d64 : fetch_word AsanUbsan.M.loaded_segments (0x48d64 : word) = Some W_48d64.
Proof. vm_refl. Qed.
Lemma D_48d64 : decode_any W_48d64 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d68 : bv 32 := 0x01150533.
Lemma F_48d68 : fetch_word AsanUbsan.M.loaded_segments (0x48d68 : word) = Some W_48d68.
Proof. vm_refl. Qed.
Lemma D_48d68 : decode_any W_48d68 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d6c : bv 32 := 0x00a584b3.
Lemma F_48d6c : fetch_word AsanUbsan.M.loaded_segments (0x48d6c : word) = Some W_48d6c.
Proof. vm_refl. Qed.
Lemma D_48d6c : decode_any W_48d6c = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d70 : bv 32 := 0x0084bc23.
Lemma F_48d70 : fetch_word AsanUbsan.M.loaded_segments (0x48d70 : word) = Some W_48d70.
Proof. vm_refl. Qed.
Lemma D_48d70 : decode_any W_48d70 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d74 : bv 32 := 0x06f4bc23.
Lemma F_48d74 : fetch_word AsanUbsan.M.loaded_segments (0x48d74 : word) = Some W_48d74.
Proof. vm_refl. Qed.
Lemma D_48d74 : decode_any W_48d74 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d78 : bv 32 := 0x00048513.
Lemma F_48d78 : fetch_word AsanUbsan.M.loaded_segments (0x48d78 : word) = Some W_48d78.
Proof. vm_refl. Qed.
Lemma D_48d78 : decode_any W_48d78 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d7c : bv 32 := 0x394000ef.
Lemma F_48d7c : fetch_word AsanUbsan.M.loaded_segments (0x48d7c : word) = Some W_48d7c.
Proof. vm_refl. Qed.
Lemma D_48d7c : decode_any W_48d7c = Some (Jal 1 916, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d80 : bv 32 := 0x00050593.
Lemma F_48d80 : fetch_word AsanUbsan.M.loaded_segments (0x48d80 : word) = Some W_48d80.
Proof. vm_refl. Qed.
Lemma D_48d80 : decode_any W_48d80 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d84 : bv 32 := 0x00048513.
Lemma F_48d84 : fetch_word AsanUbsan.M.loaded_segments (0x48d84 : word) = Some W_48d84.
Proof. vm_refl. Qed.
Lemma D_48d84 : decode_any W_48d84 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d88 : bv 32 := 0x00000613.
Lemma F_48d88 : fetch_word AsanUbsan.M.loaded_segments (0x48d88 : word) = Some W_48d88.
Proof. vm_refl. Qed.
Lemma D_48d88 : decode_any W_48d88 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d8c : bv 32 := 0x0005b023.
Lemma F_48d8c : fetch_word AsanUbsan.M.loaded_segments (0x48d8c : word) = Some W_48d8c.
Proof. vm_refl. Qed.
Lemma D_48d8c : decode_any W_48d8c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d90 : bv 32 := 0x0005b423.
Lemma F_48d90 : fetch_word AsanUbsan.M.loaded_segments (0x48d90 : word) = Some W_48d90.
Proof. vm_refl. Qed.
Lemma D_48d90 : decode_any W_48d90 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d94 : bv 32 := 0x01813083.
Lemma F_48d94 : fetch_word AsanUbsan.M.loaded_segments (0x48d94 : word) = Some W_48d94.
Proof. vm_refl. Qed.
Lemma D_48d94 : decode_any W_48d94 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d98 : bv 32 := 0x01013403.
Lemma F_48d98 : fetch_word AsanUbsan.M.loaded_segments (0x48d98 : word) = Some W_48d98.
Proof. vm_refl. Qed.
Lemma D_48d98 : decode_any W_48d98 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48d9c : bv 32 := 0x00813483.
Lemma F_48d9c : fetch_word AsanUbsan.M.loaded_segments (0x48d9c : word) = Some W_48d9c.
Proof. vm_refl. Qed.
Lemma D_48d9c : decode_any W_48d9c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48da0 : bv 32 := 0x00013903.
Lemma F_48da0 : fetch_word AsanUbsan.M.loaded_segments (0x48da0 : word) = Some W_48da0.
Proof. vm_refl. Qed.
Lemma D_48da0 : decode_any W_48da0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48da4 : bv 32 := 0x02010113.
Lemma F_48da4 : fetch_word AsanUbsan.M.loaded_segments (0x48da4 : word) = Some W_48da4.
Proof. vm_refl. Qed.
Lemma D_48da4 : decode_any W_48da4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48da8 : bv 32 := 0x00008067.
Lemma F_48da8 : fetch_word AsanUbsan.M.loaded_segments (0x48da8 : word) = Some W_48da8.
Proof. vm_refl. Qed.
Lemma D_48da8 : decode_any W_48da8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dac : bv 32 := 0x04853483.
Lemma F_48dac : fetch_word AsanUbsan.M.loaded_segments (0x48dac : word) = Some W_48dac.
Proof. vm_refl. Qed.
Lemma D_48dac : decode_any W_48dac = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48db0 : bv 32 := 0x00100593.
Lemma F_48db0 : fetch_word AsanUbsan.M.loaded_segments (0x48db0 : word) = Some W_48db0.
Proof. vm_refl. Qed.
Lemma D_48db0 : decode_any W_48db0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48db4 : bv 32 := 0x0095e663.
Lemma F_48db4 : fetch_word AsanUbsan.M.loaded_segments (0x48db4 : word) = Some W_48db4.
Proof. vm_refl. Qed.
Lemma D_48db4 : decode_any W_48db4 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48db8 : bv 32 := 0x721200ef.
Lemma F_48db8 : fetch_word AsanUbsan.M.loaded_segments (0x48db8 : word) = Some W_48db8.
Proof. vm_refl. Qed.
Lemma D_48db8 : decode_any W_48db8 = Some (Jal 1 134944, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dbc : bv 32 := 0x00050493.
Lemma F_48dbc : fetch_word AsanUbsan.M.loaded_segments (0x48dbc : word) = Some W_48dbc.
Proof. vm_refl. Qed.
Lemma D_48dbc : decode_any W_48dbc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dc0 : bv 32 := 0xea0492e3.
Lemma F_48dc0 : fetch_word AsanUbsan.M.loaded_segments (0x48dc0 : word) = Some W_48dc0.
Proof. vm_refl. Qed.
Lemma D_48dc0 : decode_any W_48dc0 = Some (Branch BC_NE 9 0 7844, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dc4 : bv 32 := 0xf4dff06f.
Lemma F_48dc4 : fetch_word AsanUbsan.M.loaded_segments (0x48dc4 : word) = Some W_48dc4.
Proof. vm_refl. Qed.
Lemma D_48dc4 : decode_any W_48dc4 = Some (Jal 0 2096972, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dc8 : bv 32 := 0xfe010113.
Lemma F_48dc8 : fetch_word AsanUbsan.M.loaded_segments (0x48dc8 : word) = Some W_48dc8.
Proof. vm_refl. Qed.
Lemma D_48dc8 : decode_any W_48dc8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dcc : bv 32 := 0x00113c23.
Lemma F_48dcc : fetch_word AsanUbsan.M.loaded_segments (0x48dcc : word) = Some W_48dcc.
Proof. vm_refl. Qed.
Lemma D_48dcc : decode_any W_48dcc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dd0 : bv 32 := 0x00813823.
Lemma F_48dd0 : fetch_word AsanUbsan.M.loaded_segments (0x48dd0 : word) = Some W_48dd0.
Proof. vm_refl. Qed.
Lemma D_48dd0 : decode_any W_48dd0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dd4 : bv 32 := 0x00913423.
Lemma F_48dd4 : fetch_word AsanUbsan.M.loaded_segments (0x48dd4 : word) = Some W_48dd4.
Proof. vm_refl. Qed.
Lemma D_48dd4 : decode_any W_48dd4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dd8 : bv 32 := 0x01213023.
Lemma F_48dd8 : fetch_word AsanUbsan.M.loaded_segments (0x48dd8 : word) = Some W_48dd8.
Proof. vm_refl. Qed.
Lemma D_48dd8 : decode_any W_48dd8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ddc : bv 32 := 0x02010413.
Lemma F_48ddc : fetch_word AsanUbsan.M.loaded_segments (0x48ddc : word) = Some W_48ddc.
Proof. vm_refl. Qed.
Lemma D_48ddc : decode_any W_48ddc = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48de0 : bv 32 := 0x0008e517.
Lemma F_48de0 : fetch_word AsanUbsan.M.loaded_segments (0x48de0 : word) = Some W_48de0.
Proof. vm_refl. Qed.
Lemma D_48de0 : decode_any W_48de0 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48de4 : bv 32 := 0x4a050513.
Lemma F_48de4 : fetch_word AsanUbsan.M.loaded_segments (0x48de4 : word) = Some W_48de4.
Proof. vm_refl. Qed.
Lemma D_48de4 : decode_any W_48de4 = Some (OpImm ALU_ADD 10 10 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_48de8 : bv 32 := 0x0a8050ef.
Lemma F_48de8 : fetch_word AsanUbsan.M.loaded_segments (0x48de8 : word) = Some W_48de8.
Proof. vm_refl. Qed.
Lemma D_48de8 : decode_any W_48de8 = Some (Jal 1 20648, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dec : bv 32 := 0x00053483.
Lemma F_48dec : fetch_word AsanUbsan.M.loaded_segments (0x48dec : word) = Some W_48dec.
Proof. vm_refl. Qed.
Lemma D_48dec : decode_any W_48dec = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48df0 : bv 32 := 0x08048863.
Lemma F_48df0 : fetch_word AsanUbsan.M.loaded_segments (0x48df0 : word) = Some W_48df0.
Proof. vm_refl. Qed.
Lemma D_48df0 : decode_any W_48df0 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_48df4 : bv 32 := 0x0604c503.
Lemma F_48df4 : fetch_word AsanUbsan.M.loaded_segments (0x48df4 : word) = Some W_48df4.
Proof. vm_refl. Qed.
Lemma D_48df4 : decode_any W_48df4 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48df8 : bv 32 := 0x0584b903.
Lemma F_48df8 : fetch_word AsanUbsan.M.loaded_segments (0x48df8 : word) = Some W_48df8.
Proof. vm_refl. Qed.
Lemma D_48df8 : decode_any W_48df8 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48dfc : bv 32 := 0x00050863.
Lemma F_48dfc : fetch_word AsanUbsan.M.loaded_segments (0x48dfc : word) = Some W_48dfc.
Proof. vm_refl. Qed.
Lemma D_48dfc : decode_any W_48dfc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e00 : bv 32 := 0x00048513.
Lemma F_48e00 : fetch_word AsanUbsan.M.loaded_segments (0x48e00 : word) = Some W_48e00.
Proof. vm_refl. Qed.
Lemma D_48e00 : decode_any W_48e00 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e04 : bv 32 := 0x00040593.
Lemma F_48e04 : fetch_word AsanUbsan.M.loaded_segments (0x48e04 : word) = Some W_48e04.
Proof. vm_refl. Qed.
Lemma D_48e04 : decode_any W_48e04 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e08 : bv 32 := 0x9e5ff0ef.
Lemma F_48e08 : fetch_word AsanUbsan.M.loaded_segments (0x48e08 : word) = Some W_48e08.
Proof. vm_refl. Qed.
Lemma D_48e08 : decode_any W_48e08 = Some (Jal 1 2095588, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e0c : bv 32 := 0xff890593.
Lemma F_48e0c : fetch_word AsanUbsan.M.loaded_segments (0x48e0c : word) = Some W_48e0c.
Proof. vm_refl. Qed.
Lemma D_48e0c : decode_any W_48e0c = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e10 : bv 32 := 0x00100513.
Lemma F_48e10 : fetch_word AsanUbsan.M.loaded_segments (0x48e10 : word) = Some W_48e10.
Proof. vm_refl. Qed.
Lemma D_48e10 : decode_any W_48e10 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e14 : bv 32 := 0x00b51533.
Lemma F_48e14 : fetch_word AsanUbsan.M.loaded_segments (0x48e14 : word) = Some W_48e14.
Proof. vm_refl. Qed.
Lemma D_48e14 : decode_any W_48e14 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e18 : bv 32 := 0x0005061b.
Lemma F_48e18 : fetch_word AsanUbsan.M.loaded_segments (0x48e18 : word) = Some W_48e18.
Proof. vm_refl. Qed.
Lemma D_48e18 : decode_any W_48e18 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e1c : bv 32 := 0x08c05263.
Lemma F_48e1c : fetch_word AsanUbsan.M.loaded_segments (0x48e1c : word) = Some W_48e1c.
Proof. vm_refl. Qed.
Lemma D_48e1c : decode_any W_48e1c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e20 : bv 32 := 0x000016b7.
Lemma F_48e20 : fetch_word AsanUbsan.M.loaded_segments (0x48e20 : word) = Some W_48e20.
Proof. vm_refl. Qed.
Lemma D_48e20 : decode_any W_48e20 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e24 : bv 32 := 0xff190613.
Lemma F_48e24 : fetch_word AsanUbsan.M.loaded_segments (0x48e24 : word) = Some W_48e24.
Proof. vm_refl. Qed.
Lemma D_48e24 : decode_any W_48e24 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e28 : bv 32 := 0x30000713.
Lemma F_48e28 : fetch_word AsanUbsan.M.loaded_segments (0x48e28 : word) = Some W_48e28.
Proof. vm_refl. Qed.
Lemma D_48e28 : decode_any W_48e28 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e2c : bv 32 := 0xfff00793.
Lemma F_48e2c : fetch_word AsanUbsan.M.loaded_segments (0x48e2c : word) = Some W_48e2c.
Proof. vm_refl. Qed.
Lemma D_48e2c : decode_any W_48e2c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e30 : bv 32 := 0x00c71733.
Lemma F_48e30 : fetch_word AsanUbsan.M.loaded_segments (0x48e30 : word) = Some W_48e30.
Proof. vm_refl. Qed.
Lemma D_48e30 : decode_any W_48e30 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e34 : bv 32 := 0x0104b603.
Lemma F_48e34 : fetch_word AsanUbsan.M.loaded_segments (0x48e34 : word) = Some W_48e34.
Proof. vm_refl. Qed.
Lemma D_48e34 : decode_any W_48e34 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e38 : bv 32 := 0x00b797b3.
Lemma F_48e38 : fetch_word AsanUbsan.M.loaded_segments (0x48e38 : word) = Some W_48e38.
Proof. vm_refl. Qed.
Lemma D_48e38 : decode_any W_48e38 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e3c : bv 32 := 0xfff50813.
Lemma F_48e3c : fetch_word AsanUbsan.M.loaded_segments (0x48e3c : word) = Some W_48e3c.
Proof. vm_refl. Qed.
Lemma D_48e3c : decode_any W_48e3c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e40 : bv 32 := 0x00d485b3.
Lemma F_48e40 : fetch_word AsanUbsan.M.loaded_segments (0x48e40 : word) = Some W_48e40.
Proof. vm_refl. Qed.
Lemma D_48e40 : decode_any W_48e40 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e44 : bv 32 := 0x00e586b3.
Lemma F_48e44 : fetch_word AsanUbsan.M.loaded_segments (0x48e44 : word) = Some W_48e44.
Proof. vm_refl. Qed.
Lemma D_48e44 : decode_any W_48e44 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e48 : bv 32 := 0xfff7c713.
Lemma F_48e48 : fetch_word AsanUbsan.M.loaded_segments (0x48e48 : word) = Some W_48e48.
Proof. vm_refl. Qed.
Lemma D_48e48 : decode_any W_48e48 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e4c : bv 32 := 0x02081813.
Lemma F_48e4c : fetch_word AsanUbsan.M.loaded_segments (0x48e4c : word) = Some W_48e4c.
Proof. vm_refl. Qed.
Lemma D_48e4c : decode_any W_48e4c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e50 : bv 32 := 0x02085793.
Lemma F_48e50 : fetch_word AsanUbsan.M.loaded_segments (0x48e50 : word) = Some W_48e50.
Proof. vm_refl. Qed.
Lemma D_48e50 : decode_any W_48e50 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e54 : bv 32 := 0x00f607b3.
Lemma F_48e54 : fetch_word AsanUbsan.M.loaded_segments (0x48e54 : word) = Some W_48e54.
Proof. vm_refl. Qed.
Lemma D_48e54 : decode_any W_48e54 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e58 : bv 32 := 0x00178813.
Lemma F_48e58 : fetch_word AsanUbsan.M.loaded_segments (0x48e58 : word) = Some W_48e58.
Proof. vm_refl. Qed.
Lemma D_48e58 : decode_any W_48e58 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e5c : bv 32 := 0x00e678b3.
Lemma F_48e5c : fetch_word AsanUbsan.M.loaded_segments (0x48e5c : word) = Some W_48e5c.
Proof. vm_refl. Qed.
Lemma D_48e5c : decode_any W_48e5c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e60 : bv 32 := 0x011687b3.
Lemma F_48e60 : fetch_word AsanUbsan.M.loaded_segments (0x48e60 : word) = Some W_48e60.
Proof. vm_refl. Qed.
Lemma D_48e60 : decode_any W_48e60 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e64 : bv 32 := 0x0007c283.
Lemma F_48e64 : fetch_word AsanUbsan.M.loaded_segments (0x48e64 : word) = Some W_48e64.
Proof. vm_refl. Qed.
Lemma D_48e64 : decode_any W_48e64 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e68 : bv 32 := 0x06028663.
Lemma F_48e68 : fetch_word AsanUbsan.M.loaded_segments (0x48e68 : word) = Some W_48e68.
Proof. vm_refl. Qed.
Lemma D_48e68 : decode_any W_48e68 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e6c : bv 32 := 0xfff5051b.
Lemma F_48e6c : fetch_word AsanUbsan.M.loaded_segments (0x48e6c : word) = Some W_48e6c.
Proof. vm_refl. Qed.
Lemma D_48e6c : decode_any W_48e6c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e70 : bv 32 := 0x00160613.
Lemma F_48e70 : fetch_word AsanUbsan.M.loaded_segments (0x48e70 : word) = Some W_48e70.
Proof. vm_refl. Qed.
Lemma D_48e70 : decode_any W_48e70 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e74 : bv 32 := 0xfe0514e3.
Lemma F_48e74 : fetch_word AsanUbsan.M.loaded_segments (0x48e74 : word) = Some W_48e74.
Proof. vm_refl. Qed.
Lemma D_48e74 : decode_any W_48e74 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e78 : bv 32 := 0x0104b823.
Lemma F_48e78 : fetch_word AsanUbsan.M.loaded_segments (0x48e78 : word) = Some W_48e78.
Proof. vm_refl. Qed.
Lemma D_48e78 : decode_any W_48e78 = Some (Store SZ8 9 16 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e7c : bv 32 := 0x0400006f.
Lemma F_48e7c : fetch_word AsanUbsan.M.loaded_segments (0x48e7c : word) = Some W_48e7c.
Proof. vm_refl. Qed.
Lemma D_48e7c : decode_any W_48e7c = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e80 : bv 32 := 0x0008d517.
Lemma F_48e80 : fetch_word AsanUbsan.M.loaded_segments (0x48e80 : word) = Some W_48e80.
Proof. vm_refl. Qed.
Lemma D_48e80 : decode_any W_48e80 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e84 : bv 32 := 0x6a053503.
Lemma F_48e84 : fetch_word AsanUbsan.M.loaded_segments (0x48e84 : word) = Some W_48e84.
Proof. vm_refl. Qed.
Lemma D_48e84 : decode_any W_48e84 = Some (Load SZ8 true 10 10 1696, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e88 : bv 32 := 0x00052503.
Lemma F_48e88 : fetch_word AsanUbsan.M.loaded_segments (0x48e88 : word) = Some W_48e88.
Proof. vm_refl. Qed.
Lemma D_48e88 : decode_any W_48e88 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e8c : bv 32 := 0x02050863.
Lemma F_48e8c : fetch_word AsanUbsan.M.loaded_segments (0x48e8c : word) = Some W_48e8c.
Proof. vm_refl. Qed.
Lemma D_48e8c : decode_any W_48e8c = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e90 : bv 32 := 0x3d5200ef.
Lemma F_48e90 : fetch_word AsanUbsan.M.loaded_segments (0x48e90 : word) = Some W_48e90.
Proof. vm_refl. Qed.
Lemma D_48e90 : decode_any W_48e90 = Some (Jal 1 134100, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e94 : bv 32 := 0x02050463.
Lemma F_48e94 : fetch_word AsanUbsan.M.loaded_segments (0x48e94 : word) = Some W_48e94.
Proof. vm_refl. Qed.
Lemma D_48e94 : decode_any W_48e94 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e98 : bv 32 := 0x02850583.
Lemma F_48e98 : fetch_word AsanUbsan.M.loaded_segments (0x48e98 : word) = Some W_48e98.
Proof. vm_refl. Qed.
Lemma D_48e98 : decode_any W_48e98 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_48e9c : bv 32 := 0x0a058663.
Lemma F_48e9c : fetch_word AsanUbsan.M.loaded_segments (0x48e9c : word) = Some W_48e9c.
Proof. vm_refl. Qed.
Lemma D_48e9c : decode_any W_48e9c = Some (Branch BC_EQ 11 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ea0 : bv 32 := 0x00000513.
Lemma F_48ea0 : fetch_word AsanUbsan.M.loaded_segments (0x48ea0 : word) = Some W_48ea0.
Proof. vm_refl. Qed.
Lemma D_48ea0 : decode_any W_48ea0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ea4 : bv 32 := 0x01813083.
Lemma F_48ea4 : fetch_word AsanUbsan.M.loaded_segments (0x48ea4 : word) = Some W_48ea4.
Proof. vm_refl. Qed.
Lemma D_48ea4 : decode_any W_48ea4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ea8 : bv 32 := 0x01013403.
Lemma F_48ea8 : fetch_word AsanUbsan.M.loaded_segments (0x48ea8 : word) = Some W_48ea8.
Proof. vm_refl. Qed.
Lemma D_48ea8 : decode_any W_48ea8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48eac : bv 32 := 0x00813483.
Lemma F_48eac : fetch_word AsanUbsan.M.loaded_segments (0x48eac : word) = Some W_48eac.
Proof. vm_refl. Qed.
Lemma D_48eac : decode_any W_48eac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48eb0 : bv 32 := 0x00013903.
Lemma F_48eb0 : fetch_word AsanUbsan.M.loaded_segments (0x48eb0 : word) = Some W_48eb0.
Proof. vm_refl. Qed.
Lemma D_48eb0 : decode_any W_48eb0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48eb4 : bv 32 := 0x02010113.
Lemma F_48eb4 : fetch_word AsanUbsan.M.loaded_segments (0x48eb4 : word) = Some W_48eb4.
Proof. vm_refl. Qed.
Lemma D_48eb4 : decode_any W_48eb4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48eb8 : bv 32 := 0x00008067.
Lemma F_48eb8 : fetch_word AsanUbsan.M.loaded_segments (0x48eb8 : word) = Some W_48eb8.
Proof. vm_refl. Qed.
Lemma D_48eb8 : decode_any W_48eb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ebc : bv 32 := 0x01813083.
Lemma F_48ebc : fetch_word AsanUbsan.M.loaded_segments (0x48ebc : word) = Some W_48ebc.
Proof. vm_refl. Qed.
Lemma D_48ebc : decode_any W_48ebc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ec0 : bv 32 := 0x01013403.
Lemma F_48ec0 : fetch_word AsanUbsan.M.loaded_segments (0x48ec0 : word) = Some W_48ec0.
Proof. vm_refl. Qed.
Lemma D_48ec0 : decode_any W_48ec0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ec4 : bv 32 := 0x00813483.
Lemma F_48ec4 : fetch_word AsanUbsan.M.loaded_segments (0x48ec4 : word) = Some W_48ec4.
Proof. vm_refl. Qed.
Lemma D_48ec4 : decode_any W_48ec4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ec8 : bv 32 := 0x00013903.
Lemma F_48ec8 : fetch_word AsanUbsan.M.loaded_segments (0x48ec8 : word) = Some W_48ec8.
Proof. vm_refl. Qed.
Lemma D_48ec8 : decode_any W_48ec8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ecc : bv 32 := 0x02010113.
Lemma F_48ecc : fetch_word AsanUbsan.M.loaded_segments (0x48ecc : word) = Some W_48ecc.
Proof. vm_refl. Qed.
Lemma D_48ecc : decode_any W_48ecc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ed0 : bv 32 := 0x00008067.
Lemma F_48ed0 : fetch_word AsanUbsan.M.loaded_segments (0x48ed0 : word) = Some W_48ed0.
Proof. vm_refl. Qed.
Lemma D_48ed0 : decode_any W_48ed0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ed4 : bv 32 := 0x00160613.
Lemma F_48ed4 : fetch_word AsanUbsan.M.loaded_segments (0x48ed4 : word) = Some W_48ed4.
Proof. vm_refl. Qed.
Lemma D_48ed4 : decode_any W_48ed4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ed8 : bv 32 := 0x00100513.
Lemma F_48ed8 : fetch_word AsanUbsan.M.loaded_segments (0x48ed8 : word) = Some W_48ed8.
Proof. vm_refl. Qed.
Lemma D_48ed8 : decode_any W_48ed8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48edc : bv 32 := 0xffb90693.
Lemma F_48edc : fetch_word AsanUbsan.M.loaded_segments (0x48edc : word) = Some W_48edc.
Proof. vm_refl. Qed.
Lemma D_48edc : decode_any W_48edc = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ee0 : bv 32 := 0x00c4b823.
Lemma F_48ee0 : fetch_word AsanUbsan.M.loaded_segments (0x48ee0 : word) = Some W_48ee0.
Proof. vm_refl. Qed.
Lemma D_48ee0 : decode_any W_48ee0 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ee4 : bv 32 := 0x00a78023.
Lemma F_48ee4 : fetch_word AsanUbsan.M.loaded_segments (0x48ee4 : word) = Some W_48ee4.
Proof. vm_refl. Qed.
Lemma D_48ee4 : decode_any W_48ee4 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ee8 : bv 32 := 0x00d51533.
Lemma F_48ee8 : fetch_word AsanUbsan.M.loaded_segments (0x48ee8 : word) = Some W_48ee8.
Proof. vm_refl. Qed.
Lemma D_48ee8 : decode_any W_48ee8 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_48eec : bv 32 := 0x00200613.
Lemma F_48eec : fetch_word AsanUbsan.M.loaded_segments (0x48eec : word) = Some W_48eec.
Proof. vm_refl. Qed.
Lemma D_48eec : decode_any W_48eec = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ef0 : bv 32 := 0x00889893.
Lemma F_48ef0 : fetch_word AsanUbsan.M.loaded_segments (0x48ef0 : word) = Some W_48ef0.
Proof. vm_refl. Qed.
Lemma D_48ef0 : decode_any W_48ef0 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ef4 : bv 32 := 0x01261633.
Lemma F_48ef4 : fetch_word AsanUbsan.M.loaded_segments (0x48ef4 : word) = Some W_48ef4.
Proof. vm_refl. Qed.
Lemma D_48ef4 : decode_any W_48ef4 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ef8 : bv 32 := 0x00a58533.
Lemma F_48ef8 : fetch_word AsanUbsan.M.loaded_segments (0x48ef8 : word) = Some W_48ef8.
Proof. vm_refl. Qed.
Lemma D_48ef8 : decode_any W_48ef8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_48efc : bv 32 := 0x01160633.
Lemma F_48efc : fetch_word AsanUbsan.M.loaded_segments (0x48efc : word) = Some W_48efc.
Proof. vm_refl. Qed.
Lemma D_48efc : decode_any W_48efc = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f00 : bv 32 := 0x00c504b3.
Lemma F_48f00 : fetch_word AsanUbsan.M.loaded_segments (0x48f00 : word) = Some W_48f00.
Proof. vm_refl. Qed.
Lemma D_48f00 : decode_any W_48f00 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f04 : bv 32 := 0x0084bc23.
Lemma F_48f04 : fetch_word AsanUbsan.M.loaded_segments (0x48f04 : word) = Some W_48f04.
Proof. vm_refl. Qed.
Lemma D_48f04 : decode_any W_48f04 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f08 : bv 32 := 0x0ef4bc23.
Lemma F_48f08 : fetch_word AsanUbsan.M.loaded_segments (0x48f08 : word) = Some W_48f08.
Proof. vm_refl. Qed.
Lemma D_48f08 : decode_any W_48f08 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f0c : bv 32 := 0x00048513.
Lemma F_48f0c : fetch_word AsanUbsan.M.loaded_segments (0x48f0c : word) = Some W_48f0c.
Proof. vm_refl. Qed.
Lemma D_48f0c : decode_any W_48f0c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f10 : bv 32 := 0x200000ef.
Lemma F_48f10 : fetch_word AsanUbsan.M.loaded_segments (0x48f10 : word) = Some W_48f10.
Proof. vm_refl. Qed.
Lemma D_48f10 : decode_any W_48f10 = Some (Jal 1 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f14 : bv 32 := 0x00050593.
Lemma F_48f14 : fetch_word AsanUbsan.M.loaded_segments (0x48f14 : word) = Some W_48f14.
Proof. vm_refl. Qed.
Lemma D_48f14 : decode_any W_48f14 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f18 : bv 32 := 0x00048513.
Lemma F_48f18 : fetch_word AsanUbsan.M.loaded_segments (0x48f18 : word) = Some W_48f18.
Proof. vm_refl. Qed.
Lemma D_48f18 : decode_any W_48f18 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f1c : bv 32 := 0x00000613.
Lemma F_48f1c : fetch_word AsanUbsan.M.loaded_segments (0x48f1c : word) = Some W_48f1c.
Proof. vm_refl. Qed.
Lemma D_48f1c : decode_any W_48f1c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f20 : bv 32 := 0x0005b023.
Lemma F_48f20 : fetch_word AsanUbsan.M.loaded_segments (0x48f20 : word) = Some W_48f20.
Proof. vm_refl. Qed.
Lemma D_48f20 : decode_any W_48f20 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f24 : bv 32 := 0x0005b423.
Lemma F_48f24 : fetch_word AsanUbsan.M.loaded_segments (0x48f24 : word) = Some W_48f24.
Proof. vm_refl. Qed.
Lemma D_48f24 : decode_any W_48f24 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f28 : bv 32 := 0x0005b823.
Lemma F_48f28 : fetch_word AsanUbsan.M.loaded_segments (0x48f28 : word) = Some W_48f28.
Proof. vm_refl. Qed.
Lemma D_48f28 : decode_any W_48f28 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f2c : bv 32 := 0x0005bc23.
Lemma F_48f2c : fetch_word AsanUbsan.M.loaded_segments (0x48f2c : word) = Some W_48f2c.
Proof. vm_refl. Qed.
Lemma D_48f2c : decode_any W_48f2c = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f30 : bv 32 := 0x01813083.
Lemma F_48f30 : fetch_word AsanUbsan.M.loaded_segments (0x48f30 : word) = Some W_48f30.
Proof. vm_refl. Qed.
Lemma D_48f30 : decode_any W_48f30 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f34 : bv 32 := 0x01013403.
Lemma F_48f34 : fetch_word AsanUbsan.M.loaded_segments (0x48f34 : word) = Some W_48f34.
Proof. vm_refl. Qed.
Lemma D_48f34 : decode_any W_48f34 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f38 : bv 32 := 0x00813483.
Lemma F_48f38 : fetch_word AsanUbsan.M.loaded_segments (0x48f38 : word) = Some W_48f38.
Proof. vm_refl. Qed.
Lemma D_48f38 : decode_any W_48f38 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f3c : bv 32 := 0x00013903.
Lemma F_48f3c : fetch_word AsanUbsan.M.loaded_segments (0x48f3c : word) = Some W_48f3c.
Proof. vm_refl. Qed.
Lemma D_48f3c : decode_any W_48f3c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f40 : bv 32 := 0x02010113.
Lemma F_48f40 : fetch_word AsanUbsan.M.loaded_segments (0x48f40 : word) = Some W_48f40.
Proof. vm_refl. Qed.
Lemma D_48f40 : decode_any W_48f40 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f44 : bv 32 := 0x00008067.
Lemma F_48f44 : fetch_word AsanUbsan.M.loaded_segments (0x48f44 : word) = Some W_48f44.
Proof. vm_refl. Qed.
Lemma D_48f44 : decode_any W_48f44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f48 : bv 32 := 0x04853483.
Lemma F_48f48 : fetch_word AsanUbsan.M.loaded_segments (0x48f48 : word) = Some W_48f48.
Proof. vm_refl. Qed.
Lemma D_48f48 : decode_any W_48f48 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f4c : bv 32 := 0x00100593.
Lemma F_48f4c : fetch_word AsanUbsan.M.loaded_segments (0x48f4c : word) = Some W_48f4c.
Proof. vm_refl. Qed.
Lemma D_48f4c : decode_any W_48f4c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f50 : bv 32 := 0x0095e663.
Lemma F_48f50 : fetch_word AsanUbsan.M.loaded_segments (0x48f50 : word) = Some W_48f50.
Proof. vm_refl. Qed.
Lemma D_48f50 : decode_any W_48f50 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f54 : bv 32 := 0x585200ef.
Lemma F_48f54 : fetch_word AsanUbsan.M.loaded_segments (0x48f54 : word) = Some W_48f54.
Proof. vm_refl. Qed.
Lemma D_48f54 : decode_any W_48f54 = Some (Jal 1 134532, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f58 : bv 32 := 0x00050493.
Lemma F_48f58 : fetch_word AsanUbsan.M.loaded_segments (0x48f58 : word) = Some W_48f58.
Proof. vm_refl. Qed.
Lemma D_48f58 : decode_any W_48f58 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f5c : bv 32 := 0xe8049ce3.
Lemma F_48f5c : fetch_word AsanUbsan.M.loaded_segments (0x48f5c : word) = Some W_48f5c.
Proof. vm_refl. Qed.
Lemma D_48f5c : decode_any W_48f5c = Some (Branch BC_NE 9 0 7832, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f60 : bv 32 := 0xf41ff06f.
Lemma F_48f60 : fetch_word AsanUbsan.M.loaded_segments (0x48f60 : word) = Some W_48f60.
Proof. vm_refl. Qed.
Lemma D_48f60 : decode_any W_48f60 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f64 : bv 32 := 0xfe010113.
Lemma F_48f64 : fetch_word AsanUbsan.M.loaded_segments (0x48f64 : word) = Some W_48f64.
Proof. vm_refl. Qed.
Lemma D_48f64 : decode_any W_48f64 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f68 : bv 32 := 0x00113c23.
Lemma F_48f68 : fetch_word AsanUbsan.M.loaded_segments (0x48f68 : word) = Some W_48f68.
Proof. vm_refl. Qed.
Lemma D_48f68 : decode_any W_48f68 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f6c : bv 32 := 0x00813823.
Lemma F_48f6c : fetch_word AsanUbsan.M.loaded_segments (0x48f6c : word) = Some W_48f6c.
Proof. vm_refl. Qed.
Lemma D_48f6c : decode_any W_48f6c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f70 : bv 32 := 0x00913423.
Lemma F_48f70 : fetch_word AsanUbsan.M.loaded_segments (0x48f70 : word) = Some W_48f70.
Proof. vm_refl. Qed.
Lemma D_48f70 : decode_any W_48f70 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f74 : bv 32 := 0x01213023.
Lemma F_48f74 : fetch_word AsanUbsan.M.loaded_segments (0x48f74 : word) = Some W_48f74.
Proof. vm_refl. Qed.
Lemma D_48f74 : decode_any W_48f74 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f78 : bv 32 := 0x02010413.
Lemma F_48f78 : fetch_word AsanUbsan.M.loaded_segments (0x48f78 : word) = Some W_48f78.
Proof. vm_refl. Qed.
Lemma D_48f78 : decode_any W_48f78 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f7c : bv 32 := 0x0008e517.
Lemma F_48f7c : fetch_word AsanUbsan.M.loaded_segments (0x48f7c : word) = Some W_48f7c.
Proof. vm_refl. Qed.
Lemma D_48f7c : decode_any W_48f7c = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f80 : bv 32 := 0x30450513.
Lemma F_48f80 : fetch_word AsanUbsan.M.loaded_segments (0x48f80 : word) = Some W_48f80.
Proof. vm_refl. Qed.
Lemma D_48f80 : decode_any W_48f80 = Some (OpImm ALU_ADD 10 10 772, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f84 : bv 32 := 0x70d040ef.
Lemma F_48f84 : fetch_word AsanUbsan.M.loaded_segments (0x48f84 : word) = Some W_48f84.
Proof. vm_refl. Qed.
Lemma D_48f84 : decode_any W_48f84 = Some (Jal 1 20236, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f88 : bv 32 := 0x00053483.
Lemma F_48f88 : fetch_word AsanUbsan.M.loaded_segments (0x48f88 : word) = Some W_48f88.
Proof. vm_refl. Qed.
Lemma D_48f88 : decode_any W_48f88 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f8c : bv 32 := 0x08048863.
Lemma F_48f8c : fetch_word AsanUbsan.M.loaded_segments (0x48f8c : word) = Some W_48f8c.
Proof. vm_refl. Qed.
Lemma D_48f8c : decode_any W_48f8c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f90 : bv 32 := 0x0604c503.
Lemma F_48f90 : fetch_word AsanUbsan.M.loaded_segments (0x48f90 : word) = Some W_48f90.
Proof. vm_refl. Qed.
Lemma D_48f90 : decode_any W_48f90 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f94 : bv 32 := 0x0584b903.
Lemma F_48f94 : fetch_word AsanUbsan.M.loaded_segments (0x48f94 : word) = Some W_48f94.
Proof. vm_refl. Qed.
Lemma D_48f94 : decode_any W_48f94 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f98 : bv 32 := 0x00050863.
Lemma F_48f98 : fetch_word AsanUbsan.M.loaded_segments (0x48f98 : word) = Some W_48f98.
Proof. vm_refl. Qed.
Lemma D_48f98 : decode_any W_48f98 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_48f9c : bv 32 := 0x00048513.
Lemma F_48f9c : fetch_word AsanUbsan.M.loaded_segments (0x48f9c : word) = Some W_48f9c.
Proof. vm_refl. Qed.
Lemma D_48f9c : decode_any W_48f9c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fa0 : bv 32 := 0x00040593.
Lemma F_48fa0 : fetch_word AsanUbsan.M.loaded_segments (0x48fa0 : word) = Some W_48fa0.
Proof. vm_refl. Qed.
Lemma D_48fa0 : decode_any W_48fa0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fa4 : bv 32 := 0x849ff0ef.
Lemma F_48fa4 : fetch_word AsanUbsan.M.loaded_segments (0x48fa4 : word) = Some W_48fa4.
Proof. vm_refl. Qed.
Lemma D_48fa4 : decode_any W_48fa4 = Some (Jal 1 2095176, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fa8 : bv 32 := 0xff790593.
Lemma F_48fa8 : fetch_word AsanUbsan.M.loaded_segments (0x48fa8 : word) = Some W_48fa8.
Proof. vm_refl. Qed.
Lemma D_48fa8 : decode_any W_48fa8 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fac : bv 32 := 0x00100513.
Lemma F_48fac : fetch_word AsanUbsan.M.loaded_segments (0x48fac : word) = Some W_48fac.
Proof. vm_refl. Qed.
Lemma D_48fac : decode_any W_48fac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fb0 : bv 32 := 0x00b51533.
Lemma F_48fb0 : fetch_word AsanUbsan.M.loaded_segments (0x48fb0 : word) = Some W_48fb0.
Proof. vm_refl. Qed.
Lemma D_48fb0 : decode_any W_48fb0 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fb4 : bv 32 := 0x0005061b.
Lemma F_48fb4 : fetch_word AsanUbsan.M.loaded_segments (0x48fb4 : word) = Some W_48fb4.
Proof. vm_refl. Qed.
Lemma D_48fb4 : decode_any W_48fb4 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fb8 : bv 32 := 0x08c05263.
Lemma F_48fb8 : fetch_word AsanUbsan.M.loaded_segments (0x48fb8 : word) = Some W_48fb8.
Proof. vm_refl. Qed.
Lemma D_48fb8 : decode_any W_48fb8 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fbc : bv 32 := 0x000016b7.
Lemma F_48fbc : fetch_word AsanUbsan.M.loaded_segments (0x48fbc : word) = Some W_48fbc.
Proof. vm_refl. Qed.
Lemma D_48fbc : decode_any W_48fbc = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fc0 : bv 32 := 0xff190613.
Lemma F_48fc0 : fetch_word AsanUbsan.M.loaded_segments (0x48fc0 : word) = Some W_48fc0.
Proof. vm_refl. Qed.
Lemma D_48fc0 : decode_any W_48fc0 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fc4 : bv 32 := 0x38000713.
Lemma F_48fc4 : fetch_word AsanUbsan.M.loaded_segments (0x48fc4 : word) = Some W_48fc4.
Proof. vm_refl. Qed.
Lemma D_48fc4 : decode_any W_48fc4 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fc8 : bv 32 := 0xfff00793.
Lemma F_48fc8 : fetch_word AsanUbsan.M.loaded_segments (0x48fc8 : word) = Some W_48fc8.
Proof. vm_refl. Qed.
Lemma D_48fc8 : decode_any W_48fc8 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fcc : bv 32 := 0x00c71733.
Lemma F_48fcc : fetch_word AsanUbsan.M.loaded_segments (0x48fcc : word) = Some W_48fcc.
Proof. vm_refl. Qed.
Lemma D_48fcc : decode_any W_48fcc = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fd0 : bv 32 := 0x0184b603.
Lemma F_48fd0 : fetch_word AsanUbsan.M.loaded_segments (0x48fd0 : word) = Some W_48fd0.
Proof. vm_refl. Qed.
Lemma D_48fd0 : decode_any W_48fd0 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fd4 : bv 32 := 0x00b797b3.
Lemma F_48fd4 : fetch_word AsanUbsan.M.loaded_segments (0x48fd4 : word) = Some W_48fd4.
Proof. vm_refl. Qed.
Lemma D_48fd4 : decode_any W_48fd4 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fd8 : bv 32 := 0xfff50813.
Lemma F_48fd8 : fetch_word AsanUbsan.M.loaded_segments (0x48fd8 : word) = Some W_48fd8.
Proof. vm_refl. Qed.
Lemma D_48fd8 : decode_any W_48fd8 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fdc : bv 32 := 0x00d485b3.
Lemma F_48fdc : fetch_word AsanUbsan.M.loaded_segments (0x48fdc : word) = Some W_48fdc.
Proof. vm_refl. Qed.
Lemma D_48fdc : decode_any W_48fdc = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fe0 : bv 32 := 0x00e586b3.
Lemma F_48fe0 : fetch_word AsanUbsan.M.loaded_segments (0x48fe0 : word) = Some W_48fe0.
Proof. vm_refl. Qed.
Lemma D_48fe0 : decode_any W_48fe0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fe4 : bv 32 := 0xfff7c713.
Lemma F_48fe4 : fetch_word AsanUbsan.M.loaded_segments (0x48fe4 : word) = Some W_48fe4.
Proof. vm_refl. Qed.
Lemma D_48fe4 : decode_any W_48fe4 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fe8 : bv 32 := 0x02081813.
Lemma F_48fe8 : fetch_word AsanUbsan.M.loaded_segments (0x48fe8 : word) = Some W_48fe8.
Proof. vm_refl. Qed.
Lemma D_48fe8 : decode_any W_48fe8 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48fec : bv 32 := 0x02085793.
Lemma F_48fec : fetch_word AsanUbsan.M.loaded_segments (0x48fec : word) = Some W_48fec.
Proof. vm_refl. Qed.
Lemma D_48fec : decode_any W_48fec = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ff0 : bv 32 := 0x00f607b3.
Lemma F_48ff0 : fetch_word AsanUbsan.M.loaded_segments (0x48ff0 : word) = Some W_48ff0.
Proof. vm_refl. Qed.
Lemma D_48ff0 : decode_any W_48ff0 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ff4 : bv 32 := 0x00178813.
Lemma F_48ff4 : fetch_word AsanUbsan.M.loaded_segments (0x48ff4 : word) = Some W_48ff4.
Proof. vm_refl. Qed.
Lemma D_48ff4 : decode_any W_48ff4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ff8 : bv 32 := 0x00e678b3.
Lemma F_48ff8 : fetch_word AsanUbsan.M.loaded_segments (0x48ff8 : word) = Some W_48ff8.
Proof. vm_refl. Qed.
Lemma D_48ff8 : decode_any W_48ff8 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_48ffc : bv 32 := 0x011687b3.
Lemma F_48ffc : fetch_word AsanUbsan.M.loaded_segments (0x48ffc : word) = Some W_48ffc.
Proof. vm_refl. Qed.
Lemma D_48ffc : decode_any W_48ffc = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_49000 : bv 32 := 0x0007c283.
Lemma F_49000 : fetch_word AsanUbsan.M.loaded_segments (0x49000 : word) = Some W_49000.
Proof. vm_refl. Qed.
Lemma D_49000 : decode_any W_49000 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49004 : bv 32 := 0x06028663.
Lemma F_49004 : fetch_word AsanUbsan.M.loaded_segments (0x49004 : word) = Some W_49004.
Proof. vm_refl. Qed.
Lemma D_49004 : decode_any W_49004 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_49008 : bv 32 := 0xfff5051b.
Lemma F_49008 : fetch_word AsanUbsan.M.loaded_segments (0x49008 : word) = Some W_49008.
Proof. vm_refl. Qed.
Lemma D_49008 : decode_any W_49008 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4900c : bv 32 := 0x00160613.
Lemma F_4900c : fetch_word AsanUbsan.M.loaded_segments (0x4900c : word) = Some W_4900c.
Proof. vm_refl. Qed.
Lemma D_4900c : decode_any W_4900c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_49010 : bv 32 := 0xfe0514e3.
Lemma F_49010 : fetch_word AsanUbsan.M.loaded_segments (0x49010 : word) = Some W_49010.
Proof. vm_refl. Qed.
Lemma D_49010 : decode_any W_49010 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_49014 : bv 32 := 0x0104bc23.
Lemma F_49014 : fetch_word AsanUbsan.M.loaded_segments (0x49014 : word) = Some W_49014.
Proof. vm_refl. Qed.
Lemma D_49014 : decode_any W_49014 = Some (Store SZ8 9 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_49018 : bv 32 := 0x0400006f.
Lemma F_49018 : fetch_word AsanUbsan.M.loaded_segments (0x49018 : word) = Some W_49018.
Proof. vm_refl. Qed.
Lemma D_49018 : decode_any W_49018 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4901c : bv 32 := 0x0008d517.
Lemma F_4901c : fetch_word AsanUbsan.M.loaded_segments (0x4901c : word) = Some W_4901c.
Proof. vm_refl. Qed.
Lemma D_4901c : decode_any W_4901c = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_49020 : bv 32 := 0x50453503.
Lemma F_49020 : fetch_word AsanUbsan.M.loaded_segments (0x49020 : word) = Some W_49020.
Proof. vm_refl. Qed.
Lemma D_49020 : decode_any W_49020 = Some (Load SZ8 true 10 10 1284, 4%Z).
Proof. vm_refl. Qed.

Definition W_49024 : bv 32 := 0x00052503.
Lemma F_49024 : fetch_word AsanUbsan.M.loaded_segments (0x49024 : word) = Some W_49024.
Proof. vm_refl. Qed.
Lemma D_49024 : decode_any W_49024 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49028 : bv 32 := 0x02050863.
Lemma F_49028 : fetch_word AsanUbsan.M.loaded_segments (0x49028 : word) = Some W_49028.
Proof. vm_refl. Qed.
Lemma D_49028 : decode_any W_49028 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4902c : bv 32 := 0x239200ef.
Lemma F_4902c : fetch_word AsanUbsan.M.loaded_segments (0x4902c : word) = Some W_4902c.
Proof. vm_refl. Qed.
Lemma D_4902c : decode_any W_4902c = Some (Jal 1 133688, 4%Z).
Proof. vm_refl. Qed.

Definition W_49030 : bv 32 := 0x02050463.
Lemma F_49030 : fetch_word AsanUbsan.M.loaded_segments (0x49030 : word) = Some W_49030.
Proof. vm_refl. Qed.
Lemma D_49030 : decode_any W_49030 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_49034 : bv 32 := 0x02850583.
Lemma F_49034 : fetch_word AsanUbsan.M.loaded_segments (0x49034 : word) = Some W_49034.
Proof. vm_refl. Qed.
Lemma D_49034 : decode_any W_49034 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_49038 : bv 32 := 0x0a058e63.
Lemma F_49038 : fetch_word AsanUbsan.M.loaded_segments (0x49038 : word) = Some W_49038.
Proof. vm_refl. Qed.
Lemma D_49038 : decode_any W_49038 = Some (Branch BC_EQ 11 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_4903c : bv 32 := 0x00000513.
Lemma F_4903c : fetch_word AsanUbsan.M.loaded_segments (0x4903c : word) = Some W_4903c.
Proof. vm_refl. Qed.
Lemma D_4903c : decode_any W_4903c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49040 : bv 32 := 0x01813083.
Lemma F_49040 : fetch_word AsanUbsan.M.loaded_segments (0x49040 : word) = Some W_49040.
Proof. vm_refl. Qed.
Lemma D_49040 : decode_any W_49040 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_49044 : bv 32 := 0x01013403.
Lemma F_49044 : fetch_word AsanUbsan.M.loaded_segments (0x49044 : word) = Some W_49044.
Proof. vm_refl. Qed.
Lemma D_49044 : decode_any W_49044 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_49048 : bv 32 := 0x00813483.
Lemma F_49048 : fetch_word AsanUbsan.M.loaded_segments (0x49048 : word) = Some W_49048.
Proof. vm_refl. Qed.
Lemma D_49048 : decode_any W_49048 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4904c : bv 32 := 0x00013903.
Lemma F_4904c : fetch_word AsanUbsan.M.loaded_segments (0x4904c : word) = Some W_4904c.
Proof. vm_refl. Qed.
Lemma D_4904c : decode_any W_4904c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49050 : bv 32 := 0x02010113.
Lemma F_49050 : fetch_word AsanUbsan.M.loaded_segments (0x49050 : word) = Some W_49050.
Proof. vm_refl. Qed.
Lemma D_49050 : decode_any W_49050 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_49054 : bv 32 := 0x00008067.
Lemma F_49054 : fetch_word AsanUbsan.M.loaded_segments (0x49054 : word) = Some W_49054.
Proof. vm_refl. Qed.
Lemma D_49054 : decode_any W_49054 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49058 : bv 32 := 0x01813083.
Lemma F_49058 : fetch_word AsanUbsan.M.loaded_segments (0x49058 : word) = Some W_49058.
Proof. vm_refl. Qed.
Lemma D_49058 : decode_any W_49058 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4905c : bv 32 := 0x01013403.
Lemma F_4905c : fetch_word AsanUbsan.M.loaded_segments (0x4905c : word) = Some W_4905c.
Proof. vm_refl. Qed.
Lemma D_4905c : decode_any W_4905c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_49060 : bv 32 := 0x00813483.
Lemma F_49060 : fetch_word AsanUbsan.M.loaded_segments (0x49060 : word) = Some W_49060.
Proof. vm_refl. Qed.
Lemma D_49060 : decode_any W_49060 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_49064 : bv 32 := 0x00013903.
Lemma F_49064 : fetch_word AsanUbsan.M.loaded_segments (0x49064 : word) = Some W_49064.
Proof. vm_refl. Qed.
Lemma D_49064 : decode_any W_49064 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49068 : bv 32 := 0x02010113.
Lemma F_49068 : fetch_word AsanUbsan.M.loaded_segments (0x49068 : word) = Some W_49068.
Proof. vm_refl. Qed.
Lemma D_49068 : decode_any W_49068 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4906c : bv 32 := 0x00008067.
Lemma F_4906c : fetch_word AsanUbsan.M.loaded_segments (0x4906c : word) = Some W_4906c.
Proof. vm_refl. Qed.
Lemma D_4906c : decode_any W_4906c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49070 : bv 32 := 0x00160613.
Lemma F_49070 : fetch_word AsanUbsan.M.loaded_segments (0x49070 : word) = Some W_49070.
Proof. vm_refl. Qed.
Lemma D_49070 : decode_any W_49070 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_49074 : bv 32 := 0x00100513.
Lemma F_49074 : fetch_word AsanUbsan.M.loaded_segments (0x49074 : word) = Some W_49074.
Proof. vm_refl. Qed.
Lemma D_49074 : decode_any W_49074 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_49078 : bv 32 := 0xffb90693.
Lemma F_49078 : fetch_word AsanUbsan.M.loaded_segments (0x49078 : word) = Some W_49078.
Proof. vm_refl. Qed.
Lemma D_49078 : decode_any W_49078 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_4907c : bv 32 := 0x00c4bc23.
Lemma F_4907c : fetch_word AsanUbsan.M.loaded_segments (0x4907c : word) = Some W_4907c.
Proof. vm_refl. Qed.
Lemma D_4907c : decode_any W_4907c = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_49080 : bv 32 := 0x00a78023.
Lemma F_49080 : fetch_word AsanUbsan.M.loaded_segments (0x49080 : word) = Some W_49080.
Proof. vm_refl. Qed.
Lemma D_49080 : decode_any W_49080 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49084 : bv 32 := 0x00d51533.
Lemma F_49084 : fetch_word AsanUbsan.M.loaded_segments (0x49084 : word) = Some W_49084.
Proof. vm_refl. Qed.
Lemma D_49084 : decode_any W_49084 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_49088 : bv 32 := 0x00300613.
Lemma F_49088 : fetch_word AsanUbsan.M.loaded_segments (0x49088 : word) = Some W_49088.
Proof. vm_refl. Qed.
Lemma D_49088 : decode_any W_49088 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4908c : bv 32 := 0x00989893.
Lemma F_4908c : fetch_word AsanUbsan.M.loaded_segments (0x4908c : word) = Some W_4908c.
Proof. vm_refl. Qed.
Lemma D_4908c : decode_any W_4908c = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_49090 : bv 32 := 0x01261633.
Lemma F_49090 : fetch_word AsanUbsan.M.loaded_segments (0x49090 : word) = Some W_49090.
Proof. vm_refl. Qed.
Lemma D_49090 : decode_any W_49090 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_49094 : bv 32 := 0x00a58533.
Lemma F_49094 : fetch_word AsanUbsan.M.loaded_segments (0x49094 : word) = Some W_49094.
Proof. vm_refl. Qed.
Lemma D_49094 : decode_any W_49094 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_49098 : bv 32 := 0x01160633.
Lemma F_49098 : fetch_word AsanUbsan.M.loaded_segments (0x49098 : word) = Some W_49098.
Proof. vm_refl. Qed.
Lemma D_49098 : decode_any W_49098 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_4909c : bv 32 := 0x00c504b3.
Lemma F_4909c : fetch_word AsanUbsan.M.loaded_segments (0x4909c : word) = Some W_4909c.
Proof. vm_refl. Qed.
Lemma D_4909c : decode_any W_4909c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_490a0 : bv 32 := 0x0084bc23.
Lemma F_490a0 : fetch_word AsanUbsan.M.loaded_segments (0x490a0 : word) = Some W_490a0.
Proof. vm_refl. Qed.
Lemma D_490a0 : decode_any W_490a0 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_490a4 : bv 32 := 0x1ef4bc23.
Lemma F_490a4 : fetch_word AsanUbsan.M.loaded_segments (0x490a4 : word) = Some W_490a4.
Proof. vm_refl. Qed.
Lemma D_490a4 : decode_any W_490a4 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

Definition W_490a8 : bv 32 := 0x00048513.
Lemma F_490a8 : fetch_word AsanUbsan.M.loaded_segments (0x490a8 : word) = Some W_490a8.
Proof. vm_refl. Qed.
Lemma D_490a8 : decode_any W_490a8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490ac : bv 32 := 0x064000ef.
Lemma F_490ac : fetch_word AsanUbsan.M.loaded_segments (0x490ac : word) = Some W_490ac.
Proof. vm_refl. Qed.
Lemma D_490ac : decode_any W_490ac = Some (Jal 1 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_490b0 : bv 32 := 0x00050593.
Lemma F_490b0 : fetch_word AsanUbsan.M.loaded_segments (0x490b0 : word) = Some W_490b0.
Proof. vm_refl. Qed.
Lemma D_490b0 : decode_any W_490b0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490b4 : bv 32 := 0x00048513.
Lemma F_490b4 : fetch_word AsanUbsan.M.loaded_segments (0x490b4 : word) = Some W_490b4.
Proof. vm_refl. Qed.
Lemma D_490b4 : decode_any W_490b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490b8 : bv 32 := 0x00000613.
Lemma F_490b8 : fetch_word AsanUbsan.M.loaded_segments (0x490b8 : word) = Some W_490b8.
Proof. vm_refl. Qed.
Lemma D_490b8 : decode_any W_490b8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490bc : bv 32 := 0x0005b023.
Lemma F_490bc : fetch_word AsanUbsan.M.loaded_segments (0x490bc : word) = Some W_490bc.
Proof. vm_refl. Qed.
Lemma D_490bc : decode_any W_490bc = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490c0 : bv 32 := 0x0005b423.
Lemma F_490c0 : fetch_word AsanUbsan.M.loaded_segments (0x490c0 : word) = Some W_490c0.
Proof. vm_refl. Qed.
Lemma D_490c0 : decode_any W_490c0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_490c4 : bv 32 := 0x0005b823.
Lemma F_490c4 : fetch_word AsanUbsan.M.loaded_segments (0x490c4 : word) = Some W_490c4.
Proof. vm_refl. Qed.
Lemma D_490c4 : decode_any W_490c4 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_490c8 : bv 32 := 0x0005bc23.
Lemma F_490c8 : fetch_word AsanUbsan.M.loaded_segments (0x490c8 : word) = Some W_490c8.
Proof. vm_refl. Qed.
Lemma D_490c8 : decode_any W_490c8 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_490cc : bv 32 := 0x0205b023.
Lemma F_490cc : fetch_word AsanUbsan.M.loaded_segments (0x490cc : word) = Some W_490cc.
Proof. vm_refl. Qed.
Lemma D_490cc : decode_any W_490cc = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_490d0 : bv 32 := 0x0205b423.
Lemma F_490d0 : fetch_word AsanUbsan.M.loaded_segments (0x490d0 : word) = Some W_490d0.
Proof. vm_refl. Qed.
Lemma D_490d0 : decode_any W_490d0 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_490d4 : bv 32 := 0x0205b823.
Lemma F_490d4 : fetch_word AsanUbsan.M.loaded_segments (0x490d4 : word) = Some W_490d4.
Proof. vm_refl. Qed.
Lemma D_490d4 : decode_any W_490d4 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_490d8 : bv 32 := 0x0205bc23.
Lemma F_490d8 : fetch_word AsanUbsan.M.loaded_segments (0x490d8 : word) = Some W_490d8.
Proof. vm_refl. Qed.
Lemma D_490d8 : decode_any W_490d8 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_490dc : bv 32 := 0x01813083.
Lemma F_490dc : fetch_word AsanUbsan.M.loaded_segments (0x490dc : word) = Some W_490dc.
Proof. vm_refl. Qed.
Lemma D_490dc : decode_any W_490dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_490e0 : bv 32 := 0x01013403.
Lemma F_490e0 : fetch_word AsanUbsan.M.loaded_segments (0x490e0 : word) = Some W_490e0.
Proof. vm_refl. Qed.
Lemma D_490e0 : decode_any W_490e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_490e4 : bv 32 := 0x00813483.
Lemma F_490e4 : fetch_word AsanUbsan.M.loaded_segments (0x490e4 : word) = Some W_490e4.
Proof. vm_refl. Qed.
Lemma D_490e4 : decode_any W_490e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_490e8 : bv 32 := 0x00013903.
Lemma F_490e8 : fetch_word AsanUbsan.M.loaded_segments (0x490e8 : word) = Some W_490e8.
Proof. vm_refl. Qed.
Lemma D_490e8 : decode_any W_490e8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490ec : bv 32 := 0x02010113.
Lemma F_490ec : fetch_word AsanUbsan.M.loaded_segments (0x490ec : word) = Some W_490ec.
Proof. vm_refl. Qed.
Lemma D_490ec : decode_any W_490ec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_490f0 : bv 32 := 0x00008067.
Lemma F_490f0 : fetch_word AsanUbsan.M.loaded_segments (0x490f0 : word) = Some W_490f0.
Proof. vm_refl. Qed.
Lemma D_490f0 : decode_any W_490f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_490f4 : bv 32 := 0x04853483.
Lemma F_490f4 : fetch_word AsanUbsan.M.loaded_segments (0x490f4 : word) = Some W_490f4.
Proof. vm_refl. Qed.
Lemma D_490f4 : decode_any W_490f4 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_490f8 : bv 32 := 0x00100593.
Lemma F_490f8 : fetch_word AsanUbsan.M.loaded_segments (0x490f8 : word) = Some W_490f8.
Proof. vm_refl. Qed.
Lemma D_490f8 : decode_any W_490f8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_490fc : bv 32 := 0x0095e663.
Lemma F_490fc : fetch_word AsanUbsan.M.loaded_segments (0x490fc : word) = Some W_490fc.
Proof. vm_refl. Qed.
Lemma D_490fc : decode_any W_490fc = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_49100 : bv 32 := 0x3d9200ef.
Lemma F_49100 : fetch_word AsanUbsan.M.loaded_segments (0x49100 : word) = Some W_49100.
Proof. vm_refl. Qed.
Lemma D_49100 : decode_any W_49100 = Some (Jal 1 134104, 4%Z).
Proof. vm_refl. Qed.

Definition W_49104 : bv 32 := 0x00050493.
Lemma F_49104 : fetch_word AsanUbsan.M.loaded_segments (0x49104 : word) = Some W_49104.
Proof. vm_refl. Qed.
Lemma D_49104 : decode_any W_49104 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49108 : bv 32 := 0xe80494e3.
Lemma F_49108 : fetch_word AsanUbsan.M.loaded_segments (0x49108 : word) = Some W_49108.
Proof. vm_refl. Qed.
Lemma D_49108 : decode_any W_49108 = Some (Branch BC_NE 9 0 7816, 4%Z).
Proof. vm_refl. Qed.

Definition W_4910c : bv 32 := 0xf31ff06f.
Lemma F_4910c : fetch_word AsanUbsan.M.loaded_segments (0x4910c : word) = Some W_4910c.
Proof. vm_refl. Qed.
Lemma D_4910c : decode_any W_4910c = Some (Jal 0 2096944, 4%Z).
Proof. vm_refl. Qed.

Definition W_49110 : bv 32 := 0x0008d597.
Lemma F_49110 : fetch_word AsanUbsan.M.loaded_segments (0x49110 : word) = Some W_49110.
Proof. vm_refl. Qed.
Lemma D_49110 : decode_any W_49110 = Some (Auipc 11 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_49114 : bv 32 := 0x3b85b583.
Lemma F_49114 : fetch_word AsanUbsan.M.loaded_segments (0x49114 : word) = Some W_49114.
Proof. vm_refl. Qed.
Lemma D_49114 : decode_any W_49114 = Some (Load SZ8 true 11 11 952, 4%Z).
Proof. vm_refl. Qed.

Definition W_49118 : bv 32 := 0x0005b583.
Lemma F_49118 : fetch_word AsanUbsan.M.loaded_segments (0x49118 : word) = Some W_49118.
Proof. vm_refl. Qed.
Lemma D_49118 : decode_any W_49118 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4911c : bv 32 := 0xfff58613.
Lemma F_4911c : fetch_word AsanUbsan.M.loaded_segments (0x4911c : word) = Some W_4911c.
Proof. vm_refl. Qed.
Lemma D_4911c : decode_any W_4911c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_49120 : bv 32 := 0x00c5b6b3.
Lemma F_49120 : fetch_word AsanUbsan.M.loaded_segments (0x49120 : word) = Some W_49120.
Proof. vm_refl. Qed.
Lemma D_49120 : decode_any W_49120 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_49124 : bv 32 := 0xfff68693.
Lemma F_49124 : fetch_word AsanUbsan.M.loaded_segments (0x49124 : word) = Some W_49124.
Proof. vm_refl. Qed.
Lemma D_49124 : decode_any W_49124 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_49128 : bv 32 := 0x00c6f6b3.
Lemma F_49128 : fetch_word AsanUbsan.M.loaded_segments (0x49128 : word) = Some W_49128.
Proof. vm_refl. Qed.
Lemma D_49128 : decode_any W_49128 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4912c : bv 32 := 0x04a6f263.
Lemma F_4912c : fetch_word AsanUbsan.M.loaded_segments (0x4912c : word) = Some W_4912c.
Proof. vm_refl. Qed.
Lemma D_4912c : decode_any W_4912c = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_49130 : bv 32 := 0x0008d697.
Lemma F_49130 : fetch_word AsanUbsan.M.loaded_segments (0x49130 : word) = Some W_49130.
Proof. vm_refl. Qed.
Lemma D_49130 : decode_any W_49130 = Some (Auipc 13 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_49134 : bv 32 := 0x3a06b683.
Lemma F_49134 : fetch_word AsanUbsan.M.loaded_segments (0x49134 : word) = Some W_49134.
Proof. vm_refl. Qed.
Lemma D_49134 : decode_any W_49134 = Some (Load SZ8 true 13 13 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_49138 : bv 32 := 0x0008d717.
Lemma F_49138 : fetch_word AsanUbsan.M.loaded_segments (0x49138 : word) = Some W_49138.
Proof. vm_refl. Qed.
Lemma D_49138 : decode_any W_49138 = Some (Auipc 14 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_4913c : bv 32 := 0x3a073703.
Lemma F_4913c : fetch_word AsanUbsan.M.loaded_segments (0x4913c : word) = Some W_4913c.
Proof. vm_refl. Qed.
Lemma D_4913c : decode_any W_4913c = Some (Load SZ8 true 14 14 928, 4%Z).
Proof. vm_refl. Qed.

Definition W_49140 : bv 32 := 0x0006b803.
Lemma F_49140 : fetch_word AsanUbsan.M.loaded_segments (0x49140 : word) = Some W_49140.
Proof. vm_refl. Qed.
Lemma D_49140 : decode_any W_49140 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49144 : bv 32 := 0x00073683.
Lemma F_49144 : fetch_word AsanUbsan.M.loaded_segments (0x49144 : word) = Some W_49144.
Proof. vm_refl. Qed.
Lemma D_49144 : decode_any W_49144 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49148 : bv 32 := 0xfff80793.
Lemma F_49148 : fetch_word AsanUbsan.M.loaded_segments (0x49148 : word) = Some W_49148.
Proof. vm_refl. Qed.
Lemma D_49148 : decode_any W_49148 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4914c : bv 32 := 0x00a7f463.
Lemma F_4914c : fetch_word AsanUbsan.M.loaded_segments (0x4914c : word) = Some W_4914c.
Proof. vm_refl. Qed.
Lemma D_4914c : decode_any W_4914c = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_49150 : bv 32 := 0x02a6f063.
Lemma F_49150 : fetch_word AsanUbsan.M.loaded_segments (0x49150 : word) = Some W_49150.
Proof. vm_refl. Qed.
Lemma D_49150 : decode_any W_49150 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_49154 : bv 32 := 0x0008d717.
Lemma F_49154 : fetch_word AsanUbsan.M.loaded_segments (0x49154 : word) = Some W_49154.
Proof. vm_refl. Qed.
Lemma D_49154 : decode_any W_49154 = Some (Auipc 14 141, 4%Z).
Proof. vm_refl. Qed.

Definition W_49158 : bv 32 := 0x38c73703.
Lemma F_49158 : fetch_word AsanUbsan.M.loaded_segments (0x49158 : word) = Some W_49158.
Proof. vm_refl. Qed.
Lemma D_49158 : decode_any W_49158 = Some (Load SZ8 true 14 14 908, 4%Z).
Proof. vm_refl. Qed.

Definition W_4915c : bv 32 := 0x00073283.
Lemma F_4915c : fetch_word AsanUbsan.M.loaded_segments (0x4915c : word) = Some W_4915c.
Proof. vm_refl. Qed.
Lemma D_4915c : decode_any W_4915c = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_49160 : bv 32 := 0x0032d713.
Lemma F_49160 : fetch_word AsanUbsan.M.loaded_segments (0x49160 : word) = Some W_49160.
Proof. vm_refl. Qed.
Lemma D_49160 : decode_any W_49160 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_49164 : bv 32 := 0x00b708b3.
Lemma F_49164 : fetch_word AsanUbsan.M.loaded_segments (0x49164 : word) = Some W_49164.
Proof. vm_refl. Qed.
Lemma D_49164 : decode_any W_49164 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_49168 : bv 32 := 0x00a2ea63.
Lemma F_49168 : fetch_word AsanUbsan.M.loaded_segments (0x49168 : word) = Some W_49168.
Proof. vm_refl. Qed.
Lemma D_49168 : decode_any W_49168 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4916c : bv 32 := 0x00a8f863.
Lemma F_4916c : fetch_word AsanUbsan.M.loaded_segments (0x4916c : word) = Some W_4916c.
Proof. vm_refl. Qed.
Lemma D_4916c : decode_any W_4916c = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_49170 : bv 32 := 0x00355513.
Lemma F_49170 : fetch_word AsanUbsan.M.loaded_segments (0x49170 : word) = Some W_49170.
Proof. vm_refl. Qed.
Lemma D_49170 : decode_any W_49170 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_49174 : bv 32 := 0x00a58533.
Lemma F_49174 : fetch_word AsanUbsan.M.loaded_segments (0x49174 : word) = Some W_49174.
Proof. vm_refl. Qed.
Lemma D_49174 : decode_any W_49174 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_49178 : bv 32 := 0x00008067.
Lemma F_49178 : fetch_word AsanUbsan.M.loaded_segments (0x49178 : word) = Some W_49178.
Proof. vm_refl. Qed.
Lemma D_49178 : decode_any W_49178 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
