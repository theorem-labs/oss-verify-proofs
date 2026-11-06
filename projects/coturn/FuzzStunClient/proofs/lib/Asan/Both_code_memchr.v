(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a26ec : bv 32 := 0x0ff5f593.
Lemma F_a26ec : fetch_word AsanUbsan.M.loaded_segments (0xa26ec : word) = Some W_a26ec.
Proof. vm_refl. Qed.
Lemma D_a26ec : decode_any W_a26ec = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f0 : bv 32 := 0x00757693.
Lemma F_a26f0 : fetch_word AsanUbsan.M.loaded_segments (0xa26f0 : word) = Some W_a26f0.
Proof. vm_refl. Qed.
Lemma D_a26f0 : decode_any W_a26f0 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f4 : bv 32 := 0x00c03733.
Lemma F_a26f4 : fetch_word AsanUbsan.M.loaded_segments (0xa26f4 : word) = Some W_a26f4.
Proof. vm_refl. Qed.
Lemma D_a26f4 : decode_any W_a26f4 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26f8 : bv 32 := 0x02068c63.
Lemma F_a26f8 : fetch_word AsanUbsan.M.loaded_segments (0xa26f8 : word) = Some W_a26f8.
Proof. vm_refl. Qed.
Lemma D_a26f8 : decode_any W_a26f8 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26fc : bv 32 := 0x02060a63.
Lemma F_a26fc : fetch_word AsanUbsan.M.loaded_segments (0xa26fc : word) = Some W_a26fc.
Proof. vm_refl. Qed.
Lemma D_a26fc : decode_any W_a26fc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2700 : bv 32 := 0x00150793.
Lemma F_a2700 : fetch_word AsanUbsan.M.loaded_segments (0xa2700 : word) = Some W_a2700.
Proof. vm_refl. Qed.
Lemma D_a2700 : decode_any W_a2700 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2704 : bv 32 := 0x00100813.
Lemma F_a2704 : fetch_word AsanUbsan.M.loaded_segments (0xa2704 : word) = Some W_a2704.
Proof. vm_refl. Qed.
Lemma D_a2704 : decode_any W_a2704 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2708 : bv 32 := 0x00054703.
Lemma F_a2708 : fetch_word AsanUbsan.M.loaded_segments (0xa2708 : word) = Some W_a2708.
Proof. vm_refl. Qed.
Lemma D_a2708 : decode_any W_a2708 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a270c : bv 32 := 0x00060693.
Lemma F_a270c : fetch_word AsanUbsan.M.loaded_segments (0xa270c : word) = Some W_a270c.
Proof. vm_refl. Qed.
Lemma D_a270c : decode_any W_a270c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2710 : bv 32 := 0x06b70e63.
Lemma F_a2710 : fetch_word AsanUbsan.M.loaded_segments (0xa2710 : word) = Some W_a2710.
Proof. vm_refl. Qed.
Lemma D_a2710 : decode_any W_a2710 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2714 : bv 32 := 0x00150513.
Lemma F_a2714 : fetch_word AsanUbsan.M.loaded_segments (0xa2714 : word) = Some W_a2714.
Proof. vm_refl. Qed.
Lemma D_a2714 : decode_any W_a2714 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2718 : bv 32 := 0xfff68613.
Lemma F_a2718 : fetch_word AsanUbsan.M.loaded_segments (0xa2718 : word) = Some W_a2718.
Proof. vm_refl. Qed.
Lemma D_a2718 : decode_any W_a2718 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a271c : bv 32 := 0x0077f893.
Lemma F_a271c : fetch_word AsanUbsan.M.loaded_segments (0xa271c : word) = Some W_a271c.
Proof. vm_refl. Qed.
Lemma D_a271c : decode_any W_a271c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2720 : bv 32 := 0x00c03733.
Lemma F_a2720 : fetch_word AsanUbsan.M.loaded_segments (0xa2720 : word) = Some W_a2720.
Proof. vm_refl. Qed.
Lemma D_a2720 : decode_any W_a2720 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2724 : bv 32 := 0x00088663.
Lemma F_a2724 : fetch_word AsanUbsan.M.loaded_segments (0xa2724 : word) = Some W_a2724.
Proof. vm_refl. Qed.
Lemma D_a2724 : decode_any W_a2724 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2728 : bv 32 := 0x00178793.
Lemma F_a2728 : fetch_word AsanUbsan.M.loaded_segments (0xa2728 : word) = Some W_a2728.
Proof. vm_refl. Qed.
Lemma D_a2728 : decode_any W_a2728 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a272c : bv 32 := 0xfd069ee3.
Lemma F_a272c : fetch_word AsanUbsan.M.loaded_segments (0xa272c : word) = Some W_a272c.
Proof. vm_refl. Qed.
Lemma D_a272c : decode_any W_a272c = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2730 : bv 32 := 0x06070863.
Lemma F_a2730 : fetch_word AsanUbsan.M.loaded_segments (0xa2730 : word) = Some W_a2730.
Proof. vm_refl. Qed.
Lemma D_a2730 : decode_any W_a2730 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2734 : bv 32 := 0x00054683.
Lemma F_a2734 : fetch_word AsanUbsan.M.loaded_segments (0xa2734 : word) = Some W_a2734.
Proof. vm_refl. Qed.
Lemma D_a2734 : decode_any W_a2734 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2738 : bv 32 := 0x04b68663.
Lemma F_a2738 : fetch_word AsanUbsan.M.loaded_segments (0xa2738 : word) = Some W_a2738.
Proof. vm_refl. Qed.
Lemma D_a2738 : decode_any W_a2738 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a273c : bv 32 := 0x00800693.
Lemma F_a273c : fetch_word AsanUbsan.M.loaded_segments (0xa273c : word) = Some W_a273c.
Proof. vm_refl. Qed.
Lemma D_a273c : decode_any W_a273c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2740 : bv 32 := 0x04d66263.
Lemma F_a2740 : fetch_word AsanUbsan.M.loaded_segments (0xa2740 : word) = Some W_a2740.
Proof. vm_refl. Qed.
Lemma D_a2740 : decode_any W_a2740 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2744 : bv 32 := 0xfff6e697.
Lemma F_a2744 : fetch_word AsanUbsan.M.loaded_segments (0xa2744 : word) = Some W_a2744.
Proof. vm_refl. Qed.
Lemma D_a2744 : decode_any W_a2744 = Some (Auipc 13 1048430, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2748 : bv 32 := 0xc3c6b683.
Lemma F_a2748 : fetch_word AsanUbsan.M.loaded_segments (0xa2748 : word) = Some W_a2748.
Proof. vm_refl. Qed.
Lemma D_a2748 : decode_any W_a2748 = Some (Load SZ8 true 13 13 3132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a274c : bv 32 := 0xfff6e717.
Lemma F_a274c : fetch_word AsanUbsan.M.loaded_segments (0xa274c : word) = Some W_a274c.
Proof. vm_refl. Qed.
Lemma D_a274c : decode_any W_a274c = Some (Auipc 14 1048430, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2750 : bv 32 := 0xc1473703.
Lemma F_a2750 : fetch_word AsanUbsan.M.loaded_segments (0xa2750 : word) = Some W_a2750.
Proof. vm_refl. Qed.
Lemma D_a2750 : decode_any W_a2750 = Some (Load SZ8 true 14 14 3092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2754 : bv 32 := 0x00168793.
Lemma F_a2754 : fetch_word AsanUbsan.M.loaded_segments (0xa2754 : word) = Some W_a2754.
Proof. vm_refl. Qed.
Lemma D_a2754 : decode_any W_a2754 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2758 : bv 32 := 0x02f587b3.
Lemma F_a2758 : fetch_word AsanUbsan.M.loaded_segments (0xa2758 : word) = Some W_a2758.
Proof. vm_refl. Qed.
Lemma D_a2758 : decode_any W_a2758 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a275c : bv 32 := 0x00700813.
Lemma F_a275c : fetch_word AsanUbsan.M.loaded_segments (0xa275c : word) = Some W_a275c.
Proof. vm_refl. Qed.
Lemma D_a275c : decode_any W_a275c = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2760 : bv 32 := 0x00053883.
Lemma F_a2760 : fetch_word AsanUbsan.M.loaded_segments (0xa2760 : word) = Some W_a2760.
Proof. vm_refl. Qed.
Lemma D_a2760 : decode_any W_a2760 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2764 : bv 32 := 0x00f8c8b3.
Lemma F_a2764 : fetch_word AsanUbsan.M.loaded_segments (0xa2764 : word) = Some W_a2764.
Proof. vm_refl. Qed.
Lemma D_a2764 : decode_any W_a2764 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2768 : bv 32 := 0x411682b3.
Lemma F_a2768 : fetch_word AsanUbsan.M.loaded_segments (0xa2768 : word) = Some W_a2768.
Proof. vm_refl. Qed.
Lemma D_a2768 : decode_any W_a2768 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a276c : bv 32 := 0x0112e8b3.
Lemma F_a276c : fetch_word AsanUbsan.M.loaded_segments (0xa276c : word) = Some W_a276c.
Proof. vm_refl. Qed.
Lemma D_a276c : decode_any W_a276c = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2770 : bv 32 := 0x00e8f8b3.
Lemma F_a2770 : fetch_word AsanUbsan.M.loaded_segments (0xa2770 : word) = Some W_a2770.
Proof. vm_refl. Qed.
Lemma D_a2770 : decode_any W_a2770 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2774 : bv 32 := 0x02e89a63.
Lemma F_a2774 : fetch_word AsanUbsan.M.loaded_segments (0xa2774 : word) = Some W_a2774.
Proof. vm_refl. Qed.
Lemma D_a2774 : decode_any W_a2774 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2778 : bv 32 := 0xff860613.
Lemma F_a2778 : fetch_word AsanUbsan.M.loaded_segments (0xa2778 : word) = Some W_a2778.
Proof. vm_refl. Qed.
Lemma D_a2778 : decode_any W_a2778 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a277c : bv 32 := 0x00850513.
Lemma F_a277c : fetch_word AsanUbsan.M.loaded_segments (0xa277c : word) = Some W_a277c.
Proof. vm_refl. Qed.
Lemma D_a277c : decode_any W_a277c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2780 : bv 32 := 0xfec860e3.
Lemma F_a2780 : fetch_word AsanUbsan.M.loaded_segments (0xa2780 : word) = Some W_a2780.
Proof. vm_refl. Qed.
Lemma D_a2780 : decode_any W_a2780 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2784 : bv 32 := 0x00060693.
Lemma F_a2784 : fetch_word AsanUbsan.M.loaded_segments (0xa2784 : word) = Some W_a2784.
Proof. vm_refl. Qed.
Lemma D_a2784 : decode_any W_a2784 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2788 : bv 32 := 0x00060c63.
Lemma F_a2788 : fetch_word AsanUbsan.M.loaded_segments (0xa2788 : word) = Some W_a2788.
Proof. vm_refl. Qed.
Lemma D_a2788 : decode_any W_a2788 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a278c : bv 32 := 0x00054603.
Lemma F_a278c : fetch_word AsanUbsan.M.loaded_segments (0xa278c : word) = Some W_a278c.
Proof. vm_refl. Qed.
Lemma D_a278c : decode_any W_a278c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2790 : bv 32 := 0x00b60a63.
Lemma F_a2790 : fetch_word AsanUbsan.M.loaded_segments (0xa2790 : word) = Some W_a2790.
Proof. vm_refl. Qed.
Lemma D_a2790 : decode_any W_a2790 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2794 : bv 32 := 0xfff68693.
Lemma F_a2794 : fetch_word AsanUbsan.M.loaded_segments (0xa2794 : word) = Some W_a2794.
Proof. vm_refl. Qed.
Lemma D_a2794 : decode_any W_a2794 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2798 : bv 32 := 0x00150513.
Lemma F_a2798 : fetch_word AsanUbsan.M.loaded_segments (0xa2798 : word) = Some W_a2798.
Proof. vm_refl. Qed.
Lemma D_a2798 : decode_any W_a2798 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a279c : bv 32 := 0xfe0698e3.
Lemma F_a279c : fetch_word AsanUbsan.M.loaded_segments (0xa279c : word) = Some W_a279c.
Proof. vm_refl. Qed.
Lemma D_a279c : decode_any W_a279c = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27a0 : bv 32 := 0x00000513.
Lemma F_a27a0 : fetch_word AsanUbsan.M.loaded_segments (0xa27a0 : word) = Some W_a27a0.
Proof. vm_refl. Qed.
Lemma D_a27a0 : decode_any W_a27a0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27a4 : bv 32 := 0x00008067.
Lemma F_a27a4 : fetch_word AsanUbsan.M.loaded_segments (0xa27a4 : word) = Some W_a27a4.
Proof. vm_refl. Qed.
Lemma D_a27a4 : decode_any W_a27a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27a8 : bv 32 := 0x00060693.
Lemma F_a27a8 : fetch_word AsanUbsan.M.loaded_segments (0xa27a8 : word) = Some W_a27a8.
Proof. vm_refl. Qed.
Lemma D_a27a8 : decode_any W_a27a8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27ac : bv 32 := 0x00054603.
Lemma F_a27ac : fetch_word AsanUbsan.M.loaded_segments (0xa27ac : word) = Some W_a27ac.
Proof. vm_refl. Qed.
Lemma D_a27ac : decode_any W_a27ac = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27b0 : bv 32 := 0xfeb612e3.
Lemma F_a27b0 : fetch_word AsanUbsan.M.loaded_segments (0xa27b0 : word) = Some W_a27b0.
Proof. vm_refl. Qed.
Lemma D_a27b0 : decode_any W_a27b0 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27b4 : bv 32 := 0xff1ff06f.
Lemma F_a27b4 : fetch_word AsanUbsan.M.loaded_segments (0xa27b4 : word) = Some W_a27b4.
Proof. vm_refl. Qed.
Lemma D_a27b4 : decode_any W_a27b4 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3074 : bv 32 := 0xfe010113.
Lemma F_a3074 : fetch_word AsanUbsan.M.loaded_segments (0xa3074 : word) = Some W_a3074.
Proof. vm_refl. Qed.
Lemma D_a3074 : decode_any W_a3074 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3078 : bv 32 := 0x00113c23.
Lemma F_a3078 : fetch_word AsanUbsan.M.loaded_segments (0xa3078 : word) = Some W_a3078.
Proof. vm_refl. Qed.
Lemma D_a3078 : decode_any W_a3078 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a307c : bv 32 := 0x00813823.
Lemma F_a307c : fetch_word AsanUbsan.M.loaded_segments (0xa307c : word) = Some W_a307c.
Proof. vm_refl. Qed.
Lemma D_a307c : decode_any W_a307c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3080 : bv 32 := 0x00913423.
Lemma F_a3080 : fetch_word AsanUbsan.M.loaded_segments (0xa3080 : word) = Some W_a3080.
Proof. vm_refl. Qed.
Lemma D_a3080 : decode_any W_a3080 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3084 : bv 32 := 0x00058413.
Lemma F_a3084 : fetch_word AsanUbsan.M.loaded_segments (0xa3084 : word) = Some W_a3084.
Proof. vm_refl. Qed.
Lemma D_a3084 : decode_any W_a3084 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3088 : bv 32 := 0x00050493.
Lemma F_a3088 : fetch_word AsanUbsan.M.loaded_segments (0xa3088 : word) = Some W_a3088.
Proof. vm_refl. Qed.
Lemma D_a3088 : decode_any W_a3088 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a308c : bv 32 := 0x00000593.
Lemma F_a308c : fetch_word AsanUbsan.M.loaded_segments (0xa308c : word) = Some W_a308c.
Proof. vm_refl. Qed.
Lemma D_a308c : decode_any W_a308c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3090 : bv 32 := 0x00040613.
Lemma F_a3090 : fetch_word AsanUbsan.M.loaded_segments (0xa3090 : word) = Some W_a3090.
Proof. vm_refl. Qed.
Lemma D_a3090 : decode_any W_a3090 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3094 : bv 32 := 0x9a4a10ef.
Lemma F_a3094 : fetch_word AsanUbsan.M.loaded_segments (0xa3094 : word) = Some W_a3094.
Proof. vm_refl. Qed.
Lemma D_a3094 : decode_any W_a3094 = Some (Jal 1 1708452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3098 : bv 32 := 0x00050463.
Lemma F_a3098 : fetch_word AsanUbsan.M.loaded_segments (0xa3098 : word) = Some W_a3098.
Proof. vm_refl. Qed.
Lemma D_a3098 : decode_any W_a3098 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a309c : bv 32 := 0x40950433.
Lemma F_a309c : fetch_word AsanUbsan.M.loaded_segments (0xa309c : word) = Some W_a309c.
Proof. vm_refl. Qed.
Lemma D_a309c : decode_any W_a309c = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30a0 : bv 32 := 0x00040513.
Lemma F_a30a0 : fetch_word AsanUbsan.M.loaded_segments (0xa30a0 : word) = Some W_a30a0.
Proof. vm_refl. Qed.
Lemma D_a30a0 : decode_any W_a30a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30a4 : bv 32 := 0x01813083.
Lemma F_a30a4 : fetch_word AsanUbsan.M.loaded_segments (0xa30a4 : word) = Some W_a30a4.
Proof. vm_refl. Qed.
Lemma D_a30a4 : decode_any W_a30a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30a8 : bv 32 := 0x01013403.
Lemma F_a30a8 : fetch_word AsanUbsan.M.loaded_segments (0xa30a8 : word) = Some W_a30a8.
Proof. vm_refl. Qed.
Lemma D_a30a8 : decode_any W_a30a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30ac : bv 32 := 0x00813483.
Lemma F_a30ac : fetch_word AsanUbsan.M.loaded_segments (0xa30ac : word) = Some W_a30ac.
Proof. vm_refl. Qed.
Lemma D_a30ac : decode_any W_a30ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30b0 : bv 32 := 0x02010113.
Lemma F_a30b0 : fetch_word AsanUbsan.M.loaded_segments (0xa30b0 : word) = Some W_a30b0.
Proof. vm_refl. Qed.
Lemma D_a30b0 : decode_any W_a30b0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30b4 : bv 32 := 0x00008067.
Lemma F_a30b4 : fetch_word AsanUbsan.M.loaded_segments (0xa30b4 : word) = Some W_a30b4.
Proof. vm_refl. Qed.
Lemma D_a30b4 : decode_any W_a30b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
