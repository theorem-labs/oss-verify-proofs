(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c2654 : bv 32 := 0xf9010113.
Lemma F_c2654 : fetch_word Ubsan.M.loaded_segments (0xc280c : word) = Some W_c2654.
Proof. vm_refl. Qed.
Lemma D_c2654 : decode_any W_c2654 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2658 : bv 32 := 0x06113423.
Lemma F_c2658 : fetch_word Ubsan.M.loaded_segments (0xc2810 : word) = Some W_c2658.
Proof. vm_refl. Qed.
Lemma D_c2658 : decode_any W_c2658 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c265c : bv 32 := 0x06813023.
Lemma F_c265c : fetch_word Ubsan.M.loaded_segments (0xc2814 : word) = Some W_c265c.
Proof. vm_refl. Qed.
Lemma D_c265c : decode_any W_c265c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2660 : bv 32 := 0x04913c23.
Lemma F_c2660 : fetch_word Ubsan.M.loaded_segments (0xc2818 : word) = Some W_c2660.
Proof. vm_refl. Qed.
Lemma D_c2660 : decode_any W_c2660 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2664 : bv 32 := 0x05213823.
Lemma F_c2664 : fetch_word Ubsan.M.loaded_segments (0xc281c : word) = Some W_c2664.
Proof. vm_refl. Qed.
Lemma D_c2664 : decode_any W_c2664 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2668 : bv 32 := 0x05313423.
Lemma F_c2668 : fetch_word Ubsan.M.loaded_segments (0xc2820 : word) = Some W_c2668.
Proof. vm_refl. Qed.
Lemma D_c2668 : decode_any W_c2668 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c266c : bv 32 := 0x05413023.
Lemma F_c266c : fetch_word Ubsan.M.loaded_segments (0xc2824 : word) = Some W_c266c.
Proof. vm_refl. Qed.
Lemma D_c266c : decode_any W_c266c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2670 : bv 32 := 0x03513c23.
Lemma F_c2670 : fetch_word Ubsan.M.loaded_segments (0xc2828 : word) = Some W_c2670.
Proof. vm_refl. Qed.
Lemma D_c2670 : decode_any W_c2670 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2674 : bv 32 := 0x03613823.
Lemma F_c2674 : fetch_word Ubsan.M.loaded_segments (0xc282c : word) = Some W_c2674.
Proof. vm_refl. Qed.
Lemma D_c2674 : decode_any W_c2674 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2678 : bv 32 := 0x00060413.
Lemma F_c2678 : fetch_word Ubsan.M.loaded_segments (0xc2830 : word) = Some W_c2678.
Proof. vm_refl. Qed.
Lemma D_c2678 : decode_any W_c2678 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c267c : bv 32 := 0x00050493.
Lemma F_c267c : fetch_word Ubsan.M.loaded_segments (0xc2834 : word) = Some W_c267c.
Proof. vm_refl. Qed.
Lemma D_c267c : decode_any W_c267c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2680 : bv 32 := 0x00018517.
Lemma F_c2680 : fetch_word Ubsan.M.loaded_segments (0xc2838 : word) = Some W_c2680.
Proof. vm_refl. Qed.
Lemma D_c2680 : decode_any W_c2680 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2684 : bv 32 := 0x83053a83.
Lemma F_c2684 : fetch_word Ubsan.M.loaded_segments (0xc283c : word) = Some W_c2684.
Proof. vm_refl. Qed.
Lemma D_c2684 : decode_any W_c2684 = Some (Load SZ8 true 21 10 2096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2688 : bv 32 := 0x000ab503.
Lemma F_c2688 : fetch_word Ubsan.M.loaded_segments (0xc2840 : word) = Some W_c2688.
Proof. vm_refl. Qed.
Lemma D_c2688 : decode_any W_c2688 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c268c : bv 32 := 0x02a13423.
Lemma F_c268c : fetch_word Ubsan.M.loaded_segments (0xc2844 : word) = Some W_c268c.
Proof. vm_refl. Qed.
Lemma D_c268c : decode_any W_c268c = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2690 : bv 32 := 0x0284b503.
Lemma F_c2690 : fetch_word Ubsan.M.loaded_segments (0xc2848 : word) = Some W_c2690.
Proof. vm_refl. Qed.
Lemma D_c2690 : decode_any W_c2690 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2694 : bv 32 := 0x0384b603.
Lemma F_c2694 : fetch_word Ubsan.M.loaded_segments (0xc284c : word) = Some W_c2694.
Proof. vm_refl. Qed.
Lemma D_c2694 : decode_any W_c2694 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2698 : bv 32 := 0x40c50b33.
Lemma F_c2698 : fetch_word Ubsan.M.loaded_segments (0xc2850 : word) = Some W_c2698.
Proof. vm_refl. Qed.
Lemma D_c2698 : decode_any W_c2698 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c269c : bv 32 := 0x00c546b3.
Lemma F_c269c : fetch_word Ubsan.M.loaded_segments (0xc2854 : word) = Some W_c269c.
Proof. vm_refl. Qed.
Lemma D_c269c : decode_any W_c269c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26a0 : bv 32 := 0x00c13423.
Lemma F_c26a0 : fetch_word Ubsan.M.loaded_segments (0xc2858 : word) = Some W_c26a0.
Proof. vm_refl. Qed.
Lemma D_c26a0 : decode_any W_c26a0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26a4 : bv 32 := 0x01613823.
Lemma F_c26a4 : fetch_word Ubsan.M.loaded_segments (0xc285c : word) = Some W_c26a4.
Proof. vm_refl. Qed.
Lemma D_c26a4 : decode_any W_c26a4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26a8 : bv 32 := 0x00b13c23.
Lemma F_c26a8 : fetch_word Ubsan.M.loaded_segments (0xc2860 : word) = Some W_c26a8.
Proof. vm_refl. Qed.
Lemma D_c26a8 : decode_any W_c26a8 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26ac : bv 32 := 0x02813023.
Lemma F_c26ac : fetch_word Ubsan.M.loaded_segments (0xc2864 : word) = Some W_c26ac.
Proof. vm_refl. Qed.
Lemma D_c26ac : decode_any W_c26ac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26b0 : bv 32 := 0x008b0b33.
Lemma F_c26b0 : fetch_word Ubsan.M.loaded_segments (0xc2868 : word) = Some W_c26b0.
Proof. vm_refl. Qed.
Lemma D_c26b0 : decode_any W_c26b0 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26b4 : bv 32 := 0x00d03933.
Lemma F_c26b4 : fetch_word Ubsan.M.loaded_segments (0xc286c : word) = Some W_c26b4.
Proof. vm_refl. Qed.
Lemma D_c26b4 : decode_any W_c26b4 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26b8 : bv 32 := 0x00c50663.
Lemma F_c26b8 : fetch_word Ubsan.M.loaded_segments (0xc2870 : word) = Some W_c26b8.
Proof. vm_refl. Qed.
Lemma D_c26b8 : decode_any W_c26b8 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26bc : bv 32 := 0x00810993.
Lemma F_c26bc : fetch_word Ubsan.M.loaded_segments (0xc2874 : word) = Some W_c26bc.
Proof. vm_refl. Qed.
Lemma D_c26bc : decode_any W_c26bc = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26c0 : bv 32 := 0x0080006f.
Lemma F_c26c0 : fetch_word Ubsan.M.loaded_segments (0xc2878 : word) = Some W_c26c0.
Proof. vm_refl. Qed.
Lemma D_c26c0 : decode_any W_c26c0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26c4 : bv 32 := 0x01810993.
Lemma F_c26c4 : fetch_word Ubsan.M.loaded_segments (0xc287c : word) = Some W_c26c4.
Proof. vm_refl. Qed.
Lemma D_c26c4 : decode_any W_c26c4 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26c8 : bv 32 := 0x0784a503.
Lemma F_c26c8 : fetch_word Ubsan.M.loaded_segments (0xc2880 : word) = Some W_c26c8.
Proof. vm_refl. Qed.
Lemma D_c26c8 : decode_any W_c26c8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26cc : bv 32 := 0x00190913.
Lemma F_c26cc : fetch_word Ubsan.M.loaded_segments (0xc2884 : word) = Some W_c26cc.
Proof. vm_refl. Qed.
Lemma D_c26cc : decode_any W_c26cc = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26d0 : bv 32 := 0x04200893.
Lemma F_c26d0 : fetch_word Ubsan.M.loaded_segments (0xc2888 : word) = Some W_c26d0.
Proof. vm_refl. Qed.
Lemma D_c26d0 : decode_any W_c26d0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26d4 : bv 32 := 0x00098593.
Lemma F_c26d4 : fetch_word Ubsan.M.loaded_segments (0xc288c : word) = Some W_c26d4.
Proof. vm_refl. Qed.
Lemma D_c26d4 : decode_any W_c26d4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26d8 : bv 32 := 0x00090613.
Lemma F_c26d8 : fetch_word Ubsan.M.loaded_segments (0xc2890 : word) = Some W_c26d8.
Proof. vm_refl. Qed.
Lemma D_c26d8 : decode_any W_c26d8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26dc : bv 32 := 0x00000073.
Lemma F_c26dc : fetch_word Ubsan.M.loaded_segments (0xc2894 : word) = Some W_c26dc.
Proof. vm_refl. Qed.
Lemma D_c26dc : decode_any W_c26dc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_c26dc : is_ecall W_c26dc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_c26e0 : bv 32 := 0xeb5fa0ef.
Lemma F_c26e0 : fetch_word Ubsan.M.loaded_segments (0xc2898 : word) = Some W_c26e0.
Proof. vm_refl. Qed.
Lemma D_c26e0 : decode_any W_c26e0 = Some (Jal 1 2076340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26e4 : bv 32 := 0x09651863.
Lemma F_c26e4 : fetch_word Ubsan.M.loaded_segments (0xc289c : word) = Some W_c26e4.
Proof. vm_refl. Qed.
Lemma D_c26e4 : decode_any W_c26e4 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26e8 : bv 32 := 0x0584b503.
Lemma F_c26e8 : fetch_word Ubsan.M.loaded_segments (0xc28a0 : word) = Some W_c26e8.
Proof. vm_refl. Qed.
Lemma D_c26e8 : decode_any W_c26e8 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26ec : bv 32 := 0x0604b583.
Lemma F_c26ec : fetch_word Ubsan.M.loaded_segments (0xc28a4 : word) = Some W_c26ec.
Proof. vm_refl. Qed.
Lemma D_c26ec : decode_any W_c26ec = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26f0 : bv 32 := 0x00b505b3.
Lemma F_c26f0 : fetch_word Ubsan.M.loaded_segments (0xc28a8 : word) = Some W_c26f0.
Proof. vm_refl. Qed.
Lemma D_c26f0 : decode_any W_c26f0 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26f4 : bv 32 := 0x02b4b023.
Lemma F_c26f4 : fetch_word Ubsan.M.loaded_segments (0xc28ac : word) = Some W_c26f4.
Proof. vm_refl. Qed.
Lemma D_c26f4 : decode_any W_c26f4 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26f8 : bv 32 := 0x02a4b423.
Lemma F_c26f8 : fetch_word Ubsan.M.loaded_segments (0xc28b0 : word) = Some W_c26f8.
Proof. vm_refl. Qed.
Lemma D_c26f8 : decode_any W_c26f8 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c26fc : bv 32 := 0x02a4bc23.
Lemma F_c26fc : fetch_word Ubsan.M.loaded_segments (0xc28b4 : word) = Some W_c26fc.
Proof. vm_refl. Qed.
Lemma D_c26fc : decode_any W_c26fc = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2700 : bv 32 := 0x00040513.
Lemma F_c2700 : fetch_word Ubsan.M.loaded_segments (0xc28b8 : word) = Some W_c2700.
Proof. vm_refl. Qed.
Lemma D_c2700 : decode_any W_c2700 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2704 : bv 32 := 0x000ab583.
Lemma F_c2704 : fetch_word Ubsan.M.loaded_segments (0xc28bc : word) = Some W_c2704.
Proof. vm_refl. Qed.
Lemma D_c2704 : decode_any W_c2704 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2708 : bv 32 := 0x02813603.
Lemma F_c2708 : fetch_word Ubsan.M.loaded_segments (0xc28c0 : word) = Some W_c2708.
Proof. vm_refl. Qed.
Lemma D_c2708 : decode_any W_c2708 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c270c : bv 32 := 0x0cc59a63.
Lemma F_c270c : fetch_word Ubsan.M.loaded_segments (0xc28c4 : word) = Some W_c270c.
Proof. vm_refl. Qed.
Lemma D_c270c : decode_any W_c270c = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2710 : bv 32 := 0x06813083.
Lemma F_c2710 : fetch_word Ubsan.M.loaded_segments (0xc28c8 : word) = Some W_c2710.
Proof. vm_refl. Qed.
Lemma D_c2710 : decode_any W_c2710 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2714 : bv 32 := 0x06013403.
Lemma F_c2714 : fetch_word Ubsan.M.loaded_segments (0xc28cc : word) = Some W_c2714.
Proof. vm_refl. Qed.
Lemma D_c2714 : decode_any W_c2714 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2718 : bv 32 := 0x05813483.
Lemma F_c2718 : fetch_word Ubsan.M.loaded_segments (0xc28d0 : word) = Some W_c2718.
Proof. vm_refl. Qed.
Lemma D_c2718 : decode_any W_c2718 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c271c : bv 32 := 0x05013903.
Lemma F_c271c : fetch_word Ubsan.M.loaded_segments (0xc28d4 : word) = Some W_c271c.
Proof. vm_refl. Qed.
Lemma D_c271c : decode_any W_c271c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2720 : bv 32 := 0x04813983.
Lemma F_c2720 : fetch_word Ubsan.M.loaded_segments (0xc28d8 : word) = Some W_c2720.
Proof. vm_refl. Qed.
Lemma D_c2720 : decode_any W_c2720 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2724 : bv 32 := 0x04013a03.
Lemma F_c2724 : fetch_word Ubsan.M.loaded_segments (0xc28dc : word) = Some W_c2724.
Proof. vm_refl. Qed.
Lemma D_c2724 : decode_any W_c2724 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2728 : bv 32 := 0x03813a83.
Lemma F_c2728 : fetch_word Ubsan.M.loaded_segments (0xc28e0 : word) = Some W_c2728.
Proof. vm_refl. Qed.
Lemma D_c2728 : decode_any W_c2728 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c272c : bv 32 := 0x03013b03.
Lemma F_c272c : fetch_word Ubsan.M.loaded_segments (0xc28e4 : word) = Some W_c272c.
Proof. vm_refl. Qed.
Lemma D_c272c : decode_any W_c272c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2730 : bv 32 := 0x07010113.
Lemma F_c2730 : fetch_word Ubsan.M.loaded_segments (0xc28e8 : word) = Some W_c2730.
Proof. vm_refl. Qed.
Lemma D_c2730 : decode_any W_c2730 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2734 : bv 32 := 0x00008067.
Lemma F_c2734 : fetch_word Ubsan.M.loaded_segments (0xc28ec : word) = Some W_c2734.
Proof. vm_refl. Qed.
Lemma D_c2734 : decode_any W_c2734 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2738 : bv 32 := 0x00800713.
Lemma F_c2738 : fetch_word Ubsan.M.loaded_segments (0xc28f0 : word) = Some W_c2738.
Proof. vm_refl. Qed.
Lemma D_c2738 : decode_any W_c2738 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c273c : bv 32 := 0x000a0593.
Lemma F_c273c : fetch_word Ubsan.M.loaded_segments (0xc28f4 : word) = Some W_c273c.
Proof. vm_refl. Qed.
Lemma D_c273c : decode_any W_c273c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2740 : bv 32 := 0x00e98733.
Lemma F_c2740 : fetch_word Ubsan.M.loaded_segments (0xc28f8 : word) = Some W_c2740.
Proof. vm_refl. Qed.
Lemma D_c2740 : decode_any W_c2740 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2744 : bv 32 := 0x00073783.
Lemma F_c2744 : fetch_word Ubsan.M.loaded_segments (0xc28fc : word) = Some W_c2744.
Proof. vm_refl. Qed.
Lemma D_c2744 : decode_any W_c2744 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2748 : bv 32 := 0x40ab0b33.
Lemma F_c2748 : fetch_word Ubsan.M.loaded_segments (0xc2900 : word) = Some W_c2748.
Proof. vm_refl. Qed.
Lemma D_c2748 : decode_any W_c2748 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c274c : bv 32 := 0x0784a503.
Lemma F_c274c : fetch_word Ubsan.M.loaded_segments (0xc2904 : word) = Some W_c274c.
Proof. vm_refl. Qed.
Lemma D_c274c : decode_any W_c274c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2750 : bv 32 := 0x40c9093b.
Lemma F_c2750 : fetch_word Ubsan.M.loaded_segments (0xc2908 : word) = Some W_c2750.
Proof. vm_refl. Qed.
Lemma D_c2750 : decode_any W_c2750 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2754 : bv 32 := 0x40d787b3.
Lemma F_c2754 : fetch_word Ubsan.M.loaded_segments (0xc290c : word) = Some W_c2754.
Proof. vm_refl. Qed.
Lemma D_c2754 : decode_any W_c2754 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2758 : bv 32 := 0x00f73023.
Lemma F_c2758 : fetch_word Ubsan.M.loaded_segments (0xc2910 : word) = Some W_c2758.
Proof. vm_refl. Qed.
Lemma D_c2758 : decode_any W_c2758 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c275c : bv 32 := 0x04200893.
Lemma F_c275c : fetch_word Ubsan.M.loaded_segments (0xc2914 : word) = Some W_c275c.
Proof. vm_refl. Qed.
Lemma D_c275c : decode_any W_c275c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2760 : bv 32 := 0x00090613.
Lemma F_c2760 : fetch_word Ubsan.M.loaded_segments (0xc2918 : word) = Some W_c2760.
Proof. vm_refl. Qed.
Lemma D_c2760 : decode_any W_c2760 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2764 : bv 32 := 0x00000073.
Lemma F_c2764 : fetch_word Ubsan.M.loaded_segments (0xc291c : word) = Some W_c2764.
Proof. vm_refl. Qed.
Lemma D_c2764 : decode_any W_c2764 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_c2764 : is_ecall W_c2764 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_c2768 : bv 32 := 0xe2dfa0ef.
Lemma F_c2768 : fetch_word Ubsan.M.loaded_segments (0xc2920 : word) = Some W_c2768.
Proof. vm_refl. Qed.
Lemma D_c2768 : decode_any W_c2768 = Some (Jal 1 2076204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c276c : bv 32 := 0x000a0993.
Lemma F_c276c : fetch_word Ubsan.M.loaded_segments (0xc2924 : word) = Some W_c276c.
Proof. vm_refl. Qed.
Lemma D_c276c : decode_any W_c276c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2770 : bv 32 := 0xf7650ce3.
Lemma F_c2770 : fetch_word Ubsan.M.loaded_segments (0xc2928 : word) = Some W_c2770.
Proof. vm_refl. Qed.
Lemma D_c2770 : decode_any W_c2770 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2774 : bv 32 := 0x02054c63.
Lemma F_c2774 : fetch_word Ubsan.M.loaded_segments (0xc292c : word) = Some W_c2774.
Proof. vm_refl. Qed.
Lemma D_c2774 : decode_any W_c2774 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2778 : bv 32 := 0x0089b583.
Lemma F_c2778 : fetch_word Ubsan.M.loaded_segments (0xc2930 : word) = Some W_c2778.
Proof. vm_refl. Qed.
Lemma D_c2778 : decode_any W_c2778 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c277c : bv 32 := 0x00a5b633.
Lemma F_c277c : fetch_word Ubsan.M.loaded_segments (0xc2934 : word) = Some W_c277c.
Proof. vm_refl. Qed.
Lemma D_c277c : decode_any W_c277c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2780 : bv 32 := 0x00461a13.
Lemma F_c2780 : fetch_word Ubsan.M.loaded_segments (0xc2938 : word) = Some W_c2780.
Proof. vm_refl. Qed.
Lemma D_c2780 : decode_any W_c2780 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2784 : bv 32 := 0x01498a33.
Lemma F_c2784 : fetch_word Ubsan.M.loaded_segments (0xc293c : word) = Some W_c2784.
Proof. vm_refl. Qed.
Lemma D_c2784 : decode_any W_c2784 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2788 : bv 32 := 0x000a3703.
Lemma F_c2788 : fetch_word Ubsan.M.loaded_segments (0xc2940 : word) = Some W_c2788.
Proof. vm_refl. Qed.
Lemma D_c2788 : decode_any W_c2788 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c278c : bv 32 := 0x40c006b3.
Lemma F_c278c : fetch_word Ubsan.M.loaded_segments (0xc2944 : word) = Some W_c278c.
Proof. vm_refl. Qed.
Lemma D_c278c : decode_any W_c278c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2790 : bv 32 := 0x00b6f6b3.
Lemma F_c2790 : fetch_word Ubsan.M.loaded_segments (0xc2948 : word) = Some W_c2790.
Proof. vm_refl. Qed.
Lemma D_c2790 : decode_any W_c2790 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2794 : bv 32 := 0x40d506b3.
Lemma F_c2794 : fetch_word Ubsan.M.loaded_segments (0xc294c : word) = Some W_c2794.
Proof. vm_refl. Qed.
Lemma D_c2794 : decode_any W_c2794 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c2798 : bv 32 := 0x00d70733.
Lemma F_c2798 : fetch_word Ubsan.M.loaded_segments (0xc2950 : word) = Some W_c2798.
Proof. vm_refl. Qed.
Lemma D_c2798 : decode_any W_c2798 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c279c : bv 32 := 0x00ea3023.
Lemma F_c279c : fetch_word Ubsan.M.loaded_segments (0xc2954 : word) = Some W_c279c.
Proof. vm_refl. Qed.
Lemma D_c279c : decode_any W_c279c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27a0 : bv 32 := 0xf8a5fce3.
Lemma F_c27a0 : fetch_word Ubsan.M.loaded_segments (0xc2958 : word) = Some W_c27a0.
Proof. vm_refl. Qed.
Lemma D_c27a0 : decode_any W_c27a0 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27a4 : bv 32 := 0x01800713.
Lemma F_c27a4 : fetch_word Ubsan.M.loaded_segments (0xc295c : word) = Some W_c27a4.
Proof. vm_refl. Qed.
Lemma D_c27a4 : decode_any W_c27a4 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27a8 : bv 32 := 0xf95ff06f.
Lemma F_c27a8 : fetch_word Ubsan.M.loaded_segments (0xc2960 : word) = Some W_c27a8.
Proof. vm_refl. Qed.
Lemma D_c27a8 : decode_any W_c27a8 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27ac : bv 32 := 0x00000513.
Lemma F_c27ac : fetch_word Ubsan.M.loaded_segments (0xc2964 : word) = Some W_c27ac.
Proof. vm_refl. Qed.
Lemma D_c27ac : decode_any W_c27ac = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27b0 : bv 32 := 0x0004a583.
Lemma F_c27b0 : fetch_word Ubsan.M.loaded_segments (0xc2968 : word) = Some W_c27b0.
Proof. vm_refl. Qed.
Lemma D_c27b0 : decode_any W_c27b0 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27b4 : bv 32 := 0x0009091b.
Lemma F_c27b4 : fetch_word Ubsan.M.loaded_segments (0xc296c : word) = Some W_c27b4.
Proof. vm_refl. Qed.
Lemma D_c27b4 : decode_any W_c27b4 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27b8 : bv 32 := 0x00200613.
Lemma F_c27b8 : fetch_word Ubsan.M.loaded_segments (0xc2970 : word) = Some W_c27b8.
Proof. vm_refl. Qed.
Lemma D_c27b8 : decode_any W_c27b8 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27bc : bv 32 := 0x0205e593.
Lemma F_c27bc : fetch_word Ubsan.M.loaded_segments (0xc2974 : word) = Some W_c27bc.
Proof. vm_refl. Qed.
Lemma D_c27bc : decode_any W_c27bc = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27c0 : bv 32 := 0x00b4a023.
Lemma F_c27c0 : fetch_word Ubsan.M.loaded_segments (0xc2978 : word) = Some W_c27c0.
Proof. vm_refl. Qed.
Lemma D_c27c0 : decode_any W_c27c0 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27c4 : bv 32 := 0x0204b023.
Lemma F_c27c4 : fetch_word Ubsan.M.loaded_segments (0xc297c : word) = Some W_c27c4.
Proof. vm_refl. Qed.
Lemma D_c27c4 : decode_any W_c27c4 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27c8 : bv 32 := 0x0204b423.
Lemma F_c27c8 : fetch_word Ubsan.M.loaded_segments (0xc2980 : word) = Some W_c27c8.
Proof. vm_refl. Qed.
Lemma D_c27c8 : decode_any W_c27c8 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27cc : bv 32 := 0x0204bc23.
Lemma F_c27cc : fetch_word Ubsan.M.loaded_segments (0xc2984 : word) = Some W_c27cc.
Proof. vm_refl. Qed.
Lemma D_c27cc : decode_any W_c27cc = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27d0 : bv 32 := 0xf2c90ae3.
Lemma F_c27d0 : fetch_word Ubsan.M.loaded_segments (0xc2988 : word) = Some W_c27d0.
Proof. vm_refl. Qed.
Lemma D_c27d0 : decode_any W_c27d0 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27d4 : bv 32 := 0x0089b503.
Lemma F_c27d4 : fetch_word Ubsan.M.loaded_segments (0xc298c : word) = Some W_c27d4.
Proof. vm_refl. Qed.
Lemma D_c27d4 : decode_any W_c27d4 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27d8 : bv 32 := 0x40a40533.
Lemma F_c27d8 : fetch_word Ubsan.M.loaded_segments (0xc2990 : word) = Some W_c27d8.
Proof. vm_refl. Qed.
Lemma D_c27d8 : decode_any W_c27d8 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27dc : bv 32 := 0xf29ff06f.
Lemma F_c27dc : fetch_word Ubsan.M.loaded_segments (0xc2994 : word) = Some W_c27dc.
Proof. vm_refl. Qed.
Lemma D_c27dc : decode_any W_c27dc = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c27e0 : bv 32 := 0xdadfa0ef.
Lemma F_c27e0 : fetch_word Ubsan.M.loaded_segments (0xc2998 : word) = Some W_c27e0.
Proof. vm_refl. Qed.
Lemma D_c27e0 : decode_any W_c27e0 = Some (Jal 1 2076076, 4%Z).
Proof. vm_refl. Qed.
