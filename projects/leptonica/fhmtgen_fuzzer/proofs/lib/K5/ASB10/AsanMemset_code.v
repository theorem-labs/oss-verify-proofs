(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)
Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof. intros segs a w. apply bool_decide_eq_true_1. Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof. intros w x. apply bool_decide_eq_true_1. Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

(* [comment removed for export] *)
Definition W_e266c : bv 32 := 0x0e060a63.
Lemma F_e266c : fetch_word AsanUbsan.M.loaded_segments (0xe2fe8 : word) = Some W_e266c.
Proof. vm_refl. Qed.
Lemma D_e266c : decode_any W_e266c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2670 : bv 32 := 0x00b50023.
Lemma F_e2670 : fetch_word AsanUbsan.M.loaded_segments (0xe2fec : word) = Some W_e2670.
Proof. vm_refl. Qed.
Lemma D_e2670 : decode_any W_e2670 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2674 : bv 32 := 0x00c506b3.
Lemma F_e2674 : fetch_word AsanUbsan.M.loaded_segments (0xe2ff0 : word) = Some W_e2674.
Proof. vm_refl. Qed.
Lemma D_e2674 : decode_any W_e2674 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2678 : bv 32 := 0x00300713.
Lemma F_e2678 : fetch_word AsanUbsan.M.loaded_segments (0xe2ff4 : word) = Some W_e2678.
Proof. vm_refl. Qed.
Lemma D_e2678 : decode_any W_e2678 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e267c : bv 32 := 0xfeb68fa3.
Lemma F_e267c : fetch_word AsanUbsan.M.loaded_segments (0xe2ff8 : word) = Some W_e267c.
Proof. vm_refl. Qed.
Lemma D_e267c : decode_any W_e267c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2680 : bv 32 := 0x0ee66063.
Lemma F_e2680 : fetch_word AsanUbsan.M.loaded_segments (0xe2ffc : word) = Some W_e2680.
Proof. vm_refl. Qed.
Lemma D_e2680 : decode_any W_e2680 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2684 : bv 32 := 0x00b500a3.
Lemma F_e2684 : fetch_word AsanUbsan.M.loaded_segments (0xe3000 : word) = Some W_e2684.
Proof. vm_refl. Qed.
Lemma D_e2684 : decode_any W_e2684 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2688 : bv 32 := 0x00b50123.
Lemma F_e2688 : fetch_word AsanUbsan.M.loaded_segments (0xe3004 : word) = Some W_e2688.
Proof. vm_refl. Qed.
Lemma D_e2688 : decode_any W_e2688 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e268c : bv 32 := 0x00700713.
Lemma F_e268c : fetch_word AsanUbsan.M.loaded_segments (0xe3008 : word) = Some W_e268c.
Proof. vm_refl. Qed.
Lemma D_e268c : decode_any W_e268c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2690 : bv 32 := 0xfeb68ea3.
Lemma F_e2690 : fetch_word AsanUbsan.M.loaded_segments (0xe300c : word) = Some W_e2690.
Proof. vm_refl. Qed.
Lemma D_e2690 : decode_any W_e2690 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2694 : bv 32 := 0xfeb68f23.
Lemma F_e2694 : fetch_word AsanUbsan.M.loaded_segments (0xe3010 : word) = Some W_e2694.
Proof. vm_refl. Qed.
Lemma D_e2694 : decode_any W_e2694 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2698 : bv 32 := 0x0ce66463.
Lemma F_e2698 : fetch_word AsanUbsan.M.loaded_segments (0xe3014 : word) = Some W_e2698.
Proof. vm_refl. Qed.
Lemma D_e2698 : decode_any W_e2698 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e269c : bv 32 := 0x00b501a3.
Lemma F_e269c : fetch_word AsanUbsan.M.loaded_segments (0xe3018 : word) = Some W_e269c.
Proof. vm_refl. Qed.
Lemma D_e269c : decode_any W_e269c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26a0 : bv 32 := 0x00900793.
Lemma F_e26a0 : fetch_word AsanUbsan.M.loaded_segments (0xe301c : word) = Some W_e26a0.
Proof. vm_refl. Qed.
Lemma D_e26a0 : decode_any W_e26a0 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26a4 : bv 32 := 0xfeb68e23.
Lemma F_e26a4 : fetch_word AsanUbsan.M.loaded_segments (0xe3020 : word) = Some W_e26a4.
Proof. vm_refl. Qed.
Lemma D_e26a4 : decode_any W_e26a4 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26a8 : bv 32 := 0x0af66c63.
Lemma F_e26a8 : fetch_word AsanUbsan.M.loaded_segments (0xe3024 : word) = Some W_e26a8.
Proof. vm_refl. Qed.
Lemma D_e26a8 : decode_any W_e26a8 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26ac : bv 32 := 0x40a006bb.
Lemma F_e26ac : fetch_word AsanUbsan.M.loaded_segments (0xe3028 : word) = Some W_e26ac.
Proof. vm_refl. Qed.
Lemma D_e26ac : decode_any W_e26ac = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26b0 : bv 32 := 0x03859813.
Lemma F_e26b0 : fetch_word AsanUbsan.M.loaded_segments (0xe302c : word) = Some W_e26b0.
Proof. vm_refl. Qed.
Lemma D_e26b0 : decode_any W_e26b0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26b4 : bv 32 := 0x101015b7.
Lemma F_e26b4 : fetch_word AsanUbsan.M.loaded_segments (0xe3030 : word) = Some W_e26b4.
Proof. vm_refl. Qed.
Lemma D_e26b4 : decode_any W_e26b4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26b8 : bv 32 := 0x0036f693.
Lemma F_e26b8 : fetch_word AsanUbsan.M.loaded_segments (0xe3034 : word) = Some W_e26b8.
Proof. vm_refl. Qed.
Lemma D_e26b8 : decode_any W_e26b8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26bc : bv 32 := 0x00459713.
Lemma F_e26bc : fetch_word AsanUbsan.M.loaded_segments (0xe3038 : word) = Some W_e26bc.
Proof. vm_refl. Qed.
Lemma D_e26bc : decode_any W_e26bc = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26c0 : bv 32 := 0x40d60633.
Lemma F_e26c0 : fetch_word AsanUbsan.M.loaded_segments (0xe303c : word) = Some W_e26c0.
Proof. vm_refl. Qed.
Lemma D_e26c0 : decode_any W_e26c0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26c4 : bv 32 := 0x00d505b3.
Lemma F_e26c4 : fetch_word AsanUbsan.M.loaded_segments (0xe3040 : word) = Some W_e26c4.
Proof. vm_refl. Qed.
Lemma D_e26c4 : decode_any W_e26c4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26c8 : bv 32 := 0x10070693.
Lemma F_e26c8 : fetch_word AsanUbsan.M.loaded_segments (0xe3044 : word) = Some W_e26c8.
Proof. vm_refl. Qed.
Lemma D_e26c8 : decode_any W_e26c8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26cc : bv 32 := 0xffc67713.
Lemma F_e26cc : fetch_word AsanUbsan.M.loaded_segments (0xe3048 : word) = Some W_e26cc.
Proof. vm_refl. Qed.
Lemma D_e26cc : decode_any W_e26cc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26d0 : bv 32 := 0x02d83633.
Lemma F_e26d0 : fetch_word AsanUbsan.M.loaded_segments (0xe304c : word) = Some W_e26d0.
Proof. vm_refl. Qed.
Lemma D_e26d0 : decode_any W_e26d0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26d4 : bv 32 := 0x00c5a023.
Lemma F_e26d4 : fetch_word AsanUbsan.M.loaded_segments (0xe3050 : word) = Some W_e26d4.
Proof. vm_refl. Qed.
Lemma D_e26d4 : decode_any W_e26d4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26d8 : bv 32 := 0x00e586b3.
Lemma F_e26d8 : fetch_word AsanUbsan.M.loaded_segments (0xe3054 : word) = Some W_e26d8.
Proof. vm_refl. Qed.
Lemma D_e26d8 : decode_any W_e26d8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26dc : bv 32 := 0xfec6ae23.
Lemma F_e26dc : fetch_word AsanUbsan.M.loaded_segments (0xe3058 : word) = Some W_e26dc.
Proof. vm_refl. Qed.
Lemma D_e26dc : decode_any W_e26dc = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26e0 : bv 32 := 0x08f76063.
Lemma F_e26e0 : fetch_word AsanUbsan.M.loaded_segments (0xe305c : word) = Some W_e26e0.
Proof. vm_refl. Qed.
Lemma D_e26e0 : decode_any W_e26e0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26e4 : bv 32 := 0x00c5a223.
Lemma F_e26e4 : fetch_word AsanUbsan.M.loaded_segments (0xe3060 : word) = Some W_e26e4.
Proof. vm_refl. Qed.
Lemma D_e26e4 : decode_any W_e26e4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26e8 : bv 32 := 0x00c5a423.
Lemma F_e26e8 : fetch_word AsanUbsan.M.loaded_segments (0xe3064 : word) = Some W_e26e8.
Proof. vm_refl. Qed.
Lemma D_e26e8 : decode_any W_e26e8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26ec : bv 32 := 0x01900793.
Lemma F_e26ec : fetch_word AsanUbsan.M.loaded_segments (0xe3068 : word) = Some W_e26ec.
Proof. vm_refl. Qed.
Lemma D_e26ec : decode_any W_e26ec = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26f0 : bv 32 := 0xfec6aa23.
Lemma F_e26f0 : fetch_word AsanUbsan.M.loaded_segments (0xe306c : word) = Some W_e26f0.
Proof. vm_refl. Qed.
Lemma D_e26f0 : decode_any W_e26f0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26f4 : bv 32 := 0xfec6ac23.
Lemma F_e26f4 : fetch_word AsanUbsan.M.loaded_segments (0xe3070 : word) = Some W_e26f4.
Proof. vm_refl. Qed.
Lemma D_e26f4 : decode_any W_e26f4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26f8 : bv 32 := 0x06f76463.
Lemma F_e26f8 : fetch_word AsanUbsan.M.loaded_segments (0xe3074 : word) = Some W_e26f8.
Proof. vm_refl. Qed.
Lemma D_e26f8 : decode_any W_e26f8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e26fc : bv 32 := 0x00c5a623.
Lemma F_e26fc : fetch_word AsanUbsan.M.loaded_segments (0xe3078 : word) = Some W_e26fc.
Proof. vm_refl. Qed.
Lemma D_e26fc : decode_any W_e26fc = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2700 : bv 32 := 0x00c5a823.
Lemma F_e2700 : fetch_word AsanUbsan.M.loaded_segments (0xe307c : word) = Some W_e2700.
Proof. vm_refl. Qed.
Lemma D_e2700 : decode_any W_e2700 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2704 : bv 32 := 0x00c5aa23.
Lemma F_e2704 : fetch_word AsanUbsan.M.loaded_segments (0xe3080 : word) = Some W_e2704.
Proof. vm_refl. Qed.
Lemma D_e2704 : decode_any W_e2704 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2708 : bv 32 := 0x00c5ac23.
Lemma F_e2708 : fetch_word AsanUbsan.M.loaded_segments (0xe3084 : word) = Some W_e2708.
Proof. vm_refl. Qed.
Lemma D_e2708 : decode_any W_e2708 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e270c : bv 32 := 0x0045f793.
Lemma F_e270c : fetch_word AsanUbsan.M.loaded_segments (0xe3088 : word) = Some W_e270c.
Proof. vm_refl. Qed.
Lemma D_e270c : decode_any W_e270c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2710 : bv 32 := 0x02000813.
Lemma F_e2710 : fetch_word AsanUbsan.M.loaded_segments (0xe308c : word) = Some W_e2710.
Proof. vm_refl. Qed.
Lemma D_e2710 : decode_any W_e2710 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2714 : bv 32 := 0x01878793.
Lemma F_e2714 : fetch_word AsanUbsan.M.loaded_segments (0xe3090 : word) = Some W_e2714.
Proof. vm_refl. Qed.
Lemma D_e2714 : decode_any W_e2714 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2718 : bv 32 := 0x40f70733.
Lemma F_e2718 : fetch_word AsanUbsan.M.loaded_segments (0xe3094 : word) = Some W_e2718.
Proof. vm_refl. Qed.
Lemma D_e2718 : decode_any W_e2718 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e271c : bv 32 := 0xfec6a223.
Lemma F_e271c : fetch_word AsanUbsan.M.loaded_segments (0xe3098 : word) = Some W_e271c.
Proof. vm_refl. Qed.
Lemma D_e271c : decode_any W_e271c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2720 : bv 32 := 0xfec6a423.
Lemma F_e2720 : fetch_word AsanUbsan.M.loaded_segments (0xe309c : word) = Some W_e2720.
Proof. vm_refl. Qed.
Lemma D_e2720 : decode_any W_e2720 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2724 : bv 32 := 0xfec6a623.
Lemma F_e2724 : fetch_word AsanUbsan.M.loaded_segments (0xe30a0 : word) = Some W_e2724.
Proof. vm_refl. Qed.
Lemma D_e2724 : decode_any W_e2724 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2728 : bv 32 := 0xfec6a823.
Lemma F_e2728 : fetch_word AsanUbsan.M.loaded_segments (0xe30a4 : word) = Some W_e2728.
Proof. vm_refl. Qed.
Lemma D_e2728 : decode_any W_e2728 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e272c : bv 32 := 0x03076a63.
Lemma F_e272c : fetch_word AsanUbsan.M.loaded_segments (0xe30a8 : word) = Some W_e272c.
Proof. vm_refl. Qed.
Lemma D_e272c : decode_any W_e272c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2730 : bv 32 := 0x02061613.
Lemma F_e2730 : fetch_word AsanUbsan.M.loaded_segments (0xe30ac : word) = Some W_e2730.
Proof. vm_refl. Qed.
Lemma D_e2730 : decode_any W_e2730 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2734 : bv 32 := 0x00f585b3.
Lemma F_e2734 : fetch_word AsanUbsan.M.loaded_segments (0xe30b0 : word) = Some W_e2734.
Proof. vm_refl. Qed.
Lemma D_e2734 : decode_any W_e2734 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2738 : bv 32 := 0x02065693.
Lemma F_e2738 : fetch_word AsanUbsan.M.loaded_segments (0xe30b4 : word) = Some W_e2738.
Proof. vm_refl. Qed.
Lemma D_e2738 : decode_any W_e2738 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e273c : bv 32 := 0x00d66633.
Lemma F_e273c : fetch_word AsanUbsan.M.loaded_segments (0xe30b8 : word) = Some W_e273c.
Proof. vm_refl. Qed.
Lemma D_e273c : decode_any W_e273c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2740 : bv 32 := 0x01f00693.
Lemma F_e2740 : fetch_word AsanUbsan.M.loaded_segments (0xe30bc : word) = Some W_e2740.
Proof. vm_refl. Qed.
Lemma D_e2740 : decode_any W_e2740 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2744 : bv 32 := 0x00c5b023.
Lemma F_e2744 : fetch_word AsanUbsan.M.loaded_segments (0xe30c0 : word) = Some W_e2744.
Proof. vm_refl. Qed.
Lemma D_e2744 : decode_any W_e2744 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2748 : bv 32 := 0x00c5b423.
Lemma F_e2748 : fetch_word AsanUbsan.M.loaded_segments (0xe30c4 : word) = Some W_e2748.
Proof. vm_refl. Qed.
Lemma D_e2748 : decode_any W_e2748 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e274c : bv 32 := 0x00c5b823.
Lemma F_e274c : fetch_word AsanUbsan.M.loaded_segments (0xe30c8 : word) = Some W_e274c.
Proof. vm_refl. Qed.
Lemma D_e274c : decode_any W_e274c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2750 : bv 32 := 0x00c5bc23.
Lemma F_e2750 : fetch_word AsanUbsan.M.loaded_segments (0xe30cc : word) = Some W_e2750.
Proof. vm_refl. Qed.
Lemma D_e2750 : decode_any W_e2750 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2754 : bv 32 := 0xfe070713.
Lemma F_e2754 : fetch_word AsanUbsan.M.loaded_segments (0xe30d0 : word) = Some W_e2754.
Proof. vm_refl. Qed.
Lemma D_e2754 : decode_any W_e2754 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2758 : bv 32 := 0x02058593.
Lemma F_e2758 : fetch_word AsanUbsan.M.loaded_segments (0xe30d4 : word) = Some W_e2758.
Proof. vm_refl. Qed.
Lemma D_e2758 : decode_any W_e2758 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e275c : bv 32 := 0xfee6e4e3.
Lemma F_e275c : fetch_word AsanUbsan.M.loaded_segments (0xe30d8 : word) = Some W_e275c.
Proof. vm_refl. Qed.
Lemma D_e275c : decode_any W_e275c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e2760 : bv 32 := 0x00008067.
Lemma F_e2760 : fetch_word AsanUbsan.M.loaded_segments (0xe30dc : word) = Some W_e2760.
Proof. vm_refl. Qed.
Lemma D_e2760 : decode_any W_e2760 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xe2fe8%Z.
Definition Fo_000 := F_e266c.
Definition Do_000 := D_e266c.
Definition Fo_004 := F_e2670.
Definition Do_004 := D_e2670.
Definition Fo_008 := F_e2674.
Definition Do_008 := D_e2674.
Definition Fo_00c := F_e2678.
Definition Do_00c := D_e2678.
Definition Fo_010 := F_e267c.
Definition Do_010 := D_e267c.
Definition Fo_014 := F_e2680.
Definition Do_014 := D_e2680.
Definition Fo_018 := F_e2684.
Definition Do_018 := D_e2684.
Definition Fo_01c := F_e2688.
Definition Do_01c := D_e2688.
Definition Fo_020 := F_e268c.
Definition Do_020 := D_e268c.
Definition Fo_024 := F_e2690.
Definition Do_024 := D_e2690.
Definition Fo_028 := F_e2694.
Definition Do_028 := D_e2694.
Definition Fo_02c := F_e2698.
Definition Do_02c := D_e2698.
Definition Fo_030 := F_e269c.
Definition Do_030 := D_e269c.
Definition Fo_034 := F_e26a0.
Definition Do_034 := D_e26a0.
Definition Fo_038 := F_e26a4.
Definition Do_038 := D_e26a4.
Definition Fo_03c := F_e26a8.
Definition Do_03c := D_e26a8.
Definition Fo_040 := F_e26ac.
Definition Do_040 := D_e26ac.
Definition Fo_044 := F_e26b0.
Definition Do_044 := D_e26b0.
Definition Fo_048 := F_e26b4.
Definition Do_048 := D_e26b4.
Definition Fo_04c := F_e26b8.
Definition Do_04c := D_e26b8.
Definition Fo_050 := F_e26bc.
Definition Do_050 := D_e26bc.
Definition Fo_054 := F_e26c0.
Definition Do_054 := D_e26c0.
Definition Fo_058 := F_e26c4.
Definition Do_058 := D_e26c4.
Definition Fo_05c := F_e26c8.
Definition Do_05c := D_e26c8.
Definition Fo_060 := F_e26cc.
Definition Do_060 := D_e26cc.
Definition Fo_064 := F_e26d0.
Definition Do_064 := D_e26d0.
Definition Fo_068 := F_e26d4.
Definition Do_068 := D_e26d4.
Definition Fo_06c := F_e26d8.
Definition Do_06c := D_e26d8.
Definition Fo_070 := F_e26dc.
Definition Do_070 := D_e26dc.
Definition Fo_074 := F_e26e0.
Definition Do_074 := D_e26e0.
Definition Fo_078 := F_e26e4.
Definition Do_078 := D_e26e4.
Definition Fo_07c := F_e26e8.
Definition Do_07c := D_e26e8.
Definition Fo_080 := F_e26ec.
Definition Do_080 := D_e26ec.
Definition Fo_084 := F_e26f0.
Definition Do_084 := D_e26f0.
Definition Fo_088 := F_e26f4.
Definition Do_088 := D_e26f4.
Definition Fo_08c := F_e26f8.
Definition Do_08c := D_e26f8.
Definition Fo_090 := F_e26fc.
Definition Do_090 := D_e26fc.
Definition Fo_094 := F_e2700.
Definition Do_094 := D_e2700.
Definition Fo_098 := F_e2704.
Definition Do_098 := D_e2704.
Definition Fo_09c := F_e2708.
Definition Do_09c := D_e2708.
Definition Fo_0a0 := F_e270c.
Definition Do_0a0 := D_e270c.
Definition Fo_0a4 := F_e2710.
Definition Do_0a4 := D_e2710.
Definition Fo_0a8 := F_e2714.
Definition Do_0a8 := D_e2714.
Definition Fo_0ac := F_e2718.
Definition Do_0ac := D_e2718.
Definition Fo_0b0 := F_e271c.
Definition Do_0b0 := D_e271c.
Definition Fo_0b4 := F_e2720.
Definition Do_0b4 := D_e2720.
Definition Fo_0b8 := F_e2724.
Definition Do_0b8 := D_e2724.
Definition Fo_0bc := F_e2728.
Definition Do_0bc := D_e2728.
Definition Fo_0c0 := F_e272c.
Definition Do_0c0 := D_e272c.
Definition Fo_0c4 := F_e2730.
Definition Do_0c4 := D_e2730.
Definition Fo_0c8 := F_e2734.
Definition Do_0c8 := D_e2734.
Definition Fo_0cc := F_e2738.
Definition Do_0cc := D_e2738.
Definition Fo_0d0 := F_e273c.
Definition Do_0d0 := D_e273c.
Definition Fo_0d4 := F_e2740.
Definition Do_0d4 := D_e2740.
Definition Fo_0d8 := F_e2744.
Definition Do_0d8 := D_e2744.
Definition Fo_0dc := F_e2748.
Definition Do_0dc := D_e2748.
Definition Fo_0e0 := F_e274c.
Definition Do_0e0 := D_e274c.
Definition Fo_0e4 := F_e2750.
Definition Do_0e4 := D_e2750.
Definition Fo_0e8 := F_e2754.
Definition Do_0e8 := D_e2754.
Definition Fo_0ec := F_e2758.
Definition Do_0ec := D_e2758.
Definition Fo_0f0 := F_e275c.
Definition Do_0f0 := D_e275c.
Definition Fo_0f4 := F_e2760.
Definition Do_0f4 := D_e2760.
