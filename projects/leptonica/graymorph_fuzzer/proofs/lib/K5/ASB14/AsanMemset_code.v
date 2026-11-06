(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import AsanUbsan.
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
Definition W_e04cc : bv 32 := 0x0e060a63.
Lemma F_e04cc : fetch_word AsanUbsan.M.loaded_segments (0xe1014 : word) = Some W_e04cc.
Proof. vm_refl. Qed.
Lemma D_e04cc : decode_any W_e04cc = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04d0 : bv 32 := 0x00b50023.
Lemma F_e04d0 : fetch_word AsanUbsan.M.loaded_segments (0xe1018 : word) = Some W_e04d0.
Proof. vm_refl. Qed.
Lemma D_e04d0 : decode_any W_e04d0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04d4 : bv 32 := 0x00c506b3.
Lemma F_e04d4 : fetch_word AsanUbsan.M.loaded_segments (0xe101c : word) = Some W_e04d4.
Proof. vm_refl. Qed.
Lemma D_e04d4 : decode_any W_e04d4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04d8 : bv 32 := 0x00300713.
Lemma F_e04d8 : fetch_word AsanUbsan.M.loaded_segments (0xe1020 : word) = Some W_e04d8.
Proof. vm_refl. Qed.
Lemma D_e04d8 : decode_any W_e04d8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04dc : bv 32 := 0xfeb68fa3.
Lemma F_e04dc : fetch_word AsanUbsan.M.loaded_segments (0xe1024 : word) = Some W_e04dc.
Proof. vm_refl. Qed.
Lemma D_e04dc : decode_any W_e04dc = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04e0 : bv 32 := 0x0ee66063.
Lemma F_e04e0 : fetch_word AsanUbsan.M.loaded_segments (0xe1028 : word) = Some W_e04e0.
Proof. vm_refl. Qed.
Lemma D_e04e0 : decode_any W_e04e0 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04e4 : bv 32 := 0x00b500a3.
Lemma F_e04e4 : fetch_word AsanUbsan.M.loaded_segments (0xe102c : word) = Some W_e04e4.
Proof. vm_refl. Qed.
Lemma D_e04e4 : decode_any W_e04e4 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04e8 : bv 32 := 0x00b50123.
Lemma F_e04e8 : fetch_word AsanUbsan.M.loaded_segments (0xe1030 : word) = Some W_e04e8.
Proof. vm_refl. Qed.
Lemma D_e04e8 : decode_any W_e04e8 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04ec : bv 32 := 0x00700713.
Lemma F_e04ec : fetch_word AsanUbsan.M.loaded_segments (0xe1034 : word) = Some W_e04ec.
Proof. vm_refl. Qed.
Lemma D_e04ec : decode_any W_e04ec = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04f0 : bv 32 := 0xfeb68ea3.
Lemma F_e04f0 : fetch_word AsanUbsan.M.loaded_segments (0xe1038 : word) = Some W_e04f0.
Proof. vm_refl. Qed.
Lemma D_e04f0 : decode_any W_e04f0 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04f4 : bv 32 := 0xfeb68f23.
Lemma F_e04f4 : fetch_word AsanUbsan.M.loaded_segments (0xe103c : word) = Some W_e04f4.
Proof. vm_refl. Qed.
Lemma D_e04f4 : decode_any W_e04f4 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04f8 : bv 32 := 0x0ce66463.
Lemma F_e04f8 : fetch_word AsanUbsan.M.loaded_segments (0xe1040 : word) = Some W_e04f8.
Proof. vm_refl. Qed.
Lemma D_e04f8 : decode_any W_e04f8 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04fc : bv 32 := 0x00b501a3.
Lemma F_e04fc : fetch_word AsanUbsan.M.loaded_segments (0xe1044 : word) = Some W_e04fc.
Proof. vm_refl. Qed.
Lemma D_e04fc : decode_any W_e04fc = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0500 : bv 32 := 0x00900793.
Lemma F_e0500 : fetch_word AsanUbsan.M.loaded_segments (0xe1048 : word) = Some W_e0500.
Proof. vm_refl. Qed.
Lemma D_e0500 : decode_any W_e0500 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0504 : bv 32 := 0xfeb68e23.
Lemma F_e0504 : fetch_word AsanUbsan.M.loaded_segments (0xe104c : word) = Some W_e0504.
Proof. vm_refl. Qed.
Lemma D_e0504 : decode_any W_e0504 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0508 : bv 32 := 0x0af66c63.
Lemma F_e0508 : fetch_word AsanUbsan.M.loaded_segments (0xe1050 : word) = Some W_e0508.
Proof. vm_refl. Qed.
Lemma D_e0508 : decode_any W_e0508 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e050c : bv 32 := 0x40a006bb.
Lemma F_e050c : fetch_word AsanUbsan.M.loaded_segments (0xe1054 : word) = Some W_e050c.
Proof. vm_refl. Qed.
Lemma D_e050c : decode_any W_e050c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0510 : bv 32 := 0x03859813.
Lemma F_e0510 : fetch_word AsanUbsan.M.loaded_segments (0xe1058 : word) = Some W_e0510.
Proof. vm_refl. Qed.
Lemma D_e0510 : decode_any W_e0510 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0514 : bv 32 := 0x101015b7.
Lemma F_e0514 : fetch_word AsanUbsan.M.loaded_segments (0xe105c : word) = Some W_e0514.
Proof. vm_refl. Qed.
Lemma D_e0514 : decode_any W_e0514 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0518 : bv 32 := 0x0036f693.
Lemma F_e0518 : fetch_word AsanUbsan.M.loaded_segments (0xe1060 : word) = Some W_e0518.
Proof. vm_refl. Qed.
Lemma D_e0518 : decode_any W_e0518 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e051c : bv 32 := 0x00459713.
Lemma F_e051c : fetch_word AsanUbsan.M.loaded_segments (0xe1064 : word) = Some W_e051c.
Proof. vm_refl. Qed.
Lemma D_e051c : decode_any W_e051c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0520 : bv 32 := 0x40d60633.
Lemma F_e0520 : fetch_word AsanUbsan.M.loaded_segments (0xe1068 : word) = Some W_e0520.
Proof. vm_refl. Qed.
Lemma D_e0520 : decode_any W_e0520 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0524 : bv 32 := 0x00d505b3.
Lemma F_e0524 : fetch_word AsanUbsan.M.loaded_segments (0xe106c : word) = Some W_e0524.
Proof. vm_refl. Qed.
Lemma D_e0524 : decode_any W_e0524 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0528 : bv 32 := 0x10070693.
Lemma F_e0528 : fetch_word AsanUbsan.M.loaded_segments (0xe1070 : word) = Some W_e0528.
Proof. vm_refl. Qed.
Lemma D_e0528 : decode_any W_e0528 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e052c : bv 32 := 0xffc67713.
Lemma F_e052c : fetch_word AsanUbsan.M.loaded_segments (0xe1074 : word) = Some W_e052c.
Proof. vm_refl. Qed.
Lemma D_e052c : decode_any W_e052c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0530 : bv 32 := 0x02d83633.
Lemma F_e0530 : fetch_word AsanUbsan.M.loaded_segments (0xe1078 : word) = Some W_e0530.
Proof. vm_refl. Qed.
Lemma D_e0530 : decode_any W_e0530 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0534 : bv 32 := 0x00c5a023.
Lemma F_e0534 : fetch_word AsanUbsan.M.loaded_segments (0xe107c : word) = Some W_e0534.
Proof. vm_refl. Qed.
Lemma D_e0534 : decode_any W_e0534 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0538 : bv 32 := 0x00e586b3.
Lemma F_e0538 : fetch_word AsanUbsan.M.loaded_segments (0xe1080 : word) = Some W_e0538.
Proof. vm_refl. Qed.
Lemma D_e0538 : decode_any W_e0538 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e053c : bv 32 := 0xfec6ae23.
Lemma F_e053c : fetch_word AsanUbsan.M.loaded_segments (0xe1084 : word) = Some W_e053c.
Proof. vm_refl. Qed.
Lemma D_e053c : decode_any W_e053c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0540 : bv 32 := 0x08f76063.
Lemma F_e0540 : fetch_word AsanUbsan.M.loaded_segments (0xe1088 : word) = Some W_e0540.
Proof. vm_refl. Qed.
Lemma D_e0540 : decode_any W_e0540 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0544 : bv 32 := 0x00c5a223.
Lemma F_e0544 : fetch_word AsanUbsan.M.loaded_segments (0xe108c : word) = Some W_e0544.
Proof. vm_refl. Qed.
Lemma D_e0544 : decode_any W_e0544 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0548 : bv 32 := 0x00c5a423.
Lemma F_e0548 : fetch_word AsanUbsan.M.loaded_segments (0xe1090 : word) = Some W_e0548.
Proof. vm_refl. Qed.
Lemma D_e0548 : decode_any W_e0548 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e054c : bv 32 := 0x01900793.
Lemma F_e054c : fetch_word AsanUbsan.M.loaded_segments (0xe1094 : word) = Some W_e054c.
Proof. vm_refl. Qed.
Lemma D_e054c : decode_any W_e054c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0550 : bv 32 := 0xfec6aa23.
Lemma F_e0550 : fetch_word AsanUbsan.M.loaded_segments (0xe1098 : word) = Some W_e0550.
Proof. vm_refl. Qed.
Lemma D_e0550 : decode_any W_e0550 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0554 : bv 32 := 0xfec6ac23.
Lemma F_e0554 : fetch_word AsanUbsan.M.loaded_segments (0xe109c : word) = Some W_e0554.
Proof. vm_refl. Qed.
Lemma D_e0554 : decode_any W_e0554 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0558 : bv 32 := 0x06f76463.
Lemma F_e0558 : fetch_word AsanUbsan.M.loaded_segments (0xe10a0 : word) = Some W_e0558.
Proof. vm_refl. Qed.
Lemma D_e0558 : decode_any W_e0558 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e055c : bv 32 := 0x00c5a623.
Lemma F_e055c : fetch_word AsanUbsan.M.loaded_segments (0xe10a4 : word) = Some W_e055c.
Proof. vm_refl. Qed.
Lemma D_e055c : decode_any W_e055c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0560 : bv 32 := 0x00c5a823.
Lemma F_e0560 : fetch_word AsanUbsan.M.loaded_segments (0xe10a8 : word) = Some W_e0560.
Proof. vm_refl. Qed.
Lemma D_e0560 : decode_any W_e0560 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0564 : bv 32 := 0x00c5aa23.
Lemma F_e0564 : fetch_word AsanUbsan.M.loaded_segments (0xe10ac : word) = Some W_e0564.
Proof. vm_refl. Qed.
Lemma D_e0564 : decode_any W_e0564 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0568 : bv 32 := 0x00c5ac23.
Lemma F_e0568 : fetch_word AsanUbsan.M.loaded_segments (0xe10b0 : word) = Some W_e0568.
Proof. vm_refl. Qed.
Lemma D_e0568 : decode_any W_e0568 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e056c : bv 32 := 0x0045f793.
Lemma F_e056c : fetch_word AsanUbsan.M.loaded_segments (0xe10b4 : word) = Some W_e056c.
Proof. vm_refl. Qed.
Lemma D_e056c : decode_any W_e056c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0570 : bv 32 := 0x02000813.
Lemma F_e0570 : fetch_word AsanUbsan.M.loaded_segments (0xe10b8 : word) = Some W_e0570.
Proof. vm_refl. Qed.
Lemma D_e0570 : decode_any W_e0570 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0574 : bv 32 := 0x01878793.
Lemma F_e0574 : fetch_word AsanUbsan.M.loaded_segments (0xe10bc : word) = Some W_e0574.
Proof. vm_refl. Qed.
Lemma D_e0574 : decode_any W_e0574 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0578 : bv 32 := 0x40f70733.
Lemma F_e0578 : fetch_word AsanUbsan.M.loaded_segments (0xe10c0 : word) = Some W_e0578.
Proof. vm_refl. Qed.
Lemma D_e0578 : decode_any W_e0578 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e057c : bv 32 := 0xfec6a223.
Lemma F_e057c : fetch_word AsanUbsan.M.loaded_segments (0xe10c4 : word) = Some W_e057c.
Proof. vm_refl. Qed.
Lemma D_e057c : decode_any W_e057c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0580 : bv 32 := 0xfec6a423.
Lemma F_e0580 : fetch_word AsanUbsan.M.loaded_segments (0xe10c8 : word) = Some W_e0580.
Proof. vm_refl. Qed.
Lemma D_e0580 : decode_any W_e0580 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0584 : bv 32 := 0xfec6a623.
Lemma F_e0584 : fetch_word AsanUbsan.M.loaded_segments (0xe10cc : word) = Some W_e0584.
Proof. vm_refl. Qed.
Lemma D_e0584 : decode_any W_e0584 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0588 : bv 32 := 0xfec6a823.
Lemma F_e0588 : fetch_word AsanUbsan.M.loaded_segments (0xe10d0 : word) = Some W_e0588.
Proof. vm_refl. Qed.
Lemma D_e0588 : decode_any W_e0588 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e058c : bv 32 := 0x03076a63.
Lemma F_e058c : fetch_word AsanUbsan.M.loaded_segments (0xe10d4 : word) = Some W_e058c.
Proof. vm_refl. Qed.
Lemma D_e058c : decode_any W_e058c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0590 : bv 32 := 0x02061613.
Lemma F_e0590 : fetch_word AsanUbsan.M.loaded_segments (0xe10d8 : word) = Some W_e0590.
Proof. vm_refl. Qed.
Lemma D_e0590 : decode_any W_e0590 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0594 : bv 32 := 0x00f585b3.
Lemma F_e0594 : fetch_word AsanUbsan.M.loaded_segments (0xe10dc : word) = Some W_e0594.
Proof. vm_refl. Qed.
Lemma D_e0594 : decode_any W_e0594 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0598 : bv 32 := 0x02065693.
Lemma F_e0598 : fetch_word AsanUbsan.M.loaded_segments (0xe10e0 : word) = Some W_e0598.
Proof. vm_refl. Qed.
Lemma D_e0598 : decode_any W_e0598 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e059c : bv 32 := 0x00d66633.
Lemma F_e059c : fetch_word AsanUbsan.M.loaded_segments (0xe10e4 : word) = Some W_e059c.
Proof. vm_refl. Qed.
Lemma D_e059c : decode_any W_e059c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05a0 : bv 32 := 0x01f00693.
Lemma F_e05a0 : fetch_word AsanUbsan.M.loaded_segments (0xe10e8 : word) = Some W_e05a0.
Proof. vm_refl. Qed.
Lemma D_e05a0 : decode_any W_e05a0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05a4 : bv 32 := 0x00c5b023.
Lemma F_e05a4 : fetch_word AsanUbsan.M.loaded_segments (0xe10ec : word) = Some W_e05a4.
Proof. vm_refl. Qed.
Lemma D_e05a4 : decode_any W_e05a4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05a8 : bv 32 := 0x00c5b423.
Lemma F_e05a8 : fetch_word AsanUbsan.M.loaded_segments (0xe10f0 : word) = Some W_e05a8.
Proof. vm_refl. Qed.
Lemma D_e05a8 : decode_any W_e05a8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05ac : bv 32 := 0x00c5b823.
Lemma F_e05ac : fetch_word AsanUbsan.M.loaded_segments (0xe10f4 : word) = Some W_e05ac.
Proof. vm_refl. Qed.
Lemma D_e05ac : decode_any W_e05ac = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05b0 : bv 32 := 0x00c5bc23.
Lemma F_e05b0 : fetch_word AsanUbsan.M.loaded_segments (0xe10f8 : word) = Some W_e05b0.
Proof. vm_refl. Qed.
Lemma D_e05b0 : decode_any W_e05b0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05b4 : bv 32 := 0xfe070713.
Lemma F_e05b4 : fetch_word AsanUbsan.M.loaded_segments (0xe10fc : word) = Some W_e05b4.
Proof. vm_refl. Qed.
Lemma D_e05b4 : decode_any W_e05b4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05b8 : bv 32 := 0x02058593.
Lemma F_e05b8 : fetch_word AsanUbsan.M.loaded_segments (0xe1100 : word) = Some W_e05b8.
Proof. vm_refl. Qed.
Lemma D_e05b8 : decode_any W_e05b8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05bc : bv 32 := 0xfee6e4e3.
Lemma F_e05bc : fetch_word AsanUbsan.M.loaded_segments (0xe1104 : word) = Some W_e05bc.
Proof. vm_refl. Qed.
Lemma D_e05bc : decode_any W_e05bc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e05c0 : bv 32 := 0x00008067.
Lemma F_e05c0 : fetch_word AsanUbsan.M.loaded_segments (0xe1108 : word) = Some W_e05c0.
Proof. vm_refl. Qed.
Lemma D_e05c0 : decode_any W_e05c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xe1014%Z.
Definition Fo_000 := F_e04cc.
Definition Do_000 := D_e04cc.
Definition Fo_004 := F_e04d0.
Definition Do_004 := D_e04d0.
Definition Fo_008 := F_e04d4.
Definition Do_008 := D_e04d4.
Definition Fo_00c := F_e04d8.
Definition Do_00c := D_e04d8.
Definition Fo_010 := F_e04dc.
Definition Do_010 := D_e04dc.
Definition Fo_014 := F_e04e0.
Definition Do_014 := D_e04e0.
Definition Fo_018 := F_e04e4.
Definition Do_018 := D_e04e4.
Definition Fo_01c := F_e04e8.
Definition Do_01c := D_e04e8.
Definition Fo_020 := F_e04ec.
Definition Do_020 := D_e04ec.
Definition Fo_024 := F_e04f0.
Definition Do_024 := D_e04f0.
Definition Fo_028 := F_e04f4.
Definition Do_028 := D_e04f4.
Definition Fo_02c := F_e04f8.
Definition Do_02c := D_e04f8.
Definition Fo_030 := F_e04fc.
Definition Do_030 := D_e04fc.
Definition Fo_034 := F_e0500.
Definition Do_034 := D_e0500.
Definition Fo_038 := F_e0504.
Definition Do_038 := D_e0504.
Definition Fo_03c := F_e0508.
Definition Do_03c := D_e0508.
Definition Fo_040 := F_e050c.
Definition Do_040 := D_e050c.
Definition Fo_044 := F_e0510.
Definition Do_044 := D_e0510.
Definition Fo_048 := F_e0514.
Definition Do_048 := D_e0514.
Definition Fo_04c := F_e0518.
Definition Do_04c := D_e0518.
Definition Fo_050 := F_e051c.
Definition Do_050 := D_e051c.
Definition Fo_054 := F_e0520.
Definition Do_054 := D_e0520.
Definition Fo_058 := F_e0524.
Definition Do_058 := D_e0524.
Definition Fo_05c := F_e0528.
Definition Do_05c := D_e0528.
Definition Fo_060 := F_e052c.
Definition Do_060 := D_e052c.
Definition Fo_064 := F_e0530.
Definition Do_064 := D_e0530.
Definition Fo_068 := F_e0534.
Definition Do_068 := D_e0534.
Definition Fo_06c := F_e0538.
Definition Do_06c := D_e0538.
Definition Fo_070 := F_e053c.
Definition Do_070 := D_e053c.
Definition Fo_074 := F_e0540.
Definition Do_074 := D_e0540.
Definition Fo_078 := F_e0544.
Definition Do_078 := D_e0544.
Definition Fo_07c := F_e0548.
Definition Do_07c := D_e0548.
Definition Fo_080 := F_e054c.
Definition Do_080 := D_e054c.
Definition Fo_084 := F_e0550.
Definition Do_084 := D_e0550.
Definition Fo_088 := F_e0554.
Definition Do_088 := D_e0554.
Definition Fo_08c := F_e0558.
Definition Do_08c := D_e0558.
Definition Fo_090 := F_e055c.
Definition Do_090 := D_e055c.
Definition Fo_094 := F_e0560.
Definition Do_094 := D_e0560.
Definition Fo_098 := F_e0564.
Definition Do_098 := D_e0564.
Definition Fo_09c := F_e0568.
Definition Do_09c := D_e0568.
Definition Fo_0a0 := F_e056c.
Definition Do_0a0 := D_e056c.
Definition Fo_0a4 := F_e0570.
Definition Do_0a4 := D_e0570.
Definition Fo_0a8 := F_e0574.
Definition Do_0a8 := D_e0574.
Definition Fo_0ac := F_e0578.
Definition Do_0ac := D_e0578.
Definition Fo_0b0 := F_e057c.
Definition Do_0b0 := D_e057c.
Definition Fo_0b4 := F_e0580.
Definition Do_0b4 := D_e0580.
Definition Fo_0b8 := F_e0584.
Definition Do_0b8 := D_e0584.
Definition Fo_0bc := F_e0588.
Definition Do_0bc := D_e0588.
Definition Fo_0c0 := F_e058c.
Definition Do_0c0 := D_e058c.
Definition Fo_0c4 := F_e0590.
Definition Do_0c4 := D_e0590.
Definition Fo_0c8 := F_e0594.
Definition Do_0c8 := D_e0594.
Definition Fo_0cc := F_e0598.
Definition Do_0cc := D_e0598.
Definition Fo_0d0 := F_e059c.
Definition Do_0d0 := D_e059c.
Definition Fo_0d4 := F_e05a0.
Definition Do_0d4 := D_e05a0.
Definition Fo_0d8 := F_e05a4.
Definition Do_0d8 := D_e05a4.
Definition Fo_0dc := F_e05a8.
Definition Do_0dc := D_e05a8.
Definition Fo_0e0 := F_e05ac.
Definition Do_0e0 := D_e05ac.
Definition Fo_0e4 := F_e05b0.
Definition Do_0e4 := D_e05b0.
Definition Fo_0e8 := F_e05b4.
Definition Do_0e8 := D_e05b4.
Definition Fo_0ec := F_e05b8.
Definition Do_0ec := D_e05b8.
Definition Fo_0f0 := F_e05bc.
Definition Do_0f0 := D_e05bc.
Definition Fo_0f4 := F_e05c0.
Definition Do_0f4 := D_e05c0.
