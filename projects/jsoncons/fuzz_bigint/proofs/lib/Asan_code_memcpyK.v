(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_cb728 : bv 32 := 0x0035f693.
Lemma F_cb728 : fetch_word Asan.M.loaded_segments (0xcb728 : word) = Some W_cb728.
Proof. vm_refl. Qed.
Lemma D_cb728 : decode_any W_cb728 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb72c : bv 32 := 0x10068863.
Lemma F_cb72c : fetch_word Asan.M.loaded_segments (0xcb72c : word) = Some W_cb72c.
Proof. vm_refl. Qed.
Lemma D_cb72c : decode_any W_cb72c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb730 : bv 32 := 0x02060e63.
Lemma F_cb730 : fetch_word Asan.M.loaded_segments (0xcb730 : word) = Some W_cb730.
Proof. vm_refl. Qed.
Lemma D_cb730 : decode_any W_cb730 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb734 : bv 32 := 0x00158713.
Lemma F_cb734 : fetch_word Asan.M.loaded_segments (0xcb734 : word) = Some W_cb734.
Proof. vm_refl. Qed.
Lemma D_cb734 : decode_any W_cb734 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb738 : bv 32 := 0x00100793.
Lemma F_cb738 : fetch_word Asan.M.loaded_segments (0xcb738 : word) = Some W_cb738.
Proof. vm_refl. Qed.
Lemma D_cb738 : decode_any W_cb738 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb73c : bv 32 := 0x00050693.
Lemma F_cb73c : fetch_word Asan.M.loaded_segments (0xcb73c : word) = Some W_cb73c.
Proof. vm_refl. Qed.
Lemma D_cb73c : decode_any W_cb73c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb740 : bv 32 := 0x0005c883.
Lemma F_cb740 : fetch_word Asan.M.loaded_segments (0xcb740 : word) = Some W_cb740.
Proof. vm_refl. Qed.
Lemma D_cb740 : decode_any W_cb740 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb744 : bv 32 := 0x00060813.
Lemma F_cb744 : fetch_word Asan.M.loaded_segments (0xcb744 : word) = Some W_cb744.
Proof. vm_refl. Qed.
Lemma D_cb744 : decode_any W_cb744 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb748 : bv 32 := 0x00158593.
Lemma F_cb748 : fetch_word Asan.M.loaded_segments (0xcb748 : word) = Some W_cb748.
Proof. vm_refl. Qed.
Lemma D_cb748 : decode_any W_cb748 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb74c : bv 32 := 0x00377293.
Lemma F_cb74c : fetch_word Asan.M.loaded_segments (0xcb74c : word) = Some W_cb74c.
Proof. vm_refl. Qed.
Lemma D_cb74c : decode_any W_cb74c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb750 : bv 32 := 0x01168023.
Lemma F_cb750 : fetch_word Asan.M.loaded_segments (0xcb750 : word) = Some W_cb750.
Proof. vm_refl. Qed.
Lemma D_cb750 : decode_any W_cb750 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb754 : bv 32 := 0x00168693.
Lemma F_cb754 : fetch_word Asan.M.loaded_segments (0xcb754 : word) = Some W_cb754.
Proof. vm_refl. Qed.
Lemma D_cb754 : decode_any W_cb754 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb758 : bv 32 := 0xfff60613.
Lemma F_cb758 : fetch_word Asan.M.loaded_segments (0xcb758 : word) = Some W_cb758.
Proof. vm_refl. Qed.
Lemma D_cb758 : decode_any W_cb758 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb75c : bv 32 := 0x00028a63.
Lemma F_cb75c : fetch_word Asan.M.loaded_segments (0xcb75c : word) = Some W_cb75c.
Proof. vm_refl. Qed.
Lemma D_cb75c : decode_any W_cb75c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb760 : bv 32 := 0x00170713.
Lemma F_cb760 : fetch_word Asan.M.loaded_segments (0xcb760 : word) = Some W_cb760.
Proof. vm_refl. Qed.
Lemma D_cb760 : decode_any W_cb760 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb764 : bv 32 := 0xfcf81ee3.
Lemma F_cb764 : fetch_word Asan.M.loaded_segments (0xcb764 : word) = Some W_cb764.
Proof. vm_refl. Qed.
Lemma D_cb764 : decode_any W_cb764 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb768 : bv 32 := 0x0080006f.
Lemma F_cb768 : fetch_word Asan.M.loaded_segments (0xcb768 : word) = Some W_cb768.
Proof. vm_refl. Qed.
Lemma D_cb768 : decode_any W_cb768 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb76c : bv 32 := 0x00050693.
Lemma F_cb76c : fetch_word Asan.M.loaded_segments (0xcb76c : word) = Some W_cb76c.
Proof. vm_refl. Qed.
Lemma D_cb76c : decode_any W_cb76c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb770 : bv 32 := 0x0036f793.
Lemma F_cb770 : fetch_word Asan.M.loaded_segments (0xcb770 : word) = Some W_cb770.
Proof. vm_refl. Qed.
Lemma D_cb770 : decode_any W_cb770 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb774 : bv 32 := 0x0c078a63.
Lemma F_cb774 : fetch_word Asan.M.loaded_segments (0xcb774 : word) = Some W_cb774.
Proof. vm_refl. Qed.
Lemma D_cb774 : decode_any W_cb774 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb778 : bv 32 := 0x02000713.
Lemma F_cb778 : fetch_word Asan.M.loaded_segments (0xcb778 : word) = Some W_cb778.
Proof. vm_refl. Qed.
Lemma D_cb778 : decode_any W_cb778 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb77c : bv 32 := 0x02e67063.
Lemma F_cb77c : fetch_word Asan.M.loaded_segments (0xcb77c : word) = Some W_cb77c.
Proof. vm_refl. Qed.
Lemma D_cb77c : decode_any W_cb77c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb780 : bv 32 := 0x01000713.
Lemma F_cb780 : fetch_word Asan.M.loaded_segments (0xcb780 : word) = Some W_cb780.
Proof. vm_refl. Qed.
Lemma D_cb780 : decode_any W_cb780 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb784 : bv 32 := 0x24e67863.
Lemma F_cb784 : fetch_word Asan.M.loaded_segments (0xcb784 : word) = Some W_cb784.
Proof. vm_refl. Qed.
Lemma D_cb784 : decode_any W_cb784 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb788 : bv 32 := 0x00867713.
Lemma F_cb788 : fetch_word Asan.M.loaded_segments (0xcb788 : word) = Some W_cb788.
Proof. vm_refl. Qed.
Lemma D_cb788 : decode_any W_cb788 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb78c : bv 32 := 0x2c071e63.
Lemma F_cb78c : fetch_word Asan.M.loaded_segments (0xcb78c : word) = Some W_cb78c.
Proof. vm_refl. Qed.
Lemma D_cb78c : decode_any W_cb78c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb790 : bv 32 := 0x00467713.
Lemma F_cb790 : fetch_word Asan.M.loaded_segments (0xcb790 : word) = Some W_cb790.
Proof. vm_refl. Qed.
Lemma D_cb790 : decode_any W_cb790 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb794 : bv 32 := 0x32071463.
Lemma F_cb794 : fetch_word Asan.M.loaded_segments (0xcb794 : word) = Some W_cb794.
Proof. vm_refl. Qed.
Lemma D_cb794 : decode_any W_cb794 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb798 : bv 32 := 0x3500006f.
Lemma F_cb798 : fetch_word Asan.M.loaded_segments (0xcb798 : word) = Some W_cb798.
Proof. vm_refl. Qed.
Lemma D_cb798 : decode_any W_cb798 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb79c : bv 32 := 0x0005a703.
Lemma F_cb79c : fetch_word Asan.M.loaded_segments (0xcb79c : word) = Some W_cb79c.
Proof. vm_refl. Qed.
Lemma D_cb79c : decode_any W_cb79c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7a0 : bv 32 := 0x00300813.
Lemma F_cb7a0 : fetch_word Asan.M.loaded_segments (0xcb7a0 : word) = Some W_cb7a0.
Proof. vm_refl. Qed.
Lemma D_cb7a0 : decode_any W_cb7a0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7a4 : bv 32 := 0x11078e63.
Lemma F_cb7a4 : fetch_word Asan.M.loaded_segments (0xcb7a4 : word) = Some W_cb7a4.
Proof. vm_refl. Qed.
Lemma D_cb7a4 : decode_any W_cb7a4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7a8 : bv 32 := 0x00200813.
Lemma F_cb7a8 : fetch_word Asan.M.loaded_segments (0xcb7a8 : word) = Some W_cb7a8.
Proof. vm_refl. Qed.
Lemma D_cb7a8 : decode_any W_cb7a8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7ac : bv 32 := 0x19079c63.
Lemma F_cb7ac : fetch_word Asan.M.loaded_segments (0xcb7ac : word) = Some W_cb7ac.
Proof. vm_refl. Qed.
Lemma D_cb7ac : decode_any W_cb7ac = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7b0 : bv 32 := 0x00875793.
Lemma F_cb7b0 : fetch_word Asan.M.loaded_segments (0xcb7b0 : word) = Some W_cb7b0.
Proof. vm_refl. Qed.
Lemma D_cb7b0 : decode_any W_cb7b0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7b4 : bv 32 := 0xffe60613.
Lemma F_cb7b4 : fetch_word Asan.M.loaded_segments (0xcb7b4 : word) = Some W_cb7b4.
Proof. vm_refl. Qed.
Lemma D_cb7b4 : decode_any W_cb7b4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7b8 : bv 32 := 0x00e68023.
Lemma F_cb7b8 : fetch_word Asan.M.loaded_segments (0xcb7b8 : word) = Some W_cb7b8.
Proof. vm_refl. Qed.
Lemma D_cb7b8 : decode_any W_cb7b8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7bc : bv 32 := 0x00f680a3.
Lemma F_cb7bc : fetch_word Asan.M.loaded_segments (0xcb7bc : word) = Some W_cb7bc.
Proof. vm_refl. Qed.
Lemma D_cb7bc : decode_any W_cb7bc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7c0 : bv 32 := 0x00268693.
Lemma F_cb7c0 : fetch_word Asan.M.loaded_segments (0xcb7c0 : word) = Some W_cb7c0.
Proof. vm_refl. Qed.
Lemma D_cb7c0 : decode_any W_cb7c0 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7c4 : bv 32 := 0x01058593.
Lemma F_cb7c4 : fetch_word Asan.M.loaded_segments (0xcb7c4 : word) = Some W_cb7c4.
Proof. vm_refl. Qed.
Lemma D_cb7c4 : decode_any W_cb7c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7c8 : bv 32 := 0x01100793.
Lemma F_cb7c8 : fetch_word Asan.M.loaded_segments (0xcb7c8 : word) = Some W_cb7c8.
Proof. vm_refl. Qed.
Lemma D_cb7c8 : decode_any W_cb7c8 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7cc : bv 32 := 0x0107581b.
Lemma F_cb7cc : fetch_word Asan.M.loaded_segments (0xcb7cc : word) = Some W_cb7cc.
Proof. vm_refl. Qed.
Lemma D_cb7cc : decode_any W_cb7cc = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7d0 : bv 32 := 0xff45a883.
Lemma F_cb7d0 : fetch_word Asan.M.loaded_segments (0xcb7d0 : word) = Some W_cb7d0.
Proof. vm_refl. Qed.
Lemma D_cb7d0 : decode_any W_cb7d0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7d4 : bv 32 := 0xff85a283.
Lemma F_cb7d4 : fetch_word Asan.M.loaded_segments (0xcb7d4 : word) = Some W_cb7d4.
Proof. vm_refl. Qed.
Lemma D_cb7d4 : decode_any W_cb7d4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7d8 : bv 32 := 0xffc5a303.
Lemma F_cb7d8 : fetch_word Asan.M.loaded_segments (0xcb7d8 : word) = Some W_cb7d8.
Proof. vm_refl. Qed.
Lemma D_cb7d8 : decode_any W_cb7d8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7dc : bv 32 := 0x0005a703.
Lemma F_cb7dc : fetch_word Asan.M.loaded_segments (0xcb7dc : word) = Some W_cb7dc.
Proof. vm_refl. Qed.
Lemma D_cb7dc : decode_any W_cb7dc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7e0 : bv 32 := 0x01089393.
Lemma F_cb7e0 : fetch_word Asan.M.loaded_segments (0xcb7e0 : word) = Some W_cb7e0.
Proof. vm_refl. Qed.
Lemma D_cb7e0 : decode_any W_cb7e0 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7e4 : bv 32 := 0x0108d89b.
Lemma F_cb7e4 : fetch_word Asan.M.loaded_segments (0xcb7e4 : word) = Some W_cb7e4.
Proof. vm_refl. Qed.
Lemma D_cb7e4 : decode_any W_cb7e4 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7e8 : bv 32 := 0x0103e833.
Lemma F_cb7e8 : fetch_word Asan.M.loaded_segments (0xcb7e8 : word) = Some W_cb7e8.
Proof. vm_refl. Qed.
Lemma D_cb7e8 : decode_any W_cb7e8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7ec : bv 32 := 0x01029393.
Lemma F_cb7ec : fetch_word Asan.M.loaded_segments (0xcb7ec : word) = Some W_cb7ec.
Proof. vm_refl. Qed.
Lemma D_cb7ec : decode_any W_cb7ec = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7f0 : bv 32 := 0x0102d29b.
Lemma F_cb7f0 : fetch_word Asan.M.loaded_segments (0xcb7f0 : word) = Some W_cb7f0.
Proof. vm_refl. Qed.
Lemma D_cb7f0 : decode_any W_cb7f0 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7f4 : bv 32 := 0x0113e8b3.
Lemma F_cb7f4 : fetch_word Asan.M.loaded_segments (0xcb7f4 : word) = Some W_cb7f4.
Proof. vm_refl. Qed.
Lemma D_cb7f4 : decode_any W_cb7f4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7f8 : bv 32 := 0x01031393.
Lemma F_cb7f8 : fetch_word Asan.M.loaded_segments (0xcb7f8 : word) = Some W_cb7f8.
Proof. vm_refl. Qed.
Lemma D_cb7f8 : decode_any W_cb7f8 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb7fc : bv 32 := 0x0103531b.
Lemma F_cb7fc : fetch_word Asan.M.loaded_segments (0xcb7fc : word) = Some W_cb7fc.
Proof. vm_refl. Qed.
Lemma D_cb7fc : decode_any W_cb7fc = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb800 : bv 32 := 0x0053e2b3.
Lemma F_cb800 : fetch_word Asan.M.loaded_segments (0xcb800 : word) = Some W_cb800.
Proof. vm_refl. Qed.
Lemma D_cb800 : decode_any W_cb800 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb804 : bv 32 := 0x01071393.
Lemma F_cb804 : fetch_word Asan.M.loaded_segments (0xcb804 : word) = Some W_cb804.
Proof. vm_refl. Qed.
Lemma D_cb804 : decode_any W_cb804 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb808 : bv 32 := 0x0063e333.
Lemma F_cb808 : fetch_word Asan.M.loaded_segments (0xcb808 : word) = Some W_cb808.
Proof. vm_refl. Qed.
Lemma D_cb808 : decode_any W_cb808 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb80c : bv 32 := 0xff060613.
Lemma F_cb80c : fetch_word Asan.M.loaded_segments (0xcb80c : word) = Some W_cb80c.
Proof. vm_refl. Qed.
Lemma D_cb80c : decode_any W_cb80c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb810 : bv 32 := 0x0106a023.
Lemma F_cb810 : fetch_word Asan.M.loaded_segments (0xcb810 : word) = Some W_cb810.
Proof. vm_refl. Qed.
Lemma D_cb810 : decode_any W_cb810 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb814 : bv 32 := 0x0116a223.
Lemma F_cb814 : fetch_word Asan.M.loaded_segments (0xcb814 : word) = Some W_cb814.
Proof. vm_refl. Qed.
Lemma D_cb814 : decode_any W_cb814 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb818 : bv 32 := 0x0056a423.
Lemma F_cb818 : fetch_word Asan.M.loaded_segments (0xcb818 : word) = Some W_cb818.
Proof. vm_refl. Qed.
Lemma D_cb818 : decode_any W_cb818 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb81c : bv 32 := 0x0066a623.
Lemma F_cb81c : fetch_word Asan.M.loaded_segments (0xcb81c : word) = Some W_cb81c.
Proof. vm_refl. Qed.
Lemma D_cb81c : decode_any W_cb81c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb820 : bv 32 := 0x01068693.
Lemma F_cb820 : fetch_word Asan.M.loaded_segments (0xcb820 : word) = Some W_cb820.
Proof. vm_refl. Qed.
Lemma D_cb820 : decode_any W_cb820 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb824 : bv 32 := 0x01058593.
Lemma F_cb824 : fetch_word Asan.M.loaded_segments (0xcb824 : word) = Some W_cb824.
Proof. vm_refl. Qed.
Lemma D_cb824 : decode_any W_cb824 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb828 : bv 32 := 0xfac7e2e3.
Lemma F_cb828 : fetch_word Asan.M.loaded_segments (0xcb828 : word) = Some W_cb828.
Proof. vm_refl. Qed.
Lemma D_cb828 : decode_any W_cb828 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb82c : bv 32 := 0xff258593.
Lemma F_cb82c : fetch_word Asan.M.loaded_segments (0xcb82c : word) = Some W_cb82c.
Proof. vm_refl. Qed.
Lemma D_cb82c : decode_any W_cb82c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb830 : bv 32 := 0x01000713.
Lemma F_cb830 : fetch_word Asan.M.loaded_segments (0xcb830 : word) = Some W_cb830.
Proof. vm_refl. Qed.
Lemma D_cb830 : decode_any W_cb830 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb834 : bv 32 := 0xf4e66ae3.
Lemma F_cb834 : fetch_word Asan.M.loaded_segments (0xcb834 : word) = Some W_cb834.
Proof. vm_refl. Qed.
Lemma D_cb834 : decode_any W_cb834 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb838 : bv 32 := 0x19c0006f.
Lemma F_cb838 : fetch_word Asan.M.loaded_segments (0xcb838 : word) = Some W_cb838.
Proof. vm_refl. Qed.
Lemma D_cb838 : decode_any W_cb838 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb83c : bv 32 := 0x00050693.
Lemma F_cb83c : fetch_word Asan.M.loaded_segments (0xcb83c : word) = Some W_cb83c.
Proof. vm_refl. Qed.
Lemma D_cb83c : decode_any W_cb83c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb840 : bv 32 := 0x00357793.
Lemma F_cb840 : fetch_word Asan.M.loaded_segments (0xcb840 : word) = Some W_cb840.
Proof. vm_refl. Qed.
Lemma D_cb840 : decode_any W_cb840 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb844 : bv 32 := 0xf2079ae3.
Lemma F_cb844 : fetch_word Asan.M.loaded_segments (0xcb844 : word) = Some W_cb844.
Proof. vm_refl. Qed.
Lemma D_cb844 : decode_any W_cb844 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb848 : bv 32 := 0x01000713.
Lemma F_cb848 : fetch_word Asan.M.loaded_segments (0xcb848 : word) = Some W_cb848.
Proof. vm_refl. Qed.
Lemma D_cb848 : decode_any W_cb848 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb84c : bv 32 := 0x02e66c63.
Lemma F_cb84c : fetch_word Asan.M.loaded_segments (0xcb84c : word) = Some W_cb84c.
Proof. vm_refl. Qed.
Lemma D_cb84c : decode_any W_cb84c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb850 : bv 32 := 0x00f00713.
Lemma F_cb850 : fetch_word Asan.M.loaded_segments (0xcb850 : word) = Some W_cb850.
Proof. vm_refl. Qed.
Lemma D_cb850 : decode_any W_cb850 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb854 : bv 32 := 0x0005a783.
Lemma F_cb854 : fetch_word Asan.M.loaded_segments (0xcb854 : word) = Some W_cb854.
Proof. vm_refl. Qed.
Lemma D_cb854 : decode_any W_cb854 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb858 : bv 32 := 0x0045a803.
Lemma F_cb858 : fetch_word Asan.M.loaded_segments (0xcb858 : word) = Some W_cb858.
Proof. vm_refl. Qed.
Lemma D_cb858 : decode_any W_cb858 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb85c : bv 32 := 0x0085a883.
Lemma F_cb85c : fetch_word Asan.M.loaded_segments (0xcb85c : word) = Some W_cb85c.
Proof. vm_refl. Qed.
Lemma D_cb85c : decode_any W_cb85c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb860 : bv 32 := 0x00c5a283.
Lemma F_cb860 : fetch_word Asan.M.loaded_segments (0xcb860 : word) = Some W_cb860.
Proof. vm_refl. Qed.
Lemma D_cb860 : decode_any W_cb860 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb864 : bv 32 := 0x01058593.
Lemma F_cb864 : fetch_word Asan.M.loaded_segments (0xcb864 : word) = Some W_cb864.
Proof. vm_refl. Qed.
Lemma D_cb864 : decode_any W_cb864 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb868 : bv 32 := 0xff060613.
Lemma F_cb868 : fetch_word Asan.M.loaded_segments (0xcb868 : word) = Some W_cb868.
Proof. vm_refl. Qed.
Lemma D_cb868 : decode_any W_cb868 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb86c : bv 32 := 0x00f6a023.
Lemma F_cb86c : fetch_word Asan.M.loaded_segments (0xcb86c : word) = Some W_cb86c.
Proof. vm_refl. Qed.
Lemma D_cb86c : decode_any W_cb86c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb870 : bv 32 := 0x0106a223.
Lemma F_cb870 : fetch_word Asan.M.loaded_segments (0xcb870 : word) = Some W_cb870.
Proof. vm_refl. Qed.
Lemma D_cb870 : decode_any W_cb870 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb874 : bv 32 := 0x0116a423.
Lemma F_cb874 : fetch_word Asan.M.loaded_segments (0xcb874 : word) = Some W_cb874.
Proof. vm_refl. Qed.
Lemma D_cb874 : decode_any W_cb874 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb878 : bv 32 := 0x0056a623.
Lemma F_cb878 : fetch_word Asan.M.loaded_segments (0xcb878 : word) = Some W_cb878.
Proof. vm_refl. Qed.
Lemma D_cb878 : decode_any W_cb878 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb87c : bv 32 := 0x01068693.
Lemma F_cb87c : fetch_word Asan.M.loaded_segments (0xcb87c : word) = Some W_cb87c.
Proof. vm_refl. Qed.
Lemma D_cb87c : decode_any W_cb87c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb880 : bv 32 := 0xfcc76ae3.
Lemma F_cb880 : fetch_word Asan.M.loaded_segments (0xcb880 : word) = Some W_cb880.
Proof. vm_refl. Qed.
Lemma D_cb880 : decode_any W_cb880 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb884 : bv 32 := 0x00800713.
Lemma F_cb884 : fetch_word Asan.M.loaded_segments (0xcb884 : word) = Some W_cb884.
Proof. vm_refl. Qed.
Lemma D_cb884 : decode_any W_cb884 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb888 : bv 32 := 0x00e66e63.
Lemma F_cb888 : fetch_word Asan.M.loaded_segments (0xcb888 : word) = Some W_cb888.
Proof. vm_refl. Qed.
Lemma D_cb888 : decode_any W_cb888 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb88c : bv 32 := 0x0005a703.
Lemma F_cb88c : fetch_word Asan.M.loaded_segments (0xcb88c : word) = Some W_cb88c.
Proof. vm_refl. Qed.
Lemma D_cb88c : decode_any W_cb88c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb890 : bv 32 := 0x0045a783.
Lemma F_cb890 : fetch_word Asan.M.loaded_segments (0xcb890 : word) = Some W_cb890.
Proof. vm_refl. Qed.
Lemma D_cb890 : decode_any W_cb890 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb894 : bv 32 := 0x00e6a023.
Lemma F_cb894 : fetch_word Asan.M.loaded_segments (0xcb894 : word) = Some W_cb894.
Proof. vm_refl. Qed.
Lemma D_cb894 : decode_any W_cb894 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb898 : bv 32 := 0x00f6a223.
Lemma F_cb898 : fetch_word Asan.M.loaded_segments (0xcb898 : word) = Some W_cb898.
Proof. vm_refl. Qed.
Lemma D_cb898 : decode_any W_cb898 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb89c : bv 32 := 0x00868693.
Lemma F_cb89c : fetch_word Asan.M.loaded_segments (0xcb89c : word) = Some W_cb89c.
Proof. vm_refl. Qed.
Lemma D_cb89c : decode_any W_cb89c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8a0 : bv 32 := 0x00858593.
Lemma F_cb8a0 : fetch_word Asan.M.loaded_segments (0xcb8a0 : word) = Some W_cb8a0.
Proof. vm_refl. Qed.
Lemma D_cb8a0 : decode_any W_cb8a0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8a4 : bv 32 := 0x00467713.
Lemma F_cb8a4 : fetch_word Asan.M.loaded_segments (0xcb8a4 : word) = Some W_cb8a4.
Proof. vm_refl. Qed.
Lemma D_cb8a4 : decode_any W_cb8a4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8a8 : bv 32 := 0x24070063.
Lemma F_cb8a8 : fetch_word Asan.M.loaded_segments (0xcb8a8 : word) = Some W_cb8a8.
Proof. vm_refl. Qed.
Lemma D_cb8a8 : decode_any W_cb8a8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8ac : bv 32 := 0x0005a703.
Lemma F_cb8ac : fetch_word Asan.M.loaded_segments (0xcb8ac : word) = Some W_cb8ac.
Proof. vm_refl. Qed.
Lemma D_cb8ac : decode_any W_cb8ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8b0 : bv 32 := 0x00458593.
Lemma F_cb8b0 : fetch_word Asan.M.loaded_segments (0xcb8b0 : word) = Some W_cb8b0.
Proof. vm_refl. Qed.
Lemma D_cb8b0 : decode_any W_cb8b0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8b4 : bv 32 := 0x00e6a023.
Lemma F_cb8b4 : fetch_word Asan.M.loaded_segments (0xcb8b4 : word) = Some W_cb8b4.
Proof. vm_refl. Qed.
Lemma D_cb8b4 : decode_any W_cb8b4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8b8 : bv 32 := 0x00468693.
Lemma F_cb8b8 : fetch_word Asan.M.loaded_segments (0xcb8b8 : word) = Some W_cb8b8.
Proof. vm_refl. Qed.
Lemma D_cb8b8 : decode_any W_cb8b8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8bc : bv 32 := 0x22c0006f.
Lemma F_cb8bc : fetch_word Asan.M.loaded_segments (0xcb8bc : word) = Some W_cb8bc.
Proof. vm_refl. Qed.
Lemma D_cb8bc : decode_any W_cb8bc = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8c0 : bv 32 := 0x00e68023.
Lemma F_cb8c0 : fetch_word Asan.M.loaded_segments (0xcb8c0 : word) = Some W_cb8c0.
Proof. vm_refl. Qed.
Lemma D_cb8c0 : decode_any W_cb8c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8c4 : bv 32 := 0x00168693.
Lemma F_cb8c4 : fetch_word Asan.M.loaded_segments (0xcb8c4 : word) = Some W_cb8c4.
Proof. vm_refl. Qed.
Lemma D_cb8c4 : decode_any W_cb8c4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8c8 : bv 32 := 0xfff60613.
Lemma F_cb8c8 : fetch_word Asan.M.loaded_segments (0xcb8c8 : word) = Some W_cb8c8.
Proof. vm_refl. Qed.
Lemma D_cb8c8 : decode_any W_cb8c8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8cc : bv 32 := 0x01058593.
Lemma F_cb8cc : fetch_word Asan.M.loaded_segments (0xcb8cc : word) = Some W_cb8cc.
Proof. vm_refl. Qed.
Lemma D_cb8cc : decode_any W_cb8cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8d0 : bv 32 := 0x01200793.
Lemma F_cb8d0 : fetch_word Asan.M.loaded_segments (0xcb8d0 : word) = Some W_cb8d0.
Proof. vm_refl. Qed.
Lemma D_cb8d0 : decode_any W_cb8d0 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8d4 : bv 32 := 0x0087581b.
Lemma F_cb8d4 : fetch_word Asan.M.loaded_segments (0xcb8d4 : word) = Some W_cb8d4.
Proof. vm_refl. Qed.
Lemma D_cb8d4 : decode_any W_cb8d4 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8d8 : bv 32 := 0xff45a883.
Lemma F_cb8d8 : fetch_word Asan.M.loaded_segments (0xcb8d8 : word) = Some W_cb8d8.
Proof. vm_refl. Qed.
Lemma D_cb8d8 : decode_any W_cb8d8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8dc : bv 32 := 0xff85a283.
Lemma F_cb8dc : fetch_word Asan.M.loaded_segments (0xcb8dc : word) = Some W_cb8dc.
Proof. vm_refl. Qed.
Lemma D_cb8dc : decode_any W_cb8dc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8e0 : bv 32 := 0xffc5a303.
Lemma F_cb8e0 : fetch_word Asan.M.loaded_segments (0xcb8e0 : word) = Some W_cb8e0.
Proof. vm_refl. Qed.
Lemma D_cb8e0 : decode_any W_cb8e0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8e4 : bv 32 := 0x0005a703.
Lemma F_cb8e4 : fetch_word Asan.M.loaded_segments (0xcb8e4 : word) = Some W_cb8e4.
Proof. vm_refl. Qed.
Lemma D_cb8e4 : decode_any W_cb8e4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8e8 : bv 32 := 0x01889393.
Lemma F_cb8e8 : fetch_word Asan.M.loaded_segments (0xcb8e8 : word) = Some W_cb8e8.
Proof. vm_refl. Qed.
Lemma D_cb8e8 : decode_any W_cb8e8 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8ec : bv 32 := 0x0088d89b.
Lemma F_cb8ec : fetch_word Asan.M.loaded_segments (0xcb8ec : word) = Some W_cb8ec.
Proof. vm_refl. Qed.
Lemma D_cb8ec : decode_any W_cb8ec = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8f0 : bv 32 := 0x0103e833.
Lemma F_cb8f0 : fetch_word Asan.M.loaded_segments (0xcb8f0 : word) = Some W_cb8f0.
Proof. vm_refl. Qed.
Lemma D_cb8f0 : decode_any W_cb8f0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8f4 : bv 32 := 0x01829393.
Lemma F_cb8f4 : fetch_word Asan.M.loaded_segments (0xcb8f4 : word) = Some W_cb8f4.
Proof. vm_refl. Qed.
Lemma D_cb8f4 : decode_any W_cb8f4 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8f8 : bv 32 := 0x0082d29b.
Lemma F_cb8f8 : fetch_word Asan.M.loaded_segments (0xcb8f8 : word) = Some W_cb8f8.
Proof. vm_refl. Qed.
Lemma D_cb8f8 : decode_any W_cb8f8 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb8fc : bv 32 := 0x0113e8b3.
Lemma F_cb8fc : fetch_word Asan.M.loaded_segments (0xcb8fc : word) = Some W_cb8fc.
Proof. vm_refl. Qed.
Lemma D_cb8fc : decode_any W_cb8fc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb900 : bv 32 := 0x01831393.
Lemma F_cb900 : fetch_word Asan.M.loaded_segments (0xcb900 : word) = Some W_cb900.
Proof. vm_refl. Qed.
Lemma D_cb900 : decode_any W_cb900 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb904 : bv 32 := 0x0083531b.
Lemma F_cb904 : fetch_word Asan.M.loaded_segments (0xcb904 : word) = Some W_cb904.
Proof. vm_refl. Qed.
Lemma D_cb904 : decode_any W_cb904 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb908 : bv 32 := 0x0053e2b3.
Lemma F_cb908 : fetch_word Asan.M.loaded_segments (0xcb908 : word) = Some W_cb908.
Proof. vm_refl. Qed.
Lemma D_cb908 : decode_any W_cb908 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb90c : bv 32 := 0x01871393.
Lemma F_cb90c : fetch_word Asan.M.loaded_segments (0xcb90c : word) = Some W_cb90c.
Proof. vm_refl. Qed.
Lemma D_cb90c : decode_any W_cb90c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb910 : bv 32 := 0x0063e333.
Lemma F_cb910 : fetch_word Asan.M.loaded_segments (0xcb910 : word) = Some W_cb910.
Proof. vm_refl. Qed.
Lemma D_cb910 : decode_any W_cb910 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb914 : bv 32 := 0xff060613.
Lemma F_cb914 : fetch_word Asan.M.loaded_segments (0xcb914 : word) = Some W_cb914.
Proof. vm_refl. Qed.
Lemma D_cb914 : decode_any W_cb914 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb918 : bv 32 := 0x0106a023.
Lemma F_cb918 : fetch_word Asan.M.loaded_segments (0xcb918 : word) = Some W_cb918.
Proof. vm_refl. Qed.
Lemma D_cb918 : decode_any W_cb918 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb91c : bv 32 := 0x0116a223.
Lemma F_cb91c : fetch_word Asan.M.loaded_segments (0xcb91c : word) = Some W_cb91c.
Proof. vm_refl. Qed.
Lemma D_cb91c : decode_any W_cb91c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb920 : bv 32 := 0x0056a423.
Lemma F_cb920 : fetch_word Asan.M.loaded_segments (0xcb920 : word) = Some W_cb920.
Proof. vm_refl. Qed.
Lemma D_cb920 : decode_any W_cb920 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb924 : bv 32 := 0x0066a623.
Lemma F_cb924 : fetch_word Asan.M.loaded_segments (0xcb924 : word) = Some W_cb924.
Proof. vm_refl. Qed.
Lemma D_cb924 : decode_any W_cb924 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb928 : bv 32 := 0x01068693.
Lemma F_cb928 : fetch_word Asan.M.loaded_segments (0xcb928 : word) = Some W_cb928.
Proof. vm_refl. Qed.
Lemma D_cb928 : decode_any W_cb928 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb92c : bv 32 := 0x01058593.
Lemma F_cb92c : fetch_word Asan.M.loaded_segments (0xcb92c : word) = Some W_cb92c.
Proof. vm_refl. Qed.
Lemma D_cb92c : decode_any W_cb92c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb930 : bv 32 := 0xfac7e2e3.
Lemma F_cb930 : fetch_word Asan.M.loaded_segments (0xcb930 : word) = Some W_cb930.
Proof. vm_refl. Qed.
Lemma D_cb930 : decode_any W_cb930 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb934 : bv 32 := 0xff158593.
Lemma F_cb934 : fetch_word Asan.M.loaded_segments (0xcb934 : word) = Some W_cb934.
Proof. vm_refl. Qed.
Lemma D_cb934 : decode_any W_cb934 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb938 : bv 32 := 0x01000713.
Lemma F_cb938 : fetch_word Asan.M.loaded_segments (0xcb938 : word) = Some W_cb938.
Proof. vm_refl. Qed.
Lemma D_cb938 : decode_any W_cb938 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb93c : bv 32 := 0xe4e666e3.
Lemma F_cb93c : fetch_word Asan.M.loaded_segments (0xcb93c : word) = Some W_cb93c.
Proof. vm_refl. Qed.
Lemma D_cb93c : decode_any W_cb93c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb940 : bv 32 := 0x0940006f.
Lemma F_cb940 : fetch_word Asan.M.loaded_segments (0xcb940 : word) = Some W_cb940.
Proof. vm_refl. Qed.
Lemma D_cb940 : decode_any W_cb940 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb944 : bv 32 := 0x00875793.
Lemma F_cb944 : fetch_word Asan.M.loaded_segments (0xcb944 : word) = Some W_cb944.
Proof. vm_refl. Qed.
Lemma D_cb944 : decode_any W_cb944 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb948 : bv 32 := 0x01075813.
Lemma F_cb948 : fetch_word Asan.M.loaded_segments (0xcb948 : word) = Some W_cb948.
Proof. vm_refl. Qed.
Lemma D_cb948 : decode_any W_cb948 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb94c : bv 32 := 0xffd60613.
Lemma F_cb94c : fetch_word Asan.M.loaded_segments (0xcb94c : word) = Some W_cb94c.
Proof. vm_refl. Qed.
Lemma D_cb94c : decode_any W_cb94c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb950 : bv 32 := 0x00e68023.
Lemma F_cb950 : fetch_word Asan.M.loaded_segments (0xcb950 : word) = Some W_cb950.
Proof. vm_refl. Qed.
Lemma D_cb950 : decode_any W_cb950 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb954 : bv 32 := 0x00f680a3.
Lemma F_cb954 : fetch_word Asan.M.loaded_segments (0xcb954 : word) = Some W_cb954.
Proof. vm_refl. Qed.
Lemma D_cb954 : decode_any W_cb954 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb958 : bv 32 := 0x01068123.
Lemma F_cb958 : fetch_word Asan.M.loaded_segments (0xcb958 : word) = Some W_cb958.
Proof. vm_refl. Qed.
Lemma D_cb958 : decode_any W_cb958 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb95c : bv 32 := 0x00368693.
Lemma F_cb95c : fetch_word Asan.M.loaded_segments (0xcb95c : word) = Some W_cb95c.
Proof. vm_refl. Qed.
Lemma D_cb95c : decode_any W_cb95c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb960 : bv 32 := 0x01058593.
Lemma F_cb960 : fetch_word Asan.M.loaded_segments (0xcb960 : word) = Some W_cb960.
Proof. vm_refl. Qed.
Lemma D_cb960 : decode_any W_cb960 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb964 : bv 32 := 0x01000793.
Lemma F_cb964 : fetch_word Asan.M.loaded_segments (0xcb964 : word) = Some W_cb964.
Proof. vm_refl. Qed.
Lemma D_cb964 : decode_any W_cb964 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb968 : bv 32 := 0x0187581b.
Lemma F_cb968 : fetch_word Asan.M.loaded_segments (0xcb968 : word) = Some W_cb968.
Proof. vm_refl. Qed.
Lemma D_cb968 : decode_any W_cb968 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb96c : bv 32 := 0xff45a883.
Lemma F_cb96c : fetch_word Asan.M.loaded_segments (0xcb96c : word) = Some W_cb96c.
Proof. vm_refl. Qed.
Lemma D_cb96c : decode_any W_cb96c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb970 : bv 32 := 0xff85a283.
Lemma F_cb970 : fetch_word Asan.M.loaded_segments (0xcb970 : word) = Some W_cb970.
Proof. vm_refl. Qed.
Lemma D_cb970 : decode_any W_cb970 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb974 : bv 32 := 0xffc5a303.
Lemma F_cb974 : fetch_word Asan.M.loaded_segments (0xcb974 : word) = Some W_cb974.
Proof. vm_refl. Qed.
Lemma D_cb974 : decode_any W_cb974 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb978 : bv 32 := 0x0005a703.
Lemma F_cb978 : fetch_word Asan.M.loaded_segments (0xcb978 : word) = Some W_cb978.
Proof. vm_refl. Qed.
Lemma D_cb978 : decode_any W_cb978 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb97c : bv 32 := 0x00889393.
Lemma F_cb97c : fetch_word Asan.M.loaded_segments (0xcb97c : word) = Some W_cb97c.
Proof. vm_refl. Qed.
Lemma D_cb97c : decode_any W_cb97c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb980 : bv 32 := 0x0188d89b.
Lemma F_cb980 : fetch_word Asan.M.loaded_segments (0xcb980 : word) = Some W_cb980.
Proof. vm_refl. Qed.
Lemma D_cb980 : decode_any W_cb980 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb984 : bv 32 := 0x0103e833.
Lemma F_cb984 : fetch_word Asan.M.loaded_segments (0xcb984 : word) = Some W_cb984.
Proof. vm_refl. Qed.
Lemma D_cb984 : decode_any W_cb984 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb988 : bv 32 := 0x00829393.
Lemma F_cb988 : fetch_word Asan.M.loaded_segments (0xcb988 : word) = Some W_cb988.
Proof. vm_refl. Qed.
Lemma D_cb988 : decode_any W_cb988 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb98c : bv 32 := 0x0182d29b.
Lemma F_cb98c : fetch_word Asan.M.loaded_segments (0xcb98c : word) = Some W_cb98c.
Proof. vm_refl. Qed.
Lemma D_cb98c : decode_any W_cb98c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb990 : bv 32 := 0x0113e8b3.
Lemma F_cb990 : fetch_word Asan.M.loaded_segments (0xcb990 : word) = Some W_cb990.
Proof. vm_refl. Qed.
Lemma D_cb990 : decode_any W_cb990 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb994 : bv 32 := 0x00831393.
Lemma F_cb994 : fetch_word Asan.M.loaded_segments (0xcb994 : word) = Some W_cb994.
Proof. vm_refl. Qed.
Lemma D_cb994 : decode_any W_cb994 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb998 : bv 32 := 0x0183531b.
Lemma F_cb998 : fetch_word Asan.M.loaded_segments (0xcb998 : word) = Some W_cb998.
Proof. vm_refl. Qed.
Lemma D_cb998 : decode_any W_cb998 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb99c : bv 32 := 0x0053e2b3.
Lemma F_cb99c : fetch_word Asan.M.loaded_segments (0xcb99c : word) = Some W_cb99c.
Proof. vm_refl. Qed.
Lemma D_cb99c : decode_any W_cb99c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9a0 : bv 32 := 0x00871393.
Lemma F_cb9a0 : fetch_word Asan.M.loaded_segments (0xcb9a0 : word) = Some W_cb9a0.
Proof. vm_refl. Qed.
Lemma D_cb9a0 : decode_any W_cb9a0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9a4 : bv 32 := 0x0063e333.
Lemma F_cb9a4 : fetch_word Asan.M.loaded_segments (0xcb9a4 : word) = Some W_cb9a4.
Proof. vm_refl. Qed.
Lemma D_cb9a4 : decode_any W_cb9a4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9a8 : bv 32 := 0xff060613.
Lemma F_cb9a8 : fetch_word Asan.M.loaded_segments (0xcb9a8 : word) = Some W_cb9a8.
Proof. vm_refl. Qed.
Lemma D_cb9a8 : decode_any W_cb9a8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9ac : bv 32 := 0x0106a023.
Lemma F_cb9ac : fetch_word Asan.M.loaded_segments (0xcb9ac : word) = Some W_cb9ac.
Proof. vm_refl. Qed.
Lemma D_cb9ac : decode_any W_cb9ac = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9b0 : bv 32 := 0x0116a223.
Lemma F_cb9b0 : fetch_word Asan.M.loaded_segments (0xcb9b0 : word) = Some W_cb9b0.
Proof. vm_refl. Qed.
Lemma D_cb9b0 : decode_any W_cb9b0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9b4 : bv 32 := 0x0056a423.
Lemma F_cb9b4 : fetch_word Asan.M.loaded_segments (0xcb9b4 : word) = Some W_cb9b4.
Proof. vm_refl. Qed.
Lemma D_cb9b4 : decode_any W_cb9b4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9b8 : bv 32 := 0x0066a623.
Lemma F_cb9b8 : fetch_word Asan.M.loaded_segments (0xcb9b8 : word) = Some W_cb9b8.
Proof. vm_refl. Qed.
Lemma D_cb9b8 : decode_any W_cb9b8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9bc : bv 32 := 0x01068693.
Lemma F_cb9bc : fetch_word Asan.M.loaded_segments (0xcb9bc : word) = Some W_cb9bc.
Proof. vm_refl. Qed.
Lemma D_cb9bc : decode_any W_cb9bc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9c0 : bv 32 := 0x01058593.
Lemma F_cb9c0 : fetch_word Asan.M.loaded_segments (0xcb9c0 : word) = Some W_cb9c0.
Proof. vm_refl. Qed.
Lemma D_cb9c0 : decode_any W_cb9c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9c4 : bv 32 := 0xfac7e2e3.
Lemma F_cb9c4 : fetch_word Asan.M.loaded_segments (0xcb9c4 : word) = Some W_cb9c4.
Proof. vm_refl. Qed.
Lemma D_cb9c4 : decode_any W_cb9c4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9c8 : bv 32 := 0xff358593.
Lemma F_cb9c8 : fetch_word Asan.M.loaded_segments (0xcb9c8 : word) = Some W_cb9c8.
Proof. vm_refl. Qed.
Lemma D_cb9c8 : decode_any W_cb9c8 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9cc : bv 32 := 0x01000713.
Lemma F_cb9cc : fetch_word Asan.M.loaded_segments (0xcb9cc : word) = Some W_cb9cc.
Proof. vm_refl. Qed.
Lemma D_cb9cc : decode_any W_cb9cc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9d0 : bv 32 := 0xdae66ce3.
Lemma F_cb9d0 : fetch_word Asan.M.loaded_segments (0xcb9d0 : word) = Some W_cb9d0.
Proof. vm_refl. Qed.
Lemma D_cb9d0 : decode_any W_cb9d0 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9d4 : bv 32 := 0x0005c703.
Lemma F_cb9d4 : fetch_word Asan.M.loaded_segments (0xcb9d4 : word) = Some W_cb9d4.
Proof. vm_refl. Qed.
Lemma D_cb9d4 : decode_any W_cb9d4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9d8 : bv 32 := 0x0015c783.
Lemma F_cb9d8 : fetch_word Asan.M.loaded_segments (0xcb9d8 : word) = Some W_cb9d8.
Proof. vm_refl. Qed.
Lemma D_cb9d8 : decode_any W_cb9d8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9dc : bv 32 := 0x0025c803.
Lemma F_cb9dc : fetch_word Asan.M.loaded_segments (0xcb9dc : word) = Some W_cb9dc.
Proof. vm_refl. Qed.
Lemma D_cb9dc : decode_any W_cb9dc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9e0 : bv 32 := 0x0035c883.
Lemma F_cb9e0 : fetch_word Asan.M.loaded_segments (0xcb9e0 : word) = Some W_cb9e0.
Proof. vm_refl. Qed.
Lemma D_cb9e0 : decode_any W_cb9e0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9e4 : bv 32 := 0x0045c283.
Lemma F_cb9e4 : fetch_word Asan.M.loaded_segments (0xcb9e4 : word) = Some W_cb9e4.
Proof. vm_refl. Qed.
Lemma D_cb9e4 : decode_any W_cb9e4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9e8 : bv 32 := 0x0055c303.
Lemma F_cb9e8 : fetch_word Asan.M.loaded_segments (0xcb9e8 : word) = Some W_cb9e8.
Proof. vm_refl. Qed.
Lemma D_cb9e8 : decode_any W_cb9e8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9ec : bv 32 := 0x0065c383.
Lemma F_cb9ec : fetch_word Asan.M.loaded_segments (0xcb9ec : word) = Some W_cb9ec.
Proof. vm_refl. Qed.
Lemma D_cb9ec : decode_any W_cb9ec = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9f0 : bv 32 := 0x0075ce03.
Lemma F_cb9f0 : fetch_word Asan.M.loaded_segments (0xcb9f0 : word) = Some W_cb9f0.
Proof. vm_refl. Qed.
Lemma D_cb9f0 : decode_any W_cb9f0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9f4 : bv 32 := 0x00e68023.
Lemma F_cb9f4 : fetch_word Asan.M.loaded_segments (0xcb9f4 : word) = Some W_cb9f4.
Proof. vm_refl. Qed.
Lemma D_cb9f4 : decode_any W_cb9f4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9f8 : bv 32 := 0x00f680a3.
Lemma F_cb9f8 : fetch_word Asan.M.loaded_segments (0xcb9f8 : word) = Some W_cb9f8.
Proof. vm_refl. Qed.
Lemma D_cb9f8 : decode_any W_cb9f8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cb9fc : bv 32 := 0x01068123.
Lemma F_cb9fc : fetch_word Asan.M.loaded_segments (0xcb9fc : word) = Some W_cb9fc.
Proof. vm_refl. Qed.
Lemma D_cb9fc : decode_any W_cb9fc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba00 : bv 32 := 0x011681a3.
Lemma F_cba00 : fetch_word Asan.M.loaded_segments (0xcba00 : word) = Some W_cba00.
Proof. vm_refl. Qed.
Lemma D_cba00 : decode_any W_cba00 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba04 : bv 32 := 0x0085c703.
Lemma F_cba04 : fetch_word Asan.M.loaded_segments (0xcba04 : word) = Some W_cba04.
Proof. vm_refl. Qed.
Lemma D_cba04 : decode_any W_cba04 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba08 : bv 32 := 0x0095c783.
Lemma F_cba08 : fetch_word Asan.M.loaded_segments (0xcba08 : word) = Some W_cba08.
Proof. vm_refl. Qed.
Lemma D_cba08 : decode_any W_cba08 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba0c : bv 32 := 0x00a5c803.
Lemma F_cba0c : fetch_word Asan.M.loaded_segments (0xcba0c : word) = Some W_cba0c.
Proof. vm_refl. Qed.
Lemma D_cba0c : decode_any W_cba0c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba10 : bv 32 := 0x00b5c883.
Lemma F_cba10 : fetch_word Asan.M.loaded_segments (0xcba10 : word) = Some W_cba10.
Proof. vm_refl. Qed.
Lemma D_cba10 : decode_any W_cba10 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba14 : bv 32 := 0x00568223.
Lemma F_cba14 : fetch_word Asan.M.loaded_segments (0xcba14 : word) = Some W_cba14.
Proof. vm_refl. Qed.
Lemma D_cba14 : decode_any W_cba14 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba18 : bv 32 := 0x006682a3.
Lemma F_cba18 : fetch_word Asan.M.loaded_segments (0xcba18 : word) = Some W_cba18.
Proof. vm_refl. Qed.
Lemma D_cba18 : decode_any W_cba18 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba1c : bv 32 := 0x00768323.
Lemma F_cba1c : fetch_word Asan.M.loaded_segments (0xcba1c : word) = Some W_cba1c.
Proof. vm_refl. Qed.
Lemma D_cba1c : decode_any W_cba1c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba20 : bv 32 := 0x01c683a3.
Lemma F_cba20 : fetch_word Asan.M.loaded_segments (0xcba20 : word) = Some W_cba20.
Proof. vm_refl. Qed.
Lemma D_cba20 : decode_any W_cba20 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba24 : bv 32 := 0x00c5c283.
Lemma F_cba24 : fetch_word Asan.M.loaded_segments (0xcba24 : word) = Some W_cba24.
Proof. vm_refl. Qed.
Lemma D_cba24 : decode_any W_cba24 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba28 : bv 32 := 0x00d5c303.
Lemma F_cba28 : fetch_word Asan.M.loaded_segments (0xcba28 : word) = Some W_cba28.
Proof. vm_refl. Qed.
Lemma D_cba28 : decode_any W_cba28 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba2c : bv 32 := 0x00e5c383.
Lemma F_cba2c : fetch_word Asan.M.loaded_segments (0xcba2c : word) = Some W_cba2c.
Proof. vm_refl. Qed.
Lemma D_cba2c : decode_any W_cba2c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba30 : bv 32 := 0x00f5ce03.
Lemma F_cba30 : fetch_word Asan.M.loaded_segments (0xcba30 : word) = Some W_cba30.
Proof. vm_refl. Qed.
Lemma D_cba30 : decode_any W_cba30 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba34 : bv 32 := 0x01058593.
Lemma F_cba34 : fetch_word Asan.M.loaded_segments (0xcba34 : word) = Some W_cba34.
Proof. vm_refl. Qed.
Lemma D_cba34 : decode_any W_cba34 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba38 : bv 32 := 0x00e68423.
Lemma F_cba38 : fetch_word Asan.M.loaded_segments (0xcba38 : word) = Some W_cba38.
Proof. vm_refl. Qed.
Lemma D_cba38 : decode_any W_cba38 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba3c : bv 32 := 0x00f684a3.
Lemma F_cba3c : fetch_word Asan.M.loaded_segments (0xcba3c : word) = Some W_cba3c.
Proof. vm_refl. Qed.
Lemma D_cba3c : decode_any W_cba3c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba40 : bv 32 := 0x01068523.
Lemma F_cba40 : fetch_word Asan.M.loaded_segments (0xcba40 : word) = Some W_cba40.
Proof. vm_refl. Qed.
Lemma D_cba40 : decode_any W_cba40 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba44 : bv 32 := 0x011685a3.
Lemma F_cba44 : fetch_word Asan.M.loaded_segments (0xcba44 : word) = Some W_cba44.
Proof. vm_refl. Qed.
Lemma D_cba44 : decode_any W_cba44 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba48 : bv 32 := 0x01068713.
Lemma F_cba48 : fetch_word Asan.M.loaded_segments (0xcba48 : word) = Some W_cba48.
Proof. vm_refl. Qed.
Lemma D_cba48 : decode_any W_cba48 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba4c : bv 32 := 0x00568623.
Lemma F_cba4c : fetch_word Asan.M.loaded_segments (0xcba4c : word) = Some W_cba4c.
Proof. vm_refl. Qed.
Lemma D_cba4c : decode_any W_cba4c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba50 : bv 32 := 0x006686a3.
Lemma F_cba50 : fetch_word Asan.M.loaded_segments (0xcba50 : word) = Some W_cba50.
Proof. vm_refl. Qed.
Lemma D_cba50 : decode_any W_cba50 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba54 : bv 32 := 0x00768723.
Lemma F_cba54 : fetch_word Asan.M.loaded_segments (0xcba54 : word) = Some W_cba54.
Proof. vm_refl. Qed.
Lemma D_cba54 : decode_any W_cba54 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba58 : bv 32 := 0x01c687a3.
Lemma F_cba58 : fetch_word Asan.M.loaded_segments (0xcba58 : word) = Some W_cba58.
Proof. vm_refl. Qed.
Lemma D_cba58 : decode_any W_cba58 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba5c : bv 32 := 0x00070693.
Lemma F_cba5c : fetch_word Asan.M.loaded_segments (0xcba5c : word) = Some W_cba5c.
Proof. vm_refl. Qed.
Lemma D_cba5c : decode_any W_cba5c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba60 : bv 32 := 0x00867713.
Lemma F_cba60 : fetch_word Asan.M.loaded_segments (0xcba60 : word) = Some W_cba60.
Proof. vm_refl. Qed.
Lemma D_cba60 : decode_any W_cba60 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba64 : bv 32 := 0xd20706e3.
Lemma F_cba64 : fetch_word Asan.M.loaded_segments (0xcba64 : word) = Some W_cba64.
Proof. vm_refl. Qed.
Lemma D_cba64 : decode_any W_cba64 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba68 : bv 32 := 0x0005c703.
Lemma F_cba68 : fetch_word Asan.M.loaded_segments (0xcba68 : word) = Some W_cba68.
Proof. vm_refl. Qed.
Lemma D_cba68 : decode_any W_cba68 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba6c : bv 32 := 0x0015c783.
Lemma F_cba6c : fetch_word Asan.M.loaded_segments (0xcba6c : word) = Some W_cba6c.
Proof. vm_refl. Qed.
Lemma D_cba6c : decode_any W_cba6c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba70 : bv 32 := 0x0025c803.
Lemma F_cba70 : fetch_word Asan.M.loaded_segments (0xcba70 : word) = Some W_cba70.
Proof. vm_refl. Qed.
Lemma D_cba70 : decode_any W_cba70 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba74 : bv 32 := 0x0035c883.
Lemma F_cba74 : fetch_word Asan.M.loaded_segments (0xcba74 : word) = Some W_cba74.
Proof. vm_refl. Qed.
Lemma D_cba74 : decode_any W_cba74 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba78 : bv 32 := 0x0045c283.
Lemma F_cba78 : fetch_word Asan.M.loaded_segments (0xcba78 : word) = Some W_cba78.
Proof. vm_refl. Qed.
Lemma D_cba78 : decode_any W_cba78 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba7c : bv 32 := 0x0055c303.
Lemma F_cba7c : fetch_word Asan.M.loaded_segments (0xcba7c : word) = Some W_cba7c.
Proof. vm_refl. Qed.
Lemma D_cba7c : decode_any W_cba7c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba80 : bv 32 := 0x0065c383.
Lemma F_cba80 : fetch_word Asan.M.loaded_segments (0xcba80 : word) = Some W_cba80.
Proof. vm_refl. Qed.
Lemma D_cba80 : decode_any W_cba80 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba84 : bv 32 := 0x0075ce03.
Lemma F_cba84 : fetch_word Asan.M.loaded_segments (0xcba84 : word) = Some W_cba84.
Proof. vm_refl. Qed.
Lemma D_cba84 : decode_any W_cba84 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba88 : bv 32 := 0x00858593.
Lemma F_cba88 : fetch_word Asan.M.loaded_segments (0xcba88 : word) = Some W_cba88.
Proof. vm_refl. Qed.
Lemma D_cba88 : decode_any W_cba88 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba8c : bv 32 := 0x00e68023.
Lemma F_cba8c : fetch_word Asan.M.loaded_segments (0xcba8c : word) = Some W_cba8c.
Proof. vm_refl. Qed.
Lemma D_cba8c : decode_any W_cba8c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba90 : bv 32 := 0x00f680a3.
Lemma F_cba90 : fetch_word Asan.M.loaded_segments (0xcba90 : word) = Some W_cba90.
Proof. vm_refl. Qed.
Lemma D_cba90 : decode_any W_cba90 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba94 : bv 32 := 0x01068123.
Lemma F_cba94 : fetch_word Asan.M.loaded_segments (0xcba94 : word) = Some W_cba94.
Proof. vm_refl. Qed.
Lemma D_cba94 : decode_any W_cba94 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba98 : bv 32 := 0x011681a3.
Lemma F_cba98 : fetch_word Asan.M.loaded_segments (0xcba98 : word) = Some W_cba98.
Proof. vm_refl. Qed.
Lemma D_cba98 : decode_any W_cba98 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cba9c : bv 32 := 0x00868713.
Lemma F_cba9c : fetch_word Asan.M.loaded_segments (0xcba9c : word) = Some W_cba9c.
Proof. vm_refl. Qed.
Lemma D_cba9c : decode_any W_cba9c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaa0 : bv 32 := 0x00568223.
Lemma F_cbaa0 : fetch_word Asan.M.loaded_segments (0xcbaa0 : word) = Some W_cbaa0.
Proof. vm_refl. Qed.
Lemma D_cbaa0 : decode_any W_cbaa0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaa4 : bv 32 := 0x006682a3.
Lemma F_cbaa4 : fetch_word Asan.M.loaded_segments (0xcbaa4 : word) = Some W_cbaa4.
Proof. vm_refl. Qed.
Lemma D_cbaa4 : decode_any W_cbaa4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaa8 : bv 32 := 0x00768323.
Lemma F_cbaa8 : fetch_word Asan.M.loaded_segments (0xcbaa8 : word) = Some W_cbaa8.
Proof. vm_refl. Qed.
Lemma D_cbaa8 : decode_any W_cbaa8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaac : bv 32 := 0x01c683a3.
Lemma F_cbaac : fetch_word Asan.M.loaded_segments (0xcbaac : word) = Some W_cbaac.
Proof. vm_refl. Qed.
Lemma D_cbaac : decode_any W_cbaac = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbab0 : bv 32 := 0x00070693.
Lemma F_cbab0 : fetch_word Asan.M.loaded_segments (0xcbab0 : word) = Some W_cbab0.
Proof. vm_refl. Qed.
Lemma D_cbab0 : decode_any W_cbab0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbab4 : bv 32 := 0x00467713.
Lemma F_cbab4 : fetch_word Asan.M.loaded_segments (0xcbab4 : word) = Some W_cbab4.
Proof. vm_refl. Qed.
Lemma D_cbab4 : decode_any W_cbab4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbab8 : bv 32 := 0x02070863.
Lemma F_cbab8 : fetch_word Asan.M.loaded_segments (0xcbab8 : word) = Some W_cbab8.
Proof. vm_refl. Qed.
Lemma D_cbab8 : decode_any W_cbab8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbabc : bv 32 := 0x0005c703.
Lemma F_cbabc : fetch_word Asan.M.loaded_segments (0xcbabc : word) = Some W_cbabc.
Proof. vm_refl. Qed.
Lemma D_cbabc : decode_any W_cbabc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbac0 : bv 32 := 0x0015c783.
Lemma F_cbac0 : fetch_word Asan.M.loaded_segments (0xcbac0 : word) = Some W_cbac0.
Proof. vm_refl. Qed.
Lemma D_cbac0 : decode_any W_cbac0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbac4 : bv 32 := 0x0025c803.
Lemma F_cbac4 : fetch_word Asan.M.loaded_segments (0xcbac4 : word) = Some W_cbac4.
Proof. vm_refl. Qed.
Lemma D_cbac4 : decode_any W_cbac4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbac8 : bv 32 := 0x0035c883.
Lemma F_cbac8 : fetch_word Asan.M.loaded_segments (0xcbac8 : word) = Some W_cbac8.
Proof. vm_refl. Qed.
Lemma D_cbac8 : decode_any W_cbac8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbacc : bv 32 := 0x00458593.
Lemma F_cbacc : fetch_word Asan.M.loaded_segments (0xcbacc : word) = Some W_cbacc.
Proof. vm_refl. Qed.
Lemma D_cbacc : decode_any W_cbacc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbad0 : bv 32 := 0x00468293.
Lemma F_cbad0 : fetch_word Asan.M.loaded_segments (0xcbad0 : word) = Some W_cbad0.
Proof. vm_refl. Qed.
Lemma D_cbad0 : decode_any W_cbad0 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbad4 : bv 32 := 0x00e68023.
Lemma F_cbad4 : fetch_word Asan.M.loaded_segments (0xcbad4 : word) = Some W_cbad4.
Proof. vm_refl. Qed.
Lemma D_cbad4 : decode_any W_cbad4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbad8 : bv 32 := 0x00f680a3.
Lemma F_cbad8 : fetch_word Asan.M.loaded_segments (0xcbad8 : word) = Some W_cbad8.
Proof. vm_refl. Qed.
Lemma D_cbad8 : decode_any W_cbad8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbadc : bv 32 := 0x01068123.
Lemma F_cbadc : fetch_word Asan.M.loaded_segments (0xcbadc : word) = Some W_cbadc.
Proof. vm_refl. Qed.
Lemma D_cbadc : decode_any W_cbadc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbae0 : bv 32 := 0x011681a3.
Lemma F_cbae0 : fetch_word Asan.M.loaded_segments (0xcbae0 : word) = Some W_cbae0.
Proof. vm_refl. Qed.
Lemma D_cbae0 : decode_any W_cbae0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbae4 : bv 32 := 0x00028693.
Lemma F_cbae4 : fetch_word Asan.M.loaded_segments (0xcbae4 : word) = Some W_cbae4.
Proof. vm_refl. Qed.
Lemma D_cbae4 : decode_any W_cbae4 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbae8 : bv 32 := 0x00267713.
Lemma F_cbae8 : fetch_word Asan.M.loaded_segments (0xcbae8 : word) = Some W_cbae8.
Proof. vm_refl. Qed.
Lemma D_cbae8 : decode_any W_cbae8 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaec : bv 32 := 0x00071863.
Lemma F_cbaec : fetch_word Asan.M.loaded_segments (0xcbaec : word) = Some W_cbaec.
Proof. vm_refl. Qed.
Lemma D_cbaec : decode_any W_cbaec = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaf0 : bv 32 := 0x00167613.
Lemma F_cbaf0 : fetch_word Asan.M.loaded_segments (0xcbaf0 : word) = Some W_cbaf0.
Proof. vm_refl. Qed.
Lemma D_cbaf0 : decode_any W_cbaf0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaf4 : bv 32 := 0x02061663.
Lemma F_cbaf4 : fetch_word Asan.M.loaded_segments (0xcbaf4 : word) = Some W_cbaf4.
Proof. vm_refl. Qed.
Lemma D_cbaf4 : decode_any W_cbaf4 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbaf8 : bv 32 := 0x00008067.
Lemma F_cbaf8 : fetch_word Asan.M.loaded_segments (0xcbaf8 : word) = Some W_cbaf8.
Proof. vm_refl. Qed.
Lemma D_cbaf8 : decode_any W_cbaf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbafc : bv 32 := 0x0005c703.
Lemma F_cbafc : fetch_word Asan.M.loaded_segments (0xcbafc : word) = Some W_cbafc.
Proof. vm_refl. Qed.
Lemma D_cbafc : decode_any W_cbafc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb00 : bv 32 := 0x0015c783.
Lemma F_cbb00 : fetch_word Asan.M.loaded_segments (0xcbb00 : word) = Some W_cbb00.
Proof. vm_refl. Qed.
Lemma D_cbb00 : decode_any W_cbb00 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb04 : bv 32 := 0x00258593.
Lemma F_cbb04 : fetch_word Asan.M.loaded_segments (0xcbb04 : word) = Some W_cbb04.
Proof. vm_refl. Qed.
Lemma D_cbb04 : decode_any W_cbb04 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb08 : bv 32 := 0x00268813.
Lemma F_cbb08 : fetch_word Asan.M.loaded_segments (0xcbb08 : word) = Some W_cbb08.
Proof. vm_refl. Qed.
Lemma D_cbb08 : decode_any W_cbb08 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb0c : bv 32 := 0x00e68023.
Lemma F_cbb0c : fetch_word Asan.M.loaded_segments (0xcbb0c : word) = Some W_cbb0c.
Proof. vm_refl. Qed.
Lemma D_cbb0c : decode_any W_cbb0c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb10 : bv 32 := 0x00f680a3.
Lemma F_cbb10 : fetch_word Asan.M.loaded_segments (0xcbb10 : word) = Some W_cbb10.
Proof. vm_refl. Qed.
Lemma D_cbb10 : decode_any W_cbb10 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb14 : bv 32 := 0x00080693.
Lemma F_cbb14 : fetch_word Asan.M.loaded_segments (0xcbb14 : word) = Some W_cbb14.
Proof. vm_refl. Qed.
Lemma D_cbb14 : decode_any W_cbb14 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb18 : bv 32 := 0x00167613.
Lemma F_cbb18 : fetch_word Asan.M.loaded_segments (0xcbb18 : word) = Some W_cbb18.
Proof. vm_refl. Qed.
Lemma D_cbb18 : decode_any W_cbb18 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb1c : bv 32 := 0xfc060ee3.
Lemma F_cbb1c : fetch_word Asan.M.loaded_segments (0xcbb1c : word) = Some W_cbb1c.
Proof. vm_refl. Qed.
Lemma D_cbb1c : decode_any W_cbb1c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb20 : bv 32 := 0x0005c583.
Lemma F_cbb20 : fetch_word Asan.M.loaded_segments (0xcbb20 : word) = Some W_cbb20.
Proof. vm_refl. Qed.
Lemma D_cbb20 : decode_any W_cbb20 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb24 : bv 32 := 0x00b68023.
Lemma F_cbb24 : fetch_word Asan.M.loaded_segments (0xcbb24 : word) = Some W_cbb24.
Proof. vm_refl. Qed.
Lemma D_cbb24 : decode_any W_cbb24 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb28 : bv 32 := 0x00008067.
Lemma F_cbb28 : fetch_word Asan.M.loaded_segments (0xcbb28 : word) = Some W_cbb28.
Proof. vm_refl. Qed.
Lemma D_cbb28 : decode_any W_cbb28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
