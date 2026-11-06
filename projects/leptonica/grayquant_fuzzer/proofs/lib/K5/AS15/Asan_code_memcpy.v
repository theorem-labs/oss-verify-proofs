(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Asan.
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
Definition W_d9884 : bv 32 := 0x0035f693.
Lemma F_d9884 : fetch_word Asan.M.loaded_segments (0xd98e8 : word) = Some W_d9884.
Proof. vm_refl. Qed.
Lemma D_d9884 : decode_any W_d9884 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9888 : bv 32 := 0x10068863.
Lemma F_d9888 : fetch_word Asan.M.loaded_segments (0xd98ec : word) = Some W_d9888.
Proof. vm_refl. Qed.
Lemma D_d9888 : decode_any W_d9888 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d988c : bv 32 := 0x02060e63.
Lemma F_d988c : fetch_word Asan.M.loaded_segments (0xd98f0 : word) = Some W_d988c.
Proof. vm_refl. Qed.
Lemma D_d988c : decode_any W_d988c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9890 : bv 32 := 0x00158713.
Lemma F_d9890 : fetch_word Asan.M.loaded_segments (0xd98f4 : word) = Some W_d9890.
Proof. vm_refl. Qed.
Lemma D_d9890 : decode_any W_d9890 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9894 : bv 32 := 0x00100793.
Lemma F_d9894 : fetch_word Asan.M.loaded_segments (0xd98f8 : word) = Some W_d9894.
Proof. vm_refl. Qed.
Lemma D_d9894 : decode_any W_d9894 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9898 : bv 32 := 0x00050693.
Lemma F_d9898 : fetch_word Asan.M.loaded_segments (0xd98fc : word) = Some W_d9898.
Proof. vm_refl. Qed.
Lemma D_d9898 : decode_any W_d9898 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d989c : bv 32 := 0x0005c883.
Lemma F_d989c : fetch_word Asan.M.loaded_segments (0xd9900 : word) = Some W_d989c.
Proof. vm_refl. Qed.
Lemma D_d989c : decode_any W_d989c = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98a0 : bv 32 := 0x00060813.
Lemma F_d98a0 : fetch_word Asan.M.loaded_segments (0xd9904 : word) = Some W_d98a0.
Proof. vm_refl. Qed.
Lemma D_d98a0 : decode_any W_d98a0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98a4 : bv 32 := 0x00158593.
Lemma F_d98a4 : fetch_word Asan.M.loaded_segments (0xd9908 : word) = Some W_d98a4.
Proof. vm_refl. Qed.
Lemma D_d98a4 : decode_any W_d98a4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98a8 : bv 32 := 0x00377293.
Lemma F_d98a8 : fetch_word Asan.M.loaded_segments (0xd990c : word) = Some W_d98a8.
Proof. vm_refl. Qed.
Lemma D_d98a8 : decode_any W_d98a8 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98ac : bv 32 := 0x01168023.
Lemma F_d98ac : fetch_word Asan.M.loaded_segments (0xd9910 : word) = Some W_d98ac.
Proof. vm_refl. Qed.
Lemma D_d98ac : decode_any W_d98ac = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98b0 : bv 32 := 0x00168693.
Lemma F_d98b0 : fetch_word Asan.M.loaded_segments (0xd9914 : word) = Some W_d98b0.
Proof. vm_refl. Qed.
Lemma D_d98b0 : decode_any W_d98b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98b4 : bv 32 := 0xfff60613.
Lemma F_d98b4 : fetch_word Asan.M.loaded_segments (0xd9918 : word) = Some W_d98b4.
Proof. vm_refl. Qed.
Lemma D_d98b4 : decode_any W_d98b4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98b8 : bv 32 := 0x00028a63.
Lemma F_d98b8 : fetch_word Asan.M.loaded_segments (0xd991c : word) = Some W_d98b8.
Proof. vm_refl. Qed.
Lemma D_d98b8 : decode_any W_d98b8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98bc : bv 32 := 0x00170713.
Lemma F_d98bc : fetch_word Asan.M.loaded_segments (0xd9920 : word) = Some W_d98bc.
Proof. vm_refl. Qed.
Lemma D_d98bc : decode_any W_d98bc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98c0 : bv 32 := 0xfcf81ee3.
Lemma F_d98c0 : fetch_word Asan.M.loaded_segments (0xd9924 : word) = Some W_d98c0.
Proof. vm_refl. Qed.
Lemma D_d98c0 : decode_any W_d98c0 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98c4 : bv 32 := 0x0080006f.
Lemma F_d98c4 : fetch_word Asan.M.loaded_segments (0xd9928 : word) = Some W_d98c4.
Proof. vm_refl. Qed.
Lemma D_d98c4 : decode_any W_d98c4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98c8 : bv 32 := 0x00050693.
Lemma F_d98c8 : fetch_word Asan.M.loaded_segments (0xd992c : word) = Some W_d98c8.
Proof. vm_refl. Qed.
Lemma D_d98c8 : decode_any W_d98c8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98cc : bv 32 := 0x0036f793.
Lemma F_d98cc : fetch_word Asan.M.loaded_segments (0xd9930 : word) = Some W_d98cc.
Proof. vm_refl. Qed.
Lemma D_d98cc : decode_any W_d98cc = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98d0 : bv 32 := 0x0c078a63.
Lemma F_d98d0 : fetch_word Asan.M.loaded_segments (0xd9934 : word) = Some W_d98d0.
Proof. vm_refl. Qed.
Lemma D_d98d0 : decode_any W_d98d0 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98d4 : bv 32 := 0x02000713.
Lemma F_d98d4 : fetch_word Asan.M.loaded_segments (0xd9938 : word) = Some W_d98d4.
Proof. vm_refl. Qed.
Lemma D_d98d4 : decode_any W_d98d4 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98d8 : bv 32 := 0x02e67063.
Lemma F_d98d8 : fetch_word Asan.M.loaded_segments (0xd993c : word) = Some W_d98d8.
Proof. vm_refl. Qed.
Lemma D_d98d8 : decode_any W_d98d8 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98dc : bv 32 := 0x01000713.
Lemma F_d98dc : fetch_word Asan.M.loaded_segments (0xd9940 : word) = Some W_d98dc.
Proof. vm_refl. Qed.
Lemma D_d98dc : decode_any W_d98dc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98e0 : bv 32 := 0x24e67863.
Lemma F_d98e0 : fetch_word Asan.M.loaded_segments (0xd9944 : word) = Some W_d98e0.
Proof. vm_refl. Qed.
Lemma D_d98e0 : decode_any W_d98e0 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98e4 : bv 32 := 0x00867713.
Lemma F_d98e4 : fetch_word Asan.M.loaded_segments (0xd9948 : word) = Some W_d98e4.
Proof. vm_refl. Qed.
Lemma D_d98e4 : decode_any W_d98e4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98e8 : bv 32 := 0x2c071e63.
Lemma F_d98e8 : fetch_word Asan.M.loaded_segments (0xd994c : word) = Some W_d98e8.
Proof. vm_refl. Qed.
Lemma D_d98e8 : decode_any W_d98e8 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98ec : bv 32 := 0x00467713.
Lemma F_d98ec : fetch_word Asan.M.loaded_segments (0xd9950 : word) = Some W_d98ec.
Proof. vm_refl. Qed.
Lemma D_d98ec : decode_any W_d98ec = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98f0 : bv 32 := 0x32071463.
Lemma F_d98f0 : fetch_word Asan.M.loaded_segments (0xd9954 : word) = Some W_d98f0.
Proof. vm_refl. Qed.
Lemma D_d98f0 : decode_any W_d98f0 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98f4 : bv 32 := 0x3500006f.
Lemma F_d98f4 : fetch_word Asan.M.loaded_segments (0xd9958 : word) = Some W_d98f4.
Proof. vm_refl. Qed.
Lemma D_d98f4 : decode_any W_d98f4 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98f8 : bv 32 := 0x0005a703.
Lemma F_d98f8 : fetch_word Asan.M.loaded_segments (0xd995c : word) = Some W_d98f8.
Proof. vm_refl. Qed.
Lemma D_d98f8 : decode_any W_d98f8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d98fc : bv 32 := 0x00300813.
Lemma F_d98fc : fetch_word Asan.M.loaded_segments (0xd9960 : word) = Some W_d98fc.
Proof. vm_refl. Qed.
Lemma D_d98fc : decode_any W_d98fc = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9900 : bv 32 := 0x11078e63.
Lemma F_d9900 : fetch_word Asan.M.loaded_segments (0xd9964 : word) = Some W_d9900.
Proof. vm_refl. Qed.
Lemma D_d9900 : decode_any W_d9900 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9904 : bv 32 := 0x00200813.
Lemma F_d9904 : fetch_word Asan.M.loaded_segments (0xd9968 : word) = Some W_d9904.
Proof. vm_refl. Qed.
Lemma D_d9904 : decode_any W_d9904 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9908 : bv 32 := 0x19079c63.
Lemma F_d9908 : fetch_word Asan.M.loaded_segments (0xd996c : word) = Some W_d9908.
Proof. vm_refl. Qed.
Lemma D_d9908 : decode_any W_d9908 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d990c : bv 32 := 0x00875793.
Lemma F_d990c : fetch_word Asan.M.loaded_segments (0xd9970 : word) = Some W_d990c.
Proof. vm_refl. Qed.
Lemma D_d990c : decode_any W_d990c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9910 : bv 32 := 0xffe60613.
Lemma F_d9910 : fetch_word Asan.M.loaded_segments (0xd9974 : word) = Some W_d9910.
Proof. vm_refl. Qed.
Lemma D_d9910 : decode_any W_d9910 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9914 : bv 32 := 0x00e68023.
Lemma F_d9914 : fetch_word Asan.M.loaded_segments (0xd9978 : word) = Some W_d9914.
Proof. vm_refl. Qed.
Lemma D_d9914 : decode_any W_d9914 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9918 : bv 32 := 0x00f680a3.
Lemma F_d9918 : fetch_word Asan.M.loaded_segments (0xd997c : word) = Some W_d9918.
Proof. vm_refl. Qed.
Lemma D_d9918 : decode_any W_d9918 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d991c : bv 32 := 0x00268693.
Lemma F_d991c : fetch_word Asan.M.loaded_segments (0xd9980 : word) = Some W_d991c.
Proof. vm_refl. Qed.
Lemma D_d991c : decode_any W_d991c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9920 : bv 32 := 0x01058593.
Lemma F_d9920 : fetch_word Asan.M.loaded_segments (0xd9984 : word) = Some W_d9920.
Proof. vm_refl. Qed.
Lemma D_d9920 : decode_any W_d9920 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9924 : bv 32 := 0x01100793.
Lemma F_d9924 : fetch_word Asan.M.loaded_segments (0xd9988 : word) = Some W_d9924.
Proof. vm_refl. Qed.
Lemma D_d9924 : decode_any W_d9924 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9928 : bv 32 := 0x0107581b.
Lemma F_d9928 : fetch_word Asan.M.loaded_segments (0xd998c : word) = Some W_d9928.
Proof. vm_refl. Qed.
Lemma D_d9928 : decode_any W_d9928 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d992c : bv 32 := 0xff45a883.
Lemma F_d992c : fetch_word Asan.M.loaded_segments (0xd9990 : word) = Some W_d992c.
Proof. vm_refl. Qed.
Lemma D_d992c : decode_any W_d992c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9930 : bv 32 := 0xff85a283.
Lemma F_d9930 : fetch_word Asan.M.loaded_segments (0xd9994 : word) = Some W_d9930.
Proof. vm_refl. Qed.
Lemma D_d9930 : decode_any W_d9930 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9934 : bv 32 := 0xffc5a303.
Lemma F_d9934 : fetch_word Asan.M.loaded_segments (0xd9998 : word) = Some W_d9934.
Proof. vm_refl. Qed.
Lemma D_d9934 : decode_any W_d9934 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9938 : bv 32 := 0x0005a703.
Lemma F_d9938 : fetch_word Asan.M.loaded_segments (0xd999c : word) = Some W_d9938.
Proof. vm_refl. Qed.
Lemma D_d9938 : decode_any W_d9938 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d993c : bv 32 := 0x01089393.
Lemma F_d993c : fetch_word Asan.M.loaded_segments (0xd99a0 : word) = Some W_d993c.
Proof. vm_refl. Qed.
Lemma D_d993c : decode_any W_d993c = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9940 : bv 32 := 0x0108d89b.
Lemma F_d9940 : fetch_word Asan.M.loaded_segments (0xd99a4 : word) = Some W_d9940.
Proof. vm_refl. Qed.
Lemma D_d9940 : decode_any W_d9940 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9944 : bv 32 := 0x0103e833.
Lemma F_d9944 : fetch_word Asan.M.loaded_segments (0xd99a8 : word) = Some W_d9944.
Proof. vm_refl. Qed.
Lemma D_d9944 : decode_any W_d9944 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9948 : bv 32 := 0x01029393.
Lemma F_d9948 : fetch_word Asan.M.loaded_segments (0xd99ac : word) = Some W_d9948.
Proof. vm_refl. Qed.
Lemma D_d9948 : decode_any W_d9948 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d994c : bv 32 := 0x0102d29b.
Lemma F_d994c : fetch_word Asan.M.loaded_segments (0xd99b0 : word) = Some W_d994c.
Proof. vm_refl. Qed.
Lemma D_d994c : decode_any W_d994c = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9950 : bv 32 := 0x0113e8b3.
Lemma F_d9950 : fetch_word Asan.M.loaded_segments (0xd99b4 : word) = Some W_d9950.
Proof. vm_refl. Qed.
Lemma D_d9950 : decode_any W_d9950 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9954 : bv 32 := 0x01031393.
Lemma F_d9954 : fetch_word Asan.M.loaded_segments (0xd99b8 : word) = Some W_d9954.
Proof. vm_refl. Qed.
Lemma D_d9954 : decode_any W_d9954 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9958 : bv 32 := 0x0103531b.
Lemma F_d9958 : fetch_word Asan.M.loaded_segments (0xd99bc : word) = Some W_d9958.
Proof. vm_refl. Qed.
Lemma D_d9958 : decode_any W_d9958 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d995c : bv 32 := 0x0053e2b3.
Lemma F_d995c : fetch_word Asan.M.loaded_segments (0xd99c0 : word) = Some W_d995c.
Proof. vm_refl. Qed.
Lemma D_d995c : decode_any W_d995c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9960 : bv 32 := 0x01071393.
Lemma F_d9960 : fetch_word Asan.M.loaded_segments (0xd99c4 : word) = Some W_d9960.
Proof. vm_refl. Qed.
Lemma D_d9960 : decode_any W_d9960 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9964 : bv 32 := 0x0063e333.
Lemma F_d9964 : fetch_word Asan.M.loaded_segments (0xd99c8 : word) = Some W_d9964.
Proof. vm_refl. Qed.
Lemma D_d9964 : decode_any W_d9964 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9968 : bv 32 := 0xff060613.
Lemma F_d9968 : fetch_word Asan.M.loaded_segments (0xd99cc : word) = Some W_d9968.
Proof. vm_refl. Qed.
Lemma D_d9968 : decode_any W_d9968 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d996c : bv 32 := 0x0106a023.
Lemma F_d996c : fetch_word Asan.M.loaded_segments (0xd99d0 : word) = Some W_d996c.
Proof. vm_refl. Qed.
Lemma D_d996c : decode_any W_d996c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9970 : bv 32 := 0x0116a223.
Lemma F_d9970 : fetch_word Asan.M.loaded_segments (0xd99d4 : word) = Some W_d9970.
Proof. vm_refl. Qed.
Lemma D_d9970 : decode_any W_d9970 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9974 : bv 32 := 0x0056a423.
Lemma F_d9974 : fetch_word Asan.M.loaded_segments (0xd99d8 : word) = Some W_d9974.
Proof. vm_refl. Qed.
Lemma D_d9974 : decode_any W_d9974 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9978 : bv 32 := 0x0066a623.
Lemma F_d9978 : fetch_word Asan.M.loaded_segments (0xd99dc : word) = Some W_d9978.
Proof. vm_refl. Qed.
Lemma D_d9978 : decode_any W_d9978 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d997c : bv 32 := 0x01068693.
Lemma F_d997c : fetch_word Asan.M.loaded_segments (0xd99e0 : word) = Some W_d997c.
Proof. vm_refl. Qed.
Lemma D_d997c : decode_any W_d997c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9980 : bv 32 := 0x01058593.
Lemma F_d9980 : fetch_word Asan.M.loaded_segments (0xd99e4 : word) = Some W_d9980.
Proof. vm_refl. Qed.
Lemma D_d9980 : decode_any W_d9980 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9984 : bv 32 := 0xfac7e2e3.
Lemma F_d9984 : fetch_word Asan.M.loaded_segments (0xd99e8 : word) = Some W_d9984.
Proof. vm_refl. Qed.
Lemma D_d9984 : decode_any W_d9984 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9988 : bv 32 := 0xff258593.
Lemma F_d9988 : fetch_word Asan.M.loaded_segments (0xd99ec : word) = Some W_d9988.
Proof. vm_refl. Qed.
Lemma D_d9988 : decode_any W_d9988 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d998c : bv 32 := 0x01000713.
Lemma F_d998c : fetch_word Asan.M.loaded_segments (0xd99f0 : word) = Some W_d998c.
Proof. vm_refl. Qed.
Lemma D_d998c : decode_any W_d998c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9990 : bv 32 := 0xf4e66ae3.
Lemma F_d9990 : fetch_word Asan.M.loaded_segments (0xd99f4 : word) = Some W_d9990.
Proof. vm_refl. Qed.
Lemma D_d9990 : decode_any W_d9990 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9994 : bv 32 := 0x19c0006f.
Lemma F_d9994 : fetch_word Asan.M.loaded_segments (0xd99f8 : word) = Some W_d9994.
Proof. vm_refl. Qed.
Lemma D_d9994 : decode_any W_d9994 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9998 : bv 32 := 0x00050693.
Lemma F_d9998 : fetch_word Asan.M.loaded_segments (0xd99fc : word) = Some W_d9998.
Proof. vm_refl. Qed.
Lemma D_d9998 : decode_any W_d9998 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d999c : bv 32 := 0x00357793.
Lemma F_d999c : fetch_word Asan.M.loaded_segments (0xd9a00 : word) = Some W_d999c.
Proof. vm_refl. Qed.
Lemma D_d999c : decode_any W_d999c = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99a0 : bv 32 := 0xf2079ae3.
Lemma F_d99a0 : fetch_word Asan.M.loaded_segments (0xd9a04 : word) = Some W_d99a0.
Proof. vm_refl. Qed.
Lemma D_d99a0 : decode_any W_d99a0 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99a4 : bv 32 := 0x01000713.
Lemma F_d99a4 : fetch_word Asan.M.loaded_segments (0xd9a08 : word) = Some W_d99a4.
Proof. vm_refl. Qed.
Lemma D_d99a4 : decode_any W_d99a4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99a8 : bv 32 := 0x02e66c63.
Lemma F_d99a8 : fetch_word Asan.M.loaded_segments (0xd9a0c : word) = Some W_d99a8.
Proof. vm_refl. Qed.
Lemma D_d99a8 : decode_any W_d99a8 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99ac : bv 32 := 0x00f00713.
Lemma F_d99ac : fetch_word Asan.M.loaded_segments (0xd9a10 : word) = Some W_d99ac.
Proof. vm_refl. Qed.
Lemma D_d99ac : decode_any W_d99ac = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99b0 : bv 32 := 0x0005a783.
Lemma F_d99b0 : fetch_word Asan.M.loaded_segments (0xd9a14 : word) = Some W_d99b0.
Proof. vm_refl. Qed.
Lemma D_d99b0 : decode_any W_d99b0 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99b4 : bv 32 := 0x0045a803.
Lemma F_d99b4 : fetch_word Asan.M.loaded_segments (0xd9a18 : word) = Some W_d99b4.
Proof. vm_refl. Qed.
Lemma D_d99b4 : decode_any W_d99b4 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99b8 : bv 32 := 0x0085a883.
Lemma F_d99b8 : fetch_word Asan.M.loaded_segments (0xd9a1c : word) = Some W_d99b8.
Proof. vm_refl. Qed.
Lemma D_d99b8 : decode_any W_d99b8 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99bc : bv 32 := 0x00c5a283.
Lemma F_d99bc : fetch_word Asan.M.loaded_segments (0xd9a20 : word) = Some W_d99bc.
Proof. vm_refl. Qed.
Lemma D_d99bc : decode_any W_d99bc = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99c0 : bv 32 := 0x01058593.
Lemma F_d99c0 : fetch_word Asan.M.loaded_segments (0xd9a24 : word) = Some W_d99c0.
Proof. vm_refl. Qed.
Lemma D_d99c0 : decode_any W_d99c0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99c4 : bv 32 := 0xff060613.
Lemma F_d99c4 : fetch_word Asan.M.loaded_segments (0xd9a28 : word) = Some W_d99c4.
Proof. vm_refl. Qed.
Lemma D_d99c4 : decode_any W_d99c4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99c8 : bv 32 := 0x00f6a023.
Lemma F_d99c8 : fetch_word Asan.M.loaded_segments (0xd9a2c : word) = Some W_d99c8.
Proof. vm_refl. Qed.
Lemma D_d99c8 : decode_any W_d99c8 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99cc : bv 32 := 0x0106a223.
Lemma F_d99cc : fetch_word Asan.M.loaded_segments (0xd9a30 : word) = Some W_d99cc.
Proof. vm_refl. Qed.
Lemma D_d99cc : decode_any W_d99cc = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99d0 : bv 32 := 0x0116a423.
Lemma F_d99d0 : fetch_word Asan.M.loaded_segments (0xd9a34 : word) = Some W_d99d0.
Proof. vm_refl. Qed.
Lemma D_d99d0 : decode_any W_d99d0 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99d4 : bv 32 := 0x0056a623.
Lemma F_d99d4 : fetch_word Asan.M.loaded_segments (0xd9a38 : word) = Some W_d99d4.
Proof. vm_refl. Qed.
Lemma D_d99d4 : decode_any W_d99d4 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99d8 : bv 32 := 0x01068693.
Lemma F_d99d8 : fetch_word Asan.M.loaded_segments (0xd9a3c : word) = Some W_d99d8.
Proof. vm_refl. Qed.
Lemma D_d99d8 : decode_any W_d99d8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99dc : bv 32 := 0xfcc76ae3.
Lemma F_d99dc : fetch_word Asan.M.loaded_segments (0xd9a40 : word) = Some W_d99dc.
Proof. vm_refl. Qed.
Lemma D_d99dc : decode_any W_d99dc = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99e0 : bv 32 := 0x00800713.
Lemma F_d99e0 : fetch_word Asan.M.loaded_segments (0xd9a44 : word) = Some W_d99e0.
Proof. vm_refl. Qed.
Lemma D_d99e0 : decode_any W_d99e0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99e4 : bv 32 := 0x00e66e63.
Lemma F_d99e4 : fetch_word Asan.M.loaded_segments (0xd9a48 : word) = Some W_d99e4.
Proof. vm_refl. Qed.
Lemma D_d99e4 : decode_any W_d99e4 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99e8 : bv 32 := 0x0005a703.
Lemma F_d99e8 : fetch_word Asan.M.loaded_segments (0xd9a4c : word) = Some W_d99e8.
Proof. vm_refl. Qed.
Lemma D_d99e8 : decode_any W_d99e8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99ec : bv 32 := 0x0045a783.
Lemma F_d99ec : fetch_word Asan.M.loaded_segments (0xd9a50 : word) = Some W_d99ec.
Proof. vm_refl. Qed.
Lemma D_d99ec : decode_any W_d99ec = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99f0 : bv 32 := 0x00e6a023.
Lemma F_d99f0 : fetch_word Asan.M.loaded_segments (0xd9a54 : word) = Some W_d99f0.
Proof. vm_refl. Qed.
Lemma D_d99f0 : decode_any W_d99f0 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99f4 : bv 32 := 0x00f6a223.
Lemma F_d99f4 : fetch_word Asan.M.loaded_segments (0xd9a58 : word) = Some W_d99f4.
Proof. vm_refl. Qed.
Lemma D_d99f4 : decode_any W_d99f4 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99f8 : bv 32 := 0x00868693.
Lemma F_d99f8 : fetch_word Asan.M.loaded_segments (0xd9a5c : word) = Some W_d99f8.
Proof. vm_refl. Qed.
Lemma D_d99f8 : decode_any W_d99f8 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d99fc : bv 32 := 0x00858593.
Lemma F_d99fc : fetch_word Asan.M.loaded_segments (0xd9a60 : word) = Some W_d99fc.
Proof. vm_refl. Qed.
Lemma D_d99fc : decode_any W_d99fc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a00 : bv 32 := 0x00467713.
Lemma F_d9a00 : fetch_word Asan.M.loaded_segments (0xd9a64 : word) = Some W_d9a00.
Proof. vm_refl. Qed.
Lemma D_d9a00 : decode_any W_d9a00 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a04 : bv 32 := 0x24070063.
Lemma F_d9a04 : fetch_word Asan.M.loaded_segments (0xd9a68 : word) = Some W_d9a04.
Proof. vm_refl. Qed.
Lemma D_d9a04 : decode_any W_d9a04 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a08 : bv 32 := 0x0005a703.
Lemma F_d9a08 : fetch_word Asan.M.loaded_segments (0xd9a6c : word) = Some W_d9a08.
Proof. vm_refl. Qed.
Lemma D_d9a08 : decode_any W_d9a08 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a0c : bv 32 := 0x00458593.
Lemma F_d9a0c : fetch_word Asan.M.loaded_segments (0xd9a70 : word) = Some W_d9a0c.
Proof. vm_refl. Qed.
Lemma D_d9a0c : decode_any W_d9a0c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a10 : bv 32 := 0x00e6a023.
Lemma F_d9a10 : fetch_word Asan.M.loaded_segments (0xd9a74 : word) = Some W_d9a10.
Proof. vm_refl. Qed.
Lemma D_d9a10 : decode_any W_d9a10 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a14 : bv 32 := 0x00468693.
Lemma F_d9a14 : fetch_word Asan.M.loaded_segments (0xd9a78 : word) = Some W_d9a14.
Proof. vm_refl. Qed.
Lemma D_d9a14 : decode_any W_d9a14 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a18 : bv 32 := 0x22c0006f.
Lemma F_d9a18 : fetch_word Asan.M.loaded_segments (0xd9a7c : word) = Some W_d9a18.
Proof. vm_refl. Qed.
Lemma D_d9a18 : decode_any W_d9a18 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a1c : bv 32 := 0x00e68023.
Lemma F_d9a1c : fetch_word Asan.M.loaded_segments (0xd9a80 : word) = Some W_d9a1c.
Proof. vm_refl. Qed.
Lemma D_d9a1c : decode_any W_d9a1c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a20 : bv 32 := 0x00168693.
Lemma F_d9a20 : fetch_word Asan.M.loaded_segments (0xd9a84 : word) = Some W_d9a20.
Proof. vm_refl. Qed.
Lemma D_d9a20 : decode_any W_d9a20 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a24 : bv 32 := 0xfff60613.
Lemma F_d9a24 : fetch_word Asan.M.loaded_segments (0xd9a88 : word) = Some W_d9a24.
Proof. vm_refl. Qed.
Lemma D_d9a24 : decode_any W_d9a24 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a28 : bv 32 := 0x01058593.
Lemma F_d9a28 : fetch_word Asan.M.loaded_segments (0xd9a8c : word) = Some W_d9a28.
Proof. vm_refl. Qed.
Lemma D_d9a28 : decode_any W_d9a28 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a2c : bv 32 := 0x01200793.
Lemma F_d9a2c : fetch_word Asan.M.loaded_segments (0xd9a90 : word) = Some W_d9a2c.
Proof. vm_refl. Qed.
Lemma D_d9a2c : decode_any W_d9a2c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a30 : bv 32 := 0x0087581b.
Lemma F_d9a30 : fetch_word Asan.M.loaded_segments (0xd9a94 : word) = Some W_d9a30.
Proof. vm_refl. Qed.
Lemma D_d9a30 : decode_any W_d9a30 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a34 : bv 32 := 0xff45a883.
Lemma F_d9a34 : fetch_word Asan.M.loaded_segments (0xd9a98 : word) = Some W_d9a34.
Proof. vm_refl. Qed.
Lemma D_d9a34 : decode_any W_d9a34 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a38 : bv 32 := 0xff85a283.
Lemma F_d9a38 : fetch_word Asan.M.loaded_segments (0xd9a9c : word) = Some W_d9a38.
Proof. vm_refl. Qed.
Lemma D_d9a38 : decode_any W_d9a38 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a3c : bv 32 := 0xffc5a303.
Lemma F_d9a3c : fetch_word Asan.M.loaded_segments (0xd9aa0 : word) = Some W_d9a3c.
Proof. vm_refl. Qed.
Lemma D_d9a3c : decode_any W_d9a3c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a40 : bv 32 := 0x0005a703.
Lemma F_d9a40 : fetch_word Asan.M.loaded_segments (0xd9aa4 : word) = Some W_d9a40.
Proof. vm_refl. Qed.
Lemma D_d9a40 : decode_any W_d9a40 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a44 : bv 32 := 0x01889393.
Lemma F_d9a44 : fetch_word Asan.M.loaded_segments (0xd9aa8 : word) = Some W_d9a44.
Proof. vm_refl. Qed.
Lemma D_d9a44 : decode_any W_d9a44 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a48 : bv 32 := 0x0088d89b.
Lemma F_d9a48 : fetch_word Asan.M.loaded_segments (0xd9aac : word) = Some W_d9a48.
Proof. vm_refl. Qed.
Lemma D_d9a48 : decode_any W_d9a48 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a4c : bv 32 := 0x0103e833.
Lemma F_d9a4c : fetch_word Asan.M.loaded_segments (0xd9ab0 : word) = Some W_d9a4c.
Proof. vm_refl. Qed.
Lemma D_d9a4c : decode_any W_d9a4c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a50 : bv 32 := 0x01829393.
Lemma F_d9a50 : fetch_word Asan.M.loaded_segments (0xd9ab4 : word) = Some W_d9a50.
Proof. vm_refl. Qed.
Lemma D_d9a50 : decode_any W_d9a50 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a54 : bv 32 := 0x0082d29b.
Lemma F_d9a54 : fetch_word Asan.M.loaded_segments (0xd9ab8 : word) = Some W_d9a54.
Proof. vm_refl. Qed.
Lemma D_d9a54 : decode_any W_d9a54 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a58 : bv 32 := 0x0113e8b3.
Lemma F_d9a58 : fetch_word Asan.M.loaded_segments (0xd9abc : word) = Some W_d9a58.
Proof. vm_refl. Qed.
Lemma D_d9a58 : decode_any W_d9a58 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a5c : bv 32 := 0x01831393.
Lemma F_d9a5c : fetch_word Asan.M.loaded_segments (0xd9ac0 : word) = Some W_d9a5c.
Proof. vm_refl. Qed.
Lemma D_d9a5c : decode_any W_d9a5c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a60 : bv 32 := 0x0083531b.
Lemma F_d9a60 : fetch_word Asan.M.loaded_segments (0xd9ac4 : word) = Some W_d9a60.
Proof. vm_refl. Qed.
Lemma D_d9a60 : decode_any W_d9a60 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a64 : bv 32 := 0x0053e2b3.
Lemma F_d9a64 : fetch_word Asan.M.loaded_segments (0xd9ac8 : word) = Some W_d9a64.
Proof. vm_refl. Qed.
Lemma D_d9a64 : decode_any W_d9a64 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a68 : bv 32 := 0x01871393.
Lemma F_d9a68 : fetch_word Asan.M.loaded_segments (0xd9acc : word) = Some W_d9a68.
Proof. vm_refl. Qed.
Lemma D_d9a68 : decode_any W_d9a68 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a6c : bv 32 := 0x0063e333.
Lemma F_d9a6c : fetch_word Asan.M.loaded_segments (0xd9ad0 : word) = Some W_d9a6c.
Proof. vm_refl. Qed.
Lemma D_d9a6c : decode_any W_d9a6c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a70 : bv 32 := 0xff060613.
Lemma F_d9a70 : fetch_word Asan.M.loaded_segments (0xd9ad4 : word) = Some W_d9a70.
Proof. vm_refl. Qed.
Lemma D_d9a70 : decode_any W_d9a70 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a74 : bv 32 := 0x0106a023.
Lemma F_d9a74 : fetch_word Asan.M.loaded_segments (0xd9ad8 : word) = Some W_d9a74.
Proof. vm_refl. Qed.
Lemma D_d9a74 : decode_any W_d9a74 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a78 : bv 32 := 0x0116a223.
Lemma F_d9a78 : fetch_word Asan.M.loaded_segments (0xd9adc : word) = Some W_d9a78.
Proof. vm_refl. Qed.
Lemma D_d9a78 : decode_any W_d9a78 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a7c : bv 32 := 0x0056a423.
Lemma F_d9a7c : fetch_word Asan.M.loaded_segments (0xd9ae0 : word) = Some W_d9a7c.
Proof. vm_refl. Qed.
Lemma D_d9a7c : decode_any W_d9a7c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a80 : bv 32 := 0x0066a623.
Lemma F_d9a80 : fetch_word Asan.M.loaded_segments (0xd9ae4 : word) = Some W_d9a80.
Proof. vm_refl. Qed.
Lemma D_d9a80 : decode_any W_d9a80 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a84 : bv 32 := 0x01068693.
Lemma F_d9a84 : fetch_word Asan.M.loaded_segments (0xd9ae8 : word) = Some W_d9a84.
Proof. vm_refl. Qed.
Lemma D_d9a84 : decode_any W_d9a84 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a88 : bv 32 := 0x01058593.
Lemma F_d9a88 : fetch_word Asan.M.loaded_segments (0xd9aec : word) = Some W_d9a88.
Proof. vm_refl. Qed.
Lemma D_d9a88 : decode_any W_d9a88 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a8c : bv 32 := 0xfac7e2e3.
Lemma F_d9a8c : fetch_word Asan.M.loaded_segments (0xd9af0 : word) = Some W_d9a8c.
Proof. vm_refl. Qed.
Lemma D_d9a8c : decode_any W_d9a8c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a90 : bv 32 := 0xff158593.
Lemma F_d9a90 : fetch_word Asan.M.loaded_segments (0xd9af4 : word) = Some W_d9a90.
Proof. vm_refl. Qed.
Lemma D_d9a90 : decode_any W_d9a90 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a94 : bv 32 := 0x01000713.
Lemma F_d9a94 : fetch_word Asan.M.loaded_segments (0xd9af8 : word) = Some W_d9a94.
Proof. vm_refl. Qed.
Lemma D_d9a94 : decode_any W_d9a94 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a98 : bv 32 := 0xe4e666e3.
Lemma F_d9a98 : fetch_word Asan.M.loaded_segments (0xd9afc : word) = Some W_d9a98.
Proof. vm_refl. Qed.
Lemma D_d9a98 : decode_any W_d9a98 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9a9c : bv 32 := 0x0940006f.
Lemma F_d9a9c : fetch_word Asan.M.loaded_segments (0xd9b00 : word) = Some W_d9a9c.
Proof. vm_refl. Qed.
Lemma D_d9a9c : decode_any W_d9a9c = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9aa0 : bv 32 := 0x00875793.
Lemma F_d9aa0 : fetch_word Asan.M.loaded_segments (0xd9b04 : word) = Some W_d9aa0.
Proof. vm_refl. Qed.
Lemma D_d9aa0 : decode_any W_d9aa0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9aa4 : bv 32 := 0x01075813.
Lemma F_d9aa4 : fetch_word Asan.M.loaded_segments (0xd9b08 : word) = Some W_d9aa4.
Proof. vm_refl. Qed.
Lemma D_d9aa4 : decode_any W_d9aa4 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9aa8 : bv 32 := 0xffd60613.
Lemma F_d9aa8 : fetch_word Asan.M.loaded_segments (0xd9b0c : word) = Some W_d9aa8.
Proof. vm_refl. Qed.
Lemma D_d9aa8 : decode_any W_d9aa8 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9aac : bv 32 := 0x00e68023.
Lemma F_d9aac : fetch_word Asan.M.loaded_segments (0xd9b10 : word) = Some W_d9aac.
Proof. vm_refl. Qed.
Lemma D_d9aac : decode_any W_d9aac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ab0 : bv 32 := 0x00f680a3.
Lemma F_d9ab0 : fetch_word Asan.M.loaded_segments (0xd9b14 : word) = Some W_d9ab0.
Proof. vm_refl. Qed.
Lemma D_d9ab0 : decode_any W_d9ab0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ab4 : bv 32 := 0x01068123.
Lemma F_d9ab4 : fetch_word Asan.M.loaded_segments (0xd9b18 : word) = Some W_d9ab4.
Proof. vm_refl. Qed.
Lemma D_d9ab4 : decode_any W_d9ab4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ab8 : bv 32 := 0x00368693.
Lemma F_d9ab8 : fetch_word Asan.M.loaded_segments (0xd9b1c : word) = Some W_d9ab8.
Proof. vm_refl. Qed.
Lemma D_d9ab8 : decode_any W_d9ab8 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9abc : bv 32 := 0x01058593.
Lemma F_d9abc : fetch_word Asan.M.loaded_segments (0xd9b20 : word) = Some W_d9abc.
Proof. vm_refl. Qed.
Lemma D_d9abc : decode_any W_d9abc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ac0 : bv 32 := 0x01000793.
Lemma F_d9ac0 : fetch_word Asan.M.loaded_segments (0xd9b24 : word) = Some W_d9ac0.
Proof. vm_refl. Qed.
Lemma D_d9ac0 : decode_any W_d9ac0 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ac4 : bv 32 := 0x0187581b.
Lemma F_d9ac4 : fetch_word Asan.M.loaded_segments (0xd9b28 : word) = Some W_d9ac4.
Proof. vm_refl. Qed.
Lemma D_d9ac4 : decode_any W_d9ac4 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ac8 : bv 32 := 0xff45a883.
Lemma F_d9ac8 : fetch_word Asan.M.loaded_segments (0xd9b2c : word) = Some W_d9ac8.
Proof. vm_refl. Qed.
Lemma D_d9ac8 : decode_any W_d9ac8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9acc : bv 32 := 0xff85a283.
Lemma F_d9acc : fetch_word Asan.M.loaded_segments (0xd9b30 : word) = Some W_d9acc.
Proof. vm_refl. Qed.
Lemma D_d9acc : decode_any W_d9acc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ad0 : bv 32 := 0xffc5a303.
Lemma F_d9ad0 : fetch_word Asan.M.loaded_segments (0xd9b34 : word) = Some W_d9ad0.
Proof. vm_refl. Qed.
Lemma D_d9ad0 : decode_any W_d9ad0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ad4 : bv 32 := 0x0005a703.
Lemma F_d9ad4 : fetch_word Asan.M.loaded_segments (0xd9b38 : word) = Some W_d9ad4.
Proof. vm_refl. Qed.
Lemma D_d9ad4 : decode_any W_d9ad4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ad8 : bv 32 := 0x00889393.
Lemma F_d9ad8 : fetch_word Asan.M.loaded_segments (0xd9b3c : word) = Some W_d9ad8.
Proof. vm_refl. Qed.
Lemma D_d9ad8 : decode_any W_d9ad8 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9adc : bv 32 := 0x0188d89b.
Lemma F_d9adc : fetch_word Asan.M.loaded_segments (0xd9b40 : word) = Some W_d9adc.
Proof. vm_refl. Qed.
Lemma D_d9adc : decode_any W_d9adc = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ae0 : bv 32 := 0x0103e833.
Lemma F_d9ae0 : fetch_word Asan.M.loaded_segments (0xd9b44 : word) = Some W_d9ae0.
Proof. vm_refl. Qed.
Lemma D_d9ae0 : decode_any W_d9ae0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ae4 : bv 32 := 0x00829393.
Lemma F_d9ae4 : fetch_word Asan.M.loaded_segments (0xd9b48 : word) = Some W_d9ae4.
Proof. vm_refl. Qed.
Lemma D_d9ae4 : decode_any W_d9ae4 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ae8 : bv 32 := 0x0182d29b.
Lemma F_d9ae8 : fetch_word Asan.M.loaded_segments (0xd9b4c : word) = Some W_d9ae8.
Proof. vm_refl. Qed.
Lemma D_d9ae8 : decode_any W_d9ae8 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9aec : bv 32 := 0x0113e8b3.
Lemma F_d9aec : fetch_word Asan.M.loaded_segments (0xd9b50 : word) = Some W_d9aec.
Proof. vm_refl. Qed.
Lemma D_d9aec : decode_any W_d9aec = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9af0 : bv 32 := 0x00831393.
Lemma F_d9af0 : fetch_word Asan.M.loaded_segments (0xd9b54 : word) = Some W_d9af0.
Proof. vm_refl. Qed.
Lemma D_d9af0 : decode_any W_d9af0 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9af4 : bv 32 := 0x0183531b.
Lemma F_d9af4 : fetch_word Asan.M.loaded_segments (0xd9b58 : word) = Some W_d9af4.
Proof. vm_refl. Qed.
Lemma D_d9af4 : decode_any W_d9af4 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9af8 : bv 32 := 0x0053e2b3.
Lemma F_d9af8 : fetch_word Asan.M.loaded_segments (0xd9b5c : word) = Some W_d9af8.
Proof. vm_refl. Qed.
Lemma D_d9af8 : decode_any W_d9af8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9afc : bv 32 := 0x00871393.
Lemma F_d9afc : fetch_word Asan.M.loaded_segments (0xd9b60 : word) = Some W_d9afc.
Proof. vm_refl. Qed.
Lemma D_d9afc : decode_any W_d9afc = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b00 : bv 32 := 0x0063e333.
Lemma F_d9b00 : fetch_word Asan.M.loaded_segments (0xd9b64 : word) = Some W_d9b00.
Proof. vm_refl. Qed.
Lemma D_d9b00 : decode_any W_d9b00 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b04 : bv 32 := 0xff060613.
Lemma F_d9b04 : fetch_word Asan.M.loaded_segments (0xd9b68 : word) = Some W_d9b04.
Proof. vm_refl. Qed.
Lemma D_d9b04 : decode_any W_d9b04 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b08 : bv 32 := 0x0106a023.
Lemma F_d9b08 : fetch_word Asan.M.loaded_segments (0xd9b6c : word) = Some W_d9b08.
Proof. vm_refl. Qed.
Lemma D_d9b08 : decode_any W_d9b08 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b0c : bv 32 := 0x0116a223.
Lemma F_d9b0c : fetch_word Asan.M.loaded_segments (0xd9b70 : word) = Some W_d9b0c.
Proof. vm_refl. Qed.
Lemma D_d9b0c : decode_any W_d9b0c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b10 : bv 32 := 0x0056a423.
Lemma F_d9b10 : fetch_word Asan.M.loaded_segments (0xd9b74 : word) = Some W_d9b10.
Proof. vm_refl. Qed.
Lemma D_d9b10 : decode_any W_d9b10 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b14 : bv 32 := 0x0066a623.
Lemma F_d9b14 : fetch_word Asan.M.loaded_segments (0xd9b78 : word) = Some W_d9b14.
Proof. vm_refl. Qed.
Lemma D_d9b14 : decode_any W_d9b14 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b18 : bv 32 := 0x01068693.
Lemma F_d9b18 : fetch_word Asan.M.loaded_segments (0xd9b7c : word) = Some W_d9b18.
Proof. vm_refl. Qed.
Lemma D_d9b18 : decode_any W_d9b18 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b1c : bv 32 := 0x01058593.
Lemma F_d9b1c : fetch_word Asan.M.loaded_segments (0xd9b80 : word) = Some W_d9b1c.
Proof. vm_refl. Qed.
Lemma D_d9b1c : decode_any W_d9b1c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b20 : bv 32 := 0xfac7e2e3.
Lemma F_d9b20 : fetch_word Asan.M.loaded_segments (0xd9b84 : word) = Some W_d9b20.
Proof. vm_refl. Qed.
Lemma D_d9b20 : decode_any W_d9b20 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b24 : bv 32 := 0xff358593.
Lemma F_d9b24 : fetch_word Asan.M.loaded_segments (0xd9b88 : word) = Some W_d9b24.
Proof. vm_refl. Qed.
Lemma D_d9b24 : decode_any W_d9b24 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b28 : bv 32 := 0x01000713.
Lemma F_d9b28 : fetch_word Asan.M.loaded_segments (0xd9b8c : word) = Some W_d9b28.
Proof. vm_refl. Qed.
Lemma D_d9b28 : decode_any W_d9b28 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b2c : bv 32 := 0xdae66ce3.
Lemma F_d9b2c : fetch_word Asan.M.loaded_segments (0xd9b90 : word) = Some W_d9b2c.
Proof. vm_refl. Qed.
Lemma D_d9b2c : decode_any W_d9b2c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b30 : bv 32 := 0x0005c703.
Lemma F_d9b30 : fetch_word Asan.M.loaded_segments (0xd9b94 : word) = Some W_d9b30.
Proof. vm_refl. Qed.
Lemma D_d9b30 : decode_any W_d9b30 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b34 : bv 32 := 0x0015c783.
Lemma F_d9b34 : fetch_word Asan.M.loaded_segments (0xd9b98 : word) = Some W_d9b34.
Proof. vm_refl. Qed.
Lemma D_d9b34 : decode_any W_d9b34 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b38 : bv 32 := 0x0025c803.
Lemma F_d9b38 : fetch_word Asan.M.loaded_segments (0xd9b9c : word) = Some W_d9b38.
Proof. vm_refl. Qed.
Lemma D_d9b38 : decode_any W_d9b38 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b3c : bv 32 := 0x0035c883.
Lemma F_d9b3c : fetch_word Asan.M.loaded_segments (0xd9ba0 : word) = Some W_d9b3c.
Proof. vm_refl. Qed.
Lemma D_d9b3c : decode_any W_d9b3c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b40 : bv 32 := 0x0045c283.
Lemma F_d9b40 : fetch_word Asan.M.loaded_segments (0xd9ba4 : word) = Some W_d9b40.
Proof. vm_refl. Qed.
Lemma D_d9b40 : decode_any W_d9b40 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b44 : bv 32 := 0x0055c303.
Lemma F_d9b44 : fetch_word Asan.M.loaded_segments (0xd9ba8 : word) = Some W_d9b44.
Proof. vm_refl. Qed.
Lemma D_d9b44 : decode_any W_d9b44 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b48 : bv 32 := 0x0065c383.
Lemma F_d9b48 : fetch_word Asan.M.loaded_segments (0xd9bac : word) = Some W_d9b48.
Proof. vm_refl. Qed.
Lemma D_d9b48 : decode_any W_d9b48 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b4c : bv 32 := 0x0075ce03.
Lemma F_d9b4c : fetch_word Asan.M.loaded_segments (0xd9bb0 : word) = Some W_d9b4c.
Proof. vm_refl. Qed.
Lemma D_d9b4c : decode_any W_d9b4c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b50 : bv 32 := 0x00e68023.
Lemma F_d9b50 : fetch_word Asan.M.loaded_segments (0xd9bb4 : word) = Some W_d9b50.
Proof. vm_refl. Qed.
Lemma D_d9b50 : decode_any W_d9b50 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b54 : bv 32 := 0x00f680a3.
Lemma F_d9b54 : fetch_word Asan.M.loaded_segments (0xd9bb8 : word) = Some W_d9b54.
Proof. vm_refl. Qed.
Lemma D_d9b54 : decode_any W_d9b54 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b58 : bv 32 := 0x01068123.
Lemma F_d9b58 : fetch_word Asan.M.loaded_segments (0xd9bbc : word) = Some W_d9b58.
Proof. vm_refl. Qed.
Lemma D_d9b58 : decode_any W_d9b58 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b5c : bv 32 := 0x011681a3.
Lemma F_d9b5c : fetch_word Asan.M.loaded_segments (0xd9bc0 : word) = Some W_d9b5c.
Proof. vm_refl. Qed.
Lemma D_d9b5c : decode_any W_d9b5c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b60 : bv 32 := 0x0085c703.
Lemma F_d9b60 : fetch_word Asan.M.loaded_segments (0xd9bc4 : word) = Some W_d9b60.
Proof. vm_refl. Qed.
Lemma D_d9b60 : decode_any W_d9b60 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b64 : bv 32 := 0x0095c783.
Lemma F_d9b64 : fetch_word Asan.M.loaded_segments (0xd9bc8 : word) = Some W_d9b64.
Proof. vm_refl. Qed.
Lemma D_d9b64 : decode_any W_d9b64 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b68 : bv 32 := 0x00a5c803.
Lemma F_d9b68 : fetch_word Asan.M.loaded_segments (0xd9bcc : word) = Some W_d9b68.
Proof. vm_refl. Qed.
Lemma D_d9b68 : decode_any W_d9b68 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b6c : bv 32 := 0x00b5c883.
Lemma F_d9b6c : fetch_word Asan.M.loaded_segments (0xd9bd0 : word) = Some W_d9b6c.
Proof. vm_refl. Qed.
Lemma D_d9b6c : decode_any W_d9b6c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b70 : bv 32 := 0x00568223.
Lemma F_d9b70 : fetch_word Asan.M.loaded_segments (0xd9bd4 : word) = Some W_d9b70.
Proof. vm_refl. Qed.
Lemma D_d9b70 : decode_any W_d9b70 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b74 : bv 32 := 0x006682a3.
Lemma F_d9b74 : fetch_word Asan.M.loaded_segments (0xd9bd8 : word) = Some W_d9b74.
Proof. vm_refl. Qed.
Lemma D_d9b74 : decode_any W_d9b74 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b78 : bv 32 := 0x00768323.
Lemma F_d9b78 : fetch_word Asan.M.loaded_segments (0xd9bdc : word) = Some W_d9b78.
Proof. vm_refl. Qed.
Lemma D_d9b78 : decode_any W_d9b78 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b7c : bv 32 := 0x01c683a3.
Lemma F_d9b7c : fetch_word Asan.M.loaded_segments (0xd9be0 : word) = Some W_d9b7c.
Proof. vm_refl. Qed.
Lemma D_d9b7c : decode_any W_d9b7c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b80 : bv 32 := 0x00c5c283.
Lemma F_d9b80 : fetch_word Asan.M.loaded_segments (0xd9be4 : word) = Some W_d9b80.
Proof. vm_refl. Qed.
Lemma D_d9b80 : decode_any W_d9b80 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b84 : bv 32 := 0x00d5c303.
Lemma F_d9b84 : fetch_word Asan.M.loaded_segments (0xd9be8 : word) = Some W_d9b84.
Proof. vm_refl. Qed.
Lemma D_d9b84 : decode_any W_d9b84 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b88 : bv 32 := 0x00e5c383.
Lemma F_d9b88 : fetch_word Asan.M.loaded_segments (0xd9bec : word) = Some W_d9b88.
Proof. vm_refl. Qed.
Lemma D_d9b88 : decode_any W_d9b88 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b8c : bv 32 := 0x00f5ce03.
Lemma F_d9b8c : fetch_word Asan.M.loaded_segments (0xd9bf0 : word) = Some W_d9b8c.
Proof. vm_refl. Qed.
Lemma D_d9b8c : decode_any W_d9b8c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b90 : bv 32 := 0x01058593.
Lemma F_d9b90 : fetch_word Asan.M.loaded_segments (0xd9bf4 : word) = Some W_d9b90.
Proof. vm_refl. Qed.
Lemma D_d9b90 : decode_any W_d9b90 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b94 : bv 32 := 0x00e68423.
Lemma F_d9b94 : fetch_word Asan.M.loaded_segments (0xd9bf8 : word) = Some W_d9b94.
Proof. vm_refl. Qed.
Lemma D_d9b94 : decode_any W_d9b94 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b98 : bv 32 := 0x00f684a3.
Lemma F_d9b98 : fetch_word Asan.M.loaded_segments (0xd9bfc : word) = Some W_d9b98.
Proof. vm_refl. Qed.
Lemma D_d9b98 : decode_any W_d9b98 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9b9c : bv 32 := 0x01068523.
Lemma F_d9b9c : fetch_word Asan.M.loaded_segments (0xd9c00 : word) = Some W_d9b9c.
Proof. vm_refl. Qed.
Lemma D_d9b9c : decode_any W_d9b9c = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ba0 : bv 32 := 0x011685a3.
Lemma F_d9ba0 : fetch_word Asan.M.loaded_segments (0xd9c04 : word) = Some W_d9ba0.
Proof. vm_refl. Qed.
Lemma D_d9ba0 : decode_any W_d9ba0 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ba4 : bv 32 := 0x01068713.
Lemma F_d9ba4 : fetch_word Asan.M.loaded_segments (0xd9c08 : word) = Some W_d9ba4.
Proof. vm_refl. Qed.
Lemma D_d9ba4 : decode_any W_d9ba4 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ba8 : bv 32 := 0x00568623.
Lemma F_d9ba8 : fetch_word Asan.M.loaded_segments (0xd9c0c : word) = Some W_d9ba8.
Proof. vm_refl. Qed.
Lemma D_d9ba8 : decode_any W_d9ba8 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bac : bv 32 := 0x006686a3.
Lemma F_d9bac : fetch_word Asan.M.loaded_segments (0xd9c10 : word) = Some W_d9bac.
Proof. vm_refl. Qed.
Lemma D_d9bac : decode_any W_d9bac = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bb0 : bv 32 := 0x00768723.
Lemma F_d9bb0 : fetch_word Asan.M.loaded_segments (0xd9c14 : word) = Some W_d9bb0.
Proof. vm_refl. Qed.
Lemma D_d9bb0 : decode_any W_d9bb0 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bb4 : bv 32 := 0x01c687a3.
Lemma F_d9bb4 : fetch_word Asan.M.loaded_segments (0xd9c18 : word) = Some W_d9bb4.
Proof. vm_refl. Qed.
Lemma D_d9bb4 : decode_any W_d9bb4 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bb8 : bv 32 := 0x00070693.
Lemma F_d9bb8 : fetch_word Asan.M.loaded_segments (0xd9c1c : word) = Some W_d9bb8.
Proof. vm_refl. Qed.
Lemma D_d9bb8 : decode_any W_d9bb8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bbc : bv 32 := 0x00867713.
Lemma F_d9bbc : fetch_word Asan.M.loaded_segments (0xd9c20 : word) = Some W_d9bbc.
Proof. vm_refl. Qed.
Lemma D_d9bbc : decode_any W_d9bbc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bc0 : bv 32 := 0xd20706e3.
Lemma F_d9bc0 : fetch_word Asan.M.loaded_segments (0xd9c24 : word) = Some W_d9bc0.
Proof. vm_refl. Qed.
Lemma D_d9bc0 : decode_any W_d9bc0 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bc4 : bv 32 := 0x0005c703.
Lemma F_d9bc4 : fetch_word Asan.M.loaded_segments (0xd9c28 : word) = Some W_d9bc4.
Proof. vm_refl. Qed.
Lemma D_d9bc4 : decode_any W_d9bc4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bc8 : bv 32 := 0x0015c783.
Lemma F_d9bc8 : fetch_word Asan.M.loaded_segments (0xd9c2c : word) = Some W_d9bc8.
Proof. vm_refl. Qed.
Lemma D_d9bc8 : decode_any W_d9bc8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bcc : bv 32 := 0x0025c803.
Lemma F_d9bcc : fetch_word Asan.M.loaded_segments (0xd9c30 : word) = Some W_d9bcc.
Proof. vm_refl. Qed.
Lemma D_d9bcc : decode_any W_d9bcc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bd0 : bv 32 := 0x0035c883.
Lemma F_d9bd0 : fetch_word Asan.M.loaded_segments (0xd9c34 : word) = Some W_d9bd0.
Proof. vm_refl. Qed.
Lemma D_d9bd0 : decode_any W_d9bd0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bd4 : bv 32 := 0x0045c283.
Lemma F_d9bd4 : fetch_word Asan.M.loaded_segments (0xd9c38 : word) = Some W_d9bd4.
Proof. vm_refl. Qed.
Lemma D_d9bd4 : decode_any W_d9bd4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bd8 : bv 32 := 0x0055c303.
Lemma F_d9bd8 : fetch_word Asan.M.loaded_segments (0xd9c3c : word) = Some W_d9bd8.
Proof. vm_refl. Qed.
Lemma D_d9bd8 : decode_any W_d9bd8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bdc : bv 32 := 0x0065c383.
Lemma F_d9bdc : fetch_word Asan.M.loaded_segments (0xd9c40 : word) = Some W_d9bdc.
Proof. vm_refl. Qed.
Lemma D_d9bdc : decode_any W_d9bdc = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9be0 : bv 32 := 0x0075ce03.
Lemma F_d9be0 : fetch_word Asan.M.loaded_segments (0xd9c44 : word) = Some W_d9be0.
Proof. vm_refl. Qed.
Lemma D_d9be0 : decode_any W_d9be0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9be4 : bv 32 := 0x00858593.
Lemma F_d9be4 : fetch_word Asan.M.loaded_segments (0xd9c48 : word) = Some W_d9be4.
Proof. vm_refl. Qed.
Lemma D_d9be4 : decode_any W_d9be4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9be8 : bv 32 := 0x00e68023.
Lemma F_d9be8 : fetch_word Asan.M.loaded_segments (0xd9c4c : word) = Some W_d9be8.
Proof. vm_refl. Qed.
Lemma D_d9be8 : decode_any W_d9be8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bec : bv 32 := 0x00f680a3.
Lemma F_d9bec : fetch_word Asan.M.loaded_segments (0xd9c50 : word) = Some W_d9bec.
Proof. vm_refl. Qed.
Lemma D_d9bec : decode_any W_d9bec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bf0 : bv 32 := 0x01068123.
Lemma F_d9bf0 : fetch_word Asan.M.loaded_segments (0xd9c54 : word) = Some W_d9bf0.
Proof. vm_refl. Qed.
Lemma D_d9bf0 : decode_any W_d9bf0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bf4 : bv 32 := 0x011681a3.
Lemma F_d9bf4 : fetch_word Asan.M.loaded_segments (0xd9c58 : word) = Some W_d9bf4.
Proof. vm_refl. Qed.
Lemma D_d9bf4 : decode_any W_d9bf4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bf8 : bv 32 := 0x00868713.
Lemma F_d9bf8 : fetch_word Asan.M.loaded_segments (0xd9c5c : word) = Some W_d9bf8.
Proof. vm_refl. Qed.
Lemma D_d9bf8 : decode_any W_d9bf8 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9bfc : bv 32 := 0x00568223.
Lemma F_d9bfc : fetch_word Asan.M.loaded_segments (0xd9c60 : word) = Some W_d9bfc.
Proof. vm_refl. Qed.
Lemma D_d9bfc : decode_any W_d9bfc = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c00 : bv 32 := 0x006682a3.
Lemma F_d9c00 : fetch_word Asan.M.loaded_segments (0xd9c64 : word) = Some W_d9c00.
Proof. vm_refl. Qed.
Lemma D_d9c00 : decode_any W_d9c00 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c04 : bv 32 := 0x00768323.
Lemma F_d9c04 : fetch_word Asan.M.loaded_segments (0xd9c68 : word) = Some W_d9c04.
Proof. vm_refl. Qed.
Lemma D_d9c04 : decode_any W_d9c04 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c08 : bv 32 := 0x01c683a3.
Lemma F_d9c08 : fetch_word Asan.M.loaded_segments (0xd9c6c : word) = Some W_d9c08.
Proof. vm_refl. Qed.
Lemma D_d9c08 : decode_any W_d9c08 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c0c : bv 32 := 0x00070693.
Lemma F_d9c0c : fetch_word Asan.M.loaded_segments (0xd9c70 : word) = Some W_d9c0c.
Proof. vm_refl. Qed.
Lemma D_d9c0c : decode_any W_d9c0c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c10 : bv 32 := 0x00467713.
Lemma F_d9c10 : fetch_word Asan.M.loaded_segments (0xd9c74 : word) = Some W_d9c10.
Proof. vm_refl. Qed.
Lemma D_d9c10 : decode_any W_d9c10 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c14 : bv 32 := 0x02070863.
Lemma F_d9c14 : fetch_word Asan.M.loaded_segments (0xd9c78 : word) = Some W_d9c14.
Proof. vm_refl. Qed.
Lemma D_d9c14 : decode_any W_d9c14 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c18 : bv 32 := 0x0005c703.
Lemma F_d9c18 : fetch_word Asan.M.loaded_segments (0xd9c7c : word) = Some W_d9c18.
Proof. vm_refl. Qed.
Lemma D_d9c18 : decode_any W_d9c18 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c1c : bv 32 := 0x0015c783.
Lemma F_d9c1c : fetch_word Asan.M.loaded_segments (0xd9c80 : word) = Some W_d9c1c.
Proof. vm_refl. Qed.
Lemma D_d9c1c : decode_any W_d9c1c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c20 : bv 32 := 0x0025c803.
Lemma F_d9c20 : fetch_word Asan.M.loaded_segments (0xd9c84 : word) = Some W_d9c20.
Proof. vm_refl. Qed.
Lemma D_d9c20 : decode_any W_d9c20 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c24 : bv 32 := 0x0035c883.
Lemma F_d9c24 : fetch_word Asan.M.loaded_segments (0xd9c88 : word) = Some W_d9c24.
Proof. vm_refl. Qed.
Lemma D_d9c24 : decode_any W_d9c24 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c28 : bv 32 := 0x00458593.
Lemma F_d9c28 : fetch_word Asan.M.loaded_segments (0xd9c8c : word) = Some W_d9c28.
Proof. vm_refl. Qed.
Lemma D_d9c28 : decode_any W_d9c28 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c2c : bv 32 := 0x00468293.
Lemma F_d9c2c : fetch_word Asan.M.loaded_segments (0xd9c90 : word) = Some W_d9c2c.
Proof. vm_refl. Qed.
Lemma D_d9c2c : decode_any W_d9c2c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c30 : bv 32 := 0x00e68023.
Lemma F_d9c30 : fetch_word Asan.M.loaded_segments (0xd9c94 : word) = Some W_d9c30.
Proof. vm_refl. Qed.
Lemma D_d9c30 : decode_any W_d9c30 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c34 : bv 32 := 0x00f680a3.
Lemma F_d9c34 : fetch_word Asan.M.loaded_segments (0xd9c98 : word) = Some W_d9c34.
Proof. vm_refl. Qed.
Lemma D_d9c34 : decode_any W_d9c34 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c38 : bv 32 := 0x01068123.
Lemma F_d9c38 : fetch_word Asan.M.loaded_segments (0xd9c9c : word) = Some W_d9c38.
Proof. vm_refl. Qed.
Lemma D_d9c38 : decode_any W_d9c38 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c3c : bv 32 := 0x011681a3.
Lemma F_d9c3c : fetch_word Asan.M.loaded_segments (0xd9ca0 : word) = Some W_d9c3c.
Proof. vm_refl. Qed.
Lemma D_d9c3c : decode_any W_d9c3c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c40 : bv 32 := 0x00028693.
Lemma F_d9c40 : fetch_word Asan.M.loaded_segments (0xd9ca4 : word) = Some W_d9c40.
Proof. vm_refl. Qed.
Lemma D_d9c40 : decode_any W_d9c40 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c44 : bv 32 := 0x00267713.
Lemma F_d9c44 : fetch_word Asan.M.loaded_segments (0xd9ca8 : word) = Some W_d9c44.
Proof. vm_refl. Qed.
Lemma D_d9c44 : decode_any W_d9c44 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c48 : bv 32 := 0x00071863.
Lemma F_d9c48 : fetch_word Asan.M.loaded_segments (0xd9cac : word) = Some W_d9c48.
Proof. vm_refl. Qed.
Lemma D_d9c48 : decode_any W_d9c48 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c4c : bv 32 := 0x00167613.
Lemma F_d9c4c : fetch_word Asan.M.loaded_segments (0xd9cb0 : word) = Some W_d9c4c.
Proof. vm_refl. Qed.
Lemma D_d9c4c : decode_any W_d9c4c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c50 : bv 32 := 0x02061663.
Lemma F_d9c50 : fetch_word Asan.M.loaded_segments (0xd9cb4 : word) = Some W_d9c50.
Proof. vm_refl. Qed.
Lemma D_d9c50 : decode_any W_d9c50 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c54 : bv 32 := 0x00008067.
Lemma F_d9c54 : fetch_word Asan.M.loaded_segments (0xd9cb8 : word) = Some W_d9c54.
Proof. vm_refl. Qed.
Lemma D_d9c54 : decode_any W_d9c54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c58 : bv 32 := 0x0005c703.
Lemma F_d9c58 : fetch_word Asan.M.loaded_segments (0xd9cbc : word) = Some W_d9c58.
Proof. vm_refl. Qed.
Lemma D_d9c58 : decode_any W_d9c58 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c5c : bv 32 := 0x0015c783.
Lemma F_d9c5c : fetch_word Asan.M.loaded_segments (0xd9cc0 : word) = Some W_d9c5c.
Proof. vm_refl. Qed.
Lemma D_d9c5c : decode_any W_d9c5c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c60 : bv 32 := 0x00258593.
Lemma F_d9c60 : fetch_word Asan.M.loaded_segments (0xd9cc4 : word) = Some W_d9c60.
Proof. vm_refl. Qed.
Lemma D_d9c60 : decode_any W_d9c60 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c64 : bv 32 := 0x00268813.
Lemma F_d9c64 : fetch_word Asan.M.loaded_segments (0xd9cc8 : word) = Some W_d9c64.
Proof. vm_refl. Qed.
Lemma D_d9c64 : decode_any W_d9c64 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c68 : bv 32 := 0x00e68023.
Lemma F_d9c68 : fetch_word Asan.M.loaded_segments (0xd9ccc : word) = Some W_d9c68.
Proof. vm_refl. Qed.
Lemma D_d9c68 : decode_any W_d9c68 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c6c : bv 32 := 0x00f680a3.
Lemma F_d9c6c : fetch_word Asan.M.loaded_segments (0xd9cd0 : word) = Some W_d9c6c.
Proof. vm_refl. Qed.
Lemma D_d9c6c : decode_any W_d9c6c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c70 : bv 32 := 0x00080693.
Lemma F_d9c70 : fetch_word Asan.M.loaded_segments (0xd9cd4 : word) = Some W_d9c70.
Proof. vm_refl. Qed.
Lemma D_d9c70 : decode_any W_d9c70 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c74 : bv 32 := 0x00167613.
Lemma F_d9c74 : fetch_word Asan.M.loaded_segments (0xd9cd8 : word) = Some W_d9c74.
Proof. vm_refl. Qed.
Lemma D_d9c74 : decode_any W_d9c74 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c78 : bv 32 := 0xfc060ee3.
Lemma F_d9c78 : fetch_word Asan.M.loaded_segments (0xd9cdc : word) = Some W_d9c78.
Proof. vm_refl. Qed.
Lemma D_d9c78 : decode_any W_d9c78 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c7c : bv 32 := 0x0005c583.
Lemma F_d9c7c : fetch_word Asan.M.loaded_segments (0xd9ce0 : word) = Some W_d9c7c.
Proof. vm_refl. Qed.
Lemma D_d9c7c : decode_any W_d9c7c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c80 : bv 32 := 0x00b68023.
Lemma F_d9c80 : fetch_word Asan.M.loaded_segments (0xd9ce4 : word) = Some W_d9c80.
Proof. vm_refl. Qed.
Lemma D_d9c80 : decode_any W_d9c80 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c84 : bv 32 := 0x00008067.
Lemma F_d9c84 : fetch_word Asan.M.loaded_segments (0xd9ce8 : word) = Some W_d9c84.
Proof. vm_refl. Qed.
Lemma D_d9c84 : decode_any W_d9c84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
