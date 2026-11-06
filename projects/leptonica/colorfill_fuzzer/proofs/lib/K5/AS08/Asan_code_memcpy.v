(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Asan.
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
Definition W_be87c : bv 32 := 0x0035f693.
Lemma F_be87c : fetch_word Asan.M.loaded_segments (0xc2134 : word) = Some W_be87c.
Proof. vm_refl. Qed.
Lemma D_be87c : decode_any W_be87c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be880 : bv 32 := 0x10068863.
Lemma F_be880 : fetch_word Asan.M.loaded_segments (0xc2138 : word) = Some W_be880.
Proof. vm_refl. Qed.
Lemma D_be880 : decode_any W_be880 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be884 : bv 32 := 0x02060e63.
Lemma F_be884 : fetch_word Asan.M.loaded_segments (0xc213c : word) = Some W_be884.
Proof. vm_refl. Qed.
Lemma D_be884 : decode_any W_be884 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be888 : bv 32 := 0x00158713.
Lemma F_be888 : fetch_word Asan.M.loaded_segments (0xc2140 : word) = Some W_be888.
Proof. vm_refl. Qed.
Lemma D_be888 : decode_any W_be888 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be88c : bv 32 := 0x00100793.
Lemma F_be88c : fetch_word Asan.M.loaded_segments (0xc2144 : word) = Some W_be88c.
Proof. vm_refl. Qed.
Lemma D_be88c : decode_any W_be88c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be890 : bv 32 := 0x00050693.
Lemma F_be890 : fetch_word Asan.M.loaded_segments (0xc2148 : word) = Some W_be890.
Proof. vm_refl. Qed.
Lemma D_be890 : decode_any W_be890 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be894 : bv 32 := 0x0005c883.
Lemma F_be894 : fetch_word Asan.M.loaded_segments (0xc214c : word) = Some W_be894.
Proof. vm_refl. Qed.
Lemma D_be894 : decode_any W_be894 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be898 : bv 32 := 0x00060813.
Lemma F_be898 : fetch_word Asan.M.loaded_segments (0xc2150 : word) = Some W_be898.
Proof. vm_refl. Qed.
Lemma D_be898 : decode_any W_be898 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be89c : bv 32 := 0x00158593.
Lemma F_be89c : fetch_word Asan.M.loaded_segments (0xc2154 : word) = Some W_be89c.
Proof. vm_refl. Qed.
Lemma D_be89c : decode_any W_be89c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8a0 : bv 32 := 0x00377293.
Lemma F_be8a0 : fetch_word Asan.M.loaded_segments (0xc2158 : word) = Some W_be8a0.
Proof. vm_refl. Qed.
Lemma D_be8a0 : decode_any W_be8a0 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8a4 : bv 32 := 0x01168023.
Lemma F_be8a4 : fetch_word Asan.M.loaded_segments (0xc215c : word) = Some W_be8a4.
Proof. vm_refl. Qed.
Lemma D_be8a4 : decode_any W_be8a4 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8a8 : bv 32 := 0x00168693.
Lemma F_be8a8 : fetch_word Asan.M.loaded_segments (0xc2160 : word) = Some W_be8a8.
Proof. vm_refl. Qed.
Lemma D_be8a8 : decode_any W_be8a8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8ac : bv 32 := 0xfff60613.
Lemma F_be8ac : fetch_word Asan.M.loaded_segments (0xc2164 : word) = Some W_be8ac.
Proof. vm_refl. Qed.
Lemma D_be8ac : decode_any W_be8ac = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8b0 : bv 32 := 0x00028a63.
Lemma F_be8b0 : fetch_word Asan.M.loaded_segments (0xc2168 : word) = Some W_be8b0.
Proof. vm_refl. Qed.
Lemma D_be8b0 : decode_any W_be8b0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8b4 : bv 32 := 0x00170713.
Lemma F_be8b4 : fetch_word Asan.M.loaded_segments (0xc216c : word) = Some W_be8b4.
Proof. vm_refl. Qed.
Lemma D_be8b4 : decode_any W_be8b4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8b8 : bv 32 := 0xfcf81ee3.
Lemma F_be8b8 : fetch_word Asan.M.loaded_segments (0xc2170 : word) = Some W_be8b8.
Proof. vm_refl. Qed.
Lemma D_be8b8 : decode_any W_be8b8 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8bc : bv 32 := 0x0080006f.
Lemma F_be8bc : fetch_word Asan.M.loaded_segments (0xc2174 : word) = Some W_be8bc.
Proof. vm_refl. Qed.
Lemma D_be8bc : decode_any W_be8bc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8c0 : bv 32 := 0x00050693.
Lemma F_be8c0 : fetch_word Asan.M.loaded_segments (0xc2178 : word) = Some W_be8c0.
Proof. vm_refl. Qed.
Lemma D_be8c0 : decode_any W_be8c0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8c4 : bv 32 := 0x0036f793.
Lemma F_be8c4 : fetch_word Asan.M.loaded_segments (0xc217c : word) = Some W_be8c4.
Proof. vm_refl. Qed.
Lemma D_be8c4 : decode_any W_be8c4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8c8 : bv 32 := 0x0c078a63.
Lemma F_be8c8 : fetch_word Asan.M.loaded_segments (0xc2180 : word) = Some W_be8c8.
Proof. vm_refl. Qed.
Lemma D_be8c8 : decode_any W_be8c8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8cc : bv 32 := 0x02000713.
Lemma F_be8cc : fetch_word Asan.M.loaded_segments (0xc2184 : word) = Some W_be8cc.
Proof. vm_refl. Qed.
Lemma D_be8cc : decode_any W_be8cc = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8d0 : bv 32 := 0x02e67063.
Lemma F_be8d0 : fetch_word Asan.M.loaded_segments (0xc2188 : word) = Some W_be8d0.
Proof. vm_refl. Qed.
Lemma D_be8d0 : decode_any W_be8d0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8d4 : bv 32 := 0x01000713.
Lemma F_be8d4 : fetch_word Asan.M.loaded_segments (0xc218c : word) = Some W_be8d4.
Proof. vm_refl. Qed.
Lemma D_be8d4 : decode_any W_be8d4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8d8 : bv 32 := 0x24e67863.
Lemma F_be8d8 : fetch_word Asan.M.loaded_segments (0xc2190 : word) = Some W_be8d8.
Proof. vm_refl. Qed.
Lemma D_be8d8 : decode_any W_be8d8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8dc : bv 32 := 0x00867713.
Lemma F_be8dc : fetch_word Asan.M.loaded_segments (0xc2194 : word) = Some W_be8dc.
Proof. vm_refl. Qed.
Lemma D_be8dc : decode_any W_be8dc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8e0 : bv 32 := 0x2c071e63.
Lemma F_be8e0 : fetch_word Asan.M.loaded_segments (0xc2198 : word) = Some W_be8e0.
Proof. vm_refl. Qed.
Lemma D_be8e0 : decode_any W_be8e0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8e4 : bv 32 := 0x00467713.
Lemma F_be8e4 : fetch_word Asan.M.loaded_segments (0xc219c : word) = Some W_be8e4.
Proof. vm_refl. Qed.
Lemma D_be8e4 : decode_any W_be8e4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8e8 : bv 32 := 0x32071463.
Lemma F_be8e8 : fetch_word Asan.M.loaded_segments (0xc21a0 : word) = Some W_be8e8.
Proof. vm_refl. Qed.
Lemma D_be8e8 : decode_any W_be8e8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8ec : bv 32 := 0x3500006f.
Lemma F_be8ec : fetch_word Asan.M.loaded_segments (0xc21a4 : word) = Some W_be8ec.
Proof. vm_refl. Qed.
Lemma D_be8ec : decode_any W_be8ec = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8f0 : bv 32 := 0x0005a703.
Lemma F_be8f0 : fetch_word Asan.M.loaded_segments (0xc21a8 : word) = Some W_be8f0.
Proof. vm_refl. Qed.
Lemma D_be8f0 : decode_any W_be8f0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8f4 : bv 32 := 0x00300813.
Lemma F_be8f4 : fetch_word Asan.M.loaded_segments (0xc21ac : word) = Some W_be8f4.
Proof. vm_refl. Qed.
Lemma D_be8f4 : decode_any W_be8f4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8f8 : bv 32 := 0x11078e63.
Lemma F_be8f8 : fetch_word Asan.M.loaded_segments (0xc21b0 : word) = Some W_be8f8.
Proof. vm_refl. Qed.
Lemma D_be8f8 : decode_any W_be8f8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be8fc : bv 32 := 0x00200813.
Lemma F_be8fc : fetch_word Asan.M.loaded_segments (0xc21b4 : word) = Some W_be8fc.
Proof. vm_refl. Qed.
Lemma D_be8fc : decode_any W_be8fc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be900 : bv 32 := 0x19079c63.
Lemma F_be900 : fetch_word Asan.M.loaded_segments (0xc21b8 : word) = Some W_be900.
Proof. vm_refl. Qed.
Lemma D_be900 : decode_any W_be900 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be904 : bv 32 := 0x00875793.
Lemma F_be904 : fetch_word Asan.M.loaded_segments (0xc21bc : word) = Some W_be904.
Proof. vm_refl. Qed.
Lemma D_be904 : decode_any W_be904 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be908 : bv 32 := 0xffe60613.
Lemma F_be908 : fetch_word Asan.M.loaded_segments (0xc21c0 : word) = Some W_be908.
Proof. vm_refl. Qed.
Lemma D_be908 : decode_any W_be908 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be90c : bv 32 := 0x00e68023.
Lemma F_be90c : fetch_word Asan.M.loaded_segments (0xc21c4 : word) = Some W_be90c.
Proof. vm_refl. Qed.
Lemma D_be90c : decode_any W_be90c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be910 : bv 32 := 0x00f680a3.
Lemma F_be910 : fetch_word Asan.M.loaded_segments (0xc21c8 : word) = Some W_be910.
Proof. vm_refl. Qed.
Lemma D_be910 : decode_any W_be910 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be914 : bv 32 := 0x00268693.
Lemma F_be914 : fetch_word Asan.M.loaded_segments (0xc21cc : word) = Some W_be914.
Proof. vm_refl. Qed.
Lemma D_be914 : decode_any W_be914 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be918 : bv 32 := 0x01058593.
Lemma F_be918 : fetch_word Asan.M.loaded_segments (0xc21d0 : word) = Some W_be918.
Proof. vm_refl. Qed.
Lemma D_be918 : decode_any W_be918 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be91c : bv 32 := 0x01100793.
Lemma F_be91c : fetch_word Asan.M.loaded_segments (0xc21d4 : word) = Some W_be91c.
Proof. vm_refl. Qed.
Lemma D_be91c : decode_any W_be91c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be920 : bv 32 := 0x0107581b.
Lemma F_be920 : fetch_word Asan.M.loaded_segments (0xc21d8 : word) = Some W_be920.
Proof. vm_refl. Qed.
Lemma D_be920 : decode_any W_be920 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be924 : bv 32 := 0xff45a883.
Lemma F_be924 : fetch_word Asan.M.loaded_segments (0xc21dc : word) = Some W_be924.
Proof. vm_refl. Qed.
Lemma D_be924 : decode_any W_be924 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be928 : bv 32 := 0xff85a283.
Lemma F_be928 : fetch_word Asan.M.loaded_segments (0xc21e0 : word) = Some W_be928.
Proof. vm_refl. Qed.
Lemma D_be928 : decode_any W_be928 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be92c : bv 32 := 0xffc5a303.
Lemma F_be92c : fetch_word Asan.M.loaded_segments (0xc21e4 : word) = Some W_be92c.
Proof. vm_refl. Qed.
Lemma D_be92c : decode_any W_be92c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be930 : bv 32 := 0x0005a703.
Lemma F_be930 : fetch_word Asan.M.loaded_segments (0xc21e8 : word) = Some W_be930.
Proof. vm_refl. Qed.
Lemma D_be930 : decode_any W_be930 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be934 : bv 32 := 0x01089393.
Lemma F_be934 : fetch_word Asan.M.loaded_segments (0xc21ec : word) = Some W_be934.
Proof. vm_refl. Qed.
Lemma D_be934 : decode_any W_be934 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be938 : bv 32 := 0x0108d89b.
Lemma F_be938 : fetch_word Asan.M.loaded_segments (0xc21f0 : word) = Some W_be938.
Proof. vm_refl. Qed.
Lemma D_be938 : decode_any W_be938 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be93c : bv 32 := 0x0103e833.
Lemma F_be93c : fetch_word Asan.M.loaded_segments (0xc21f4 : word) = Some W_be93c.
Proof. vm_refl. Qed.
Lemma D_be93c : decode_any W_be93c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be940 : bv 32 := 0x01029393.
Lemma F_be940 : fetch_word Asan.M.loaded_segments (0xc21f8 : word) = Some W_be940.
Proof. vm_refl. Qed.
Lemma D_be940 : decode_any W_be940 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be944 : bv 32 := 0x0102d29b.
Lemma F_be944 : fetch_word Asan.M.loaded_segments (0xc21fc : word) = Some W_be944.
Proof. vm_refl. Qed.
Lemma D_be944 : decode_any W_be944 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be948 : bv 32 := 0x0113e8b3.
Lemma F_be948 : fetch_word Asan.M.loaded_segments (0xc2200 : word) = Some W_be948.
Proof. vm_refl. Qed.
Lemma D_be948 : decode_any W_be948 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be94c : bv 32 := 0x01031393.
Lemma F_be94c : fetch_word Asan.M.loaded_segments (0xc2204 : word) = Some W_be94c.
Proof. vm_refl. Qed.
Lemma D_be94c : decode_any W_be94c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be950 : bv 32 := 0x0103531b.
Lemma F_be950 : fetch_word Asan.M.loaded_segments (0xc2208 : word) = Some W_be950.
Proof. vm_refl. Qed.
Lemma D_be950 : decode_any W_be950 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be954 : bv 32 := 0x0053e2b3.
Lemma F_be954 : fetch_word Asan.M.loaded_segments (0xc220c : word) = Some W_be954.
Proof. vm_refl. Qed.
Lemma D_be954 : decode_any W_be954 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be958 : bv 32 := 0x01071393.
Lemma F_be958 : fetch_word Asan.M.loaded_segments (0xc2210 : word) = Some W_be958.
Proof. vm_refl. Qed.
Lemma D_be958 : decode_any W_be958 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be95c : bv 32 := 0x0063e333.
Lemma F_be95c : fetch_word Asan.M.loaded_segments (0xc2214 : word) = Some W_be95c.
Proof. vm_refl. Qed.
Lemma D_be95c : decode_any W_be95c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be960 : bv 32 := 0xff060613.
Lemma F_be960 : fetch_word Asan.M.loaded_segments (0xc2218 : word) = Some W_be960.
Proof. vm_refl. Qed.
Lemma D_be960 : decode_any W_be960 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be964 : bv 32 := 0x0106a023.
Lemma F_be964 : fetch_word Asan.M.loaded_segments (0xc221c : word) = Some W_be964.
Proof. vm_refl. Qed.
Lemma D_be964 : decode_any W_be964 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be968 : bv 32 := 0x0116a223.
Lemma F_be968 : fetch_word Asan.M.loaded_segments (0xc2220 : word) = Some W_be968.
Proof. vm_refl. Qed.
Lemma D_be968 : decode_any W_be968 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be96c : bv 32 := 0x0056a423.
Lemma F_be96c : fetch_word Asan.M.loaded_segments (0xc2224 : word) = Some W_be96c.
Proof. vm_refl. Qed.
Lemma D_be96c : decode_any W_be96c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be970 : bv 32 := 0x0066a623.
Lemma F_be970 : fetch_word Asan.M.loaded_segments (0xc2228 : word) = Some W_be970.
Proof. vm_refl. Qed.
Lemma D_be970 : decode_any W_be970 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be974 : bv 32 := 0x01068693.
Lemma F_be974 : fetch_word Asan.M.loaded_segments (0xc222c : word) = Some W_be974.
Proof. vm_refl. Qed.
Lemma D_be974 : decode_any W_be974 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be978 : bv 32 := 0x01058593.
Lemma F_be978 : fetch_word Asan.M.loaded_segments (0xc2230 : word) = Some W_be978.
Proof. vm_refl. Qed.
Lemma D_be978 : decode_any W_be978 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be97c : bv 32 := 0xfac7e2e3.
Lemma F_be97c : fetch_word Asan.M.loaded_segments (0xc2234 : word) = Some W_be97c.
Proof. vm_refl. Qed.
Lemma D_be97c : decode_any W_be97c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be980 : bv 32 := 0xff258593.
Lemma F_be980 : fetch_word Asan.M.loaded_segments (0xc2238 : word) = Some W_be980.
Proof. vm_refl. Qed.
Lemma D_be980 : decode_any W_be980 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be984 : bv 32 := 0x01000713.
Lemma F_be984 : fetch_word Asan.M.loaded_segments (0xc223c : word) = Some W_be984.
Proof. vm_refl. Qed.
Lemma D_be984 : decode_any W_be984 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be988 : bv 32 := 0xf4e66ae3.
Lemma F_be988 : fetch_word Asan.M.loaded_segments (0xc2240 : word) = Some W_be988.
Proof. vm_refl. Qed.
Lemma D_be988 : decode_any W_be988 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be98c : bv 32 := 0x19c0006f.
Lemma F_be98c : fetch_word Asan.M.loaded_segments (0xc2244 : word) = Some W_be98c.
Proof. vm_refl. Qed.
Lemma D_be98c : decode_any W_be98c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be990 : bv 32 := 0x00050693.
Lemma F_be990 : fetch_word Asan.M.loaded_segments (0xc2248 : word) = Some W_be990.
Proof. vm_refl. Qed.
Lemma D_be990 : decode_any W_be990 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be994 : bv 32 := 0x00357793.
Lemma F_be994 : fetch_word Asan.M.loaded_segments (0xc224c : word) = Some W_be994.
Proof. vm_refl. Qed.
Lemma D_be994 : decode_any W_be994 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be998 : bv 32 := 0xf2079ae3.
Lemma F_be998 : fetch_word Asan.M.loaded_segments (0xc2250 : word) = Some W_be998.
Proof. vm_refl. Qed.
Lemma D_be998 : decode_any W_be998 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be99c : bv 32 := 0x01000713.
Lemma F_be99c : fetch_word Asan.M.loaded_segments (0xc2254 : word) = Some W_be99c.
Proof. vm_refl. Qed.
Lemma D_be99c : decode_any W_be99c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9a0 : bv 32 := 0x02e66c63.
Lemma F_be9a0 : fetch_word Asan.M.loaded_segments (0xc2258 : word) = Some W_be9a0.
Proof. vm_refl. Qed.
Lemma D_be9a0 : decode_any W_be9a0 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9a4 : bv 32 := 0x00f00713.
Lemma F_be9a4 : fetch_word Asan.M.loaded_segments (0xc225c : word) = Some W_be9a4.
Proof. vm_refl. Qed.
Lemma D_be9a4 : decode_any W_be9a4 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9a8 : bv 32 := 0x0005a783.
Lemma F_be9a8 : fetch_word Asan.M.loaded_segments (0xc2260 : word) = Some W_be9a8.
Proof. vm_refl. Qed.
Lemma D_be9a8 : decode_any W_be9a8 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9ac : bv 32 := 0x0045a803.
Lemma F_be9ac : fetch_word Asan.M.loaded_segments (0xc2264 : word) = Some W_be9ac.
Proof. vm_refl. Qed.
Lemma D_be9ac : decode_any W_be9ac = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9b0 : bv 32 := 0x0085a883.
Lemma F_be9b0 : fetch_word Asan.M.loaded_segments (0xc2268 : word) = Some W_be9b0.
Proof. vm_refl. Qed.
Lemma D_be9b0 : decode_any W_be9b0 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9b4 : bv 32 := 0x00c5a283.
Lemma F_be9b4 : fetch_word Asan.M.loaded_segments (0xc226c : word) = Some W_be9b4.
Proof. vm_refl. Qed.
Lemma D_be9b4 : decode_any W_be9b4 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9b8 : bv 32 := 0x01058593.
Lemma F_be9b8 : fetch_word Asan.M.loaded_segments (0xc2270 : word) = Some W_be9b8.
Proof. vm_refl. Qed.
Lemma D_be9b8 : decode_any W_be9b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9bc : bv 32 := 0xff060613.
Lemma F_be9bc : fetch_word Asan.M.loaded_segments (0xc2274 : word) = Some W_be9bc.
Proof. vm_refl. Qed.
Lemma D_be9bc : decode_any W_be9bc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9c0 : bv 32 := 0x00f6a023.
Lemma F_be9c0 : fetch_word Asan.M.loaded_segments (0xc2278 : word) = Some W_be9c0.
Proof. vm_refl. Qed.
Lemma D_be9c0 : decode_any W_be9c0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9c4 : bv 32 := 0x0106a223.
Lemma F_be9c4 : fetch_word Asan.M.loaded_segments (0xc227c : word) = Some W_be9c4.
Proof. vm_refl. Qed.
Lemma D_be9c4 : decode_any W_be9c4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9c8 : bv 32 := 0x0116a423.
Lemma F_be9c8 : fetch_word Asan.M.loaded_segments (0xc2280 : word) = Some W_be9c8.
Proof. vm_refl. Qed.
Lemma D_be9c8 : decode_any W_be9c8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9cc : bv 32 := 0x0056a623.
Lemma F_be9cc : fetch_word Asan.M.loaded_segments (0xc2284 : word) = Some W_be9cc.
Proof. vm_refl. Qed.
Lemma D_be9cc : decode_any W_be9cc = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9d0 : bv 32 := 0x01068693.
Lemma F_be9d0 : fetch_word Asan.M.loaded_segments (0xc2288 : word) = Some W_be9d0.
Proof. vm_refl. Qed.
Lemma D_be9d0 : decode_any W_be9d0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9d4 : bv 32 := 0xfcc76ae3.
Lemma F_be9d4 : fetch_word Asan.M.loaded_segments (0xc228c : word) = Some W_be9d4.
Proof. vm_refl. Qed.
Lemma D_be9d4 : decode_any W_be9d4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9d8 : bv 32 := 0x00800713.
Lemma F_be9d8 : fetch_word Asan.M.loaded_segments (0xc2290 : word) = Some W_be9d8.
Proof. vm_refl. Qed.
Lemma D_be9d8 : decode_any W_be9d8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9dc : bv 32 := 0x00e66e63.
Lemma F_be9dc : fetch_word Asan.M.loaded_segments (0xc2294 : word) = Some W_be9dc.
Proof. vm_refl. Qed.
Lemma D_be9dc : decode_any W_be9dc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9e0 : bv 32 := 0x0005a703.
Lemma F_be9e0 : fetch_word Asan.M.loaded_segments (0xc2298 : word) = Some W_be9e0.
Proof. vm_refl. Qed.
Lemma D_be9e0 : decode_any W_be9e0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9e4 : bv 32 := 0x0045a783.
Lemma F_be9e4 : fetch_word Asan.M.loaded_segments (0xc229c : word) = Some W_be9e4.
Proof. vm_refl. Qed.
Lemma D_be9e4 : decode_any W_be9e4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9e8 : bv 32 := 0x00e6a023.
Lemma F_be9e8 : fetch_word Asan.M.loaded_segments (0xc22a0 : word) = Some W_be9e8.
Proof. vm_refl. Qed.
Lemma D_be9e8 : decode_any W_be9e8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9ec : bv 32 := 0x00f6a223.
Lemma F_be9ec : fetch_word Asan.M.loaded_segments (0xc22a4 : word) = Some W_be9ec.
Proof. vm_refl. Qed.
Lemma D_be9ec : decode_any W_be9ec = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9f0 : bv 32 := 0x00868693.
Lemma F_be9f0 : fetch_word Asan.M.loaded_segments (0xc22a8 : word) = Some W_be9f0.
Proof. vm_refl. Qed.
Lemma D_be9f0 : decode_any W_be9f0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9f4 : bv 32 := 0x00858593.
Lemma F_be9f4 : fetch_word Asan.M.loaded_segments (0xc22ac : word) = Some W_be9f4.
Proof. vm_refl. Qed.
Lemma D_be9f4 : decode_any W_be9f4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9f8 : bv 32 := 0x00467713.
Lemma F_be9f8 : fetch_word Asan.M.loaded_segments (0xc22b0 : word) = Some W_be9f8.
Proof. vm_refl. Qed.
Lemma D_be9f8 : decode_any W_be9f8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_be9fc : bv 32 := 0x24070063.
Lemma F_be9fc : fetch_word Asan.M.loaded_segments (0xc22b4 : word) = Some W_be9fc.
Proof. vm_refl. Qed.
Lemma D_be9fc : decode_any W_be9fc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea00 : bv 32 := 0x0005a703.
Lemma F_bea00 : fetch_word Asan.M.loaded_segments (0xc22b8 : word) = Some W_bea00.
Proof. vm_refl. Qed.
Lemma D_bea00 : decode_any W_bea00 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea04 : bv 32 := 0x00458593.
Lemma F_bea04 : fetch_word Asan.M.loaded_segments (0xc22bc : word) = Some W_bea04.
Proof. vm_refl. Qed.
Lemma D_bea04 : decode_any W_bea04 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea08 : bv 32 := 0x00e6a023.
Lemma F_bea08 : fetch_word Asan.M.loaded_segments (0xc22c0 : word) = Some W_bea08.
Proof. vm_refl. Qed.
Lemma D_bea08 : decode_any W_bea08 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea0c : bv 32 := 0x00468693.
Lemma F_bea0c : fetch_word Asan.M.loaded_segments (0xc22c4 : word) = Some W_bea0c.
Proof. vm_refl. Qed.
Lemma D_bea0c : decode_any W_bea0c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea10 : bv 32 := 0x22c0006f.
Lemma F_bea10 : fetch_word Asan.M.loaded_segments (0xc22c8 : word) = Some W_bea10.
Proof. vm_refl. Qed.
Lemma D_bea10 : decode_any W_bea10 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea14 : bv 32 := 0x00e68023.
Lemma F_bea14 : fetch_word Asan.M.loaded_segments (0xc22cc : word) = Some W_bea14.
Proof. vm_refl. Qed.
Lemma D_bea14 : decode_any W_bea14 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea18 : bv 32 := 0x00168693.
Lemma F_bea18 : fetch_word Asan.M.loaded_segments (0xc22d0 : word) = Some W_bea18.
Proof. vm_refl. Qed.
Lemma D_bea18 : decode_any W_bea18 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea1c : bv 32 := 0xfff60613.
Lemma F_bea1c : fetch_word Asan.M.loaded_segments (0xc22d4 : word) = Some W_bea1c.
Proof. vm_refl. Qed.
Lemma D_bea1c : decode_any W_bea1c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea20 : bv 32 := 0x01058593.
Lemma F_bea20 : fetch_word Asan.M.loaded_segments (0xc22d8 : word) = Some W_bea20.
Proof. vm_refl. Qed.
Lemma D_bea20 : decode_any W_bea20 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea24 : bv 32 := 0x01200793.
Lemma F_bea24 : fetch_word Asan.M.loaded_segments (0xc22dc : word) = Some W_bea24.
Proof. vm_refl. Qed.
Lemma D_bea24 : decode_any W_bea24 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea28 : bv 32 := 0x0087581b.
Lemma F_bea28 : fetch_word Asan.M.loaded_segments (0xc22e0 : word) = Some W_bea28.
Proof. vm_refl. Qed.
Lemma D_bea28 : decode_any W_bea28 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea2c : bv 32 := 0xff45a883.
Lemma F_bea2c : fetch_word Asan.M.loaded_segments (0xc22e4 : word) = Some W_bea2c.
Proof. vm_refl. Qed.
Lemma D_bea2c : decode_any W_bea2c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea30 : bv 32 := 0xff85a283.
Lemma F_bea30 : fetch_word Asan.M.loaded_segments (0xc22e8 : word) = Some W_bea30.
Proof. vm_refl. Qed.
Lemma D_bea30 : decode_any W_bea30 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea34 : bv 32 := 0xffc5a303.
Lemma F_bea34 : fetch_word Asan.M.loaded_segments (0xc22ec : word) = Some W_bea34.
Proof. vm_refl. Qed.
Lemma D_bea34 : decode_any W_bea34 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea38 : bv 32 := 0x0005a703.
Lemma F_bea38 : fetch_word Asan.M.loaded_segments (0xc22f0 : word) = Some W_bea38.
Proof. vm_refl. Qed.
Lemma D_bea38 : decode_any W_bea38 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea3c : bv 32 := 0x01889393.
Lemma F_bea3c : fetch_word Asan.M.loaded_segments (0xc22f4 : word) = Some W_bea3c.
Proof. vm_refl. Qed.
Lemma D_bea3c : decode_any W_bea3c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea40 : bv 32 := 0x0088d89b.
Lemma F_bea40 : fetch_word Asan.M.loaded_segments (0xc22f8 : word) = Some W_bea40.
Proof. vm_refl. Qed.
Lemma D_bea40 : decode_any W_bea40 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea44 : bv 32 := 0x0103e833.
Lemma F_bea44 : fetch_word Asan.M.loaded_segments (0xc22fc : word) = Some W_bea44.
Proof. vm_refl. Qed.
Lemma D_bea44 : decode_any W_bea44 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea48 : bv 32 := 0x01829393.
Lemma F_bea48 : fetch_word Asan.M.loaded_segments (0xc2300 : word) = Some W_bea48.
Proof. vm_refl. Qed.
Lemma D_bea48 : decode_any W_bea48 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea4c : bv 32 := 0x0082d29b.
Lemma F_bea4c : fetch_word Asan.M.loaded_segments (0xc2304 : word) = Some W_bea4c.
Proof. vm_refl. Qed.
Lemma D_bea4c : decode_any W_bea4c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea50 : bv 32 := 0x0113e8b3.
Lemma F_bea50 : fetch_word Asan.M.loaded_segments (0xc2308 : word) = Some W_bea50.
Proof. vm_refl. Qed.
Lemma D_bea50 : decode_any W_bea50 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea54 : bv 32 := 0x01831393.
Lemma F_bea54 : fetch_word Asan.M.loaded_segments (0xc230c : word) = Some W_bea54.
Proof. vm_refl. Qed.
Lemma D_bea54 : decode_any W_bea54 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea58 : bv 32 := 0x0083531b.
Lemma F_bea58 : fetch_word Asan.M.loaded_segments (0xc2310 : word) = Some W_bea58.
Proof. vm_refl. Qed.
Lemma D_bea58 : decode_any W_bea58 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea5c : bv 32 := 0x0053e2b3.
Lemma F_bea5c : fetch_word Asan.M.loaded_segments (0xc2314 : word) = Some W_bea5c.
Proof. vm_refl. Qed.
Lemma D_bea5c : decode_any W_bea5c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea60 : bv 32 := 0x01871393.
Lemma F_bea60 : fetch_word Asan.M.loaded_segments (0xc2318 : word) = Some W_bea60.
Proof. vm_refl. Qed.
Lemma D_bea60 : decode_any W_bea60 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea64 : bv 32 := 0x0063e333.
Lemma F_bea64 : fetch_word Asan.M.loaded_segments (0xc231c : word) = Some W_bea64.
Proof. vm_refl. Qed.
Lemma D_bea64 : decode_any W_bea64 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea68 : bv 32 := 0xff060613.
Lemma F_bea68 : fetch_word Asan.M.loaded_segments (0xc2320 : word) = Some W_bea68.
Proof. vm_refl. Qed.
Lemma D_bea68 : decode_any W_bea68 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea6c : bv 32 := 0x0106a023.
Lemma F_bea6c : fetch_word Asan.M.loaded_segments (0xc2324 : word) = Some W_bea6c.
Proof. vm_refl. Qed.
Lemma D_bea6c : decode_any W_bea6c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea70 : bv 32 := 0x0116a223.
Lemma F_bea70 : fetch_word Asan.M.loaded_segments (0xc2328 : word) = Some W_bea70.
Proof. vm_refl. Qed.
Lemma D_bea70 : decode_any W_bea70 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea74 : bv 32 := 0x0056a423.
Lemma F_bea74 : fetch_word Asan.M.loaded_segments (0xc232c : word) = Some W_bea74.
Proof. vm_refl. Qed.
Lemma D_bea74 : decode_any W_bea74 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea78 : bv 32 := 0x0066a623.
Lemma F_bea78 : fetch_word Asan.M.loaded_segments (0xc2330 : word) = Some W_bea78.
Proof. vm_refl. Qed.
Lemma D_bea78 : decode_any W_bea78 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea7c : bv 32 := 0x01068693.
Lemma F_bea7c : fetch_word Asan.M.loaded_segments (0xc2334 : word) = Some W_bea7c.
Proof. vm_refl. Qed.
Lemma D_bea7c : decode_any W_bea7c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea80 : bv 32 := 0x01058593.
Lemma F_bea80 : fetch_word Asan.M.loaded_segments (0xc2338 : word) = Some W_bea80.
Proof. vm_refl. Qed.
Lemma D_bea80 : decode_any W_bea80 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea84 : bv 32 := 0xfac7e2e3.
Lemma F_bea84 : fetch_word Asan.M.loaded_segments (0xc233c : word) = Some W_bea84.
Proof. vm_refl. Qed.
Lemma D_bea84 : decode_any W_bea84 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea88 : bv 32 := 0xff158593.
Lemma F_bea88 : fetch_word Asan.M.loaded_segments (0xc2340 : word) = Some W_bea88.
Proof. vm_refl. Qed.
Lemma D_bea88 : decode_any W_bea88 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea8c : bv 32 := 0x01000713.
Lemma F_bea8c : fetch_word Asan.M.loaded_segments (0xc2344 : word) = Some W_bea8c.
Proof. vm_refl. Qed.
Lemma D_bea8c : decode_any W_bea8c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea90 : bv 32 := 0xe4e666e3.
Lemma F_bea90 : fetch_word Asan.M.loaded_segments (0xc2348 : word) = Some W_bea90.
Proof. vm_refl. Qed.
Lemma D_bea90 : decode_any W_bea90 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea94 : bv 32 := 0x0940006f.
Lemma F_bea94 : fetch_word Asan.M.loaded_segments (0xc234c : word) = Some W_bea94.
Proof. vm_refl. Qed.
Lemma D_bea94 : decode_any W_bea94 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea98 : bv 32 := 0x00875793.
Lemma F_bea98 : fetch_word Asan.M.loaded_segments (0xc2350 : word) = Some W_bea98.
Proof. vm_refl. Qed.
Lemma D_bea98 : decode_any W_bea98 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bea9c : bv 32 := 0x01075813.
Lemma F_bea9c : fetch_word Asan.M.loaded_segments (0xc2354 : word) = Some W_bea9c.
Proof. vm_refl. Qed.
Lemma D_bea9c : decode_any W_bea9c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaa0 : bv 32 := 0xffd60613.
Lemma F_beaa0 : fetch_word Asan.M.loaded_segments (0xc2358 : word) = Some W_beaa0.
Proof. vm_refl. Qed.
Lemma D_beaa0 : decode_any W_beaa0 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaa4 : bv 32 := 0x00e68023.
Lemma F_beaa4 : fetch_word Asan.M.loaded_segments (0xc235c : word) = Some W_beaa4.
Proof. vm_refl. Qed.
Lemma D_beaa4 : decode_any W_beaa4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaa8 : bv 32 := 0x00f680a3.
Lemma F_beaa8 : fetch_word Asan.M.loaded_segments (0xc2360 : word) = Some W_beaa8.
Proof. vm_refl. Qed.
Lemma D_beaa8 : decode_any W_beaa8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaac : bv 32 := 0x01068123.
Lemma F_beaac : fetch_word Asan.M.loaded_segments (0xc2364 : word) = Some W_beaac.
Proof. vm_refl. Qed.
Lemma D_beaac : decode_any W_beaac = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beab0 : bv 32 := 0x00368693.
Lemma F_beab0 : fetch_word Asan.M.loaded_segments (0xc2368 : word) = Some W_beab0.
Proof. vm_refl. Qed.
Lemma D_beab0 : decode_any W_beab0 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beab4 : bv 32 := 0x01058593.
Lemma F_beab4 : fetch_word Asan.M.loaded_segments (0xc236c : word) = Some W_beab4.
Proof. vm_refl. Qed.
Lemma D_beab4 : decode_any W_beab4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beab8 : bv 32 := 0x01000793.
Lemma F_beab8 : fetch_word Asan.M.loaded_segments (0xc2370 : word) = Some W_beab8.
Proof. vm_refl. Qed.
Lemma D_beab8 : decode_any W_beab8 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beabc : bv 32 := 0x0187581b.
Lemma F_beabc : fetch_word Asan.M.loaded_segments (0xc2374 : word) = Some W_beabc.
Proof. vm_refl. Qed.
Lemma D_beabc : decode_any W_beabc = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beac0 : bv 32 := 0xff45a883.
Lemma F_beac0 : fetch_word Asan.M.loaded_segments (0xc2378 : word) = Some W_beac0.
Proof. vm_refl. Qed.
Lemma D_beac0 : decode_any W_beac0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beac4 : bv 32 := 0xff85a283.
Lemma F_beac4 : fetch_word Asan.M.loaded_segments (0xc237c : word) = Some W_beac4.
Proof. vm_refl. Qed.
Lemma D_beac4 : decode_any W_beac4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beac8 : bv 32 := 0xffc5a303.
Lemma F_beac8 : fetch_word Asan.M.loaded_segments (0xc2380 : word) = Some W_beac8.
Proof. vm_refl. Qed.
Lemma D_beac8 : decode_any W_beac8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beacc : bv 32 := 0x0005a703.
Lemma F_beacc : fetch_word Asan.M.loaded_segments (0xc2384 : word) = Some W_beacc.
Proof. vm_refl. Qed.
Lemma D_beacc : decode_any W_beacc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bead0 : bv 32 := 0x00889393.
Lemma F_bead0 : fetch_word Asan.M.loaded_segments (0xc2388 : word) = Some W_bead0.
Proof. vm_refl. Qed.
Lemma D_bead0 : decode_any W_bead0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bead4 : bv 32 := 0x0188d89b.
Lemma F_bead4 : fetch_word Asan.M.loaded_segments (0xc238c : word) = Some W_bead4.
Proof. vm_refl. Qed.
Lemma D_bead4 : decode_any W_bead4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bead8 : bv 32 := 0x0103e833.
Lemma F_bead8 : fetch_word Asan.M.loaded_segments (0xc2390 : word) = Some W_bead8.
Proof. vm_refl. Qed.
Lemma D_bead8 : decode_any W_bead8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beadc : bv 32 := 0x00829393.
Lemma F_beadc : fetch_word Asan.M.loaded_segments (0xc2394 : word) = Some W_beadc.
Proof. vm_refl. Qed.
Lemma D_beadc : decode_any W_beadc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beae0 : bv 32 := 0x0182d29b.
Lemma F_beae0 : fetch_word Asan.M.loaded_segments (0xc2398 : word) = Some W_beae0.
Proof. vm_refl. Qed.
Lemma D_beae0 : decode_any W_beae0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beae4 : bv 32 := 0x0113e8b3.
Lemma F_beae4 : fetch_word Asan.M.loaded_segments (0xc239c : word) = Some W_beae4.
Proof. vm_refl. Qed.
Lemma D_beae4 : decode_any W_beae4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beae8 : bv 32 := 0x00831393.
Lemma F_beae8 : fetch_word Asan.M.loaded_segments (0xc23a0 : word) = Some W_beae8.
Proof. vm_refl. Qed.
Lemma D_beae8 : decode_any W_beae8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaec : bv 32 := 0x0183531b.
Lemma F_beaec : fetch_word Asan.M.loaded_segments (0xc23a4 : word) = Some W_beaec.
Proof. vm_refl. Qed.
Lemma D_beaec : decode_any W_beaec = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaf0 : bv 32 := 0x0053e2b3.
Lemma F_beaf0 : fetch_word Asan.M.loaded_segments (0xc23a8 : word) = Some W_beaf0.
Proof. vm_refl. Qed.
Lemma D_beaf0 : decode_any W_beaf0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaf4 : bv 32 := 0x00871393.
Lemma F_beaf4 : fetch_word Asan.M.loaded_segments (0xc23ac : word) = Some W_beaf4.
Proof. vm_refl. Qed.
Lemma D_beaf4 : decode_any W_beaf4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beaf8 : bv 32 := 0x0063e333.
Lemma F_beaf8 : fetch_word Asan.M.loaded_segments (0xc23b0 : word) = Some W_beaf8.
Proof. vm_refl. Qed.
Lemma D_beaf8 : decode_any W_beaf8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beafc : bv 32 := 0xff060613.
Lemma F_beafc : fetch_word Asan.M.loaded_segments (0xc23b4 : word) = Some W_beafc.
Proof. vm_refl. Qed.
Lemma D_beafc : decode_any W_beafc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb00 : bv 32 := 0x0106a023.
Lemma F_beb00 : fetch_word Asan.M.loaded_segments (0xc23b8 : word) = Some W_beb00.
Proof. vm_refl. Qed.
Lemma D_beb00 : decode_any W_beb00 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb04 : bv 32 := 0x0116a223.
Lemma F_beb04 : fetch_word Asan.M.loaded_segments (0xc23bc : word) = Some W_beb04.
Proof. vm_refl. Qed.
Lemma D_beb04 : decode_any W_beb04 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb08 : bv 32 := 0x0056a423.
Lemma F_beb08 : fetch_word Asan.M.loaded_segments (0xc23c0 : word) = Some W_beb08.
Proof. vm_refl. Qed.
Lemma D_beb08 : decode_any W_beb08 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb0c : bv 32 := 0x0066a623.
Lemma F_beb0c : fetch_word Asan.M.loaded_segments (0xc23c4 : word) = Some W_beb0c.
Proof. vm_refl. Qed.
Lemma D_beb0c : decode_any W_beb0c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb10 : bv 32 := 0x01068693.
Lemma F_beb10 : fetch_word Asan.M.loaded_segments (0xc23c8 : word) = Some W_beb10.
Proof. vm_refl. Qed.
Lemma D_beb10 : decode_any W_beb10 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb14 : bv 32 := 0x01058593.
Lemma F_beb14 : fetch_word Asan.M.loaded_segments (0xc23cc : word) = Some W_beb14.
Proof. vm_refl. Qed.
Lemma D_beb14 : decode_any W_beb14 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb18 : bv 32 := 0xfac7e2e3.
Lemma F_beb18 : fetch_word Asan.M.loaded_segments (0xc23d0 : word) = Some W_beb18.
Proof. vm_refl. Qed.
Lemma D_beb18 : decode_any W_beb18 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb1c : bv 32 := 0xff358593.
Lemma F_beb1c : fetch_word Asan.M.loaded_segments (0xc23d4 : word) = Some W_beb1c.
Proof. vm_refl. Qed.
Lemma D_beb1c : decode_any W_beb1c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb20 : bv 32 := 0x01000713.
Lemma F_beb20 : fetch_word Asan.M.loaded_segments (0xc23d8 : word) = Some W_beb20.
Proof. vm_refl. Qed.
Lemma D_beb20 : decode_any W_beb20 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb24 : bv 32 := 0xdae66ce3.
Lemma F_beb24 : fetch_word Asan.M.loaded_segments (0xc23dc : word) = Some W_beb24.
Proof. vm_refl. Qed.
Lemma D_beb24 : decode_any W_beb24 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb28 : bv 32 := 0x0005c703.
Lemma F_beb28 : fetch_word Asan.M.loaded_segments (0xc23e0 : word) = Some W_beb28.
Proof. vm_refl. Qed.
Lemma D_beb28 : decode_any W_beb28 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb2c : bv 32 := 0x0015c783.
Lemma F_beb2c : fetch_word Asan.M.loaded_segments (0xc23e4 : word) = Some W_beb2c.
Proof. vm_refl. Qed.
Lemma D_beb2c : decode_any W_beb2c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb30 : bv 32 := 0x0025c803.
Lemma F_beb30 : fetch_word Asan.M.loaded_segments (0xc23e8 : word) = Some W_beb30.
Proof. vm_refl. Qed.
Lemma D_beb30 : decode_any W_beb30 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb34 : bv 32 := 0x0035c883.
Lemma F_beb34 : fetch_word Asan.M.loaded_segments (0xc23ec : word) = Some W_beb34.
Proof. vm_refl. Qed.
Lemma D_beb34 : decode_any W_beb34 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb38 : bv 32 := 0x0045c283.
Lemma F_beb38 : fetch_word Asan.M.loaded_segments (0xc23f0 : word) = Some W_beb38.
Proof. vm_refl. Qed.
Lemma D_beb38 : decode_any W_beb38 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb3c : bv 32 := 0x0055c303.
Lemma F_beb3c : fetch_word Asan.M.loaded_segments (0xc23f4 : word) = Some W_beb3c.
Proof. vm_refl. Qed.
Lemma D_beb3c : decode_any W_beb3c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb40 : bv 32 := 0x0065c383.
Lemma F_beb40 : fetch_word Asan.M.loaded_segments (0xc23f8 : word) = Some W_beb40.
Proof. vm_refl. Qed.
Lemma D_beb40 : decode_any W_beb40 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb44 : bv 32 := 0x0075ce03.
Lemma F_beb44 : fetch_word Asan.M.loaded_segments (0xc23fc : word) = Some W_beb44.
Proof. vm_refl. Qed.
Lemma D_beb44 : decode_any W_beb44 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb48 : bv 32 := 0x00e68023.
Lemma F_beb48 : fetch_word Asan.M.loaded_segments (0xc2400 : word) = Some W_beb48.
Proof. vm_refl. Qed.
Lemma D_beb48 : decode_any W_beb48 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb4c : bv 32 := 0x00f680a3.
Lemma F_beb4c : fetch_word Asan.M.loaded_segments (0xc2404 : word) = Some W_beb4c.
Proof. vm_refl. Qed.
Lemma D_beb4c : decode_any W_beb4c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb50 : bv 32 := 0x01068123.
Lemma F_beb50 : fetch_word Asan.M.loaded_segments (0xc2408 : word) = Some W_beb50.
Proof. vm_refl. Qed.
Lemma D_beb50 : decode_any W_beb50 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb54 : bv 32 := 0x011681a3.
Lemma F_beb54 : fetch_word Asan.M.loaded_segments (0xc240c : word) = Some W_beb54.
Proof. vm_refl. Qed.
Lemma D_beb54 : decode_any W_beb54 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb58 : bv 32 := 0x0085c703.
Lemma F_beb58 : fetch_word Asan.M.loaded_segments (0xc2410 : word) = Some W_beb58.
Proof. vm_refl. Qed.
Lemma D_beb58 : decode_any W_beb58 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb5c : bv 32 := 0x0095c783.
Lemma F_beb5c : fetch_word Asan.M.loaded_segments (0xc2414 : word) = Some W_beb5c.
Proof. vm_refl. Qed.
Lemma D_beb5c : decode_any W_beb5c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb60 : bv 32 := 0x00a5c803.
Lemma F_beb60 : fetch_word Asan.M.loaded_segments (0xc2418 : word) = Some W_beb60.
Proof. vm_refl. Qed.
Lemma D_beb60 : decode_any W_beb60 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb64 : bv 32 := 0x00b5c883.
Lemma F_beb64 : fetch_word Asan.M.loaded_segments (0xc241c : word) = Some W_beb64.
Proof. vm_refl. Qed.
Lemma D_beb64 : decode_any W_beb64 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb68 : bv 32 := 0x00568223.
Lemma F_beb68 : fetch_word Asan.M.loaded_segments (0xc2420 : word) = Some W_beb68.
Proof. vm_refl. Qed.
Lemma D_beb68 : decode_any W_beb68 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb6c : bv 32 := 0x006682a3.
Lemma F_beb6c : fetch_word Asan.M.loaded_segments (0xc2424 : word) = Some W_beb6c.
Proof. vm_refl. Qed.
Lemma D_beb6c : decode_any W_beb6c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb70 : bv 32 := 0x00768323.
Lemma F_beb70 : fetch_word Asan.M.loaded_segments (0xc2428 : word) = Some W_beb70.
Proof. vm_refl. Qed.
Lemma D_beb70 : decode_any W_beb70 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb74 : bv 32 := 0x01c683a3.
Lemma F_beb74 : fetch_word Asan.M.loaded_segments (0xc242c : word) = Some W_beb74.
Proof. vm_refl. Qed.
Lemma D_beb74 : decode_any W_beb74 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb78 : bv 32 := 0x00c5c283.
Lemma F_beb78 : fetch_word Asan.M.loaded_segments (0xc2430 : word) = Some W_beb78.
Proof. vm_refl. Qed.
Lemma D_beb78 : decode_any W_beb78 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb7c : bv 32 := 0x00d5c303.
Lemma F_beb7c : fetch_word Asan.M.loaded_segments (0xc2434 : word) = Some W_beb7c.
Proof. vm_refl. Qed.
Lemma D_beb7c : decode_any W_beb7c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb80 : bv 32 := 0x00e5c383.
Lemma F_beb80 : fetch_word Asan.M.loaded_segments (0xc2438 : word) = Some W_beb80.
Proof. vm_refl. Qed.
Lemma D_beb80 : decode_any W_beb80 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb84 : bv 32 := 0x00f5ce03.
Lemma F_beb84 : fetch_word Asan.M.loaded_segments (0xc243c : word) = Some W_beb84.
Proof. vm_refl. Qed.
Lemma D_beb84 : decode_any W_beb84 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb88 : bv 32 := 0x01058593.
Lemma F_beb88 : fetch_word Asan.M.loaded_segments (0xc2440 : word) = Some W_beb88.
Proof. vm_refl. Qed.
Lemma D_beb88 : decode_any W_beb88 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb8c : bv 32 := 0x00e68423.
Lemma F_beb8c : fetch_word Asan.M.loaded_segments (0xc2444 : word) = Some W_beb8c.
Proof. vm_refl. Qed.
Lemma D_beb8c : decode_any W_beb8c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb90 : bv 32 := 0x00f684a3.
Lemma F_beb90 : fetch_word Asan.M.loaded_segments (0xc2448 : word) = Some W_beb90.
Proof. vm_refl. Qed.
Lemma D_beb90 : decode_any W_beb90 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb94 : bv 32 := 0x01068523.
Lemma F_beb94 : fetch_word Asan.M.loaded_segments (0xc244c : word) = Some W_beb94.
Proof. vm_refl. Qed.
Lemma D_beb94 : decode_any W_beb94 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb98 : bv 32 := 0x011685a3.
Lemma F_beb98 : fetch_word Asan.M.loaded_segments (0xc2450 : word) = Some W_beb98.
Proof. vm_refl. Qed.
Lemma D_beb98 : decode_any W_beb98 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beb9c : bv 32 := 0x01068713.
Lemma F_beb9c : fetch_word Asan.M.loaded_segments (0xc2454 : word) = Some W_beb9c.
Proof. vm_refl. Qed.
Lemma D_beb9c : decode_any W_beb9c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beba0 : bv 32 := 0x00568623.
Lemma F_beba0 : fetch_word Asan.M.loaded_segments (0xc2458 : word) = Some W_beba0.
Proof. vm_refl. Qed.
Lemma D_beba0 : decode_any W_beba0 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beba4 : bv 32 := 0x006686a3.
Lemma F_beba4 : fetch_word Asan.M.loaded_segments (0xc245c : word) = Some W_beba4.
Proof. vm_refl. Qed.
Lemma D_beba4 : decode_any W_beba4 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beba8 : bv 32 := 0x00768723.
Lemma F_beba8 : fetch_word Asan.M.loaded_segments (0xc2460 : word) = Some W_beba8.
Proof. vm_refl. Qed.
Lemma D_beba8 : decode_any W_beba8 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebac : bv 32 := 0x01c687a3.
Lemma F_bebac : fetch_word Asan.M.loaded_segments (0xc2464 : word) = Some W_bebac.
Proof. vm_refl. Qed.
Lemma D_bebac : decode_any W_bebac = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebb0 : bv 32 := 0x00070693.
Lemma F_bebb0 : fetch_word Asan.M.loaded_segments (0xc2468 : word) = Some W_bebb0.
Proof. vm_refl. Qed.
Lemma D_bebb0 : decode_any W_bebb0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebb4 : bv 32 := 0x00867713.
Lemma F_bebb4 : fetch_word Asan.M.loaded_segments (0xc246c : word) = Some W_bebb4.
Proof. vm_refl. Qed.
Lemma D_bebb4 : decode_any W_bebb4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebb8 : bv 32 := 0xd20706e3.
Lemma F_bebb8 : fetch_word Asan.M.loaded_segments (0xc2470 : word) = Some W_bebb8.
Proof. vm_refl. Qed.
Lemma D_bebb8 : decode_any W_bebb8 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebbc : bv 32 := 0x0005c703.
Lemma F_bebbc : fetch_word Asan.M.loaded_segments (0xc2474 : word) = Some W_bebbc.
Proof. vm_refl. Qed.
Lemma D_bebbc : decode_any W_bebbc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebc0 : bv 32 := 0x0015c783.
Lemma F_bebc0 : fetch_word Asan.M.loaded_segments (0xc2478 : word) = Some W_bebc0.
Proof. vm_refl. Qed.
Lemma D_bebc0 : decode_any W_bebc0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebc4 : bv 32 := 0x0025c803.
Lemma F_bebc4 : fetch_word Asan.M.loaded_segments (0xc247c : word) = Some W_bebc4.
Proof. vm_refl. Qed.
Lemma D_bebc4 : decode_any W_bebc4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebc8 : bv 32 := 0x0035c883.
Lemma F_bebc8 : fetch_word Asan.M.loaded_segments (0xc2480 : word) = Some W_bebc8.
Proof. vm_refl. Qed.
Lemma D_bebc8 : decode_any W_bebc8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebcc : bv 32 := 0x0045c283.
Lemma F_bebcc : fetch_word Asan.M.loaded_segments (0xc2484 : word) = Some W_bebcc.
Proof. vm_refl. Qed.
Lemma D_bebcc : decode_any W_bebcc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebd0 : bv 32 := 0x0055c303.
Lemma F_bebd0 : fetch_word Asan.M.loaded_segments (0xc2488 : word) = Some W_bebd0.
Proof. vm_refl. Qed.
Lemma D_bebd0 : decode_any W_bebd0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebd4 : bv 32 := 0x0065c383.
Lemma F_bebd4 : fetch_word Asan.M.loaded_segments (0xc248c : word) = Some W_bebd4.
Proof. vm_refl. Qed.
Lemma D_bebd4 : decode_any W_bebd4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebd8 : bv 32 := 0x0075ce03.
Lemma F_bebd8 : fetch_word Asan.M.loaded_segments (0xc2490 : word) = Some W_bebd8.
Proof. vm_refl. Qed.
Lemma D_bebd8 : decode_any W_bebd8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebdc : bv 32 := 0x00858593.
Lemma F_bebdc : fetch_word Asan.M.loaded_segments (0xc2494 : word) = Some W_bebdc.
Proof. vm_refl. Qed.
Lemma D_bebdc : decode_any W_bebdc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebe0 : bv 32 := 0x00e68023.
Lemma F_bebe0 : fetch_word Asan.M.loaded_segments (0xc2498 : word) = Some W_bebe0.
Proof. vm_refl. Qed.
Lemma D_bebe0 : decode_any W_bebe0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebe4 : bv 32 := 0x00f680a3.
Lemma F_bebe4 : fetch_word Asan.M.loaded_segments (0xc249c : word) = Some W_bebe4.
Proof. vm_refl. Qed.
Lemma D_bebe4 : decode_any W_bebe4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebe8 : bv 32 := 0x01068123.
Lemma F_bebe8 : fetch_word Asan.M.loaded_segments (0xc24a0 : word) = Some W_bebe8.
Proof. vm_refl. Qed.
Lemma D_bebe8 : decode_any W_bebe8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebec : bv 32 := 0x011681a3.
Lemma F_bebec : fetch_word Asan.M.loaded_segments (0xc24a4 : word) = Some W_bebec.
Proof. vm_refl. Qed.
Lemma D_bebec : decode_any W_bebec = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebf0 : bv 32 := 0x00868713.
Lemma F_bebf0 : fetch_word Asan.M.loaded_segments (0xc24a8 : word) = Some W_bebf0.
Proof. vm_refl. Qed.
Lemma D_bebf0 : decode_any W_bebf0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebf4 : bv 32 := 0x00568223.
Lemma F_bebf4 : fetch_word Asan.M.loaded_segments (0xc24ac : word) = Some W_bebf4.
Proof. vm_refl. Qed.
Lemma D_bebf4 : decode_any W_bebf4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebf8 : bv 32 := 0x006682a3.
Lemma F_bebf8 : fetch_word Asan.M.loaded_segments (0xc24b0 : word) = Some W_bebf8.
Proof. vm_refl. Qed.
Lemma D_bebf8 : decode_any W_bebf8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bebfc : bv 32 := 0x00768323.
Lemma F_bebfc : fetch_word Asan.M.loaded_segments (0xc24b4 : word) = Some W_bebfc.
Proof. vm_refl. Qed.
Lemma D_bebfc : decode_any W_bebfc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec00 : bv 32 := 0x01c683a3.
Lemma F_bec00 : fetch_word Asan.M.loaded_segments (0xc24b8 : word) = Some W_bec00.
Proof. vm_refl. Qed.
Lemma D_bec00 : decode_any W_bec00 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec04 : bv 32 := 0x00070693.
Lemma F_bec04 : fetch_word Asan.M.loaded_segments (0xc24bc : word) = Some W_bec04.
Proof. vm_refl. Qed.
Lemma D_bec04 : decode_any W_bec04 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec08 : bv 32 := 0x00467713.
Lemma F_bec08 : fetch_word Asan.M.loaded_segments (0xc24c0 : word) = Some W_bec08.
Proof. vm_refl. Qed.
Lemma D_bec08 : decode_any W_bec08 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec0c : bv 32 := 0x02070863.
Lemma F_bec0c : fetch_word Asan.M.loaded_segments (0xc24c4 : word) = Some W_bec0c.
Proof. vm_refl. Qed.
Lemma D_bec0c : decode_any W_bec0c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec10 : bv 32 := 0x0005c703.
Lemma F_bec10 : fetch_word Asan.M.loaded_segments (0xc24c8 : word) = Some W_bec10.
Proof. vm_refl. Qed.
Lemma D_bec10 : decode_any W_bec10 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec14 : bv 32 := 0x0015c783.
Lemma F_bec14 : fetch_word Asan.M.loaded_segments (0xc24cc : word) = Some W_bec14.
Proof. vm_refl. Qed.
Lemma D_bec14 : decode_any W_bec14 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec18 : bv 32 := 0x0025c803.
Lemma F_bec18 : fetch_word Asan.M.loaded_segments (0xc24d0 : word) = Some W_bec18.
Proof. vm_refl. Qed.
Lemma D_bec18 : decode_any W_bec18 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec1c : bv 32 := 0x0035c883.
Lemma F_bec1c : fetch_word Asan.M.loaded_segments (0xc24d4 : word) = Some W_bec1c.
Proof. vm_refl. Qed.
Lemma D_bec1c : decode_any W_bec1c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec20 : bv 32 := 0x00458593.
Lemma F_bec20 : fetch_word Asan.M.loaded_segments (0xc24d8 : word) = Some W_bec20.
Proof. vm_refl. Qed.
Lemma D_bec20 : decode_any W_bec20 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec24 : bv 32 := 0x00468293.
Lemma F_bec24 : fetch_word Asan.M.loaded_segments (0xc24dc : word) = Some W_bec24.
Proof. vm_refl. Qed.
Lemma D_bec24 : decode_any W_bec24 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec28 : bv 32 := 0x00e68023.
Lemma F_bec28 : fetch_word Asan.M.loaded_segments (0xc24e0 : word) = Some W_bec28.
Proof. vm_refl. Qed.
Lemma D_bec28 : decode_any W_bec28 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec2c : bv 32 := 0x00f680a3.
Lemma F_bec2c : fetch_word Asan.M.loaded_segments (0xc24e4 : word) = Some W_bec2c.
Proof. vm_refl. Qed.
Lemma D_bec2c : decode_any W_bec2c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec30 : bv 32 := 0x01068123.
Lemma F_bec30 : fetch_word Asan.M.loaded_segments (0xc24e8 : word) = Some W_bec30.
Proof. vm_refl. Qed.
Lemma D_bec30 : decode_any W_bec30 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec34 : bv 32 := 0x011681a3.
Lemma F_bec34 : fetch_word Asan.M.loaded_segments (0xc24ec : word) = Some W_bec34.
Proof. vm_refl. Qed.
Lemma D_bec34 : decode_any W_bec34 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec38 : bv 32 := 0x00028693.
Lemma F_bec38 : fetch_word Asan.M.loaded_segments (0xc24f0 : word) = Some W_bec38.
Proof. vm_refl. Qed.
Lemma D_bec38 : decode_any W_bec38 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec3c : bv 32 := 0x00267713.
Lemma F_bec3c : fetch_word Asan.M.loaded_segments (0xc24f4 : word) = Some W_bec3c.
Proof. vm_refl. Qed.
Lemma D_bec3c : decode_any W_bec3c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec40 : bv 32 := 0x00071863.
Lemma F_bec40 : fetch_word Asan.M.loaded_segments (0xc24f8 : word) = Some W_bec40.
Proof. vm_refl. Qed.
Lemma D_bec40 : decode_any W_bec40 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec44 : bv 32 := 0x00167613.
Lemma F_bec44 : fetch_word Asan.M.loaded_segments (0xc24fc : word) = Some W_bec44.
Proof. vm_refl. Qed.
Lemma D_bec44 : decode_any W_bec44 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec48 : bv 32 := 0x02061663.
Lemma F_bec48 : fetch_word Asan.M.loaded_segments (0xc2500 : word) = Some W_bec48.
Proof. vm_refl. Qed.
Lemma D_bec48 : decode_any W_bec48 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec4c : bv 32 := 0x00008067.
Lemma F_bec4c : fetch_word Asan.M.loaded_segments (0xc2504 : word) = Some W_bec4c.
Proof. vm_refl. Qed.
Lemma D_bec4c : decode_any W_bec4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec50 : bv 32 := 0x0005c703.
Lemma F_bec50 : fetch_word Asan.M.loaded_segments (0xc2508 : word) = Some W_bec50.
Proof. vm_refl. Qed.
Lemma D_bec50 : decode_any W_bec50 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec54 : bv 32 := 0x0015c783.
Lemma F_bec54 : fetch_word Asan.M.loaded_segments (0xc250c : word) = Some W_bec54.
Proof. vm_refl. Qed.
Lemma D_bec54 : decode_any W_bec54 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec58 : bv 32 := 0x00258593.
Lemma F_bec58 : fetch_word Asan.M.loaded_segments (0xc2510 : word) = Some W_bec58.
Proof. vm_refl. Qed.
Lemma D_bec58 : decode_any W_bec58 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec5c : bv 32 := 0x00268813.
Lemma F_bec5c : fetch_word Asan.M.loaded_segments (0xc2514 : word) = Some W_bec5c.
Proof. vm_refl. Qed.
Lemma D_bec5c : decode_any W_bec5c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec60 : bv 32 := 0x00e68023.
Lemma F_bec60 : fetch_word Asan.M.loaded_segments (0xc2518 : word) = Some W_bec60.
Proof. vm_refl. Qed.
Lemma D_bec60 : decode_any W_bec60 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec64 : bv 32 := 0x00f680a3.
Lemma F_bec64 : fetch_word Asan.M.loaded_segments (0xc251c : word) = Some W_bec64.
Proof. vm_refl. Qed.
Lemma D_bec64 : decode_any W_bec64 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec68 : bv 32 := 0x00080693.
Lemma F_bec68 : fetch_word Asan.M.loaded_segments (0xc2520 : word) = Some W_bec68.
Proof. vm_refl. Qed.
Lemma D_bec68 : decode_any W_bec68 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec6c : bv 32 := 0x00167613.
Lemma F_bec6c : fetch_word Asan.M.loaded_segments (0xc2524 : word) = Some W_bec6c.
Proof. vm_refl. Qed.
Lemma D_bec6c : decode_any W_bec6c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec70 : bv 32 := 0xfc060ee3.
Lemma F_bec70 : fetch_word Asan.M.loaded_segments (0xc2528 : word) = Some W_bec70.
Proof. vm_refl. Qed.
Lemma D_bec70 : decode_any W_bec70 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec74 : bv 32 := 0x0005c583.
Lemma F_bec74 : fetch_word Asan.M.loaded_segments (0xc252c : word) = Some W_bec74.
Proof. vm_refl. Qed.
Lemma D_bec74 : decode_any W_bec74 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec78 : bv 32 := 0x00b68023.
Lemma F_bec78 : fetch_word Asan.M.loaded_segments (0xc2530 : word) = Some W_bec78.
Proof. vm_refl. Qed.
Lemma D_bec78 : decode_any W_bec78 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bec7c : bv 32 := 0x00008067.
Lemma F_bec7c : fetch_word Asan.M.loaded_segments (0xc2534 : word) = Some W_bec7c.
Proof. vm_refl. Qed.
Lemma D_bec7c : decode_any W_bec7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
