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
Definition W_e00c8 : bv 32 := 0x0035f693.
Lemma F_e00c8 : fetch_word AsanUbsan.M.loaded_segments (0xe0c10 : word) = Some W_e00c8.
Proof. vm_refl. Qed.
Lemma D_e00c8 : decode_any W_e00c8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00cc : bv 32 := 0x10068863.
Lemma F_e00cc : fetch_word AsanUbsan.M.loaded_segments (0xe0c14 : word) = Some W_e00cc.
Proof. vm_refl. Qed.
Lemma D_e00cc : decode_any W_e00cc = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00d0 : bv 32 := 0x02060e63.
Lemma F_e00d0 : fetch_word AsanUbsan.M.loaded_segments (0xe0c18 : word) = Some W_e00d0.
Proof. vm_refl. Qed.
Lemma D_e00d0 : decode_any W_e00d0 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00d4 : bv 32 := 0x00158713.
Lemma F_e00d4 : fetch_word AsanUbsan.M.loaded_segments (0xe0c1c : word) = Some W_e00d4.
Proof. vm_refl. Qed.
Lemma D_e00d4 : decode_any W_e00d4 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00d8 : bv 32 := 0x00100793.
Lemma F_e00d8 : fetch_word AsanUbsan.M.loaded_segments (0xe0c20 : word) = Some W_e00d8.
Proof. vm_refl. Qed.
Lemma D_e00d8 : decode_any W_e00d8 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00dc : bv 32 := 0x00050693.
Lemma F_e00dc : fetch_word AsanUbsan.M.loaded_segments (0xe0c24 : word) = Some W_e00dc.
Proof. vm_refl. Qed.
Lemma D_e00dc : decode_any W_e00dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00e0 : bv 32 := 0x0005c883.
Lemma F_e00e0 : fetch_word AsanUbsan.M.loaded_segments (0xe0c28 : word) = Some W_e00e0.
Proof. vm_refl. Qed.
Lemma D_e00e0 : decode_any W_e00e0 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00e4 : bv 32 := 0x00060813.
Lemma F_e00e4 : fetch_word AsanUbsan.M.loaded_segments (0xe0c2c : word) = Some W_e00e4.
Proof. vm_refl. Qed.
Lemma D_e00e4 : decode_any W_e00e4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00e8 : bv 32 := 0x00158593.
Lemma F_e00e8 : fetch_word AsanUbsan.M.loaded_segments (0xe0c30 : word) = Some W_e00e8.
Proof. vm_refl. Qed.
Lemma D_e00e8 : decode_any W_e00e8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00ec : bv 32 := 0x00377293.
Lemma F_e00ec : fetch_word AsanUbsan.M.loaded_segments (0xe0c34 : word) = Some W_e00ec.
Proof. vm_refl. Qed.
Lemma D_e00ec : decode_any W_e00ec = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00f0 : bv 32 := 0x01168023.
Lemma F_e00f0 : fetch_word AsanUbsan.M.loaded_segments (0xe0c38 : word) = Some W_e00f0.
Proof. vm_refl. Qed.
Lemma D_e00f0 : decode_any W_e00f0 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00f4 : bv 32 := 0x00168693.
Lemma F_e00f4 : fetch_word AsanUbsan.M.loaded_segments (0xe0c3c : word) = Some W_e00f4.
Proof. vm_refl. Qed.
Lemma D_e00f4 : decode_any W_e00f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00f8 : bv 32 := 0xfff60613.
Lemma F_e00f8 : fetch_word AsanUbsan.M.loaded_segments (0xe0c40 : word) = Some W_e00f8.
Proof. vm_refl. Qed.
Lemma D_e00f8 : decode_any W_e00f8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e00fc : bv 32 := 0x00028a63.
Lemma F_e00fc : fetch_word AsanUbsan.M.loaded_segments (0xe0c44 : word) = Some W_e00fc.
Proof. vm_refl. Qed.
Lemma D_e00fc : decode_any W_e00fc = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0100 : bv 32 := 0x00170713.
Lemma F_e0100 : fetch_word AsanUbsan.M.loaded_segments (0xe0c48 : word) = Some W_e0100.
Proof. vm_refl. Qed.
Lemma D_e0100 : decode_any W_e0100 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0104 : bv 32 := 0xfcf81ee3.
Lemma F_e0104 : fetch_word AsanUbsan.M.loaded_segments (0xe0c4c : word) = Some W_e0104.
Proof. vm_refl. Qed.
Lemma D_e0104 : decode_any W_e0104 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0108 : bv 32 := 0x0080006f.
Lemma F_e0108 : fetch_word AsanUbsan.M.loaded_segments (0xe0c50 : word) = Some W_e0108.
Proof. vm_refl. Qed.
Lemma D_e0108 : decode_any W_e0108 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e010c : bv 32 := 0x00050693.
Lemma F_e010c : fetch_word AsanUbsan.M.loaded_segments (0xe0c54 : word) = Some W_e010c.
Proof. vm_refl. Qed.
Lemma D_e010c : decode_any W_e010c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0110 : bv 32 := 0x0036f793.
Lemma F_e0110 : fetch_word AsanUbsan.M.loaded_segments (0xe0c58 : word) = Some W_e0110.
Proof. vm_refl. Qed.
Lemma D_e0110 : decode_any W_e0110 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0114 : bv 32 := 0x0c078a63.
Lemma F_e0114 : fetch_word AsanUbsan.M.loaded_segments (0xe0c5c : word) = Some W_e0114.
Proof. vm_refl. Qed.
Lemma D_e0114 : decode_any W_e0114 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0118 : bv 32 := 0x02000713.
Lemma F_e0118 : fetch_word AsanUbsan.M.loaded_segments (0xe0c60 : word) = Some W_e0118.
Proof. vm_refl. Qed.
Lemma D_e0118 : decode_any W_e0118 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e011c : bv 32 := 0x02e67063.
Lemma F_e011c : fetch_word AsanUbsan.M.loaded_segments (0xe0c64 : word) = Some W_e011c.
Proof. vm_refl. Qed.
Lemma D_e011c : decode_any W_e011c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0120 : bv 32 := 0x01000713.
Lemma F_e0120 : fetch_word AsanUbsan.M.loaded_segments (0xe0c68 : word) = Some W_e0120.
Proof. vm_refl. Qed.
Lemma D_e0120 : decode_any W_e0120 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0124 : bv 32 := 0x24e67863.
Lemma F_e0124 : fetch_word AsanUbsan.M.loaded_segments (0xe0c6c : word) = Some W_e0124.
Proof. vm_refl. Qed.
Lemma D_e0124 : decode_any W_e0124 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0128 : bv 32 := 0x00867713.
Lemma F_e0128 : fetch_word AsanUbsan.M.loaded_segments (0xe0c70 : word) = Some W_e0128.
Proof. vm_refl. Qed.
Lemma D_e0128 : decode_any W_e0128 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e012c : bv 32 := 0x2c071e63.
Lemma F_e012c : fetch_word AsanUbsan.M.loaded_segments (0xe0c74 : word) = Some W_e012c.
Proof. vm_refl. Qed.
Lemma D_e012c : decode_any W_e012c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0130 : bv 32 := 0x00467713.
Lemma F_e0130 : fetch_word AsanUbsan.M.loaded_segments (0xe0c78 : word) = Some W_e0130.
Proof. vm_refl. Qed.
Lemma D_e0130 : decode_any W_e0130 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0134 : bv 32 := 0x32071463.
Lemma F_e0134 : fetch_word AsanUbsan.M.loaded_segments (0xe0c7c : word) = Some W_e0134.
Proof. vm_refl. Qed.
Lemma D_e0134 : decode_any W_e0134 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0138 : bv 32 := 0x3500006f.
Lemma F_e0138 : fetch_word AsanUbsan.M.loaded_segments (0xe0c80 : word) = Some W_e0138.
Proof. vm_refl. Qed.
Lemma D_e0138 : decode_any W_e0138 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e013c : bv 32 := 0x0005a703.
Lemma F_e013c : fetch_word AsanUbsan.M.loaded_segments (0xe0c84 : word) = Some W_e013c.
Proof. vm_refl. Qed.
Lemma D_e013c : decode_any W_e013c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0140 : bv 32 := 0x00300813.
Lemma F_e0140 : fetch_word AsanUbsan.M.loaded_segments (0xe0c88 : word) = Some W_e0140.
Proof. vm_refl. Qed.
Lemma D_e0140 : decode_any W_e0140 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0144 : bv 32 := 0x11078e63.
Lemma F_e0144 : fetch_word AsanUbsan.M.loaded_segments (0xe0c8c : word) = Some W_e0144.
Proof. vm_refl. Qed.
Lemma D_e0144 : decode_any W_e0144 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0148 : bv 32 := 0x00200813.
Lemma F_e0148 : fetch_word AsanUbsan.M.loaded_segments (0xe0c90 : word) = Some W_e0148.
Proof. vm_refl. Qed.
Lemma D_e0148 : decode_any W_e0148 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e014c : bv 32 := 0x19079c63.
Lemma F_e014c : fetch_word AsanUbsan.M.loaded_segments (0xe0c94 : word) = Some W_e014c.
Proof. vm_refl. Qed.
Lemma D_e014c : decode_any W_e014c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0150 : bv 32 := 0x00875793.
Lemma F_e0150 : fetch_word AsanUbsan.M.loaded_segments (0xe0c98 : word) = Some W_e0150.
Proof. vm_refl. Qed.
Lemma D_e0150 : decode_any W_e0150 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0154 : bv 32 := 0xffe60613.
Lemma F_e0154 : fetch_word AsanUbsan.M.loaded_segments (0xe0c9c : word) = Some W_e0154.
Proof. vm_refl. Qed.
Lemma D_e0154 : decode_any W_e0154 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0158 : bv 32 := 0x00e68023.
Lemma F_e0158 : fetch_word AsanUbsan.M.loaded_segments (0xe0ca0 : word) = Some W_e0158.
Proof. vm_refl. Qed.
Lemma D_e0158 : decode_any W_e0158 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e015c : bv 32 := 0x00f680a3.
Lemma F_e015c : fetch_word AsanUbsan.M.loaded_segments (0xe0ca4 : word) = Some W_e015c.
Proof. vm_refl. Qed.
Lemma D_e015c : decode_any W_e015c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0160 : bv 32 := 0x00268693.
Lemma F_e0160 : fetch_word AsanUbsan.M.loaded_segments (0xe0ca8 : word) = Some W_e0160.
Proof. vm_refl. Qed.
Lemma D_e0160 : decode_any W_e0160 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0164 : bv 32 := 0x01058593.
Lemma F_e0164 : fetch_word AsanUbsan.M.loaded_segments (0xe0cac : word) = Some W_e0164.
Proof. vm_refl. Qed.
Lemma D_e0164 : decode_any W_e0164 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0168 : bv 32 := 0x01100793.
Lemma F_e0168 : fetch_word AsanUbsan.M.loaded_segments (0xe0cb0 : word) = Some W_e0168.
Proof. vm_refl. Qed.
Lemma D_e0168 : decode_any W_e0168 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e016c : bv 32 := 0x0107581b.
Lemma F_e016c : fetch_word AsanUbsan.M.loaded_segments (0xe0cb4 : word) = Some W_e016c.
Proof. vm_refl. Qed.
Lemma D_e016c : decode_any W_e016c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0170 : bv 32 := 0xff45a883.
Lemma F_e0170 : fetch_word AsanUbsan.M.loaded_segments (0xe0cb8 : word) = Some W_e0170.
Proof. vm_refl. Qed.
Lemma D_e0170 : decode_any W_e0170 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0174 : bv 32 := 0xff85a283.
Lemma F_e0174 : fetch_word AsanUbsan.M.loaded_segments (0xe0cbc : word) = Some W_e0174.
Proof. vm_refl. Qed.
Lemma D_e0174 : decode_any W_e0174 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0178 : bv 32 := 0xffc5a303.
Lemma F_e0178 : fetch_word AsanUbsan.M.loaded_segments (0xe0cc0 : word) = Some W_e0178.
Proof. vm_refl. Qed.
Lemma D_e0178 : decode_any W_e0178 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e017c : bv 32 := 0x0005a703.
Lemma F_e017c : fetch_word AsanUbsan.M.loaded_segments (0xe0cc4 : word) = Some W_e017c.
Proof. vm_refl. Qed.
Lemma D_e017c : decode_any W_e017c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0180 : bv 32 := 0x01089393.
Lemma F_e0180 : fetch_word AsanUbsan.M.loaded_segments (0xe0cc8 : word) = Some W_e0180.
Proof. vm_refl. Qed.
Lemma D_e0180 : decode_any W_e0180 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0184 : bv 32 := 0x0108d89b.
Lemma F_e0184 : fetch_word AsanUbsan.M.loaded_segments (0xe0ccc : word) = Some W_e0184.
Proof. vm_refl. Qed.
Lemma D_e0184 : decode_any W_e0184 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0188 : bv 32 := 0x0103e833.
Lemma F_e0188 : fetch_word AsanUbsan.M.loaded_segments (0xe0cd0 : word) = Some W_e0188.
Proof. vm_refl. Qed.
Lemma D_e0188 : decode_any W_e0188 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e018c : bv 32 := 0x01029393.
Lemma F_e018c : fetch_word AsanUbsan.M.loaded_segments (0xe0cd4 : word) = Some W_e018c.
Proof. vm_refl. Qed.
Lemma D_e018c : decode_any W_e018c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0190 : bv 32 := 0x0102d29b.
Lemma F_e0190 : fetch_word AsanUbsan.M.loaded_segments (0xe0cd8 : word) = Some W_e0190.
Proof. vm_refl. Qed.
Lemma D_e0190 : decode_any W_e0190 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0194 : bv 32 := 0x0113e8b3.
Lemma F_e0194 : fetch_word AsanUbsan.M.loaded_segments (0xe0cdc : word) = Some W_e0194.
Proof. vm_refl. Qed.
Lemma D_e0194 : decode_any W_e0194 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0198 : bv 32 := 0x01031393.
Lemma F_e0198 : fetch_word AsanUbsan.M.loaded_segments (0xe0ce0 : word) = Some W_e0198.
Proof. vm_refl. Qed.
Lemma D_e0198 : decode_any W_e0198 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e019c : bv 32 := 0x0103531b.
Lemma F_e019c : fetch_word AsanUbsan.M.loaded_segments (0xe0ce4 : word) = Some W_e019c.
Proof. vm_refl. Qed.
Lemma D_e019c : decode_any W_e019c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01a0 : bv 32 := 0x0053e2b3.
Lemma F_e01a0 : fetch_word AsanUbsan.M.loaded_segments (0xe0ce8 : word) = Some W_e01a0.
Proof. vm_refl. Qed.
Lemma D_e01a0 : decode_any W_e01a0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01a4 : bv 32 := 0x01071393.
Lemma F_e01a4 : fetch_word AsanUbsan.M.loaded_segments (0xe0cec : word) = Some W_e01a4.
Proof. vm_refl. Qed.
Lemma D_e01a4 : decode_any W_e01a4 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01a8 : bv 32 := 0x0063e333.
Lemma F_e01a8 : fetch_word AsanUbsan.M.loaded_segments (0xe0cf0 : word) = Some W_e01a8.
Proof. vm_refl. Qed.
Lemma D_e01a8 : decode_any W_e01a8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01ac : bv 32 := 0xff060613.
Lemma F_e01ac : fetch_word AsanUbsan.M.loaded_segments (0xe0cf4 : word) = Some W_e01ac.
Proof. vm_refl. Qed.
Lemma D_e01ac : decode_any W_e01ac = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01b0 : bv 32 := 0x0106a023.
Lemma F_e01b0 : fetch_word AsanUbsan.M.loaded_segments (0xe0cf8 : word) = Some W_e01b0.
Proof. vm_refl. Qed.
Lemma D_e01b0 : decode_any W_e01b0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01b4 : bv 32 := 0x0116a223.
Lemma F_e01b4 : fetch_word AsanUbsan.M.loaded_segments (0xe0cfc : word) = Some W_e01b4.
Proof. vm_refl. Qed.
Lemma D_e01b4 : decode_any W_e01b4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01b8 : bv 32 := 0x0056a423.
Lemma F_e01b8 : fetch_word AsanUbsan.M.loaded_segments (0xe0d00 : word) = Some W_e01b8.
Proof. vm_refl. Qed.
Lemma D_e01b8 : decode_any W_e01b8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01bc : bv 32 := 0x0066a623.
Lemma F_e01bc : fetch_word AsanUbsan.M.loaded_segments (0xe0d04 : word) = Some W_e01bc.
Proof. vm_refl. Qed.
Lemma D_e01bc : decode_any W_e01bc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01c0 : bv 32 := 0x01068693.
Lemma F_e01c0 : fetch_word AsanUbsan.M.loaded_segments (0xe0d08 : word) = Some W_e01c0.
Proof. vm_refl. Qed.
Lemma D_e01c0 : decode_any W_e01c0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01c4 : bv 32 := 0x01058593.
Lemma F_e01c4 : fetch_word AsanUbsan.M.loaded_segments (0xe0d0c : word) = Some W_e01c4.
Proof. vm_refl. Qed.
Lemma D_e01c4 : decode_any W_e01c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01c8 : bv 32 := 0xfac7e2e3.
Lemma F_e01c8 : fetch_word AsanUbsan.M.loaded_segments (0xe0d10 : word) = Some W_e01c8.
Proof. vm_refl. Qed.
Lemma D_e01c8 : decode_any W_e01c8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01cc : bv 32 := 0xff258593.
Lemma F_e01cc : fetch_word AsanUbsan.M.loaded_segments (0xe0d14 : word) = Some W_e01cc.
Proof. vm_refl. Qed.
Lemma D_e01cc : decode_any W_e01cc = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01d0 : bv 32 := 0x01000713.
Lemma F_e01d0 : fetch_word AsanUbsan.M.loaded_segments (0xe0d18 : word) = Some W_e01d0.
Proof. vm_refl. Qed.
Lemma D_e01d0 : decode_any W_e01d0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01d4 : bv 32 := 0xf4e66ae3.
Lemma F_e01d4 : fetch_word AsanUbsan.M.loaded_segments (0xe0d1c : word) = Some W_e01d4.
Proof. vm_refl. Qed.
Lemma D_e01d4 : decode_any W_e01d4 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01d8 : bv 32 := 0x19c0006f.
Lemma F_e01d8 : fetch_word AsanUbsan.M.loaded_segments (0xe0d20 : word) = Some W_e01d8.
Proof. vm_refl. Qed.
Lemma D_e01d8 : decode_any W_e01d8 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01dc : bv 32 := 0x00050693.
Lemma F_e01dc : fetch_word AsanUbsan.M.loaded_segments (0xe0d24 : word) = Some W_e01dc.
Proof. vm_refl. Qed.
Lemma D_e01dc : decode_any W_e01dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01e0 : bv 32 := 0x00357793.
Lemma F_e01e0 : fetch_word AsanUbsan.M.loaded_segments (0xe0d28 : word) = Some W_e01e0.
Proof. vm_refl. Qed.
Lemma D_e01e0 : decode_any W_e01e0 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01e4 : bv 32 := 0xf2079ae3.
Lemma F_e01e4 : fetch_word AsanUbsan.M.loaded_segments (0xe0d2c : word) = Some W_e01e4.
Proof. vm_refl. Qed.
Lemma D_e01e4 : decode_any W_e01e4 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01e8 : bv 32 := 0x01000713.
Lemma F_e01e8 : fetch_word AsanUbsan.M.loaded_segments (0xe0d30 : word) = Some W_e01e8.
Proof. vm_refl. Qed.
Lemma D_e01e8 : decode_any W_e01e8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01ec : bv 32 := 0x02e66c63.
Lemma F_e01ec : fetch_word AsanUbsan.M.loaded_segments (0xe0d34 : word) = Some W_e01ec.
Proof. vm_refl. Qed.
Lemma D_e01ec : decode_any W_e01ec = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01f0 : bv 32 := 0x00f00713.
Lemma F_e01f0 : fetch_word AsanUbsan.M.loaded_segments (0xe0d38 : word) = Some W_e01f0.
Proof. vm_refl. Qed.
Lemma D_e01f0 : decode_any W_e01f0 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01f4 : bv 32 := 0x0005a783.
Lemma F_e01f4 : fetch_word AsanUbsan.M.loaded_segments (0xe0d3c : word) = Some W_e01f4.
Proof. vm_refl. Qed.
Lemma D_e01f4 : decode_any W_e01f4 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01f8 : bv 32 := 0x0045a803.
Lemma F_e01f8 : fetch_word AsanUbsan.M.loaded_segments (0xe0d40 : word) = Some W_e01f8.
Proof. vm_refl. Qed.
Lemma D_e01f8 : decode_any W_e01f8 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e01fc : bv 32 := 0x0085a883.
Lemma F_e01fc : fetch_word AsanUbsan.M.loaded_segments (0xe0d44 : word) = Some W_e01fc.
Proof. vm_refl. Qed.
Lemma D_e01fc : decode_any W_e01fc = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0200 : bv 32 := 0x00c5a283.
Lemma F_e0200 : fetch_word AsanUbsan.M.loaded_segments (0xe0d48 : word) = Some W_e0200.
Proof. vm_refl. Qed.
Lemma D_e0200 : decode_any W_e0200 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0204 : bv 32 := 0x01058593.
Lemma F_e0204 : fetch_word AsanUbsan.M.loaded_segments (0xe0d4c : word) = Some W_e0204.
Proof. vm_refl. Qed.
Lemma D_e0204 : decode_any W_e0204 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0208 : bv 32 := 0xff060613.
Lemma F_e0208 : fetch_word AsanUbsan.M.loaded_segments (0xe0d50 : word) = Some W_e0208.
Proof. vm_refl. Qed.
Lemma D_e0208 : decode_any W_e0208 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e020c : bv 32 := 0x00f6a023.
Lemma F_e020c : fetch_word AsanUbsan.M.loaded_segments (0xe0d54 : word) = Some W_e020c.
Proof. vm_refl. Qed.
Lemma D_e020c : decode_any W_e020c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0210 : bv 32 := 0x0106a223.
Lemma F_e0210 : fetch_word AsanUbsan.M.loaded_segments (0xe0d58 : word) = Some W_e0210.
Proof. vm_refl. Qed.
Lemma D_e0210 : decode_any W_e0210 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0214 : bv 32 := 0x0116a423.
Lemma F_e0214 : fetch_word AsanUbsan.M.loaded_segments (0xe0d5c : word) = Some W_e0214.
Proof. vm_refl. Qed.
Lemma D_e0214 : decode_any W_e0214 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0218 : bv 32 := 0x0056a623.
Lemma F_e0218 : fetch_word AsanUbsan.M.loaded_segments (0xe0d60 : word) = Some W_e0218.
Proof. vm_refl. Qed.
Lemma D_e0218 : decode_any W_e0218 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e021c : bv 32 := 0x01068693.
Lemma F_e021c : fetch_word AsanUbsan.M.loaded_segments (0xe0d64 : word) = Some W_e021c.
Proof. vm_refl. Qed.
Lemma D_e021c : decode_any W_e021c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0220 : bv 32 := 0xfcc76ae3.
Lemma F_e0220 : fetch_word AsanUbsan.M.loaded_segments (0xe0d68 : word) = Some W_e0220.
Proof. vm_refl. Qed.
Lemma D_e0220 : decode_any W_e0220 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0224 : bv 32 := 0x00800713.
Lemma F_e0224 : fetch_word AsanUbsan.M.loaded_segments (0xe0d6c : word) = Some W_e0224.
Proof. vm_refl. Qed.
Lemma D_e0224 : decode_any W_e0224 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0228 : bv 32 := 0x00e66e63.
Lemma F_e0228 : fetch_word AsanUbsan.M.loaded_segments (0xe0d70 : word) = Some W_e0228.
Proof. vm_refl. Qed.
Lemma D_e0228 : decode_any W_e0228 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e022c : bv 32 := 0x0005a703.
Lemma F_e022c : fetch_word AsanUbsan.M.loaded_segments (0xe0d74 : word) = Some W_e022c.
Proof. vm_refl. Qed.
Lemma D_e022c : decode_any W_e022c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0230 : bv 32 := 0x0045a783.
Lemma F_e0230 : fetch_word AsanUbsan.M.loaded_segments (0xe0d78 : word) = Some W_e0230.
Proof. vm_refl. Qed.
Lemma D_e0230 : decode_any W_e0230 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0234 : bv 32 := 0x00e6a023.
Lemma F_e0234 : fetch_word AsanUbsan.M.loaded_segments (0xe0d7c : word) = Some W_e0234.
Proof. vm_refl. Qed.
Lemma D_e0234 : decode_any W_e0234 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0238 : bv 32 := 0x00f6a223.
Lemma F_e0238 : fetch_word AsanUbsan.M.loaded_segments (0xe0d80 : word) = Some W_e0238.
Proof. vm_refl. Qed.
Lemma D_e0238 : decode_any W_e0238 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e023c : bv 32 := 0x00868693.
Lemma F_e023c : fetch_word AsanUbsan.M.loaded_segments (0xe0d84 : word) = Some W_e023c.
Proof. vm_refl. Qed.
Lemma D_e023c : decode_any W_e023c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0240 : bv 32 := 0x00858593.
Lemma F_e0240 : fetch_word AsanUbsan.M.loaded_segments (0xe0d88 : word) = Some W_e0240.
Proof. vm_refl. Qed.
Lemma D_e0240 : decode_any W_e0240 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0244 : bv 32 := 0x00467713.
Lemma F_e0244 : fetch_word AsanUbsan.M.loaded_segments (0xe0d8c : word) = Some W_e0244.
Proof. vm_refl. Qed.
Lemma D_e0244 : decode_any W_e0244 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0248 : bv 32 := 0x24070063.
Lemma F_e0248 : fetch_word AsanUbsan.M.loaded_segments (0xe0d90 : word) = Some W_e0248.
Proof. vm_refl. Qed.
Lemma D_e0248 : decode_any W_e0248 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e024c : bv 32 := 0x0005a703.
Lemma F_e024c : fetch_word AsanUbsan.M.loaded_segments (0xe0d94 : word) = Some W_e024c.
Proof. vm_refl. Qed.
Lemma D_e024c : decode_any W_e024c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0250 : bv 32 := 0x00458593.
Lemma F_e0250 : fetch_word AsanUbsan.M.loaded_segments (0xe0d98 : word) = Some W_e0250.
Proof. vm_refl. Qed.
Lemma D_e0250 : decode_any W_e0250 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0254 : bv 32 := 0x00e6a023.
Lemma F_e0254 : fetch_word AsanUbsan.M.loaded_segments (0xe0d9c : word) = Some W_e0254.
Proof. vm_refl. Qed.
Lemma D_e0254 : decode_any W_e0254 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0258 : bv 32 := 0x00468693.
Lemma F_e0258 : fetch_word AsanUbsan.M.loaded_segments (0xe0da0 : word) = Some W_e0258.
Proof. vm_refl. Qed.
Lemma D_e0258 : decode_any W_e0258 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e025c : bv 32 := 0x22c0006f.
Lemma F_e025c : fetch_word AsanUbsan.M.loaded_segments (0xe0da4 : word) = Some W_e025c.
Proof. vm_refl. Qed.
Lemma D_e025c : decode_any W_e025c = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0260 : bv 32 := 0x00e68023.
Lemma F_e0260 : fetch_word AsanUbsan.M.loaded_segments (0xe0da8 : word) = Some W_e0260.
Proof. vm_refl. Qed.
Lemma D_e0260 : decode_any W_e0260 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0264 : bv 32 := 0x00168693.
Lemma F_e0264 : fetch_word AsanUbsan.M.loaded_segments (0xe0dac : word) = Some W_e0264.
Proof. vm_refl. Qed.
Lemma D_e0264 : decode_any W_e0264 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0268 : bv 32 := 0xfff60613.
Lemma F_e0268 : fetch_word AsanUbsan.M.loaded_segments (0xe0db0 : word) = Some W_e0268.
Proof. vm_refl. Qed.
Lemma D_e0268 : decode_any W_e0268 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e026c : bv 32 := 0x01058593.
Lemma F_e026c : fetch_word AsanUbsan.M.loaded_segments (0xe0db4 : word) = Some W_e026c.
Proof. vm_refl. Qed.
Lemma D_e026c : decode_any W_e026c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0270 : bv 32 := 0x01200793.
Lemma F_e0270 : fetch_word AsanUbsan.M.loaded_segments (0xe0db8 : word) = Some W_e0270.
Proof. vm_refl. Qed.
Lemma D_e0270 : decode_any W_e0270 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0274 : bv 32 := 0x0087581b.
Lemma F_e0274 : fetch_word AsanUbsan.M.loaded_segments (0xe0dbc : word) = Some W_e0274.
Proof. vm_refl. Qed.
Lemma D_e0274 : decode_any W_e0274 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0278 : bv 32 := 0xff45a883.
Lemma F_e0278 : fetch_word AsanUbsan.M.loaded_segments (0xe0dc0 : word) = Some W_e0278.
Proof. vm_refl. Qed.
Lemma D_e0278 : decode_any W_e0278 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e027c : bv 32 := 0xff85a283.
Lemma F_e027c : fetch_word AsanUbsan.M.loaded_segments (0xe0dc4 : word) = Some W_e027c.
Proof. vm_refl. Qed.
Lemma D_e027c : decode_any W_e027c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0280 : bv 32 := 0xffc5a303.
Lemma F_e0280 : fetch_word AsanUbsan.M.loaded_segments (0xe0dc8 : word) = Some W_e0280.
Proof. vm_refl. Qed.
Lemma D_e0280 : decode_any W_e0280 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0284 : bv 32 := 0x0005a703.
Lemma F_e0284 : fetch_word AsanUbsan.M.loaded_segments (0xe0dcc : word) = Some W_e0284.
Proof. vm_refl. Qed.
Lemma D_e0284 : decode_any W_e0284 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0288 : bv 32 := 0x01889393.
Lemma F_e0288 : fetch_word AsanUbsan.M.loaded_segments (0xe0dd0 : word) = Some W_e0288.
Proof. vm_refl. Qed.
Lemma D_e0288 : decode_any W_e0288 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e028c : bv 32 := 0x0088d89b.
Lemma F_e028c : fetch_word AsanUbsan.M.loaded_segments (0xe0dd4 : word) = Some W_e028c.
Proof. vm_refl. Qed.
Lemma D_e028c : decode_any W_e028c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0290 : bv 32 := 0x0103e833.
Lemma F_e0290 : fetch_word AsanUbsan.M.loaded_segments (0xe0dd8 : word) = Some W_e0290.
Proof. vm_refl. Qed.
Lemma D_e0290 : decode_any W_e0290 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0294 : bv 32 := 0x01829393.
Lemma F_e0294 : fetch_word AsanUbsan.M.loaded_segments (0xe0ddc : word) = Some W_e0294.
Proof. vm_refl. Qed.
Lemma D_e0294 : decode_any W_e0294 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0298 : bv 32 := 0x0082d29b.
Lemma F_e0298 : fetch_word AsanUbsan.M.loaded_segments (0xe0de0 : word) = Some W_e0298.
Proof. vm_refl. Qed.
Lemma D_e0298 : decode_any W_e0298 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e029c : bv 32 := 0x0113e8b3.
Lemma F_e029c : fetch_word AsanUbsan.M.loaded_segments (0xe0de4 : word) = Some W_e029c.
Proof. vm_refl. Qed.
Lemma D_e029c : decode_any W_e029c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02a0 : bv 32 := 0x01831393.
Lemma F_e02a0 : fetch_word AsanUbsan.M.loaded_segments (0xe0de8 : word) = Some W_e02a0.
Proof. vm_refl. Qed.
Lemma D_e02a0 : decode_any W_e02a0 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02a4 : bv 32 := 0x0083531b.
Lemma F_e02a4 : fetch_word AsanUbsan.M.loaded_segments (0xe0dec : word) = Some W_e02a4.
Proof. vm_refl. Qed.
Lemma D_e02a4 : decode_any W_e02a4 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02a8 : bv 32 := 0x0053e2b3.
Lemma F_e02a8 : fetch_word AsanUbsan.M.loaded_segments (0xe0df0 : word) = Some W_e02a8.
Proof. vm_refl. Qed.
Lemma D_e02a8 : decode_any W_e02a8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02ac : bv 32 := 0x01871393.
Lemma F_e02ac : fetch_word AsanUbsan.M.loaded_segments (0xe0df4 : word) = Some W_e02ac.
Proof. vm_refl. Qed.
Lemma D_e02ac : decode_any W_e02ac = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02b0 : bv 32 := 0x0063e333.
Lemma F_e02b0 : fetch_word AsanUbsan.M.loaded_segments (0xe0df8 : word) = Some W_e02b0.
Proof. vm_refl. Qed.
Lemma D_e02b0 : decode_any W_e02b0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02b4 : bv 32 := 0xff060613.
Lemma F_e02b4 : fetch_word AsanUbsan.M.loaded_segments (0xe0dfc : word) = Some W_e02b4.
Proof. vm_refl. Qed.
Lemma D_e02b4 : decode_any W_e02b4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02b8 : bv 32 := 0x0106a023.
Lemma F_e02b8 : fetch_word AsanUbsan.M.loaded_segments (0xe0e00 : word) = Some W_e02b8.
Proof. vm_refl. Qed.
Lemma D_e02b8 : decode_any W_e02b8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02bc : bv 32 := 0x0116a223.
Lemma F_e02bc : fetch_word AsanUbsan.M.loaded_segments (0xe0e04 : word) = Some W_e02bc.
Proof. vm_refl. Qed.
Lemma D_e02bc : decode_any W_e02bc = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02c0 : bv 32 := 0x0056a423.
Lemma F_e02c0 : fetch_word AsanUbsan.M.loaded_segments (0xe0e08 : word) = Some W_e02c0.
Proof. vm_refl. Qed.
Lemma D_e02c0 : decode_any W_e02c0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02c4 : bv 32 := 0x0066a623.
Lemma F_e02c4 : fetch_word AsanUbsan.M.loaded_segments (0xe0e0c : word) = Some W_e02c4.
Proof. vm_refl. Qed.
Lemma D_e02c4 : decode_any W_e02c4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02c8 : bv 32 := 0x01068693.
Lemma F_e02c8 : fetch_word AsanUbsan.M.loaded_segments (0xe0e10 : word) = Some W_e02c8.
Proof. vm_refl. Qed.
Lemma D_e02c8 : decode_any W_e02c8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02cc : bv 32 := 0x01058593.
Lemma F_e02cc : fetch_word AsanUbsan.M.loaded_segments (0xe0e14 : word) = Some W_e02cc.
Proof. vm_refl. Qed.
Lemma D_e02cc : decode_any W_e02cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02d0 : bv 32 := 0xfac7e2e3.
Lemma F_e02d0 : fetch_word AsanUbsan.M.loaded_segments (0xe0e18 : word) = Some W_e02d0.
Proof. vm_refl. Qed.
Lemma D_e02d0 : decode_any W_e02d0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02d4 : bv 32 := 0xff158593.
Lemma F_e02d4 : fetch_word AsanUbsan.M.loaded_segments (0xe0e1c : word) = Some W_e02d4.
Proof. vm_refl. Qed.
Lemma D_e02d4 : decode_any W_e02d4 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02d8 : bv 32 := 0x01000713.
Lemma F_e02d8 : fetch_word AsanUbsan.M.loaded_segments (0xe0e20 : word) = Some W_e02d8.
Proof. vm_refl. Qed.
Lemma D_e02d8 : decode_any W_e02d8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02dc : bv 32 := 0xe4e666e3.
Lemma F_e02dc : fetch_word AsanUbsan.M.loaded_segments (0xe0e24 : word) = Some W_e02dc.
Proof. vm_refl. Qed.
Lemma D_e02dc : decode_any W_e02dc = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02e0 : bv 32 := 0x0940006f.
Lemma F_e02e0 : fetch_word AsanUbsan.M.loaded_segments (0xe0e28 : word) = Some W_e02e0.
Proof. vm_refl. Qed.
Lemma D_e02e0 : decode_any W_e02e0 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02e4 : bv 32 := 0x00875793.
Lemma F_e02e4 : fetch_word AsanUbsan.M.loaded_segments (0xe0e2c : word) = Some W_e02e4.
Proof. vm_refl. Qed.
Lemma D_e02e4 : decode_any W_e02e4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02e8 : bv 32 := 0x01075813.
Lemma F_e02e8 : fetch_word AsanUbsan.M.loaded_segments (0xe0e30 : word) = Some W_e02e8.
Proof. vm_refl. Qed.
Lemma D_e02e8 : decode_any W_e02e8 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02ec : bv 32 := 0xffd60613.
Lemma F_e02ec : fetch_word AsanUbsan.M.loaded_segments (0xe0e34 : word) = Some W_e02ec.
Proof. vm_refl. Qed.
Lemma D_e02ec : decode_any W_e02ec = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02f0 : bv 32 := 0x00e68023.
Lemma F_e02f0 : fetch_word AsanUbsan.M.loaded_segments (0xe0e38 : word) = Some W_e02f0.
Proof. vm_refl. Qed.
Lemma D_e02f0 : decode_any W_e02f0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02f4 : bv 32 := 0x00f680a3.
Lemma F_e02f4 : fetch_word AsanUbsan.M.loaded_segments (0xe0e3c : word) = Some W_e02f4.
Proof. vm_refl. Qed.
Lemma D_e02f4 : decode_any W_e02f4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02f8 : bv 32 := 0x01068123.
Lemma F_e02f8 : fetch_word AsanUbsan.M.loaded_segments (0xe0e40 : word) = Some W_e02f8.
Proof. vm_refl. Qed.
Lemma D_e02f8 : decode_any W_e02f8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e02fc : bv 32 := 0x00368693.
Lemma F_e02fc : fetch_word AsanUbsan.M.loaded_segments (0xe0e44 : word) = Some W_e02fc.
Proof. vm_refl. Qed.
Lemma D_e02fc : decode_any W_e02fc = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0300 : bv 32 := 0x01058593.
Lemma F_e0300 : fetch_word AsanUbsan.M.loaded_segments (0xe0e48 : word) = Some W_e0300.
Proof. vm_refl. Qed.
Lemma D_e0300 : decode_any W_e0300 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0304 : bv 32 := 0x01000793.
Lemma F_e0304 : fetch_word AsanUbsan.M.loaded_segments (0xe0e4c : word) = Some W_e0304.
Proof. vm_refl. Qed.
Lemma D_e0304 : decode_any W_e0304 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0308 : bv 32 := 0x0187581b.
Lemma F_e0308 : fetch_word AsanUbsan.M.loaded_segments (0xe0e50 : word) = Some W_e0308.
Proof. vm_refl. Qed.
Lemma D_e0308 : decode_any W_e0308 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e030c : bv 32 := 0xff45a883.
Lemma F_e030c : fetch_word AsanUbsan.M.loaded_segments (0xe0e54 : word) = Some W_e030c.
Proof. vm_refl. Qed.
Lemma D_e030c : decode_any W_e030c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0310 : bv 32 := 0xff85a283.
Lemma F_e0310 : fetch_word AsanUbsan.M.loaded_segments (0xe0e58 : word) = Some W_e0310.
Proof. vm_refl. Qed.
Lemma D_e0310 : decode_any W_e0310 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0314 : bv 32 := 0xffc5a303.
Lemma F_e0314 : fetch_word AsanUbsan.M.loaded_segments (0xe0e5c : word) = Some W_e0314.
Proof. vm_refl. Qed.
Lemma D_e0314 : decode_any W_e0314 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0318 : bv 32 := 0x0005a703.
Lemma F_e0318 : fetch_word AsanUbsan.M.loaded_segments (0xe0e60 : word) = Some W_e0318.
Proof. vm_refl. Qed.
Lemma D_e0318 : decode_any W_e0318 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e031c : bv 32 := 0x00889393.
Lemma F_e031c : fetch_word AsanUbsan.M.loaded_segments (0xe0e64 : word) = Some W_e031c.
Proof. vm_refl. Qed.
Lemma D_e031c : decode_any W_e031c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0320 : bv 32 := 0x0188d89b.
Lemma F_e0320 : fetch_word AsanUbsan.M.loaded_segments (0xe0e68 : word) = Some W_e0320.
Proof. vm_refl. Qed.
Lemma D_e0320 : decode_any W_e0320 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0324 : bv 32 := 0x0103e833.
Lemma F_e0324 : fetch_word AsanUbsan.M.loaded_segments (0xe0e6c : word) = Some W_e0324.
Proof. vm_refl. Qed.
Lemma D_e0324 : decode_any W_e0324 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0328 : bv 32 := 0x00829393.
Lemma F_e0328 : fetch_word AsanUbsan.M.loaded_segments (0xe0e70 : word) = Some W_e0328.
Proof. vm_refl. Qed.
Lemma D_e0328 : decode_any W_e0328 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e032c : bv 32 := 0x0182d29b.
Lemma F_e032c : fetch_word AsanUbsan.M.loaded_segments (0xe0e74 : word) = Some W_e032c.
Proof. vm_refl. Qed.
Lemma D_e032c : decode_any W_e032c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0330 : bv 32 := 0x0113e8b3.
Lemma F_e0330 : fetch_word AsanUbsan.M.loaded_segments (0xe0e78 : word) = Some W_e0330.
Proof. vm_refl. Qed.
Lemma D_e0330 : decode_any W_e0330 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0334 : bv 32 := 0x00831393.
Lemma F_e0334 : fetch_word AsanUbsan.M.loaded_segments (0xe0e7c : word) = Some W_e0334.
Proof. vm_refl. Qed.
Lemma D_e0334 : decode_any W_e0334 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0338 : bv 32 := 0x0183531b.
Lemma F_e0338 : fetch_word AsanUbsan.M.loaded_segments (0xe0e80 : word) = Some W_e0338.
Proof. vm_refl. Qed.
Lemma D_e0338 : decode_any W_e0338 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e033c : bv 32 := 0x0053e2b3.
Lemma F_e033c : fetch_word AsanUbsan.M.loaded_segments (0xe0e84 : word) = Some W_e033c.
Proof. vm_refl. Qed.
Lemma D_e033c : decode_any W_e033c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0340 : bv 32 := 0x00871393.
Lemma F_e0340 : fetch_word AsanUbsan.M.loaded_segments (0xe0e88 : word) = Some W_e0340.
Proof. vm_refl. Qed.
Lemma D_e0340 : decode_any W_e0340 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0344 : bv 32 := 0x0063e333.
Lemma F_e0344 : fetch_word AsanUbsan.M.loaded_segments (0xe0e8c : word) = Some W_e0344.
Proof. vm_refl. Qed.
Lemma D_e0344 : decode_any W_e0344 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0348 : bv 32 := 0xff060613.
Lemma F_e0348 : fetch_word AsanUbsan.M.loaded_segments (0xe0e90 : word) = Some W_e0348.
Proof. vm_refl. Qed.
Lemma D_e0348 : decode_any W_e0348 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e034c : bv 32 := 0x0106a023.
Lemma F_e034c : fetch_word AsanUbsan.M.loaded_segments (0xe0e94 : word) = Some W_e034c.
Proof. vm_refl. Qed.
Lemma D_e034c : decode_any W_e034c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0350 : bv 32 := 0x0116a223.
Lemma F_e0350 : fetch_word AsanUbsan.M.loaded_segments (0xe0e98 : word) = Some W_e0350.
Proof. vm_refl. Qed.
Lemma D_e0350 : decode_any W_e0350 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0354 : bv 32 := 0x0056a423.
Lemma F_e0354 : fetch_word AsanUbsan.M.loaded_segments (0xe0e9c : word) = Some W_e0354.
Proof. vm_refl. Qed.
Lemma D_e0354 : decode_any W_e0354 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0358 : bv 32 := 0x0066a623.
Lemma F_e0358 : fetch_word AsanUbsan.M.loaded_segments (0xe0ea0 : word) = Some W_e0358.
Proof. vm_refl. Qed.
Lemma D_e0358 : decode_any W_e0358 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e035c : bv 32 := 0x01068693.
Lemma F_e035c : fetch_word AsanUbsan.M.loaded_segments (0xe0ea4 : word) = Some W_e035c.
Proof. vm_refl. Qed.
Lemma D_e035c : decode_any W_e035c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0360 : bv 32 := 0x01058593.
Lemma F_e0360 : fetch_word AsanUbsan.M.loaded_segments (0xe0ea8 : word) = Some W_e0360.
Proof. vm_refl. Qed.
Lemma D_e0360 : decode_any W_e0360 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0364 : bv 32 := 0xfac7e2e3.
Lemma F_e0364 : fetch_word AsanUbsan.M.loaded_segments (0xe0eac : word) = Some W_e0364.
Proof. vm_refl. Qed.
Lemma D_e0364 : decode_any W_e0364 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0368 : bv 32 := 0xff358593.
Lemma F_e0368 : fetch_word AsanUbsan.M.loaded_segments (0xe0eb0 : word) = Some W_e0368.
Proof. vm_refl. Qed.
Lemma D_e0368 : decode_any W_e0368 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e036c : bv 32 := 0x01000713.
Lemma F_e036c : fetch_word AsanUbsan.M.loaded_segments (0xe0eb4 : word) = Some W_e036c.
Proof. vm_refl. Qed.
Lemma D_e036c : decode_any W_e036c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0370 : bv 32 := 0xdae66ce3.
Lemma F_e0370 : fetch_word AsanUbsan.M.loaded_segments (0xe0eb8 : word) = Some W_e0370.
Proof. vm_refl. Qed.
Lemma D_e0370 : decode_any W_e0370 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0374 : bv 32 := 0x0005c703.
Lemma F_e0374 : fetch_word AsanUbsan.M.loaded_segments (0xe0ebc : word) = Some W_e0374.
Proof. vm_refl. Qed.
Lemma D_e0374 : decode_any W_e0374 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0378 : bv 32 := 0x0015c783.
Lemma F_e0378 : fetch_word AsanUbsan.M.loaded_segments (0xe0ec0 : word) = Some W_e0378.
Proof. vm_refl. Qed.
Lemma D_e0378 : decode_any W_e0378 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e037c : bv 32 := 0x0025c803.
Lemma F_e037c : fetch_word AsanUbsan.M.loaded_segments (0xe0ec4 : word) = Some W_e037c.
Proof. vm_refl. Qed.
Lemma D_e037c : decode_any W_e037c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0380 : bv 32 := 0x0035c883.
Lemma F_e0380 : fetch_word AsanUbsan.M.loaded_segments (0xe0ec8 : word) = Some W_e0380.
Proof. vm_refl. Qed.
Lemma D_e0380 : decode_any W_e0380 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0384 : bv 32 := 0x0045c283.
Lemma F_e0384 : fetch_word AsanUbsan.M.loaded_segments (0xe0ecc : word) = Some W_e0384.
Proof. vm_refl. Qed.
Lemma D_e0384 : decode_any W_e0384 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0388 : bv 32 := 0x0055c303.
Lemma F_e0388 : fetch_word AsanUbsan.M.loaded_segments (0xe0ed0 : word) = Some W_e0388.
Proof. vm_refl. Qed.
Lemma D_e0388 : decode_any W_e0388 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e038c : bv 32 := 0x0065c383.
Lemma F_e038c : fetch_word AsanUbsan.M.loaded_segments (0xe0ed4 : word) = Some W_e038c.
Proof. vm_refl. Qed.
Lemma D_e038c : decode_any W_e038c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0390 : bv 32 := 0x0075ce03.
Lemma F_e0390 : fetch_word AsanUbsan.M.loaded_segments (0xe0ed8 : word) = Some W_e0390.
Proof. vm_refl. Qed.
Lemma D_e0390 : decode_any W_e0390 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0394 : bv 32 := 0x00e68023.
Lemma F_e0394 : fetch_word AsanUbsan.M.loaded_segments (0xe0edc : word) = Some W_e0394.
Proof. vm_refl. Qed.
Lemma D_e0394 : decode_any W_e0394 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0398 : bv 32 := 0x00f680a3.
Lemma F_e0398 : fetch_word AsanUbsan.M.loaded_segments (0xe0ee0 : word) = Some W_e0398.
Proof. vm_refl. Qed.
Lemma D_e0398 : decode_any W_e0398 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e039c : bv 32 := 0x01068123.
Lemma F_e039c : fetch_word AsanUbsan.M.loaded_segments (0xe0ee4 : word) = Some W_e039c.
Proof. vm_refl. Qed.
Lemma D_e039c : decode_any W_e039c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03a0 : bv 32 := 0x011681a3.
Lemma F_e03a0 : fetch_word AsanUbsan.M.loaded_segments (0xe0ee8 : word) = Some W_e03a0.
Proof. vm_refl. Qed.
Lemma D_e03a0 : decode_any W_e03a0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03a4 : bv 32 := 0x0085c703.
Lemma F_e03a4 : fetch_word AsanUbsan.M.loaded_segments (0xe0eec : word) = Some W_e03a4.
Proof. vm_refl. Qed.
Lemma D_e03a4 : decode_any W_e03a4 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03a8 : bv 32 := 0x0095c783.
Lemma F_e03a8 : fetch_word AsanUbsan.M.loaded_segments (0xe0ef0 : word) = Some W_e03a8.
Proof. vm_refl. Qed.
Lemma D_e03a8 : decode_any W_e03a8 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03ac : bv 32 := 0x00a5c803.
Lemma F_e03ac : fetch_word AsanUbsan.M.loaded_segments (0xe0ef4 : word) = Some W_e03ac.
Proof. vm_refl. Qed.
Lemma D_e03ac : decode_any W_e03ac = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03b0 : bv 32 := 0x00b5c883.
Lemma F_e03b0 : fetch_word AsanUbsan.M.loaded_segments (0xe0ef8 : word) = Some W_e03b0.
Proof. vm_refl. Qed.
Lemma D_e03b0 : decode_any W_e03b0 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03b4 : bv 32 := 0x00568223.
Lemma F_e03b4 : fetch_word AsanUbsan.M.loaded_segments (0xe0efc : word) = Some W_e03b4.
Proof. vm_refl. Qed.
Lemma D_e03b4 : decode_any W_e03b4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03b8 : bv 32 := 0x006682a3.
Lemma F_e03b8 : fetch_word AsanUbsan.M.loaded_segments (0xe0f00 : word) = Some W_e03b8.
Proof. vm_refl. Qed.
Lemma D_e03b8 : decode_any W_e03b8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03bc : bv 32 := 0x00768323.
Lemma F_e03bc : fetch_word AsanUbsan.M.loaded_segments (0xe0f04 : word) = Some W_e03bc.
Proof. vm_refl. Qed.
Lemma D_e03bc : decode_any W_e03bc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03c0 : bv 32 := 0x01c683a3.
Lemma F_e03c0 : fetch_word AsanUbsan.M.loaded_segments (0xe0f08 : word) = Some W_e03c0.
Proof. vm_refl. Qed.
Lemma D_e03c0 : decode_any W_e03c0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03c4 : bv 32 := 0x00c5c283.
Lemma F_e03c4 : fetch_word AsanUbsan.M.loaded_segments (0xe0f0c : word) = Some W_e03c4.
Proof. vm_refl. Qed.
Lemma D_e03c4 : decode_any W_e03c4 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03c8 : bv 32 := 0x00d5c303.
Lemma F_e03c8 : fetch_word AsanUbsan.M.loaded_segments (0xe0f10 : word) = Some W_e03c8.
Proof. vm_refl. Qed.
Lemma D_e03c8 : decode_any W_e03c8 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03cc : bv 32 := 0x00e5c383.
Lemma F_e03cc : fetch_word AsanUbsan.M.loaded_segments (0xe0f14 : word) = Some W_e03cc.
Proof. vm_refl. Qed.
Lemma D_e03cc : decode_any W_e03cc = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03d0 : bv 32 := 0x00f5ce03.
Lemma F_e03d0 : fetch_word AsanUbsan.M.loaded_segments (0xe0f18 : word) = Some W_e03d0.
Proof. vm_refl. Qed.
Lemma D_e03d0 : decode_any W_e03d0 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03d4 : bv 32 := 0x01058593.
Lemma F_e03d4 : fetch_word AsanUbsan.M.loaded_segments (0xe0f1c : word) = Some W_e03d4.
Proof. vm_refl. Qed.
Lemma D_e03d4 : decode_any W_e03d4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03d8 : bv 32 := 0x00e68423.
Lemma F_e03d8 : fetch_word AsanUbsan.M.loaded_segments (0xe0f20 : word) = Some W_e03d8.
Proof. vm_refl. Qed.
Lemma D_e03d8 : decode_any W_e03d8 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03dc : bv 32 := 0x00f684a3.
Lemma F_e03dc : fetch_word AsanUbsan.M.loaded_segments (0xe0f24 : word) = Some W_e03dc.
Proof. vm_refl. Qed.
Lemma D_e03dc : decode_any W_e03dc = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03e0 : bv 32 := 0x01068523.
Lemma F_e03e0 : fetch_word AsanUbsan.M.loaded_segments (0xe0f28 : word) = Some W_e03e0.
Proof. vm_refl. Qed.
Lemma D_e03e0 : decode_any W_e03e0 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03e4 : bv 32 := 0x011685a3.
Lemma F_e03e4 : fetch_word AsanUbsan.M.loaded_segments (0xe0f2c : word) = Some W_e03e4.
Proof. vm_refl. Qed.
Lemma D_e03e4 : decode_any W_e03e4 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03e8 : bv 32 := 0x01068713.
Lemma F_e03e8 : fetch_word AsanUbsan.M.loaded_segments (0xe0f30 : word) = Some W_e03e8.
Proof. vm_refl. Qed.
Lemma D_e03e8 : decode_any W_e03e8 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03ec : bv 32 := 0x00568623.
Lemma F_e03ec : fetch_word AsanUbsan.M.loaded_segments (0xe0f34 : word) = Some W_e03ec.
Proof. vm_refl. Qed.
Lemma D_e03ec : decode_any W_e03ec = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03f0 : bv 32 := 0x006686a3.
Lemma F_e03f0 : fetch_word AsanUbsan.M.loaded_segments (0xe0f38 : word) = Some W_e03f0.
Proof. vm_refl. Qed.
Lemma D_e03f0 : decode_any W_e03f0 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03f4 : bv 32 := 0x00768723.
Lemma F_e03f4 : fetch_word AsanUbsan.M.loaded_segments (0xe0f3c : word) = Some W_e03f4.
Proof. vm_refl. Qed.
Lemma D_e03f4 : decode_any W_e03f4 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03f8 : bv 32 := 0x01c687a3.
Lemma F_e03f8 : fetch_word AsanUbsan.M.loaded_segments (0xe0f40 : word) = Some W_e03f8.
Proof. vm_refl. Qed.
Lemma D_e03f8 : decode_any W_e03f8 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e03fc : bv 32 := 0x00070693.
Lemma F_e03fc : fetch_word AsanUbsan.M.loaded_segments (0xe0f44 : word) = Some W_e03fc.
Proof. vm_refl. Qed.
Lemma D_e03fc : decode_any W_e03fc = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0400 : bv 32 := 0x00867713.
Lemma F_e0400 : fetch_word AsanUbsan.M.loaded_segments (0xe0f48 : word) = Some W_e0400.
Proof. vm_refl. Qed.
Lemma D_e0400 : decode_any W_e0400 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0404 : bv 32 := 0xd20706e3.
Lemma F_e0404 : fetch_word AsanUbsan.M.loaded_segments (0xe0f4c : word) = Some W_e0404.
Proof. vm_refl. Qed.
Lemma D_e0404 : decode_any W_e0404 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0408 : bv 32 := 0x0005c703.
Lemma F_e0408 : fetch_word AsanUbsan.M.loaded_segments (0xe0f50 : word) = Some W_e0408.
Proof. vm_refl. Qed.
Lemma D_e0408 : decode_any W_e0408 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e040c : bv 32 := 0x0015c783.
Lemma F_e040c : fetch_word AsanUbsan.M.loaded_segments (0xe0f54 : word) = Some W_e040c.
Proof. vm_refl. Qed.
Lemma D_e040c : decode_any W_e040c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0410 : bv 32 := 0x0025c803.
Lemma F_e0410 : fetch_word AsanUbsan.M.loaded_segments (0xe0f58 : word) = Some W_e0410.
Proof. vm_refl. Qed.
Lemma D_e0410 : decode_any W_e0410 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0414 : bv 32 := 0x0035c883.
Lemma F_e0414 : fetch_word AsanUbsan.M.loaded_segments (0xe0f5c : word) = Some W_e0414.
Proof. vm_refl. Qed.
Lemma D_e0414 : decode_any W_e0414 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0418 : bv 32 := 0x0045c283.
Lemma F_e0418 : fetch_word AsanUbsan.M.loaded_segments (0xe0f60 : word) = Some W_e0418.
Proof. vm_refl. Qed.
Lemma D_e0418 : decode_any W_e0418 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e041c : bv 32 := 0x0055c303.
Lemma F_e041c : fetch_word AsanUbsan.M.loaded_segments (0xe0f64 : word) = Some W_e041c.
Proof. vm_refl. Qed.
Lemma D_e041c : decode_any W_e041c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0420 : bv 32 := 0x0065c383.
Lemma F_e0420 : fetch_word AsanUbsan.M.loaded_segments (0xe0f68 : word) = Some W_e0420.
Proof. vm_refl. Qed.
Lemma D_e0420 : decode_any W_e0420 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0424 : bv 32 := 0x0075ce03.
Lemma F_e0424 : fetch_word AsanUbsan.M.loaded_segments (0xe0f6c : word) = Some W_e0424.
Proof. vm_refl. Qed.
Lemma D_e0424 : decode_any W_e0424 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0428 : bv 32 := 0x00858593.
Lemma F_e0428 : fetch_word AsanUbsan.M.loaded_segments (0xe0f70 : word) = Some W_e0428.
Proof. vm_refl. Qed.
Lemma D_e0428 : decode_any W_e0428 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e042c : bv 32 := 0x00e68023.
Lemma F_e042c : fetch_word AsanUbsan.M.loaded_segments (0xe0f74 : word) = Some W_e042c.
Proof. vm_refl. Qed.
Lemma D_e042c : decode_any W_e042c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0430 : bv 32 := 0x00f680a3.
Lemma F_e0430 : fetch_word AsanUbsan.M.loaded_segments (0xe0f78 : word) = Some W_e0430.
Proof. vm_refl. Qed.
Lemma D_e0430 : decode_any W_e0430 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0434 : bv 32 := 0x01068123.
Lemma F_e0434 : fetch_word AsanUbsan.M.loaded_segments (0xe0f7c : word) = Some W_e0434.
Proof. vm_refl. Qed.
Lemma D_e0434 : decode_any W_e0434 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0438 : bv 32 := 0x011681a3.
Lemma F_e0438 : fetch_word AsanUbsan.M.loaded_segments (0xe0f80 : word) = Some W_e0438.
Proof. vm_refl. Qed.
Lemma D_e0438 : decode_any W_e0438 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e043c : bv 32 := 0x00868713.
Lemma F_e043c : fetch_word AsanUbsan.M.loaded_segments (0xe0f84 : word) = Some W_e043c.
Proof. vm_refl. Qed.
Lemma D_e043c : decode_any W_e043c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0440 : bv 32 := 0x00568223.
Lemma F_e0440 : fetch_word AsanUbsan.M.loaded_segments (0xe0f88 : word) = Some W_e0440.
Proof. vm_refl. Qed.
Lemma D_e0440 : decode_any W_e0440 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0444 : bv 32 := 0x006682a3.
Lemma F_e0444 : fetch_word AsanUbsan.M.loaded_segments (0xe0f8c : word) = Some W_e0444.
Proof. vm_refl. Qed.
Lemma D_e0444 : decode_any W_e0444 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0448 : bv 32 := 0x00768323.
Lemma F_e0448 : fetch_word AsanUbsan.M.loaded_segments (0xe0f90 : word) = Some W_e0448.
Proof. vm_refl. Qed.
Lemma D_e0448 : decode_any W_e0448 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e044c : bv 32 := 0x01c683a3.
Lemma F_e044c : fetch_word AsanUbsan.M.loaded_segments (0xe0f94 : word) = Some W_e044c.
Proof. vm_refl. Qed.
Lemma D_e044c : decode_any W_e044c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0450 : bv 32 := 0x00070693.
Lemma F_e0450 : fetch_word AsanUbsan.M.loaded_segments (0xe0f98 : word) = Some W_e0450.
Proof. vm_refl. Qed.
Lemma D_e0450 : decode_any W_e0450 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0454 : bv 32 := 0x00467713.
Lemma F_e0454 : fetch_word AsanUbsan.M.loaded_segments (0xe0f9c : word) = Some W_e0454.
Proof. vm_refl. Qed.
Lemma D_e0454 : decode_any W_e0454 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0458 : bv 32 := 0x02070863.
Lemma F_e0458 : fetch_word AsanUbsan.M.loaded_segments (0xe0fa0 : word) = Some W_e0458.
Proof. vm_refl. Qed.
Lemma D_e0458 : decode_any W_e0458 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e045c : bv 32 := 0x0005c703.
Lemma F_e045c : fetch_word AsanUbsan.M.loaded_segments (0xe0fa4 : word) = Some W_e045c.
Proof. vm_refl. Qed.
Lemma D_e045c : decode_any W_e045c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0460 : bv 32 := 0x0015c783.
Lemma F_e0460 : fetch_word AsanUbsan.M.loaded_segments (0xe0fa8 : word) = Some W_e0460.
Proof. vm_refl. Qed.
Lemma D_e0460 : decode_any W_e0460 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0464 : bv 32 := 0x0025c803.
Lemma F_e0464 : fetch_word AsanUbsan.M.loaded_segments (0xe0fac : word) = Some W_e0464.
Proof. vm_refl. Qed.
Lemma D_e0464 : decode_any W_e0464 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0468 : bv 32 := 0x0035c883.
Lemma F_e0468 : fetch_word AsanUbsan.M.loaded_segments (0xe0fb0 : word) = Some W_e0468.
Proof. vm_refl. Qed.
Lemma D_e0468 : decode_any W_e0468 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e046c : bv 32 := 0x00458593.
Lemma F_e046c : fetch_word AsanUbsan.M.loaded_segments (0xe0fb4 : word) = Some W_e046c.
Proof. vm_refl. Qed.
Lemma D_e046c : decode_any W_e046c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0470 : bv 32 := 0x00468293.
Lemma F_e0470 : fetch_word AsanUbsan.M.loaded_segments (0xe0fb8 : word) = Some W_e0470.
Proof. vm_refl. Qed.
Lemma D_e0470 : decode_any W_e0470 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0474 : bv 32 := 0x00e68023.
Lemma F_e0474 : fetch_word AsanUbsan.M.loaded_segments (0xe0fbc : word) = Some W_e0474.
Proof. vm_refl. Qed.
Lemma D_e0474 : decode_any W_e0474 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0478 : bv 32 := 0x00f680a3.
Lemma F_e0478 : fetch_word AsanUbsan.M.loaded_segments (0xe0fc0 : word) = Some W_e0478.
Proof. vm_refl. Qed.
Lemma D_e0478 : decode_any W_e0478 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e047c : bv 32 := 0x01068123.
Lemma F_e047c : fetch_word AsanUbsan.M.loaded_segments (0xe0fc4 : word) = Some W_e047c.
Proof. vm_refl. Qed.
Lemma D_e047c : decode_any W_e047c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0480 : bv 32 := 0x011681a3.
Lemma F_e0480 : fetch_word AsanUbsan.M.loaded_segments (0xe0fc8 : word) = Some W_e0480.
Proof. vm_refl. Qed.
Lemma D_e0480 : decode_any W_e0480 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0484 : bv 32 := 0x00028693.
Lemma F_e0484 : fetch_word AsanUbsan.M.loaded_segments (0xe0fcc : word) = Some W_e0484.
Proof. vm_refl. Qed.
Lemma D_e0484 : decode_any W_e0484 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0488 : bv 32 := 0x00267713.
Lemma F_e0488 : fetch_word AsanUbsan.M.loaded_segments (0xe0fd0 : word) = Some W_e0488.
Proof. vm_refl. Qed.
Lemma D_e0488 : decode_any W_e0488 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e048c : bv 32 := 0x00071863.
Lemma F_e048c : fetch_word AsanUbsan.M.loaded_segments (0xe0fd4 : word) = Some W_e048c.
Proof. vm_refl. Qed.
Lemma D_e048c : decode_any W_e048c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0490 : bv 32 := 0x00167613.
Lemma F_e0490 : fetch_word AsanUbsan.M.loaded_segments (0xe0fd8 : word) = Some W_e0490.
Proof. vm_refl. Qed.
Lemma D_e0490 : decode_any W_e0490 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0494 : bv 32 := 0x02061663.
Lemma F_e0494 : fetch_word AsanUbsan.M.loaded_segments (0xe0fdc : word) = Some W_e0494.
Proof. vm_refl. Qed.
Lemma D_e0494 : decode_any W_e0494 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e0498 : bv 32 := 0x00008067.
Lemma F_e0498 : fetch_word AsanUbsan.M.loaded_segments (0xe0fe0 : word) = Some W_e0498.
Proof. vm_refl. Qed.
Lemma D_e0498 : decode_any W_e0498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e049c : bv 32 := 0x0005c703.
Lemma F_e049c : fetch_word AsanUbsan.M.loaded_segments (0xe0fe4 : word) = Some W_e049c.
Proof. vm_refl. Qed.
Lemma D_e049c : decode_any W_e049c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04a0 : bv 32 := 0x0015c783.
Lemma F_e04a0 : fetch_word AsanUbsan.M.loaded_segments (0xe0fe8 : word) = Some W_e04a0.
Proof. vm_refl. Qed.
Lemma D_e04a0 : decode_any W_e04a0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04a4 : bv 32 := 0x00258593.
Lemma F_e04a4 : fetch_word AsanUbsan.M.loaded_segments (0xe0fec : word) = Some W_e04a4.
Proof. vm_refl. Qed.
Lemma D_e04a4 : decode_any W_e04a4 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04a8 : bv 32 := 0x00268813.
Lemma F_e04a8 : fetch_word AsanUbsan.M.loaded_segments (0xe0ff0 : word) = Some W_e04a8.
Proof. vm_refl. Qed.
Lemma D_e04a8 : decode_any W_e04a8 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04ac : bv 32 := 0x00e68023.
Lemma F_e04ac : fetch_word AsanUbsan.M.loaded_segments (0xe0ff4 : word) = Some W_e04ac.
Proof. vm_refl. Qed.
Lemma D_e04ac : decode_any W_e04ac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04b0 : bv 32 := 0x00f680a3.
Lemma F_e04b0 : fetch_word AsanUbsan.M.loaded_segments (0xe0ff8 : word) = Some W_e04b0.
Proof. vm_refl. Qed.
Lemma D_e04b0 : decode_any W_e04b0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04b4 : bv 32 := 0x00080693.
Lemma F_e04b4 : fetch_word AsanUbsan.M.loaded_segments (0xe0ffc : word) = Some W_e04b4.
Proof. vm_refl. Qed.
Lemma D_e04b4 : decode_any W_e04b4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04b8 : bv 32 := 0x00167613.
Lemma F_e04b8 : fetch_word AsanUbsan.M.loaded_segments (0xe1000 : word) = Some W_e04b8.
Proof. vm_refl. Qed.
Lemma D_e04b8 : decode_any W_e04b8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04bc : bv 32 := 0xfc060ee3.
Lemma F_e04bc : fetch_word AsanUbsan.M.loaded_segments (0xe1004 : word) = Some W_e04bc.
Proof. vm_refl. Qed.
Lemma D_e04bc : decode_any W_e04bc = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04c0 : bv 32 := 0x0005c583.
Lemma F_e04c0 : fetch_word AsanUbsan.M.loaded_segments (0xe1008 : word) = Some W_e04c0.
Proof. vm_refl. Qed.
Lemma D_e04c0 : decode_any W_e04c0 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04c4 : bv 32 := 0x00b68023.
Lemma F_e04c4 : fetch_word AsanUbsan.M.loaded_segments (0xe100c : word) = Some W_e04c4.
Proof. vm_refl. Qed.
Lemma D_e04c4 : decode_any W_e04c4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e04c8 : bv 32 := 0x00008067.
Lemma F_e04c8 : fetch_word AsanUbsan.M.loaded_segments (0xe1010 : word) = Some W_e04c8.
Proof. vm_refl. Qed.
Lemma D_e04c8 : decode_any W_e04c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
