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
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Asan.
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
Definition W_d80f8 : bv 32 := 0x0035f693.
Lemma F_d80f8 : fetch_word Asan.M.loaded_segments (0xd8348 : word) = Some W_d80f8.
Proof. vm_refl. Qed.
Lemma D_d80f8 : decode_any W_d80f8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d80fc : bv 32 := 0x10068863.
Lemma F_d80fc : fetch_word Asan.M.loaded_segments (0xd834c : word) = Some W_d80fc.
Proof. vm_refl. Qed.
Lemma D_d80fc : decode_any W_d80fc = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8100 : bv 32 := 0x02060e63.
Lemma F_d8100 : fetch_word Asan.M.loaded_segments (0xd8350 : word) = Some W_d8100.
Proof. vm_refl. Qed.
Lemma D_d8100 : decode_any W_d8100 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8104 : bv 32 := 0x00158713.
Lemma F_d8104 : fetch_word Asan.M.loaded_segments (0xd8354 : word) = Some W_d8104.
Proof. vm_refl. Qed.
Lemma D_d8104 : decode_any W_d8104 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8108 : bv 32 := 0x00100793.
Lemma F_d8108 : fetch_word Asan.M.loaded_segments (0xd8358 : word) = Some W_d8108.
Proof. vm_refl. Qed.
Lemma D_d8108 : decode_any W_d8108 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d810c : bv 32 := 0x00050693.
Lemma F_d810c : fetch_word Asan.M.loaded_segments (0xd835c : word) = Some W_d810c.
Proof. vm_refl. Qed.
Lemma D_d810c : decode_any W_d810c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8110 : bv 32 := 0x0005c883.
Lemma F_d8110 : fetch_word Asan.M.loaded_segments (0xd8360 : word) = Some W_d8110.
Proof. vm_refl. Qed.
Lemma D_d8110 : decode_any W_d8110 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8114 : bv 32 := 0x00060813.
Lemma F_d8114 : fetch_word Asan.M.loaded_segments (0xd8364 : word) = Some W_d8114.
Proof. vm_refl. Qed.
Lemma D_d8114 : decode_any W_d8114 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8118 : bv 32 := 0x00158593.
Lemma F_d8118 : fetch_word Asan.M.loaded_segments (0xd8368 : word) = Some W_d8118.
Proof. vm_refl. Qed.
Lemma D_d8118 : decode_any W_d8118 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d811c : bv 32 := 0x00377293.
Lemma F_d811c : fetch_word Asan.M.loaded_segments (0xd836c : word) = Some W_d811c.
Proof. vm_refl. Qed.
Lemma D_d811c : decode_any W_d811c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8120 : bv 32 := 0x01168023.
Lemma F_d8120 : fetch_word Asan.M.loaded_segments (0xd8370 : word) = Some W_d8120.
Proof. vm_refl. Qed.
Lemma D_d8120 : decode_any W_d8120 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8124 : bv 32 := 0x00168693.
Lemma F_d8124 : fetch_word Asan.M.loaded_segments (0xd8374 : word) = Some W_d8124.
Proof. vm_refl. Qed.
Lemma D_d8124 : decode_any W_d8124 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8128 : bv 32 := 0xfff60613.
Lemma F_d8128 : fetch_word Asan.M.loaded_segments (0xd8378 : word) = Some W_d8128.
Proof. vm_refl. Qed.
Lemma D_d8128 : decode_any W_d8128 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d812c : bv 32 := 0x00028a63.
Lemma F_d812c : fetch_word Asan.M.loaded_segments (0xd837c : word) = Some W_d812c.
Proof. vm_refl. Qed.
Lemma D_d812c : decode_any W_d812c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8130 : bv 32 := 0x00170713.
Lemma F_d8130 : fetch_word Asan.M.loaded_segments (0xd8380 : word) = Some W_d8130.
Proof. vm_refl. Qed.
Lemma D_d8130 : decode_any W_d8130 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8134 : bv 32 := 0xfcf81ee3.
Lemma F_d8134 : fetch_word Asan.M.loaded_segments (0xd8384 : word) = Some W_d8134.
Proof. vm_refl. Qed.
Lemma D_d8134 : decode_any W_d8134 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8138 : bv 32 := 0x0080006f.
Lemma F_d8138 : fetch_word Asan.M.loaded_segments (0xd8388 : word) = Some W_d8138.
Proof. vm_refl. Qed.
Lemma D_d8138 : decode_any W_d8138 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d813c : bv 32 := 0x00050693.
Lemma F_d813c : fetch_word Asan.M.loaded_segments (0xd838c : word) = Some W_d813c.
Proof. vm_refl. Qed.
Lemma D_d813c : decode_any W_d813c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8140 : bv 32 := 0x0036f793.
Lemma F_d8140 : fetch_word Asan.M.loaded_segments (0xd8390 : word) = Some W_d8140.
Proof. vm_refl. Qed.
Lemma D_d8140 : decode_any W_d8140 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8144 : bv 32 := 0x0c078a63.
Lemma F_d8144 : fetch_word Asan.M.loaded_segments (0xd8394 : word) = Some W_d8144.
Proof. vm_refl. Qed.
Lemma D_d8144 : decode_any W_d8144 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8148 : bv 32 := 0x02000713.
Lemma F_d8148 : fetch_word Asan.M.loaded_segments (0xd8398 : word) = Some W_d8148.
Proof. vm_refl. Qed.
Lemma D_d8148 : decode_any W_d8148 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d814c : bv 32 := 0x02e67063.
Lemma F_d814c : fetch_word Asan.M.loaded_segments (0xd839c : word) = Some W_d814c.
Proof. vm_refl. Qed.
Lemma D_d814c : decode_any W_d814c = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8150 : bv 32 := 0x01000713.
Lemma F_d8150 : fetch_word Asan.M.loaded_segments (0xd83a0 : word) = Some W_d8150.
Proof. vm_refl. Qed.
Lemma D_d8150 : decode_any W_d8150 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8154 : bv 32 := 0x24e67863.
Lemma F_d8154 : fetch_word Asan.M.loaded_segments (0xd83a4 : word) = Some W_d8154.
Proof. vm_refl. Qed.
Lemma D_d8154 : decode_any W_d8154 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8158 : bv 32 := 0x00867713.
Lemma F_d8158 : fetch_word Asan.M.loaded_segments (0xd83a8 : word) = Some W_d8158.
Proof. vm_refl. Qed.
Lemma D_d8158 : decode_any W_d8158 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d815c : bv 32 := 0x2c071e63.
Lemma F_d815c : fetch_word Asan.M.loaded_segments (0xd83ac : word) = Some W_d815c.
Proof. vm_refl. Qed.
Lemma D_d815c : decode_any W_d815c = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8160 : bv 32 := 0x00467713.
Lemma F_d8160 : fetch_word Asan.M.loaded_segments (0xd83b0 : word) = Some W_d8160.
Proof. vm_refl. Qed.
Lemma D_d8160 : decode_any W_d8160 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8164 : bv 32 := 0x32071463.
Lemma F_d8164 : fetch_word Asan.M.loaded_segments (0xd83b4 : word) = Some W_d8164.
Proof. vm_refl. Qed.
Lemma D_d8164 : decode_any W_d8164 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8168 : bv 32 := 0x3500006f.
Lemma F_d8168 : fetch_word Asan.M.loaded_segments (0xd83b8 : word) = Some W_d8168.
Proof. vm_refl. Qed.
Lemma D_d8168 : decode_any W_d8168 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d816c : bv 32 := 0x0005a703.
Lemma F_d816c : fetch_word Asan.M.loaded_segments (0xd83bc : word) = Some W_d816c.
Proof. vm_refl. Qed.
Lemma D_d816c : decode_any W_d816c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8170 : bv 32 := 0x00300813.
Lemma F_d8170 : fetch_word Asan.M.loaded_segments (0xd83c0 : word) = Some W_d8170.
Proof. vm_refl. Qed.
Lemma D_d8170 : decode_any W_d8170 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8174 : bv 32 := 0x11078e63.
Lemma F_d8174 : fetch_word Asan.M.loaded_segments (0xd83c4 : word) = Some W_d8174.
Proof. vm_refl. Qed.
Lemma D_d8174 : decode_any W_d8174 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8178 : bv 32 := 0x00200813.
Lemma F_d8178 : fetch_word Asan.M.loaded_segments (0xd83c8 : word) = Some W_d8178.
Proof. vm_refl. Qed.
Lemma D_d8178 : decode_any W_d8178 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d817c : bv 32 := 0x19079c63.
Lemma F_d817c : fetch_word Asan.M.loaded_segments (0xd83cc : word) = Some W_d817c.
Proof. vm_refl. Qed.
Lemma D_d817c : decode_any W_d817c = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8180 : bv 32 := 0x00875793.
Lemma F_d8180 : fetch_word Asan.M.loaded_segments (0xd83d0 : word) = Some W_d8180.
Proof. vm_refl. Qed.
Lemma D_d8180 : decode_any W_d8180 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8184 : bv 32 := 0xffe60613.
Lemma F_d8184 : fetch_word Asan.M.loaded_segments (0xd83d4 : word) = Some W_d8184.
Proof. vm_refl. Qed.
Lemma D_d8184 : decode_any W_d8184 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8188 : bv 32 := 0x00e68023.
Lemma F_d8188 : fetch_word Asan.M.loaded_segments (0xd83d8 : word) = Some W_d8188.
Proof. vm_refl. Qed.
Lemma D_d8188 : decode_any W_d8188 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d818c : bv 32 := 0x00f680a3.
Lemma F_d818c : fetch_word Asan.M.loaded_segments (0xd83dc : word) = Some W_d818c.
Proof. vm_refl. Qed.
Lemma D_d818c : decode_any W_d818c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8190 : bv 32 := 0x00268693.
Lemma F_d8190 : fetch_word Asan.M.loaded_segments (0xd83e0 : word) = Some W_d8190.
Proof. vm_refl. Qed.
Lemma D_d8190 : decode_any W_d8190 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8194 : bv 32 := 0x01058593.
Lemma F_d8194 : fetch_word Asan.M.loaded_segments (0xd83e4 : word) = Some W_d8194.
Proof. vm_refl. Qed.
Lemma D_d8194 : decode_any W_d8194 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8198 : bv 32 := 0x01100793.
Lemma F_d8198 : fetch_word Asan.M.loaded_segments (0xd83e8 : word) = Some W_d8198.
Proof. vm_refl. Qed.
Lemma D_d8198 : decode_any W_d8198 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d819c : bv 32 := 0x0107581b.
Lemma F_d819c : fetch_word Asan.M.loaded_segments (0xd83ec : word) = Some W_d819c.
Proof. vm_refl. Qed.
Lemma D_d819c : decode_any W_d819c = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81a0 : bv 32 := 0xff45a883.
Lemma F_d81a0 : fetch_word Asan.M.loaded_segments (0xd83f0 : word) = Some W_d81a0.
Proof. vm_refl. Qed.
Lemma D_d81a0 : decode_any W_d81a0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81a4 : bv 32 := 0xff85a283.
Lemma F_d81a4 : fetch_word Asan.M.loaded_segments (0xd83f4 : word) = Some W_d81a4.
Proof. vm_refl. Qed.
Lemma D_d81a4 : decode_any W_d81a4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81a8 : bv 32 := 0xffc5a303.
Lemma F_d81a8 : fetch_word Asan.M.loaded_segments (0xd83f8 : word) = Some W_d81a8.
Proof. vm_refl. Qed.
Lemma D_d81a8 : decode_any W_d81a8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81ac : bv 32 := 0x0005a703.
Lemma F_d81ac : fetch_word Asan.M.loaded_segments (0xd83fc : word) = Some W_d81ac.
Proof. vm_refl. Qed.
Lemma D_d81ac : decode_any W_d81ac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81b0 : bv 32 := 0x01089393.
Lemma F_d81b0 : fetch_word Asan.M.loaded_segments (0xd8400 : word) = Some W_d81b0.
Proof. vm_refl. Qed.
Lemma D_d81b0 : decode_any W_d81b0 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81b4 : bv 32 := 0x0108d89b.
Lemma F_d81b4 : fetch_word Asan.M.loaded_segments (0xd8404 : word) = Some W_d81b4.
Proof. vm_refl. Qed.
Lemma D_d81b4 : decode_any W_d81b4 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81b8 : bv 32 := 0x0103e833.
Lemma F_d81b8 : fetch_word Asan.M.loaded_segments (0xd8408 : word) = Some W_d81b8.
Proof. vm_refl. Qed.
Lemma D_d81b8 : decode_any W_d81b8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81bc : bv 32 := 0x01029393.
Lemma F_d81bc : fetch_word Asan.M.loaded_segments (0xd840c : word) = Some W_d81bc.
Proof. vm_refl. Qed.
Lemma D_d81bc : decode_any W_d81bc = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81c0 : bv 32 := 0x0102d29b.
Lemma F_d81c0 : fetch_word Asan.M.loaded_segments (0xd8410 : word) = Some W_d81c0.
Proof. vm_refl. Qed.
Lemma D_d81c0 : decode_any W_d81c0 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81c4 : bv 32 := 0x0113e8b3.
Lemma F_d81c4 : fetch_word Asan.M.loaded_segments (0xd8414 : word) = Some W_d81c4.
Proof. vm_refl. Qed.
Lemma D_d81c4 : decode_any W_d81c4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81c8 : bv 32 := 0x01031393.
Lemma F_d81c8 : fetch_word Asan.M.loaded_segments (0xd8418 : word) = Some W_d81c8.
Proof. vm_refl. Qed.
Lemma D_d81c8 : decode_any W_d81c8 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81cc : bv 32 := 0x0103531b.
Lemma F_d81cc : fetch_word Asan.M.loaded_segments (0xd841c : word) = Some W_d81cc.
Proof. vm_refl. Qed.
Lemma D_d81cc : decode_any W_d81cc = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81d0 : bv 32 := 0x0053e2b3.
Lemma F_d81d0 : fetch_word Asan.M.loaded_segments (0xd8420 : word) = Some W_d81d0.
Proof. vm_refl. Qed.
Lemma D_d81d0 : decode_any W_d81d0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81d4 : bv 32 := 0x01071393.
Lemma F_d81d4 : fetch_word Asan.M.loaded_segments (0xd8424 : word) = Some W_d81d4.
Proof. vm_refl. Qed.
Lemma D_d81d4 : decode_any W_d81d4 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81d8 : bv 32 := 0x0063e333.
Lemma F_d81d8 : fetch_word Asan.M.loaded_segments (0xd8428 : word) = Some W_d81d8.
Proof. vm_refl. Qed.
Lemma D_d81d8 : decode_any W_d81d8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81dc : bv 32 := 0xff060613.
Lemma F_d81dc : fetch_word Asan.M.loaded_segments (0xd842c : word) = Some W_d81dc.
Proof. vm_refl. Qed.
Lemma D_d81dc : decode_any W_d81dc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81e0 : bv 32 := 0x0106a023.
Lemma F_d81e0 : fetch_word Asan.M.loaded_segments (0xd8430 : word) = Some W_d81e0.
Proof. vm_refl. Qed.
Lemma D_d81e0 : decode_any W_d81e0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81e4 : bv 32 := 0x0116a223.
Lemma F_d81e4 : fetch_word Asan.M.loaded_segments (0xd8434 : word) = Some W_d81e4.
Proof. vm_refl. Qed.
Lemma D_d81e4 : decode_any W_d81e4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81e8 : bv 32 := 0x0056a423.
Lemma F_d81e8 : fetch_word Asan.M.loaded_segments (0xd8438 : word) = Some W_d81e8.
Proof. vm_refl. Qed.
Lemma D_d81e8 : decode_any W_d81e8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81ec : bv 32 := 0x0066a623.
Lemma F_d81ec : fetch_word Asan.M.loaded_segments (0xd843c : word) = Some W_d81ec.
Proof. vm_refl. Qed.
Lemma D_d81ec : decode_any W_d81ec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81f0 : bv 32 := 0x01068693.
Lemma F_d81f0 : fetch_word Asan.M.loaded_segments (0xd8440 : word) = Some W_d81f0.
Proof. vm_refl. Qed.
Lemma D_d81f0 : decode_any W_d81f0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81f4 : bv 32 := 0x01058593.
Lemma F_d81f4 : fetch_word Asan.M.loaded_segments (0xd8444 : word) = Some W_d81f4.
Proof. vm_refl. Qed.
Lemma D_d81f4 : decode_any W_d81f4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81f8 : bv 32 := 0xfac7e2e3.
Lemma F_d81f8 : fetch_word Asan.M.loaded_segments (0xd8448 : word) = Some W_d81f8.
Proof. vm_refl. Qed.
Lemma D_d81f8 : decode_any W_d81f8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d81fc : bv 32 := 0xff258593.
Lemma F_d81fc : fetch_word Asan.M.loaded_segments (0xd844c : word) = Some W_d81fc.
Proof. vm_refl. Qed.
Lemma D_d81fc : decode_any W_d81fc = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8200 : bv 32 := 0x01000713.
Lemma F_d8200 : fetch_word Asan.M.loaded_segments (0xd8450 : word) = Some W_d8200.
Proof. vm_refl. Qed.
Lemma D_d8200 : decode_any W_d8200 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8204 : bv 32 := 0xf4e66ae3.
Lemma F_d8204 : fetch_word Asan.M.loaded_segments (0xd8454 : word) = Some W_d8204.
Proof. vm_refl. Qed.
Lemma D_d8204 : decode_any W_d8204 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8208 : bv 32 := 0x19c0006f.
Lemma F_d8208 : fetch_word Asan.M.loaded_segments (0xd8458 : word) = Some W_d8208.
Proof. vm_refl. Qed.
Lemma D_d8208 : decode_any W_d8208 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d820c : bv 32 := 0x00050693.
Lemma F_d820c : fetch_word Asan.M.loaded_segments (0xd845c : word) = Some W_d820c.
Proof. vm_refl. Qed.
Lemma D_d820c : decode_any W_d820c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8210 : bv 32 := 0x00357793.
Lemma F_d8210 : fetch_word Asan.M.loaded_segments (0xd8460 : word) = Some W_d8210.
Proof. vm_refl. Qed.
Lemma D_d8210 : decode_any W_d8210 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8214 : bv 32 := 0xf2079ae3.
Lemma F_d8214 : fetch_word Asan.M.loaded_segments (0xd8464 : word) = Some W_d8214.
Proof. vm_refl. Qed.
Lemma D_d8214 : decode_any W_d8214 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8218 : bv 32 := 0x01000713.
Lemma F_d8218 : fetch_word Asan.M.loaded_segments (0xd8468 : word) = Some W_d8218.
Proof. vm_refl. Qed.
Lemma D_d8218 : decode_any W_d8218 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d821c : bv 32 := 0x02e66c63.
Lemma F_d821c : fetch_word Asan.M.loaded_segments (0xd846c : word) = Some W_d821c.
Proof. vm_refl. Qed.
Lemma D_d821c : decode_any W_d821c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8220 : bv 32 := 0x00f00713.
Lemma F_d8220 : fetch_word Asan.M.loaded_segments (0xd8470 : word) = Some W_d8220.
Proof. vm_refl. Qed.
Lemma D_d8220 : decode_any W_d8220 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8224 : bv 32 := 0x0005a783.
Lemma F_d8224 : fetch_word Asan.M.loaded_segments (0xd8474 : word) = Some W_d8224.
Proof. vm_refl. Qed.
Lemma D_d8224 : decode_any W_d8224 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8228 : bv 32 := 0x0045a803.
Lemma F_d8228 : fetch_word Asan.M.loaded_segments (0xd8478 : word) = Some W_d8228.
Proof. vm_refl. Qed.
Lemma D_d8228 : decode_any W_d8228 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d822c : bv 32 := 0x0085a883.
Lemma F_d822c : fetch_word Asan.M.loaded_segments (0xd847c : word) = Some W_d822c.
Proof. vm_refl. Qed.
Lemma D_d822c : decode_any W_d822c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8230 : bv 32 := 0x00c5a283.
Lemma F_d8230 : fetch_word Asan.M.loaded_segments (0xd8480 : word) = Some W_d8230.
Proof. vm_refl. Qed.
Lemma D_d8230 : decode_any W_d8230 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8234 : bv 32 := 0x01058593.
Lemma F_d8234 : fetch_word Asan.M.loaded_segments (0xd8484 : word) = Some W_d8234.
Proof. vm_refl. Qed.
Lemma D_d8234 : decode_any W_d8234 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8238 : bv 32 := 0xff060613.
Lemma F_d8238 : fetch_word Asan.M.loaded_segments (0xd8488 : word) = Some W_d8238.
Proof. vm_refl. Qed.
Lemma D_d8238 : decode_any W_d8238 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d823c : bv 32 := 0x00f6a023.
Lemma F_d823c : fetch_word Asan.M.loaded_segments (0xd848c : word) = Some W_d823c.
Proof. vm_refl. Qed.
Lemma D_d823c : decode_any W_d823c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8240 : bv 32 := 0x0106a223.
Lemma F_d8240 : fetch_word Asan.M.loaded_segments (0xd8490 : word) = Some W_d8240.
Proof. vm_refl. Qed.
Lemma D_d8240 : decode_any W_d8240 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8244 : bv 32 := 0x0116a423.
Lemma F_d8244 : fetch_word Asan.M.loaded_segments (0xd8494 : word) = Some W_d8244.
Proof. vm_refl. Qed.
Lemma D_d8244 : decode_any W_d8244 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8248 : bv 32 := 0x0056a623.
Lemma F_d8248 : fetch_word Asan.M.loaded_segments (0xd8498 : word) = Some W_d8248.
Proof. vm_refl. Qed.
Lemma D_d8248 : decode_any W_d8248 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d824c : bv 32 := 0x01068693.
Lemma F_d824c : fetch_word Asan.M.loaded_segments (0xd849c : word) = Some W_d824c.
Proof. vm_refl. Qed.
Lemma D_d824c : decode_any W_d824c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8250 : bv 32 := 0xfcc76ae3.
Lemma F_d8250 : fetch_word Asan.M.loaded_segments (0xd84a0 : word) = Some W_d8250.
Proof. vm_refl. Qed.
Lemma D_d8250 : decode_any W_d8250 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8254 : bv 32 := 0x00800713.
Lemma F_d8254 : fetch_word Asan.M.loaded_segments (0xd84a4 : word) = Some W_d8254.
Proof. vm_refl. Qed.
Lemma D_d8254 : decode_any W_d8254 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8258 : bv 32 := 0x00e66e63.
Lemma F_d8258 : fetch_word Asan.M.loaded_segments (0xd84a8 : word) = Some W_d8258.
Proof. vm_refl. Qed.
Lemma D_d8258 : decode_any W_d8258 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d825c : bv 32 := 0x0005a703.
Lemma F_d825c : fetch_word Asan.M.loaded_segments (0xd84ac : word) = Some W_d825c.
Proof. vm_refl. Qed.
Lemma D_d825c : decode_any W_d825c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8260 : bv 32 := 0x0045a783.
Lemma F_d8260 : fetch_word Asan.M.loaded_segments (0xd84b0 : word) = Some W_d8260.
Proof. vm_refl. Qed.
Lemma D_d8260 : decode_any W_d8260 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8264 : bv 32 := 0x00e6a023.
Lemma F_d8264 : fetch_word Asan.M.loaded_segments (0xd84b4 : word) = Some W_d8264.
Proof. vm_refl. Qed.
Lemma D_d8264 : decode_any W_d8264 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8268 : bv 32 := 0x00f6a223.
Lemma F_d8268 : fetch_word Asan.M.loaded_segments (0xd84b8 : word) = Some W_d8268.
Proof. vm_refl. Qed.
Lemma D_d8268 : decode_any W_d8268 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d826c : bv 32 := 0x00868693.
Lemma F_d826c : fetch_word Asan.M.loaded_segments (0xd84bc : word) = Some W_d826c.
Proof. vm_refl. Qed.
Lemma D_d826c : decode_any W_d826c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8270 : bv 32 := 0x00858593.
Lemma F_d8270 : fetch_word Asan.M.loaded_segments (0xd84c0 : word) = Some W_d8270.
Proof. vm_refl. Qed.
Lemma D_d8270 : decode_any W_d8270 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8274 : bv 32 := 0x00467713.
Lemma F_d8274 : fetch_word Asan.M.loaded_segments (0xd84c4 : word) = Some W_d8274.
Proof. vm_refl. Qed.
Lemma D_d8274 : decode_any W_d8274 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8278 : bv 32 := 0x24070063.
Lemma F_d8278 : fetch_word Asan.M.loaded_segments (0xd84c8 : word) = Some W_d8278.
Proof. vm_refl. Qed.
Lemma D_d8278 : decode_any W_d8278 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d827c : bv 32 := 0x0005a703.
Lemma F_d827c : fetch_word Asan.M.loaded_segments (0xd84cc : word) = Some W_d827c.
Proof. vm_refl. Qed.
Lemma D_d827c : decode_any W_d827c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8280 : bv 32 := 0x00458593.
Lemma F_d8280 : fetch_word Asan.M.loaded_segments (0xd84d0 : word) = Some W_d8280.
Proof. vm_refl. Qed.
Lemma D_d8280 : decode_any W_d8280 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8284 : bv 32 := 0x00e6a023.
Lemma F_d8284 : fetch_word Asan.M.loaded_segments (0xd84d4 : word) = Some W_d8284.
Proof. vm_refl. Qed.
Lemma D_d8284 : decode_any W_d8284 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8288 : bv 32 := 0x00468693.
Lemma F_d8288 : fetch_word Asan.M.loaded_segments (0xd84d8 : word) = Some W_d8288.
Proof. vm_refl. Qed.
Lemma D_d8288 : decode_any W_d8288 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d828c : bv 32 := 0x22c0006f.
Lemma F_d828c : fetch_word Asan.M.loaded_segments (0xd84dc : word) = Some W_d828c.
Proof. vm_refl. Qed.
Lemma D_d828c : decode_any W_d828c = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8290 : bv 32 := 0x00e68023.
Lemma F_d8290 : fetch_word Asan.M.loaded_segments (0xd84e0 : word) = Some W_d8290.
Proof. vm_refl. Qed.
Lemma D_d8290 : decode_any W_d8290 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8294 : bv 32 := 0x00168693.
Lemma F_d8294 : fetch_word Asan.M.loaded_segments (0xd84e4 : word) = Some W_d8294.
Proof. vm_refl. Qed.
Lemma D_d8294 : decode_any W_d8294 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8298 : bv 32 := 0xfff60613.
Lemma F_d8298 : fetch_word Asan.M.loaded_segments (0xd84e8 : word) = Some W_d8298.
Proof. vm_refl. Qed.
Lemma D_d8298 : decode_any W_d8298 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d829c : bv 32 := 0x01058593.
Lemma F_d829c : fetch_word Asan.M.loaded_segments (0xd84ec : word) = Some W_d829c.
Proof. vm_refl. Qed.
Lemma D_d829c : decode_any W_d829c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82a0 : bv 32 := 0x01200793.
Lemma F_d82a0 : fetch_word Asan.M.loaded_segments (0xd84f0 : word) = Some W_d82a0.
Proof. vm_refl. Qed.
Lemma D_d82a0 : decode_any W_d82a0 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82a4 : bv 32 := 0x0087581b.
Lemma F_d82a4 : fetch_word Asan.M.loaded_segments (0xd84f4 : word) = Some W_d82a4.
Proof. vm_refl. Qed.
Lemma D_d82a4 : decode_any W_d82a4 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82a8 : bv 32 := 0xff45a883.
Lemma F_d82a8 : fetch_word Asan.M.loaded_segments (0xd84f8 : word) = Some W_d82a8.
Proof. vm_refl. Qed.
Lemma D_d82a8 : decode_any W_d82a8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82ac : bv 32 := 0xff85a283.
Lemma F_d82ac : fetch_word Asan.M.loaded_segments (0xd84fc : word) = Some W_d82ac.
Proof. vm_refl. Qed.
Lemma D_d82ac : decode_any W_d82ac = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82b0 : bv 32 := 0xffc5a303.
Lemma F_d82b0 : fetch_word Asan.M.loaded_segments (0xd8500 : word) = Some W_d82b0.
Proof. vm_refl. Qed.
Lemma D_d82b0 : decode_any W_d82b0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82b4 : bv 32 := 0x0005a703.
Lemma F_d82b4 : fetch_word Asan.M.loaded_segments (0xd8504 : word) = Some W_d82b4.
Proof. vm_refl. Qed.
Lemma D_d82b4 : decode_any W_d82b4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82b8 : bv 32 := 0x01889393.
Lemma F_d82b8 : fetch_word Asan.M.loaded_segments (0xd8508 : word) = Some W_d82b8.
Proof. vm_refl. Qed.
Lemma D_d82b8 : decode_any W_d82b8 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82bc : bv 32 := 0x0088d89b.
Lemma F_d82bc : fetch_word Asan.M.loaded_segments (0xd850c : word) = Some W_d82bc.
Proof. vm_refl. Qed.
Lemma D_d82bc : decode_any W_d82bc = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82c0 : bv 32 := 0x0103e833.
Lemma F_d82c0 : fetch_word Asan.M.loaded_segments (0xd8510 : word) = Some W_d82c0.
Proof. vm_refl. Qed.
Lemma D_d82c0 : decode_any W_d82c0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82c4 : bv 32 := 0x01829393.
Lemma F_d82c4 : fetch_word Asan.M.loaded_segments (0xd8514 : word) = Some W_d82c4.
Proof. vm_refl. Qed.
Lemma D_d82c4 : decode_any W_d82c4 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82c8 : bv 32 := 0x0082d29b.
Lemma F_d82c8 : fetch_word Asan.M.loaded_segments (0xd8518 : word) = Some W_d82c8.
Proof. vm_refl. Qed.
Lemma D_d82c8 : decode_any W_d82c8 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82cc : bv 32 := 0x0113e8b3.
Lemma F_d82cc : fetch_word Asan.M.loaded_segments (0xd851c : word) = Some W_d82cc.
Proof. vm_refl. Qed.
Lemma D_d82cc : decode_any W_d82cc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82d0 : bv 32 := 0x01831393.
Lemma F_d82d0 : fetch_word Asan.M.loaded_segments (0xd8520 : word) = Some W_d82d0.
Proof. vm_refl. Qed.
Lemma D_d82d0 : decode_any W_d82d0 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82d4 : bv 32 := 0x0083531b.
Lemma F_d82d4 : fetch_word Asan.M.loaded_segments (0xd8524 : word) = Some W_d82d4.
Proof. vm_refl. Qed.
Lemma D_d82d4 : decode_any W_d82d4 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82d8 : bv 32 := 0x0053e2b3.
Lemma F_d82d8 : fetch_word Asan.M.loaded_segments (0xd8528 : word) = Some W_d82d8.
Proof. vm_refl. Qed.
Lemma D_d82d8 : decode_any W_d82d8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82dc : bv 32 := 0x01871393.
Lemma F_d82dc : fetch_word Asan.M.loaded_segments (0xd852c : word) = Some W_d82dc.
Proof. vm_refl. Qed.
Lemma D_d82dc : decode_any W_d82dc = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82e0 : bv 32 := 0x0063e333.
Lemma F_d82e0 : fetch_word Asan.M.loaded_segments (0xd8530 : word) = Some W_d82e0.
Proof. vm_refl. Qed.
Lemma D_d82e0 : decode_any W_d82e0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82e4 : bv 32 := 0xff060613.
Lemma F_d82e4 : fetch_word Asan.M.loaded_segments (0xd8534 : word) = Some W_d82e4.
Proof. vm_refl. Qed.
Lemma D_d82e4 : decode_any W_d82e4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82e8 : bv 32 := 0x0106a023.
Lemma F_d82e8 : fetch_word Asan.M.loaded_segments (0xd8538 : word) = Some W_d82e8.
Proof. vm_refl. Qed.
Lemma D_d82e8 : decode_any W_d82e8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82ec : bv 32 := 0x0116a223.
Lemma F_d82ec : fetch_word Asan.M.loaded_segments (0xd853c : word) = Some W_d82ec.
Proof. vm_refl. Qed.
Lemma D_d82ec : decode_any W_d82ec = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82f0 : bv 32 := 0x0056a423.
Lemma F_d82f0 : fetch_word Asan.M.loaded_segments (0xd8540 : word) = Some W_d82f0.
Proof. vm_refl. Qed.
Lemma D_d82f0 : decode_any W_d82f0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82f4 : bv 32 := 0x0066a623.
Lemma F_d82f4 : fetch_word Asan.M.loaded_segments (0xd8544 : word) = Some W_d82f4.
Proof. vm_refl. Qed.
Lemma D_d82f4 : decode_any W_d82f4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82f8 : bv 32 := 0x01068693.
Lemma F_d82f8 : fetch_word Asan.M.loaded_segments (0xd8548 : word) = Some W_d82f8.
Proof. vm_refl. Qed.
Lemma D_d82f8 : decode_any W_d82f8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d82fc : bv 32 := 0x01058593.
Lemma F_d82fc : fetch_word Asan.M.loaded_segments (0xd854c : word) = Some W_d82fc.
Proof. vm_refl. Qed.
Lemma D_d82fc : decode_any W_d82fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8300 : bv 32 := 0xfac7e2e3.
Lemma F_d8300 : fetch_word Asan.M.loaded_segments (0xd8550 : word) = Some W_d8300.
Proof. vm_refl. Qed.
Lemma D_d8300 : decode_any W_d8300 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8304 : bv 32 := 0xff158593.
Lemma F_d8304 : fetch_word Asan.M.loaded_segments (0xd8554 : word) = Some W_d8304.
Proof. vm_refl. Qed.
Lemma D_d8304 : decode_any W_d8304 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8308 : bv 32 := 0x01000713.
Lemma F_d8308 : fetch_word Asan.M.loaded_segments (0xd8558 : word) = Some W_d8308.
Proof. vm_refl. Qed.
Lemma D_d8308 : decode_any W_d8308 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d830c : bv 32 := 0xe4e666e3.
Lemma F_d830c : fetch_word Asan.M.loaded_segments (0xd855c : word) = Some W_d830c.
Proof. vm_refl. Qed.
Lemma D_d830c : decode_any W_d830c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8310 : bv 32 := 0x0940006f.
Lemma F_d8310 : fetch_word Asan.M.loaded_segments (0xd8560 : word) = Some W_d8310.
Proof. vm_refl. Qed.
Lemma D_d8310 : decode_any W_d8310 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8314 : bv 32 := 0x00875793.
Lemma F_d8314 : fetch_word Asan.M.loaded_segments (0xd8564 : word) = Some W_d8314.
Proof. vm_refl. Qed.
Lemma D_d8314 : decode_any W_d8314 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8318 : bv 32 := 0x01075813.
Lemma F_d8318 : fetch_word Asan.M.loaded_segments (0xd8568 : word) = Some W_d8318.
Proof. vm_refl. Qed.
Lemma D_d8318 : decode_any W_d8318 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d831c : bv 32 := 0xffd60613.
Lemma F_d831c : fetch_word Asan.M.loaded_segments (0xd856c : word) = Some W_d831c.
Proof. vm_refl. Qed.
Lemma D_d831c : decode_any W_d831c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8320 : bv 32 := 0x00e68023.
Lemma F_d8320 : fetch_word Asan.M.loaded_segments (0xd8570 : word) = Some W_d8320.
Proof. vm_refl. Qed.
Lemma D_d8320 : decode_any W_d8320 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8324 : bv 32 := 0x00f680a3.
Lemma F_d8324 : fetch_word Asan.M.loaded_segments (0xd8574 : word) = Some W_d8324.
Proof. vm_refl. Qed.
Lemma D_d8324 : decode_any W_d8324 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8328 : bv 32 := 0x01068123.
Lemma F_d8328 : fetch_word Asan.M.loaded_segments (0xd8578 : word) = Some W_d8328.
Proof. vm_refl. Qed.
Lemma D_d8328 : decode_any W_d8328 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d832c : bv 32 := 0x00368693.
Lemma F_d832c : fetch_word Asan.M.loaded_segments (0xd857c : word) = Some W_d832c.
Proof. vm_refl. Qed.
Lemma D_d832c : decode_any W_d832c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8330 : bv 32 := 0x01058593.
Lemma F_d8330 : fetch_word Asan.M.loaded_segments (0xd8580 : word) = Some W_d8330.
Proof. vm_refl. Qed.
Lemma D_d8330 : decode_any W_d8330 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8334 : bv 32 := 0x01000793.
Lemma F_d8334 : fetch_word Asan.M.loaded_segments (0xd8584 : word) = Some W_d8334.
Proof. vm_refl. Qed.
Lemma D_d8334 : decode_any W_d8334 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8338 : bv 32 := 0x0187581b.
Lemma F_d8338 : fetch_word Asan.M.loaded_segments (0xd8588 : word) = Some W_d8338.
Proof. vm_refl. Qed.
Lemma D_d8338 : decode_any W_d8338 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d833c : bv 32 := 0xff45a883.
Lemma F_d833c : fetch_word Asan.M.loaded_segments (0xd858c : word) = Some W_d833c.
Proof. vm_refl. Qed.
Lemma D_d833c : decode_any W_d833c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8340 : bv 32 := 0xff85a283.
Lemma F_d8340 : fetch_word Asan.M.loaded_segments (0xd8590 : word) = Some W_d8340.
Proof. vm_refl. Qed.
Lemma D_d8340 : decode_any W_d8340 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8344 : bv 32 := 0xffc5a303.
Lemma F_d8344 : fetch_word Asan.M.loaded_segments (0xd8594 : word) = Some W_d8344.
Proof. vm_refl. Qed.
Lemma D_d8344 : decode_any W_d8344 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8348 : bv 32 := 0x0005a703.
Lemma F_d8348 : fetch_word Asan.M.loaded_segments (0xd8598 : word) = Some W_d8348.
Proof. vm_refl. Qed.
Lemma D_d8348 : decode_any W_d8348 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d834c : bv 32 := 0x00889393.
Lemma F_d834c : fetch_word Asan.M.loaded_segments (0xd859c : word) = Some W_d834c.
Proof. vm_refl. Qed.
Lemma D_d834c : decode_any W_d834c = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8350 : bv 32 := 0x0188d89b.
Lemma F_d8350 : fetch_word Asan.M.loaded_segments (0xd85a0 : word) = Some W_d8350.
Proof. vm_refl. Qed.
Lemma D_d8350 : decode_any W_d8350 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8354 : bv 32 := 0x0103e833.
Lemma F_d8354 : fetch_word Asan.M.loaded_segments (0xd85a4 : word) = Some W_d8354.
Proof. vm_refl. Qed.
Lemma D_d8354 : decode_any W_d8354 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8358 : bv 32 := 0x00829393.
Lemma F_d8358 : fetch_word Asan.M.loaded_segments (0xd85a8 : word) = Some W_d8358.
Proof. vm_refl. Qed.
Lemma D_d8358 : decode_any W_d8358 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d835c : bv 32 := 0x0182d29b.
Lemma F_d835c : fetch_word Asan.M.loaded_segments (0xd85ac : word) = Some W_d835c.
Proof. vm_refl. Qed.
Lemma D_d835c : decode_any W_d835c = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8360 : bv 32 := 0x0113e8b3.
Lemma F_d8360 : fetch_word Asan.M.loaded_segments (0xd85b0 : word) = Some W_d8360.
Proof. vm_refl. Qed.
Lemma D_d8360 : decode_any W_d8360 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8364 : bv 32 := 0x00831393.
Lemma F_d8364 : fetch_word Asan.M.loaded_segments (0xd85b4 : word) = Some W_d8364.
Proof. vm_refl. Qed.
Lemma D_d8364 : decode_any W_d8364 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8368 : bv 32 := 0x0183531b.
Lemma F_d8368 : fetch_word Asan.M.loaded_segments (0xd85b8 : word) = Some W_d8368.
Proof. vm_refl. Qed.
Lemma D_d8368 : decode_any W_d8368 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d836c : bv 32 := 0x0053e2b3.
Lemma F_d836c : fetch_word Asan.M.loaded_segments (0xd85bc : word) = Some W_d836c.
Proof. vm_refl. Qed.
Lemma D_d836c : decode_any W_d836c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8370 : bv 32 := 0x00871393.
Lemma F_d8370 : fetch_word Asan.M.loaded_segments (0xd85c0 : word) = Some W_d8370.
Proof. vm_refl. Qed.
Lemma D_d8370 : decode_any W_d8370 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8374 : bv 32 := 0x0063e333.
Lemma F_d8374 : fetch_word Asan.M.loaded_segments (0xd85c4 : word) = Some W_d8374.
Proof. vm_refl. Qed.
Lemma D_d8374 : decode_any W_d8374 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8378 : bv 32 := 0xff060613.
Lemma F_d8378 : fetch_word Asan.M.loaded_segments (0xd85c8 : word) = Some W_d8378.
Proof. vm_refl. Qed.
Lemma D_d8378 : decode_any W_d8378 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d837c : bv 32 := 0x0106a023.
Lemma F_d837c : fetch_word Asan.M.loaded_segments (0xd85cc : word) = Some W_d837c.
Proof. vm_refl. Qed.
Lemma D_d837c : decode_any W_d837c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8380 : bv 32 := 0x0116a223.
Lemma F_d8380 : fetch_word Asan.M.loaded_segments (0xd85d0 : word) = Some W_d8380.
Proof. vm_refl. Qed.
Lemma D_d8380 : decode_any W_d8380 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8384 : bv 32 := 0x0056a423.
Lemma F_d8384 : fetch_word Asan.M.loaded_segments (0xd85d4 : word) = Some W_d8384.
Proof. vm_refl. Qed.
Lemma D_d8384 : decode_any W_d8384 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8388 : bv 32 := 0x0066a623.
Lemma F_d8388 : fetch_word Asan.M.loaded_segments (0xd85d8 : word) = Some W_d8388.
Proof. vm_refl. Qed.
Lemma D_d8388 : decode_any W_d8388 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d838c : bv 32 := 0x01068693.
Lemma F_d838c : fetch_word Asan.M.loaded_segments (0xd85dc : word) = Some W_d838c.
Proof. vm_refl. Qed.
Lemma D_d838c : decode_any W_d838c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8390 : bv 32 := 0x01058593.
Lemma F_d8390 : fetch_word Asan.M.loaded_segments (0xd85e0 : word) = Some W_d8390.
Proof. vm_refl. Qed.
Lemma D_d8390 : decode_any W_d8390 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8394 : bv 32 := 0xfac7e2e3.
Lemma F_d8394 : fetch_word Asan.M.loaded_segments (0xd85e4 : word) = Some W_d8394.
Proof. vm_refl. Qed.
Lemma D_d8394 : decode_any W_d8394 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8398 : bv 32 := 0xff358593.
Lemma F_d8398 : fetch_word Asan.M.loaded_segments (0xd85e8 : word) = Some W_d8398.
Proof. vm_refl. Qed.
Lemma D_d8398 : decode_any W_d8398 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d839c : bv 32 := 0x01000713.
Lemma F_d839c : fetch_word Asan.M.loaded_segments (0xd85ec : word) = Some W_d839c.
Proof. vm_refl. Qed.
Lemma D_d839c : decode_any W_d839c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83a0 : bv 32 := 0xdae66ce3.
Lemma F_d83a0 : fetch_word Asan.M.loaded_segments (0xd85f0 : word) = Some W_d83a0.
Proof. vm_refl. Qed.
Lemma D_d83a0 : decode_any W_d83a0 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83a4 : bv 32 := 0x0005c703.
Lemma F_d83a4 : fetch_word Asan.M.loaded_segments (0xd85f4 : word) = Some W_d83a4.
Proof. vm_refl. Qed.
Lemma D_d83a4 : decode_any W_d83a4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83a8 : bv 32 := 0x0015c783.
Lemma F_d83a8 : fetch_word Asan.M.loaded_segments (0xd85f8 : word) = Some W_d83a8.
Proof. vm_refl. Qed.
Lemma D_d83a8 : decode_any W_d83a8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83ac : bv 32 := 0x0025c803.
Lemma F_d83ac : fetch_word Asan.M.loaded_segments (0xd85fc : word) = Some W_d83ac.
Proof. vm_refl. Qed.
Lemma D_d83ac : decode_any W_d83ac = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83b0 : bv 32 := 0x0035c883.
Lemma F_d83b0 : fetch_word Asan.M.loaded_segments (0xd8600 : word) = Some W_d83b0.
Proof. vm_refl. Qed.
Lemma D_d83b0 : decode_any W_d83b0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83b4 : bv 32 := 0x0045c283.
Lemma F_d83b4 : fetch_word Asan.M.loaded_segments (0xd8604 : word) = Some W_d83b4.
Proof. vm_refl. Qed.
Lemma D_d83b4 : decode_any W_d83b4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83b8 : bv 32 := 0x0055c303.
Lemma F_d83b8 : fetch_word Asan.M.loaded_segments (0xd8608 : word) = Some W_d83b8.
Proof. vm_refl. Qed.
Lemma D_d83b8 : decode_any W_d83b8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83bc : bv 32 := 0x0065c383.
Lemma F_d83bc : fetch_word Asan.M.loaded_segments (0xd860c : word) = Some W_d83bc.
Proof. vm_refl. Qed.
Lemma D_d83bc : decode_any W_d83bc = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83c0 : bv 32 := 0x0075ce03.
Lemma F_d83c0 : fetch_word Asan.M.loaded_segments (0xd8610 : word) = Some W_d83c0.
Proof. vm_refl. Qed.
Lemma D_d83c0 : decode_any W_d83c0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83c4 : bv 32 := 0x00e68023.
Lemma F_d83c4 : fetch_word Asan.M.loaded_segments (0xd8614 : word) = Some W_d83c4.
Proof. vm_refl. Qed.
Lemma D_d83c4 : decode_any W_d83c4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83c8 : bv 32 := 0x00f680a3.
Lemma F_d83c8 : fetch_word Asan.M.loaded_segments (0xd8618 : word) = Some W_d83c8.
Proof. vm_refl. Qed.
Lemma D_d83c8 : decode_any W_d83c8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83cc : bv 32 := 0x01068123.
Lemma F_d83cc : fetch_word Asan.M.loaded_segments (0xd861c : word) = Some W_d83cc.
Proof. vm_refl. Qed.
Lemma D_d83cc : decode_any W_d83cc = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83d0 : bv 32 := 0x011681a3.
Lemma F_d83d0 : fetch_word Asan.M.loaded_segments (0xd8620 : word) = Some W_d83d0.
Proof. vm_refl. Qed.
Lemma D_d83d0 : decode_any W_d83d0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83d4 : bv 32 := 0x0085c703.
Lemma F_d83d4 : fetch_word Asan.M.loaded_segments (0xd8624 : word) = Some W_d83d4.
Proof. vm_refl. Qed.
Lemma D_d83d4 : decode_any W_d83d4 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83d8 : bv 32 := 0x0095c783.
Lemma F_d83d8 : fetch_word Asan.M.loaded_segments (0xd8628 : word) = Some W_d83d8.
Proof. vm_refl. Qed.
Lemma D_d83d8 : decode_any W_d83d8 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83dc : bv 32 := 0x00a5c803.
Lemma F_d83dc : fetch_word Asan.M.loaded_segments (0xd862c : word) = Some W_d83dc.
Proof. vm_refl. Qed.
Lemma D_d83dc : decode_any W_d83dc = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83e0 : bv 32 := 0x00b5c883.
Lemma F_d83e0 : fetch_word Asan.M.loaded_segments (0xd8630 : word) = Some W_d83e0.
Proof. vm_refl. Qed.
Lemma D_d83e0 : decode_any W_d83e0 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83e4 : bv 32 := 0x00568223.
Lemma F_d83e4 : fetch_word Asan.M.loaded_segments (0xd8634 : word) = Some W_d83e4.
Proof. vm_refl. Qed.
Lemma D_d83e4 : decode_any W_d83e4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83e8 : bv 32 := 0x006682a3.
Lemma F_d83e8 : fetch_word Asan.M.loaded_segments (0xd8638 : word) = Some W_d83e8.
Proof. vm_refl. Qed.
Lemma D_d83e8 : decode_any W_d83e8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83ec : bv 32 := 0x00768323.
Lemma F_d83ec : fetch_word Asan.M.loaded_segments (0xd863c : word) = Some W_d83ec.
Proof. vm_refl. Qed.
Lemma D_d83ec : decode_any W_d83ec = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83f0 : bv 32 := 0x01c683a3.
Lemma F_d83f0 : fetch_word Asan.M.loaded_segments (0xd8640 : word) = Some W_d83f0.
Proof. vm_refl. Qed.
Lemma D_d83f0 : decode_any W_d83f0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83f4 : bv 32 := 0x00c5c283.
Lemma F_d83f4 : fetch_word Asan.M.loaded_segments (0xd8644 : word) = Some W_d83f4.
Proof. vm_refl. Qed.
Lemma D_d83f4 : decode_any W_d83f4 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83f8 : bv 32 := 0x00d5c303.
Lemma F_d83f8 : fetch_word Asan.M.loaded_segments (0xd8648 : word) = Some W_d83f8.
Proof. vm_refl. Qed.
Lemma D_d83f8 : decode_any W_d83f8 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d83fc : bv 32 := 0x00e5c383.
Lemma F_d83fc : fetch_word Asan.M.loaded_segments (0xd864c : word) = Some W_d83fc.
Proof. vm_refl. Qed.
Lemma D_d83fc : decode_any W_d83fc = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8400 : bv 32 := 0x00f5ce03.
Lemma F_d8400 : fetch_word Asan.M.loaded_segments (0xd8650 : word) = Some W_d8400.
Proof. vm_refl. Qed.
Lemma D_d8400 : decode_any W_d8400 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8404 : bv 32 := 0x01058593.
Lemma F_d8404 : fetch_word Asan.M.loaded_segments (0xd8654 : word) = Some W_d8404.
Proof. vm_refl. Qed.
Lemma D_d8404 : decode_any W_d8404 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8408 : bv 32 := 0x00e68423.
Lemma F_d8408 : fetch_word Asan.M.loaded_segments (0xd8658 : word) = Some W_d8408.
Proof. vm_refl. Qed.
Lemma D_d8408 : decode_any W_d8408 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d840c : bv 32 := 0x00f684a3.
Lemma F_d840c : fetch_word Asan.M.loaded_segments (0xd865c : word) = Some W_d840c.
Proof. vm_refl. Qed.
Lemma D_d840c : decode_any W_d840c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8410 : bv 32 := 0x01068523.
Lemma F_d8410 : fetch_word Asan.M.loaded_segments (0xd8660 : word) = Some W_d8410.
Proof. vm_refl. Qed.
Lemma D_d8410 : decode_any W_d8410 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8414 : bv 32 := 0x011685a3.
Lemma F_d8414 : fetch_word Asan.M.loaded_segments (0xd8664 : word) = Some W_d8414.
Proof. vm_refl. Qed.
Lemma D_d8414 : decode_any W_d8414 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8418 : bv 32 := 0x01068713.
Lemma F_d8418 : fetch_word Asan.M.loaded_segments (0xd8668 : word) = Some W_d8418.
Proof. vm_refl. Qed.
Lemma D_d8418 : decode_any W_d8418 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d841c : bv 32 := 0x00568623.
Lemma F_d841c : fetch_word Asan.M.loaded_segments (0xd866c : word) = Some W_d841c.
Proof. vm_refl. Qed.
Lemma D_d841c : decode_any W_d841c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8420 : bv 32 := 0x006686a3.
Lemma F_d8420 : fetch_word Asan.M.loaded_segments (0xd8670 : word) = Some W_d8420.
Proof. vm_refl. Qed.
Lemma D_d8420 : decode_any W_d8420 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8424 : bv 32 := 0x00768723.
Lemma F_d8424 : fetch_word Asan.M.loaded_segments (0xd8674 : word) = Some W_d8424.
Proof. vm_refl. Qed.
Lemma D_d8424 : decode_any W_d8424 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8428 : bv 32 := 0x01c687a3.
Lemma F_d8428 : fetch_word Asan.M.loaded_segments (0xd8678 : word) = Some W_d8428.
Proof. vm_refl. Qed.
Lemma D_d8428 : decode_any W_d8428 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d842c : bv 32 := 0x00070693.
Lemma F_d842c : fetch_word Asan.M.loaded_segments (0xd867c : word) = Some W_d842c.
Proof. vm_refl. Qed.
Lemma D_d842c : decode_any W_d842c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8430 : bv 32 := 0x00867713.
Lemma F_d8430 : fetch_word Asan.M.loaded_segments (0xd8680 : word) = Some W_d8430.
Proof. vm_refl. Qed.
Lemma D_d8430 : decode_any W_d8430 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8434 : bv 32 := 0xd20706e3.
Lemma F_d8434 : fetch_word Asan.M.loaded_segments (0xd8684 : word) = Some W_d8434.
Proof. vm_refl. Qed.
Lemma D_d8434 : decode_any W_d8434 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8438 : bv 32 := 0x0005c703.
Lemma F_d8438 : fetch_word Asan.M.loaded_segments (0xd8688 : word) = Some W_d8438.
Proof. vm_refl. Qed.
Lemma D_d8438 : decode_any W_d8438 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d843c : bv 32 := 0x0015c783.
Lemma F_d843c : fetch_word Asan.M.loaded_segments (0xd868c : word) = Some W_d843c.
Proof. vm_refl. Qed.
Lemma D_d843c : decode_any W_d843c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8440 : bv 32 := 0x0025c803.
Lemma F_d8440 : fetch_word Asan.M.loaded_segments (0xd8690 : word) = Some W_d8440.
Proof. vm_refl. Qed.
Lemma D_d8440 : decode_any W_d8440 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8444 : bv 32 := 0x0035c883.
Lemma F_d8444 : fetch_word Asan.M.loaded_segments (0xd8694 : word) = Some W_d8444.
Proof. vm_refl. Qed.
Lemma D_d8444 : decode_any W_d8444 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8448 : bv 32 := 0x0045c283.
Lemma F_d8448 : fetch_word Asan.M.loaded_segments (0xd8698 : word) = Some W_d8448.
Proof. vm_refl. Qed.
Lemma D_d8448 : decode_any W_d8448 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d844c : bv 32 := 0x0055c303.
Lemma F_d844c : fetch_word Asan.M.loaded_segments (0xd869c : word) = Some W_d844c.
Proof. vm_refl. Qed.
Lemma D_d844c : decode_any W_d844c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8450 : bv 32 := 0x0065c383.
Lemma F_d8450 : fetch_word Asan.M.loaded_segments (0xd86a0 : word) = Some W_d8450.
Proof. vm_refl. Qed.
Lemma D_d8450 : decode_any W_d8450 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8454 : bv 32 := 0x0075ce03.
Lemma F_d8454 : fetch_word Asan.M.loaded_segments (0xd86a4 : word) = Some W_d8454.
Proof. vm_refl. Qed.
Lemma D_d8454 : decode_any W_d8454 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8458 : bv 32 := 0x00858593.
Lemma F_d8458 : fetch_word Asan.M.loaded_segments (0xd86a8 : word) = Some W_d8458.
Proof. vm_refl. Qed.
Lemma D_d8458 : decode_any W_d8458 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d845c : bv 32 := 0x00e68023.
Lemma F_d845c : fetch_word Asan.M.loaded_segments (0xd86ac : word) = Some W_d845c.
Proof. vm_refl. Qed.
Lemma D_d845c : decode_any W_d845c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8460 : bv 32 := 0x00f680a3.
Lemma F_d8460 : fetch_word Asan.M.loaded_segments (0xd86b0 : word) = Some W_d8460.
Proof. vm_refl. Qed.
Lemma D_d8460 : decode_any W_d8460 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8464 : bv 32 := 0x01068123.
Lemma F_d8464 : fetch_word Asan.M.loaded_segments (0xd86b4 : word) = Some W_d8464.
Proof. vm_refl. Qed.
Lemma D_d8464 : decode_any W_d8464 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8468 : bv 32 := 0x011681a3.
Lemma F_d8468 : fetch_word Asan.M.loaded_segments (0xd86b8 : word) = Some W_d8468.
Proof. vm_refl. Qed.
Lemma D_d8468 : decode_any W_d8468 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d846c : bv 32 := 0x00868713.
Lemma F_d846c : fetch_word Asan.M.loaded_segments (0xd86bc : word) = Some W_d846c.
Proof. vm_refl. Qed.
Lemma D_d846c : decode_any W_d846c = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8470 : bv 32 := 0x00568223.
Lemma F_d8470 : fetch_word Asan.M.loaded_segments (0xd86c0 : word) = Some W_d8470.
Proof. vm_refl. Qed.
Lemma D_d8470 : decode_any W_d8470 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8474 : bv 32 := 0x006682a3.
Lemma F_d8474 : fetch_word Asan.M.loaded_segments (0xd86c4 : word) = Some W_d8474.
Proof. vm_refl. Qed.
Lemma D_d8474 : decode_any W_d8474 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8478 : bv 32 := 0x00768323.
Lemma F_d8478 : fetch_word Asan.M.loaded_segments (0xd86c8 : word) = Some W_d8478.
Proof. vm_refl. Qed.
Lemma D_d8478 : decode_any W_d8478 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d847c : bv 32 := 0x01c683a3.
Lemma F_d847c : fetch_word Asan.M.loaded_segments (0xd86cc : word) = Some W_d847c.
Proof. vm_refl. Qed.
Lemma D_d847c : decode_any W_d847c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8480 : bv 32 := 0x00070693.
Lemma F_d8480 : fetch_word Asan.M.loaded_segments (0xd86d0 : word) = Some W_d8480.
Proof. vm_refl. Qed.
Lemma D_d8480 : decode_any W_d8480 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8484 : bv 32 := 0x00467713.
Lemma F_d8484 : fetch_word Asan.M.loaded_segments (0xd86d4 : word) = Some W_d8484.
Proof. vm_refl. Qed.
Lemma D_d8484 : decode_any W_d8484 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8488 : bv 32 := 0x02070863.
Lemma F_d8488 : fetch_word Asan.M.loaded_segments (0xd86d8 : word) = Some W_d8488.
Proof. vm_refl. Qed.
Lemma D_d8488 : decode_any W_d8488 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d848c : bv 32 := 0x0005c703.
Lemma F_d848c : fetch_word Asan.M.loaded_segments (0xd86dc : word) = Some W_d848c.
Proof. vm_refl. Qed.
Lemma D_d848c : decode_any W_d848c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8490 : bv 32 := 0x0015c783.
Lemma F_d8490 : fetch_word Asan.M.loaded_segments (0xd86e0 : word) = Some W_d8490.
Proof. vm_refl. Qed.
Lemma D_d8490 : decode_any W_d8490 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8494 : bv 32 := 0x0025c803.
Lemma F_d8494 : fetch_word Asan.M.loaded_segments (0xd86e4 : word) = Some W_d8494.
Proof. vm_refl. Qed.
Lemma D_d8494 : decode_any W_d8494 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8498 : bv 32 := 0x0035c883.
Lemma F_d8498 : fetch_word Asan.M.loaded_segments (0xd86e8 : word) = Some W_d8498.
Proof. vm_refl. Qed.
Lemma D_d8498 : decode_any W_d8498 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d849c : bv 32 := 0x00458593.
Lemma F_d849c : fetch_word Asan.M.loaded_segments (0xd86ec : word) = Some W_d849c.
Proof. vm_refl. Qed.
Lemma D_d849c : decode_any W_d849c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84a0 : bv 32 := 0x00468293.
Lemma F_d84a0 : fetch_word Asan.M.loaded_segments (0xd86f0 : word) = Some W_d84a0.
Proof. vm_refl. Qed.
Lemma D_d84a0 : decode_any W_d84a0 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84a4 : bv 32 := 0x00e68023.
Lemma F_d84a4 : fetch_word Asan.M.loaded_segments (0xd86f4 : word) = Some W_d84a4.
Proof. vm_refl. Qed.
Lemma D_d84a4 : decode_any W_d84a4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84a8 : bv 32 := 0x00f680a3.
Lemma F_d84a8 : fetch_word Asan.M.loaded_segments (0xd86f8 : word) = Some W_d84a8.
Proof. vm_refl. Qed.
Lemma D_d84a8 : decode_any W_d84a8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84ac : bv 32 := 0x01068123.
Lemma F_d84ac : fetch_word Asan.M.loaded_segments (0xd86fc : word) = Some W_d84ac.
Proof. vm_refl. Qed.
Lemma D_d84ac : decode_any W_d84ac = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84b0 : bv 32 := 0x011681a3.
Lemma F_d84b0 : fetch_word Asan.M.loaded_segments (0xd8700 : word) = Some W_d84b0.
Proof. vm_refl. Qed.
Lemma D_d84b0 : decode_any W_d84b0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84b4 : bv 32 := 0x00028693.
Lemma F_d84b4 : fetch_word Asan.M.loaded_segments (0xd8704 : word) = Some W_d84b4.
Proof. vm_refl. Qed.
Lemma D_d84b4 : decode_any W_d84b4 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84b8 : bv 32 := 0x00267713.
Lemma F_d84b8 : fetch_word Asan.M.loaded_segments (0xd8708 : word) = Some W_d84b8.
Proof. vm_refl. Qed.
Lemma D_d84b8 : decode_any W_d84b8 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84bc : bv 32 := 0x00071863.
Lemma F_d84bc : fetch_word Asan.M.loaded_segments (0xd870c : word) = Some W_d84bc.
Proof. vm_refl. Qed.
Lemma D_d84bc : decode_any W_d84bc = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84c0 : bv 32 := 0x00167613.
Lemma F_d84c0 : fetch_word Asan.M.loaded_segments (0xd8710 : word) = Some W_d84c0.
Proof. vm_refl. Qed.
Lemma D_d84c0 : decode_any W_d84c0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84c4 : bv 32 := 0x02061663.
Lemma F_d84c4 : fetch_word Asan.M.loaded_segments (0xd8714 : word) = Some W_d84c4.
Proof. vm_refl. Qed.
Lemma D_d84c4 : decode_any W_d84c4 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84c8 : bv 32 := 0x00008067.
Lemma F_d84c8 : fetch_word Asan.M.loaded_segments (0xd8718 : word) = Some W_d84c8.
Proof. vm_refl. Qed.
Lemma D_d84c8 : decode_any W_d84c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84cc : bv 32 := 0x0005c703.
Lemma F_d84cc : fetch_word Asan.M.loaded_segments (0xd871c : word) = Some W_d84cc.
Proof. vm_refl. Qed.
Lemma D_d84cc : decode_any W_d84cc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84d0 : bv 32 := 0x0015c783.
Lemma F_d84d0 : fetch_word Asan.M.loaded_segments (0xd8720 : word) = Some W_d84d0.
Proof. vm_refl. Qed.
Lemma D_d84d0 : decode_any W_d84d0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84d4 : bv 32 := 0x00258593.
Lemma F_d84d4 : fetch_word Asan.M.loaded_segments (0xd8724 : word) = Some W_d84d4.
Proof. vm_refl. Qed.
Lemma D_d84d4 : decode_any W_d84d4 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84d8 : bv 32 := 0x00268813.
Lemma F_d84d8 : fetch_word Asan.M.loaded_segments (0xd8728 : word) = Some W_d84d8.
Proof. vm_refl. Qed.
Lemma D_d84d8 : decode_any W_d84d8 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84dc : bv 32 := 0x00e68023.
Lemma F_d84dc : fetch_word Asan.M.loaded_segments (0xd872c : word) = Some W_d84dc.
Proof. vm_refl. Qed.
Lemma D_d84dc : decode_any W_d84dc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84e0 : bv 32 := 0x00f680a3.
Lemma F_d84e0 : fetch_word Asan.M.loaded_segments (0xd8730 : word) = Some W_d84e0.
Proof. vm_refl. Qed.
Lemma D_d84e0 : decode_any W_d84e0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84e4 : bv 32 := 0x00080693.
Lemma F_d84e4 : fetch_word Asan.M.loaded_segments (0xd8734 : word) = Some W_d84e4.
Proof. vm_refl. Qed.
Lemma D_d84e4 : decode_any W_d84e4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84e8 : bv 32 := 0x00167613.
Lemma F_d84e8 : fetch_word Asan.M.loaded_segments (0xd8738 : word) = Some W_d84e8.
Proof. vm_refl. Qed.
Lemma D_d84e8 : decode_any W_d84e8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84ec : bv 32 := 0xfc060ee3.
Lemma F_d84ec : fetch_word Asan.M.loaded_segments (0xd873c : word) = Some W_d84ec.
Proof. vm_refl. Qed.
Lemma D_d84ec : decode_any W_d84ec = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84f0 : bv 32 := 0x0005c583.
Lemma F_d84f0 : fetch_word Asan.M.loaded_segments (0xd8740 : word) = Some W_d84f0.
Proof. vm_refl. Qed.
Lemma D_d84f0 : decode_any W_d84f0 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84f4 : bv 32 := 0x00b68023.
Lemma F_d84f4 : fetch_word Asan.M.loaded_segments (0xd8744 : word) = Some W_d84f4.
Proof. vm_refl. Qed.
Lemma D_d84f4 : decode_any W_d84f4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d84f8 : bv 32 := 0x00008067.
Lemma F_d84f8 : fetch_word Asan.M.loaded_segments (0xd8748 : word) = Some W_d84f8.
Proof. vm_refl. Qed.
Lemma D_d84f8 : decode_any W_d84f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
