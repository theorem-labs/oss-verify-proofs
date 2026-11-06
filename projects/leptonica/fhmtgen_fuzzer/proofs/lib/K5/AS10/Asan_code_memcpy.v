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
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Asan.
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
Definition W_da1dc : bv 32 := 0x0035f693.
Lemma F_da1dc : fetch_word Asan.M.loaded_segments (0xda340 : word) = Some W_da1dc.
Proof. vm_refl. Qed.
Lemma D_da1dc : decode_any W_da1dc = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1e0 : bv 32 := 0x10068863.
Lemma F_da1e0 : fetch_word Asan.M.loaded_segments (0xda344 : word) = Some W_da1e0.
Proof. vm_refl. Qed.
Lemma D_da1e0 : decode_any W_da1e0 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1e4 : bv 32 := 0x02060e63.
Lemma F_da1e4 : fetch_word Asan.M.loaded_segments (0xda348 : word) = Some W_da1e4.
Proof. vm_refl. Qed.
Lemma D_da1e4 : decode_any W_da1e4 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1e8 : bv 32 := 0x00158713.
Lemma F_da1e8 : fetch_word Asan.M.loaded_segments (0xda34c : word) = Some W_da1e8.
Proof. vm_refl. Qed.
Lemma D_da1e8 : decode_any W_da1e8 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1ec : bv 32 := 0x00100793.
Lemma F_da1ec : fetch_word Asan.M.loaded_segments (0xda350 : word) = Some W_da1ec.
Proof. vm_refl. Qed.
Lemma D_da1ec : decode_any W_da1ec = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1f0 : bv 32 := 0x00050693.
Lemma F_da1f0 : fetch_word Asan.M.loaded_segments (0xda354 : word) = Some W_da1f0.
Proof. vm_refl. Qed.
Lemma D_da1f0 : decode_any W_da1f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1f4 : bv 32 := 0x0005c883.
Lemma F_da1f4 : fetch_word Asan.M.loaded_segments (0xda358 : word) = Some W_da1f4.
Proof. vm_refl. Qed.
Lemma D_da1f4 : decode_any W_da1f4 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1f8 : bv 32 := 0x00060813.
Lemma F_da1f8 : fetch_word Asan.M.loaded_segments (0xda35c : word) = Some W_da1f8.
Proof. vm_refl. Qed.
Lemma D_da1f8 : decode_any W_da1f8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da1fc : bv 32 := 0x00158593.
Lemma F_da1fc : fetch_word Asan.M.loaded_segments (0xda360 : word) = Some W_da1fc.
Proof. vm_refl. Qed.
Lemma D_da1fc : decode_any W_da1fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da200 : bv 32 := 0x00377293.
Lemma F_da200 : fetch_word Asan.M.loaded_segments (0xda364 : word) = Some W_da200.
Proof. vm_refl. Qed.
Lemma D_da200 : decode_any W_da200 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da204 : bv 32 := 0x01168023.
Lemma F_da204 : fetch_word Asan.M.loaded_segments (0xda368 : word) = Some W_da204.
Proof. vm_refl. Qed.
Lemma D_da204 : decode_any W_da204 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da208 : bv 32 := 0x00168693.
Lemma F_da208 : fetch_word Asan.M.loaded_segments (0xda36c : word) = Some W_da208.
Proof. vm_refl. Qed.
Lemma D_da208 : decode_any W_da208 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da20c : bv 32 := 0xfff60613.
Lemma F_da20c : fetch_word Asan.M.loaded_segments (0xda370 : word) = Some W_da20c.
Proof. vm_refl. Qed.
Lemma D_da20c : decode_any W_da20c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da210 : bv 32 := 0x00028a63.
Lemma F_da210 : fetch_word Asan.M.loaded_segments (0xda374 : word) = Some W_da210.
Proof. vm_refl. Qed.
Lemma D_da210 : decode_any W_da210 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da214 : bv 32 := 0x00170713.
Lemma F_da214 : fetch_word Asan.M.loaded_segments (0xda378 : word) = Some W_da214.
Proof. vm_refl. Qed.
Lemma D_da214 : decode_any W_da214 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da218 : bv 32 := 0xfcf81ee3.
Lemma F_da218 : fetch_word Asan.M.loaded_segments (0xda37c : word) = Some W_da218.
Proof. vm_refl. Qed.
Lemma D_da218 : decode_any W_da218 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da21c : bv 32 := 0x0080006f.
Lemma F_da21c : fetch_word Asan.M.loaded_segments (0xda380 : word) = Some W_da21c.
Proof. vm_refl. Qed.
Lemma D_da21c : decode_any W_da21c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da220 : bv 32 := 0x00050693.
Lemma F_da220 : fetch_word Asan.M.loaded_segments (0xda384 : word) = Some W_da220.
Proof. vm_refl. Qed.
Lemma D_da220 : decode_any W_da220 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da224 : bv 32 := 0x0036f793.
Lemma F_da224 : fetch_word Asan.M.loaded_segments (0xda388 : word) = Some W_da224.
Proof. vm_refl. Qed.
Lemma D_da224 : decode_any W_da224 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da228 : bv 32 := 0x0c078a63.
Lemma F_da228 : fetch_word Asan.M.loaded_segments (0xda38c : word) = Some W_da228.
Proof. vm_refl. Qed.
Lemma D_da228 : decode_any W_da228 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da22c : bv 32 := 0x02000713.
Lemma F_da22c : fetch_word Asan.M.loaded_segments (0xda390 : word) = Some W_da22c.
Proof. vm_refl. Qed.
Lemma D_da22c : decode_any W_da22c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da230 : bv 32 := 0x02e67063.
Lemma F_da230 : fetch_word Asan.M.loaded_segments (0xda394 : word) = Some W_da230.
Proof. vm_refl. Qed.
Lemma D_da230 : decode_any W_da230 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da234 : bv 32 := 0x01000713.
Lemma F_da234 : fetch_word Asan.M.loaded_segments (0xda398 : word) = Some W_da234.
Proof. vm_refl. Qed.
Lemma D_da234 : decode_any W_da234 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da238 : bv 32 := 0x24e67863.
Lemma F_da238 : fetch_word Asan.M.loaded_segments (0xda39c : word) = Some W_da238.
Proof. vm_refl. Qed.
Lemma D_da238 : decode_any W_da238 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da23c : bv 32 := 0x00867713.
Lemma F_da23c : fetch_word Asan.M.loaded_segments (0xda3a0 : word) = Some W_da23c.
Proof. vm_refl. Qed.
Lemma D_da23c : decode_any W_da23c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da240 : bv 32 := 0x2c071e63.
Lemma F_da240 : fetch_word Asan.M.loaded_segments (0xda3a4 : word) = Some W_da240.
Proof. vm_refl. Qed.
Lemma D_da240 : decode_any W_da240 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da244 : bv 32 := 0x00467713.
Lemma F_da244 : fetch_word Asan.M.loaded_segments (0xda3a8 : word) = Some W_da244.
Proof. vm_refl. Qed.
Lemma D_da244 : decode_any W_da244 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da248 : bv 32 := 0x32071463.
Lemma F_da248 : fetch_word Asan.M.loaded_segments (0xda3ac : word) = Some W_da248.
Proof. vm_refl. Qed.
Lemma D_da248 : decode_any W_da248 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da24c : bv 32 := 0x3500006f.
Lemma F_da24c : fetch_word Asan.M.loaded_segments (0xda3b0 : word) = Some W_da24c.
Proof. vm_refl. Qed.
Lemma D_da24c : decode_any W_da24c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da250 : bv 32 := 0x0005a703.
Lemma F_da250 : fetch_word Asan.M.loaded_segments (0xda3b4 : word) = Some W_da250.
Proof. vm_refl. Qed.
Lemma D_da250 : decode_any W_da250 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da254 : bv 32 := 0x00300813.
Lemma F_da254 : fetch_word Asan.M.loaded_segments (0xda3b8 : word) = Some W_da254.
Proof. vm_refl. Qed.
Lemma D_da254 : decode_any W_da254 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da258 : bv 32 := 0x11078e63.
Lemma F_da258 : fetch_word Asan.M.loaded_segments (0xda3bc : word) = Some W_da258.
Proof. vm_refl. Qed.
Lemma D_da258 : decode_any W_da258 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da25c : bv 32 := 0x00200813.
Lemma F_da25c : fetch_word Asan.M.loaded_segments (0xda3c0 : word) = Some W_da25c.
Proof. vm_refl. Qed.
Lemma D_da25c : decode_any W_da25c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da260 : bv 32 := 0x19079c63.
Lemma F_da260 : fetch_word Asan.M.loaded_segments (0xda3c4 : word) = Some W_da260.
Proof. vm_refl. Qed.
Lemma D_da260 : decode_any W_da260 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da264 : bv 32 := 0x00875793.
Lemma F_da264 : fetch_word Asan.M.loaded_segments (0xda3c8 : word) = Some W_da264.
Proof. vm_refl. Qed.
Lemma D_da264 : decode_any W_da264 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da268 : bv 32 := 0xffe60613.
Lemma F_da268 : fetch_word Asan.M.loaded_segments (0xda3cc : word) = Some W_da268.
Proof. vm_refl. Qed.
Lemma D_da268 : decode_any W_da268 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da26c : bv 32 := 0x00e68023.
Lemma F_da26c : fetch_word Asan.M.loaded_segments (0xda3d0 : word) = Some W_da26c.
Proof. vm_refl. Qed.
Lemma D_da26c : decode_any W_da26c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da270 : bv 32 := 0x00f680a3.
Lemma F_da270 : fetch_word Asan.M.loaded_segments (0xda3d4 : word) = Some W_da270.
Proof. vm_refl. Qed.
Lemma D_da270 : decode_any W_da270 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da274 : bv 32 := 0x00268693.
Lemma F_da274 : fetch_word Asan.M.loaded_segments (0xda3d8 : word) = Some W_da274.
Proof. vm_refl. Qed.
Lemma D_da274 : decode_any W_da274 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da278 : bv 32 := 0x01058593.
Lemma F_da278 : fetch_word Asan.M.loaded_segments (0xda3dc : word) = Some W_da278.
Proof. vm_refl. Qed.
Lemma D_da278 : decode_any W_da278 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da27c : bv 32 := 0x01100793.
Lemma F_da27c : fetch_word Asan.M.loaded_segments (0xda3e0 : word) = Some W_da27c.
Proof. vm_refl. Qed.
Lemma D_da27c : decode_any W_da27c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da280 : bv 32 := 0x0107581b.
Lemma F_da280 : fetch_word Asan.M.loaded_segments (0xda3e4 : word) = Some W_da280.
Proof. vm_refl. Qed.
Lemma D_da280 : decode_any W_da280 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da284 : bv 32 := 0xff45a883.
Lemma F_da284 : fetch_word Asan.M.loaded_segments (0xda3e8 : word) = Some W_da284.
Proof. vm_refl. Qed.
Lemma D_da284 : decode_any W_da284 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da288 : bv 32 := 0xff85a283.
Lemma F_da288 : fetch_word Asan.M.loaded_segments (0xda3ec : word) = Some W_da288.
Proof. vm_refl. Qed.
Lemma D_da288 : decode_any W_da288 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da28c : bv 32 := 0xffc5a303.
Lemma F_da28c : fetch_word Asan.M.loaded_segments (0xda3f0 : word) = Some W_da28c.
Proof. vm_refl. Qed.
Lemma D_da28c : decode_any W_da28c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da290 : bv 32 := 0x0005a703.
Lemma F_da290 : fetch_word Asan.M.loaded_segments (0xda3f4 : word) = Some W_da290.
Proof. vm_refl. Qed.
Lemma D_da290 : decode_any W_da290 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da294 : bv 32 := 0x01089393.
Lemma F_da294 : fetch_word Asan.M.loaded_segments (0xda3f8 : word) = Some W_da294.
Proof. vm_refl. Qed.
Lemma D_da294 : decode_any W_da294 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da298 : bv 32 := 0x0108d89b.
Lemma F_da298 : fetch_word Asan.M.loaded_segments (0xda3fc : word) = Some W_da298.
Proof. vm_refl. Qed.
Lemma D_da298 : decode_any W_da298 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da29c : bv 32 := 0x0103e833.
Lemma F_da29c : fetch_word Asan.M.loaded_segments (0xda400 : word) = Some W_da29c.
Proof. vm_refl. Qed.
Lemma D_da29c : decode_any W_da29c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2a0 : bv 32 := 0x01029393.
Lemma F_da2a0 : fetch_word Asan.M.loaded_segments (0xda404 : word) = Some W_da2a0.
Proof. vm_refl. Qed.
Lemma D_da2a0 : decode_any W_da2a0 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2a4 : bv 32 := 0x0102d29b.
Lemma F_da2a4 : fetch_word Asan.M.loaded_segments (0xda408 : word) = Some W_da2a4.
Proof. vm_refl. Qed.
Lemma D_da2a4 : decode_any W_da2a4 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2a8 : bv 32 := 0x0113e8b3.
Lemma F_da2a8 : fetch_word Asan.M.loaded_segments (0xda40c : word) = Some W_da2a8.
Proof. vm_refl. Qed.
Lemma D_da2a8 : decode_any W_da2a8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2ac : bv 32 := 0x01031393.
Lemma F_da2ac : fetch_word Asan.M.loaded_segments (0xda410 : word) = Some W_da2ac.
Proof. vm_refl. Qed.
Lemma D_da2ac : decode_any W_da2ac = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2b0 : bv 32 := 0x0103531b.
Lemma F_da2b0 : fetch_word Asan.M.loaded_segments (0xda414 : word) = Some W_da2b0.
Proof. vm_refl. Qed.
Lemma D_da2b0 : decode_any W_da2b0 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2b4 : bv 32 := 0x0053e2b3.
Lemma F_da2b4 : fetch_word Asan.M.loaded_segments (0xda418 : word) = Some W_da2b4.
Proof. vm_refl. Qed.
Lemma D_da2b4 : decode_any W_da2b4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2b8 : bv 32 := 0x01071393.
Lemma F_da2b8 : fetch_word Asan.M.loaded_segments (0xda41c : word) = Some W_da2b8.
Proof. vm_refl. Qed.
Lemma D_da2b8 : decode_any W_da2b8 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2bc : bv 32 := 0x0063e333.
Lemma F_da2bc : fetch_word Asan.M.loaded_segments (0xda420 : word) = Some W_da2bc.
Proof. vm_refl. Qed.
Lemma D_da2bc : decode_any W_da2bc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2c0 : bv 32 := 0xff060613.
Lemma F_da2c0 : fetch_word Asan.M.loaded_segments (0xda424 : word) = Some W_da2c0.
Proof. vm_refl. Qed.
Lemma D_da2c0 : decode_any W_da2c0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2c4 : bv 32 := 0x0106a023.
Lemma F_da2c4 : fetch_word Asan.M.loaded_segments (0xda428 : word) = Some W_da2c4.
Proof. vm_refl. Qed.
Lemma D_da2c4 : decode_any W_da2c4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2c8 : bv 32 := 0x0116a223.
Lemma F_da2c8 : fetch_word Asan.M.loaded_segments (0xda42c : word) = Some W_da2c8.
Proof. vm_refl. Qed.
Lemma D_da2c8 : decode_any W_da2c8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2cc : bv 32 := 0x0056a423.
Lemma F_da2cc : fetch_word Asan.M.loaded_segments (0xda430 : word) = Some W_da2cc.
Proof. vm_refl. Qed.
Lemma D_da2cc : decode_any W_da2cc = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2d0 : bv 32 := 0x0066a623.
Lemma F_da2d0 : fetch_word Asan.M.loaded_segments (0xda434 : word) = Some W_da2d0.
Proof. vm_refl. Qed.
Lemma D_da2d0 : decode_any W_da2d0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2d4 : bv 32 := 0x01068693.
Lemma F_da2d4 : fetch_word Asan.M.loaded_segments (0xda438 : word) = Some W_da2d4.
Proof. vm_refl. Qed.
Lemma D_da2d4 : decode_any W_da2d4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2d8 : bv 32 := 0x01058593.
Lemma F_da2d8 : fetch_word Asan.M.loaded_segments (0xda43c : word) = Some W_da2d8.
Proof. vm_refl. Qed.
Lemma D_da2d8 : decode_any W_da2d8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2dc : bv 32 := 0xfac7e2e3.
Lemma F_da2dc : fetch_word Asan.M.loaded_segments (0xda440 : word) = Some W_da2dc.
Proof. vm_refl. Qed.
Lemma D_da2dc : decode_any W_da2dc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2e0 : bv 32 := 0xff258593.
Lemma F_da2e0 : fetch_word Asan.M.loaded_segments (0xda444 : word) = Some W_da2e0.
Proof. vm_refl. Qed.
Lemma D_da2e0 : decode_any W_da2e0 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2e4 : bv 32 := 0x01000713.
Lemma F_da2e4 : fetch_word Asan.M.loaded_segments (0xda448 : word) = Some W_da2e4.
Proof. vm_refl. Qed.
Lemma D_da2e4 : decode_any W_da2e4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2e8 : bv 32 := 0xf4e66ae3.
Lemma F_da2e8 : fetch_word Asan.M.loaded_segments (0xda44c : word) = Some W_da2e8.
Proof. vm_refl. Qed.
Lemma D_da2e8 : decode_any W_da2e8 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2ec : bv 32 := 0x19c0006f.
Lemma F_da2ec : fetch_word Asan.M.loaded_segments (0xda450 : word) = Some W_da2ec.
Proof. vm_refl. Qed.
Lemma D_da2ec : decode_any W_da2ec = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2f0 : bv 32 := 0x00050693.
Lemma F_da2f0 : fetch_word Asan.M.loaded_segments (0xda454 : word) = Some W_da2f0.
Proof. vm_refl. Qed.
Lemma D_da2f0 : decode_any W_da2f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2f4 : bv 32 := 0x00357793.
Lemma F_da2f4 : fetch_word Asan.M.loaded_segments (0xda458 : word) = Some W_da2f4.
Proof. vm_refl. Qed.
Lemma D_da2f4 : decode_any W_da2f4 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2f8 : bv 32 := 0xf2079ae3.
Lemma F_da2f8 : fetch_word Asan.M.loaded_segments (0xda45c : word) = Some W_da2f8.
Proof. vm_refl. Qed.
Lemma D_da2f8 : decode_any W_da2f8 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da2fc : bv 32 := 0x01000713.
Lemma F_da2fc : fetch_word Asan.M.loaded_segments (0xda460 : word) = Some W_da2fc.
Proof. vm_refl. Qed.
Lemma D_da2fc : decode_any W_da2fc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da300 : bv 32 := 0x02e66c63.
Lemma F_da300 : fetch_word Asan.M.loaded_segments (0xda464 : word) = Some W_da300.
Proof. vm_refl. Qed.
Lemma D_da300 : decode_any W_da300 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da304 : bv 32 := 0x00f00713.
Lemma F_da304 : fetch_word Asan.M.loaded_segments (0xda468 : word) = Some W_da304.
Proof. vm_refl. Qed.
Lemma D_da304 : decode_any W_da304 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da308 : bv 32 := 0x0005a783.
Lemma F_da308 : fetch_word Asan.M.loaded_segments (0xda46c : word) = Some W_da308.
Proof. vm_refl. Qed.
Lemma D_da308 : decode_any W_da308 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da30c : bv 32 := 0x0045a803.
Lemma F_da30c : fetch_word Asan.M.loaded_segments (0xda470 : word) = Some W_da30c.
Proof. vm_refl. Qed.
Lemma D_da30c : decode_any W_da30c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da310 : bv 32 := 0x0085a883.
Lemma F_da310 : fetch_word Asan.M.loaded_segments (0xda474 : word) = Some W_da310.
Proof. vm_refl. Qed.
Lemma D_da310 : decode_any W_da310 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da314 : bv 32 := 0x00c5a283.
Lemma F_da314 : fetch_word Asan.M.loaded_segments (0xda478 : word) = Some W_da314.
Proof. vm_refl. Qed.
Lemma D_da314 : decode_any W_da314 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da318 : bv 32 := 0x01058593.
Lemma F_da318 : fetch_word Asan.M.loaded_segments (0xda47c : word) = Some W_da318.
Proof. vm_refl. Qed.
Lemma D_da318 : decode_any W_da318 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da31c : bv 32 := 0xff060613.
Lemma F_da31c : fetch_word Asan.M.loaded_segments (0xda480 : word) = Some W_da31c.
Proof. vm_refl. Qed.
Lemma D_da31c : decode_any W_da31c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da320 : bv 32 := 0x00f6a023.
Lemma F_da320 : fetch_word Asan.M.loaded_segments (0xda484 : word) = Some W_da320.
Proof. vm_refl. Qed.
Lemma D_da320 : decode_any W_da320 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da324 : bv 32 := 0x0106a223.
Lemma F_da324 : fetch_word Asan.M.loaded_segments (0xda488 : word) = Some W_da324.
Proof. vm_refl. Qed.
Lemma D_da324 : decode_any W_da324 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da328 : bv 32 := 0x0116a423.
Lemma F_da328 : fetch_word Asan.M.loaded_segments (0xda48c : word) = Some W_da328.
Proof. vm_refl. Qed.
Lemma D_da328 : decode_any W_da328 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da32c : bv 32 := 0x0056a623.
Lemma F_da32c : fetch_word Asan.M.loaded_segments (0xda490 : word) = Some W_da32c.
Proof. vm_refl. Qed.
Lemma D_da32c : decode_any W_da32c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da330 : bv 32 := 0x01068693.
Lemma F_da330 : fetch_word Asan.M.loaded_segments (0xda494 : word) = Some W_da330.
Proof. vm_refl. Qed.
Lemma D_da330 : decode_any W_da330 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da334 : bv 32 := 0xfcc76ae3.
Lemma F_da334 : fetch_word Asan.M.loaded_segments (0xda498 : word) = Some W_da334.
Proof. vm_refl. Qed.
Lemma D_da334 : decode_any W_da334 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da338 : bv 32 := 0x00800713.
Lemma F_da338 : fetch_word Asan.M.loaded_segments (0xda49c : word) = Some W_da338.
Proof. vm_refl. Qed.
Lemma D_da338 : decode_any W_da338 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da33c : bv 32 := 0x00e66e63.
Lemma F_da33c : fetch_word Asan.M.loaded_segments (0xda4a0 : word) = Some W_da33c.
Proof. vm_refl. Qed.
Lemma D_da33c : decode_any W_da33c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da340 : bv 32 := 0x0005a703.
Lemma F_da340 : fetch_word Asan.M.loaded_segments (0xda4a4 : word) = Some W_da340.
Proof. vm_refl. Qed.
Lemma D_da340 : decode_any W_da340 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da344 : bv 32 := 0x0045a783.
Lemma F_da344 : fetch_word Asan.M.loaded_segments (0xda4a8 : word) = Some W_da344.
Proof. vm_refl. Qed.
Lemma D_da344 : decode_any W_da344 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da348 : bv 32 := 0x00e6a023.
Lemma F_da348 : fetch_word Asan.M.loaded_segments (0xda4ac : word) = Some W_da348.
Proof. vm_refl. Qed.
Lemma D_da348 : decode_any W_da348 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da34c : bv 32 := 0x00f6a223.
Lemma F_da34c : fetch_word Asan.M.loaded_segments (0xda4b0 : word) = Some W_da34c.
Proof. vm_refl. Qed.
Lemma D_da34c : decode_any W_da34c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da350 : bv 32 := 0x00868693.
Lemma F_da350 : fetch_word Asan.M.loaded_segments (0xda4b4 : word) = Some W_da350.
Proof. vm_refl. Qed.
Lemma D_da350 : decode_any W_da350 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da354 : bv 32 := 0x00858593.
Lemma F_da354 : fetch_word Asan.M.loaded_segments (0xda4b8 : word) = Some W_da354.
Proof. vm_refl. Qed.
Lemma D_da354 : decode_any W_da354 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da358 : bv 32 := 0x00467713.
Lemma F_da358 : fetch_word Asan.M.loaded_segments (0xda4bc : word) = Some W_da358.
Proof. vm_refl. Qed.
Lemma D_da358 : decode_any W_da358 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da35c : bv 32 := 0x24070063.
Lemma F_da35c : fetch_word Asan.M.loaded_segments (0xda4c0 : word) = Some W_da35c.
Proof. vm_refl. Qed.
Lemma D_da35c : decode_any W_da35c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da360 : bv 32 := 0x0005a703.
Lemma F_da360 : fetch_word Asan.M.loaded_segments (0xda4c4 : word) = Some W_da360.
Proof. vm_refl. Qed.
Lemma D_da360 : decode_any W_da360 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da364 : bv 32 := 0x00458593.
Lemma F_da364 : fetch_word Asan.M.loaded_segments (0xda4c8 : word) = Some W_da364.
Proof. vm_refl. Qed.
Lemma D_da364 : decode_any W_da364 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da368 : bv 32 := 0x00e6a023.
Lemma F_da368 : fetch_word Asan.M.loaded_segments (0xda4cc : word) = Some W_da368.
Proof. vm_refl. Qed.
Lemma D_da368 : decode_any W_da368 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da36c : bv 32 := 0x00468693.
Lemma F_da36c : fetch_word Asan.M.loaded_segments (0xda4d0 : word) = Some W_da36c.
Proof. vm_refl. Qed.
Lemma D_da36c : decode_any W_da36c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da370 : bv 32 := 0x22c0006f.
Lemma F_da370 : fetch_word Asan.M.loaded_segments (0xda4d4 : word) = Some W_da370.
Proof. vm_refl. Qed.
Lemma D_da370 : decode_any W_da370 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da374 : bv 32 := 0x00e68023.
Lemma F_da374 : fetch_word Asan.M.loaded_segments (0xda4d8 : word) = Some W_da374.
Proof. vm_refl. Qed.
Lemma D_da374 : decode_any W_da374 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da378 : bv 32 := 0x00168693.
Lemma F_da378 : fetch_word Asan.M.loaded_segments (0xda4dc : word) = Some W_da378.
Proof. vm_refl. Qed.
Lemma D_da378 : decode_any W_da378 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da37c : bv 32 := 0xfff60613.
Lemma F_da37c : fetch_word Asan.M.loaded_segments (0xda4e0 : word) = Some W_da37c.
Proof. vm_refl. Qed.
Lemma D_da37c : decode_any W_da37c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da380 : bv 32 := 0x01058593.
Lemma F_da380 : fetch_word Asan.M.loaded_segments (0xda4e4 : word) = Some W_da380.
Proof. vm_refl. Qed.
Lemma D_da380 : decode_any W_da380 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da384 : bv 32 := 0x01200793.
Lemma F_da384 : fetch_word Asan.M.loaded_segments (0xda4e8 : word) = Some W_da384.
Proof. vm_refl. Qed.
Lemma D_da384 : decode_any W_da384 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da388 : bv 32 := 0x0087581b.
Lemma F_da388 : fetch_word Asan.M.loaded_segments (0xda4ec : word) = Some W_da388.
Proof. vm_refl. Qed.
Lemma D_da388 : decode_any W_da388 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da38c : bv 32 := 0xff45a883.
Lemma F_da38c : fetch_word Asan.M.loaded_segments (0xda4f0 : word) = Some W_da38c.
Proof. vm_refl. Qed.
Lemma D_da38c : decode_any W_da38c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da390 : bv 32 := 0xff85a283.
Lemma F_da390 : fetch_word Asan.M.loaded_segments (0xda4f4 : word) = Some W_da390.
Proof. vm_refl. Qed.
Lemma D_da390 : decode_any W_da390 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da394 : bv 32 := 0xffc5a303.
Lemma F_da394 : fetch_word Asan.M.loaded_segments (0xda4f8 : word) = Some W_da394.
Proof. vm_refl. Qed.
Lemma D_da394 : decode_any W_da394 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da398 : bv 32 := 0x0005a703.
Lemma F_da398 : fetch_word Asan.M.loaded_segments (0xda4fc : word) = Some W_da398.
Proof. vm_refl. Qed.
Lemma D_da398 : decode_any W_da398 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da39c : bv 32 := 0x01889393.
Lemma F_da39c : fetch_word Asan.M.loaded_segments (0xda500 : word) = Some W_da39c.
Proof. vm_refl. Qed.
Lemma D_da39c : decode_any W_da39c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3a0 : bv 32 := 0x0088d89b.
Lemma F_da3a0 : fetch_word Asan.M.loaded_segments (0xda504 : word) = Some W_da3a0.
Proof. vm_refl. Qed.
Lemma D_da3a0 : decode_any W_da3a0 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3a4 : bv 32 := 0x0103e833.
Lemma F_da3a4 : fetch_word Asan.M.loaded_segments (0xda508 : word) = Some W_da3a4.
Proof. vm_refl. Qed.
Lemma D_da3a4 : decode_any W_da3a4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3a8 : bv 32 := 0x01829393.
Lemma F_da3a8 : fetch_word Asan.M.loaded_segments (0xda50c : word) = Some W_da3a8.
Proof. vm_refl. Qed.
Lemma D_da3a8 : decode_any W_da3a8 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3ac : bv 32 := 0x0082d29b.
Lemma F_da3ac : fetch_word Asan.M.loaded_segments (0xda510 : word) = Some W_da3ac.
Proof. vm_refl. Qed.
Lemma D_da3ac : decode_any W_da3ac = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3b0 : bv 32 := 0x0113e8b3.
Lemma F_da3b0 : fetch_word Asan.M.loaded_segments (0xda514 : word) = Some W_da3b0.
Proof. vm_refl. Qed.
Lemma D_da3b0 : decode_any W_da3b0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3b4 : bv 32 := 0x01831393.
Lemma F_da3b4 : fetch_word Asan.M.loaded_segments (0xda518 : word) = Some W_da3b4.
Proof. vm_refl. Qed.
Lemma D_da3b4 : decode_any W_da3b4 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3b8 : bv 32 := 0x0083531b.
Lemma F_da3b8 : fetch_word Asan.M.loaded_segments (0xda51c : word) = Some W_da3b8.
Proof. vm_refl. Qed.
Lemma D_da3b8 : decode_any W_da3b8 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3bc : bv 32 := 0x0053e2b3.
Lemma F_da3bc : fetch_word Asan.M.loaded_segments (0xda520 : word) = Some W_da3bc.
Proof. vm_refl. Qed.
Lemma D_da3bc : decode_any W_da3bc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3c0 : bv 32 := 0x01871393.
Lemma F_da3c0 : fetch_word Asan.M.loaded_segments (0xda524 : word) = Some W_da3c0.
Proof. vm_refl. Qed.
Lemma D_da3c0 : decode_any W_da3c0 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3c4 : bv 32 := 0x0063e333.
Lemma F_da3c4 : fetch_word Asan.M.loaded_segments (0xda528 : word) = Some W_da3c4.
Proof. vm_refl. Qed.
Lemma D_da3c4 : decode_any W_da3c4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3c8 : bv 32 := 0xff060613.
Lemma F_da3c8 : fetch_word Asan.M.loaded_segments (0xda52c : word) = Some W_da3c8.
Proof. vm_refl. Qed.
Lemma D_da3c8 : decode_any W_da3c8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3cc : bv 32 := 0x0106a023.
Lemma F_da3cc : fetch_word Asan.M.loaded_segments (0xda530 : word) = Some W_da3cc.
Proof. vm_refl. Qed.
Lemma D_da3cc : decode_any W_da3cc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3d0 : bv 32 := 0x0116a223.
Lemma F_da3d0 : fetch_word Asan.M.loaded_segments (0xda534 : word) = Some W_da3d0.
Proof. vm_refl. Qed.
Lemma D_da3d0 : decode_any W_da3d0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3d4 : bv 32 := 0x0056a423.
Lemma F_da3d4 : fetch_word Asan.M.loaded_segments (0xda538 : word) = Some W_da3d4.
Proof. vm_refl. Qed.
Lemma D_da3d4 : decode_any W_da3d4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3d8 : bv 32 := 0x0066a623.
Lemma F_da3d8 : fetch_word Asan.M.loaded_segments (0xda53c : word) = Some W_da3d8.
Proof. vm_refl. Qed.
Lemma D_da3d8 : decode_any W_da3d8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3dc : bv 32 := 0x01068693.
Lemma F_da3dc : fetch_word Asan.M.loaded_segments (0xda540 : word) = Some W_da3dc.
Proof. vm_refl. Qed.
Lemma D_da3dc : decode_any W_da3dc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3e0 : bv 32 := 0x01058593.
Lemma F_da3e0 : fetch_word Asan.M.loaded_segments (0xda544 : word) = Some W_da3e0.
Proof. vm_refl. Qed.
Lemma D_da3e0 : decode_any W_da3e0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3e4 : bv 32 := 0xfac7e2e3.
Lemma F_da3e4 : fetch_word Asan.M.loaded_segments (0xda548 : word) = Some W_da3e4.
Proof. vm_refl. Qed.
Lemma D_da3e4 : decode_any W_da3e4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3e8 : bv 32 := 0xff158593.
Lemma F_da3e8 : fetch_word Asan.M.loaded_segments (0xda54c : word) = Some W_da3e8.
Proof. vm_refl. Qed.
Lemma D_da3e8 : decode_any W_da3e8 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3ec : bv 32 := 0x01000713.
Lemma F_da3ec : fetch_word Asan.M.loaded_segments (0xda550 : word) = Some W_da3ec.
Proof. vm_refl. Qed.
Lemma D_da3ec : decode_any W_da3ec = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3f0 : bv 32 := 0xe4e666e3.
Lemma F_da3f0 : fetch_word Asan.M.loaded_segments (0xda554 : word) = Some W_da3f0.
Proof. vm_refl. Qed.
Lemma D_da3f0 : decode_any W_da3f0 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3f4 : bv 32 := 0x0940006f.
Lemma F_da3f4 : fetch_word Asan.M.loaded_segments (0xda558 : word) = Some W_da3f4.
Proof. vm_refl. Qed.
Lemma D_da3f4 : decode_any W_da3f4 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3f8 : bv 32 := 0x00875793.
Lemma F_da3f8 : fetch_word Asan.M.loaded_segments (0xda55c : word) = Some W_da3f8.
Proof. vm_refl. Qed.
Lemma D_da3f8 : decode_any W_da3f8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da3fc : bv 32 := 0x01075813.
Lemma F_da3fc : fetch_word Asan.M.loaded_segments (0xda560 : word) = Some W_da3fc.
Proof. vm_refl. Qed.
Lemma D_da3fc : decode_any W_da3fc = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da400 : bv 32 := 0xffd60613.
Lemma F_da400 : fetch_word Asan.M.loaded_segments (0xda564 : word) = Some W_da400.
Proof. vm_refl. Qed.
Lemma D_da400 : decode_any W_da400 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da404 : bv 32 := 0x00e68023.
Lemma F_da404 : fetch_word Asan.M.loaded_segments (0xda568 : word) = Some W_da404.
Proof. vm_refl. Qed.
Lemma D_da404 : decode_any W_da404 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da408 : bv 32 := 0x00f680a3.
Lemma F_da408 : fetch_word Asan.M.loaded_segments (0xda56c : word) = Some W_da408.
Proof. vm_refl. Qed.
Lemma D_da408 : decode_any W_da408 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da40c : bv 32 := 0x01068123.
Lemma F_da40c : fetch_word Asan.M.loaded_segments (0xda570 : word) = Some W_da40c.
Proof. vm_refl. Qed.
Lemma D_da40c : decode_any W_da40c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da410 : bv 32 := 0x00368693.
Lemma F_da410 : fetch_word Asan.M.loaded_segments (0xda574 : word) = Some W_da410.
Proof. vm_refl. Qed.
Lemma D_da410 : decode_any W_da410 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da414 : bv 32 := 0x01058593.
Lemma F_da414 : fetch_word Asan.M.loaded_segments (0xda578 : word) = Some W_da414.
Proof. vm_refl. Qed.
Lemma D_da414 : decode_any W_da414 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da418 : bv 32 := 0x01000793.
Lemma F_da418 : fetch_word Asan.M.loaded_segments (0xda57c : word) = Some W_da418.
Proof. vm_refl. Qed.
Lemma D_da418 : decode_any W_da418 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da41c : bv 32 := 0x0187581b.
Lemma F_da41c : fetch_word Asan.M.loaded_segments (0xda580 : word) = Some W_da41c.
Proof. vm_refl. Qed.
Lemma D_da41c : decode_any W_da41c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da420 : bv 32 := 0xff45a883.
Lemma F_da420 : fetch_word Asan.M.loaded_segments (0xda584 : word) = Some W_da420.
Proof. vm_refl. Qed.
Lemma D_da420 : decode_any W_da420 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da424 : bv 32 := 0xff85a283.
Lemma F_da424 : fetch_word Asan.M.loaded_segments (0xda588 : word) = Some W_da424.
Proof. vm_refl. Qed.
Lemma D_da424 : decode_any W_da424 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da428 : bv 32 := 0xffc5a303.
Lemma F_da428 : fetch_word Asan.M.loaded_segments (0xda58c : word) = Some W_da428.
Proof. vm_refl. Qed.
Lemma D_da428 : decode_any W_da428 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da42c : bv 32 := 0x0005a703.
Lemma F_da42c : fetch_word Asan.M.loaded_segments (0xda590 : word) = Some W_da42c.
Proof. vm_refl. Qed.
Lemma D_da42c : decode_any W_da42c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da430 : bv 32 := 0x00889393.
Lemma F_da430 : fetch_word Asan.M.loaded_segments (0xda594 : word) = Some W_da430.
Proof. vm_refl. Qed.
Lemma D_da430 : decode_any W_da430 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da434 : bv 32 := 0x0188d89b.
Lemma F_da434 : fetch_word Asan.M.loaded_segments (0xda598 : word) = Some W_da434.
Proof. vm_refl. Qed.
Lemma D_da434 : decode_any W_da434 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da438 : bv 32 := 0x0103e833.
Lemma F_da438 : fetch_word Asan.M.loaded_segments (0xda59c : word) = Some W_da438.
Proof. vm_refl. Qed.
Lemma D_da438 : decode_any W_da438 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da43c : bv 32 := 0x00829393.
Lemma F_da43c : fetch_word Asan.M.loaded_segments (0xda5a0 : word) = Some W_da43c.
Proof. vm_refl. Qed.
Lemma D_da43c : decode_any W_da43c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da440 : bv 32 := 0x0182d29b.
Lemma F_da440 : fetch_word Asan.M.loaded_segments (0xda5a4 : word) = Some W_da440.
Proof. vm_refl. Qed.
Lemma D_da440 : decode_any W_da440 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da444 : bv 32 := 0x0113e8b3.
Lemma F_da444 : fetch_word Asan.M.loaded_segments (0xda5a8 : word) = Some W_da444.
Proof. vm_refl. Qed.
Lemma D_da444 : decode_any W_da444 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da448 : bv 32 := 0x00831393.
Lemma F_da448 : fetch_word Asan.M.loaded_segments (0xda5ac : word) = Some W_da448.
Proof. vm_refl. Qed.
Lemma D_da448 : decode_any W_da448 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da44c : bv 32 := 0x0183531b.
Lemma F_da44c : fetch_word Asan.M.loaded_segments (0xda5b0 : word) = Some W_da44c.
Proof. vm_refl. Qed.
Lemma D_da44c : decode_any W_da44c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da450 : bv 32 := 0x0053e2b3.
Lemma F_da450 : fetch_word Asan.M.loaded_segments (0xda5b4 : word) = Some W_da450.
Proof. vm_refl. Qed.
Lemma D_da450 : decode_any W_da450 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da454 : bv 32 := 0x00871393.
Lemma F_da454 : fetch_word Asan.M.loaded_segments (0xda5b8 : word) = Some W_da454.
Proof. vm_refl. Qed.
Lemma D_da454 : decode_any W_da454 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da458 : bv 32 := 0x0063e333.
Lemma F_da458 : fetch_word Asan.M.loaded_segments (0xda5bc : word) = Some W_da458.
Proof. vm_refl. Qed.
Lemma D_da458 : decode_any W_da458 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da45c : bv 32 := 0xff060613.
Lemma F_da45c : fetch_word Asan.M.loaded_segments (0xda5c0 : word) = Some W_da45c.
Proof. vm_refl. Qed.
Lemma D_da45c : decode_any W_da45c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da460 : bv 32 := 0x0106a023.
Lemma F_da460 : fetch_word Asan.M.loaded_segments (0xda5c4 : word) = Some W_da460.
Proof. vm_refl. Qed.
Lemma D_da460 : decode_any W_da460 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da464 : bv 32 := 0x0116a223.
Lemma F_da464 : fetch_word Asan.M.loaded_segments (0xda5c8 : word) = Some W_da464.
Proof. vm_refl. Qed.
Lemma D_da464 : decode_any W_da464 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da468 : bv 32 := 0x0056a423.
Lemma F_da468 : fetch_word Asan.M.loaded_segments (0xda5cc : word) = Some W_da468.
Proof. vm_refl. Qed.
Lemma D_da468 : decode_any W_da468 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da46c : bv 32 := 0x0066a623.
Lemma F_da46c : fetch_word Asan.M.loaded_segments (0xda5d0 : word) = Some W_da46c.
Proof. vm_refl. Qed.
Lemma D_da46c : decode_any W_da46c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da470 : bv 32 := 0x01068693.
Lemma F_da470 : fetch_word Asan.M.loaded_segments (0xda5d4 : word) = Some W_da470.
Proof. vm_refl. Qed.
Lemma D_da470 : decode_any W_da470 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da474 : bv 32 := 0x01058593.
Lemma F_da474 : fetch_word Asan.M.loaded_segments (0xda5d8 : word) = Some W_da474.
Proof. vm_refl. Qed.
Lemma D_da474 : decode_any W_da474 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da478 : bv 32 := 0xfac7e2e3.
Lemma F_da478 : fetch_word Asan.M.loaded_segments (0xda5dc : word) = Some W_da478.
Proof. vm_refl. Qed.
Lemma D_da478 : decode_any W_da478 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da47c : bv 32 := 0xff358593.
Lemma F_da47c : fetch_word Asan.M.loaded_segments (0xda5e0 : word) = Some W_da47c.
Proof. vm_refl. Qed.
Lemma D_da47c : decode_any W_da47c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da480 : bv 32 := 0x01000713.
Lemma F_da480 : fetch_word Asan.M.loaded_segments (0xda5e4 : word) = Some W_da480.
Proof. vm_refl. Qed.
Lemma D_da480 : decode_any W_da480 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da484 : bv 32 := 0xdae66ce3.
Lemma F_da484 : fetch_word Asan.M.loaded_segments (0xda5e8 : word) = Some W_da484.
Proof. vm_refl. Qed.
Lemma D_da484 : decode_any W_da484 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da488 : bv 32 := 0x0005c703.
Lemma F_da488 : fetch_word Asan.M.loaded_segments (0xda5ec : word) = Some W_da488.
Proof. vm_refl. Qed.
Lemma D_da488 : decode_any W_da488 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da48c : bv 32 := 0x0015c783.
Lemma F_da48c : fetch_word Asan.M.loaded_segments (0xda5f0 : word) = Some W_da48c.
Proof. vm_refl. Qed.
Lemma D_da48c : decode_any W_da48c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da490 : bv 32 := 0x0025c803.
Lemma F_da490 : fetch_word Asan.M.loaded_segments (0xda5f4 : word) = Some W_da490.
Proof. vm_refl. Qed.
Lemma D_da490 : decode_any W_da490 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da494 : bv 32 := 0x0035c883.
Lemma F_da494 : fetch_word Asan.M.loaded_segments (0xda5f8 : word) = Some W_da494.
Proof. vm_refl. Qed.
Lemma D_da494 : decode_any W_da494 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da498 : bv 32 := 0x0045c283.
Lemma F_da498 : fetch_word Asan.M.loaded_segments (0xda5fc : word) = Some W_da498.
Proof. vm_refl. Qed.
Lemma D_da498 : decode_any W_da498 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da49c : bv 32 := 0x0055c303.
Lemma F_da49c : fetch_word Asan.M.loaded_segments (0xda600 : word) = Some W_da49c.
Proof. vm_refl. Qed.
Lemma D_da49c : decode_any W_da49c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4a0 : bv 32 := 0x0065c383.
Lemma F_da4a0 : fetch_word Asan.M.loaded_segments (0xda604 : word) = Some W_da4a0.
Proof. vm_refl. Qed.
Lemma D_da4a0 : decode_any W_da4a0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4a4 : bv 32 := 0x0075ce03.
Lemma F_da4a4 : fetch_word Asan.M.loaded_segments (0xda608 : word) = Some W_da4a4.
Proof. vm_refl. Qed.
Lemma D_da4a4 : decode_any W_da4a4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4a8 : bv 32 := 0x00e68023.
Lemma F_da4a8 : fetch_word Asan.M.loaded_segments (0xda60c : word) = Some W_da4a8.
Proof. vm_refl. Qed.
Lemma D_da4a8 : decode_any W_da4a8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4ac : bv 32 := 0x00f680a3.
Lemma F_da4ac : fetch_word Asan.M.loaded_segments (0xda610 : word) = Some W_da4ac.
Proof. vm_refl. Qed.
Lemma D_da4ac : decode_any W_da4ac = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4b0 : bv 32 := 0x01068123.
Lemma F_da4b0 : fetch_word Asan.M.loaded_segments (0xda614 : word) = Some W_da4b0.
Proof. vm_refl. Qed.
Lemma D_da4b0 : decode_any W_da4b0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4b4 : bv 32 := 0x011681a3.
Lemma F_da4b4 : fetch_word Asan.M.loaded_segments (0xda618 : word) = Some W_da4b4.
Proof. vm_refl. Qed.
Lemma D_da4b4 : decode_any W_da4b4 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4b8 : bv 32 := 0x0085c703.
Lemma F_da4b8 : fetch_word Asan.M.loaded_segments (0xda61c : word) = Some W_da4b8.
Proof. vm_refl. Qed.
Lemma D_da4b8 : decode_any W_da4b8 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4bc : bv 32 := 0x0095c783.
Lemma F_da4bc : fetch_word Asan.M.loaded_segments (0xda620 : word) = Some W_da4bc.
Proof. vm_refl. Qed.
Lemma D_da4bc : decode_any W_da4bc = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4c0 : bv 32 := 0x00a5c803.
Lemma F_da4c0 : fetch_word Asan.M.loaded_segments (0xda624 : word) = Some W_da4c0.
Proof. vm_refl. Qed.
Lemma D_da4c0 : decode_any W_da4c0 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4c4 : bv 32 := 0x00b5c883.
Lemma F_da4c4 : fetch_word Asan.M.loaded_segments (0xda628 : word) = Some W_da4c4.
Proof. vm_refl. Qed.
Lemma D_da4c4 : decode_any W_da4c4 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4c8 : bv 32 := 0x00568223.
Lemma F_da4c8 : fetch_word Asan.M.loaded_segments (0xda62c : word) = Some W_da4c8.
Proof. vm_refl. Qed.
Lemma D_da4c8 : decode_any W_da4c8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4cc : bv 32 := 0x006682a3.
Lemma F_da4cc : fetch_word Asan.M.loaded_segments (0xda630 : word) = Some W_da4cc.
Proof. vm_refl. Qed.
Lemma D_da4cc : decode_any W_da4cc = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4d0 : bv 32 := 0x00768323.
Lemma F_da4d0 : fetch_word Asan.M.loaded_segments (0xda634 : word) = Some W_da4d0.
Proof. vm_refl. Qed.
Lemma D_da4d0 : decode_any W_da4d0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4d4 : bv 32 := 0x01c683a3.
Lemma F_da4d4 : fetch_word Asan.M.loaded_segments (0xda638 : word) = Some W_da4d4.
Proof. vm_refl. Qed.
Lemma D_da4d4 : decode_any W_da4d4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4d8 : bv 32 := 0x00c5c283.
Lemma F_da4d8 : fetch_word Asan.M.loaded_segments (0xda63c : word) = Some W_da4d8.
Proof. vm_refl. Qed.
Lemma D_da4d8 : decode_any W_da4d8 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4dc : bv 32 := 0x00d5c303.
Lemma F_da4dc : fetch_word Asan.M.loaded_segments (0xda640 : word) = Some W_da4dc.
Proof. vm_refl. Qed.
Lemma D_da4dc : decode_any W_da4dc = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4e0 : bv 32 := 0x00e5c383.
Lemma F_da4e0 : fetch_word Asan.M.loaded_segments (0xda644 : word) = Some W_da4e0.
Proof. vm_refl. Qed.
Lemma D_da4e0 : decode_any W_da4e0 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4e4 : bv 32 := 0x00f5ce03.
Lemma F_da4e4 : fetch_word Asan.M.loaded_segments (0xda648 : word) = Some W_da4e4.
Proof. vm_refl. Qed.
Lemma D_da4e4 : decode_any W_da4e4 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4e8 : bv 32 := 0x01058593.
Lemma F_da4e8 : fetch_word Asan.M.loaded_segments (0xda64c : word) = Some W_da4e8.
Proof. vm_refl. Qed.
Lemma D_da4e8 : decode_any W_da4e8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4ec : bv 32 := 0x00e68423.
Lemma F_da4ec : fetch_word Asan.M.loaded_segments (0xda650 : word) = Some W_da4ec.
Proof. vm_refl. Qed.
Lemma D_da4ec : decode_any W_da4ec = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4f0 : bv 32 := 0x00f684a3.
Lemma F_da4f0 : fetch_word Asan.M.loaded_segments (0xda654 : word) = Some W_da4f0.
Proof. vm_refl. Qed.
Lemma D_da4f0 : decode_any W_da4f0 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4f4 : bv 32 := 0x01068523.
Lemma F_da4f4 : fetch_word Asan.M.loaded_segments (0xda658 : word) = Some W_da4f4.
Proof. vm_refl. Qed.
Lemma D_da4f4 : decode_any W_da4f4 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4f8 : bv 32 := 0x011685a3.
Lemma F_da4f8 : fetch_word Asan.M.loaded_segments (0xda65c : word) = Some W_da4f8.
Proof. vm_refl. Qed.
Lemma D_da4f8 : decode_any W_da4f8 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da4fc : bv 32 := 0x01068713.
Lemma F_da4fc : fetch_word Asan.M.loaded_segments (0xda660 : word) = Some W_da4fc.
Proof. vm_refl. Qed.
Lemma D_da4fc : decode_any W_da4fc = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da500 : bv 32 := 0x00568623.
Lemma F_da500 : fetch_word Asan.M.loaded_segments (0xda664 : word) = Some W_da500.
Proof. vm_refl. Qed.
Lemma D_da500 : decode_any W_da500 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da504 : bv 32 := 0x006686a3.
Lemma F_da504 : fetch_word Asan.M.loaded_segments (0xda668 : word) = Some W_da504.
Proof. vm_refl. Qed.
Lemma D_da504 : decode_any W_da504 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da508 : bv 32 := 0x00768723.
Lemma F_da508 : fetch_word Asan.M.loaded_segments (0xda66c : word) = Some W_da508.
Proof. vm_refl. Qed.
Lemma D_da508 : decode_any W_da508 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da50c : bv 32 := 0x01c687a3.
Lemma F_da50c : fetch_word Asan.M.loaded_segments (0xda670 : word) = Some W_da50c.
Proof. vm_refl. Qed.
Lemma D_da50c : decode_any W_da50c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da510 : bv 32 := 0x00070693.
Lemma F_da510 : fetch_word Asan.M.loaded_segments (0xda674 : word) = Some W_da510.
Proof. vm_refl. Qed.
Lemma D_da510 : decode_any W_da510 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da514 : bv 32 := 0x00867713.
Lemma F_da514 : fetch_word Asan.M.loaded_segments (0xda678 : word) = Some W_da514.
Proof. vm_refl. Qed.
Lemma D_da514 : decode_any W_da514 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da518 : bv 32 := 0xd20706e3.
Lemma F_da518 : fetch_word Asan.M.loaded_segments (0xda67c : word) = Some W_da518.
Proof. vm_refl. Qed.
Lemma D_da518 : decode_any W_da518 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da51c : bv 32 := 0x0005c703.
Lemma F_da51c : fetch_word Asan.M.loaded_segments (0xda680 : word) = Some W_da51c.
Proof. vm_refl. Qed.
Lemma D_da51c : decode_any W_da51c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da520 : bv 32 := 0x0015c783.
Lemma F_da520 : fetch_word Asan.M.loaded_segments (0xda684 : word) = Some W_da520.
Proof. vm_refl. Qed.
Lemma D_da520 : decode_any W_da520 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da524 : bv 32 := 0x0025c803.
Lemma F_da524 : fetch_word Asan.M.loaded_segments (0xda688 : word) = Some W_da524.
Proof. vm_refl. Qed.
Lemma D_da524 : decode_any W_da524 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da528 : bv 32 := 0x0035c883.
Lemma F_da528 : fetch_word Asan.M.loaded_segments (0xda68c : word) = Some W_da528.
Proof. vm_refl. Qed.
Lemma D_da528 : decode_any W_da528 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da52c : bv 32 := 0x0045c283.
Lemma F_da52c : fetch_word Asan.M.loaded_segments (0xda690 : word) = Some W_da52c.
Proof. vm_refl. Qed.
Lemma D_da52c : decode_any W_da52c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da530 : bv 32 := 0x0055c303.
Lemma F_da530 : fetch_word Asan.M.loaded_segments (0xda694 : word) = Some W_da530.
Proof. vm_refl. Qed.
Lemma D_da530 : decode_any W_da530 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da534 : bv 32 := 0x0065c383.
Lemma F_da534 : fetch_word Asan.M.loaded_segments (0xda698 : word) = Some W_da534.
Proof. vm_refl. Qed.
Lemma D_da534 : decode_any W_da534 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da538 : bv 32 := 0x0075ce03.
Lemma F_da538 : fetch_word Asan.M.loaded_segments (0xda69c : word) = Some W_da538.
Proof. vm_refl. Qed.
Lemma D_da538 : decode_any W_da538 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da53c : bv 32 := 0x00858593.
Lemma F_da53c : fetch_word Asan.M.loaded_segments (0xda6a0 : word) = Some W_da53c.
Proof. vm_refl. Qed.
Lemma D_da53c : decode_any W_da53c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da540 : bv 32 := 0x00e68023.
Lemma F_da540 : fetch_word Asan.M.loaded_segments (0xda6a4 : word) = Some W_da540.
Proof. vm_refl. Qed.
Lemma D_da540 : decode_any W_da540 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da544 : bv 32 := 0x00f680a3.
Lemma F_da544 : fetch_word Asan.M.loaded_segments (0xda6a8 : word) = Some W_da544.
Proof. vm_refl. Qed.
Lemma D_da544 : decode_any W_da544 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da548 : bv 32 := 0x01068123.
Lemma F_da548 : fetch_word Asan.M.loaded_segments (0xda6ac : word) = Some W_da548.
Proof. vm_refl. Qed.
Lemma D_da548 : decode_any W_da548 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da54c : bv 32 := 0x011681a3.
Lemma F_da54c : fetch_word Asan.M.loaded_segments (0xda6b0 : word) = Some W_da54c.
Proof. vm_refl. Qed.
Lemma D_da54c : decode_any W_da54c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da550 : bv 32 := 0x00868713.
Lemma F_da550 : fetch_word Asan.M.loaded_segments (0xda6b4 : word) = Some W_da550.
Proof. vm_refl. Qed.
Lemma D_da550 : decode_any W_da550 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da554 : bv 32 := 0x00568223.
Lemma F_da554 : fetch_word Asan.M.loaded_segments (0xda6b8 : word) = Some W_da554.
Proof. vm_refl. Qed.
Lemma D_da554 : decode_any W_da554 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da558 : bv 32 := 0x006682a3.
Lemma F_da558 : fetch_word Asan.M.loaded_segments (0xda6bc : word) = Some W_da558.
Proof. vm_refl. Qed.
Lemma D_da558 : decode_any W_da558 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da55c : bv 32 := 0x00768323.
Lemma F_da55c : fetch_word Asan.M.loaded_segments (0xda6c0 : word) = Some W_da55c.
Proof. vm_refl. Qed.
Lemma D_da55c : decode_any W_da55c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da560 : bv 32 := 0x01c683a3.
Lemma F_da560 : fetch_word Asan.M.loaded_segments (0xda6c4 : word) = Some W_da560.
Proof. vm_refl. Qed.
Lemma D_da560 : decode_any W_da560 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da564 : bv 32 := 0x00070693.
Lemma F_da564 : fetch_word Asan.M.loaded_segments (0xda6c8 : word) = Some W_da564.
Proof. vm_refl. Qed.
Lemma D_da564 : decode_any W_da564 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da568 : bv 32 := 0x00467713.
Lemma F_da568 : fetch_word Asan.M.loaded_segments (0xda6cc : word) = Some W_da568.
Proof. vm_refl. Qed.
Lemma D_da568 : decode_any W_da568 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da56c : bv 32 := 0x02070863.
Lemma F_da56c : fetch_word Asan.M.loaded_segments (0xda6d0 : word) = Some W_da56c.
Proof. vm_refl. Qed.
Lemma D_da56c : decode_any W_da56c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da570 : bv 32 := 0x0005c703.
Lemma F_da570 : fetch_word Asan.M.loaded_segments (0xda6d4 : word) = Some W_da570.
Proof. vm_refl. Qed.
Lemma D_da570 : decode_any W_da570 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da574 : bv 32 := 0x0015c783.
Lemma F_da574 : fetch_word Asan.M.loaded_segments (0xda6d8 : word) = Some W_da574.
Proof. vm_refl. Qed.
Lemma D_da574 : decode_any W_da574 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da578 : bv 32 := 0x0025c803.
Lemma F_da578 : fetch_word Asan.M.loaded_segments (0xda6dc : word) = Some W_da578.
Proof. vm_refl. Qed.
Lemma D_da578 : decode_any W_da578 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da57c : bv 32 := 0x0035c883.
Lemma F_da57c : fetch_word Asan.M.loaded_segments (0xda6e0 : word) = Some W_da57c.
Proof. vm_refl. Qed.
Lemma D_da57c : decode_any W_da57c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da580 : bv 32 := 0x00458593.
Lemma F_da580 : fetch_word Asan.M.loaded_segments (0xda6e4 : word) = Some W_da580.
Proof. vm_refl. Qed.
Lemma D_da580 : decode_any W_da580 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da584 : bv 32 := 0x00468293.
Lemma F_da584 : fetch_word Asan.M.loaded_segments (0xda6e8 : word) = Some W_da584.
Proof. vm_refl. Qed.
Lemma D_da584 : decode_any W_da584 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da588 : bv 32 := 0x00e68023.
Lemma F_da588 : fetch_word Asan.M.loaded_segments (0xda6ec : word) = Some W_da588.
Proof. vm_refl. Qed.
Lemma D_da588 : decode_any W_da588 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da58c : bv 32 := 0x00f680a3.
Lemma F_da58c : fetch_word Asan.M.loaded_segments (0xda6f0 : word) = Some W_da58c.
Proof. vm_refl. Qed.
Lemma D_da58c : decode_any W_da58c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da590 : bv 32 := 0x01068123.
Lemma F_da590 : fetch_word Asan.M.loaded_segments (0xda6f4 : word) = Some W_da590.
Proof. vm_refl. Qed.
Lemma D_da590 : decode_any W_da590 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da594 : bv 32 := 0x011681a3.
Lemma F_da594 : fetch_word Asan.M.loaded_segments (0xda6f8 : word) = Some W_da594.
Proof. vm_refl. Qed.
Lemma D_da594 : decode_any W_da594 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da598 : bv 32 := 0x00028693.
Lemma F_da598 : fetch_word Asan.M.loaded_segments (0xda6fc : word) = Some W_da598.
Proof. vm_refl. Qed.
Lemma D_da598 : decode_any W_da598 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da59c : bv 32 := 0x00267713.
Lemma F_da59c : fetch_word Asan.M.loaded_segments (0xda700 : word) = Some W_da59c.
Proof. vm_refl. Qed.
Lemma D_da59c : decode_any W_da59c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5a0 : bv 32 := 0x00071863.
Lemma F_da5a0 : fetch_word Asan.M.loaded_segments (0xda704 : word) = Some W_da5a0.
Proof. vm_refl. Qed.
Lemma D_da5a0 : decode_any W_da5a0 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5a4 : bv 32 := 0x00167613.
Lemma F_da5a4 : fetch_word Asan.M.loaded_segments (0xda708 : word) = Some W_da5a4.
Proof. vm_refl. Qed.
Lemma D_da5a4 : decode_any W_da5a4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5a8 : bv 32 := 0x02061663.
Lemma F_da5a8 : fetch_word Asan.M.loaded_segments (0xda70c : word) = Some W_da5a8.
Proof. vm_refl. Qed.
Lemma D_da5a8 : decode_any W_da5a8 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5ac : bv 32 := 0x00008067.
Lemma F_da5ac : fetch_word Asan.M.loaded_segments (0xda710 : word) = Some W_da5ac.
Proof. vm_refl. Qed.
Lemma D_da5ac : decode_any W_da5ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5b0 : bv 32 := 0x0005c703.
Lemma F_da5b0 : fetch_word Asan.M.loaded_segments (0xda714 : word) = Some W_da5b0.
Proof. vm_refl. Qed.
Lemma D_da5b0 : decode_any W_da5b0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5b4 : bv 32 := 0x0015c783.
Lemma F_da5b4 : fetch_word Asan.M.loaded_segments (0xda718 : word) = Some W_da5b4.
Proof. vm_refl. Qed.
Lemma D_da5b4 : decode_any W_da5b4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5b8 : bv 32 := 0x00258593.
Lemma F_da5b8 : fetch_word Asan.M.loaded_segments (0xda71c : word) = Some W_da5b8.
Proof. vm_refl. Qed.
Lemma D_da5b8 : decode_any W_da5b8 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5bc : bv 32 := 0x00268813.
Lemma F_da5bc : fetch_word Asan.M.loaded_segments (0xda720 : word) = Some W_da5bc.
Proof. vm_refl. Qed.
Lemma D_da5bc : decode_any W_da5bc = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5c0 : bv 32 := 0x00e68023.
Lemma F_da5c0 : fetch_word Asan.M.loaded_segments (0xda724 : word) = Some W_da5c0.
Proof. vm_refl. Qed.
Lemma D_da5c0 : decode_any W_da5c0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5c4 : bv 32 := 0x00f680a3.
Lemma F_da5c4 : fetch_word Asan.M.loaded_segments (0xda728 : word) = Some W_da5c4.
Proof. vm_refl. Qed.
Lemma D_da5c4 : decode_any W_da5c4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5c8 : bv 32 := 0x00080693.
Lemma F_da5c8 : fetch_word Asan.M.loaded_segments (0xda72c : word) = Some W_da5c8.
Proof. vm_refl. Qed.
Lemma D_da5c8 : decode_any W_da5c8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5cc : bv 32 := 0x00167613.
Lemma F_da5cc : fetch_word Asan.M.loaded_segments (0xda730 : word) = Some W_da5cc.
Proof. vm_refl. Qed.
Lemma D_da5cc : decode_any W_da5cc = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5d0 : bv 32 := 0xfc060ee3.
Lemma F_da5d0 : fetch_word Asan.M.loaded_segments (0xda734 : word) = Some W_da5d0.
Proof. vm_refl. Qed.
Lemma D_da5d0 : decode_any W_da5d0 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5d4 : bv 32 := 0x0005c583.
Lemma F_da5d4 : fetch_word Asan.M.loaded_segments (0xda738 : word) = Some W_da5d4.
Proof. vm_refl. Qed.
Lemma D_da5d4 : decode_any W_da5d4 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5d8 : bv 32 := 0x00b68023.
Lemma F_da5d8 : fetch_word Asan.M.loaded_segments (0xda73c : word) = Some W_da5d8.
Proof. vm_refl. Qed.
Lemma D_da5d8 : decode_any W_da5d8 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5dc : bv 32 := 0x00008067.
Lemma F_da5dc : fetch_word Asan.M.loaded_segments (0xda740 : word) = Some W_da5dc.
Proof. vm_refl. Qed.
Lemma D_da5dc : decode_any W_da5dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
