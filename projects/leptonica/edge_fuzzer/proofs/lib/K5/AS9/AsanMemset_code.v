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
From OSSVerify.leptonica.edge_fuzzer.images Require Import Asan.
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
Definition W_1b6274 : bv 32 := 0x0e060a63.
Lemma F_1b6274 : fetch_word Asan.M.loaded_segments (0x1b63dc : word) = Some W_1b6274.
Proof. vm_refl. Qed.
Lemma D_1b6274 : decode_any W_1b6274 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6278 : bv 32 := 0x00b50023.
Lemma F_1b6278 : fetch_word Asan.M.loaded_segments (0x1b63e0 : word) = Some W_1b6278.
Proof. vm_refl. Qed.
Lemma D_1b6278 : decode_any W_1b6278 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b627c : bv 32 := 0x00c506b3.
Lemma F_1b627c : fetch_word Asan.M.loaded_segments (0x1b63e4 : word) = Some W_1b627c.
Proof. vm_refl. Qed.
Lemma D_1b627c : decode_any W_1b627c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6280 : bv 32 := 0x00300713.
Lemma F_1b6280 : fetch_word Asan.M.loaded_segments (0x1b63e8 : word) = Some W_1b6280.
Proof. vm_refl. Qed.
Lemma D_1b6280 : decode_any W_1b6280 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6284 : bv 32 := 0xfeb68fa3.
Lemma F_1b6284 : fetch_word Asan.M.loaded_segments (0x1b63ec : word) = Some W_1b6284.
Proof. vm_refl. Qed.
Lemma D_1b6284 : decode_any W_1b6284 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6288 : bv 32 := 0x0ee66063.
Lemma F_1b6288 : fetch_word Asan.M.loaded_segments (0x1b63f0 : word) = Some W_1b6288.
Proof. vm_refl. Qed.
Lemma D_1b6288 : decode_any W_1b6288 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b628c : bv 32 := 0x00b500a3.
Lemma F_1b628c : fetch_word Asan.M.loaded_segments (0x1b63f4 : word) = Some W_1b628c.
Proof. vm_refl. Qed.
Lemma D_1b628c : decode_any W_1b628c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6290 : bv 32 := 0x00b50123.
Lemma F_1b6290 : fetch_word Asan.M.loaded_segments (0x1b63f8 : word) = Some W_1b6290.
Proof. vm_refl. Qed.
Lemma D_1b6290 : decode_any W_1b6290 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6294 : bv 32 := 0x00700713.
Lemma F_1b6294 : fetch_word Asan.M.loaded_segments (0x1b63fc : word) = Some W_1b6294.
Proof. vm_refl. Qed.
Lemma D_1b6294 : decode_any W_1b6294 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6298 : bv 32 := 0xfeb68ea3.
Lemma F_1b6298 : fetch_word Asan.M.loaded_segments (0x1b6400 : word) = Some W_1b6298.
Proof. vm_refl. Qed.
Lemma D_1b6298 : decode_any W_1b6298 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b629c : bv 32 := 0xfeb68f23.
Lemma F_1b629c : fetch_word Asan.M.loaded_segments (0x1b6404 : word) = Some W_1b629c.
Proof. vm_refl. Qed.
Lemma D_1b629c : decode_any W_1b629c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62a0 : bv 32 := 0x0ce66463.
Lemma F_1b62a0 : fetch_word Asan.M.loaded_segments (0x1b6408 : word) = Some W_1b62a0.
Proof. vm_refl. Qed.
Lemma D_1b62a0 : decode_any W_1b62a0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62a4 : bv 32 := 0x00b501a3.
Lemma F_1b62a4 : fetch_word Asan.M.loaded_segments (0x1b640c : word) = Some W_1b62a4.
Proof. vm_refl. Qed.
Lemma D_1b62a4 : decode_any W_1b62a4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62a8 : bv 32 := 0x00900793.
Lemma F_1b62a8 : fetch_word Asan.M.loaded_segments (0x1b6410 : word) = Some W_1b62a8.
Proof. vm_refl. Qed.
Lemma D_1b62a8 : decode_any W_1b62a8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62ac : bv 32 := 0xfeb68e23.
Lemma F_1b62ac : fetch_word Asan.M.loaded_segments (0x1b6414 : word) = Some W_1b62ac.
Proof. vm_refl. Qed.
Lemma D_1b62ac : decode_any W_1b62ac = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62b0 : bv 32 := 0x0af66c63.
Lemma F_1b62b0 : fetch_word Asan.M.loaded_segments (0x1b6418 : word) = Some W_1b62b0.
Proof. vm_refl. Qed.
Lemma D_1b62b0 : decode_any W_1b62b0 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62b4 : bv 32 := 0x40a006bb.
Lemma F_1b62b4 : fetch_word Asan.M.loaded_segments (0x1b641c : word) = Some W_1b62b4.
Proof. vm_refl. Qed.
Lemma D_1b62b4 : decode_any W_1b62b4 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62b8 : bv 32 := 0x03859813.
Lemma F_1b62b8 : fetch_word Asan.M.loaded_segments (0x1b6420 : word) = Some W_1b62b8.
Proof. vm_refl. Qed.
Lemma D_1b62b8 : decode_any W_1b62b8 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62bc : bv 32 := 0x101015b7.
Lemma F_1b62bc : fetch_word Asan.M.loaded_segments (0x1b6424 : word) = Some W_1b62bc.
Proof. vm_refl. Qed.
Lemma D_1b62bc : decode_any W_1b62bc = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62c0 : bv 32 := 0x0036f693.
Lemma F_1b62c0 : fetch_word Asan.M.loaded_segments (0x1b6428 : word) = Some W_1b62c0.
Proof. vm_refl. Qed.
Lemma D_1b62c0 : decode_any W_1b62c0 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62c4 : bv 32 := 0x00459713.
Lemma F_1b62c4 : fetch_word Asan.M.loaded_segments (0x1b642c : word) = Some W_1b62c4.
Proof. vm_refl. Qed.
Lemma D_1b62c4 : decode_any W_1b62c4 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62c8 : bv 32 := 0x40d60633.
Lemma F_1b62c8 : fetch_word Asan.M.loaded_segments (0x1b6430 : word) = Some W_1b62c8.
Proof. vm_refl. Qed.
Lemma D_1b62c8 : decode_any W_1b62c8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62cc : bv 32 := 0x00d505b3.
Lemma F_1b62cc : fetch_word Asan.M.loaded_segments (0x1b6434 : word) = Some W_1b62cc.
Proof. vm_refl. Qed.
Lemma D_1b62cc : decode_any W_1b62cc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62d0 : bv 32 := 0x10070693.
Lemma F_1b62d0 : fetch_word Asan.M.loaded_segments (0x1b6438 : word) = Some W_1b62d0.
Proof. vm_refl. Qed.
Lemma D_1b62d0 : decode_any W_1b62d0 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62d4 : bv 32 := 0xffc67713.
Lemma F_1b62d4 : fetch_word Asan.M.loaded_segments (0x1b643c : word) = Some W_1b62d4.
Proof. vm_refl. Qed.
Lemma D_1b62d4 : decode_any W_1b62d4 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62d8 : bv 32 := 0x02d83633.
Lemma F_1b62d8 : fetch_word Asan.M.loaded_segments (0x1b6440 : word) = Some W_1b62d8.
Proof. vm_refl. Qed.
Lemma D_1b62d8 : decode_any W_1b62d8 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62dc : bv 32 := 0x00c5a023.
Lemma F_1b62dc : fetch_word Asan.M.loaded_segments (0x1b6444 : word) = Some W_1b62dc.
Proof. vm_refl. Qed.
Lemma D_1b62dc : decode_any W_1b62dc = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62e0 : bv 32 := 0x00e586b3.
Lemma F_1b62e0 : fetch_word Asan.M.loaded_segments (0x1b6448 : word) = Some W_1b62e0.
Proof. vm_refl. Qed.
Lemma D_1b62e0 : decode_any W_1b62e0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62e4 : bv 32 := 0xfec6ae23.
Lemma F_1b62e4 : fetch_word Asan.M.loaded_segments (0x1b644c : word) = Some W_1b62e4.
Proof. vm_refl. Qed.
Lemma D_1b62e4 : decode_any W_1b62e4 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62e8 : bv 32 := 0x08f76063.
Lemma F_1b62e8 : fetch_word Asan.M.loaded_segments (0x1b6450 : word) = Some W_1b62e8.
Proof. vm_refl. Qed.
Lemma D_1b62e8 : decode_any W_1b62e8 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62ec : bv 32 := 0x00c5a223.
Lemma F_1b62ec : fetch_word Asan.M.loaded_segments (0x1b6454 : word) = Some W_1b62ec.
Proof. vm_refl. Qed.
Lemma D_1b62ec : decode_any W_1b62ec = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62f0 : bv 32 := 0x00c5a423.
Lemma F_1b62f0 : fetch_word Asan.M.loaded_segments (0x1b6458 : word) = Some W_1b62f0.
Proof. vm_refl. Qed.
Lemma D_1b62f0 : decode_any W_1b62f0 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62f4 : bv 32 := 0x01900793.
Lemma F_1b62f4 : fetch_word Asan.M.loaded_segments (0x1b645c : word) = Some W_1b62f4.
Proof. vm_refl. Qed.
Lemma D_1b62f4 : decode_any W_1b62f4 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62f8 : bv 32 := 0xfec6aa23.
Lemma F_1b62f8 : fetch_word Asan.M.loaded_segments (0x1b6460 : word) = Some W_1b62f8.
Proof. vm_refl. Qed.
Lemma D_1b62f8 : decode_any W_1b62f8 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b62fc : bv 32 := 0xfec6ac23.
Lemma F_1b62fc : fetch_word Asan.M.loaded_segments (0x1b6464 : word) = Some W_1b62fc.
Proof. vm_refl. Qed.
Lemma D_1b62fc : decode_any W_1b62fc = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6300 : bv 32 := 0x06f76463.
Lemma F_1b6300 : fetch_word Asan.M.loaded_segments (0x1b6468 : word) = Some W_1b6300.
Proof. vm_refl. Qed.
Lemma D_1b6300 : decode_any W_1b6300 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6304 : bv 32 := 0x00c5a623.
Lemma F_1b6304 : fetch_word Asan.M.loaded_segments (0x1b646c : word) = Some W_1b6304.
Proof. vm_refl. Qed.
Lemma D_1b6304 : decode_any W_1b6304 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6308 : bv 32 := 0x00c5a823.
Lemma F_1b6308 : fetch_word Asan.M.loaded_segments (0x1b6470 : word) = Some W_1b6308.
Proof. vm_refl. Qed.
Lemma D_1b6308 : decode_any W_1b6308 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b630c : bv 32 := 0x00c5aa23.
Lemma F_1b630c : fetch_word Asan.M.loaded_segments (0x1b6474 : word) = Some W_1b630c.
Proof. vm_refl. Qed.
Lemma D_1b630c : decode_any W_1b630c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6310 : bv 32 := 0x00c5ac23.
Lemma F_1b6310 : fetch_word Asan.M.loaded_segments (0x1b6478 : word) = Some W_1b6310.
Proof. vm_refl. Qed.
Lemma D_1b6310 : decode_any W_1b6310 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6314 : bv 32 := 0x0045f793.
Lemma F_1b6314 : fetch_word Asan.M.loaded_segments (0x1b647c : word) = Some W_1b6314.
Proof. vm_refl. Qed.
Lemma D_1b6314 : decode_any W_1b6314 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6318 : bv 32 := 0x02000813.
Lemma F_1b6318 : fetch_word Asan.M.loaded_segments (0x1b6480 : word) = Some W_1b6318.
Proof. vm_refl. Qed.
Lemma D_1b6318 : decode_any W_1b6318 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b631c : bv 32 := 0x01878793.
Lemma F_1b631c : fetch_word Asan.M.loaded_segments (0x1b6484 : word) = Some W_1b631c.
Proof. vm_refl. Qed.
Lemma D_1b631c : decode_any W_1b631c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6320 : bv 32 := 0x40f70733.
Lemma F_1b6320 : fetch_word Asan.M.loaded_segments (0x1b6488 : word) = Some W_1b6320.
Proof. vm_refl. Qed.
Lemma D_1b6320 : decode_any W_1b6320 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6324 : bv 32 := 0xfec6a223.
Lemma F_1b6324 : fetch_word Asan.M.loaded_segments (0x1b648c : word) = Some W_1b6324.
Proof. vm_refl. Qed.
Lemma D_1b6324 : decode_any W_1b6324 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6328 : bv 32 := 0xfec6a423.
Lemma F_1b6328 : fetch_word Asan.M.loaded_segments (0x1b6490 : word) = Some W_1b6328.
Proof. vm_refl. Qed.
Lemma D_1b6328 : decode_any W_1b6328 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b632c : bv 32 := 0xfec6a623.
Lemma F_1b632c : fetch_word Asan.M.loaded_segments (0x1b6494 : word) = Some W_1b632c.
Proof. vm_refl. Qed.
Lemma D_1b632c : decode_any W_1b632c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6330 : bv 32 := 0xfec6a823.
Lemma F_1b6330 : fetch_word Asan.M.loaded_segments (0x1b6498 : word) = Some W_1b6330.
Proof. vm_refl. Qed.
Lemma D_1b6330 : decode_any W_1b6330 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6334 : bv 32 := 0x03076a63.
Lemma F_1b6334 : fetch_word Asan.M.loaded_segments (0x1b649c : word) = Some W_1b6334.
Proof. vm_refl. Qed.
Lemma D_1b6334 : decode_any W_1b6334 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6338 : bv 32 := 0x02061613.
Lemma F_1b6338 : fetch_word Asan.M.loaded_segments (0x1b64a0 : word) = Some W_1b6338.
Proof. vm_refl. Qed.
Lemma D_1b6338 : decode_any W_1b6338 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b633c : bv 32 := 0x00f585b3.
Lemma F_1b633c : fetch_word Asan.M.loaded_segments (0x1b64a4 : word) = Some W_1b633c.
Proof. vm_refl. Qed.
Lemma D_1b633c : decode_any W_1b633c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6340 : bv 32 := 0x02065693.
Lemma F_1b6340 : fetch_word Asan.M.loaded_segments (0x1b64a8 : word) = Some W_1b6340.
Proof. vm_refl. Qed.
Lemma D_1b6340 : decode_any W_1b6340 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6344 : bv 32 := 0x00d66633.
Lemma F_1b6344 : fetch_word Asan.M.loaded_segments (0x1b64ac : word) = Some W_1b6344.
Proof. vm_refl. Qed.
Lemma D_1b6344 : decode_any W_1b6344 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6348 : bv 32 := 0x01f00693.
Lemma F_1b6348 : fetch_word Asan.M.loaded_segments (0x1b64b0 : word) = Some W_1b6348.
Proof. vm_refl. Qed.
Lemma D_1b6348 : decode_any W_1b6348 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b634c : bv 32 := 0x00c5b023.
Lemma F_1b634c : fetch_word Asan.M.loaded_segments (0x1b64b4 : word) = Some W_1b634c.
Proof. vm_refl. Qed.
Lemma D_1b634c : decode_any W_1b634c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6350 : bv 32 := 0x00c5b423.
Lemma F_1b6350 : fetch_word Asan.M.loaded_segments (0x1b64b8 : word) = Some W_1b6350.
Proof. vm_refl. Qed.
Lemma D_1b6350 : decode_any W_1b6350 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6354 : bv 32 := 0x00c5b823.
Lemma F_1b6354 : fetch_word Asan.M.loaded_segments (0x1b64bc : word) = Some W_1b6354.
Proof. vm_refl. Qed.
Lemma D_1b6354 : decode_any W_1b6354 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6358 : bv 32 := 0x00c5bc23.
Lemma F_1b6358 : fetch_word Asan.M.loaded_segments (0x1b64c0 : word) = Some W_1b6358.
Proof. vm_refl. Qed.
Lemma D_1b6358 : decode_any W_1b6358 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b635c : bv 32 := 0xfe070713.
Lemma F_1b635c : fetch_word Asan.M.loaded_segments (0x1b64c4 : word) = Some W_1b635c.
Proof. vm_refl. Qed.
Lemma D_1b635c : decode_any W_1b635c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6360 : bv 32 := 0x02058593.
Lemma F_1b6360 : fetch_word Asan.M.loaded_segments (0x1b64c8 : word) = Some W_1b6360.
Proof. vm_refl. Qed.
Lemma D_1b6360 : decode_any W_1b6360 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6364 : bv 32 := 0xfee6e4e3.
Lemma F_1b6364 : fetch_word Asan.M.loaded_segments (0x1b64cc : word) = Some W_1b6364.
Proof. vm_refl. Qed.
Lemma D_1b6364 : decode_any W_1b6364 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b6368 : bv 32 := 0x00008067.
Lemma F_1b6368 : fetch_word Asan.M.loaded_segments (0x1b64d0 : word) = Some W_1b6368.
Proof. vm_refl. Qed.
Lemma D_1b6368 : decode_any W_1b6368 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x1b63dc%Z.
Definition Fo_000 := F_1b6274.
Definition Do_000 := D_1b6274.
Definition Fo_004 := F_1b6278.
Definition Do_004 := D_1b6278.
Definition Fo_008 := F_1b627c.
Definition Do_008 := D_1b627c.
Definition Fo_00c := F_1b6280.
Definition Do_00c := D_1b6280.
Definition Fo_010 := F_1b6284.
Definition Do_010 := D_1b6284.
Definition Fo_014 := F_1b6288.
Definition Do_014 := D_1b6288.
Definition Fo_018 := F_1b628c.
Definition Do_018 := D_1b628c.
Definition Fo_01c := F_1b6290.
Definition Do_01c := D_1b6290.
Definition Fo_020 := F_1b6294.
Definition Do_020 := D_1b6294.
Definition Fo_024 := F_1b6298.
Definition Do_024 := D_1b6298.
Definition Fo_028 := F_1b629c.
Definition Do_028 := D_1b629c.
Definition Fo_02c := F_1b62a0.
Definition Do_02c := D_1b62a0.
Definition Fo_030 := F_1b62a4.
Definition Do_030 := D_1b62a4.
Definition Fo_034 := F_1b62a8.
Definition Do_034 := D_1b62a8.
Definition Fo_038 := F_1b62ac.
Definition Do_038 := D_1b62ac.
Definition Fo_03c := F_1b62b0.
Definition Do_03c := D_1b62b0.
Definition Fo_040 := F_1b62b4.
Definition Do_040 := D_1b62b4.
Definition Fo_044 := F_1b62b8.
Definition Do_044 := D_1b62b8.
Definition Fo_048 := F_1b62bc.
Definition Do_048 := D_1b62bc.
Definition Fo_04c := F_1b62c0.
Definition Do_04c := D_1b62c0.
Definition Fo_050 := F_1b62c4.
Definition Do_050 := D_1b62c4.
Definition Fo_054 := F_1b62c8.
Definition Do_054 := D_1b62c8.
Definition Fo_058 := F_1b62cc.
Definition Do_058 := D_1b62cc.
Definition Fo_05c := F_1b62d0.
Definition Do_05c := D_1b62d0.
Definition Fo_060 := F_1b62d4.
Definition Do_060 := D_1b62d4.
Definition Fo_064 := F_1b62d8.
Definition Do_064 := D_1b62d8.
Definition Fo_068 := F_1b62dc.
Definition Do_068 := D_1b62dc.
Definition Fo_06c := F_1b62e0.
Definition Do_06c := D_1b62e0.
Definition Fo_070 := F_1b62e4.
Definition Do_070 := D_1b62e4.
Definition Fo_074 := F_1b62e8.
Definition Do_074 := D_1b62e8.
Definition Fo_078 := F_1b62ec.
Definition Do_078 := D_1b62ec.
Definition Fo_07c := F_1b62f0.
Definition Do_07c := D_1b62f0.
Definition Fo_080 := F_1b62f4.
Definition Do_080 := D_1b62f4.
Definition Fo_084 := F_1b62f8.
Definition Do_084 := D_1b62f8.
Definition Fo_088 := F_1b62fc.
Definition Do_088 := D_1b62fc.
Definition Fo_08c := F_1b6300.
Definition Do_08c := D_1b6300.
Definition Fo_090 := F_1b6304.
Definition Do_090 := D_1b6304.
Definition Fo_094 := F_1b6308.
Definition Do_094 := D_1b6308.
Definition Fo_098 := F_1b630c.
Definition Do_098 := D_1b630c.
Definition Fo_09c := F_1b6310.
Definition Do_09c := D_1b6310.
Definition Fo_0a0 := F_1b6314.
Definition Do_0a0 := D_1b6314.
Definition Fo_0a4 := F_1b6318.
Definition Do_0a4 := D_1b6318.
Definition Fo_0a8 := F_1b631c.
Definition Do_0a8 := D_1b631c.
Definition Fo_0ac := F_1b6320.
Definition Do_0ac := D_1b6320.
Definition Fo_0b0 := F_1b6324.
Definition Do_0b0 := D_1b6324.
Definition Fo_0b4 := F_1b6328.
Definition Do_0b4 := D_1b6328.
Definition Fo_0b8 := F_1b632c.
Definition Do_0b8 := D_1b632c.
Definition Fo_0bc := F_1b6330.
Definition Do_0bc := D_1b6330.
Definition Fo_0c0 := F_1b6334.
Definition Do_0c0 := D_1b6334.
Definition Fo_0c4 := F_1b6338.
Definition Do_0c4 := D_1b6338.
Definition Fo_0c8 := F_1b633c.
Definition Do_0c8 := D_1b633c.
Definition Fo_0cc := F_1b6340.
Definition Do_0cc := D_1b6340.
Definition Fo_0d0 := F_1b6344.
Definition Do_0d0 := D_1b6344.
Definition Fo_0d4 := F_1b6348.
Definition Do_0d4 := D_1b6348.
Definition Fo_0d8 := F_1b634c.
Definition Do_0d8 := D_1b634c.
Definition Fo_0dc := F_1b6350.
Definition Do_0dc := D_1b6350.
Definition Fo_0e0 := F_1b6354.
Definition Do_0e0 := D_1b6354.
Definition Fo_0e4 := F_1b6358.
Definition Do_0e4 := D_1b6358.
Definition Fo_0e8 := F_1b635c.
Definition Do_0e8 := D_1b635c.
Definition Fo_0ec := F_1b6360.
Definition Do_0ec := D_1b6360.
Definition Fo_0f0 := F_1b6364.
Definition Do_0f0 := D_1b6364.
Definition Fo_0f4 := F_1b6368.
Definition Do_0f4 := D_1b6368.
