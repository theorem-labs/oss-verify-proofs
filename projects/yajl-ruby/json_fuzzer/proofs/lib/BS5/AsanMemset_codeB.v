(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_9e26c : bv 32 := 0x0e060a63.
Lemma F_9e26c : fetch_word AsanUbsan.M.loaded_segments (0x9ecd0 : word) = Some W_9e26c.
Proof. vm_refl. Qed.
Lemma D_9e26c : decode_any W_9e26c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e270 : bv 32 := 0x00b50023.
Lemma F_9e270 : fetch_word AsanUbsan.M.loaded_segments (0x9ecd4 : word) = Some W_9e270.
Proof. vm_refl. Qed.
Lemma D_9e270 : decode_any W_9e270 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e274 : bv 32 := 0x00c506b3.
Lemma F_9e274 : fetch_word AsanUbsan.M.loaded_segments (0x9ecd8 : word) = Some W_9e274.
Proof. vm_refl. Qed.
Lemma D_9e274 : decode_any W_9e274 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e278 : bv 32 := 0x00300713.
Lemma F_9e278 : fetch_word AsanUbsan.M.loaded_segments (0x9ecdc : word) = Some W_9e278.
Proof. vm_refl. Qed.
Lemma D_9e278 : decode_any W_9e278 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e27c : bv 32 := 0xfeb68fa3.
Lemma F_9e27c : fetch_word AsanUbsan.M.loaded_segments (0x9ece0 : word) = Some W_9e27c.
Proof. vm_refl. Qed.
Lemma D_9e27c : decode_any W_9e27c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e280 : bv 32 := 0x0ee66063.
Lemma F_9e280 : fetch_word AsanUbsan.M.loaded_segments (0x9ece4 : word) = Some W_9e280.
Proof. vm_refl. Qed.
Lemma D_9e280 : decode_any W_9e280 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e284 : bv 32 := 0x00b500a3.
Lemma F_9e284 : fetch_word AsanUbsan.M.loaded_segments (0x9ece8 : word) = Some W_9e284.
Proof. vm_refl. Qed.
Lemma D_9e284 : decode_any W_9e284 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e288 : bv 32 := 0x00b50123.
Lemma F_9e288 : fetch_word AsanUbsan.M.loaded_segments (0x9ecec : word) = Some W_9e288.
Proof. vm_refl. Qed.
Lemma D_9e288 : decode_any W_9e288 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e28c : bv 32 := 0x00700713.
Lemma F_9e28c : fetch_word AsanUbsan.M.loaded_segments (0x9ecf0 : word) = Some W_9e28c.
Proof. vm_refl. Qed.
Lemma D_9e28c : decode_any W_9e28c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e290 : bv 32 := 0xfeb68ea3.
Lemma F_9e290 : fetch_word AsanUbsan.M.loaded_segments (0x9ecf4 : word) = Some W_9e290.
Proof. vm_refl. Qed.
Lemma D_9e290 : decode_any W_9e290 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e294 : bv 32 := 0xfeb68f23.
Lemma F_9e294 : fetch_word AsanUbsan.M.loaded_segments (0x9ecf8 : word) = Some W_9e294.
Proof. vm_refl. Qed.
Lemma D_9e294 : decode_any W_9e294 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e298 : bv 32 := 0x0ce66463.
Lemma F_9e298 : fetch_word AsanUbsan.M.loaded_segments (0x9ecfc : word) = Some W_9e298.
Proof. vm_refl. Qed.
Lemma D_9e298 : decode_any W_9e298 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e29c : bv 32 := 0x00b501a3.
Lemma F_9e29c : fetch_word AsanUbsan.M.loaded_segments (0x9ed00 : word) = Some W_9e29c.
Proof. vm_refl. Qed.
Lemma D_9e29c : decode_any W_9e29c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2a0 : bv 32 := 0x00900793.
Lemma F_9e2a0 : fetch_word AsanUbsan.M.loaded_segments (0x9ed04 : word) = Some W_9e2a0.
Proof. vm_refl. Qed.
Lemma D_9e2a0 : decode_any W_9e2a0 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2a4 : bv 32 := 0xfeb68e23.
Lemma F_9e2a4 : fetch_word AsanUbsan.M.loaded_segments (0x9ed08 : word) = Some W_9e2a4.
Proof. vm_refl. Qed.
Lemma D_9e2a4 : decode_any W_9e2a4 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2a8 : bv 32 := 0x0af66c63.
Lemma F_9e2a8 : fetch_word AsanUbsan.M.loaded_segments (0x9ed0c : word) = Some W_9e2a8.
Proof. vm_refl. Qed.
Lemma D_9e2a8 : decode_any W_9e2a8 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2ac : bv 32 := 0x40a006bb.
Lemma F_9e2ac : fetch_word AsanUbsan.M.loaded_segments (0x9ed10 : word) = Some W_9e2ac.
Proof. vm_refl. Qed.
Lemma D_9e2ac : decode_any W_9e2ac = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2b0 : bv 32 := 0x03859813.
Lemma F_9e2b0 : fetch_word AsanUbsan.M.loaded_segments (0x9ed14 : word) = Some W_9e2b0.
Proof. vm_refl. Qed.
Lemma D_9e2b0 : decode_any W_9e2b0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2b4 : bv 32 := 0x101015b7.
Lemma F_9e2b4 : fetch_word AsanUbsan.M.loaded_segments (0x9ed18 : word) = Some W_9e2b4.
Proof. vm_refl. Qed.
Lemma D_9e2b4 : decode_any W_9e2b4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2b8 : bv 32 := 0x0036f693.
Lemma F_9e2b8 : fetch_word AsanUbsan.M.loaded_segments (0x9ed1c : word) = Some W_9e2b8.
Proof. vm_refl. Qed.
Lemma D_9e2b8 : decode_any W_9e2b8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2bc : bv 32 := 0x00459713.
Lemma F_9e2bc : fetch_word AsanUbsan.M.loaded_segments (0x9ed20 : word) = Some W_9e2bc.
Proof. vm_refl. Qed.
Lemma D_9e2bc : decode_any W_9e2bc = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2c0 : bv 32 := 0x40d60633.
Lemma F_9e2c0 : fetch_word AsanUbsan.M.loaded_segments (0x9ed24 : word) = Some W_9e2c0.
Proof. vm_refl. Qed.
Lemma D_9e2c0 : decode_any W_9e2c0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2c4 : bv 32 := 0x00d505b3.
Lemma F_9e2c4 : fetch_word AsanUbsan.M.loaded_segments (0x9ed28 : word) = Some W_9e2c4.
Proof. vm_refl. Qed.
Lemma D_9e2c4 : decode_any W_9e2c4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2c8 : bv 32 := 0x10070693.
Lemma F_9e2c8 : fetch_word AsanUbsan.M.loaded_segments (0x9ed2c : word) = Some W_9e2c8.
Proof. vm_refl. Qed.
Lemma D_9e2c8 : decode_any W_9e2c8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2cc : bv 32 := 0xffc67713.
Lemma F_9e2cc : fetch_word AsanUbsan.M.loaded_segments (0x9ed30 : word) = Some W_9e2cc.
Proof. vm_refl. Qed.
Lemma D_9e2cc : decode_any W_9e2cc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2d0 : bv 32 := 0x02d83633.
Lemma F_9e2d0 : fetch_word AsanUbsan.M.loaded_segments (0x9ed34 : word) = Some W_9e2d0.
Proof. vm_refl. Qed.
Lemma D_9e2d0 : decode_any W_9e2d0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2d4 : bv 32 := 0x00c5a023.
Lemma F_9e2d4 : fetch_word AsanUbsan.M.loaded_segments (0x9ed38 : word) = Some W_9e2d4.
Proof. vm_refl. Qed.
Lemma D_9e2d4 : decode_any W_9e2d4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2d8 : bv 32 := 0x00e586b3.
Lemma F_9e2d8 : fetch_word AsanUbsan.M.loaded_segments (0x9ed3c : word) = Some W_9e2d8.
Proof. vm_refl. Qed.
Lemma D_9e2d8 : decode_any W_9e2d8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2dc : bv 32 := 0xfec6ae23.
Lemma F_9e2dc : fetch_word AsanUbsan.M.loaded_segments (0x9ed40 : word) = Some W_9e2dc.
Proof. vm_refl. Qed.
Lemma D_9e2dc : decode_any W_9e2dc = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2e0 : bv 32 := 0x08f76063.
Lemma F_9e2e0 : fetch_word AsanUbsan.M.loaded_segments (0x9ed44 : word) = Some W_9e2e0.
Proof. vm_refl. Qed.
Lemma D_9e2e0 : decode_any W_9e2e0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2e4 : bv 32 := 0x00c5a223.
Lemma F_9e2e4 : fetch_word AsanUbsan.M.loaded_segments (0x9ed48 : word) = Some W_9e2e4.
Proof. vm_refl. Qed.
Lemma D_9e2e4 : decode_any W_9e2e4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2e8 : bv 32 := 0x00c5a423.
Lemma F_9e2e8 : fetch_word AsanUbsan.M.loaded_segments (0x9ed4c : word) = Some W_9e2e8.
Proof. vm_refl. Qed.
Lemma D_9e2e8 : decode_any W_9e2e8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2ec : bv 32 := 0x01900793.
Lemma F_9e2ec : fetch_word AsanUbsan.M.loaded_segments (0x9ed50 : word) = Some W_9e2ec.
Proof. vm_refl. Qed.
Lemma D_9e2ec : decode_any W_9e2ec = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2f0 : bv 32 := 0xfec6aa23.
Lemma F_9e2f0 : fetch_word AsanUbsan.M.loaded_segments (0x9ed54 : word) = Some W_9e2f0.
Proof. vm_refl. Qed.
Lemma D_9e2f0 : decode_any W_9e2f0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2f4 : bv 32 := 0xfec6ac23.
Lemma F_9e2f4 : fetch_word AsanUbsan.M.loaded_segments (0x9ed58 : word) = Some W_9e2f4.
Proof. vm_refl. Qed.
Lemma D_9e2f4 : decode_any W_9e2f4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2f8 : bv 32 := 0x06f76463.
Lemma F_9e2f8 : fetch_word AsanUbsan.M.loaded_segments (0x9ed5c : word) = Some W_9e2f8.
Proof. vm_refl. Qed.
Lemma D_9e2f8 : decode_any W_9e2f8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e2fc : bv 32 := 0x00c5a623.
Lemma F_9e2fc : fetch_word AsanUbsan.M.loaded_segments (0x9ed60 : word) = Some W_9e2fc.
Proof. vm_refl. Qed.
Lemma D_9e2fc : decode_any W_9e2fc = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e300 : bv 32 := 0x00c5a823.
Lemma F_9e300 : fetch_word AsanUbsan.M.loaded_segments (0x9ed64 : word) = Some W_9e300.
Proof. vm_refl. Qed.
Lemma D_9e300 : decode_any W_9e300 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e304 : bv 32 := 0x00c5aa23.
Lemma F_9e304 : fetch_word AsanUbsan.M.loaded_segments (0x9ed68 : word) = Some W_9e304.
Proof. vm_refl. Qed.
Lemma D_9e304 : decode_any W_9e304 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e308 : bv 32 := 0x00c5ac23.
Lemma F_9e308 : fetch_word AsanUbsan.M.loaded_segments (0x9ed6c : word) = Some W_9e308.
Proof. vm_refl. Qed.
Lemma D_9e308 : decode_any W_9e308 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e30c : bv 32 := 0x0045f793.
Lemma F_9e30c : fetch_word AsanUbsan.M.loaded_segments (0x9ed70 : word) = Some W_9e30c.
Proof. vm_refl. Qed.
Lemma D_9e30c : decode_any W_9e30c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e310 : bv 32 := 0x02000813.
Lemma F_9e310 : fetch_word AsanUbsan.M.loaded_segments (0x9ed74 : word) = Some W_9e310.
Proof. vm_refl. Qed.
Lemma D_9e310 : decode_any W_9e310 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e314 : bv 32 := 0x01878793.
Lemma F_9e314 : fetch_word AsanUbsan.M.loaded_segments (0x9ed78 : word) = Some W_9e314.
Proof. vm_refl. Qed.
Lemma D_9e314 : decode_any W_9e314 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e318 : bv 32 := 0x40f70733.
Lemma F_9e318 : fetch_word AsanUbsan.M.loaded_segments (0x9ed7c : word) = Some W_9e318.
Proof. vm_refl. Qed.
Lemma D_9e318 : decode_any W_9e318 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e31c : bv 32 := 0xfec6a223.
Lemma F_9e31c : fetch_word AsanUbsan.M.loaded_segments (0x9ed80 : word) = Some W_9e31c.
Proof. vm_refl. Qed.
Lemma D_9e31c : decode_any W_9e31c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e320 : bv 32 := 0xfec6a423.
Lemma F_9e320 : fetch_word AsanUbsan.M.loaded_segments (0x9ed84 : word) = Some W_9e320.
Proof. vm_refl. Qed.
Lemma D_9e320 : decode_any W_9e320 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e324 : bv 32 := 0xfec6a623.
Lemma F_9e324 : fetch_word AsanUbsan.M.loaded_segments (0x9ed88 : word) = Some W_9e324.
Proof. vm_refl. Qed.
Lemma D_9e324 : decode_any W_9e324 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e328 : bv 32 := 0xfec6a823.
Lemma F_9e328 : fetch_word AsanUbsan.M.loaded_segments (0x9ed8c : word) = Some W_9e328.
Proof. vm_refl. Qed.
Lemma D_9e328 : decode_any W_9e328 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e32c : bv 32 := 0x03076a63.
Lemma F_9e32c : fetch_word AsanUbsan.M.loaded_segments (0x9ed90 : word) = Some W_9e32c.
Proof. vm_refl. Qed.
Lemma D_9e32c : decode_any W_9e32c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e330 : bv 32 := 0x02061613.
Lemma F_9e330 : fetch_word AsanUbsan.M.loaded_segments (0x9ed94 : word) = Some W_9e330.
Proof. vm_refl. Qed.
Lemma D_9e330 : decode_any W_9e330 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e334 : bv 32 := 0x00f585b3.
Lemma F_9e334 : fetch_word AsanUbsan.M.loaded_segments (0x9ed98 : word) = Some W_9e334.
Proof. vm_refl. Qed.
Lemma D_9e334 : decode_any W_9e334 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e338 : bv 32 := 0x02065693.
Lemma F_9e338 : fetch_word AsanUbsan.M.loaded_segments (0x9ed9c : word) = Some W_9e338.
Proof. vm_refl. Qed.
Lemma D_9e338 : decode_any W_9e338 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e33c : bv 32 := 0x00d66633.
Lemma F_9e33c : fetch_word AsanUbsan.M.loaded_segments (0x9eda0 : word) = Some W_9e33c.
Proof. vm_refl. Qed.
Lemma D_9e33c : decode_any W_9e33c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e340 : bv 32 := 0x01f00693.
Lemma F_9e340 : fetch_word AsanUbsan.M.loaded_segments (0x9eda4 : word) = Some W_9e340.
Proof. vm_refl. Qed.
Lemma D_9e340 : decode_any W_9e340 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e344 : bv 32 := 0x00c5b023.
Lemma F_9e344 : fetch_word AsanUbsan.M.loaded_segments (0x9eda8 : word) = Some W_9e344.
Proof. vm_refl. Qed.
Lemma D_9e344 : decode_any W_9e344 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e348 : bv 32 := 0x00c5b423.
Lemma F_9e348 : fetch_word AsanUbsan.M.loaded_segments (0x9edac : word) = Some W_9e348.
Proof. vm_refl. Qed.
Lemma D_9e348 : decode_any W_9e348 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e34c : bv 32 := 0x00c5b823.
Lemma F_9e34c : fetch_word AsanUbsan.M.loaded_segments (0x9edb0 : word) = Some W_9e34c.
Proof. vm_refl. Qed.
Lemma D_9e34c : decode_any W_9e34c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e350 : bv 32 := 0x00c5bc23.
Lemma F_9e350 : fetch_word AsanUbsan.M.loaded_segments (0x9edb4 : word) = Some W_9e350.
Proof. vm_refl. Qed.
Lemma D_9e350 : decode_any W_9e350 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e354 : bv 32 := 0xfe070713.
Lemma F_9e354 : fetch_word AsanUbsan.M.loaded_segments (0x9edb8 : word) = Some W_9e354.
Proof. vm_refl. Qed.
Lemma D_9e354 : decode_any W_9e354 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e358 : bv 32 := 0x02058593.
Lemma F_9e358 : fetch_word AsanUbsan.M.loaded_segments (0x9edbc : word) = Some W_9e358.
Proof. vm_refl. Qed.
Lemma D_9e358 : decode_any W_9e358 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e35c : bv 32 := 0xfee6e4e3.
Lemma F_9e35c : fetch_word AsanUbsan.M.loaded_segments (0x9edc0 : word) = Some W_9e35c.
Proof. vm_refl. Qed.
Lemma D_9e35c : decode_any W_9e35c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e360 : bv 32 := 0x00008067.
Lemma F_9e360 : fetch_word AsanUbsan.M.loaded_segments (0x9edc4 : word) = Some W_9e360.
Proof. vm_refl. Qed.
Lemma D_9e360 : decode_any W_9e360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x9ecd0%Z.
Definition Fo_000 := F_9e26c.
Definition Do_000 := D_9e26c.
Definition Fo_004 := F_9e270.
Definition Do_004 := D_9e270.
Definition Fo_008 := F_9e274.
Definition Do_008 := D_9e274.
Definition Fo_00c := F_9e278.
Definition Do_00c := D_9e278.
Definition Fo_010 := F_9e27c.
Definition Do_010 := D_9e27c.
Definition Fo_014 := F_9e280.
Definition Do_014 := D_9e280.
Definition Fo_018 := F_9e284.
Definition Do_018 := D_9e284.
Definition Fo_01c := F_9e288.
Definition Do_01c := D_9e288.
Definition Fo_020 := F_9e28c.
Definition Do_020 := D_9e28c.
Definition Fo_024 := F_9e290.
Definition Do_024 := D_9e290.
Definition Fo_028 := F_9e294.
Definition Do_028 := D_9e294.
Definition Fo_02c := F_9e298.
Definition Do_02c := D_9e298.
Definition Fo_030 := F_9e29c.
Definition Do_030 := D_9e29c.
Definition Fo_034 := F_9e2a0.
Definition Do_034 := D_9e2a0.
Definition Fo_038 := F_9e2a4.
Definition Do_038 := D_9e2a4.
Definition Fo_03c := F_9e2a8.
Definition Do_03c := D_9e2a8.
Definition Fo_040 := F_9e2ac.
Definition Do_040 := D_9e2ac.
Definition Fo_044 := F_9e2b0.
Definition Do_044 := D_9e2b0.
Definition Fo_048 := F_9e2b4.
Definition Do_048 := D_9e2b4.
Definition Fo_04c := F_9e2b8.
Definition Do_04c := D_9e2b8.
Definition Fo_050 := F_9e2bc.
Definition Do_050 := D_9e2bc.
Definition Fo_054 := F_9e2c0.
Definition Do_054 := D_9e2c0.
Definition Fo_058 := F_9e2c4.
Definition Do_058 := D_9e2c4.
Definition Fo_05c := F_9e2c8.
Definition Do_05c := D_9e2c8.
Definition Fo_060 := F_9e2cc.
Definition Do_060 := D_9e2cc.
Definition Fo_064 := F_9e2d0.
Definition Do_064 := D_9e2d0.
Definition Fo_068 := F_9e2d4.
Definition Do_068 := D_9e2d4.
Definition Fo_06c := F_9e2d8.
Definition Do_06c := D_9e2d8.
Definition Fo_070 := F_9e2dc.
Definition Do_070 := D_9e2dc.
Definition Fo_074 := F_9e2e0.
Definition Do_074 := D_9e2e0.
Definition Fo_078 := F_9e2e4.
Definition Do_078 := D_9e2e4.
Definition Fo_07c := F_9e2e8.
Definition Do_07c := D_9e2e8.
Definition Fo_080 := F_9e2ec.
Definition Do_080 := D_9e2ec.
Definition Fo_084 := F_9e2f0.
Definition Do_084 := D_9e2f0.
Definition Fo_088 := F_9e2f4.
Definition Do_088 := D_9e2f4.
Definition Fo_08c := F_9e2f8.
Definition Do_08c := D_9e2f8.
Definition Fo_090 := F_9e2fc.
Definition Do_090 := D_9e2fc.
Definition Fo_094 := F_9e300.
Definition Do_094 := D_9e300.
Definition Fo_098 := F_9e304.
Definition Do_098 := D_9e304.
Definition Fo_09c := F_9e308.
Definition Do_09c := D_9e308.
Definition Fo_0a0 := F_9e30c.
Definition Do_0a0 := D_9e30c.
Definition Fo_0a4 := F_9e310.
Definition Do_0a4 := D_9e310.
Definition Fo_0a8 := F_9e314.
Definition Do_0a8 := D_9e314.
Definition Fo_0ac := F_9e318.
Definition Do_0ac := D_9e318.
Definition Fo_0b0 := F_9e31c.
Definition Do_0b0 := D_9e31c.
Definition Fo_0b4 := F_9e320.
Definition Do_0b4 := D_9e320.
Definition Fo_0b8 := F_9e324.
Definition Do_0b8 := D_9e324.
Definition Fo_0bc := F_9e328.
Definition Do_0bc := D_9e328.
Definition Fo_0c0 := F_9e32c.
Definition Do_0c0 := D_9e32c.
Definition Fo_0c4 := F_9e330.
Definition Do_0c4 := D_9e330.
Definition Fo_0c8 := F_9e334.
Definition Do_0c8 := D_9e334.
Definition Fo_0cc := F_9e338.
Definition Do_0cc := D_9e338.
Definition Fo_0d0 := F_9e33c.
Definition Do_0d0 := D_9e33c.
Definition Fo_0d4 := F_9e340.
Definition Do_0d4 := D_9e340.
Definition Fo_0d8 := F_9e344.
Definition Do_0d8 := D_9e344.
Definition Fo_0dc := F_9e348.
Definition Do_0dc := D_9e348.
Definition Fo_0e0 := F_9e34c.
Definition Do_0e0 := D_9e34c.
Definition Fo_0e4 := F_9e350.
Definition Do_0e4 := D_9e350.
Definition Fo_0e8 := F_9e354.
Definition Do_0e8 := D_9e354.
Definition Fo_0ec := F_9e358.
Definition Do_0ec := D_9e358.
Definition Fo_0f0 := F_9e35c.
Definition Do_0f0 := D_9e35c.
Definition Fo_0f4 := F_9e360.
Definition Do_0f4 := D_9e360.
