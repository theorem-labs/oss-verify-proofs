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
Definition W_d9c88 : bv 32 := 0x0e060a63.
Lemma F_d9c88 : fetch_word Asan.M.loaded_segments (0xd9cec : word) = Some W_d9c88.
Proof. vm_refl. Qed.
Lemma D_d9c88 : decode_any W_d9c88 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c8c : bv 32 := 0x00b50023.
Lemma F_d9c8c : fetch_word Asan.M.loaded_segments (0xd9cf0 : word) = Some W_d9c8c.
Proof. vm_refl. Qed.
Lemma D_d9c8c : decode_any W_d9c8c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c90 : bv 32 := 0x00c506b3.
Lemma F_d9c90 : fetch_word Asan.M.loaded_segments (0xd9cf4 : word) = Some W_d9c90.
Proof. vm_refl. Qed.
Lemma D_d9c90 : decode_any W_d9c90 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c94 : bv 32 := 0x00300713.
Lemma F_d9c94 : fetch_word Asan.M.loaded_segments (0xd9cf8 : word) = Some W_d9c94.
Proof. vm_refl. Qed.
Lemma D_d9c94 : decode_any W_d9c94 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c98 : bv 32 := 0xfeb68fa3.
Lemma F_d9c98 : fetch_word Asan.M.loaded_segments (0xd9cfc : word) = Some W_d9c98.
Proof. vm_refl. Qed.
Lemma D_d9c98 : decode_any W_d9c98 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9c9c : bv 32 := 0x0ee66063.
Lemma F_d9c9c : fetch_word Asan.M.loaded_segments (0xd9d00 : word) = Some W_d9c9c.
Proof. vm_refl. Qed.
Lemma D_d9c9c : decode_any W_d9c9c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ca0 : bv 32 := 0x00b500a3.
Lemma F_d9ca0 : fetch_word Asan.M.loaded_segments (0xd9d04 : word) = Some W_d9ca0.
Proof. vm_refl. Qed.
Lemma D_d9ca0 : decode_any W_d9ca0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ca4 : bv 32 := 0x00b50123.
Lemma F_d9ca4 : fetch_word Asan.M.loaded_segments (0xd9d08 : word) = Some W_d9ca4.
Proof. vm_refl. Qed.
Lemma D_d9ca4 : decode_any W_d9ca4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ca8 : bv 32 := 0x00700713.
Lemma F_d9ca8 : fetch_word Asan.M.loaded_segments (0xd9d0c : word) = Some W_d9ca8.
Proof. vm_refl. Qed.
Lemma D_d9ca8 : decode_any W_d9ca8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cac : bv 32 := 0xfeb68ea3.
Lemma F_d9cac : fetch_word Asan.M.loaded_segments (0xd9d10 : word) = Some W_d9cac.
Proof. vm_refl. Qed.
Lemma D_d9cac : decode_any W_d9cac = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cb0 : bv 32 := 0xfeb68f23.
Lemma F_d9cb0 : fetch_word Asan.M.loaded_segments (0xd9d14 : word) = Some W_d9cb0.
Proof. vm_refl. Qed.
Lemma D_d9cb0 : decode_any W_d9cb0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cb4 : bv 32 := 0x0ce66463.
Lemma F_d9cb4 : fetch_word Asan.M.loaded_segments (0xd9d18 : word) = Some W_d9cb4.
Proof. vm_refl. Qed.
Lemma D_d9cb4 : decode_any W_d9cb4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cb8 : bv 32 := 0x00b501a3.
Lemma F_d9cb8 : fetch_word Asan.M.loaded_segments (0xd9d1c : word) = Some W_d9cb8.
Proof. vm_refl. Qed.
Lemma D_d9cb8 : decode_any W_d9cb8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cbc : bv 32 := 0x00900793.
Lemma F_d9cbc : fetch_word Asan.M.loaded_segments (0xd9d20 : word) = Some W_d9cbc.
Proof. vm_refl. Qed.
Lemma D_d9cbc : decode_any W_d9cbc = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cc0 : bv 32 := 0xfeb68e23.
Lemma F_d9cc0 : fetch_word Asan.M.loaded_segments (0xd9d24 : word) = Some W_d9cc0.
Proof. vm_refl. Qed.
Lemma D_d9cc0 : decode_any W_d9cc0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cc4 : bv 32 := 0x0af66c63.
Lemma F_d9cc4 : fetch_word Asan.M.loaded_segments (0xd9d28 : word) = Some W_d9cc4.
Proof. vm_refl. Qed.
Lemma D_d9cc4 : decode_any W_d9cc4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cc8 : bv 32 := 0x40a006bb.
Lemma F_d9cc8 : fetch_word Asan.M.loaded_segments (0xd9d2c : word) = Some W_d9cc8.
Proof. vm_refl. Qed.
Lemma D_d9cc8 : decode_any W_d9cc8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ccc : bv 32 := 0x03859813.
Lemma F_d9ccc : fetch_word Asan.M.loaded_segments (0xd9d30 : word) = Some W_d9ccc.
Proof. vm_refl. Qed.
Lemma D_d9ccc : decode_any W_d9ccc = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cd0 : bv 32 := 0x101015b7.
Lemma F_d9cd0 : fetch_word Asan.M.loaded_segments (0xd9d34 : word) = Some W_d9cd0.
Proof. vm_refl. Qed.
Lemma D_d9cd0 : decode_any W_d9cd0 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cd4 : bv 32 := 0x0036f693.
Lemma F_d9cd4 : fetch_word Asan.M.loaded_segments (0xd9d38 : word) = Some W_d9cd4.
Proof. vm_refl. Qed.
Lemma D_d9cd4 : decode_any W_d9cd4 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cd8 : bv 32 := 0x00459713.
Lemma F_d9cd8 : fetch_word Asan.M.loaded_segments (0xd9d3c : word) = Some W_d9cd8.
Proof. vm_refl. Qed.
Lemma D_d9cd8 : decode_any W_d9cd8 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cdc : bv 32 := 0x40d60633.
Lemma F_d9cdc : fetch_word Asan.M.loaded_segments (0xd9d40 : word) = Some W_d9cdc.
Proof. vm_refl. Qed.
Lemma D_d9cdc : decode_any W_d9cdc = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ce0 : bv 32 := 0x00d505b3.
Lemma F_d9ce0 : fetch_word Asan.M.loaded_segments (0xd9d44 : word) = Some W_d9ce0.
Proof. vm_refl. Qed.
Lemma D_d9ce0 : decode_any W_d9ce0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ce4 : bv 32 := 0x10070693.
Lemma F_d9ce4 : fetch_word Asan.M.loaded_segments (0xd9d48 : word) = Some W_d9ce4.
Proof. vm_refl. Qed.
Lemma D_d9ce4 : decode_any W_d9ce4 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9ce8 : bv 32 := 0xffc67713.
Lemma F_d9ce8 : fetch_word Asan.M.loaded_segments (0xd9d4c : word) = Some W_d9ce8.
Proof. vm_refl. Qed.
Lemma D_d9ce8 : decode_any W_d9ce8 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cec : bv 32 := 0x02d83633.
Lemma F_d9cec : fetch_word Asan.M.loaded_segments (0xd9d50 : word) = Some W_d9cec.
Proof. vm_refl. Qed.
Lemma D_d9cec : decode_any W_d9cec = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cf0 : bv 32 := 0x00c5a023.
Lemma F_d9cf0 : fetch_word Asan.M.loaded_segments (0xd9d54 : word) = Some W_d9cf0.
Proof. vm_refl. Qed.
Lemma D_d9cf0 : decode_any W_d9cf0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cf4 : bv 32 := 0x00e586b3.
Lemma F_d9cf4 : fetch_word Asan.M.loaded_segments (0xd9d58 : word) = Some W_d9cf4.
Proof. vm_refl. Qed.
Lemma D_d9cf4 : decode_any W_d9cf4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cf8 : bv 32 := 0xfec6ae23.
Lemma F_d9cf8 : fetch_word Asan.M.loaded_segments (0xd9d5c : word) = Some W_d9cf8.
Proof. vm_refl. Qed.
Lemma D_d9cf8 : decode_any W_d9cf8 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9cfc : bv 32 := 0x08f76063.
Lemma F_d9cfc : fetch_word Asan.M.loaded_segments (0xd9d60 : word) = Some W_d9cfc.
Proof. vm_refl. Qed.
Lemma D_d9cfc : decode_any W_d9cfc = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d00 : bv 32 := 0x00c5a223.
Lemma F_d9d00 : fetch_word Asan.M.loaded_segments (0xd9d64 : word) = Some W_d9d00.
Proof. vm_refl. Qed.
Lemma D_d9d00 : decode_any W_d9d00 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d04 : bv 32 := 0x00c5a423.
Lemma F_d9d04 : fetch_word Asan.M.loaded_segments (0xd9d68 : word) = Some W_d9d04.
Proof. vm_refl. Qed.
Lemma D_d9d04 : decode_any W_d9d04 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d08 : bv 32 := 0x01900793.
Lemma F_d9d08 : fetch_word Asan.M.loaded_segments (0xd9d6c : word) = Some W_d9d08.
Proof. vm_refl. Qed.
Lemma D_d9d08 : decode_any W_d9d08 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d0c : bv 32 := 0xfec6aa23.
Lemma F_d9d0c : fetch_word Asan.M.loaded_segments (0xd9d70 : word) = Some W_d9d0c.
Proof. vm_refl. Qed.
Lemma D_d9d0c : decode_any W_d9d0c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d10 : bv 32 := 0xfec6ac23.
Lemma F_d9d10 : fetch_word Asan.M.loaded_segments (0xd9d74 : word) = Some W_d9d10.
Proof. vm_refl. Qed.
Lemma D_d9d10 : decode_any W_d9d10 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d14 : bv 32 := 0x06f76463.
Lemma F_d9d14 : fetch_word Asan.M.loaded_segments (0xd9d78 : word) = Some W_d9d14.
Proof. vm_refl. Qed.
Lemma D_d9d14 : decode_any W_d9d14 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d18 : bv 32 := 0x00c5a623.
Lemma F_d9d18 : fetch_word Asan.M.loaded_segments (0xd9d7c : word) = Some W_d9d18.
Proof. vm_refl. Qed.
Lemma D_d9d18 : decode_any W_d9d18 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d1c : bv 32 := 0x00c5a823.
Lemma F_d9d1c : fetch_word Asan.M.loaded_segments (0xd9d80 : word) = Some W_d9d1c.
Proof. vm_refl. Qed.
Lemma D_d9d1c : decode_any W_d9d1c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d20 : bv 32 := 0x00c5aa23.
Lemma F_d9d20 : fetch_word Asan.M.loaded_segments (0xd9d84 : word) = Some W_d9d20.
Proof. vm_refl. Qed.
Lemma D_d9d20 : decode_any W_d9d20 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d24 : bv 32 := 0x00c5ac23.
Lemma F_d9d24 : fetch_word Asan.M.loaded_segments (0xd9d88 : word) = Some W_d9d24.
Proof. vm_refl. Qed.
Lemma D_d9d24 : decode_any W_d9d24 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d28 : bv 32 := 0x0045f793.
Lemma F_d9d28 : fetch_word Asan.M.loaded_segments (0xd9d8c : word) = Some W_d9d28.
Proof. vm_refl. Qed.
Lemma D_d9d28 : decode_any W_d9d28 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d2c : bv 32 := 0x02000813.
Lemma F_d9d2c : fetch_word Asan.M.loaded_segments (0xd9d90 : word) = Some W_d9d2c.
Proof. vm_refl. Qed.
Lemma D_d9d2c : decode_any W_d9d2c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d30 : bv 32 := 0x01878793.
Lemma F_d9d30 : fetch_word Asan.M.loaded_segments (0xd9d94 : word) = Some W_d9d30.
Proof. vm_refl. Qed.
Lemma D_d9d30 : decode_any W_d9d30 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d34 : bv 32 := 0x40f70733.
Lemma F_d9d34 : fetch_word Asan.M.loaded_segments (0xd9d98 : word) = Some W_d9d34.
Proof. vm_refl. Qed.
Lemma D_d9d34 : decode_any W_d9d34 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d38 : bv 32 := 0xfec6a223.
Lemma F_d9d38 : fetch_word Asan.M.loaded_segments (0xd9d9c : word) = Some W_d9d38.
Proof. vm_refl. Qed.
Lemma D_d9d38 : decode_any W_d9d38 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d3c : bv 32 := 0xfec6a423.
Lemma F_d9d3c : fetch_word Asan.M.loaded_segments (0xd9da0 : word) = Some W_d9d3c.
Proof. vm_refl. Qed.
Lemma D_d9d3c : decode_any W_d9d3c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d40 : bv 32 := 0xfec6a623.
Lemma F_d9d40 : fetch_word Asan.M.loaded_segments (0xd9da4 : word) = Some W_d9d40.
Proof. vm_refl. Qed.
Lemma D_d9d40 : decode_any W_d9d40 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d44 : bv 32 := 0xfec6a823.
Lemma F_d9d44 : fetch_word Asan.M.loaded_segments (0xd9da8 : word) = Some W_d9d44.
Proof. vm_refl. Qed.
Lemma D_d9d44 : decode_any W_d9d44 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d48 : bv 32 := 0x03076a63.
Lemma F_d9d48 : fetch_word Asan.M.loaded_segments (0xd9dac : word) = Some W_d9d48.
Proof. vm_refl. Qed.
Lemma D_d9d48 : decode_any W_d9d48 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d4c : bv 32 := 0x02061613.
Lemma F_d9d4c : fetch_word Asan.M.loaded_segments (0xd9db0 : word) = Some W_d9d4c.
Proof. vm_refl. Qed.
Lemma D_d9d4c : decode_any W_d9d4c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d50 : bv 32 := 0x00f585b3.
Lemma F_d9d50 : fetch_word Asan.M.loaded_segments (0xd9db4 : word) = Some W_d9d50.
Proof. vm_refl. Qed.
Lemma D_d9d50 : decode_any W_d9d50 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d54 : bv 32 := 0x02065693.
Lemma F_d9d54 : fetch_word Asan.M.loaded_segments (0xd9db8 : word) = Some W_d9d54.
Proof. vm_refl. Qed.
Lemma D_d9d54 : decode_any W_d9d54 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d58 : bv 32 := 0x00d66633.
Lemma F_d9d58 : fetch_word Asan.M.loaded_segments (0xd9dbc : word) = Some W_d9d58.
Proof. vm_refl. Qed.
Lemma D_d9d58 : decode_any W_d9d58 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d5c : bv 32 := 0x01f00693.
Lemma F_d9d5c : fetch_word Asan.M.loaded_segments (0xd9dc0 : word) = Some W_d9d5c.
Proof. vm_refl. Qed.
Lemma D_d9d5c : decode_any W_d9d5c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d60 : bv 32 := 0x00c5b023.
Lemma F_d9d60 : fetch_word Asan.M.loaded_segments (0xd9dc4 : word) = Some W_d9d60.
Proof. vm_refl. Qed.
Lemma D_d9d60 : decode_any W_d9d60 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d64 : bv 32 := 0x00c5b423.
Lemma F_d9d64 : fetch_word Asan.M.loaded_segments (0xd9dc8 : word) = Some W_d9d64.
Proof. vm_refl. Qed.
Lemma D_d9d64 : decode_any W_d9d64 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d68 : bv 32 := 0x00c5b823.
Lemma F_d9d68 : fetch_word Asan.M.loaded_segments (0xd9dcc : word) = Some W_d9d68.
Proof. vm_refl. Qed.
Lemma D_d9d68 : decode_any W_d9d68 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d6c : bv 32 := 0x00c5bc23.
Lemma F_d9d6c : fetch_word Asan.M.loaded_segments (0xd9dd0 : word) = Some W_d9d6c.
Proof. vm_refl. Qed.
Lemma D_d9d6c : decode_any W_d9d6c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d70 : bv 32 := 0xfe070713.
Lemma F_d9d70 : fetch_word Asan.M.loaded_segments (0xd9dd4 : word) = Some W_d9d70.
Proof. vm_refl. Qed.
Lemma D_d9d70 : decode_any W_d9d70 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d74 : bv 32 := 0x02058593.
Lemma F_d9d74 : fetch_word Asan.M.loaded_segments (0xd9dd8 : word) = Some W_d9d74.
Proof. vm_refl. Qed.
Lemma D_d9d74 : decode_any W_d9d74 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d78 : bv 32 := 0xfee6e4e3.
Lemma F_d9d78 : fetch_word Asan.M.loaded_segments (0xd9ddc : word) = Some W_d9d78.
Proof. vm_refl. Qed.
Lemma D_d9d78 : decode_any W_d9d78 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d9d7c : bv 32 := 0x00008067.
Lemma F_d9d7c : fetch_word Asan.M.loaded_segments (0xd9de0 : word) = Some W_d9d7c.
Proof. vm_refl. Qed.
Lemma D_d9d7c : decode_any W_d9d7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xd9cec%Z.
Definition Fo_000 := F_d9c88.
Definition Do_000 := D_d9c88.
Definition Fo_004 := F_d9c8c.
Definition Do_004 := D_d9c8c.
Definition Fo_008 := F_d9c90.
Definition Do_008 := D_d9c90.
Definition Fo_00c := F_d9c94.
Definition Do_00c := D_d9c94.
Definition Fo_010 := F_d9c98.
Definition Do_010 := D_d9c98.
Definition Fo_014 := F_d9c9c.
Definition Do_014 := D_d9c9c.
Definition Fo_018 := F_d9ca0.
Definition Do_018 := D_d9ca0.
Definition Fo_01c := F_d9ca4.
Definition Do_01c := D_d9ca4.
Definition Fo_020 := F_d9ca8.
Definition Do_020 := D_d9ca8.
Definition Fo_024 := F_d9cac.
Definition Do_024 := D_d9cac.
Definition Fo_028 := F_d9cb0.
Definition Do_028 := D_d9cb0.
Definition Fo_02c := F_d9cb4.
Definition Do_02c := D_d9cb4.
Definition Fo_030 := F_d9cb8.
Definition Do_030 := D_d9cb8.
Definition Fo_034 := F_d9cbc.
Definition Do_034 := D_d9cbc.
Definition Fo_038 := F_d9cc0.
Definition Do_038 := D_d9cc0.
Definition Fo_03c := F_d9cc4.
Definition Do_03c := D_d9cc4.
Definition Fo_040 := F_d9cc8.
Definition Do_040 := D_d9cc8.
Definition Fo_044 := F_d9ccc.
Definition Do_044 := D_d9ccc.
Definition Fo_048 := F_d9cd0.
Definition Do_048 := D_d9cd0.
Definition Fo_04c := F_d9cd4.
Definition Do_04c := D_d9cd4.
Definition Fo_050 := F_d9cd8.
Definition Do_050 := D_d9cd8.
Definition Fo_054 := F_d9cdc.
Definition Do_054 := D_d9cdc.
Definition Fo_058 := F_d9ce0.
Definition Do_058 := D_d9ce0.
Definition Fo_05c := F_d9ce4.
Definition Do_05c := D_d9ce4.
Definition Fo_060 := F_d9ce8.
Definition Do_060 := D_d9ce8.
Definition Fo_064 := F_d9cec.
Definition Do_064 := D_d9cec.
Definition Fo_068 := F_d9cf0.
Definition Do_068 := D_d9cf0.
Definition Fo_06c := F_d9cf4.
Definition Do_06c := D_d9cf4.
Definition Fo_070 := F_d9cf8.
Definition Do_070 := D_d9cf8.
Definition Fo_074 := F_d9cfc.
Definition Do_074 := D_d9cfc.
Definition Fo_078 := F_d9d00.
Definition Do_078 := D_d9d00.
Definition Fo_07c := F_d9d04.
Definition Do_07c := D_d9d04.
Definition Fo_080 := F_d9d08.
Definition Do_080 := D_d9d08.
Definition Fo_084 := F_d9d0c.
Definition Do_084 := D_d9d0c.
Definition Fo_088 := F_d9d10.
Definition Do_088 := D_d9d10.
Definition Fo_08c := F_d9d14.
Definition Do_08c := D_d9d14.
Definition Fo_090 := F_d9d18.
Definition Do_090 := D_d9d18.
Definition Fo_094 := F_d9d1c.
Definition Do_094 := D_d9d1c.
Definition Fo_098 := F_d9d20.
Definition Do_098 := D_d9d20.
Definition Fo_09c := F_d9d24.
Definition Do_09c := D_d9d24.
Definition Fo_0a0 := F_d9d28.
Definition Do_0a0 := D_d9d28.
Definition Fo_0a4 := F_d9d2c.
Definition Do_0a4 := D_d9d2c.
Definition Fo_0a8 := F_d9d30.
Definition Do_0a8 := D_d9d30.
Definition Fo_0ac := F_d9d34.
Definition Do_0ac := D_d9d34.
Definition Fo_0b0 := F_d9d38.
Definition Do_0b0 := D_d9d38.
Definition Fo_0b4 := F_d9d3c.
Definition Do_0b4 := D_d9d3c.
Definition Fo_0b8 := F_d9d40.
Definition Do_0b8 := D_d9d40.
Definition Fo_0bc := F_d9d44.
Definition Do_0bc := D_d9d44.
Definition Fo_0c0 := F_d9d48.
Definition Do_0c0 := D_d9d48.
Definition Fo_0c4 := F_d9d4c.
Definition Do_0c4 := D_d9d4c.
Definition Fo_0c8 := F_d9d50.
Definition Do_0c8 := D_d9d50.
Definition Fo_0cc := F_d9d54.
Definition Do_0cc := D_d9d54.
Definition Fo_0d0 := F_d9d58.
Definition Do_0d0 := D_d9d58.
Definition Fo_0d4 := F_d9d5c.
Definition Do_0d4 := D_d9d5c.
Definition Fo_0d8 := F_d9d60.
Definition Do_0d8 := D_d9d60.
Definition Fo_0dc := F_d9d64.
Definition Do_0dc := D_d9d64.
Definition Fo_0e0 := F_d9d68.
Definition Do_0e0 := D_d9d68.
Definition Fo_0e4 := F_d9d6c.
Definition Do_0e4 := D_d9d6c.
Definition Fo_0e8 := F_d9d70.
Definition Do_0e8 := D_d9d70.
Definition Fo_0ec := F_d9d74.
Definition Do_0ec := D_d9d74.
Definition Fo_0f0 := F_d9d78.
Definition Do_0f0 := D_d9d78.
Definition Fo_0f4 := F_d9d7c.
Definition Do_0f4 := D_d9d7c.
