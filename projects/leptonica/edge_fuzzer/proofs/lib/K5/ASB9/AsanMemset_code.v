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
From OSSVerify.leptonica.edge_fuzzer.images Require Import AsanUbsan.
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
Definition W_1c07a4 : bv 32 := 0x0e060a63.
Lemma F_1c07a4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1bfc : word) = Some W_1c07a4.
Proof. vm_refl. Qed.
Lemma D_1c07a4 : decode_any W_1c07a4 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07a8 : bv 32 := 0x00b50023.
Lemma F_1c07a8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c00 : word) = Some W_1c07a8.
Proof. vm_refl. Qed.
Lemma D_1c07a8 : decode_any W_1c07a8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07ac : bv 32 := 0x00c506b3.
Lemma F_1c07ac : fetch_word AsanUbsan.M.loaded_segments (0x1c1c04 : word) = Some W_1c07ac.
Proof. vm_refl. Qed.
Lemma D_1c07ac : decode_any W_1c07ac = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07b0 : bv 32 := 0x00300713.
Lemma F_1c07b0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c08 : word) = Some W_1c07b0.
Proof. vm_refl. Qed.
Lemma D_1c07b0 : decode_any W_1c07b0 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07b4 : bv 32 := 0xfeb68fa3.
Lemma F_1c07b4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c0c : word) = Some W_1c07b4.
Proof. vm_refl. Qed.
Lemma D_1c07b4 : decode_any W_1c07b4 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07b8 : bv 32 := 0x0ee66063.
Lemma F_1c07b8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c10 : word) = Some W_1c07b8.
Proof. vm_refl. Qed.
Lemma D_1c07b8 : decode_any W_1c07b8 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07bc : bv 32 := 0x00b500a3.
Lemma F_1c07bc : fetch_word AsanUbsan.M.loaded_segments (0x1c1c14 : word) = Some W_1c07bc.
Proof. vm_refl. Qed.
Lemma D_1c07bc : decode_any W_1c07bc = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07c0 : bv 32 := 0x00b50123.
Lemma F_1c07c0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c18 : word) = Some W_1c07c0.
Proof. vm_refl. Qed.
Lemma D_1c07c0 : decode_any W_1c07c0 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07c4 : bv 32 := 0x00700713.
Lemma F_1c07c4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c1c : word) = Some W_1c07c4.
Proof. vm_refl. Qed.
Lemma D_1c07c4 : decode_any W_1c07c4 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07c8 : bv 32 := 0xfeb68ea3.
Lemma F_1c07c8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c20 : word) = Some W_1c07c8.
Proof. vm_refl. Qed.
Lemma D_1c07c8 : decode_any W_1c07c8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee34 : bv 32 := 0xfeb68f23.
Lemma F_bee34 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c24 : word) = Some W_bee34.
Proof. vm_refl. Qed.
Lemma D_bee34 : decode_any W_bee34 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee38 : bv 32 := 0x0ce66463.
Lemma F_bee38 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c28 : word) = Some W_bee38.
Proof. vm_refl. Qed.
Lemma D_bee38 : decode_any W_bee38 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee3c : bv 32 := 0x00b501a3.
Lemma F_bee3c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c2c : word) = Some W_bee3c.
Proof. vm_refl. Qed.
Lemma D_bee3c : decode_any W_bee3c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee40 : bv 32 := 0x00900793.
Lemma F_bee40 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c30 : word) = Some W_bee40.
Proof. vm_refl. Qed.
Lemma D_bee40 : decode_any W_bee40 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee44 : bv 32 := 0xfeb68e23.
Lemma F_bee44 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c34 : word) = Some W_bee44.
Proof. vm_refl. Qed.
Lemma D_bee44 : decode_any W_bee44 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee48 : bv 32 := 0x0af66c63.
Lemma F_bee48 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c38 : word) = Some W_bee48.
Proof. vm_refl. Qed.
Lemma D_bee48 : decode_any W_bee48 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee4c : bv 32 := 0x40a006bb.
Lemma F_bee4c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c3c : word) = Some W_bee4c.
Proof. vm_refl. Qed.
Lemma D_bee4c : decode_any W_bee4c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee50 : bv 32 := 0x03859813.
Lemma F_bee50 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c40 : word) = Some W_bee50.
Proof. vm_refl. Qed.
Lemma D_bee50 : decode_any W_bee50 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee54 : bv 32 := 0x101015b7.
Lemma F_bee54 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c44 : word) = Some W_bee54.
Proof. vm_refl. Qed.
Lemma D_bee54 : decode_any W_bee54 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee58 : bv 32 := 0x0036f693.
Lemma F_bee58 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c48 : word) = Some W_bee58.
Proof. vm_refl. Qed.
Lemma D_bee58 : decode_any W_bee58 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee5c : bv 32 := 0x00459713.
Lemma F_bee5c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c4c : word) = Some W_bee5c.
Proof. vm_refl. Qed.
Lemma D_bee5c : decode_any W_bee5c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee60 : bv 32 := 0x40d60633.
Lemma F_bee60 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c50 : word) = Some W_bee60.
Proof. vm_refl. Qed.
Lemma D_bee60 : decode_any W_bee60 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee64 : bv 32 := 0x00d505b3.
Lemma F_bee64 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c54 : word) = Some W_bee64.
Proof. vm_refl. Qed.
Lemma D_bee64 : decode_any W_bee64 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee68 : bv 32 := 0x10070693.
Lemma F_bee68 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c58 : word) = Some W_bee68.
Proof. vm_refl. Qed.
Lemma D_bee68 : decode_any W_bee68 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee6c : bv 32 := 0xffc67713.
Lemma F_bee6c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c5c : word) = Some W_bee6c.
Proof. vm_refl. Qed.
Lemma D_bee6c : decode_any W_bee6c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee70 : bv 32 := 0x02d83633.
Lemma F_bee70 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c60 : word) = Some W_bee70.
Proof. vm_refl. Qed.
Lemma D_bee70 : decode_any W_bee70 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee74 : bv 32 := 0x00c5a023.
Lemma F_bee74 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c64 : word) = Some W_bee74.
Proof. vm_refl. Qed.
Lemma D_bee74 : decode_any W_bee74 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee78 : bv 32 := 0x00e586b3.
Lemma F_bee78 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c68 : word) = Some W_bee78.
Proof. vm_refl. Qed.
Lemma D_bee78 : decode_any W_bee78 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee7c : bv 32 := 0xfec6ae23.
Lemma F_bee7c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c6c : word) = Some W_bee7c.
Proof. vm_refl. Qed.
Lemma D_bee7c : decode_any W_bee7c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee80 : bv 32 := 0x08f76063.
Lemma F_bee80 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c70 : word) = Some W_bee80.
Proof. vm_refl. Qed.
Lemma D_bee80 : decode_any W_bee80 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee84 : bv 32 := 0x00c5a223.
Lemma F_bee84 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c74 : word) = Some W_bee84.
Proof. vm_refl. Qed.
Lemma D_bee84 : decode_any W_bee84 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee88 : bv 32 := 0x00c5a423.
Lemma F_bee88 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c78 : word) = Some W_bee88.
Proof. vm_refl. Qed.
Lemma D_bee88 : decode_any W_bee88 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee8c : bv 32 := 0x01900793.
Lemma F_bee8c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c7c : word) = Some W_bee8c.
Proof. vm_refl. Qed.
Lemma D_bee8c : decode_any W_bee8c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee90 : bv 32 := 0xfec6aa23.
Lemma F_bee90 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c80 : word) = Some W_bee90.
Proof. vm_refl. Qed.
Lemma D_bee90 : decode_any W_bee90 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee94 : bv 32 := 0xfec6ac23.
Lemma F_bee94 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c84 : word) = Some W_bee94.
Proof. vm_refl. Qed.
Lemma D_bee94 : decode_any W_bee94 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee98 : bv 32 := 0x06f76463.
Lemma F_bee98 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c88 : word) = Some W_bee98.
Proof. vm_refl. Qed.
Lemma D_bee98 : decode_any W_bee98 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bee9c : bv 32 := 0x00c5a623.
Lemma F_bee9c : fetch_word AsanUbsan.M.loaded_segments (0x1c1c8c : word) = Some W_bee9c.
Proof. vm_refl. Qed.
Lemma D_bee9c : decode_any W_bee9c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beea0 : bv 32 := 0x00c5a823.
Lemma F_beea0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c90 : word) = Some W_beea0.
Proof. vm_refl. Qed.
Lemma D_beea0 : decode_any W_beea0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beea4 : bv 32 := 0x00c5aa23.
Lemma F_beea4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c94 : word) = Some W_beea4.
Proof. vm_refl. Qed.
Lemma D_beea4 : decode_any W_beea4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beea8 : bv 32 := 0x00c5ac23.
Lemma F_beea8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1c98 : word) = Some W_beea8.
Proof. vm_refl. Qed.
Lemma D_beea8 : decode_any W_beea8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beeac : bv 32 := 0x0045f793.
Lemma F_beeac : fetch_word AsanUbsan.M.loaded_segments (0x1c1c9c : word) = Some W_beeac.
Proof. vm_refl. Qed.
Lemma D_beeac : decode_any W_beeac = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beeb0 : bv 32 := 0x02000813.
Lemma F_beeb0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1ca0 : word) = Some W_beeb0.
Proof. vm_refl. Qed.
Lemma D_beeb0 : decode_any W_beeb0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beeb4 : bv 32 := 0x01878793.
Lemma F_beeb4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1ca4 : word) = Some W_beeb4.
Proof. vm_refl. Qed.
Lemma D_beeb4 : decode_any W_beeb4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beeb8 : bv 32 := 0x40f70733.
Lemma F_beeb8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1ca8 : word) = Some W_beeb8.
Proof. vm_refl. Qed.
Lemma D_beeb8 : decode_any W_beeb8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beebc : bv 32 := 0xfec6a223.
Lemma F_beebc : fetch_word AsanUbsan.M.loaded_segments (0x1c1cac : word) = Some W_beebc.
Proof. vm_refl. Qed.
Lemma D_beebc : decode_any W_beebc = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beec0 : bv 32 := 0xfec6a423.
Lemma F_beec0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cb0 : word) = Some W_beec0.
Proof. vm_refl. Qed.
Lemma D_beec0 : decode_any W_beec0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beec4 : bv 32 := 0xfec6a623.
Lemma F_beec4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cb4 : word) = Some W_beec4.
Proof. vm_refl. Qed.
Lemma D_beec4 : decode_any W_beec4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beec8 : bv 32 := 0xfec6a823.
Lemma F_beec8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cb8 : word) = Some W_beec8.
Proof. vm_refl. Qed.
Lemma D_beec8 : decode_any W_beec8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beecc : bv 32 := 0x03076a63.
Lemma F_beecc : fetch_word AsanUbsan.M.loaded_segments (0x1c1cbc : word) = Some W_beecc.
Proof. vm_refl. Qed.
Lemma D_beecc : decode_any W_beecc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beed0 : bv 32 := 0x02061613.
Lemma F_beed0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cc0 : word) = Some W_beed0.
Proof. vm_refl. Qed.
Lemma D_beed0 : decode_any W_beed0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beed4 : bv 32 := 0x00f585b3.
Lemma F_beed4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cc4 : word) = Some W_beed4.
Proof. vm_refl. Qed.
Lemma D_beed4 : decode_any W_beed4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beed8 : bv 32 := 0x02065693.
Lemma F_beed8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cc8 : word) = Some W_beed8.
Proof. vm_refl. Qed.
Lemma D_beed8 : decode_any W_beed8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beedc : bv 32 := 0x00d66633.
Lemma F_beedc : fetch_word AsanUbsan.M.loaded_segments (0x1c1ccc : word) = Some W_beedc.
Proof. vm_refl. Qed.
Lemma D_beedc : decode_any W_beedc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beee0 : bv 32 := 0x01f00693.
Lemma F_beee0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cd0 : word) = Some W_beee0.
Proof. vm_refl. Qed.
Lemma D_beee0 : decode_any W_beee0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beee4 : bv 32 := 0x00c5b023.
Lemma F_beee4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cd4 : word) = Some W_beee4.
Proof. vm_refl. Qed.
Lemma D_beee4 : decode_any W_beee4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beee8 : bv 32 := 0x00c5b423.
Lemma F_beee8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cd8 : word) = Some W_beee8.
Proof. vm_refl. Qed.
Lemma D_beee8 : decode_any W_beee8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beeec : bv 32 := 0x00c5b823.
Lemma F_beeec : fetch_word AsanUbsan.M.loaded_segments (0x1c1cdc : word) = Some W_beeec.
Proof. vm_refl. Qed.
Lemma D_beeec : decode_any W_beeec = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beef0 : bv 32 := 0x00c5bc23.
Lemma F_beef0 : fetch_word AsanUbsan.M.loaded_segments (0x1c1ce0 : word) = Some W_beef0.
Proof. vm_refl. Qed.
Lemma D_beef0 : decode_any W_beef0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beef4 : bv 32 := 0xfe070713.
Lemma F_beef4 : fetch_word AsanUbsan.M.loaded_segments (0x1c1ce4 : word) = Some W_beef4.
Proof. vm_refl. Qed.
Lemma D_beef4 : decode_any W_beef4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beef8 : bv 32 := 0x02058593.
Lemma F_beef8 : fetch_word AsanUbsan.M.loaded_segments (0x1c1ce8 : word) = Some W_beef8.
Proof. vm_refl. Qed.
Lemma D_beef8 : decode_any W_beef8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_beefc : bv 32 := 0xfee6e4e3.
Lemma F_beefc : fetch_word AsanUbsan.M.loaded_segments (0x1c1cec : word) = Some W_beefc.
Proof. vm_refl. Qed.
Lemma D_beefc : decode_any W_beefc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bef00 : bv 32 := 0x00008067.
Lemma F_bef00 : fetch_word AsanUbsan.M.loaded_segments (0x1c1cf0 : word) = Some W_bef00.
Proof. vm_refl. Qed.
Lemma D_bef00 : decode_any W_bef00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x1c1bfc%Z.
Definition Fo_000 := F_1c07a4.
Definition Do_000 := D_1c07a4.
Definition Fo_004 := F_1c07a8.
Definition Do_004 := D_1c07a8.
Definition Fo_008 := F_1c07ac.
Definition Do_008 := D_1c07ac.
Definition Fo_00c := F_1c07b0.
Definition Do_00c := D_1c07b0.
Definition Fo_010 := F_1c07b4.
Definition Do_010 := D_1c07b4.
Definition Fo_014 := F_1c07b8.
Definition Do_014 := D_1c07b8.
Definition Fo_018 := F_1c07bc.
Definition Do_018 := D_1c07bc.
Definition Fo_01c := F_1c07c0.
Definition Do_01c := D_1c07c0.
Definition Fo_020 := F_1c07c4.
Definition Do_020 := D_1c07c4.
Definition Fo_024 := F_1c07c8.
Definition Do_024 := D_1c07c8.
Definition Fo_028 := F_bee34.
Definition Do_028 := D_bee34.
Definition Fo_02c := F_bee38.
Definition Do_02c := D_bee38.
Definition Fo_030 := F_bee3c.
Definition Do_030 := D_bee3c.
Definition Fo_034 := F_bee40.
Definition Do_034 := D_bee40.
Definition Fo_038 := F_bee44.
Definition Do_038 := D_bee44.
Definition Fo_03c := F_bee48.
Definition Do_03c := D_bee48.
Definition Fo_040 := F_bee4c.
Definition Do_040 := D_bee4c.
Definition Fo_044 := F_bee50.
Definition Do_044 := D_bee50.
Definition Fo_048 := F_bee54.
Definition Do_048 := D_bee54.
Definition Fo_04c := F_bee58.
Definition Do_04c := D_bee58.
Definition Fo_050 := F_bee5c.
Definition Do_050 := D_bee5c.
Definition Fo_054 := F_bee60.
Definition Do_054 := D_bee60.
Definition Fo_058 := F_bee64.
Definition Do_058 := D_bee64.
Definition Fo_05c := F_bee68.
Definition Do_05c := D_bee68.
Definition Fo_060 := F_bee6c.
Definition Do_060 := D_bee6c.
Definition Fo_064 := F_bee70.
Definition Do_064 := D_bee70.
Definition Fo_068 := F_bee74.
Definition Do_068 := D_bee74.
Definition Fo_06c := F_bee78.
Definition Do_06c := D_bee78.
Definition Fo_070 := F_bee7c.
Definition Do_070 := D_bee7c.
Definition Fo_074 := F_bee80.
Definition Do_074 := D_bee80.
Definition Fo_078 := F_bee84.
Definition Do_078 := D_bee84.
Definition Fo_07c := F_bee88.
Definition Do_07c := D_bee88.
Definition Fo_080 := F_bee8c.
Definition Do_080 := D_bee8c.
Definition Fo_084 := F_bee90.
Definition Do_084 := D_bee90.
Definition Fo_088 := F_bee94.
Definition Do_088 := D_bee94.
Definition Fo_08c := F_bee98.
Definition Do_08c := D_bee98.
Definition Fo_090 := F_bee9c.
Definition Do_090 := D_bee9c.
Definition Fo_094 := F_beea0.
Definition Do_094 := D_beea0.
Definition Fo_098 := F_beea4.
Definition Do_098 := D_beea4.
Definition Fo_09c := F_beea8.
Definition Do_09c := D_beea8.
Definition Fo_0a0 := F_beeac.
Definition Do_0a0 := D_beeac.
Definition Fo_0a4 := F_beeb0.
Definition Do_0a4 := D_beeb0.
Definition Fo_0a8 := F_beeb4.
Definition Do_0a8 := D_beeb4.
Definition Fo_0ac := F_beeb8.
Definition Do_0ac := D_beeb8.
Definition Fo_0b0 := F_beebc.
Definition Do_0b0 := D_beebc.
Definition Fo_0b4 := F_beec0.
Definition Do_0b4 := D_beec0.
Definition Fo_0b8 := F_beec4.
Definition Do_0b8 := D_beec4.
Definition Fo_0bc := F_beec8.
Definition Do_0bc := D_beec8.
Definition Fo_0c0 := F_beecc.
Definition Do_0c0 := D_beecc.
Definition Fo_0c4 := F_beed0.
Definition Do_0c4 := D_beed0.
Definition Fo_0c8 := F_beed4.
Definition Do_0c8 := D_beed4.
Definition Fo_0cc := F_beed8.
Definition Do_0cc := D_beed8.
Definition Fo_0d0 := F_beedc.
Definition Do_0d0 := D_beedc.
Definition Fo_0d4 := F_beee0.
Definition Do_0d4 := D_beee0.
Definition Fo_0d8 := F_beee4.
Definition Do_0d8 := D_beee4.
Definition Fo_0dc := F_beee8.
Definition Do_0dc := D_beee8.
Definition Fo_0e0 := F_beeec.
Definition Do_0e0 := D_beeec.
Definition Fo_0e4 := F_beef0.
Definition Do_0e4 := D_beef0.
Definition Fo_0e8 := F_beef4.
Definition Do_0e8 := D_beef4.
Definition Fo_0ec := F_beef8.
Definition Do_0ec := D_beef8.
Definition Fo_0f0 := F_beefc.
Definition Do_0f0 := D_beefc.
Definition Fo_0f4 := F_bef00.
Definition Do_0f4 := D_bef00.
