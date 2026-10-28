(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_127714 : bv 32 := 0x0e060a63.
Lemma F_127714 : fetch_word AsanUbsan.M.loaded_segments (0x129d04 : word) = Some W_127714.
Proof. vm_refl. Qed.
Lemma D_127714 : decode_any W_127714 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127718 : bv 32 := 0x00b50023.
Lemma F_127718 : fetch_word AsanUbsan.M.loaded_segments (0x129d08 : word) = Some W_127718.
Proof. vm_refl. Qed.
Lemma D_127718 : decode_any W_127718 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12771c : bv 32 := 0x00c506b3.
Lemma F_12771c : fetch_word AsanUbsan.M.loaded_segments (0x129d0c : word) = Some W_12771c.
Proof. vm_refl. Qed.
Lemma D_12771c : decode_any W_12771c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127720 : bv 32 := 0x00300713.
Lemma F_127720 : fetch_word AsanUbsan.M.loaded_segments (0x129d10 : word) = Some W_127720.
Proof. vm_refl. Qed.
Lemma D_127720 : decode_any W_127720 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127724 : bv 32 := 0xfeb68fa3.
Lemma F_127724 : fetch_word AsanUbsan.M.loaded_segments (0x129d14 : word) = Some W_127724.
Proof. vm_refl. Qed.
Lemma D_127724 : decode_any W_127724 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127728 : bv 32 := 0x0ee66063.
Lemma F_127728 : fetch_word AsanUbsan.M.loaded_segments (0x129d18 : word) = Some W_127728.
Proof. vm_refl. Qed.
Lemma D_127728 : decode_any W_127728 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12772c : bv 32 := 0x00b500a3.
Lemma F_12772c : fetch_word AsanUbsan.M.loaded_segments (0x129d1c : word) = Some W_12772c.
Proof. vm_refl. Qed.
Lemma D_12772c : decode_any W_12772c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127730 : bv 32 := 0x00b50123.
Lemma F_127730 : fetch_word AsanUbsan.M.loaded_segments (0x129d20 : word) = Some W_127730.
Proof. vm_refl. Qed.
Lemma D_127730 : decode_any W_127730 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127734 : bv 32 := 0x00700713.
Lemma F_127734 : fetch_word AsanUbsan.M.loaded_segments (0x129d24 : word) = Some W_127734.
Proof. vm_refl. Qed.
Lemma D_127734 : decode_any W_127734 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127738 : bv 32 := 0xfeb68ea3.
Lemma F_127738 : fetch_word AsanUbsan.M.loaded_segments (0x129d28 : word) = Some W_127738.
Proof. vm_refl. Qed.
Lemma D_127738 : decode_any W_127738 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12773c : bv 32 := 0xfeb68f23.
Lemma F_12773c : fetch_word AsanUbsan.M.loaded_segments (0x129d2c : word) = Some W_12773c.
Proof. vm_refl. Qed.
Lemma D_12773c : decode_any W_12773c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127740 : bv 32 := 0x0ce66463.
Lemma F_127740 : fetch_word AsanUbsan.M.loaded_segments (0x129d30 : word) = Some W_127740.
Proof. vm_refl. Qed.
Lemma D_127740 : decode_any W_127740 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127744 : bv 32 := 0x00b501a3.
Lemma F_127744 : fetch_word AsanUbsan.M.loaded_segments (0x129d34 : word) = Some W_127744.
Proof. vm_refl. Qed.
Lemma D_127744 : decode_any W_127744 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127748 : bv 32 := 0x00900793.
Lemma F_127748 : fetch_word AsanUbsan.M.loaded_segments (0x129d38 : word) = Some W_127748.
Proof. vm_refl. Qed.
Lemma D_127748 : decode_any W_127748 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12774c : bv 32 := 0xfeb68e23.
Lemma F_12774c : fetch_word AsanUbsan.M.loaded_segments (0x129d3c : word) = Some W_12774c.
Proof. vm_refl. Qed.
Lemma D_12774c : decode_any W_12774c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127750 : bv 32 := 0x0af66c63.
Lemma F_127750 : fetch_word AsanUbsan.M.loaded_segments (0x129d40 : word) = Some W_127750.
Proof. vm_refl. Qed.
Lemma D_127750 : decode_any W_127750 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127754 : bv 32 := 0x40a006bb.
Lemma F_127754 : fetch_word AsanUbsan.M.loaded_segments (0x129d44 : word) = Some W_127754.
Proof. vm_refl. Qed.
Lemma D_127754 : decode_any W_127754 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127758 : bv 32 := 0x03859813.
Lemma F_127758 : fetch_word AsanUbsan.M.loaded_segments (0x129d48 : word) = Some W_127758.
Proof. vm_refl. Qed.
Lemma D_127758 : decode_any W_127758 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12775c : bv 32 := 0x101015b7.
Lemma F_12775c : fetch_word AsanUbsan.M.loaded_segments (0x129d4c : word) = Some W_12775c.
Proof. vm_refl. Qed.
Lemma D_12775c : decode_any W_12775c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127760 : bv 32 := 0x0036f693.
Lemma F_127760 : fetch_word AsanUbsan.M.loaded_segments (0x129d50 : word) = Some W_127760.
Proof. vm_refl. Qed.
Lemma D_127760 : decode_any W_127760 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127764 : bv 32 := 0x00459713.
Lemma F_127764 : fetch_word AsanUbsan.M.loaded_segments (0x129d54 : word) = Some W_127764.
Proof. vm_refl. Qed.
Lemma D_127764 : decode_any W_127764 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127768 : bv 32 := 0x40d60633.
Lemma F_127768 : fetch_word AsanUbsan.M.loaded_segments (0x129d58 : word) = Some W_127768.
Proof. vm_refl. Qed.
Lemma D_127768 : decode_any W_127768 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12776c : bv 32 := 0x00d505b3.
Lemma F_12776c : fetch_word AsanUbsan.M.loaded_segments (0x129d5c : word) = Some W_12776c.
Proof. vm_refl. Qed.
Lemma D_12776c : decode_any W_12776c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127770 : bv 32 := 0x10070693.
Lemma F_127770 : fetch_word AsanUbsan.M.loaded_segments (0x129d60 : word) = Some W_127770.
Proof. vm_refl. Qed.
Lemma D_127770 : decode_any W_127770 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127774 : bv 32 := 0xffc67713.
Lemma F_127774 : fetch_word AsanUbsan.M.loaded_segments (0x129d64 : word) = Some W_127774.
Proof. vm_refl. Qed.
Lemma D_127774 : decode_any W_127774 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127778 : bv 32 := 0x02d83633.
Lemma F_127778 : fetch_word AsanUbsan.M.loaded_segments (0x129d68 : word) = Some W_127778.
Proof. vm_refl. Qed.
Lemma D_127778 : decode_any W_127778 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12777c : bv 32 := 0x00c5a023.
Lemma F_12777c : fetch_word AsanUbsan.M.loaded_segments (0x129d6c : word) = Some W_12777c.
Proof. vm_refl. Qed.
Lemma D_12777c : decode_any W_12777c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127780 : bv 32 := 0x00e586b3.
Lemma F_127780 : fetch_word AsanUbsan.M.loaded_segments (0x129d70 : word) = Some W_127780.
Proof. vm_refl. Qed.
Lemma D_127780 : decode_any W_127780 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127784 : bv 32 := 0xfec6ae23.
Lemma F_127784 : fetch_word AsanUbsan.M.loaded_segments (0x129d74 : word) = Some W_127784.
Proof. vm_refl. Qed.
Lemma D_127784 : decode_any W_127784 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127788 : bv 32 := 0x08f76063.
Lemma F_127788 : fetch_word AsanUbsan.M.loaded_segments (0x129d78 : word) = Some W_127788.
Proof. vm_refl. Qed.
Lemma D_127788 : decode_any W_127788 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12778c : bv 32 := 0x00c5a223.
Lemma F_12778c : fetch_word AsanUbsan.M.loaded_segments (0x129d7c : word) = Some W_12778c.
Proof. vm_refl. Qed.
Lemma D_12778c : decode_any W_12778c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127790 : bv 32 := 0x00c5a423.
Lemma F_127790 : fetch_word AsanUbsan.M.loaded_segments (0x129d80 : word) = Some W_127790.
Proof. vm_refl. Qed.
Lemma D_127790 : decode_any W_127790 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127794 : bv 32 := 0x01900793.
Lemma F_127794 : fetch_word AsanUbsan.M.loaded_segments (0x129d84 : word) = Some W_127794.
Proof. vm_refl. Qed.
Lemma D_127794 : decode_any W_127794 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127798 : bv 32 := 0xfec6aa23.
Lemma F_127798 : fetch_word AsanUbsan.M.loaded_segments (0x129d88 : word) = Some W_127798.
Proof. vm_refl. Qed.
Lemma D_127798 : decode_any W_127798 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12779c : bv 32 := 0xfec6ac23.
Lemma F_12779c : fetch_word AsanUbsan.M.loaded_segments (0x129d8c : word) = Some W_12779c.
Proof. vm_refl. Qed.
Lemma D_12779c : decode_any W_12779c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277a0 : bv 32 := 0x06f76463.
Lemma F_1277a0 : fetch_word AsanUbsan.M.loaded_segments (0x129d90 : word) = Some W_1277a0.
Proof. vm_refl. Qed.
Lemma D_1277a0 : decode_any W_1277a0 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277a4 : bv 32 := 0x00c5a623.
Lemma F_1277a4 : fetch_word AsanUbsan.M.loaded_segments (0x129d94 : word) = Some W_1277a4.
Proof. vm_refl. Qed.
Lemma D_1277a4 : decode_any W_1277a4 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277a8 : bv 32 := 0x00c5a823.
Lemma F_1277a8 : fetch_word AsanUbsan.M.loaded_segments (0x129d98 : word) = Some W_1277a8.
Proof. vm_refl. Qed.
Lemma D_1277a8 : decode_any W_1277a8 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277ac : bv 32 := 0x00c5aa23.
Lemma F_1277ac : fetch_word AsanUbsan.M.loaded_segments (0x129d9c : word) = Some W_1277ac.
Proof. vm_refl. Qed.
Lemma D_1277ac : decode_any W_1277ac = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277b0 : bv 32 := 0x00c5ac23.
Lemma F_1277b0 : fetch_word AsanUbsan.M.loaded_segments (0x129da0 : word) = Some W_1277b0.
Proof. vm_refl. Qed.
Lemma D_1277b0 : decode_any W_1277b0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277b4 : bv 32 := 0x0045f793.
Lemma F_1277b4 : fetch_word AsanUbsan.M.loaded_segments (0x129da4 : word) = Some W_1277b4.
Proof. vm_refl. Qed.
Lemma D_1277b4 : decode_any W_1277b4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277b8 : bv 32 := 0x02000813.
Lemma F_1277b8 : fetch_word AsanUbsan.M.loaded_segments (0x129da8 : word) = Some W_1277b8.
Proof. vm_refl. Qed.
Lemma D_1277b8 : decode_any W_1277b8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277bc : bv 32 := 0x01878793.
Lemma F_1277bc : fetch_word AsanUbsan.M.loaded_segments (0x129dac : word) = Some W_1277bc.
Proof. vm_refl. Qed.
Lemma D_1277bc : decode_any W_1277bc = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277c0 : bv 32 := 0x40f70733.
Lemma F_1277c0 : fetch_word AsanUbsan.M.loaded_segments (0x129db0 : word) = Some W_1277c0.
Proof. vm_refl. Qed.
Lemma D_1277c0 : decode_any W_1277c0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277c4 : bv 32 := 0xfec6a223.
Lemma F_1277c4 : fetch_word AsanUbsan.M.loaded_segments (0x129db4 : word) = Some W_1277c4.
Proof. vm_refl. Qed.
Lemma D_1277c4 : decode_any W_1277c4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277c8 : bv 32 := 0xfec6a423.
Lemma F_1277c8 : fetch_word AsanUbsan.M.loaded_segments (0x129db8 : word) = Some W_1277c8.
Proof. vm_refl. Qed.
Lemma D_1277c8 : decode_any W_1277c8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277cc : bv 32 := 0xfec6a623.
Lemma F_1277cc : fetch_word AsanUbsan.M.loaded_segments (0x129dbc : word) = Some W_1277cc.
Proof. vm_refl. Qed.
Lemma D_1277cc : decode_any W_1277cc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277d0 : bv 32 := 0xfec6a823.
Lemma F_1277d0 : fetch_word AsanUbsan.M.loaded_segments (0x129dc0 : word) = Some W_1277d0.
Proof. vm_refl. Qed.
Lemma D_1277d0 : decode_any W_1277d0 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277d4 : bv 32 := 0x03076a63.
Lemma F_1277d4 : fetch_word AsanUbsan.M.loaded_segments (0x129dc4 : word) = Some W_1277d4.
Proof. vm_refl. Qed.
Lemma D_1277d4 : decode_any W_1277d4 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277d8 : bv 32 := 0x02061613.
Lemma F_1277d8 : fetch_word AsanUbsan.M.loaded_segments (0x129dc8 : word) = Some W_1277d8.
Proof. vm_refl. Qed.
Lemma D_1277d8 : decode_any W_1277d8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277dc : bv 32 := 0x00f585b3.
Lemma F_1277dc : fetch_word AsanUbsan.M.loaded_segments (0x129dcc : word) = Some W_1277dc.
Proof. vm_refl. Qed.
Lemma D_1277dc : decode_any W_1277dc = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277e0 : bv 32 := 0x02065693.
Lemma F_1277e0 : fetch_word AsanUbsan.M.loaded_segments (0x129dd0 : word) = Some W_1277e0.
Proof. vm_refl. Qed.
Lemma D_1277e0 : decode_any W_1277e0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277e4 : bv 32 := 0x00d66633.
Lemma F_1277e4 : fetch_word AsanUbsan.M.loaded_segments (0x129dd4 : word) = Some W_1277e4.
Proof. vm_refl. Qed.
Lemma D_1277e4 : decode_any W_1277e4 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277e8 : bv 32 := 0x01f00693.
Lemma F_1277e8 : fetch_word AsanUbsan.M.loaded_segments (0x129dd8 : word) = Some W_1277e8.
Proof. vm_refl. Qed.
Lemma D_1277e8 : decode_any W_1277e8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277ec : bv 32 := 0x00c5b023.
Lemma F_1277ec : fetch_word AsanUbsan.M.loaded_segments (0x129ddc : word) = Some W_1277ec.
Proof. vm_refl. Qed.
Lemma D_1277ec : decode_any W_1277ec = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277f0 : bv 32 := 0x00c5b423.
Lemma F_1277f0 : fetch_word AsanUbsan.M.loaded_segments (0x129de0 : word) = Some W_1277f0.
Proof. vm_refl. Qed.
Lemma D_1277f0 : decode_any W_1277f0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277f4 : bv 32 := 0x00c5b823.
Lemma F_1277f4 : fetch_word AsanUbsan.M.loaded_segments (0x129de4 : word) = Some W_1277f4.
Proof. vm_refl. Qed.
Lemma D_1277f4 : decode_any W_1277f4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277f8 : bv 32 := 0x00c5bc23.
Lemma F_1277f8 : fetch_word AsanUbsan.M.loaded_segments (0x129de8 : word) = Some W_1277f8.
Proof. vm_refl. Qed.
Lemma D_1277f8 : decode_any W_1277f8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1277fc : bv 32 := 0xfe070713.
Lemma F_1277fc : fetch_word AsanUbsan.M.loaded_segments (0x129dec : word) = Some W_1277fc.
Proof. vm_refl. Qed.
Lemma D_1277fc : decode_any W_1277fc = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127800 : bv 32 := 0x02058593.
Lemma F_127800 : fetch_word AsanUbsan.M.loaded_segments (0x129df0 : word) = Some W_127800.
Proof. vm_refl. Qed.
Lemma D_127800 : decode_any W_127800 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127804 : bv 32 := 0xfee6e4e3.
Lemma F_127804 : fetch_word AsanUbsan.M.loaded_segments (0x129df4 : word) = Some W_127804.
Proof. vm_refl. Qed.
Lemma D_127804 : decode_any W_127804 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_127808 : bv 32 := 0x00008067.
Lemma F_127808 : fetch_word AsanUbsan.M.loaded_segments (0x129df8 : word) = Some W_127808.
Proof. vm_refl. Qed.
Lemma D_127808 : decode_any W_127808 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x129d04%Z.
Definition Fo_000 := F_127714.
Definition Do_000 := D_127714.
Definition Fo_004 := F_127718.
Definition Do_004 := D_127718.
Definition Fo_008 := F_12771c.
Definition Do_008 := D_12771c.
Definition Fo_00c := F_127720.
Definition Do_00c := D_127720.
Definition Fo_010 := F_127724.
Definition Do_010 := D_127724.
Definition Fo_014 := F_127728.
Definition Do_014 := D_127728.
Definition Fo_018 := F_12772c.
Definition Do_018 := D_12772c.
Definition Fo_01c := F_127730.
Definition Do_01c := D_127730.
Definition Fo_020 := F_127734.
Definition Do_020 := D_127734.
Definition Fo_024 := F_127738.
Definition Do_024 := D_127738.
Definition Fo_028 := F_12773c.
Definition Do_028 := D_12773c.
Definition Fo_02c := F_127740.
Definition Do_02c := D_127740.
Definition Fo_030 := F_127744.
Definition Do_030 := D_127744.
Definition Fo_034 := F_127748.
Definition Do_034 := D_127748.
Definition Fo_038 := F_12774c.
Definition Do_038 := D_12774c.
Definition Fo_03c := F_127750.
Definition Do_03c := D_127750.
Definition Fo_040 := F_127754.
Definition Do_040 := D_127754.
Definition Fo_044 := F_127758.
Definition Do_044 := D_127758.
Definition Fo_048 := F_12775c.
Definition Do_048 := D_12775c.
Definition Fo_04c := F_127760.
Definition Do_04c := D_127760.
Definition Fo_050 := F_127764.
Definition Do_050 := D_127764.
Definition Fo_054 := F_127768.
Definition Do_054 := D_127768.
Definition Fo_058 := F_12776c.
Definition Do_058 := D_12776c.
Definition Fo_05c := F_127770.
Definition Do_05c := D_127770.
Definition Fo_060 := F_127774.
Definition Do_060 := D_127774.
Definition Fo_064 := F_127778.
Definition Do_064 := D_127778.
Definition Fo_068 := F_12777c.
Definition Do_068 := D_12777c.
Definition Fo_06c := F_127780.
Definition Do_06c := D_127780.
Definition Fo_070 := F_127784.
Definition Do_070 := D_127784.
Definition Fo_074 := F_127788.
Definition Do_074 := D_127788.
Definition Fo_078 := F_12778c.
Definition Do_078 := D_12778c.
Definition Fo_07c := F_127790.
Definition Do_07c := D_127790.
Definition Fo_080 := F_127794.
Definition Do_080 := D_127794.
Definition Fo_084 := F_127798.
Definition Do_084 := D_127798.
Definition Fo_088 := F_12779c.
Definition Do_088 := D_12779c.
Definition Fo_08c := F_1277a0.
Definition Do_08c := D_1277a0.
Definition Fo_090 := F_1277a4.
Definition Do_090 := D_1277a4.
Definition Fo_094 := F_1277a8.
Definition Do_094 := D_1277a8.
Definition Fo_098 := F_1277ac.
Definition Do_098 := D_1277ac.
Definition Fo_09c := F_1277b0.
Definition Do_09c := D_1277b0.
Definition Fo_0a0 := F_1277b4.
Definition Do_0a0 := D_1277b4.
Definition Fo_0a4 := F_1277b8.
Definition Do_0a4 := D_1277b8.
Definition Fo_0a8 := F_1277bc.
Definition Do_0a8 := D_1277bc.
Definition Fo_0ac := F_1277c0.
Definition Do_0ac := D_1277c0.
Definition Fo_0b0 := F_1277c4.
Definition Do_0b0 := D_1277c4.
Definition Fo_0b4 := F_1277c8.
Definition Do_0b4 := D_1277c8.
Definition Fo_0b8 := F_1277cc.
Definition Do_0b8 := D_1277cc.
Definition Fo_0bc := F_1277d0.
Definition Do_0bc := D_1277d0.
Definition Fo_0c0 := F_1277d4.
Definition Do_0c0 := D_1277d4.
Definition Fo_0c4 := F_1277d8.
Definition Do_0c4 := D_1277d8.
Definition Fo_0c8 := F_1277dc.
Definition Do_0c8 := D_1277dc.
Definition Fo_0cc := F_1277e0.
Definition Do_0cc := D_1277e0.
Definition Fo_0d0 := F_1277e4.
Definition Do_0d0 := D_1277e4.
Definition Fo_0d4 := F_1277e8.
Definition Do_0d4 := D_1277e8.
Definition Fo_0d8 := F_1277ec.
Definition Do_0d8 := D_1277ec.
Definition Fo_0dc := F_1277f0.
Definition Do_0dc := D_1277f0.
Definition Fo_0e0 := F_1277f4.
Definition Do_0e0 := D_1277f4.
Definition Fo_0e4 := F_1277f8.
Definition Do_0e4 := D_1277f8.
Definition Fo_0e8 := F_1277fc.
Definition Do_0e8 := D_1277fc.
Definition Fo_0ec := F_127800.
Definition Do_0ec := D_127800.
Definition Fo_0f0 := F_127804.
Definition Do_0f0 := D_127804.
Definition Fo_0f4 := F_127808.
Definition Do_0f4 := D_127808.
