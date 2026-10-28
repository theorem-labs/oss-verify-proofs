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
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a8e98 : bv 32 := 0x0e060a63.
Lemma F_a8e98 : fetch_word AsanUbsan.M.loaded_segments (0xab85c : word) = Some W_a8e98.
Proof. vm_refl. Qed.
Lemma D_a8e98 : decode_any W_a8e98 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e9c : bv 32 := 0x00b50023.
Lemma F_a8e9c : fetch_word AsanUbsan.M.loaded_segments (0xab860 : word) = Some W_a8e9c.
Proof. vm_refl. Qed.
Lemma D_a8e9c : decode_any W_a8e9c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ea0 : bv 32 := 0x00c506b3.
Lemma F_a8ea0 : fetch_word AsanUbsan.M.loaded_segments (0xab864 : word) = Some W_a8ea0.
Proof. vm_refl. Qed.
Lemma D_a8ea0 : decode_any W_a8ea0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ea4 : bv 32 := 0x00300713.
Lemma F_a8ea4 : fetch_word AsanUbsan.M.loaded_segments (0xab868 : word) = Some W_a8ea4.
Proof. vm_refl. Qed.
Lemma D_a8ea4 : decode_any W_a8ea4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ea8 : bv 32 := 0xfeb68fa3.
Lemma F_a8ea8 : fetch_word AsanUbsan.M.loaded_segments (0xab86c : word) = Some W_a8ea8.
Proof. vm_refl. Qed.
Lemma D_a8ea8 : decode_any W_a8ea8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8eac : bv 32 := 0x0ee66063.
Lemma F_a8eac : fetch_word AsanUbsan.M.loaded_segments (0xab870 : word) = Some W_a8eac.
Proof. vm_refl. Qed.
Lemma D_a8eac : decode_any W_a8eac = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8eb0 : bv 32 := 0x00b500a3.
Lemma F_a8eb0 : fetch_word AsanUbsan.M.loaded_segments (0xab874 : word) = Some W_a8eb0.
Proof. vm_refl. Qed.
Lemma D_a8eb0 : decode_any W_a8eb0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8eb4 : bv 32 := 0x00b50123.
Lemma F_a8eb4 : fetch_word AsanUbsan.M.loaded_segments (0xab878 : word) = Some W_a8eb4.
Proof. vm_refl. Qed.
Lemma D_a8eb4 : decode_any W_a8eb4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8eb8 : bv 32 := 0x00700713.
Lemma F_a8eb8 : fetch_word AsanUbsan.M.loaded_segments (0xab87c : word) = Some W_a8eb8.
Proof. vm_refl. Qed.
Lemma D_a8eb8 : decode_any W_a8eb8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ebc : bv 32 := 0xfeb68ea3.
Lemma F_a8ebc : fetch_word AsanUbsan.M.loaded_segments (0xab880 : word) = Some W_a8ebc.
Proof. vm_refl. Qed.
Lemma D_a8ebc : decode_any W_a8ebc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ec0 : bv 32 := 0xfeb68f23.
Lemma F_a8ec0 : fetch_word AsanUbsan.M.loaded_segments (0xab884 : word) = Some W_a8ec0.
Proof. vm_refl. Qed.
Lemma D_a8ec0 : decode_any W_a8ec0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ec4 : bv 32 := 0x0ce66463.
Lemma F_a8ec4 : fetch_word AsanUbsan.M.loaded_segments (0xab888 : word) = Some W_a8ec4.
Proof. vm_refl. Qed.
Lemma D_a8ec4 : decode_any W_a8ec4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ec8 : bv 32 := 0x00b501a3.
Lemma F_a8ec8 : fetch_word AsanUbsan.M.loaded_segments (0xab88c : word) = Some W_a8ec8.
Proof. vm_refl. Qed.
Lemma D_a8ec8 : decode_any W_a8ec8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ecc : bv 32 := 0x00900793.
Lemma F_a8ecc : fetch_word AsanUbsan.M.loaded_segments (0xab890 : word) = Some W_a8ecc.
Proof. vm_refl. Qed.
Lemma D_a8ecc : decode_any W_a8ecc = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ed0 : bv 32 := 0xfeb68e23.
Lemma F_a8ed0 : fetch_word AsanUbsan.M.loaded_segments (0xab894 : word) = Some W_a8ed0.
Proof. vm_refl. Qed.
Lemma D_a8ed0 : decode_any W_a8ed0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ed4 : bv 32 := 0x0af66c63.
Lemma F_a8ed4 : fetch_word AsanUbsan.M.loaded_segments (0xab898 : word) = Some W_a8ed4.
Proof. vm_refl. Qed.
Lemma D_a8ed4 : decode_any W_a8ed4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ed8 : bv 32 := 0x40a006bb.
Lemma F_a8ed8 : fetch_word AsanUbsan.M.loaded_segments (0xab89c : word) = Some W_a8ed8.
Proof. vm_refl. Qed.
Lemma D_a8ed8 : decode_any W_a8ed8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8edc : bv 32 := 0x03859813.
Lemma F_a8edc : fetch_word AsanUbsan.M.loaded_segments (0xab8a0 : word) = Some W_a8edc.
Proof. vm_refl. Qed.
Lemma D_a8edc : decode_any W_a8edc = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ee0 : bv 32 := 0x101015b7.
Lemma F_a8ee0 : fetch_word AsanUbsan.M.loaded_segments (0xab8a4 : word) = Some W_a8ee0.
Proof. vm_refl. Qed.
Lemma D_a8ee0 : decode_any W_a8ee0 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ee4 : bv 32 := 0x0036f693.
Lemma F_a8ee4 : fetch_word AsanUbsan.M.loaded_segments (0xab8a8 : word) = Some W_a8ee4.
Proof. vm_refl. Qed.
Lemma D_a8ee4 : decode_any W_a8ee4 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ee8 : bv 32 := 0x00459713.
Lemma F_a8ee8 : fetch_word AsanUbsan.M.loaded_segments (0xab8ac : word) = Some W_a8ee8.
Proof. vm_refl. Qed.
Lemma D_a8ee8 : decode_any W_a8ee8 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8eec : bv 32 := 0x40d60633.
Lemma F_a8eec : fetch_word AsanUbsan.M.loaded_segments (0xab8b0 : word) = Some W_a8eec.
Proof. vm_refl. Qed.
Lemma D_a8eec : decode_any W_a8eec = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ef0 : bv 32 := 0x00d505b3.
Lemma F_a8ef0 : fetch_word AsanUbsan.M.loaded_segments (0xab8b4 : word) = Some W_a8ef0.
Proof. vm_refl. Qed.
Lemma D_a8ef0 : decode_any W_a8ef0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ef4 : bv 32 := 0x10070693.
Lemma F_a8ef4 : fetch_word AsanUbsan.M.loaded_segments (0xab8b8 : word) = Some W_a8ef4.
Proof. vm_refl. Qed.
Lemma D_a8ef4 : decode_any W_a8ef4 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ef8 : bv 32 := 0xffc67713.
Lemma F_a8ef8 : fetch_word AsanUbsan.M.loaded_segments (0xab8bc : word) = Some W_a8ef8.
Proof. vm_refl. Qed.
Lemma D_a8ef8 : decode_any W_a8ef8 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8efc : bv 32 := 0x02d83633.
Lemma F_a8efc : fetch_word AsanUbsan.M.loaded_segments (0xab8c0 : word) = Some W_a8efc.
Proof. vm_refl. Qed.
Lemma D_a8efc : decode_any W_a8efc = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f00 : bv 32 := 0x00c5a023.
Lemma F_a8f00 : fetch_word AsanUbsan.M.loaded_segments (0xab8c4 : word) = Some W_a8f00.
Proof. vm_refl. Qed.
Lemma D_a8f00 : decode_any W_a8f00 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f04 : bv 32 := 0x00e586b3.
Lemma F_a8f04 : fetch_word AsanUbsan.M.loaded_segments (0xab8c8 : word) = Some W_a8f04.
Proof. vm_refl. Qed.
Lemma D_a8f04 : decode_any W_a8f04 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f08 : bv 32 := 0xfec6ae23.
Lemma F_a8f08 : fetch_word AsanUbsan.M.loaded_segments (0xab8cc : word) = Some W_a8f08.
Proof. vm_refl. Qed.
Lemma D_a8f08 : decode_any W_a8f08 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f0c : bv 32 := 0x08f76063.
Lemma F_a8f0c : fetch_word AsanUbsan.M.loaded_segments (0xab8d0 : word) = Some W_a8f0c.
Proof. vm_refl. Qed.
Lemma D_a8f0c : decode_any W_a8f0c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f10 : bv 32 := 0x00c5a223.
Lemma F_a8f10 : fetch_word AsanUbsan.M.loaded_segments (0xab8d4 : word) = Some W_a8f10.
Proof. vm_refl. Qed.
Lemma D_a8f10 : decode_any W_a8f10 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f14 : bv 32 := 0x00c5a423.
Lemma F_a8f14 : fetch_word AsanUbsan.M.loaded_segments (0xab8d8 : word) = Some W_a8f14.
Proof. vm_refl. Qed.
Lemma D_a8f14 : decode_any W_a8f14 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f18 : bv 32 := 0x01900793.
Lemma F_a8f18 : fetch_word AsanUbsan.M.loaded_segments (0xab8dc : word) = Some W_a8f18.
Proof. vm_refl. Qed.
Lemma D_a8f18 : decode_any W_a8f18 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f1c : bv 32 := 0xfec6aa23.
Lemma F_a8f1c : fetch_word AsanUbsan.M.loaded_segments (0xab8e0 : word) = Some W_a8f1c.
Proof. vm_refl. Qed.
Lemma D_a8f1c : decode_any W_a8f1c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f20 : bv 32 := 0xfec6ac23.
Lemma F_a8f20 : fetch_word AsanUbsan.M.loaded_segments (0xab8e4 : word) = Some W_a8f20.
Proof. vm_refl. Qed.
Lemma D_a8f20 : decode_any W_a8f20 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f24 : bv 32 := 0x06f76463.
Lemma F_a8f24 : fetch_word AsanUbsan.M.loaded_segments (0xab8e8 : word) = Some W_a8f24.
Proof. vm_refl. Qed.
Lemma D_a8f24 : decode_any W_a8f24 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f28 : bv 32 := 0x00c5a623.
Lemma F_a8f28 : fetch_word AsanUbsan.M.loaded_segments (0xab8ec : word) = Some W_a8f28.
Proof. vm_refl. Qed.
Lemma D_a8f28 : decode_any W_a8f28 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f2c : bv 32 := 0x00c5a823.
Lemma F_a8f2c : fetch_word AsanUbsan.M.loaded_segments (0xab8f0 : word) = Some W_a8f2c.
Proof. vm_refl. Qed.
Lemma D_a8f2c : decode_any W_a8f2c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f30 : bv 32 := 0x00c5aa23.
Lemma F_a8f30 : fetch_word AsanUbsan.M.loaded_segments (0xab8f4 : word) = Some W_a8f30.
Proof. vm_refl. Qed.
Lemma D_a8f30 : decode_any W_a8f30 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f34 : bv 32 := 0x00c5ac23.
Lemma F_a8f34 : fetch_word AsanUbsan.M.loaded_segments (0xab8f8 : word) = Some W_a8f34.
Proof. vm_refl. Qed.
Lemma D_a8f34 : decode_any W_a8f34 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f38 : bv 32 := 0x0045f793.
Lemma F_a8f38 : fetch_word AsanUbsan.M.loaded_segments (0xab8fc : word) = Some W_a8f38.
Proof. vm_refl. Qed.
Lemma D_a8f38 : decode_any W_a8f38 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f3c : bv 32 := 0x02000813.
Lemma F_a8f3c : fetch_word AsanUbsan.M.loaded_segments (0xab900 : word) = Some W_a8f3c.
Proof. vm_refl. Qed.
Lemma D_a8f3c : decode_any W_a8f3c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f40 : bv 32 := 0x01878793.
Lemma F_a8f40 : fetch_word AsanUbsan.M.loaded_segments (0xab904 : word) = Some W_a8f40.
Proof. vm_refl. Qed.
Lemma D_a8f40 : decode_any W_a8f40 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f44 : bv 32 := 0x40f70733.
Lemma F_a8f44 : fetch_word AsanUbsan.M.loaded_segments (0xab908 : word) = Some W_a8f44.
Proof. vm_refl. Qed.
Lemma D_a8f44 : decode_any W_a8f44 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f48 : bv 32 := 0xfec6a223.
Lemma F_a8f48 : fetch_word AsanUbsan.M.loaded_segments (0xab90c : word) = Some W_a8f48.
Proof. vm_refl. Qed.
Lemma D_a8f48 : decode_any W_a8f48 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f4c : bv 32 := 0xfec6a423.
Lemma F_a8f4c : fetch_word AsanUbsan.M.loaded_segments (0xab910 : word) = Some W_a8f4c.
Proof. vm_refl. Qed.
Lemma D_a8f4c : decode_any W_a8f4c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f50 : bv 32 := 0xfec6a623.
Lemma F_a8f50 : fetch_word AsanUbsan.M.loaded_segments (0xab914 : word) = Some W_a8f50.
Proof. vm_refl. Qed.
Lemma D_a8f50 : decode_any W_a8f50 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f54 : bv 32 := 0xfec6a823.
Lemma F_a8f54 : fetch_word AsanUbsan.M.loaded_segments (0xab918 : word) = Some W_a8f54.
Proof. vm_refl. Qed.
Lemma D_a8f54 : decode_any W_a8f54 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f58 : bv 32 := 0x03076a63.
Lemma F_a8f58 : fetch_word AsanUbsan.M.loaded_segments (0xab91c : word) = Some W_a8f58.
Proof. vm_refl. Qed.
Lemma D_a8f58 : decode_any W_a8f58 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f5c : bv 32 := 0x02061613.
Lemma F_a8f5c : fetch_word AsanUbsan.M.loaded_segments (0xab920 : word) = Some W_a8f5c.
Proof. vm_refl. Qed.
Lemma D_a8f5c : decode_any W_a8f5c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f60 : bv 32 := 0x00f585b3.
Lemma F_a8f60 : fetch_word AsanUbsan.M.loaded_segments (0xab924 : word) = Some W_a8f60.
Proof. vm_refl. Qed.
Lemma D_a8f60 : decode_any W_a8f60 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f64 : bv 32 := 0x02065693.
Lemma F_a8f64 : fetch_word AsanUbsan.M.loaded_segments (0xab928 : word) = Some W_a8f64.
Proof. vm_refl. Qed.
Lemma D_a8f64 : decode_any W_a8f64 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f68 : bv 32 := 0x00d66633.
Lemma F_a8f68 : fetch_word AsanUbsan.M.loaded_segments (0xab92c : word) = Some W_a8f68.
Proof. vm_refl. Qed.
Lemma D_a8f68 : decode_any W_a8f68 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f6c : bv 32 := 0x01f00693.
Lemma F_a8f6c : fetch_word AsanUbsan.M.loaded_segments (0xab930 : word) = Some W_a8f6c.
Proof. vm_refl. Qed.
Lemma D_a8f6c : decode_any W_a8f6c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f70 : bv 32 := 0x00c5b023.
Lemma F_a8f70 : fetch_word AsanUbsan.M.loaded_segments (0xab934 : word) = Some W_a8f70.
Proof. vm_refl. Qed.
Lemma D_a8f70 : decode_any W_a8f70 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f74 : bv 32 := 0x00c5b423.
Lemma F_a8f74 : fetch_word AsanUbsan.M.loaded_segments (0xab938 : word) = Some W_a8f74.
Proof. vm_refl. Qed.
Lemma D_a8f74 : decode_any W_a8f74 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f78 : bv 32 := 0x00c5b823.
Lemma F_a8f78 : fetch_word AsanUbsan.M.loaded_segments (0xab93c : word) = Some W_a8f78.
Proof. vm_refl. Qed.
Lemma D_a8f78 : decode_any W_a8f78 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f7c : bv 32 := 0x00c5bc23.
Lemma F_a8f7c : fetch_word AsanUbsan.M.loaded_segments (0xab940 : word) = Some W_a8f7c.
Proof. vm_refl. Qed.
Lemma D_a8f7c : decode_any W_a8f7c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f80 : bv 32 := 0xfe070713.
Lemma F_a8f80 : fetch_word AsanUbsan.M.loaded_segments (0xab944 : word) = Some W_a8f80.
Proof. vm_refl. Qed.
Lemma D_a8f80 : decode_any W_a8f80 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f84 : bv 32 := 0x02058593.
Lemma F_a8f84 : fetch_word AsanUbsan.M.loaded_segments (0xab948 : word) = Some W_a8f84.
Proof. vm_refl. Qed.
Lemma D_a8f84 : decode_any W_a8f84 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f88 : bv 32 := 0xfee6e4e3.
Lemma F_a8f88 : fetch_word AsanUbsan.M.loaded_segments (0xab94c : word) = Some W_a8f88.
Proof. vm_refl. Qed.
Lemma D_a8f88 : decode_any W_a8f88 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8f8c : bv 32 := 0x00008067.
Lemma F_a8f8c : fetch_word AsanUbsan.M.loaded_segments (0xab950 : word) = Some W_a8f8c.
Proof. vm_refl. Qed.
Lemma D_a8f8c : decode_any W_a8f8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xab85c%Z.
Definition Fo_000 := F_a8e98.
Definition Do_000 := D_a8e98.
Definition Fo_004 := F_a8e9c.
Definition Do_004 := D_a8e9c.
Definition Fo_008 := F_a8ea0.
Definition Do_008 := D_a8ea0.
Definition Fo_00c := F_a8ea4.
Definition Do_00c := D_a8ea4.
Definition Fo_010 := F_a8ea8.
Definition Do_010 := D_a8ea8.
Definition Fo_014 := F_a8eac.
Definition Do_014 := D_a8eac.
Definition Fo_018 := F_a8eb0.
Definition Do_018 := D_a8eb0.
Definition Fo_01c := F_a8eb4.
Definition Do_01c := D_a8eb4.
Definition Fo_020 := F_a8eb8.
Definition Do_020 := D_a8eb8.
Definition Fo_024 := F_a8ebc.
Definition Do_024 := D_a8ebc.
Definition Fo_028 := F_a8ec0.
Definition Do_028 := D_a8ec0.
Definition Fo_02c := F_a8ec4.
Definition Do_02c := D_a8ec4.
Definition Fo_030 := F_a8ec8.
Definition Do_030 := D_a8ec8.
Definition Fo_034 := F_a8ecc.
Definition Do_034 := D_a8ecc.
Definition Fo_038 := F_a8ed0.
Definition Do_038 := D_a8ed0.
Definition Fo_03c := F_a8ed4.
Definition Do_03c := D_a8ed4.
Definition Fo_040 := F_a8ed8.
Definition Do_040 := D_a8ed8.
Definition Fo_044 := F_a8edc.
Definition Do_044 := D_a8edc.
Definition Fo_048 := F_a8ee0.
Definition Do_048 := D_a8ee0.
Definition Fo_04c := F_a8ee4.
Definition Do_04c := D_a8ee4.
Definition Fo_050 := F_a8ee8.
Definition Do_050 := D_a8ee8.
Definition Fo_054 := F_a8eec.
Definition Do_054 := D_a8eec.
Definition Fo_058 := F_a8ef0.
Definition Do_058 := D_a8ef0.
Definition Fo_05c := F_a8ef4.
Definition Do_05c := D_a8ef4.
Definition Fo_060 := F_a8ef8.
Definition Do_060 := D_a8ef8.
Definition Fo_064 := F_a8efc.
Definition Do_064 := D_a8efc.
Definition Fo_068 := F_a8f00.
Definition Do_068 := D_a8f00.
Definition Fo_06c := F_a8f04.
Definition Do_06c := D_a8f04.
Definition Fo_070 := F_a8f08.
Definition Do_070 := D_a8f08.
Definition Fo_074 := F_a8f0c.
Definition Do_074 := D_a8f0c.
Definition Fo_078 := F_a8f10.
Definition Do_078 := D_a8f10.
Definition Fo_07c := F_a8f14.
Definition Do_07c := D_a8f14.
Definition Fo_080 := F_a8f18.
Definition Do_080 := D_a8f18.
Definition Fo_084 := F_a8f1c.
Definition Do_084 := D_a8f1c.
Definition Fo_088 := F_a8f20.
Definition Do_088 := D_a8f20.
Definition Fo_08c := F_a8f24.
Definition Do_08c := D_a8f24.
Definition Fo_090 := F_a8f28.
Definition Do_090 := D_a8f28.
Definition Fo_094 := F_a8f2c.
Definition Do_094 := D_a8f2c.
Definition Fo_098 := F_a8f30.
Definition Do_098 := D_a8f30.
Definition Fo_09c := F_a8f34.
Definition Do_09c := D_a8f34.
Definition Fo_0a0 := F_a8f38.
Definition Do_0a0 := D_a8f38.
Definition Fo_0a4 := F_a8f3c.
Definition Do_0a4 := D_a8f3c.
Definition Fo_0a8 := F_a8f40.
Definition Do_0a8 := D_a8f40.
Definition Fo_0ac := F_a8f44.
Definition Do_0ac := D_a8f44.
Definition Fo_0b0 := F_a8f48.
Definition Do_0b0 := D_a8f48.
Definition Fo_0b4 := F_a8f4c.
Definition Do_0b4 := D_a8f4c.
Definition Fo_0b8 := F_a8f50.
Definition Do_0b8 := D_a8f50.
Definition Fo_0bc := F_a8f54.
Definition Do_0bc := D_a8f54.
Definition Fo_0c0 := F_a8f58.
Definition Do_0c0 := D_a8f58.
Definition Fo_0c4 := F_a8f5c.
Definition Do_0c4 := D_a8f5c.
Definition Fo_0c8 := F_a8f60.
Definition Do_0c8 := D_a8f60.
Definition Fo_0cc := F_a8f64.
Definition Do_0cc := D_a8f64.
Definition Fo_0d0 := F_a8f68.
Definition Do_0d0 := D_a8f68.
Definition Fo_0d4 := F_a8f6c.
Definition Do_0d4 := D_a8f6c.
Definition Fo_0d8 := F_a8f70.
Definition Do_0d8 := D_a8f70.
Definition Fo_0dc := F_a8f74.
Definition Do_0dc := D_a8f74.
Definition Fo_0e0 := F_a8f78.
Definition Do_0e0 := D_a8f78.
Definition Fo_0e4 := F_a8f7c.
Definition Do_0e4 := D_a8f7c.
Definition Fo_0e8 := F_a8f80.
Definition Do_0e8 := D_a8f80.
Definition Fo_0ec := F_a8f84.
Definition Do_0ec := D_a8f84.
Definition Fo_0f0 := F_a8f88.
Definition Do_0f0 := D_a8f88.
Definition Fo_0f4 := F_a8f8c.
Definition Do_0f4 := D_a8f8c.
