(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_126be8 : bv 32 := 0x0e060a63.
Lemma F_126be8 : fetch_word AsanUbsan.M.loaded_segments (0x126be8 : word) = Some W_126be8.
Proof. vm_refl. Qed.
Lemma D_126be8 : decode_any W_126be8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.
Definition W_126bec : bv 32 := 0x00b50023.
Lemma F_126bec : fetch_word AsanUbsan.M.loaded_segments (0x126bec : word) = Some W_126bec.
Proof. vm_refl. Qed.
Lemma D_126bec : decode_any W_126bec = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_126bf0 : bv 32 := 0x00c506b3.
Lemma F_126bf0 : fetch_word AsanUbsan.M.loaded_segments (0x126bf0 : word) = Some W_126bf0.
Proof. vm_refl. Qed.
Lemma D_126bf0 : decode_any W_126bf0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_126bf4 : bv 32 := 0x00300713.
Lemma F_126bf4 : fetch_word AsanUbsan.M.loaded_segments (0x126bf4 : word) = Some W_126bf4.
Proof. vm_refl. Qed.
Lemma D_126bf4 : decode_any W_126bf4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_126bf8 : bv 32 := 0xfeb68fa3.
Lemma F_126bf8 : fetch_word AsanUbsan.M.loaded_segments (0x126bf8 : word) = Some W_126bf8.
Proof. vm_refl. Qed.
Lemma D_126bf8 : decode_any W_126bf8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_126bfc : bv 32 := 0x0ee66063.
Lemma F_126bfc : fetch_word AsanUbsan.M.loaded_segments (0x126bfc : word) = Some W_126bfc.
Proof. vm_refl. Qed.
Lemma D_126bfc : decode_any W_126bfc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c00 : bv 32 := 0x00b500a3.
Lemma F_126c00 : fetch_word AsanUbsan.M.loaded_segments (0x126c00 : word) = Some W_126c00.
Proof. vm_refl. Qed.
Lemma D_126c00 : decode_any W_126c00 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c04 : bv 32 := 0x00b50123.
Lemma F_126c04 : fetch_word AsanUbsan.M.loaded_segments (0x126c04 : word) = Some W_126c04.
Proof. vm_refl. Qed.
Lemma D_126c04 : decode_any W_126c04 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c08 : bv 32 := 0x00700713.
Lemma F_126c08 : fetch_word AsanUbsan.M.loaded_segments (0x126c08 : word) = Some W_126c08.
Proof. vm_refl. Qed.
Lemma D_126c08 : decode_any W_126c08 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c0c : bv 32 := 0xfeb68ea3.
Lemma F_126c0c : fetch_word AsanUbsan.M.loaded_segments (0x126c0c : word) = Some W_126c0c.
Proof. vm_refl. Qed.
Lemma D_126c0c : decode_any W_126c0c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c10 : bv 32 := 0xfeb68f23.
Lemma F_126c10 : fetch_word AsanUbsan.M.loaded_segments (0x126c10 : word) = Some W_126c10.
Proof. vm_refl. Qed.
Lemma D_126c10 : decode_any W_126c10 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c14 : bv 32 := 0x0ce66463.
Lemma F_126c14 : fetch_word AsanUbsan.M.loaded_segments (0x126c14 : word) = Some W_126c14.
Proof. vm_refl. Qed.
Lemma D_126c14 : decode_any W_126c14 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c18 : bv 32 := 0x00b501a3.
Lemma F_126c18 : fetch_word AsanUbsan.M.loaded_segments (0x126c18 : word) = Some W_126c18.
Proof. vm_refl. Qed.
Lemma D_126c18 : decode_any W_126c18 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c1c : bv 32 := 0x00900793.
Lemma F_126c1c : fetch_word AsanUbsan.M.loaded_segments (0x126c1c : word) = Some W_126c1c.
Proof. vm_refl. Qed.
Lemma D_126c1c : decode_any W_126c1c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c20 : bv 32 := 0xfeb68e23.
Lemma F_126c20 : fetch_word AsanUbsan.M.loaded_segments (0x126c20 : word) = Some W_126c20.
Proof. vm_refl. Qed.
Lemma D_126c20 : decode_any W_126c20 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c24 : bv 32 := 0x0af66c63.
Lemma F_126c24 : fetch_word AsanUbsan.M.loaded_segments (0x126c24 : word) = Some W_126c24.
Proof. vm_refl. Qed.
Lemma D_126c24 : decode_any W_126c24 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c28 : bv 32 := 0x40a006bb.
Lemma F_126c28 : fetch_word AsanUbsan.M.loaded_segments (0x126c28 : word) = Some W_126c28.
Proof. vm_refl. Qed.
Lemma D_126c28 : decode_any W_126c28 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c2c : bv 32 := 0x03859813.
Lemma F_126c2c : fetch_word AsanUbsan.M.loaded_segments (0x126c2c : word) = Some W_126c2c.
Proof. vm_refl. Qed.
Lemma D_126c2c : decode_any W_126c2c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c30 : bv 32 := 0x101015b7.
Lemma F_126c30 : fetch_word AsanUbsan.M.loaded_segments (0x126c30 : word) = Some W_126c30.
Proof. vm_refl. Qed.
Lemma D_126c30 : decode_any W_126c30 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c34 : bv 32 := 0x0036f693.
Lemma F_126c34 : fetch_word AsanUbsan.M.loaded_segments (0x126c34 : word) = Some W_126c34.
Proof. vm_refl. Qed.
Lemma D_126c34 : decode_any W_126c34 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c38 : bv 32 := 0x00459713.
Lemma F_126c38 : fetch_word AsanUbsan.M.loaded_segments (0x126c38 : word) = Some W_126c38.
Proof. vm_refl. Qed.
Lemma D_126c38 : decode_any W_126c38 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c3c : bv 32 := 0x40d60633.
Lemma F_126c3c : fetch_word AsanUbsan.M.loaded_segments (0x126c3c : word) = Some W_126c3c.
Proof. vm_refl. Qed.
Lemma D_126c3c : decode_any W_126c3c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c40 : bv 32 := 0x00d505b3.
Lemma F_126c40 : fetch_word AsanUbsan.M.loaded_segments (0x126c40 : word) = Some W_126c40.
Proof. vm_refl. Qed.
Lemma D_126c40 : decode_any W_126c40 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c44 : bv 32 := 0x10070693.
Lemma F_126c44 : fetch_word AsanUbsan.M.loaded_segments (0x126c44 : word) = Some W_126c44.
Proof. vm_refl. Qed.
Lemma D_126c44 : decode_any W_126c44 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c48 : bv 32 := 0xffc67713.
Lemma F_126c48 : fetch_word AsanUbsan.M.loaded_segments (0x126c48 : word) = Some W_126c48.
Proof. vm_refl. Qed.
Lemma D_126c48 : decode_any W_126c48 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c4c : bv 32 := 0x02d83633.
Lemma F_126c4c : fetch_word AsanUbsan.M.loaded_segments (0x126c4c : word) = Some W_126c4c.
Proof. vm_refl. Qed.
Lemma D_126c4c : decode_any W_126c4c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c50 : bv 32 := 0x00c5a023.
Lemma F_126c50 : fetch_word AsanUbsan.M.loaded_segments (0x126c50 : word) = Some W_126c50.
Proof. vm_refl. Qed.
Lemma D_126c50 : decode_any W_126c50 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c54 : bv 32 := 0x00e586b3.
Lemma F_126c54 : fetch_word AsanUbsan.M.loaded_segments (0x126c54 : word) = Some W_126c54.
Proof. vm_refl. Qed.
Lemma D_126c54 : decode_any W_126c54 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c58 : bv 32 := 0xfec6ae23.
Lemma F_126c58 : fetch_word AsanUbsan.M.loaded_segments (0x126c58 : word) = Some W_126c58.
Proof. vm_refl. Qed.
Lemma D_126c58 : decode_any W_126c58 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c5c : bv 32 := 0x08f76063.
Lemma F_126c5c : fetch_word AsanUbsan.M.loaded_segments (0x126c5c : word) = Some W_126c5c.
Proof. vm_refl. Qed.
Lemma D_126c5c : decode_any W_126c5c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c60 : bv 32 := 0x00c5a223.
Lemma F_126c60 : fetch_word AsanUbsan.M.loaded_segments (0x126c60 : word) = Some W_126c60.
Proof. vm_refl. Qed.
Lemma D_126c60 : decode_any W_126c60 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c64 : bv 32 := 0x00c5a423.
Lemma F_126c64 : fetch_word AsanUbsan.M.loaded_segments (0x126c64 : word) = Some W_126c64.
Proof. vm_refl. Qed.
Lemma D_126c64 : decode_any W_126c64 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c68 : bv 32 := 0x01900793.
Lemma F_126c68 : fetch_word AsanUbsan.M.loaded_segments (0x126c68 : word) = Some W_126c68.
Proof. vm_refl. Qed.
Lemma D_126c68 : decode_any W_126c68 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c6c : bv 32 := 0xfec6aa23.
Lemma F_126c6c : fetch_word AsanUbsan.M.loaded_segments (0x126c6c : word) = Some W_126c6c.
Proof. vm_refl. Qed.
Lemma D_126c6c : decode_any W_126c6c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c70 : bv 32 := 0xfec6ac23.
Lemma F_126c70 : fetch_word AsanUbsan.M.loaded_segments (0x126c70 : word) = Some W_126c70.
Proof. vm_refl. Qed.
Lemma D_126c70 : decode_any W_126c70 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c74 : bv 32 := 0x06f76463.
Lemma F_126c74 : fetch_word AsanUbsan.M.loaded_segments (0x126c74 : word) = Some W_126c74.
Proof. vm_refl. Qed.
Lemma D_126c74 : decode_any W_126c74 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c78 : bv 32 := 0x00c5a623.
Lemma F_126c78 : fetch_word AsanUbsan.M.loaded_segments (0x126c78 : word) = Some W_126c78.
Proof. vm_refl. Qed.
Lemma D_126c78 : decode_any W_126c78 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c7c : bv 32 := 0x00c5a823.
Lemma F_126c7c : fetch_word AsanUbsan.M.loaded_segments (0x126c7c : word) = Some W_126c7c.
Proof. vm_refl. Qed.
Lemma D_126c7c : decode_any W_126c7c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c80 : bv 32 := 0x00c5aa23.
Lemma F_126c80 : fetch_word AsanUbsan.M.loaded_segments (0x126c80 : word) = Some W_126c80.
Proof. vm_refl. Qed.
Lemma D_126c80 : decode_any W_126c80 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c84 : bv 32 := 0x00c5ac23.
Lemma F_126c84 : fetch_word AsanUbsan.M.loaded_segments (0x126c84 : word) = Some W_126c84.
Proof. vm_refl. Qed.
Lemma D_126c84 : decode_any W_126c84 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c88 : bv 32 := 0x0045f793.
Lemma F_126c88 : fetch_word AsanUbsan.M.loaded_segments (0x126c88 : word) = Some W_126c88.
Proof. vm_refl. Qed.
Lemma D_126c88 : decode_any W_126c88 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c8c : bv 32 := 0x02000813.
Lemma F_126c8c : fetch_word AsanUbsan.M.loaded_segments (0x126c8c : word) = Some W_126c8c.
Proof. vm_refl. Qed.
Lemma D_126c8c : decode_any W_126c8c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c90 : bv 32 := 0x01878793.
Lemma F_126c90 : fetch_word AsanUbsan.M.loaded_segments (0x126c90 : word) = Some W_126c90.
Proof. vm_refl. Qed.
Lemma D_126c90 : decode_any W_126c90 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c94 : bv 32 := 0x40f70733.
Lemma F_126c94 : fetch_word AsanUbsan.M.loaded_segments (0x126c94 : word) = Some W_126c94.
Proof. vm_refl. Qed.
Lemma D_126c94 : decode_any W_126c94 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c98 : bv 32 := 0xfec6a223.
Lemma F_126c98 : fetch_word AsanUbsan.M.loaded_segments (0x126c98 : word) = Some W_126c98.
Proof. vm_refl. Qed.
Lemma D_126c98 : decode_any W_126c98 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.
Definition W_126c9c : bv 32 := 0xfec6a423.
Lemma F_126c9c : fetch_word AsanUbsan.M.loaded_segments (0x126c9c : word) = Some W_126c9c.
Proof. vm_refl. Qed.
Lemma D_126c9c : decode_any W_126c9c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.
Definition W_126ca0 : bv 32 := 0xfec6a623.
Lemma F_126ca0 : fetch_word AsanUbsan.M.loaded_segments (0x126ca0 : word) = Some W_126ca0.
Proof. vm_refl. Qed.
Lemma D_126ca0 : decode_any W_126ca0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.
Definition W_126ca4 : bv 32 := 0xfec6a823.
Lemma F_126ca4 : fetch_word AsanUbsan.M.loaded_segments (0x126ca4 : word) = Some W_126ca4.
Proof. vm_refl. Qed.
Lemma D_126ca4 : decode_any W_126ca4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_126ca8 : bv 32 := 0x03076a63.
Lemma F_126ca8 : fetch_word AsanUbsan.M.loaded_segments (0x126ca8 : word) = Some W_126ca8.
Proof. vm_refl. Qed.
Lemma D_126ca8 : decode_any W_126ca8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cac : bv 32 := 0x02061613.
Lemma F_126cac : fetch_word AsanUbsan.M.loaded_segments (0x126cac : word) = Some W_126cac.
Proof. vm_refl. Qed.
Lemma D_126cac : decode_any W_126cac = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cb0 : bv 32 := 0x00f585b3.
Lemma F_126cb0 : fetch_word AsanUbsan.M.loaded_segments (0x126cb0 : word) = Some W_126cb0.
Proof. vm_refl. Qed.
Lemma D_126cb0 : decode_any W_126cb0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cb4 : bv 32 := 0x02065693.
Lemma F_126cb4 : fetch_word AsanUbsan.M.loaded_segments (0x126cb4 : word) = Some W_126cb4.
Proof. vm_refl. Qed.
Lemma D_126cb4 : decode_any W_126cb4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cb8 : bv 32 := 0x00d66633.
Lemma F_126cb8 : fetch_word AsanUbsan.M.loaded_segments (0x126cb8 : word) = Some W_126cb8.
Proof. vm_refl. Qed.
Lemma D_126cb8 : decode_any W_126cb8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cbc : bv 32 := 0x01f00693.
Lemma F_126cbc : fetch_word AsanUbsan.M.loaded_segments (0x126cbc : word) = Some W_126cbc.
Proof. vm_refl. Qed.
Lemma D_126cbc : decode_any W_126cbc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cc0 : bv 32 := 0x00c5b023.
Lemma F_126cc0 : fetch_word AsanUbsan.M.loaded_segments (0x126cc0 : word) = Some W_126cc0.
Proof. vm_refl. Qed.
Lemma D_126cc0 : decode_any W_126cc0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cc4 : bv 32 := 0x00c5b423.
Lemma F_126cc4 : fetch_word AsanUbsan.M.loaded_segments (0x126cc4 : word) = Some W_126cc4.
Proof. vm_refl. Qed.
Lemma D_126cc4 : decode_any W_126cc4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cc8 : bv 32 := 0x00c5b823.
Lemma F_126cc8 : fetch_word AsanUbsan.M.loaded_segments (0x126cc8 : word) = Some W_126cc8.
Proof. vm_refl. Qed.
Lemma D_126cc8 : decode_any W_126cc8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_126ccc : bv 32 := 0x00c5bc23.
Lemma F_126ccc : fetch_word AsanUbsan.M.loaded_segments (0x126ccc : word) = Some W_126ccc.
Proof. vm_refl. Qed.
Lemma D_126ccc : decode_any W_126ccc = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cd0 : bv 32 := 0xfe070713.
Lemma F_126cd0 : fetch_word AsanUbsan.M.loaded_segments (0x126cd0 : word) = Some W_126cd0.
Proof. vm_refl. Qed.
Lemma D_126cd0 : decode_any W_126cd0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cd4 : bv 32 := 0x02058593.
Lemma F_126cd4 : fetch_word AsanUbsan.M.loaded_segments (0x126cd4 : word) = Some W_126cd4.
Proof. vm_refl. Qed.
Lemma D_126cd4 : decode_any W_126cd4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cd8 : bv 32 := 0xfee6e4e3.
Lemma F_126cd8 : fetch_word AsanUbsan.M.loaded_segments (0x126cd8 : word) = Some W_126cd8.
Proof. vm_refl. Qed.
Lemma D_126cd8 : decode_any W_126cd8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.
Definition W_126cdc : bv 32 := 0x00008067.
Lemma F_126cdc : fetch_word AsanUbsan.M.loaded_segments (0x126cdc : word) = Some W_126cdc.
Proof. vm_refl. Qed.
Lemma D_126cdc : decode_any W_126cdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x126be8%Z.
Definition Fo_000 := F_126be8.
Definition Do_000 := D_126be8.
Definition Fo_004 := F_126bec.
Definition Do_004 := D_126bec.
Definition Fo_008 := F_126bf0.
Definition Do_008 := D_126bf0.
Definition Fo_00c := F_126bf4.
Definition Do_00c := D_126bf4.
Definition Fo_010 := F_126bf8.
Definition Do_010 := D_126bf8.
Definition Fo_014 := F_126bfc.
Definition Do_014 := D_126bfc.
Definition Fo_018 := F_126c00.
Definition Do_018 := D_126c00.
Definition Fo_01c := F_126c04.
Definition Do_01c := D_126c04.
Definition Fo_020 := F_126c08.
Definition Do_020 := D_126c08.
Definition Fo_024 := F_126c0c.
Definition Do_024 := D_126c0c.
Definition Fo_028 := F_126c10.
Definition Do_028 := D_126c10.
Definition Fo_02c := F_126c14.
Definition Do_02c := D_126c14.
Definition Fo_030 := F_126c18.
Definition Do_030 := D_126c18.
Definition Fo_034 := F_126c1c.
Definition Do_034 := D_126c1c.
Definition Fo_038 := F_126c20.
Definition Do_038 := D_126c20.
Definition Fo_03c := F_126c24.
Definition Do_03c := D_126c24.
Definition Fo_040 := F_126c28.
Definition Do_040 := D_126c28.
Definition Fo_044 := F_126c2c.
Definition Do_044 := D_126c2c.
Definition Fo_048 := F_126c30.
Definition Do_048 := D_126c30.
Definition Fo_04c := F_126c34.
Definition Do_04c := D_126c34.
Definition Fo_050 := F_126c38.
Definition Do_050 := D_126c38.
Definition Fo_054 := F_126c3c.
Definition Do_054 := D_126c3c.
Definition Fo_058 := F_126c40.
Definition Do_058 := D_126c40.
Definition Fo_05c := F_126c44.
Definition Do_05c := D_126c44.
Definition Fo_060 := F_126c48.
Definition Do_060 := D_126c48.
Definition Fo_064 := F_126c4c.
Definition Do_064 := D_126c4c.
Definition Fo_068 := F_126c50.
Definition Do_068 := D_126c50.
Definition Fo_06c := F_126c54.
Definition Do_06c := D_126c54.
Definition Fo_070 := F_126c58.
Definition Do_070 := D_126c58.
Definition Fo_074 := F_126c5c.
Definition Do_074 := D_126c5c.
Definition Fo_078 := F_126c60.
Definition Do_078 := D_126c60.
Definition Fo_07c := F_126c64.
Definition Do_07c := D_126c64.
Definition Fo_080 := F_126c68.
Definition Do_080 := D_126c68.
Definition Fo_084 := F_126c6c.
Definition Do_084 := D_126c6c.
Definition Fo_088 := F_126c70.
Definition Do_088 := D_126c70.
Definition Fo_08c := F_126c74.
Definition Do_08c := D_126c74.
Definition Fo_090 := F_126c78.
Definition Do_090 := D_126c78.
Definition Fo_094 := F_126c7c.
Definition Do_094 := D_126c7c.
Definition Fo_098 := F_126c80.
Definition Do_098 := D_126c80.
Definition Fo_09c := F_126c84.
Definition Do_09c := D_126c84.
Definition Fo_0a0 := F_126c88.
Definition Do_0a0 := D_126c88.
Definition Fo_0a4 := F_126c8c.
Definition Do_0a4 := D_126c8c.
Definition Fo_0a8 := F_126c90.
Definition Do_0a8 := D_126c90.
Definition Fo_0ac := F_126c94.
Definition Do_0ac := D_126c94.
Definition Fo_0b0 := F_126c98.
Definition Do_0b0 := D_126c98.
Definition Fo_0b4 := F_126c9c.
Definition Do_0b4 := D_126c9c.
Definition Fo_0b8 := F_126ca0.
Definition Do_0b8 := D_126ca0.
Definition Fo_0bc := F_126ca4.
Definition Do_0bc := D_126ca4.
Definition Fo_0c0 := F_126ca8.
Definition Do_0c0 := D_126ca8.
Definition Fo_0c4 := F_126cac.
Definition Do_0c4 := D_126cac.
Definition Fo_0c8 := F_126cb0.
Definition Do_0c8 := D_126cb0.
Definition Fo_0cc := F_126cb4.
Definition Do_0cc := D_126cb4.
Definition Fo_0d0 := F_126cb8.
Definition Do_0d0 := D_126cb8.
Definition Fo_0d4 := F_126cbc.
Definition Do_0d4 := D_126cbc.
Definition Fo_0d8 := F_126cc0.
Definition Do_0d8 := D_126cc0.
Definition Fo_0dc := F_126cc4.
Definition Do_0dc := D_126cc4.
Definition Fo_0e0 := F_126cc8.
Definition Do_0e0 := D_126cc8.
Definition Fo_0e4 := F_126ccc.
Definition Do_0e4 := D_126ccc.
Definition Fo_0e8 := F_126cd0.
Definition Do_0e8 := D_126cd0.
Definition Fo_0ec := F_126cd4.
Definition Do_0ec := D_126cd4.
Definition Fo_0f0 := F_126cd8.
Definition Do_0f0 := D_126cd8.
Definition Fo_0f4 := F_126cdc.
Definition Do_0f4 := D_126cdc.
