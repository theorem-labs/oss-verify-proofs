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
Definition W_90bfc : bv 32 := 0xf7010113.
Lemma F_90bfc : fetch_word AsanUbsan.M.loaded_segments (0x91014 : word) = Some W_90bfc.
Proof. vm_refl. Qed.
Lemma D_90bfc : decode_any W_90bfc = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c00 : bv 32 := 0x08113423.
Lemma F_90c00 : fetch_word AsanUbsan.M.loaded_segments (0x91018 : word) = Some W_90c00.
Proof. vm_refl. Qed.
Lemma D_90c00 : decode_any W_90c00 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c04 : bv 32 := 0x08813023.
Lemma F_90c04 : fetch_word AsanUbsan.M.loaded_segments (0x9101c : word) = Some W_90c04.
Proof. vm_refl. Qed.
Lemma D_90c04 : decode_any W_90c04 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c08 : bv 32 := 0x06913c23.
Lemma F_90c08 : fetch_word AsanUbsan.M.loaded_segments (0x91020 : word) = Some W_90c08.
Proof. vm_refl. Qed.
Lemma D_90c08 : decode_any W_90c08 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c0c : bv 32 := 0x07213823.
Lemma F_90c0c : fetch_word AsanUbsan.M.loaded_segments (0x91024 : word) = Some W_90c0c.
Proof. vm_refl. Qed.
Lemma D_90c0c : decode_any W_90c0c = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c10 : bv 32 := 0x07313423.
Lemma F_90c10 : fetch_word AsanUbsan.M.loaded_segments (0x91028 : word) = Some W_90c10.
Proof. vm_refl. Qed.
Lemma D_90c10 : decode_any W_90c10 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c14 : bv 32 := 0x07413023.
Lemma F_90c14 : fetch_word AsanUbsan.M.loaded_segments (0x9102c : word) = Some W_90c14.
Proof. vm_refl. Qed.
Lemma D_90c14 : decode_any W_90c14 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c18 : bv 32 := 0x05513c23.
Lemma F_90c18 : fetch_word AsanUbsan.M.loaded_segments (0x91030 : word) = Some W_90c18.
Proof. vm_refl. Qed.
Lemma D_90c18 : decode_any W_90c18 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c1c : bv 32 := 0x05613823.
Lemma F_90c1c : fetch_word AsanUbsan.M.loaded_segments (0x91034 : word) = Some W_90c1c.
Proof. vm_refl. Qed.
Lemma D_90c1c : decode_any W_90c1c = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c20 : bv 32 := 0x05713423.
Lemma F_90c20 : fetch_word AsanUbsan.M.loaded_segments (0x91038 : word) = Some W_90c20.
Proof. vm_refl. Qed.
Lemma D_90c20 : decode_any W_90c20 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c24 : bv 32 := 0x05813023.
Lemma F_90c24 : fetch_word AsanUbsan.M.loaded_segments (0x9103c : word) = Some W_90c24.
Proof. vm_refl. Qed.
Lemma D_90c24 : decode_any W_90c24 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c28 : bv 32 := 0x03913c23.
Lemma F_90c28 : fetch_word AsanUbsan.M.loaded_segments (0x91040 : word) = Some W_90c28.
Proof. vm_refl. Qed.
Lemma D_90c28 : decode_any W_90c28 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c2c : bv 32 := 0x03a13823.
Lemma F_90c2c : fetch_word AsanUbsan.M.loaded_segments (0x91044 : word) = Some W_90c2c.
Proof. vm_refl. Qed.
Lemma D_90c2c : decode_any W_90c2c = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c30 : bv 32 := 0x03b13423.
Lemma F_90c30 : fetch_word AsanUbsan.M.loaded_segments (0x91048 : word) = Some W_90c30.
Proof. vm_refl. Qed.
Lemma D_90c30 : decode_any W_90c30 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c34 : bv 32 := 0x00058913.
Lemma F_90c34 : fetch_word AsanUbsan.M.loaded_segments (0x9104c : word) = Some W_90c34.
Proof. vm_refl. Qed.
Lemma D_90c34 : decode_any W_90c34 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c38 : bv 32 := 0x000a6597.
Lemma F_90c38 : fetch_word AsanUbsan.M.loaded_segments (0x91050 : word) = Some W_90c38.
Proof. vm_refl. Qed.
Lemma D_90c38 : decode_any W_90c38 = Some (Auipc 11 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c3c : bv 32 := 0x4605b583.
Lemma F_90c3c : fetch_word AsanUbsan.M.loaded_segments (0x91054 : word) = Some W_90c3c.
Proof. vm_refl. Qed.
Lemma D_90c3c : decode_any W_90c3c = Some (Load SZ8 true 11 11 1120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c40 : bv 32 := 0x0895c583.
Lemma F_90c40 : fetch_word AsanUbsan.M.loaded_segments (0x91058 : word) = Some W_90c40.
Proof. vm_refl. Qed.
Lemma D_90c40 : decode_any W_90c40 = Some (Load SZ1 false 11 11 137, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c44 : bv 32 := 0x18058a63.
Lemma F_90c44 : fetch_word AsanUbsan.M.loaded_segments (0x9105c : word) = Some W_90c44.
Proof. vm_refl. Qed.
Lemma D_90c44 : decode_any W_90c44 = Some (Branch BC_EQ 11 0 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c48 : bv 32 := 0x00050993.
Lemma F_90c48 : fetch_word AsanUbsan.M.loaded_segments (0x91060 : word) = Some W_90c48.
Proof. vm_refl. Qed.
Lemma D_90c48 : decode_any W_90c48 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c4c : bv 32 := 0x000a6517.
Lemma F_90c4c : fetch_word AsanUbsan.M.loaded_segments (0x91064 : word) = Some W_90c4c.
Proof. vm_refl. Qed.
Lemma D_90c4c : decode_any W_90c4c = Some (Auipc 10 166, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c50 : bv 32 := 0x4ac53d03.
Lemma F_90c50 : fetch_word AsanUbsan.M.loaded_segments (0x91068 : word) = Some W_90c50.
Proof. vm_refl. Qed.
Lemma D_90c50 : decode_any W_90c50 = Some (Load SZ8 true 26 10 1196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c54 : bv 32 := 0x0009ba03.
Lemma F_90c54 : fetch_word AsanUbsan.M.loaded_segments (0x9106c : word) = Some W_90c54.
Proof. vm_refl. Qed.
Lemma D_90c54 : decode_any W_90c54 = Some (Load SZ8 true 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c58 : bv 32 := 0x000a7517.
Lemma F_90c58 : fetch_word AsanUbsan.M.loaded_segments (0x91070 : word) = Some W_90c58.
Proof. vm_refl. Qed.
Lemma D_90c58 : decode_any W_90c58 = Some (Auipc 10 167, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c5c : bv 32 := 0x000d2583.
Lemma F_90c5c : fetch_word AsanUbsan.M.loaded_segments (0x91074 : word) = Some W_90c5c.
Proof. vm_refl. Qed.
Lemma D_90c5c : decode_any W_90c5c = Some (Load SZ4 true 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c60 : bv 32 := 0x25853a83.
Lemma F_90c60 : fetch_word AsanUbsan.M.loaded_segments (0x91078 : word) = Some W_90c60.
Proof. vm_refl. Qed.
Lemma D_90c60 : decode_any W_90c60 = Some (Load SZ8 true 21 10 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c64 : bv 32 := 0x00300513.
Lemma F_90c64 : fetch_word AsanUbsan.M.loaded_segments (0x9107c : word) = Some W_90c64.
Proof. vm_refl. Qed.
Lemma D_90c64 : decode_any W_90c64 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c68 : bv 32 := 0x004a8ab3.
Lemma F_90c68 : fetch_word AsanUbsan.M.loaded_segments (0x91080 : word) = Some W_90c68.
Proof. vm_refl. Qed.
Lemma D_90c68 : decode_any W_90c68 = Some (Op ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c6c : bv 32 := 0x1ea5fa63.
Lemma F_90c6c : fetch_word AsanUbsan.M.loaded_segments (0x91084 : word) = Some W_90c6c.
Proof. vm_refl. Qed.
Lemma D_90c6c : decode_any W_90c6c = Some (Branch BC_GEU 11 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c70 : bv 32 := 0x000abb03.
Lemma F_90c70 : fetch_word AsanUbsan.M.loaded_segments (0x91088 : word) = Some W_90c70.
Proof. vm_refl. Qed.
Lemma D_90c70 : decode_any W_90c70 = Some (Load SZ8 true 22 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c74 : bv 32 := 0xfff00513.
Lemma F_90c74 : fetch_word AsanUbsan.M.loaded_segments (0x9108c : word) = Some W_90c74.
Proof. vm_refl. Qed.
Lemma D_90c74 : decode_any W_90c74 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c78 : bv 32 := 0x0230000f.
Lemma F_90c78 : fetch_word AsanUbsan.M.loaded_segments (0x91090 : word) = Some W_90c78.
Proof. vm_refl. Qed.
Lemma D_90c78 : decode_any W_90c78 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c7c : bv 32 := 0x14ab0e63.
Lemma F_90c7c : fetch_word AsanUbsan.M.loaded_segments (0x91094 : word) = Some W_90c7c.
Proof. vm_refl. Qed.
Lemma D_90c7c : decode_any W_90c7c = Some (Branch BC_EQ 22 10 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90c80 : bv 32 := 0x080b1263.
Lemma F_90c80 : fetch_word AsanUbsan.M.loaded_segments (0x91098 : word) = Some W_90c80.
Proof. vm_refl. Qed.
Lemma D_90c80 : decode_any W_90c80 = Some (Branch BC_NE 22 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90d04 : bv 32 := 0x0c0b0a63.
Lemma F_90d04 : fetch_word AsanUbsan.M.loaded_segments (0x9111c : word) = Some W_90d04.
Proof. vm_refl. Qed.
Lemma D_90d04 : decode_any W_90d04 = Some (Branch BC_EQ 22 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90d08 : bv 32 := 0x00c13823.
Lemma F_90d08 : fetch_word AsanUbsan.M.loaded_segments (0x91120 : word) = Some W_90d08.
Proof. vm_refl. Qed.
Lemma D_90d08 : decode_any W_90d08 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90d0c : bv 32 := 0x00d13c23.
Lemma F_90d0c : fetch_word AsanUbsan.M.loaded_segments (0x91124 : word) = Some W_90d0c.
Proof. vm_refl. Qed.
Lemma D_90d0c : decode_any W_90d0c = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90d10 : bv 32 := 0x0ff00513.
Lemma F_90d10 : fetch_word AsanUbsan.M.loaded_segments (0x91128 : word) = Some W_90d10.
Proof. vm_refl. Qed.
Lemma D_90d10 : decode_any W_90d10 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90d14 : bv 32 := 0x0aaa6863.
Lemma F_90d14 : fetch_word AsanUbsan.M.loaded_segments (0x9112c : word) = Some W_90d14.
Proof. vm_refl. Qed.
Lemma D_90d14 : decode_any W_90d14 = Some (Branch BC_LTU 20 10 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dc4 : bv 32 := 0x000b0513.
Lemma F_90dc4 : fetch_word AsanUbsan.M.loaded_segments (0x911dc : word) = Some W_90dc4.
Proof. vm_refl. Qed.
Lemma D_90dc4 : decode_any W_90dc4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dc8 : bv 32 := 0x004a1413.
Lemma F_90dc8 : fetch_word AsanUbsan.M.loaded_segments (0x911e0 : word) = Some W_90dc8.
Proof. vm_refl. Qed.
Lemma D_90dc8 : decode_any W_90dc8 = Some (ShiftImm ALU_SLL 8 20 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dcc : bv 32 := 0x00850433.
Lemma F_90dcc : fetch_word AsanUbsan.M.loaded_segments (0x911e4 : word) = Some W_90dcc.
Proof. vm_refl. Qed.
Lemma D_90dcc : decode_any W_90dcc = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dd0 : bv 32 := 0x00843503.
Lemma F_90dd0 : fetch_word AsanUbsan.M.loaded_segments (0x911e8 : word) = Some W_90dd0.
Proof. vm_refl. Qed.
Lemma D_90dd0 : decode_any W_90dd0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dd4 : bv 32 := 0x04050263.
Lemma F_90dd4 : fetch_word AsanUbsan.M.loaded_segments (0x911ec : word) = Some W_90dd4.
Proof. vm_refl. Qed.
Lemma D_90dd4 : decode_any W_90dd4 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dd8 : bv 32 := 0x00000513.
Lemma F_90dd8 : fetch_word AsanUbsan.M.loaded_segments (0x911f0 : word) = Some W_90dd8.
Proof. vm_refl. Qed.
Lemma D_90dd8 : decode_any W_90dd8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90ddc : bv 32 := 0x08813083.
Lemma F_90ddc : fetch_word AsanUbsan.M.loaded_segments (0x911f4 : word) = Some W_90ddc.
Proof. vm_refl. Qed.
Lemma D_90ddc : decode_any W_90ddc = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90de0 : bv 32 := 0x08013403.
Lemma F_90de0 : fetch_word AsanUbsan.M.loaded_segments (0x911f8 : word) = Some W_90de0.
Proof. vm_refl. Qed.
Lemma D_90de0 : decode_any W_90de0 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90de4 : bv 32 := 0x07813483.
Lemma F_90de4 : fetch_word AsanUbsan.M.loaded_segments (0x911fc : word) = Some W_90de4.
Proof. vm_refl. Qed.
Lemma D_90de4 : decode_any W_90de4 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90de8 : bv 32 := 0x07013903.
Lemma F_90de8 : fetch_word AsanUbsan.M.loaded_segments (0x91200 : word) = Some W_90de8.
Proof. vm_refl. Qed.
Lemma D_90de8 : decode_any W_90de8 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dec : bv 32 := 0x06813983.
Lemma F_90dec : fetch_word AsanUbsan.M.loaded_segments (0x91204 : word) = Some W_90dec.
Proof. vm_refl. Qed.
Lemma D_90dec : decode_any W_90dec = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90df0 : bv 32 := 0x06013a03.
Lemma F_90df0 : fetch_word AsanUbsan.M.loaded_segments (0x91208 : word) = Some W_90df0.
Proof. vm_refl. Qed.
Lemma D_90df0 : decode_any W_90df0 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90df4 : bv 32 := 0x05813a83.
Lemma F_90df4 : fetch_word AsanUbsan.M.loaded_segments (0x9120c : word) = Some W_90df4.
Proof. vm_refl. Qed.
Lemma D_90df4 : decode_any W_90df4 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90df8 : bv 32 := 0x05013b03.
Lemma F_90df8 : fetch_word AsanUbsan.M.loaded_segments (0x91210 : word) = Some W_90df8.
Proof. vm_refl. Qed.
Lemma D_90df8 : decode_any W_90df8 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90dfc : bv 32 := 0x04813b83.
Lemma F_90dfc : fetch_word AsanUbsan.M.loaded_segments (0x91214 : word) = Some W_90dfc.
Proof. vm_refl. Qed.
Lemma D_90dfc : decode_any W_90dfc = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90e00 : bv 32 := 0x04013c03.
Lemma F_90e00 : fetch_word AsanUbsan.M.loaded_segments (0x91218 : word) = Some W_90e00.
Proof. vm_refl. Qed.
Lemma D_90e00 : decode_any W_90e00 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90e04 : bv 32 := 0x03813c83.
Lemma F_90e04 : fetch_word AsanUbsan.M.loaded_segments (0x9121c : word) = Some W_90e04.
Proof. vm_refl. Qed.
Lemma D_90e04 : decode_any W_90e04 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90e08 : bv 32 := 0x03013d03.
Lemma F_90e08 : fetch_word AsanUbsan.M.loaded_segments (0x91220 : word) = Some W_90e08.
Proof. vm_refl. Qed.
Lemma D_90e08 : decode_any W_90e08 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90e0c : bv 32 := 0x02813d83.
Lemma F_90e0c : fetch_word AsanUbsan.M.loaded_segments (0x91224 : word) = Some W_90e0c.
Proof. vm_refl. Qed.
Lemma D_90e0c : decode_any W_90e0c = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90e10 : bv 32 := 0x09010113.
Lemma F_90e10 : fetch_word AsanUbsan.M.loaded_segments (0x91228 : word) = Some W_90e10.
Proof. vm_refl. Qed.
Lemma D_90e10 : decode_any W_90e10 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90e14 : bv 32 := 0x00008067.
Lemma F_90e14 : fetch_word AsanUbsan.M.loaded_segments (0x9122c : word) = Some W_90e14.
Proof. vm_refl. Qed.
Lemma D_90e14 : decode_any W_90e14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
