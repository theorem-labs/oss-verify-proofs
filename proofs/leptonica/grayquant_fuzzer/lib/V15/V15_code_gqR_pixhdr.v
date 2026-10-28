(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_16c30 : bv 32 := 0xfd010113.
Lemma F_16c30 : fetch_word Ubsan.M.loaded_segments (0x16d34 : word) = Some W_16c30.
Proof. vm_refl. Qed.
Lemma D_16c30 : decode_any W_16c30 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c34 : bv 32 := 0x02113423.
Lemma F_16c34 : fetch_word Ubsan.M.loaded_segments (0x16d38 : word) = Some W_16c34.
Proof. vm_refl. Qed.
Lemma D_16c34 : decode_any W_16c34 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c38 : bv 32 := 0x02813023.
Lemma F_16c38 : fetch_word Ubsan.M.loaded_segments (0x16d3c : word) = Some W_16c38.
Proof. vm_refl. Qed.
Lemma D_16c38 : decode_any W_16c38 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c3c : bv 32 := 0x00913c23.
Lemma F_16c3c : fetch_word Ubsan.M.loaded_segments (0x16d40 : word) = Some W_16c3c.
Proof. vm_refl. Qed.
Lemma D_16c3c : decode_any W_16c3c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c40 : bv 32 := 0x01213823.
Lemma F_16c40 : fetch_word Ubsan.M.loaded_segments (0x16d44 : word) = Some W_16c40.
Proof. vm_refl. Qed.
Lemma D_16c40 : decode_any W_16c40 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c44 : bv 32 := 0x01313423.
Lemma F_16c44 : fetch_word Ubsan.M.loaded_segments (0x16d48 : word) = Some W_16c44.
Proof. vm_refl. Qed.
Lemma D_16c44 : decode_any W_16c44 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c48 : bv 32 := 0x01413023.
Lemma F_16c48 : fetch_word Ubsan.M.loaded_segments (0x16d4c : word) = Some W_16c48.
Proof. vm_refl. Qed.
Lemma D_16c48 : decode_any W_16c48 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c4c : bv 32 := 0x02000693.
Lemma F_16c4c : fetch_word Ubsan.M.loaded_segments (0x16d50 : word) = Some W_16c4c.
Proof. vm_refl. Qed.
Lemma D_16c4c : decode_any W_16c4c = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c50 : bv 32 := 0x14c6ea63.
Lemma F_16c50 : fetch_word Ubsan.M.loaded_segments (0x16d54 : word) = Some W_16c50.
Proof. vm_refl. Qed.
Lemma D_16c50 : decode_any W_16c50 = Some (Branch BC_LTU 13 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c54 : bv 32 := 0x101016b7.
Lemma F_16c54 : fetch_word Ubsan.M.loaded_segments (0x16d58 : word) = Some W_16c54.
Proof. vm_refl. Qed.
Lemma D_16c54 : decode_any W_16c54 = Some (Lui 13 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c58 : bv 32 := 0x00469693.
Lemma F_16c58 : fetch_word Ubsan.M.loaded_segments (0x16d5c : word) = Some W_16c58.
Proof. vm_refl. Qed.
Lemma D_16c58 : decode_any W_16c58 = Some (ShiftImm ALU_SLL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c5c : bv 32 := 0x11668693.
Lemma F_16c5c : fetch_word Ubsan.M.loaded_segments (0x16d60 : word) = Some W_16c5c.
Proof. vm_refl. Qed.
Lemma D_16c5c : decode_any W_16c5c = Some (OpImm ALU_ADD 13 13 278, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c60 : bv 32 := 0x00c6d6b3.
Lemma F_16c60 : fetch_word Ubsan.M.loaded_segments (0x16d64 : word) = Some W_16c60.
Proof. vm_refl. Qed.
Lemma D_16c60 : decode_any W_16c60 = Some (Op ALU_SRL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c64 : bv 32 := 0x0016f693.
Lemma F_16c64 : fetch_word Ubsan.M.loaded_segments (0x16d68 : word) = Some W_16c64.
Proof. vm_refl. Qed.
Lemma D_16c64 : decode_any W_16c64 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c68 : bv 32 := 0x12068e63.
Lemma F_16c68 : fetch_word Ubsan.M.loaded_segments (0x16d6c : word) = Some W_16c68.
Proof. vm_refl. Qed.
Lemma D_16c68 : decode_any W_16c68 = Some (Branch BC_EQ 13 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c6c : bv 32 := 0x06a05a63.
Lemma F_16c6c : fetch_word Ubsan.M.loaded_segments (0x16d70 : word) = Some W_16c6c.
Proof. vm_refl. Qed.
Lemma D_16c6c : decode_any W_16c6c = Some (Branch BC_GE 0 10 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c70 : bv 32 := 0x08b05c63.
Lemma F_16c70 : fetch_word Ubsan.M.loaded_segments (0x16d74 : word) = Some W_16c70.
Proof. vm_refl. Qed.
Lemma D_16c70 : decode_any W_16c70 = Some (Branch BC_GE 0 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c74 : bv 32 := 0x02a606b3.
Lemma F_16c74 : fetch_word Ubsan.M.loaded_segments (0x16d78 : word) = Some W_16c74.
Proof. vm_refl. Qed.
Lemma D_16c74 : decode_any W_16c74 = Some (Mul M_MUL 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c78 : bv 32 := 0x20000737.
Lemma F_16c78 : fetch_word Ubsan.M.loaded_segments (0x16d7c : word) = Some W_16c78.
Proof. vm_refl. Qed.
Lemma D_16c78 : decode_any W_16c78 = Some (Lui 14 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c7c : bv 32 := 0xfe17071b.
Lemma F_16c7c : fetch_word Ubsan.M.loaded_segments (0x16d80 : word) = Some W_16c7c.
Proof. vm_refl. Qed.
Lemma D_16c7c : decode_any W_16c7c = Some (OpImm32 14 14 4065, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16c80 : bv 32 := 0x0ae6e863.
Lemma F_16c80 : fetch_word Ubsan.M.loaded_segments (0x16d84 : word) = Some W_16c80.
Proof. vm_refl. Qed.
Lemma D_16c80 : decode_any W_16c80 = Some (Branch BC_LTU 13 14 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d30 : bv 32 := 0x01f68693.
Lemma F_16d30 : fetch_word Ubsan.M.loaded_segments (0x16e34 : word) = Some W_16d30.
Proof. vm_refl. Qed.
Lemma D_16d30 : decode_any W_16d30 = Some (OpImm ALU_ADD 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d34 : bv 32 := 0x0056da13.
Lemma F_16d34 : fetch_word Ubsan.M.loaded_segments (0x16e38 : word) = Some W_16d34.
Proof. vm_refl. Qed.
Lemma D_16d34 : decode_any W_16d34 = Some (ShiftImm ALU_SRL 20 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d38 : bv 32 := 0x02ba06b3.
Lemma F_16d38 : fetch_word Ubsan.M.loaded_segments (0x16e3c : word) = Some W_16d38.
Proof. vm_refl. Qed.
Lemma D_16d38 : decode_any W_16d38 = Some (Mul M_MUL 13 20 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d3c : bv 32 := 0x00269693.
Lemma F_16d3c : fetch_word Ubsan.M.loaded_segments (0x16e40 : word) = Some W_16d3c.
Proof. vm_refl. Qed.
Lemma D_16d3c : decode_any W_16d3c = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d40 : bv 32 := 0x01f6d713.
Lemma F_16d40 : fetch_word Ubsan.M.loaded_segments (0x16e44 : word) = Some W_16d40.
Proof. vm_refl. Qed.
Lemma D_16d40 : decode_any W_16d40 = Some (ShiftImm ALU_SRL 14 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16d44 : bv 32 := 0x0a070463.
Lemma F_16d44 : fetch_word Ubsan.M.loaded_segments (0x16e48 : word) = Some W_16d44.
Proof. vm_refl. Qed.
Lemma D_16d44 : decode_any W_16d44 = Some (Branch BC_EQ 14 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16da4 : bv 32 := 0x0001d517.
Lemma F_16da4 : fetch_word Ubsan.M.loaded_segments (0x16ea8 : word) = Some W_16da4.
Proof. vm_refl. Qed.
Lemma D_16da4 : decode_any W_16da4 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16da8 : bv 32 := 0x35053503.
Lemma F_16da8 : fetch_word Ubsan.M.loaded_segments (0x16eac : word) = Some W_16da8.
Proof. vm_refl. Qed.
Lemma D_16da8 : decode_any W_16da8 = Some (Load SZ8 true 10 10 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dac : bv 32 := 0x00052503.
Lemma F_16dac : fetch_word Ubsan.M.loaded_segments (0x16eb0 : word) = Some W_16dac.
Proof. vm_refl. Qed.
Lemma D_16dac : decode_any W_16dac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16db0 : bv 32 := 0x00500593.
Lemma F_16db0 : fetch_word Ubsan.M.loaded_segments (0x16eb4 : word) = Some W_16db0.
Proof. vm_refl. Qed.
Lemma D_16db0 : decode_any W_16db0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16db4 : bv 32 := 0x0ca5c663.
Lemma F_16db4 : fetch_word Ubsan.M.loaded_segments (0x16eb8 : word) = Some W_16db4.
Proof. vm_refl. Qed.
Lemma D_16db4 : decode_any W_16db4 = Some (Branch BC_LT 11 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16db8 : bv 32 := 0xffff9517.
Lemma F_16db8 : fetch_word Ubsan.M.loaded_segments (0x16ebc : word) = Some W_16db8.
Proof. vm_refl. Qed.
Lemma D_16db8 : decode_any W_16db8 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dbc : bv 32 := 0xffffa597.
Lemma F_16dbc : fetch_word Ubsan.M.loaded_segments (0x16ec0 : word) = Some W_16dbc.
Proof. vm_refl. Qed.
Lemma D_16dbc : decode_any W_16dbc = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dc0 : bv 32 := 0x70850513.
Lemma F_16dc0 : fetch_word Ubsan.M.loaded_segments (0x16ec4 : word) = Some W_16dc0.
Proof. vm_refl. Qed.
Lemma D_16dc0 : decode_any W_16dc0 = Some (OpImm ALU_ADD 10 10 1800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dc4 : bv 32 := 0xa7b58593.
Lemma F_16dc4 : fetch_word Ubsan.M.loaded_segments (0x16ec8 : word) = Some W_16dc4.
Proof. vm_refl. Qed.
Lemma D_16dc4 : decode_any W_16dc4 = Some (OpImm ALU_ADD 11 11 2683, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dc8 : bv 32 := 0x00000613.
Lemma F_16dc8 : fetch_word Ubsan.M.loaded_segments (0x16ecc : word) = Some W_16dc8.
Proof. vm_refl. Qed.
Lemma D_16dc8 : decode_any W_16dc8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dcc : bv 32 := 0x02813083.
Lemma F_16dcc : fetch_word Ubsan.M.loaded_segments (0x16ed0 : word) = Some W_16dcc.
Proof. vm_refl. Qed.
Lemma D_16dcc : decode_any W_16dcc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dd0 : bv 32 := 0x02013403.
Lemma F_16dd0 : fetch_word Ubsan.M.loaded_segments (0x16ed4 : word) = Some W_16dd0.
Proof. vm_refl. Qed.
Lemma D_16dd0 : decode_any W_16dd0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dd4 : bv 32 := 0x01813483.
Lemma F_16dd4 : fetch_word Ubsan.M.loaded_segments (0x16ed8 : word) = Some W_16dd4.
Proof. vm_refl. Qed.
Lemma D_16dd4 : decode_any W_16dd4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dd8 : bv 32 := 0x01013903.
Lemma F_16dd8 : fetch_word Ubsan.M.loaded_segments (0x16edc : word) = Some W_16dd8.
Proof. vm_refl. Qed.
Lemma D_16dd8 : decode_any W_16dd8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ddc : bv 32 := 0x00813983.
Lemma F_16ddc : fetch_word Ubsan.M.loaded_segments (0x16ee0 : word) = Some W_16ddc.
Proof. vm_refl. Qed.
Lemma D_16ddc : decode_any W_16ddc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16de0 : bv 32 := 0x00013a03.
Lemma F_16de0 : fetch_word Ubsan.M.loaded_segments (0x16ee4 : word) = Some W_16de0.
Proof. vm_refl. Qed.
Lemma D_16de0 : decode_any W_16de0 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16de4 : bv 32 := 0x03010113.
Lemma F_16de4 : fetch_word Ubsan.M.loaded_segments (0x16ee8 : word) = Some W_16de4.
Proof. vm_refl. Qed.
Lemma D_16de4 : decode_any W_16de4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16de8 : bv 32 := 0xed0fe06f.
Lemma F_16de8 : fetch_word Ubsan.M.loaded_segments (0x16eec : word) = Some W_16de8.
Proof. vm_refl. Qed.
Lemma D_16de8 : decode_any W_16de8 = Some (Jal 0 2090704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dec : bv 32 := 0x04000737.
Lemma F_16dec : fetch_word Ubsan.M.loaded_segments (0x16ef0 : word) = Some W_16dec.
Proof. vm_refl. Qed.
Lemma D_16dec : decode_any W_16dec = Some (Lui 14 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16df0 : bv 32 := 0x0017071b.
Lemma F_16df0 : fetch_word Ubsan.M.loaded_segments (0x16ef4 : word) = Some W_16df0.
Proof. vm_refl. Qed.
Lemma D_16df0 : decode_any W_16df0 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16df4 : bv 32 := 0x02e6e663.
Lemma F_16df4 : fetch_word Ubsan.M.loaded_segments (0x16ef8 : word) = Some W_16df4.
Proof. vm_refl. Qed.
Lemma D_16df4 : decode_any W_16df4 = Some (Branch BC_LTU 13 14 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16df8 : bv 32 := 0x0001d517.
Lemma F_16df8 : fetch_word Ubsan.M.loaded_segments (0x16efc : word) = Some W_16df8.
Proof. vm_refl. Qed.
Lemma D_16df8 : decode_any W_16df8 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16dfc : bv 32 := 0x2fc53503.
Lemma F_16dfc : fetch_word Ubsan.M.loaded_segments (0x16f00 : word) = Some W_16dfc.
Proof. vm_refl. Qed.
Lemma D_16dfc : decode_any W_16dfc = Some (Load SZ8 true 10 10 764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e00 : bv 32 := 0x00052503.
Lemma F_16e00 : fetch_word Ubsan.M.loaded_segments (0x16f04 : word) = Some W_16e00.
Proof. vm_refl. Qed.
Lemma D_16e00 : decode_any W_16e00 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e04 : bv 32 := 0x00500593.
Lemma F_16e04 : fetch_word Ubsan.M.loaded_segments (0x16f08 : word) = Some W_16e04.
Proof. vm_refl. Qed.
Lemma D_16e04 : decode_any W_16e04 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e08 : bv 32 := 0x06a5cc63.
Lemma F_16e08 : fetch_word Ubsan.M.loaded_segments (0x16f0c : word) = Some W_16e08.
Proof. vm_refl. Qed.
Lemma D_16e08 : decode_any W_16e08 = Some (Branch BC_LT 11 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e0c : bv 32 := 0xffff9517.
Lemma F_16e0c : fetch_word Ubsan.M.loaded_segments (0x16f10 : word) = Some W_16e0c.
Proof. vm_refl. Qed.
Lemma D_16e0c : decode_any W_16e0c = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e10 : bv 32 := 0xffffa597.
Lemma F_16e10 : fetch_word Ubsan.M.loaded_segments (0x16f14 : word) = Some W_16e10.
Proof. vm_refl. Qed.
Lemma D_16e10 : decode_any W_16e10 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e14 : bv 32 := 0x54450513.
Lemma F_16e14 : fetch_word Ubsan.M.loaded_segments (0x16f18 : word) = Some W_16e14.
Proof. vm_refl. Qed.
Lemma D_16e14 : decode_any W_16e14 = Some (OpImm ALU_ADD 10 10 1348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e18 : bv 32 := 0xa2758593.
Lemma F_16e18 : fetch_word Ubsan.M.loaded_segments (0x16f1c : word) = Some W_16e18.
Proof. vm_refl. Qed.
Lemma D_16e18 : decode_any W_16e18 = Some (OpImm ALU_ADD 11 11 2599, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e1c : bv 32 := 0x0600006f.
Lemma F_16e1c : fetch_word Ubsan.M.loaded_segments (0x16f20 : word) = Some W_16e1c.
Proof. vm_refl. Qed.
Lemma D_16e1c : decode_any W_16e1c = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e20 : bv 32 := 0x000056b7.
Lemma F_16e20 : fetch_word Ubsan.M.loaded_segments (0x16f24 : word) = Some W_16e20.
Proof. vm_refl. Qed.
Lemma D_16e20 : decode_any W_16e20 = Some (Lui 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e24 : bv 32 := 0xe216869b.
Lemma F_16e24 : fetch_word Ubsan.M.loaded_segments (0x16f28 : word) = Some W_16e24.
Proof. vm_refl. Qed.
Lemma D_16e24 : decode_any W_16e24 = Some (OpImm32 13 13 3617, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e28 : bv 32 := 0x02d56663.
Lemma F_16e28 : fetch_word Ubsan.M.loaded_segments (0x16f2c : word) = Some W_16e28.
Proof. vm_refl. Qed.
Lemma D_16e28 : decode_any W_16e28 = Some (Branch BC_LTU 10 13 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e2c : bv 32 := 0x0001d517.
Lemma F_16e2c : fetch_word Ubsan.M.loaded_segments (0x16f30 : word) = Some W_16e2c.
Proof. vm_refl. Qed.
Lemma D_16e2c : decode_any W_16e2c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e30 : bv 32 := 0x2c853503.
Lemma F_16e30 : fetch_word Ubsan.M.loaded_segments (0x16f34 : word) = Some W_16e30.
Proof. vm_refl. Qed.
Lemma D_16e30 : decode_any W_16e30 = Some (Load SZ8 true 10 10 712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e34 : bv 32 := 0x00052503.
Lemma F_16e34 : fetch_word Ubsan.M.loaded_segments (0x16f38 : word) = Some W_16e34.
Proof. vm_refl. Qed.
Lemma D_16e34 : decode_any W_16e34 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e38 : bv 32 := 0x00500593.
Lemma F_16e38 : fetch_word Ubsan.M.loaded_segments (0x16f3c : word) = Some W_16e38.
Proof. vm_refl. Qed.
Lemma D_16e38 : decode_any W_16e38 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e3c : bv 32 := 0x04a5c263.
Lemma F_16e3c : fetch_word Ubsan.M.loaded_segments (0x16f40 : word) = Some W_16e3c.
Proof. vm_refl. Qed.
Lemma D_16e3c : decode_any W_16e3c = Some (Branch BC_LT 11 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e40 : bv 32 := 0xffffa517.
Lemma F_16e40 : fetch_word Ubsan.M.loaded_segments (0x16f44 : word) = Some W_16e40.
Proof. vm_refl. Qed.
Lemma D_16e40 : decode_any W_16e40 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e44 : bv 32 := 0xffffa597.
Lemma F_16e44 : fetch_word Ubsan.M.loaded_segments (0x16f48 : word) = Some W_16e44.
Proof. vm_refl. Qed.
Lemma D_16e44 : decode_any W_16e44 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e48 : bv 32 := 0x30b50513.
Lemma F_16e48 : fetch_word Ubsan.M.loaded_segments (0x16f4c : word) = Some W_16e48.
Proof. vm_refl. Qed.
Lemma D_16e48 : decode_any W_16e48 = Some (OpImm ALU_ADD 10 10 779, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e4c : bv 32 := 0x9f358593.
Lemma F_16e4c : fetch_word Ubsan.M.loaded_segments (0x16f50 : word) = Some W_16e4c.
Proof. vm_refl. Qed.
Lemma D_16e4c : decode_any W_16e4c = Some (OpImm ALU_ADD 11 11 2547, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e50 : bv 32 := 0x02c0006f.
Lemma F_16e50 : fetch_word Ubsan.M.loaded_segments (0x16f54 : word) = Some W_16e50.
Proof. vm_refl. Qed.
Lemma D_16e50 : decode_any W_16e50 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e54 : bv 32 := 0x04d5e863.
Lemma F_16e54 : fetch_word Ubsan.M.loaded_segments (0x16f58 : word) = Some W_16e54.
Proof. vm_refl. Qed.
Lemma D_16e54 : decode_any W_16e54 = Some (Branch BC_LTU 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e58 : bv 32 := 0x0001d517.
Lemma F_16e58 : fetch_word Ubsan.M.loaded_segments (0x16f5c : word) = Some W_16e58.
Proof. vm_refl. Qed.
Lemma D_16e58 : decode_any W_16e58 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e5c : bv 32 := 0x29c53503.
Lemma F_16e5c : fetch_word Ubsan.M.loaded_segments (0x16f60 : word) = Some W_16e5c.
Proof. vm_refl. Qed.
Lemma D_16e5c : decode_any W_16e5c = Some (Load SZ8 true 10 10 668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e60 : bv 32 := 0x00052503.
Lemma F_16e60 : fetch_word Ubsan.M.loaded_segments (0x16f64 : word) = Some W_16e60.
Proof. vm_refl. Qed.
Lemma D_16e60 : decode_any W_16e60 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e64 : bv 32 := 0x00500593.
Lemma F_16e64 : fetch_word Ubsan.M.loaded_segments (0x16f68 : word) = Some W_16e64.
Proof. vm_refl. Qed.
Lemma D_16e64 : decode_any W_16e64 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e68 : bv 32 := 0x00a5cc63.
Lemma F_16e68 : fetch_word Ubsan.M.loaded_segments (0x16f6c : word) = Some W_16e68.
Proof. vm_refl. Qed.
Lemma D_16e68 : decode_any W_16e68 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e6c : bv 32 := 0xffffa517.
Lemma F_16e6c : fetch_word Ubsan.M.loaded_segments (0x16f70 : word) = Some W_16e6c.
Proof. vm_refl. Qed.
Lemma D_16e6c : decode_any W_16e6c = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e70 : bv 32 := 0xffffa597.
Lemma F_16e70 : fetch_word Ubsan.M.loaded_segments (0x16f74 : word) = Some W_16e70.
Proof. vm_refl. Qed.
Lemma D_16e70 : decode_any W_16e70 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e74 : bv 32 := 0xe0a50513.
Lemma F_16e74 : fetch_word Ubsan.M.loaded_segments (0x16f78 : word) = Some W_16e74.
Proof. vm_refl. Qed.
Lemma D_16e74 : decode_any W_16e74 = Some (OpImm ALU_ADD 10 10 3594, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e78 : bv 32 := 0x9c758593.
Lemma F_16e78 : fetch_word Ubsan.M.loaded_segments (0x16f7c : word) = Some W_16e78.
Proof. vm_refl. Qed.
Lemma D_16e78 : decode_any W_16e78 = Some (OpImm ALU_ADD 11 11 2503, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e7c : bv 32 := 0xda0fe0ef.
Lemma F_16e7c : fetch_word Ubsan.M.loaded_segments (0x16f80 : word) = Some W_16e7c.
Proof. vm_refl. Qed.
Lemma D_16e7c : decode_any W_16e7c = Some (Jal 1 2090400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e80 : bv 32 := 0x00000513.
Lemma F_16e80 : fetch_word Ubsan.M.loaded_segments (0x16f84 : word) = Some W_16e80.
Proof. vm_refl. Qed.
Lemma D_16e80 : decode_any W_16e80 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e84 : bv 32 := 0x02813083.
Lemma F_16e84 : fetch_word Ubsan.M.loaded_segments (0x16f88 : word) = Some W_16e84.
Proof. vm_refl. Qed.
Lemma D_16e84 : decode_any W_16e84 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e88 : bv 32 := 0x02013403.
Lemma F_16e88 : fetch_word Ubsan.M.loaded_segments (0x16f8c : word) = Some W_16e88.
Proof. vm_refl. Qed.
Lemma D_16e88 : decode_any W_16e88 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e8c : bv 32 := 0x01813483.
Lemma F_16e8c : fetch_word Ubsan.M.loaded_segments (0x16f90 : word) = Some W_16e8c.
Proof. vm_refl. Qed.
Lemma D_16e8c : decode_any W_16e8c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e90 : bv 32 := 0x01013903.
Lemma F_16e90 : fetch_word Ubsan.M.loaded_segments (0x16f94 : word) = Some W_16e90.
Proof. vm_refl. Qed.
Lemma D_16e90 : decode_any W_16e90 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e94 : bv 32 := 0x00813983.
Lemma F_16e94 : fetch_word Ubsan.M.loaded_segments (0x16f98 : word) = Some W_16e94.
Proof. vm_refl. Qed.
Lemma D_16e94 : decode_any W_16e94 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e98 : bv 32 := 0x00013a03.
Lemma F_16e98 : fetch_word Ubsan.M.loaded_segments (0x16f9c : word) = Some W_16e98.
Proof. vm_refl. Qed.
Lemma D_16e98 : decode_any W_16e98 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16e9c : bv 32 := 0x03010113.
Lemma F_16e9c : fetch_word Ubsan.M.loaded_segments (0x16fa0 : word) = Some W_16e9c.
Proof. vm_refl. Qed.
Lemma D_16e9c : decode_any W_16e9c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ea0 : bv 32 := 0x00008067.
Lemma F_16ea0 : fetch_word Ubsan.M.loaded_segments (0x16fa4 : word) = Some W_16ea0.
Proof. vm_refl. Qed.
Lemma D_16ea0 : decode_any W_16ea0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ea4 : bv 32 := 0x00050993.
Lemma F_16ea4 : fetch_word Ubsan.M.loaded_segments (0x16fa8 : word) = Some W_16ea4.
Proof. vm_refl. Qed.
Lemma D_16ea4 : decode_any W_16ea4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ea8 : bv 32 := 0x00058493.
Lemma F_16ea8 : fetch_word Ubsan.M.loaded_segments (0x16fac : word) = Some W_16ea8.
Proof. vm_refl. Qed.
Lemma D_16ea8 : decode_any W_16ea8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eac : bv 32 := 0x00060413.
Lemma F_16eac : fetch_word Ubsan.M.loaded_segments (0x16fb0 : word) = Some W_16eac.
Proof. vm_refl. Qed.
Lemma D_16eac : decode_any W_16eac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eb0 : bv 32 := 0x00100513.
Lemma F_16eb0 : fetch_word Ubsan.M.loaded_segments (0x16fb4 : word) = Some W_16eb0.
Proof. vm_refl. Qed.
Lemma D_16eb0 : decode_any W_16eb0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eb4 : bv 32 := 0x04000593.
Lemma F_16eb4 : fetch_word Ubsan.M.loaded_segments (0x16fb8 : word) = Some W_16eb4.
Proof. vm_refl. Qed.
Lemma D_16eb4 : decode_any W_16eb4 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eb8 : bv 32 := 0x161110ef.
Lemma F_16eb8 : fetch_word Ubsan.M.loaded_segments (0x16fbc : word) = Some W_16eb8.
Proof. vm_refl. Qed.
Lemma D_16eb8 : decode_any W_16eb8 = Some (Jal 1 72032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ebc : bv 32 := 0x04050863.
Lemma F_16ebc : fetch_word Ubsan.M.loaded_segments (0x16fc0 : word) = Some W_16ebc.
Proof. vm_refl. Qed.
Lemma D_16ebc : decode_any W_16ebc = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ec0 : bv 32 := 0x00050913.
Lemma F_16ec0 : fetch_word Ubsan.M.loaded_segments (0x16fc4 : word) = Some W_16ec0.
Proof. vm_refl. Qed.
Lemma D_16ec0 : decode_any W_16ec0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ec4 : bv 32 := 0x00098593.
Lemma F_16ec4 : fetch_word Ubsan.M.loaded_segments (0x16fc8 : word) = Some W_16ec4.
Proof. vm_refl. Qed.
Lemma D_16ec4 : decode_any W_16ec4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ec8 : bv 32 := 0x7e0000ef.
Lemma F_16ec8 : fetch_word Ubsan.M.loaded_segments (0x16fcc : word) = Some W_16ec8.
Proof. vm_refl. Qed.
Lemma D_16ec8 : decode_any W_16ec8 = Some (Jal 1 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ecc : bv 32 := 0x00090513.
Lemma F_16ecc : fetch_word Ubsan.M.loaded_segments (0x16fd0 : word) = Some W_16ecc.
Proof. vm_refl. Qed.
Lemma D_16ecc : decode_any W_16ecc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ed0 : bv 32 := 0x00048593.
Lemma F_16ed0 : fetch_word Ubsan.M.loaded_segments (0x16fd4 : word) = Some W_16ed0.
Proof. vm_refl. Qed.
Lemma D_16ed0 : decode_any W_16ed0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ed4 : bv 32 := 0x05d000ef.
Lemma F_16ed4 : fetch_word Ubsan.M.loaded_segments (0x16fd8 : word) = Some W_16ed4.
Proof. vm_refl. Qed.
Lemma D_16ed4 : decode_any W_16ed4 = Some (Jal 1 2140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ed8 : bv 32 := 0x00090513.
Lemma F_16ed8 : fetch_word Ubsan.M.loaded_segments (0x16fdc : word) = Some W_16ed8.
Proof. vm_refl. Qed.
Lemma D_16ed8 : decode_any W_16ed8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16edc : bv 32 := 0x00040593.
Lemma F_16edc : fetch_word Ubsan.M.loaded_segments (0x16fe0 : word) = Some W_16edc.
Proof. vm_refl. Qed.
Lemma D_16edc : decode_any W_16edc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ee0 : bv 32 := 0x0d9000ef.
Lemma F_16ee0 : fetch_word Ubsan.M.loaded_segments (0x16fe4 : word) = Some W_16ee0.
Proof. vm_refl. Qed.
Lemma D_16ee0 : decode_any W_16ee0 = Some (Jal 1 2264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ee4 : bv 32 := 0x00797593.
Lemma F_16ee4 : fetch_word Ubsan.M.loaded_segments (0x16fe8 : word) = Some W_16ee4.
Proof. vm_refl. Qed.
Lemma D_16ee4 : decode_any W_16ee4 = Some (OpImm ALU_AND 11 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ee8 : bv 32 := 0x06059463.
Lemma F_16ee8 : fetch_word Ubsan.M.loaded_segments (0x16fec : word) = Some W_16ee8.
Proof. vm_refl. Qed.
Lemma D_16ee8 : decode_any W_16ee8 = Some (Branch BC_NE 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16eec : bv 32 := 0x00090513.
Lemma F_16eec : fetch_word Ubsan.M.loaded_segments (0x16ff0 : word) = Some W_16eec.
Proof. vm_refl. Qed.
Lemma D_16eec : decode_any W_16eec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ef0 : bv 32 := 0x01492823.
Lemma F_16ef0 : fetch_word Ubsan.M.loaded_segments (0x16ff4 : word) = Some W_16ef0.
Proof. vm_refl. Qed.
Lemma D_16ef0 : decode_any W_16ef0 = Some (Store SZ4 18 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ef4 : bv 32 := 0xfe84041b.
Lemma F_16ef4 : fetch_word Ubsan.M.loaded_segments (0x16ff8 : word) = Some W_16ef4.
Proof. vm_refl. Qed.
Lemma D_16ef4 : decode_any W_16ef4 = Some (OpImm32 8 8 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ef8 : bv 32 := 0xff747413.
Lemma F_16ef8 : fetch_word Ubsan.M.loaded_segments (0x16ffc : word) = Some W_16ef8.
Proof. vm_refl. Qed.
Lemma D_16ef8 : decode_any W_16ef8 = Some (OpImm ALU_AND 8 8 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16efc : bv 32 := 0x00100593.
Lemma F_16efc : fetch_word Ubsan.M.loaded_segments (0x17000 : word) = Some W_16efc.
Proof. vm_refl. Qed.
Lemma D_16efc : decode_any W_16efc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f00 : bv 32 := 0x02040a63.
Lemma F_16f00 : fetch_word Ubsan.M.loaded_segments (0x17004 : word) = Some W_16f00.
Proof. vm_refl. Qed.
Lemma D_16f00 : decode_any W_16f00 = Some (Branch BC_EQ 8 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f04 : bv 32 := 0x00100613.
Lemma F_16f04 : fetch_word Ubsan.M.loaded_segments (0x17008 : word) = Some W_16f04.
Proof. vm_refl. Qed.
Lemma D_16f04 : decode_any W_16f04 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f08 : bv 32 := 0x0300006f.
Lemma F_16f08 : fetch_word Ubsan.M.loaded_segments (0x1700c : word) = Some W_16f08.
Proof. vm_refl. Qed.
Lemma D_16f08 : decode_any W_16f08 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f0c : bv 32 := 0x0001d517.
Lemma F_16f0c : fetch_word Ubsan.M.loaded_segments (0x17010 : word) = Some W_16f0c.
Proof. vm_refl. Qed.
Lemma D_16f0c : decode_any W_16f0c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f10 : bv 32 := 0x1e853503.
Lemma F_16f10 : fetch_word Ubsan.M.loaded_segments (0x17014 : word) = Some W_16f10.
Proof. vm_refl. Qed.
Lemma D_16f10 : decode_any W_16f10 = Some (Load SZ8 true 10 10 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f14 : bv 32 := 0x00052503.
Lemma F_16f14 : fetch_word Ubsan.M.loaded_segments (0x17018 : word) = Some W_16f14.
Proof. vm_refl. Qed.
Lemma D_16f14 : decode_any W_16f14 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f18 : bv 32 := 0x00500593.
Lemma F_16f18 : fetch_word Ubsan.M.loaded_segments (0x1701c : word) = Some W_16f18.
Proof. vm_refl. Qed.
Lemma D_16f18 : decode_any W_16f18 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f1c : bv 32 := 0xf6a5c2e3.
Lemma F_16f1c : fetch_word Ubsan.M.loaded_segments (0x17020 : word) = Some W_16f1c.
Proof. vm_refl. Qed.
Lemma D_16f1c : decode_any W_16f1c = Some (Branch BC_LT 11 10 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f20 : bv 32 := 0xffff9517.
Lemma F_16f20 : fetch_word Ubsan.M.loaded_segments (0x17024 : word) = Some W_16f20.
Proof. vm_refl. Qed.
Lemma D_16f20 : decode_any W_16f20 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f24 : bv 32 := 0xffffa597.
Lemma F_16f24 : fetch_word Ubsan.M.loaded_segments (0x17028 : word) = Some W_16f24.
Proof. vm_refl. Qed.
Lemma D_16f24 : decode_any W_16f24 = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f28 : bv 32 := 0x4fb50513.
Lemma F_16f28 : fetch_word Ubsan.M.loaded_segments (0x1702c : word) = Some W_16f28.
Proof. vm_refl. Qed.
Lemma D_16f28 : decode_any W_16f28 = Some (OpImm ALU_ADD 10 10 1275, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f2c : bv 32 := 0x91358593.
Lemma F_16f2c : fetch_word Ubsan.M.loaded_segments (0x17030 : word) = Some W_16f2c.
Proof. vm_refl. Qed.
Lemma D_16f2c : decode_any W_16f2c = Some (OpImm ALU_ADD 11 11 2323, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f30 : bv 32 := 0xe99ff06f.
Lemma F_16f30 : fetch_word Ubsan.M.loaded_segments (0x17034 : word) = Some W_16f30.
Proof. vm_refl. Qed.
Lemma D_16f30 : decode_any W_16f30 = Some (Jal 0 2096792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f34 : bv 32 := 0x00300613.
Lemma F_16f34 : fetch_word Ubsan.M.loaded_segments (0x17038 : word) = Some W_16f34.
Proof. vm_refl. Qed.
Lemma D_16f34 : decode_any W_16f34 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f38 : bv 32 := 0x00c52623.
Lemma F_16f38 : fetch_word Ubsan.M.loaded_segments (0x1703c : word) = Some W_16f38.
Proof. vm_refl. Qed.
Lemma D_16f38 : decode_any W_16f38 = Some (Store SZ4 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f3c : bv 32 := 0x0310000f.
Lemma F_16f3c : fetch_word Ubsan.M.loaded_segments (0x17040 : word) = Some W_16f3c.
Proof. vm_refl. Qed.
Lemma D_16f3c : decode_any W_16f3c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f40 : bv 32 := 0x00b52a23.
Lemma F_16f40 : fetch_word Ubsan.M.loaded_segments (0x17044 : word) = Some W_16f40.
Proof. vm_refl. Qed.
Lemma D_16f40 : decode_any W_16f40 = Some (Store SZ4 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f44 : bv 32 := 0x0330000f.
Lemma F_16f44 : fetch_word Ubsan.M.loaded_segments (0x17048 : word) = Some W_16f44.
Proof. vm_refl. Qed.
Lemma D_16f44 : decode_any W_16f44 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f48 : bv 32 := 0x02052023.
Lemma F_16f48 : fetch_word Ubsan.M.loaded_segments (0x1704c : word) = Some W_16f48.
Proof. vm_refl. Qed.
Lemma D_16f48 : decode_any W_16f48 = Some (Store SZ4 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16f4c : bv 32 := 0xf39ff06f.
Lemma F_16f4c : fetch_word Ubsan.M.loaded_segments (0x17050 : word) = Some W_16f4c.
Proof. vm_refl. Qed.
Lemma D_16f4c : decode_any W_16f4c = Some (Jal 0 2096952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176a8 : bv 32 := 0x00050e63.
Lemma F_176a8 : fetch_word Ubsan.M.loaded_segments (0x177ac : word) = Some W_176a8.
Proof. vm_refl. Qed.
Lemma D_176a8 : decode_any W_176a8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176ac : bv 32 := 0x00757613.
Lemma F_176ac : fetch_word Ubsan.M.loaded_segments (0x177b0 : word) = Some W_176ac.
Proof. vm_refl. Qed.
Lemma D_176ac : decode_any W_176ac = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176b0 : bv 32 := 0x0405c063.
Lemma F_176b0 : fetch_word Ubsan.M.loaded_segments (0x177b4 : word) = Some W_176b0.
Proof. vm_refl. Qed.
Lemma D_176b0 : decode_any W_176b0 = Some (Branch BC_LT 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176b4 : bv 32 := 0x06061c63.
Lemma F_176b4 : fetch_word Ubsan.M.loaded_segments (0x177b8 : word) = Some W_176b4.
Proof. vm_refl. Qed.
Lemma D_176b4 : decode_any W_176b4 = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176b8 : bv 32 := 0x00b52023.
Lemma F_176b8 : fetch_word Ubsan.M.loaded_segments (0x177bc : word) = Some W_176b8.
Proof. vm_refl. Qed.
Lemma D_176b8 : decode_any W_176b8 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176bc : bv 32 := 0x00060513.
Lemma F_176bc : fetch_word Ubsan.M.loaded_segments (0x177c0 : word) = Some W_176bc.
Proof. vm_refl. Qed.
Lemma D_176bc : decode_any W_176bc = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_176c0 : bv 32 := 0x00008067.
Lemma F_176c0 : fetch_word Ubsan.M.loaded_segments (0x177c4 : word) = Some W_176c0.
Proof. vm_refl. Qed.
Lemma D_176c0 : decode_any W_176c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17730 : bv 32 := 0x00050e63.
Lemma F_17730 : fetch_word Ubsan.M.loaded_segments (0x17834 : word) = Some W_17730.
Proof. vm_refl. Qed.
Lemma D_17730 : decode_any W_17730 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17734 : bv 32 := 0x00757613.
Lemma F_17734 : fetch_word Ubsan.M.loaded_segments (0x17838 : word) = Some W_17734.
Proof. vm_refl. Qed.
Lemma D_17734 : decode_any W_17734 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17738 : bv 32 := 0x0405c063.
Lemma F_17738 : fetch_word Ubsan.M.loaded_segments (0x1783c : word) = Some W_17738.
Proof. vm_refl. Qed.
Lemma D_17738 : decode_any W_17738 = Some (Branch BC_LT 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1773c : bv 32 := 0x06061c63.
Lemma F_1773c : fetch_word Ubsan.M.loaded_segments (0x17840 : word) = Some W_1773c.
Proof. vm_refl. Qed.
Lemma D_1773c : decode_any W_1773c = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17740 : bv 32 := 0x00b52223.
Lemma F_17740 : fetch_word Ubsan.M.loaded_segments (0x17844 : word) = Some W_17740.
Proof. vm_refl. Qed.
Lemma D_17740 : decode_any W_17740 = Some (Store SZ4 10 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17744 : bv 32 := 0x00060513.
Lemma F_17744 : fetch_word Ubsan.M.loaded_segments (0x17848 : word) = Some W_17744.
Proof. vm_refl. Qed.
Lemma D_17744 : decode_any W_17744 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17748 : bv 32 := 0x00008067.
Lemma F_17748 : fetch_word Ubsan.M.loaded_segments (0x1784c : word) = Some W_17748.
Proof. vm_refl. Qed.
Lemma D_17748 : decode_any W_17748 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177b8 : bv 32 := 0x00050e63.
Lemma F_177b8 : fetch_word Ubsan.M.loaded_segments (0x178bc : word) = Some W_177b8.
Proof. vm_refl. Qed.
Lemma D_177b8 : decode_any W_177b8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177bc : bv 32 := 0x04b05263.
Lemma F_177bc : fetch_word Ubsan.M.loaded_segments (0x178c0 : word) = Some W_177bc.
Proof. vm_refl. Qed.
Lemma D_177bc : decode_any W_177bc = Some (Branch BC_GE 0 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177c0 : bv 32 := 0x00757613.
Lemma F_177c0 : fetch_word Ubsan.M.loaded_segments (0x178c4 : word) = Some W_177c0.
Proof. vm_refl. Qed.
Lemma D_177c0 : decode_any W_177c0 = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177c4 : bv 32 := 0x06061863.
Lemma F_177c4 : fetch_word Ubsan.M.loaded_segments (0x178c8 : word) = Some W_177c4.
Proof. vm_refl. Qed.
Lemma D_177c4 : decode_any W_177c4 = Some (Branch BC_NE 12 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177c8 : bv 32 := 0x00b52423.
Lemma F_177c8 : fetch_word Ubsan.M.loaded_segments (0x178cc : word) = Some W_177c8.
Proof. vm_refl. Qed.
Lemma D_177c8 : decode_any W_177c8 = Some (Store SZ4 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177cc : bv 32 := 0x00060513.
Lemma F_177cc : fetch_word Ubsan.M.loaded_segments (0x178d0 : word) = Some W_177cc.
Proof. vm_refl. Qed.
Lemma D_177cc : decode_any W_177cc = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_177d0 : bv 32 := 0x00008067.
Lemma F_177d0 : fetch_word Ubsan.M.loaded_segments (0x178d4 : word) = Some W_177d0.
Proof. vm_refl. Qed.
Lemma D_177d0 : decode_any W_177d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

