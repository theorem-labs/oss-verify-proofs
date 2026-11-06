(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import AsanUbsan.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_92dbc : bv 32 := 0x0035f693.
Lemma F_92dbc : fetch_word AsanUbsan.M.loaded_segments (0x92c40 : word) = Some W_92dbc.
Proof. vm_refl. Qed.
Lemma D_92dbc : decode_any W_92dbc = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dc0 : bv 32 := 0x10068863.
Lemma F_92dc0 : fetch_word AsanUbsan.M.loaded_segments (0x92c44 : word) = Some W_92dc0.
Proof. vm_refl. Qed.
Lemma D_92dc0 : decode_any W_92dc0 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dc4 : bv 32 := 0x02060e63.
Lemma F_92dc4 : fetch_word AsanUbsan.M.loaded_segments (0x92c48 : word) = Some W_92dc4.
Proof. vm_refl. Qed.
Lemma D_92dc4 : decode_any W_92dc4 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dc8 : bv 32 := 0x00158713.
Lemma F_92dc8 : fetch_word AsanUbsan.M.loaded_segments (0x92c4c : word) = Some W_92dc8.
Proof. vm_refl. Qed.
Lemma D_92dc8 : decode_any W_92dc8 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dcc : bv 32 := 0x00100793.
Lemma F_92dcc : fetch_word AsanUbsan.M.loaded_segments (0x92c50 : word) = Some W_92dcc.
Proof. vm_refl. Qed.
Lemma D_92dcc : decode_any W_92dcc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dd0 : bv 32 := 0x00050693.
Lemma F_92dd0 : fetch_word AsanUbsan.M.loaded_segments (0x92c54 : word) = Some W_92dd0.
Proof. vm_refl. Qed.
Lemma D_92dd0 : decode_any W_92dd0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dd4 : bv 32 := 0x0005c883.
Lemma F_92dd4 : fetch_word AsanUbsan.M.loaded_segments (0x92c58 : word) = Some W_92dd4.
Proof. vm_refl. Qed.
Lemma D_92dd4 : decode_any W_92dd4 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dd8 : bv 32 := 0x00060813.
Lemma F_92dd8 : fetch_word AsanUbsan.M.loaded_segments (0x92c5c : word) = Some W_92dd8.
Proof. vm_refl. Qed.
Lemma D_92dd8 : decode_any W_92dd8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ddc : bv 32 := 0x00158593.
Lemma F_92ddc : fetch_word AsanUbsan.M.loaded_segments (0x92c60 : word) = Some W_92ddc.
Proof. vm_refl. Qed.
Lemma D_92ddc : decode_any W_92ddc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92de0 : bv 32 := 0x00377293.
Lemma F_92de0 : fetch_word AsanUbsan.M.loaded_segments (0x92c64 : word) = Some W_92de0.
Proof. vm_refl. Qed.
Lemma D_92de0 : decode_any W_92de0 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92de4 : bv 32 := 0x01168023.
Lemma F_92de4 : fetch_word AsanUbsan.M.loaded_segments (0x92c68 : word) = Some W_92de4.
Proof. vm_refl. Qed.
Lemma D_92de4 : decode_any W_92de4 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92de8 : bv 32 := 0x00168693.
Lemma F_92de8 : fetch_word AsanUbsan.M.loaded_segments (0x92c6c : word) = Some W_92de8.
Proof. vm_refl. Qed.
Lemma D_92de8 : decode_any W_92de8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dec : bv 32 := 0xfff60613.
Lemma F_92dec : fetch_word AsanUbsan.M.loaded_segments (0x92c70 : word) = Some W_92dec.
Proof. vm_refl. Qed.
Lemma D_92dec : decode_any W_92dec = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_92df0 : bv 32 := 0x00028a63.
Lemma F_92df0 : fetch_word AsanUbsan.M.loaded_segments (0x92c74 : word) = Some W_92df0.
Proof. vm_refl. Qed.
Lemma D_92df0 : decode_any W_92df0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_92df4 : bv 32 := 0x00170713.
Lemma F_92df4 : fetch_word AsanUbsan.M.loaded_segments (0x92c78 : word) = Some W_92df4.
Proof. vm_refl. Qed.
Lemma D_92df4 : decode_any W_92df4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92df8 : bv 32 := 0xfcf81ee3.
Lemma F_92df8 : fetch_word AsanUbsan.M.loaded_segments (0x92c7c : word) = Some W_92df8.
Proof. vm_refl. Qed.
Lemma D_92df8 : decode_any W_92df8 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.
Definition W_92dfc : bv 32 := 0x0080006f.
Lemma F_92dfc : fetch_word AsanUbsan.M.loaded_segments (0x92c80 : word) = Some W_92dfc.
Proof. vm_refl. Qed.
Lemma D_92dfc : decode_any W_92dfc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e00 : bv 32 := 0x00050693.
Lemma F_92e00 : fetch_word AsanUbsan.M.loaded_segments (0x92c84 : word) = Some W_92e00.
Proof. vm_refl. Qed.
Lemma D_92e00 : decode_any W_92e00 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e04 : bv 32 := 0x0036f793.
Lemma F_92e04 : fetch_word AsanUbsan.M.loaded_segments (0x92c88 : word) = Some W_92e04.
Proof. vm_refl. Qed.
Lemma D_92e04 : decode_any W_92e04 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e08 : bv 32 := 0x0c078a63.
Lemma F_92e08 : fetch_word AsanUbsan.M.loaded_segments (0x92c8c : word) = Some W_92e08.
Proof. vm_refl. Qed.
Lemma D_92e08 : decode_any W_92e08 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e0c : bv 32 := 0x02000713.
Lemma F_92e0c : fetch_word AsanUbsan.M.loaded_segments (0x92c90 : word) = Some W_92e0c.
Proof. vm_refl. Qed.
Lemma D_92e0c : decode_any W_92e0c = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e10 : bv 32 := 0x02e67063.
Lemma F_92e10 : fetch_word AsanUbsan.M.loaded_segments (0x92c94 : word) = Some W_92e10.
Proof. vm_refl. Qed.
Lemma D_92e10 : decode_any W_92e10 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e14 : bv 32 := 0x01000713.
Lemma F_92e14 : fetch_word AsanUbsan.M.loaded_segments (0x92c98 : word) = Some W_92e14.
Proof. vm_refl. Qed.
Lemma D_92e14 : decode_any W_92e14 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e18 : bv 32 := 0x24e67863.
Lemma F_92e18 : fetch_word AsanUbsan.M.loaded_segments (0x92c9c : word) = Some W_92e18.
Proof. vm_refl. Qed.
Lemma D_92e18 : decode_any W_92e18 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e1c : bv 32 := 0x00867713.
Lemma F_92e1c : fetch_word AsanUbsan.M.loaded_segments (0x92ca0 : word) = Some W_92e1c.
Proof. vm_refl. Qed.
Lemma D_92e1c : decode_any W_92e1c = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e20 : bv 32 := 0x2c071e63.
Lemma F_92e20 : fetch_word AsanUbsan.M.loaded_segments (0x92ca4 : word) = Some W_92e20.
Proof. vm_refl. Qed.
Lemma D_92e20 : decode_any W_92e20 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e24 : bv 32 := 0x00467713.
Lemma F_92e24 : fetch_word AsanUbsan.M.loaded_segments (0x92ca8 : word) = Some W_92e24.
Proof. vm_refl. Qed.
Lemma D_92e24 : decode_any W_92e24 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e28 : bv 32 := 0x32071463.
Lemma F_92e28 : fetch_word AsanUbsan.M.loaded_segments (0x92cac : word) = Some W_92e28.
Proof. vm_refl. Qed.
Lemma D_92e28 : decode_any W_92e28 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e2c : bv 32 := 0x3500006f.
Lemma F_92e2c : fetch_word AsanUbsan.M.loaded_segments (0x92cb0 : word) = Some W_92e2c.
Proof. vm_refl. Qed.
Lemma D_92e2c : decode_any W_92e2c = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e30 : bv 32 := 0x0005a703.
Lemma F_92e30 : fetch_word AsanUbsan.M.loaded_segments (0x92cb4 : word) = Some W_92e30.
Proof. vm_refl. Qed.
Lemma D_92e30 : decode_any W_92e30 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e34 : bv 32 := 0x00300813.
Lemma F_92e34 : fetch_word AsanUbsan.M.loaded_segments (0x92cb8 : word) = Some W_92e34.
Proof. vm_refl. Qed.
Lemma D_92e34 : decode_any W_92e34 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e38 : bv 32 := 0x11078e63.
Lemma F_92e38 : fetch_word AsanUbsan.M.loaded_segments (0x92cbc : word) = Some W_92e38.
Proof. vm_refl. Qed.
Lemma D_92e38 : decode_any W_92e38 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e3c : bv 32 := 0x00200813.
Lemma F_92e3c : fetch_word AsanUbsan.M.loaded_segments (0x92cc0 : word) = Some W_92e3c.
Proof. vm_refl. Qed.
Lemma D_92e3c : decode_any W_92e3c = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e40 : bv 32 := 0x19079c63.
Lemma F_92e40 : fetch_word AsanUbsan.M.loaded_segments (0x92cc4 : word) = Some W_92e40.
Proof. vm_refl. Qed.
Lemma D_92e40 : decode_any W_92e40 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e44 : bv 32 := 0x00875793.
Lemma F_92e44 : fetch_word AsanUbsan.M.loaded_segments (0x92cc8 : word) = Some W_92e44.
Proof. vm_refl. Qed.
Lemma D_92e44 : decode_any W_92e44 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e48 : bv 32 := 0xffe60613.
Lemma F_92e48 : fetch_word AsanUbsan.M.loaded_segments (0x92ccc : word) = Some W_92e48.
Proof. vm_refl. Qed.
Lemma D_92e48 : decode_any W_92e48 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e4c : bv 32 := 0x00e68023.
Lemma F_92e4c : fetch_word AsanUbsan.M.loaded_segments (0x92cd0 : word) = Some W_92e4c.
Proof. vm_refl. Qed.
Lemma D_92e4c : decode_any W_92e4c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e50 : bv 32 := 0x00f680a3.
Lemma F_92e50 : fetch_word AsanUbsan.M.loaded_segments (0x92cd4 : word) = Some W_92e50.
Proof. vm_refl. Qed.
Lemma D_92e50 : decode_any W_92e50 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e54 : bv 32 := 0x00268693.
Lemma F_92e54 : fetch_word AsanUbsan.M.loaded_segments (0x92cd8 : word) = Some W_92e54.
Proof. vm_refl. Qed.
Lemma D_92e54 : decode_any W_92e54 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e58 : bv 32 := 0x01058593.
Lemma F_92e58 : fetch_word AsanUbsan.M.loaded_segments (0x92cdc : word) = Some W_92e58.
Proof. vm_refl. Qed.
Lemma D_92e58 : decode_any W_92e58 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e5c : bv 32 := 0x01100793.
Lemma F_92e5c : fetch_word AsanUbsan.M.loaded_segments (0x92ce0 : word) = Some W_92e5c.
Proof. vm_refl. Qed.
Lemma D_92e5c : decode_any W_92e5c = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e60 : bv 32 := 0x0107581b.
Lemma F_92e60 : fetch_word AsanUbsan.M.loaded_segments (0x92ce4 : word) = Some W_92e60.
Proof. vm_refl. Qed.
Lemma D_92e60 : decode_any W_92e60 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e64 : bv 32 := 0xff45a883.
Lemma F_92e64 : fetch_word AsanUbsan.M.loaded_segments (0x92ce8 : word) = Some W_92e64.
Proof. vm_refl. Qed.
Lemma D_92e64 : decode_any W_92e64 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e68 : bv 32 := 0xff85a283.
Lemma F_92e68 : fetch_word AsanUbsan.M.loaded_segments (0x92cec : word) = Some W_92e68.
Proof. vm_refl. Qed.
Lemma D_92e68 : decode_any W_92e68 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e6c : bv 32 := 0xffc5a303.
Lemma F_92e6c : fetch_word AsanUbsan.M.loaded_segments (0x92cf0 : word) = Some W_92e6c.
Proof. vm_refl. Qed.
Lemma D_92e6c : decode_any W_92e6c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e70 : bv 32 := 0x0005a703.
Lemma F_92e70 : fetch_word AsanUbsan.M.loaded_segments (0x92cf4 : word) = Some W_92e70.
Proof. vm_refl. Qed.
Lemma D_92e70 : decode_any W_92e70 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e74 : bv 32 := 0x01089393.
Lemma F_92e74 : fetch_word AsanUbsan.M.loaded_segments (0x92cf8 : word) = Some W_92e74.
Proof. vm_refl. Qed.
Lemma D_92e74 : decode_any W_92e74 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e78 : bv 32 := 0x0108d89b.
Lemma F_92e78 : fetch_word AsanUbsan.M.loaded_segments (0x92cfc : word) = Some W_92e78.
Proof. vm_refl. Qed.
Lemma D_92e78 : decode_any W_92e78 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e7c : bv 32 := 0x0103e833.
Lemma F_92e7c : fetch_word AsanUbsan.M.loaded_segments (0x92d00 : word) = Some W_92e7c.
Proof. vm_refl. Qed.
Lemma D_92e7c : decode_any W_92e7c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e80 : bv 32 := 0x01029393.
Lemma F_92e80 : fetch_word AsanUbsan.M.loaded_segments (0x92d04 : word) = Some W_92e80.
Proof. vm_refl. Qed.
Lemma D_92e80 : decode_any W_92e80 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e84 : bv 32 := 0x0102d29b.
Lemma F_92e84 : fetch_word AsanUbsan.M.loaded_segments (0x92d08 : word) = Some W_92e84.
Proof. vm_refl. Qed.
Lemma D_92e84 : decode_any W_92e84 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e88 : bv 32 := 0x0113e8b3.
Lemma F_92e88 : fetch_word AsanUbsan.M.loaded_segments (0x92d0c : word) = Some W_92e88.
Proof. vm_refl. Qed.
Lemma D_92e88 : decode_any W_92e88 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e8c : bv 32 := 0x01031393.
Lemma F_92e8c : fetch_word AsanUbsan.M.loaded_segments (0x92d10 : word) = Some W_92e8c.
Proof. vm_refl. Qed.
Lemma D_92e8c : decode_any W_92e8c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e90 : bv 32 := 0x0103531b.
Lemma F_92e90 : fetch_word AsanUbsan.M.loaded_segments (0x92d14 : word) = Some W_92e90.
Proof. vm_refl. Qed.
Lemma D_92e90 : decode_any W_92e90 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e94 : bv 32 := 0x0053e2b3.
Lemma F_92e94 : fetch_word AsanUbsan.M.loaded_segments (0x92d18 : word) = Some W_92e94.
Proof. vm_refl. Qed.
Lemma D_92e94 : decode_any W_92e94 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e98 : bv 32 := 0x01071393.
Lemma F_92e98 : fetch_word AsanUbsan.M.loaded_segments (0x92d1c : word) = Some W_92e98.
Proof. vm_refl. Qed.
Lemma D_92e98 : decode_any W_92e98 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92e9c : bv 32 := 0x0063e333.
Lemma F_92e9c : fetch_word AsanUbsan.M.loaded_segments (0x92d20 : word) = Some W_92e9c.
Proof. vm_refl. Qed.
Lemma D_92e9c : decode_any W_92e9c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ea0 : bv 32 := 0xff060613.
Lemma F_92ea0 : fetch_word AsanUbsan.M.loaded_segments (0x92d24 : word) = Some W_92ea0.
Proof. vm_refl. Qed.
Lemma D_92ea0 : decode_any W_92ea0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ea4 : bv 32 := 0x0106a023.
Lemma F_92ea4 : fetch_word AsanUbsan.M.loaded_segments (0x92d28 : word) = Some W_92ea4.
Proof. vm_refl. Qed.
Lemma D_92ea4 : decode_any W_92ea4 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ea8 : bv 32 := 0x0116a223.
Lemma F_92ea8 : fetch_word AsanUbsan.M.loaded_segments (0x92d2c : word) = Some W_92ea8.
Proof. vm_refl. Qed.
Lemma D_92ea8 : decode_any W_92ea8 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eac : bv 32 := 0x0056a423.
Lemma F_92eac : fetch_word AsanUbsan.M.loaded_segments (0x92d30 : word) = Some W_92eac.
Proof. vm_refl. Qed.
Lemma D_92eac : decode_any W_92eac = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eb0 : bv 32 := 0x0066a623.
Lemma F_92eb0 : fetch_word AsanUbsan.M.loaded_segments (0x92d34 : word) = Some W_92eb0.
Proof. vm_refl. Qed.
Lemma D_92eb0 : decode_any W_92eb0 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eb4 : bv 32 := 0x01068693.
Lemma F_92eb4 : fetch_word AsanUbsan.M.loaded_segments (0x92d38 : word) = Some W_92eb4.
Proof. vm_refl. Qed.
Lemma D_92eb4 : decode_any W_92eb4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eb8 : bv 32 := 0x01058593.
Lemma F_92eb8 : fetch_word AsanUbsan.M.loaded_segments (0x92d3c : word) = Some W_92eb8.
Proof. vm_refl. Qed.
Lemma D_92eb8 : decode_any W_92eb8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ebc : bv 32 := 0xfac7e2e3.
Lemma F_92ebc : fetch_word AsanUbsan.M.loaded_segments (0x92d40 : word) = Some W_92ebc.
Proof. vm_refl. Qed.
Lemma D_92ebc : decode_any W_92ebc = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ec0 : bv 32 := 0xff258593.
Lemma F_92ec0 : fetch_word AsanUbsan.M.loaded_segments (0x92d44 : word) = Some W_92ec0.
Proof. vm_refl. Qed.
Lemma D_92ec0 : decode_any W_92ec0 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ec4 : bv 32 := 0x01000713.
Lemma F_92ec4 : fetch_word AsanUbsan.M.loaded_segments (0x92d48 : word) = Some W_92ec4.
Proof. vm_refl. Qed.
Lemma D_92ec4 : decode_any W_92ec4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ec8 : bv 32 := 0xf4e66ae3.
Lemma F_92ec8 : fetch_word AsanUbsan.M.loaded_segments (0x92d4c : word) = Some W_92ec8.
Proof. vm_refl. Qed.
Lemma D_92ec8 : decode_any W_92ec8 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ecc : bv 32 := 0x19c0006f.
Lemma F_92ecc : fetch_word AsanUbsan.M.loaded_segments (0x92d50 : word) = Some W_92ecc.
Proof. vm_refl. Qed.
Lemma D_92ecc : decode_any W_92ecc = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ed0 : bv 32 := 0x00050693.
Lemma F_92ed0 : fetch_word AsanUbsan.M.loaded_segments (0x92d54 : word) = Some W_92ed0.
Proof. vm_refl. Qed.
Lemma D_92ed0 : decode_any W_92ed0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ed4 : bv 32 := 0x00357793.
Lemma F_92ed4 : fetch_word AsanUbsan.M.loaded_segments (0x92d58 : word) = Some W_92ed4.
Proof. vm_refl. Qed.
Lemma D_92ed4 : decode_any W_92ed4 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ed8 : bv 32 := 0xf2079ae3.
Lemma F_92ed8 : fetch_word AsanUbsan.M.loaded_segments (0x92d5c : word) = Some W_92ed8.
Proof. vm_refl. Qed.
Lemma D_92ed8 : decode_any W_92ed8 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.
Definition W_92edc : bv 32 := 0x01000713.
Lemma F_92edc : fetch_word AsanUbsan.M.loaded_segments (0x92d60 : word) = Some W_92edc.
Proof. vm_refl. Qed.
Lemma D_92edc : decode_any W_92edc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ee0 : bv 32 := 0x02e66c63.
Lemma F_92ee0 : fetch_word AsanUbsan.M.loaded_segments (0x92d64 : word) = Some W_92ee0.
Proof. vm_refl. Qed.
Lemma D_92ee0 : decode_any W_92ee0 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ee4 : bv 32 := 0x00f00713.
Lemma F_92ee4 : fetch_word AsanUbsan.M.loaded_segments (0x92d68 : word) = Some W_92ee4.
Proof. vm_refl. Qed.
Lemma D_92ee4 : decode_any W_92ee4 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ee8 : bv 32 := 0x0005a783.
Lemma F_92ee8 : fetch_word AsanUbsan.M.loaded_segments (0x92d6c : word) = Some W_92ee8.
Proof. vm_refl. Qed.
Lemma D_92ee8 : decode_any W_92ee8 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92eec : bv 32 := 0x0045a803.
Lemma F_92eec : fetch_word AsanUbsan.M.loaded_segments (0x92d70 : word) = Some W_92eec.
Proof. vm_refl. Qed.
Lemma D_92eec : decode_any W_92eec = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ef0 : bv 32 := 0x0085a883.
Lemma F_92ef0 : fetch_word AsanUbsan.M.loaded_segments (0x92d74 : word) = Some W_92ef0.
Proof. vm_refl. Qed.
Lemma D_92ef0 : decode_any W_92ef0 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ef4 : bv 32 := 0x00c5a283.
Lemma F_92ef4 : fetch_word AsanUbsan.M.loaded_segments (0x92d78 : word) = Some W_92ef4.
Proof. vm_refl. Qed.
Lemma D_92ef4 : decode_any W_92ef4 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ef8 : bv 32 := 0x01058593.
Lemma F_92ef8 : fetch_word AsanUbsan.M.loaded_segments (0x92d7c : word) = Some W_92ef8.
Proof. vm_refl. Qed.
Lemma D_92ef8 : decode_any W_92ef8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92efc : bv 32 := 0xff060613.
Lemma F_92efc : fetch_word AsanUbsan.M.loaded_segments (0x92d80 : word) = Some W_92efc.
Proof. vm_refl. Qed.
Lemma D_92efc : decode_any W_92efc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f00 : bv 32 := 0x00f6a023.
Lemma F_92f00 : fetch_word AsanUbsan.M.loaded_segments (0x92d84 : word) = Some W_92f00.
Proof. vm_refl. Qed.
Lemma D_92f00 : decode_any W_92f00 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f04 : bv 32 := 0x0106a223.
Lemma F_92f04 : fetch_word AsanUbsan.M.loaded_segments (0x92d88 : word) = Some W_92f04.
Proof. vm_refl. Qed.
Lemma D_92f04 : decode_any W_92f04 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f08 : bv 32 := 0x0116a423.
Lemma F_92f08 : fetch_word AsanUbsan.M.loaded_segments (0x92d8c : word) = Some W_92f08.
Proof. vm_refl. Qed.
Lemma D_92f08 : decode_any W_92f08 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f0c : bv 32 := 0x0056a623.
Lemma F_92f0c : fetch_word AsanUbsan.M.loaded_segments (0x92d90 : word) = Some W_92f0c.
Proof. vm_refl. Qed.
Lemma D_92f0c : decode_any W_92f0c = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f10 : bv 32 := 0x01068693.
Lemma F_92f10 : fetch_word AsanUbsan.M.loaded_segments (0x92d94 : word) = Some W_92f10.
Proof. vm_refl. Qed.
Lemma D_92f10 : decode_any W_92f10 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f14 : bv 32 := 0xfcc76ae3.
Lemma F_92f14 : fetch_word AsanUbsan.M.loaded_segments (0x92d98 : word) = Some W_92f14.
Proof. vm_refl. Qed.
Lemma D_92f14 : decode_any W_92f14 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f18 : bv 32 := 0x00800713.
Lemma F_92f18 : fetch_word AsanUbsan.M.loaded_segments (0x92d9c : word) = Some W_92f18.
Proof. vm_refl. Qed.
Lemma D_92f18 : decode_any W_92f18 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f1c : bv 32 := 0x00e66e63.
Lemma F_92f1c : fetch_word AsanUbsan.M.loaded_segments (0x92da0 : word) = Some W_92f1c.
Proof. vm_refl. Qed.
Lemma D_92f1c : decode_any W_92f1c = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f20 : bv 32 := 0x0005a703.
Lemma F_92f20 : fetch_word AsanUbsan.M.loaded_segments (0x92da4 : word) = Some W_92f20.
Proof. vm_refl. Qed.
Lemma D_92f20 : decode_any W_92f20 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f24 : bv 32 := 0x0045a783.
Lemma F_92f24 : fetch_word AsanUbsan.M.loaded_segments (0x92da8 : word) = Some W_92f24.
Proof. vm_refl. Qed.
Lemma D_92f24 : decode_any W_92f24 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f28 : bv 32 := 0x00e6a023.
Lemma F_92f28 : fetch_word AsanUbsan.M.loaded_segments (0x92dac : word) = Some W_92f28.
Proof. vm_refl. Qed.
Lemma D_92f28 : decode_any W_92f28 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f2c : bv 32 := 0x00f6a223.
Lemma F_92f2c : fetch_word AsanUbsan.M.loaded_segments (0x92db0 : word) = Some W_92f2c.
Proof. vm_refl. Qed.
Lemma D_92f2c : decode_any W_92f2c = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f30 : bv 32 := 0x00868693.
Lemma F_92f30 : fetch_word AsanUbsan.M.loaded_segments (0x92db4 : word) = Some W_92f30.
Proof. vm_refl. Qed.
Lemma D_92f30 : decode_any W_92f30 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f34 : bv 32 := 0x00858593.
Lemma F_92f34 : fetch_word AsanUbsan.M.loaded_segments (0x92db8 : word) = Some W_92f34.
Proof. vm_refl. Qed.
Lemma D_92f34 : decode_any W_92f34 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f38 : bv 32 := 0x00467713.
Lemma F_92f38 : fetch_word AsanUbsan.M.loaded_segments (0x92dbc : word) = Some W_92f38.
Proof. vm_refl. Qed.
Lemma D_92f38 : decode_any W_92f38 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f3c : bv 32 := 0x24070063.
Lemma F_92f3c : fetch_word AsanUbsan.M.loaded_segments (0x92dc0 : word) = Some W_92f3c.
Proof. vm_refl. Qed.
Lemma D_92f3c : decode_any W_92f3c = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f40 : bv 32 := 0x0005a703.
Lemma F_92f40 : fetch_word AsanUbsan.M.loaded_segments (0x92dc4 : word) = Some W_92f40.
Proof. vm_refl. Qed.
Lemma D_92f40 : decode_any W_92f40 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f44 : bv 32 := 0x00458593.
Lemma F_92f44 : fetch_word AsanUbsan.M.loaded_segments (0x92dc8 : word) = Some W_92f44.
Proof. vm_refl. Qed.
Lemma D_92f44 : decode_any W_92f44 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f48 : bv 32 := 0x00e6a023.
Lemma F_92f48 : fetch_word AsanUbsan.M.loaded_segments (0x92dcc : word) = Some W_92f48.
Proof. vm_refl. Qed.
Lemma D_92f48 : decode_any W_92f48 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f4c : bv 32 := 0x00468693.
Lemma F_92f4c : fetch_word AsanUbsan.M.loaded_segments (0x92dd0 : word) = Some W_92f4c.
Proof. vm_refl. Qed.
Lemma D_92f4c : decode_any W_92f4c = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f50 : bv 32 := 0x22c0006f.
Lemma F_92f50 : fetch_word AsanUbsan.M.loaded_segments (0x92dd4 : word) = Some W_92f50.
Proof. vm_refl. Qed.
Lemma D_92f50 : decode_any W_92f50 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f54 : bv 32 := 0x00e68023.
Lemma F_92f54 : fetch_word AsanUbsan.M.loaded_segments (0x92dd8 : word) = Some W_92f54.
Proof. vm_refl. Qed.
Lemma D_92f54 : decode_any W_92f54 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f58 : bv 32 := 0x00168693.
Lemma F_92f58 : fetch_word AsanUbsan.M.loaded_segments (0x92ddc : word) = Some W_92f58.
Proof. vm_refl. Qed.
Lemma D_92f58 : decode_any W_92f58 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f5c : bv 32 := 0xfff60613.
Lemma F_92f5c : fetch_word AsanUbsan.M.loaded_segments (0x92de0 : word) = Some W_92f5c.
Proof. vm_refl. Qed.
Lemma D_92f5c : decode_any W_92f5c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f60 : bv 32 := 0x01058593.
Lemma F_92f60 : fetch_word AsanUbsan.M.loaded_segments (0x92de4 : word) = Some W_92f60.
Proof. vm_refl. Qed.
Lemma D_92f60 : decode_any W_92f60 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f64 : bv 32 := 0x01200793.
Lemma F_92f64 : fetch_word AsanUbsan.M.loaded_segments (0x92de8 : word) = Some W_92f64.
Proof. vm_refl. Qed.
Lemma D_92f64 : decode_any W_92f64 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f68 : bv 32 := 0x0087581b.
Lemma F_92f68 : fetch_word AsanUbsan.M.loaded_segments (0x92dec : word) = Some W_92f68.
Proof. vm_refl. Qed.
Lemma D_92f68 : decode_any W_92f68 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f6c : bv 32 := 0xff45a883.
Lemma F_92f6c : fetch_word AsanUbsan.M.loaded_segments (0x92df0 : word) = Some W_92f6c.
Proof. vm_refl. Qed.
Lemma D_92f6c : decode_any W_92f6c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f70 : bv 32 := 0xff85a283.
Lemma F_92f70 : fetch_word AsanUbsan.M.loaded_segments (0x92df4 : word) = Some W_92f70.
Proof. vm_refl. Qed.
Lemma D_92f70 : decode_any W_92f70 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f74 : bv 32 := 0xffc5a303.
Lemma F_92f74 : fetch_word AsanUbsan.M.loaded_segments (0x92df8 : word) = Some W_92f74.
Proof. vm_refl. Qed.
Lemma D_92f74 : decode_any W_92f74 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f78 : bv 32 := 0x0005a703.
Lemma F_92f78 : fetch_word AsanUbsan.M.loaded_segments (0x92dfc : word) = Some W_92f78.
Proof. vm_refl. Qed.
Lemma D_92f78 : decode_any W_92f78 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f7c : bv 32 := 0x01889393.
Lemma F_92f7c : fetch_word AsanUbsan.M.loaded_segments (0x92e00 : word) = Some W_92f7c.
Proof. vm_refl. Qed.
Lemma D_92f7c : decode_any W_92f7c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f80 : bv 32 := 0x0088d89b.
Lemma F_92f80 : fetch_word AsanUbsan.M.loaded_segments (0x92e04 : word) = Some W_92f80.
Proof. vm_refl. Qed.
Lemma D_92f80 : decode_any W_92f80 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f84 : bv 32 := 0x0103e833.
Lemma F_92f84 : fetch_word AsanUbsan.M.loaded_segments (0x92e08 : word) = Some W_92f84.
Proof. vm_refl. Qed.
Lemma D_92f84 : decode_any W_92f84 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f88 : bv 32 := 0x01829393.
Lemma F_92f88 : fetch_word AsanUbsan.M.loaded_segments (0x92e0c : word) = Some W_92f88.
Proof. vm_refl. Qed.
Lemma D_92f88 : decode_any W_92f88 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f8c : bv 32 := 0x0082d29b.
Lemma F_92f8c : fetch_word AsanUbsan.M.loaded_segments (0x92e10 : word) = Some W_92f8c.
Proof. vm_refl. Qed.
Lemma D_92f8c : decode_any W_92f8c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f90 : bv 32 := 0x0113e8b3.
Lemma F_92f90 : fetch_word AsanUbsan.M.loaded_segments (0x92e14 : word) = Some W_92f90.
Proof. vm_refl. Qed.
Lemma D_92f90 : decode_any W_92f90 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f94 : bv 32 := 0x01831393.
Lemma F_92f94 : fetch_word AsanUbsan.M.loaded_segments (0x92e18 : word) = Some W_92f94.
Proof. vm_refl. Qed.
Lemma D_92f94 : decode_any W_92f94 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f98 : bv 32 := 0x0083531b.
Lemma F_92f98 : fetch_word AsanUbsan.M.loaded_segments (0x92e1c : word) = Some W_92f98.
Proof. vm_refl. Qed.
Lemma D_92f98 : decode_any W_92f98 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92f9c : bv 32 := 0x0053e2b3.
Lemma F_92f9c : fetch_word AsanUbsan.M.loaded_segments (0x92e20 : word) = Some W_92f9c.
Proof. vm_refl. Qed.
Lemma D_92f9c : decode_any W_92f9c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fa0 : bv 32 := 0x01871393.
Lemma F_92fa0 : fetch_word AsanUbsan.M.loaded_segments (0x92e24 : word) = Some W_92fa0.
Proof. vm_refl. Qed.
Lemma D_92fa0 : decode_any W_92fa0 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fa4 : bv 32 := 0x0063e333.
Lemma F_92fa4 : fetch_word AsanUbsan.M.loaded_segments (0x92e28 : word) = Some W_92fa4.
Proof. vm_refl. Qed.
Lemma D_92fa4 : decode_any W_92fa4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fa8 : bv 32 := 0xff060613.
Lemma F_92fa8 : fetch_word AsanUbsan.M.loaded_segments (0x92e2c : word) = Some W_92fa8.
Proof. vm_refl. Qed.
Lemma D_92fa8 : decode_any W_92fa8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fac : bv 32 := 0x0106a023.
Lemma F_92fac : fetch_word AsanUbsan.M.loaded_segments (0x92e30 : word) = Some W_92fac.
Proof. vm_refl. Qed.
Lemma D_92fac : decode_any W_92fac = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fb0 : bv 32 := 0x0116a223.
Lemma F_92fb0 : fetch_word AsanUbsan.M.loaded_segments (0x92e34 : word) = Some W_92fb0.
Proof. vm_refl. Qed.
Lemma D_92fb0 : decode_any W_92fb0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fb4 : bv 32 := 0x0056a423.
Lemma F_92fb4 : fetch_word AsanUbsan.M.loaded_segments (0x92e38 : word) = Some W_92fb4.
Proof. vm_refl. Qed.
Lemma D_92fb4 : decode_any W_92fb4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fb8 : bv 32 := 0x0066a623.
Lemma F_92fb8 : fetch_word AsanUbsan.M.loaded_segments (0x92e3c : word) = Some W_92fb8.
Proof. vm_refl. Qed.
Lemma D_92fb8 : decode_any W_92fb8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fbc : bv 32 := 0x01068693.
Lemma F_92fbc : fetch_word AsanUbsan.M.loaded_segments (0x92e40 : word) = Some W_92fbc.
Proof. vm_refl. Qed.
Lemma D_92fbc : decode_any W_92fbc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fc0 : bv 32 := 0x01058593.
Lemma F_92fc0 : fetch_word AsanUbsan.M.loaded_segments (0x92e44 : word) = Some W_92fc0.
Proof. vm_refl. Qed.
Lemma D_92fc0 : decode_any W_92fc0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fc4 : bv 32 := 0xfac7e2e3.
Lemma F_92fc4 : fetch_word AsanUbsan.M.loaded_segments (0x92e48 : word) = Some W_92fc4.
Proof. vm_refl. Qed.
Lemma D_92fc4 : decode_any W_92fc4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fc8 : bv 32 := 0xff158593.
Lemma F_92fc8 : fetch_word AsanUbsan.M.loaded_segments (0x92e4c : word) = Some W_92fc8.
Proof. vm_refl. Qed.
Lemma D_92fc8 : decode_any W_92fc8 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fcc : bv 32 := 0x01000713.
Lemma F_92fcc : fetch_word AsanUbsan.M.loaded_segments (0x92e50 : word) = Some W_92fcc.
Proof. vm_refl. Qed.
Lemma D_92fcc : decode_any W_92fcc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fd0 : bv 32 := 0xe4e666e3.
Lemma F_92fd0 : fetch_word AsanUbsan.M.loaded_segments (0x92e54 : word) = Some W_92fd0.
Proof. vm_refl. Qed.
Lemma D_92fd0 : decode_any W_92fd0 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fd4 : bv 32 := 0x0940006f.
Lemma F_92fd4 : fetch_word AsanUbsan.M.loaded_segments (0x92e58 : word) = Some W_92fd4.
Proof. vm_refl. Qed.
Lemma D_92fd4 : decode_any W_92fd4 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fd8 : bv 32 := 0x00875793.
Lemma F_92fd8 : fetch_word AsanUbsan.M.loaded_segments (0x92e5c : word) = Some W_92fd8.
Proof. vm_refl. Qed.
Lemma D_92fd8 : decode_any W_92fd8 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fdc : bv 32 := 0x01075813.
Lemma F_92fdc : fetch_word AsanUbsan.M.loaded_segments (0x92e60 : word) = Some W_92fdc.
Proof. vm_refl. Qed.
Lemma D_92fdc : decode_any W_92fdc = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fe0 : bv 32 := 0xffd60613.
Lemma F_92fe0 : fetch_word AsanUbsan.M.loaded_segments (0x92e64 : word) = Some W_92fe0.
Proof. vm_refl. Qed.
Lemma D_92fe0 : decode_any W_92fe0 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fe4 : bv 32 := 0x00e68023.
Lemma F_92fe4 : fetch_word AsanUbsan.M.loaded_segments (0x92e68 : word) = Some W_92fe4.
Proof. vm_refl. Qed.
Lemma D_92fe4 : decode_any W_92fe4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fe8 : bv 32 := 0x00f680a3.
Lemma F_92fe8 : fetch_word AsanUbsan.M.loaded_segments (0x92e6c : word) = Some W_92fe8.
Proof. vm_refl. Qed.
Lemma D_92fe8 : decode_any W_92fe8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_92fec : bv 32 := 0x01068123.
Lemma F_92fec : fetch_word AsanUbsan.M.loaded_segments (0x92e70 : word) = Some W_92fec.
Proof. vm_refl. Qed.
Lemma D_92fec : decode_any W_92fec = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ff0 : bv 32 := 0x00368693.
Lemma F_92ff0 : fetch_word AsanUbsan.M.loaded_segments (0x92e74 : word) = Some W_92ff0.
Proof. vm_refl. Qed.
Lemma D_92ff0 : decode_any W_92ff0 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ff4 : bv 32 := 0x01058593.
Lemma F_92ff4 : fetch_word AsanUbsan.M.loaded_segments (0x92e78 : word) = Some W_92ff4.
Proof. vm_refl. Qed.
Lemma D_92ff4 : decode_any W_92ff4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ff8 : bv 32 := 0x01000793.
Lemma F_92ff8 : fetch_word AsanUbsan.M.loaded_segments (0x92e7c : word) = Some W_92ff8.
Proof. vm_refl. Qed.
Lemma D_92ff8 : decode_any W_92ff8 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_92ffc : bv 32 := 0x0187581b.
Lemma F_92ffc : fetch_word AsanUbsan.M.loaded_segments (0x92e80 : word) = Some W_92ffc.
Proof. vm_refl. Qed.
Lemma D_92ffc : decode_any W_92ffc = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_93000 : bv 32 := 0xff45a883.
Lemma F_93000 : fetch_word AsanUbsan.M.loaded_segments (0x92e84 : word) = Some W_93000.
Proof. vm_refl. Qed.
Lemma D_93000 : decode_any W_93000 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_93004 : bv 32 := 0xff85a283.
Lemma F_93004 : fetch_word AsanUbsan.M.loaded_segments (0x92e88 : word) = Some W_93004.
Proof. vm_refl. Qed.
Lemma D_93004 : decode_any W_93004 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_93008 : bv 32 := 0xffc5a303.
Lemma F_93008 : fetch_word AsanUbsan.M.loaded_segments (0x92e8c : word) = Some W_93008.
Proof. vm_refl. Qed.
Lemma D_93008 : decode_any W_93008 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_9300c : bv 32 := 0x0005a703.
Lemma F_9300c : fetch_word AsanUbsan.M.loaded_segments (0x92e90 : word) = Some W_9300c.
Proof. vm_refl. Qed.
Lemma D_9300c : decode_any W_9300c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93010 : bv 32 := 0x00889393.
Lemma F_93010 : fetch_word AsanUbsan.M.loaded_segments (0x92e94 : word) = Some W_93010.
Proof. vm_refl. Qed.
Lemma D_93010 : decode_any W_93010 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_93014 : bv 32 := 0x0188d89b.
Lemma F_93014 : fetch_word AsanUbsan.M.loaded_segments (0x92e98 : word) = Some W_93014.
Proof. vm_refl. Qed.
Lemma D_93014 : decode_any W_93014 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_93018 : bv 32 := 0x0103e833.
Lemma F_93018 : fetch_word AsanUbsan.M.loaded_segments (0x92e9c : word) = Some W_93018.
Proof. vm_refl. Qed.
Lemma D_93018 : decode_any W_93018 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_9301c : bv 32 := 0x00829393.
Lemma F_9301c : fetch_word AsanUbsan.M.loaded_segments (0x92ea0 : word) = Some W_9301c.
Proof. vm_refl. Qed.
Lemma D_9301c : decode_any W_9301c = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_93020 : bv 32 := 0x0182d29b.
Lemma F_93020 : fetch_word AsanUbsan.M.loaded_segments (0x92ea4 : word) = Some W_93020.
Proof. vm_refl. Qed.
Lemma D_93020 : decode_any W_93020 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_93024 : bv 32 := 0x0113e8b3.
Lemma F_93024 : fetch_word AsanUbsan.M.loaded_segments (0x92ea8 : word) = Some W_93024.
Proof. vm_refl. Qed.
Lemma D_93024 : decode_any W_93024 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_93028 : bv 32 := 0x00831393.
Lemma F_93028 : fetch_word AsanUbsan.M.loaded_segments (0x92eac : word) = Some W_93028.
Proof. vm_refl. Qed.
Lemma D_93028 : decode_any W_93028 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_9302c : bv 32 := 0x0183531b.
Lemma F_9302c : fetch_word AsanUbsan.M.loaded_segments (0x92eb0 : word) = Some W_9302c.
Proof. vm_refl. Qed.
Lemma D_9302c : decode_any W_9302c = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_93030 : bv 32 := 0x0053e2b3.
Lemma F_93030 : fetch_word AsanUbsan.M.loaded_segments (0x92eb4 : word) = Some W_93030.
Proof. vm_refl. Qed.
Lemma D_93030 : decode_any W_93030 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_93034 : bv 32 := 0x00871393.
Lemma F_93034 : fetch_word AsanUbsan.M.loaded_segments (0x92eb8 : word) = Some W_93034.
Proof. vm_refl. Qed.
Lemma D_93034 : decode_any W_93034 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_93038 : bv 32 := 0x0063e333.
Lemma F_93038 : fetch_word AsanUbsan.M.loaded_segments (0x92ebc : word) = Some W_93038.
Proof. vm_refl. Qed.
Lemma D_93038 : decode_any W_93038 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_9303c : bv 32 := 0xff060613.
Lemma F_9303c : fetch_word AsanUbsan.M.loaded_segments (0x92ec0 : word) = Some W_9303c.
Proof. vm_refl. Qed.
Lemma D_9303c : decode_any W_9303c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_93040 : bv 32 := 0x0106a023.
Lemma F_93040 : fetch_word AsanUbsan.M.loaded_segments (0x92ec4 : word) = Some W_93040.
Proof. vm_refl. Qed.
Lemma D_93040 : decode_any W_93040 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93044 : bv 32 := 0x0116a223.
Lemma F_93044 : fetch_word AsanUbsan.M.loaded_segments (0x92ec8 : word) = Some W_93044.
Proof. vm_refl. Qed.
Lemma D_93044 : decode_any W_93044 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_93048 : bv 32 := 0x0056a423.
Lemma F_93048 : fetch_word AsanUbsan.M.loaded_segments (0x92ecc : word) = Some W_93048.
Proof. vm_refl. Qed.
Lemma D_93048 : decode_any W_93048 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_9304c : bv 32 := 0x0066a623.
Lemma F_9304c : fetch_word AsanUbsan.M.loaded_segments (0x92ed0 : word) = Some W_9304c.
Proof. vm_refl. Qed.
Lemma D_9304c : decode_any W_9304c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_93050 : bv 32 := 0x01068693.
Lemma F_93050 : fetch_word AsanUbsan.M.loaded_segments (0x92ed4 : word) = Some W_93050.
Proof. vm_refl. Qed.
Lemma D_93050 : decode_any W_93050 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_93054 : bv 32 := 0x01058593.
Lemma F_93054 : fetch_word AsanUbsan.M.loaded_segments (0x92ed8 : word) = Some W_93054.
Proof. vm_refl. Qed.
Lemma D_93054 : decode_any W_93054 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_93058 : bv 32 := 0xfac7e2e3.
Lemma F_93058 : fetch_word AsanUbsan.M.loaded_segments (0x92edc : word) = Some W_93058.
Proof. vm_refl. Qed.
Lemma D_93058 : decode_any W_93058 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_9305c : bv 32 := 0xff358593.
Lemma F_9305c : fetch_word AsanUbsan.M.loaded_segments (0x92ee0 : word) = Some W_9305c.
Proof. vm_refl. Qed.
Lemma D_9305c : decode_any W_9305c = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.
Definition W_93060 : bv 32 := 0x01000713.
Lemma F_93060 : fetch_word AsanUbsan.M.loaded_segments (0x92ee4 : word) = Some W_93060.
Proof. vm_refl. Qed.
Lemma D_93060 : decode_any W_93060 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_93064 : bv 32 := 0xdae66ce3.
Lemma F_93064 : fetch_word AsanUbsan.M.loaded_segments (0x92ee8 : word) = Some W_93064.
Proof. vm_refl. Qed.
Lemma D_93064 : decode_any W_93064 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.
Definition W_93068 : bv 32 := 0x0005c703.
Lemma F_93068 : fetch_word AsanUbsan.M.loaded_segments (0x92eec : word) = Some W_93068.
Proof. vm_refl. Qed.
Lemma D_93068 : decode_any W_93068 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_9306c : bv 32 := 0x0015c783.
Lemma F_9306c : fetch_word AsanUbsan.M.loaded_segments (0x92ef0 : word) = Some W_9306c.
Proof. vm_refl. Qed.
Lemma D_9306c : decode_any W_9306c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93070 : bv 32 := 0x0025c803.
Lemma F_93070 : fetch_word AsanUbsan.M.loaded_segments (0x92ef4 : word) = Some W_93070.
Proof. vm_refl. Qed.
Lemma D_93070 : decode_any W_93070 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_93074 : bv 32 := 0x0035c883.
Lemma F_93074 : fetch_word AsanUbsan.M.loaded_segments (0x92ef8 : word) = Some W_93074.
Proof. vm_refl. Qed.
Lemma D_93074 : decode_any W_93074 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_93078 : bv 32 := 0x0045c283.
Lemma F_93078 : fetch_word AsanUbsan.M.loaded_segments (0x92efc : word) = Some W_93078.
Proof. vm_refl. Qed.
Lemma D_93078 : decode_any W_93078 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_9307c : bv 32 := 0x0055c303.
Lemma F_9307c : fetch_word AsanUbsan.M.loaded_segments (0x92f00 : word) = Some W_9307c.
Proof. vm_refl. Qed.
Lemma D_9307c : decode_any W_9307c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_93080 : bv 32 := 0x0065c383.
Lemma F_93080 : fetch_word AsanUbsan.M.loaded_segments (0x92f04 : word) = Some W_93080.
Proof. vm_refl. Qed.
Lemma D_93080 : decode_any W_93080 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_93084 : bv 32 := 0x0075ce03.
Lemma F_93084 : fetch_word AsanUbsan.M.loaded_segments (0x92f08 : word) = Some W_93084.
Proof. vm_refl. Qed.
Lemma D_93084 : decode_any W_93084 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_93088 : bv 32 := 0x00e68023.
Lemma F_93088 : fetch_word AsanUbsan.M.loaded_segments (0x92f0c : word) = Some W_93088.
Proof. vm_refl. Qed.
Lemma D_93088 : decode_any W_93088 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_9308c : bv 32 := 0x00f680a3.
Lemma F_9308c : fetch_word AsanUbsan.M.loaded_segments (0x92f10 : word) = Some W_9308c.
Proof. vm_refl. Qed.
Lemma D_9308c : decode_any W_9308c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93090 : bv 32 := 0x01068123.
Lemma F_93090 : fetch_word AsanUbsan.M.loaded_segments (0x92f14 : word) = Some W_93090.
Proof. vm_refl. Qed.
Lemma D_93090 : decode_any W_93090 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_93094 : bv 32 := 0x011681a3.
Lemma F_93094 : fetch_word AsanUbsan.M.loaded_segments (0x92f18 : word) = Some W_93094.
Proof. vm_refl. Qed.
Lemma D_93094 : decode_any W_93094 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_93098 : bv 32 := 0x0085c703.
Lemma F_93098 : fetch_word AsanUbsan.M.loaded_segments (0x92f1c : word) = Some W_93098.
Proof. vm_refl. Qed.
Lemma D_93098 : decode_any W_93098 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_9309c : bv 32 := 0x0095c783.
Lemma F_9309c : fetch_word AsanUbsan.M.loaded_segments (0x92f20 : word) = Some W_9309c.
Proof. vm_refl. Qed.
Lemma D_9309c : decode_any W_9309c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_930a0 : bv 32 := 0x00a5c803.
Lemma F_930a0 : fetch_word AsanUbsan.M.loaded_segments (0x92f24 : word) = Some W_930a0.
Proof. vm_refl. Qed.
Lemma D_930a0 : decode_any W_930a0 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_930a4 : bv 32 := 0x00b5c883.
Lemma F_930a4 : fetch_word AsanUbsan.M.loaded_segments (0x92f28 : word) = Some W_930a4.
Proof. vm_refl. Qed.
Lemma D_930a4 : decode_any W_930a4 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_930a8 : bv 32 := 0x00568223.
Lemma F_930a8 : fetch_word AsanUbsan.M.loaded_segments (0x92f2c : word) = Some W_930a8.
Proof. vm_refl. Qed.
Lemma D_930a8 : decode_any W_930a8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_930ac : bv 32 := 0x006682a3.
Lemma F_930ac : fetch_word AsanUbsan.M.loaded_segments (0x92f30 : word) = Some W_930ac.
Proof. vm_refl. Qed.
Lemma D_930ac : decode_any W_930ac = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_930b0 : bv 32 := 0x00768323.
Lemma F_930b0 : fetch_word AsanUbsan.M.loaded_segments (0x92f34 : word) = Some W_930b0.
Proof. vm_refl. Qed.
Lemma D_930b0 : decode_any W_930b0 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_930b4 : bv 32 := 0x01c683a3.
Lemma F_930b4 : fetch_word AsanUbsan.M.loaded_segments (0x92f38 : word) = Some W_930b4.
Proof. vm_refl. Qed.
Lemma D_930b4 : decode_any W_930b4 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_930b8 : bv 32 := 0x00c5c283.
Lemma F_930b8 : fetch_word AsanUbsan.M.loaded_segments (0x92f3c : word) = Some W_930b8.
Proof. vm_refl. Qed.
Lemma D_930b8 : decode_any W_930b8 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_930bc : bv 32 := 0x00d5c303.
Lemma F_930bc : fetch_word AsanUbsan.M.loaded_segments (0x92f40 : word) = Some W_930bc.
Proof. vm_refl. Qed.
Lemma D_930bc : decode_any W_930bc = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_930c0 : bv 32 := 0x00e5c383.
Lemma F_930c0 : fetch_word AsanUbsan.M.loaded_segments (0x92f44 : word) = Some W_930c0.
Proof. vm_refl. Qed.
Lemma D_930c0 : decode_any W_930c0 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_930c4 : bv 32 := 0x00f5ce03.
Lemma F_930c4 : fetch_word AsanUbsan.M.loaded_segments (0x92f48 : word) = Some W_930c4.
Proof. vm_refl. Qed.
Lemma D_930c4 : decode_any W_930c4 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_930c8 : bv 32 := 0x01058593.
Lemma F_930c8 : fetch_word AsanUbsan.M.loaded_segments (0x92f4c : word) = Some W_930c8.
Proof. vm_refl. Qed.
Lemma D_930c8 : decode_any W_930c8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_930cc : bv 32 := 0x00e68423.
Lemma F_930cc : fetch_word AsanUbsan.M.loaded_segments (0x92f50 : word) = Some W_930cc.
Proof. vm_refl. Qed.
Lemma D_930cc : decode_any W_930cc = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_930d0 : bv 32 := 0x00f684a3.
Lemma F_930d0 : fetch_word AsanUbsan.M.loaded_segments (0x92f54 : word) = Some W_930d0.
Proof. vm_refl. Qed.
Lemma D_930d0 : decode_any W_930d0 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_930d4 : bv 32 := 0x01068523.
Lemma F_930d4 : fetch_word AsanUbsan.M.loaded_segments (0x92f58 : word) = Some W_930d4.
Proof. vm_refl. Qed.
Lemma D_930d4 : decode_any W_930d4 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_930d8 : bv 32 := 0x011685a3.
Lemma F_930d8 : fetch_word AsanUbsan.M.loaded_segments (0x92f5c : word) = Some W_930d8.
Proof. vm_refl. Qed.
Lemma D_930d8 : decode_any W_930d8 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_930dc : bv 32 := 0x01068713.
Lemma F_930dc : fetch_word AsanUbsan.M.loaded_segments (0x92f60 : word) = Some W_930dc.
Proof. vm_refl. Qed.
Lemma D_930dc : decode_any W_930dc = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_930e0 : bv 32 := 0x00568623.
Lemma F_930e0 : fetch_word AsanUbsan.M.loaded_segments (0x92f64 : word) = Some W_930e0.
Proof. vm_refl. Qed.
Lemma D_930e0 : decode_any W_930e0 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_930e4 : bv 32 := 0x006686a3.
Lemma F_930e4 : fetch_word AsanUbsan.M.loaded_segments (0x92f68 : word) = Some W_930e4.
Proof. vm_refl. Qed.
Lemma D_930e4 : decode_any W_930e4 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_930e8 : bv 32 := 0x00768723.
Lemma F_930e8 : fetch_word AsanUbsan.M.loaded_segments (0x92f6c : word) = Some W_930e8.
Proof. vm_refl. Qed.
Lemma D_930e8 : decode_any W_930e8 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_930ec : bv 32 := 0x01c687a3.
Lemma F_930ec : fetch_word AsanUbsan.M.loaded_segments (0x92f70 : word) = Some W_930ec.
Proof. vm_refl. Qed.
Lemma D_930ec : decode_any W_930ec = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_930f0 : bv 32 := 0x00070693.
Lemma F_930f0 : fetch_word AsanUbsan.M.loaded_segments (0x92f74 : word) = Some W_930f0.
Proof. vm_refl. Qed.
Lemma D_930f0 : decode_any W_930f0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_930f4 : bv 32 := 0x00867713.
Lemma F_930f4 : fetch_word AsanUbsan.M.loaded_segments (0x92f78 : word) = Some W_930f4.
Proof. vm_refl. Qed.
Lemma D_930f4 : decode_any W_930f4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_930f8 : bv 32 := 0xd20706e3.
Lemma F_930f8 : fetch_word AsanUbsan.M.loaded_segments (0x92f7c : word) = Some W_930f8.
Proof. vm_refl. Qed.
Lemma D_930f8 : decode_any W_930f8 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.
Definition W_930fc : bv 32 := 0x0005c703.
Lemma F_930fc : fetch_word AsanUbsan.M.loaded_segments (0x92f80 : word) = Some W_930fc.
Proof. vm_refl. Qed.
Lemma D_930fc : decode_any W_930fc = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93100 : bv 32 := 0x0015c783.
Lemma F_93100 : fetch_word AsanUbsan.M.loaded_segments (0x92f84 : word) = Some W_93100.
Proof. vm_refl. Qed.
Lemma D_93100 : decode_any W_93100 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93104 : bv 32 := 0x0025c803.
Lemma F_93104 : fetch_word AsanUbsan.M.loaded_segments (0x92f88 : word) = Some W_93104.
Proof. vm_refl. Qed.
Lemma D_93104 : decode_any W_93104 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_93108 : bv 32 := 0x0035c883.
Lemma F_93108 : fetch_word AsanUbsan.M.loaded_segments (0x92f8c : word) = Some W_93108.
Proof. vm_refl. Qed.
Lemma D_93108 : decode_any W_93108 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_9310c : bv 32 := 0x0045c283.
Lemma F_9310c : fetch_word AsanUbsan.M.loaded_segments (0x92f90 : word) = Some W_9310c.
Proof. vm_refl. Qed.
Lemma D_9310c : decode_any W_9310c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_93110 : bv 32 := 0x0055c303.
Lemma F_93110 : fetch_word AsanUbsan.M.loaded_segments (0x92f94 : word) = Some W_93110.
Proof. vm_refl. Qed.
Lemma D_93110 : decode_any W_93110 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_93114 : bv 32 := 0x0065c383.
Lemma F_93114 : fetch_word AsanUbsan.M.loaded_segments (0x92f98 : word) = Some W_93114.
Proof. vm_refl. Qed.
Lemma D_93114 : decode_any W_93114 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_93118 : bv 32 := 0x0075ce03.
Lemma F_93118 : fetch_word AsanUbsan.M.loaded_segments (0x92f9c : word) = Some W_93118.
Proof. vm_refl. Qed.
Lemma D_93118 : decode_any W_93118 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_9311c : bv 32 := 0x00858593.
Lemma F_9311c : fetch_word AsanUbsan.M.loaded_segments (0x92fa0 : word) = Some W_9311c.
Proof. vm_refl. Qed.
Lemma D_9311c : decode_any W_9311c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_93120 : bv 32 := 0x00e68023.
Lemma F_93120 : fetch_word AsanUbsan.M.loaded_segments (0x92fa4 : word) = Some W_93120.
Proof. vm_refl. Qed.
Lemma D_93120 : decode_any W_93120 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93124 : bv 32 := 0x00f680a3.
Lemma F_93124 : fetch_word AsanUbsan.M.loaded_segments (0x92fa8 : word) = Some W_93124.
Proof. vm_refl. Qed.
Lemma D_93124 : decode_any W_93124 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93128 : bv 32 := 0x01068123.
Lemma F_93128 : fetch_word AsanUbsan.M.loaded_segments (0x92fac : word) = Some W_93128.
Proof. vm_refl. Qed.
Lemma D_93128 : decode_any W_93128 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_9312c : bv 32 := 0x011681a3.
Lemma F_9312c : fetch_word AsanUbsan.M.loaded_segments (0x92fb0 : word) = Some W_9312c.
Proof. vm_refl. Qed.
Lemma D_9312c : decode_any W_9312c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_93130 : bv 32 := 0x00868713.
Lemma F_93130 : fetch_word AsanUbsan.M.loaded_segments (0x92fb4 : word) = Some W_93130.
Proof. vm_refl. Qed.
Lemma D_93130 : decode_any W_93130 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_93134 : bv 32 := 0x00568223.
Lemma F_93134 : fetch_word AsanUbsan.M.loaded_segments (0x92fb8 : word) = Some W_93134.
Proof. vm_refl. Qed.
Lemma D_93134 : decode_any W_93134 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_93138 : bv 32 := 0x006682a3.
Lemma F_93138 : fetch_word AsanUbsan.M.loaded_segments (0x92fbc : word) = Some W_93138.
Proof. vm_refl. Qed.
Lemma D_93138 : decode_any W_93138 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_9313c : bv 32 := 0x00768323.
Lemma F_9313c : fetch_word AsanUbsan.M.loaded_segments (0x92fc0 : word) = Some W_9313c.
Proof. vm_refl. Qed.
Lemma D_9313c : decode_any W_9313c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_93140 : bv 32 := 0x01c683a3.
Lemma F_93140 : fetch_word AsanUbsan.M.loaded_segments (0x92fc4 : word) = Some W_93140.
Proof. vm_refl. Qed.
Lemma D_93140 : decode_any W_93140 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_93144 : bv 32 := 0x00070693.
Lemma F_93144 : fetch_word AsanUbsan.M.loaded_segments (0x92fc8 : word) = Some W_93144.
Proof. vm_refl. Qed.
Lemma D_93144 : decode_any W_93144 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93148 : bv 32 := 0x00467713.
Lemma F_93148 : fetch_word AsanUbsan.M.loaded_segments (0x92fcc : word) = Some W_93148.
Proof. vm_refl. Qed.
Lemma D_93148 : decode_any W_93148 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_9314c : bv 32 := 0x02070863.
Lemma F_9314c : fetch_word AsanUbsan.M.loaded_segments (0x92fd0 : word) = Some W_9314c.
Proof. vm_refl. Qed.
Lemma D_9314c : decode_any W_9314c = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.
Definition W_93150 : bv 32 := 0x0005c703.
Lemma F_93150 : fetch_word AsanUbsan.M.loaded_segments (0x92fd4 : word) = Some W_93150.
Proof. vm_refl. Qed.
Lemma D_93150 : decode_any W_93150 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93154 : bv 32 := 0x0015c783.
Lemma F_93154 : fetch_word AsanUbsan.M.loaded_segments (0x92fd8 : word) = Some W_93154.
Proof. vm_refl. Qed.
Lemma D_93154 : decode_any W_93154 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93158 : bv 32 := 0x0025c803.
Lemma F_93158 : fetch_word AsanUbsan.M.loaded_segments (0x92fdc : word) = Some W_93158.
Proof. vm_refl. Qed.
Lemma D_93158 : decode_any W_93158 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_9315c : bv 32 := 0x0035c883.
Lemma F_9315c : fetch_word AsanUbsan.M.loaded_segments (0x92fe0 : word) = Some W_9315c.
Proof. vm_refl. Qed.
Lemma D_9315c : decode_any W_9315c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_93160 : bv 32 := 0x00458593.
Lemma F_93160 : fetch_word AsanUbsan.M.loaded_segments (0x92fe4 : word) = Some W_93160.
Proof. vm_refl. Qed.
Lemma D_93160 : decode_any W_93160 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_93164 : bv 32 := 0x00468293.
Lemma F_93164 : fetch_word AsanUbsan.M.loaded_segments (0x92fe8 : word) = Some W_93164.
Proof. vm_refl. Qed.
Lemma D_93164 : decode_any W_93164 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_93168 : bv 32 := 0x00e68023.
Lemma F_93168 : fetch_word AsanUbsan.M.loaded_segments (0x92fec : word) = Some W_93168.
Proof. vm_refl. Qed.
Lemma D_93168 : decode_any W_93168 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_9316c : bv 32 := 0x00f680a3.
Lemma F_9316c : fetch_word AsanUbsan.M.loaded_segments (0x92ff0 : word) = Some W_9316c.
Proof. vm_refl. Qed.
Lemma D_9316c : decode_any W_9316c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93170 : bv 32 := 0x01068123.
Lemma F_93170 : fetch_word AsanUbsan.M.loaded_segments (0x92ff4 : word) = Some W_93170.
Proof. vm_refl. Qed.
Lemma D_93170 : decode_any W_93170 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_93174 : bv 32 := 0x011681a3.
Lemma F_93174 : fetch_word AsanUbsan.M.loaded_segments (0x92ff8 : word) = Some W_93174.
Proof. vm_refl. Qed.
Lemma D_93174 : decode_any W_93174 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_93178 : bv 32 := 0x00028693.
Lemma F_93178 : fetch_word AsanUbsan.M.loaded_segments (0x92ffc : word) = Some W_93178.
Proof. vm_refl. Qed.
Lemma D_93178 : decode_any W_93178 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_9317c : bv 32 := 0x00267713.
Lemma F_9317c : fetch_word AsanUbsan.M.loaded_segments (0x93000 : word) = Some W_9317c.
Proof. vm_refl. Qed.
Lemma D_9317c : decode_any W_9317c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_93180 : bv 32 := 0x00071863.
Lemma F_93180 : fetch_word AsanUbsan.M.loaded_segments (0x93004 : word) = Some W_93180.
Proof. vm_refl. Qed.
Lemma D_93180 : decode_any W_93180 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_93184 : bv 32 := 0x00167613.
Lemma F_93184 : fetch_word AsanUbsan.M.loaded_segments (0x93008 : word) = Some W_93184.
Proof. vm_refl. Qed.
Lemma D_93184 : decode_any W_93184 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93188 : bv 32 := 0x02061663.
Lemma F_93188 : fetch_word AsanUbsan.M.loaded_segments (0x9300c : word) = Some W_93188.
Proof. vm_refl. Qed.
Lemma D_93188 : decode_any W_93188 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.
Definition W_9318c : bv 32 := 0x00008067.
Lemma F_9318c : fetch_word AsanUbsan.M.loaded_segments (0x93010 : word) = Some W_9318c.
Proof. vm_refl. Qed.
Lemma D_9318c : decode_any W_9318c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93190 : bv 32 := 0x0005c703.
Lemma F_93190 : fetch_word AsanUbsan.M.loaded_segments (0x93014 : word) = Some W_93190.
Proof. vm_refl. Qed.
Lemma D_93190 : decode_any W_93190 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_93194 : bv 32 := 0x0015c783.
Lemma F_93194 : fetch_word AsanUbsan.M.loaded_segments (0x93018 : word) = Some W_93194.
Proof. vm_refl. Qed.
Lemma D_93194 : decode_any W_93194 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_93198 : bv 32 := 0x00258593.
Lemma F_93198 : fetch_word AsanUbsan.M.loaded_segments (0x9301c : word) = Some W_93198.
Proof. vm_refl. Qed.
Lemma D_93198 : decode_any W_93198 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_9319c : bv 32 := 0x00268813.
Lemma F_9319c : fetch_word AsanUbsan.M.loaded_segments (0x93020 : word) = Some W_9319c.
Proof. vm_refl. Qed.
Lemma D_9319c : decode_any W_9319c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_931a0 : bv 32 := 0x00e68023.
Lemma F_931a0 : fetch_word AsanUbsan.M.loaded_segments (0x93024 : word) = Some W_931a0.
Proof. vm_refl. Qed.
Lemma D_931a0 : decode_any W_931a0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_931a4 : bv 32 := 0x00f680a3.
Lemma F_931a4 : fetch_word AsanUbsan.M.loaded_segments (0x93028 : word) = Some W_931a4.
Proof. vm_refl. Qed.
Lemma D_931a4 : decode_any W_931a4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_931a8 : bv 32 := 0x00080693.
Lemma F_931a8 : fetch_word AsanUbsan.M.loaded_segments (0x9302c : word) = Some W_931a8.
Proof. vm_refl. Qed.
Lemma D_931a8 : decode_any W_931a8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_931ac : bv 32 := 0x00167613.
Lemma F_931ac : fetch_word AsanUbsan.M.loaded_segments (0x93030 : word) = Some W_931ac.
Proof. vm_refl. Qed.
Lemma D_931ac : decode_any W_931ac = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_931b0 : bv 32 := 0xfc060ee3.
Lemma F_931b0 : fetch_word AsanUbsan.M.loaded_segments (0x93034 : word) = Some W_931b0.
Proof. vm_refl. Qed.
Lemma D_931b0 : decode_any W_931b0 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.
Definition W_931b4 : bv 32 := 0x0005c583.
Lemma F_931b4 : fetch_word AsanUbsan.M.loaded_segments (0x93038 : word) = Some W_931b4.
Proof. vm_refl. Qed.
Lemma D_931b4 : decode_any W_931b4 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_931b8 : bv 32 := 0x00b68023.
Lemma F_931b8 : fetch_word AsanUbsan.M.loaded_segments (0x9303c : word) = Some W_931b8.
Proof. vm_refl. Qed.
Lemma D_931b8 : decode_any W_931b8 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_931bc : bv 32 := 0x00008067.
Lemma F_931bc : fetch_word AsanUbsan.M.loaded_segments (0x93040 : word) = Some W_931bc.
Proof. vm_refl. Qed.
Lemma D_931bc : decode_any W_931bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
