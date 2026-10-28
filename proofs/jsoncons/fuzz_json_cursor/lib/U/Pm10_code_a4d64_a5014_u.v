From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
(lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Local Notation "'F!' a w" := (fetch_word Ubsan.M.loaded_segments (a : word) = Some w) (at level 200, a at level 0, w at level 0, only parsing).
Local Notation "'D!' w i" := (decode_any w = Some (i, 4%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Local Notation "'D2!' w i" := (decode_any w = Some (i, 2%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Definition W_a4d64 : bv 32 := 0xfc010113.
Lemma F_a4d64 : F! 0xa6b18 W_a4d64.
Proof. vm_refl. Qed.
Lemma D_a4d64 : D! W_a4d64 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_a4d68 : bv 32 := 0x02113c23.
Lemma F_a4d68 : F! 0xa6b1c W_a4d68.
Proof. vm_refl. Qed.
Lemma D_a4d68 : D! W_a4d68 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_a4d6c : bv 32 := 0x02813823.
Lemma F_a4d6c : F! 0xa6b20 W_a4d6c.
Proof. vm_refl. Qed.
Lemma D_a4d6c : D! W_a4d6c (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_a4d70 : bv 32 := 0x02913423.
Lemma F_a4d70 : F! 0xa6b24 W_a4d70.
Proof. vm_refl. Qed.
Lemma D_a4d70 : D! W_a4d70 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_a4d74 : bv 32 := 0x03213023.
Lemma F_a4d74 : F! 0xa6b28 W_a4d74.
Proof. vm_refl. Qed.
Lemma D_a4d74 : D! W_a4d74 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_a4d78 : bv 32 := 0x01313c23.
Lemma F_a4d78 : F! 0xa6b2c W_a4d78.
Proof. vm_refl. Qed.
Lemma D_a4d78 : D! W_a4d78 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_a4d7c : bv 32 := 0x01413823.
Lemma F_a4d7c : F! 0xa6b30 W_a4d7c.
Proof. vm_refl. Qed.
Lemma D_a4d7c : D! W_a4d7c (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_a4d80 : bv 32 := 0x01513423.
Lemma F_a4d80 : F! 0xa6b34 W_a4d80.
Proof. vm_refl. Qed.
Lemma D_a4d80 : D! W_a4d80 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_a4d84 : bv 32 := 0x02853683.
Lemma F_a4d84 : F! 0xa6b38 W_a4d84.
Proof. vm_refl. Qed.
Lemma D_a4d84 : D! W_a4d84 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_a4d88 : bv 32 := 0x00050597.
Lemma F_a4d88 : F! 0xa6b3c W_a4d88.
Proof. vm_refl. Qed.
Lemma D_a4d88 : D! W_a4d88 (Auipc 11 80).
Proof. vm_refl. Qed.
Definition W_a4d8c : bv 32 := 0xccc58593.
Lemma F_a4d8c : F! 0xa6b40 W_a4d8c.
Proof. vm_refl. Qed.
Lemma D_a4d8c : D! W_a4d8c (OpImm ALU_ADD 11 11 3276).
Proof. vm_refl. Qed.
Definition W_a4d90 : bv 32 := 0x00050617.
Lemma F_a4d90 : F! 0xa6b44 W_a4d90.
Proof. vm_refl. Qed.
Lemma D_a4d90 : D! W_a4d90 (Auipc 12 80).
Proof. vm_refl. Qed.
Definition W_a4d94 : bv 32 := 0xf4c60493.
Lemma F_a4d94 : F! 0xa6b48 W_a4d94.
Proof. vm_refl. Qed.
Lemma D_a4d94 : D! W_a4d94 (OpImm ALU_ADD 9 12 3916).
Proof. vm_refl. Qed.
Definition W_a4d98 : bv 32 := 0x0c068e63.
Lemma F_a4d98 : F! 0xa6b4c W_a4d98.
Proof. vm_refl. Qed.
Lemma D_a4d98 : D! W_a4d98 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_a4d9c : bv 32 := 0x00000613.
Lemma F_a4d9c : F! 0xa6b50 W_a4d9c.
Proof. vm_refl. Qed.
Lemma D_a4d9c : D! W_a4d9c (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_a4da0 : bv 32 := 0x00000893.
Lemma F_a4da0 : F! 0xa6b54 W_a4da0.
Proof. vm_refl. Qed.
Lemma D_a4da0 : D! W_a4da0 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_a4da4 : bv 32 := 0x0001e717.
Lemma F_a4da4 : F! 0xa6b58 W_a4da4.
Proof. vm_refl. Qed.
Lemma D_a4da4 : D! W_a4da4 (Auipc 14 30).
Proof. vm_refl. Qed.
Definition W_a4da8 : bv 32 := 0x01853783.
Lemma F_a4da8 : F! 0xa6b5c W_a4da8.
Proof. vm_refl. Qed.
Lemma D_a4da8 : D! W_a4da8 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_a4dac : bv 32 := 0x02053503.
Lemma F_a4dac : F! 0xa6b60 W_a4dac.
Proof. vm_refl. Qed.
Lemma D_a4dac : D! W_a4dac (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_a4db0 : bv 32 := 0x00600813.
Lemma F_a4db0 : F! 0xa6b64 W_a4db0.
Proof. vm_refl. Qed.
Lemma D_a4db0 : D! W_a4db0 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_a4db4 : bv 32 := 0x0001d297.
Lemma F_a4db4 : F! 0xa6b68 W_a4db4.
Proof. vm_refl. Qed.
Lemma D_a4db4 : D! W_a4db4 (Auipc 5 29).
Proof. vm_refl. Qed.
Definition W_a4db8 : bv 32 := 0x1f076f03.
Lemma F_a4db8 : F! 0xa6b6c W_a4db8.
Proof. vm_refl. Qed.
Lemma D_a4db8 : D! W_a4db8 (Load SZ4 false 30 14 496).
Proof. vm_refl. Qed.
Definition W_a4dbc : bv 32 := 0xd382b283.
Lemma F_a4dbc : F! 0xa6b70 W_a4dbc.
Proof. vm_refl. Qed.
Lemma D_a4dbc : D! W_a4dbc (Load SZ8 true 5 5 3384).
Proof. vm_refl. Qed.
Definition W_a4dc0 : bv 32 := 0x00200313.
Lemma F_a4dc0 : F! 0xa6b74 W_a4dc0.
Proof. vm_refl. Qed.
Lemma D_a4dc0 : D! W_a4dc0 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_a4dc4 : bv 32 := 0x00700393.
Lemma F_a4dc4 : F! 0xa6b78 W_a4dc4.
Proof. vm_refl. Qed.
Lemma D_a4dc4 : D! W_a4dc4 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_a4dc8 : bv 32 := 0x6474ee37.
Lemma F_a4dc8 : F! 0xa6b7c W_a4dc8.
Proof. vm_refl. Qed.
Lemma D_a4dc8 : D! W_a4dc8 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_a4dcc : bv 32 := 0x551e0e1b.
Lemma F_a4dcc : F! 0xa6b80 W_a4dcc.
Proof. vm_refl. Qed.
Lemma D_a4dcc : D! W_a4dcc (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_a4dd0 : bv 32 := 0x00078e93.
Lemma F_a4dd0 : F! 0xa6b84 W_a4dd0.
Proof. vm_refl. Qed.
Lemma D_a4dd0 : D! W_a4dd0 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_a4dd4 : bv 32 := 0x0180006f.
Lemma F_a4dd4 : F! 0xa6b88 W_a4dd4.
Proof. vm_refl. Qed.
Lemma D_a4dd4 : D! W_a4dd4 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_a4dd8 : bv 32 := 0x010eb603.
Lemma F_a4dd8 : F! 0xa6b8c W_a4dd8.
Proof. vm_refl. Qed.
Lemma D_a4dd8 : D! W_a4dd8 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_a4ddc : bv 32 := 0x40c78633.
Lemma F_a4ddc : F! 0xa6b90 W_a4ddc.
Proof. vm_refl. Qed.
Lemma D_a4ddc : D! W_a4ddc (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_a4de0 : bv 32 := 0xfff68693.
Lemma F_a4de0 : F! 0xa6b94 W_a4de0.
Proof. vm_refl. Qed.
Lemma D_a4de0 : D! W_a4de0 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_a4de4 : bv 32 := 0x00ae8eb3.
Lemma F_a4de4 : F! 0xa6b98 W_a4de4.
Proof. vm_refl. Qed.
Lemma D_a4de4 : D! W_a4de4 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_a4de8 : bv 32 := 0x04068a63.
Lemma F_a4de8 : F! 0xa6b9c W_a4de8.
Proof. vm_refl. Qed.
Lemma D_a4de8 : D! W_a4de8 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_a4dec : bv 32 := 0x000ea403.
Lemma F_a4dec : F! 0xa6ba0 W_a4dec.
Proof. vm_refl. Qed.
Lemma D_a4dec : D! W_a4dec (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_a4df0 : bv 32 := 0xff0404e3.
Lemma F_a4df0 : F! 0xa6ba4 W_a4df0.
Proof. vm_refl. Qed.
Lemma D_a4df0 : D! W_a4df0 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_a4df4 : bv 32 := 0x00028a63.
Lemma F_a4df4 : F! 0xa6ba8 W_a4df4.
Proof. vm_refl. Qed.
Lemma D_a4df4 : D! W_a4df4 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_a4e08 : bv 32 := 0x000e8f93.
Lemma F_a4e08 : F! 0xa6bbc W_a4e08.
Proof. vm_refl. Qed.
Lemma D_a4e08 : D! W_a4e08 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_a4e0c : bv 32 := 0x00740463.
Lemma F_a4e0c : F! 0xa6bc0 W_a4e0c.
Proof. vm_refl. Qed.
Lemma D_a4e0c : D! W_a4e0c (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_a4e10 : bv 32 := 0x00088f93.
Lemma F_a4e10 : F! 0xa6bc4 W_a4e10.
Proof. vm_refl. Qed.
Lemma D_a4e10 : D! W_a4e10 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_a4e14 : bv 32 := 0x03c41063.
Lemma F_a4e14 : F! 0xa6bc8 W_a4e14.
Proof. vm_refl. Qed.
Lemma D_a4e14 : D! W_a4e14 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_a4e18 : bv 32 := 0x028eb883.
Lemma F_a4e18 : F! 0xa6bcc W_a4e18.
Proof. vm_refl. Qed.
Lemma D_a4e18 : D! W_a4e18 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_a4e1c : bv 32 := 0x011f7c63.
Lemma F_a4e1c : F! 0xa6bd0 W_a4e1c.
Proof. vm_refl. Qed.
Lemma D_a4e1c : D! W_a4e1c (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_a4e34 : bv 32 := 0x000f8893.
Lemma F_a4e34 : F! 0xa6be8 W_a4e34.
Proof. vm_refl. Qed.
Lemma D_a4e34 : D! W_a4e34 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_a4e38 : bv 32 := 0xfa9ff06f.
Lemma F_a4e38 : F! 0xa6bec W_a4e38.
Proof. vm_refl. Qed.
Lemma D_a4e38 : D! W_a4e38 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_a4e3c : bv 32 := 0x02088c63.
Lemma F_a4e3c : F! 0xa6bf0 W_a4e3c.
Proof. vm_refl. Qed.
Lemma D_a4e3c : D! W_a4e3c (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_a4e74 : bv 32 := 0x0105b603.
Lemma F_a4e74 : F! 0xa6c28 W_a4e74.
Proof. vm_refl. Qed.
Lemma D_a4e74 : D! W_a4e74 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_a4e78 : bv 32 := 0x0205b683.
Lemma F_a4e78 : F! 0xa6c2c W_a4e78.
Proof. vm_refl. Qed.
Lemma D_a4e78 : D! W_a4e78 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_a4e7c : bv 32 := 0x0285b503.
Lemma F_a4e7c : F! 0xa6c30 W_a4e7c.
Proof. vm_refl. Qed.
Lemma D_a4e7c : D! W_a4e7c (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_a4e80 : bv 32 := 0x00c68733.
Lemma F_a4e80 : F! 0xa6c34 W_a4e80.
Proof. vm_refl. Qed.
Lemma D_a4e80 : D! W_a4e80 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_a4e84 : bv 32 := 0xfff50793.
Lemma F_a4e84 : F! 0xa6c38 W_a4e84.
Proof. vm_refl. Qed.
Lemma D_a4e84 : D! W_a4e84 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_a4e88 : bv 32 := 0x40e00733.
Lemma F_a4e88 : F! 0xa6c3c W_a4e88.
Proof. vm_refl. Qed.
Lemma D_a4e88 : D! W_a4e88 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_a4e8c : bv 32 := 0x00c7f633.
Lemma F_a4e8c : F! 0xa6c40 W_a4e8c.
Proof. vm_refl. Qed.
Lemma D_a4e8c : D! W_a4e8c (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_a4e90 : bv 32 := 0x00e7f733.
Lemma F_a4e90 : F! 0xa6c44 W_a4e90.
Proof. vm_refl. Qed.
Lemma D_a4e90 : D! W_a4e90 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_a4e94 : bv 32 := 0x00700793.
Lemma F_a4e94 : F! 0xa6c48 W_a4e94.
Proof. vm_refl. Qed.
Lemma D_a4e94 : D! W_a4e94 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_a4e98 : bv 32 := 0x00d706b3.
Lemma F_a4e98 : F! 0xa6c4c W_a4e98.
Proof. vm_refl. Qed.
Lemma D_a4e98 : D! W_a4e98 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_a4e9c : bv 32 := 0x02d5b023.
Lemma F_a4e9c : F! 0xa6c50 W_a4e9c.
Proof. vm_refl. Qed.
Lemma D_a4e9c : D! W_a4e9c (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_a4ea0 : bv 32 := 0x02c5b823.
Lemma F_a4ea0 : F! 0xa6c54 W_a4ea0.
Proof. vm_refl. Qed.
Lemma D_a4ea0 : D! W_a4ea0 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_a4ea4 : bv 32 := 0x00a7e663.
Lemma F_a4ea4 : F! 0xa6c58 W_a4ea4.
Proof. vm_refl. Qed.
Lemma D_a4ea4 : D! W_a4ea4 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_a4ea8 : bv 32 := 0x00800513.
Lemma F_a4ea8 : F! 0xa6c5c W_a4ea8.
Proof. vm_refl. Qed.
Lemma D_a4ea8 : D! W_a4ea8 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_a4eac : bv 32 := 0x02a5b423.
Lemma F_a4eac : F! 0xa6c60 W_a4eac.
Proof. vm_refl. Qed.
Lemma D_a4eac : D! W_a4eac (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_a4eb0 : bv 32 := 0x00d60633.
Lemma F_a4eb0 : F! 0xa6c64 W_a4eb0.
Proof. vm_refl. Qed.
Lemma D_a4eb0 : D! W_a4eb0 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_a4eb4 : bv 32 := 0x000205b7.
Lemma F_a4eb4 : F! 0xa6c68 W_a4eb4.
Proof. vm_refl. Qed.
Lemma D_a4eb4 : D! W_a4eb4 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_a4eb8 : bv 32 := 0x00a60633.
Lemma F_a4eb8 : F! 0xa6c6c W_a4eb8.
Proof. vm_refl. Qed.
Lemma D_a4eb8 : D! W_a4eb8 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_a4ebc : bv 32 := 0x0d15869b.
Lemma F_a4ebc : F! 0xa6c70 W_a4ebc.
Proof. vm_refl. Qed.
Lemma D_a4ebc : D! W_a4ebc (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_a4ec0 : bv 32 := 0x0df60593.
Lemma F_a4ec0 : F! 0xa6c74 W_a4ec0.
Proof. vm_refl. Qed.
Lemma D_a4ec0 : D! W_a4ec0 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_a4ec4 : bv 32 := 0xff85f593.
Lemma F_a4ec4 : F! 0xa6c78 W_a4ec4.
Proof. vm_refl. Qed.
Lemma D_a4ec4 : D! W_a4ec4 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_a4ec8 : bv 32 := 0x00b4bc23.
Lemma F_a4ec8 : F! 0xa6c7c W_a4ec8.
Proof. vm_refl. Qed.
Lemma D_a4ec8 : D! W_a4ec8 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_a4ecc : bv 32 := 0x02a4b023.
Lemma F_a4ecc : F! 0xa6c80 W_a4ecc.
Proof. vm_refl. Qed.
Lemma D_a4ecc : D! W_a4ecc (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_a4ed0 : bv 32 := 0x02d5ea63.
Lemma F_a4ed0 : F! 0xa6c84 W_a4ed0.
Proof. vm_refl. Qed.
Lemma D_a4ed0 : D! W_a4ed0 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_a4f04 : bv 32 := 0x00030697.
Lemma F_a4f04 : F! 0xa6cb8 W_a4f04.
Proof. vm_refl. Qed.
Lemma D_a4f04 : D! W_a4f04 (Auipc 13 48).
Proof. vm_refl. Qed.
Definition W_a4f08 : bv 32 := 0x0104b983.
Lemma F_a4f08 : F! 0xa6cbc W_a4f08.
Proof. vm_refl. Qed.
Lemma D_a4f08 : D! W_a4f08 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_a4f0c : bv 32 := 0x0284b603.
Lemma F_a4f0c : F! 0xa6cc0 W_a4f0c.
Proof. vm_refl. Qed.
Lemma D_a4f0c : D! W_a4f0c (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_a4f10 : bv 32 := 0xfff50713.
Lemma F_a4f10 : F! 0xa6cc4 W_a4f10.
Proof. vm_refl. Qed.
Lemma D_a4f10 : D! W_a4f10 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_a4f14 : bv 32 := 0xf3800793.
Lemma F_a4f14 : F! 0xa6cc8 W_a4f14.
Proof. vm_refl. Qed.
Lemma D_a4f14 : D! W_a4f14 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_a4f18 : bv 32 := 0xa8068513.
Lemma F_a4f18 : F! 0xa6ccc W_a4f18.
Proof. vm_refl. Qed.
Lemma D_a4f18 : D! W_a4f18 (OpImm ALU_ADD 10 13 2688).
Proof. vm_refl. Qed.
Definition W_a4f1c : bv 32 := 0x40a787b3.
Lemma F_a4f1c : F! 0xa6cd0 W_a4f1c.
Proof. vm_refl. Qed.
Lemma D_a4f1c : D! W_a4f1c (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_a4f20 : bv 32 := 0x00f77733.
Lemma F_a4f20 : F! 0xa6cd4 W_a4f20.
Proof. vm_refl. Qed.
Lemma D_a4f20 : D! W_a4f20 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_a4f24 : bv 32 := 0xfff64693.
Lemma F_a4f24 : F! 0xa6cd8 W_a4f24.
Proof. vm_refl. Qed.
Lemma D_a4f24 : D! W_a4f24 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_a4f28 : bv 32 := 0x00e50933.
Lemma F_a4f28 : F! 0xa6cdc W_a4f28.
Proof. vm_refl. Qed.
Lemma D_a4f28 : D! W_a4f28 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_a4f2c : bv 32 := 0x00369693.
Lemma F_a4f2c : F! 0xa6ce0 W_a4f2c.
Proof. vm_refl. Qed.
Lemma D_a4f2c : D! W_a4f2c (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_a4f30 : bv 32 := 0x00d506b3.
Lemma F_a4f30 : F! 0xa6ce4 W_a4f30.
Proof. vm_refl. Qed.
Lemma D_a4f30 : D! W_a4f30 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_a4f34 : bv 32 := 0x00b68a33.
Lemma F_a4f34 : F! 0xa6ce8 W_a4f34.
Proof. vm_refl. Qed.
Lemma D_a4f34 : D! W_a4f34 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_a4f38 : bv 32 := 0x0c890413.
Lemma F_a4f38 : F! 0xa6cec W_a4f38.
Proof. vm_refl. Qed.
Lemma D_a4f38 : D! W_a4f38 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_a4f3c : bv 32 := 0x04098463.
Lemma F_a4f3c : F! 0xa6cf0 W_a4f3c.
Proof. vm_refl. Qed.
Lemma D_a4f3c : D! W_a4f3c (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_a4f84 : bv 32 := 0x00ca3023.
Lemma F_a4f84 : F! 0xa6d38 W_a4f84.
Proof. vm_refl. Qed.
Lemma D_a4f84 : D! W_a4f84 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_a4f88 : bv 32 := 0x0d493023.
Lemma F_a4f88 : F! 0xa6d3c W_a4f88.
Proof. vm_refl. Qed.
Lemma D_a4f88 : D! W_a4f88 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_a4f8c : bv 32 := 0x01293023.
Lemma F_a4f8c : F! 0xa6d40 W_a4f8c.
Proof. vm_refl. Qed.
Lemma D_a4f8c : D! W_a4f8c (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_a4f90 : bv 32 := 0x00040513.
Lemma F_a4f90 : F! 0xa6d44 W_a4f90.
Proof. vm_refl. Qed.
Lemma D_a4f90 : D! W_a4f90 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_a4f94 : bv 32 := 0x20c130ef.
Lemma F_a4f94 : F! 0xa6d48 W_a4f94.
Proof. vm_refl. Qed.
Lemma D_a4f94 : D! W_a4f94 (Jal 1 78348).
Proof. vm_refl. Qed.
Definition W_a4f98 : bv 32 := 0x04054a63.
Lemma F_a4f98 : F! 0xa6d4c W_a4f98.
Proof. vm_refl. Qed.
Lemma D_a4f98 : D! W_a4f98 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_a4f9c : bv 32 := 0x00051663.
Lemma F_a4f9c : F! 0xa6d50 W_a4f9c.
Proof. vm_refl. Qed.
Lemma D_a4f9c : D! W_a4f9c (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_a4fa0 : bv 32 := 0x00100513.
Lemma F_a4fa0 : F! 0xa6d54 W_a4fa0.
Proof. vm_refl. Qed.
Lemma D_a4fa0 : D! W_a4fa0 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_a4fa4 : bv 32 := 0x00a48023.
Lemma F_a4fa4 : F! 0xa6d58 W_a4fa4.
Proof. vm_refl. Qed.
Lemma D_a4fa4 : D! W_a4fa4 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_a4fa8 : bv 32 := 0x00200513.
Lemma F_a4fa8 : F! 0xa6d5c W_a4fa8.
Proof. vm_refl. Qed.
Lemma D_a4fa8 : D! W_a4fa8 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_a4fac : bv 32 := 0x00050597.
Lemma F_a4fac : F! 0xa6d60 W_a4fac.
Proof. vm_refl. Qed.
Lemma D_a4fac : D! W_a4fac (Auipc 11 80).
Proof. vm_refl. Qed.
Definition W_a4fb0 : bv 32 := 0x02a92423.
Lemma F_a4fb0 : F! 0xa6d64 W_a4fb0.
Proof. vm_refl. Qed.
Lemma D_a4fb0 : D! W_a4fb0 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_a4fb4 : bv 32 := 0x06000893.
Lemma F_a4fb4 : F! 0xa6d68 W_a4fb4.
Proof. vm_refl. Qed.
Lemma D_a4fb4 : D! W_a4fb4 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_a4fb8 : bv 32 := 0xaa858513.
Lemma F_a4fb8 : F! 0xa6d6c W_a4fb8.
Proof. vm_refl. Qed.
Lemma D_a4fb8 : D! W_a4fb8 (OpImm ALU_ADD 10 11 2728).
Proof. vm_refl. Qed.
Definition W_a4fbc : bv 32 := 0x03848593.
Lemma F_a4fbc : F! 0xa6d70 W_a4fbc.
Proof. vm_refl. Qed.
Lemma D_a4fbc : D! W_a4fbc (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_a4fc0 : bv 32 := 0x00000073.
Lemma F_a4fc0 : F! 0xa6d74 W_a4fc0.
Proof. vm_refl. Qed.
Lemma E_a4fc0 : is_ecall W_a4fc0 = true.
Proof. reflexivity. Qed.
Definition W_a4fc4 : bv 32 := 0x07890613.
Lemma F_a4fc4 : F! 0xa6d78 W_a4fc4.
Proof. vm_refl. Qed.
Lemma D_a4fc4 : D! W_a4fc4 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_a4fc8 : bv 32 := 0x02a92023.
Lemma F_a4fc8 : F! 0xa6d7c W_a4fc8.
Proof. vm_refl. Qed.
Lemma D_a4fc8 : D! W_a4fc8 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_a4fcc : bv 32 := 0x08b93c23.
Lemma F_a4fcc : F! 0xa6d80 W_a4fcc.
Proof. vm_refl. Qed.
Lemma D_a4fcc : D! W_a4fcc (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_a4fd0 : bv 32 := 0x06c93c23.
Lemma F_a4fd0 : F! 0xa6d84 W_a4fd0.
Proof. vm_refl. Qed.
Lemma D_a4fd0 : D! W_a4fd0 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_a4fd4 : bv 32 := 0x00050517.
Lemma F_a4fd4 : F! 0xa6d88 W_a4fd4.
Proof. vm_refl. Qed.
Lemma D_a4fd4 : D! W_a4fd4 (Auipc 10 80).
Proof. vm_refl. Qed.
Definition W_a4fd8 : bv 32 := 0xcf053503.
Lemma F_a4fd8 : F! 0xa6d8c W_a4fd8.
Proof. vm_refl. Qed.
Lemma D_a4fd8 : D! W_a4fd8 (Load SZ8 true 10 10 3312).
Proof. vm_refl. Qed.
Definition W_a4fdc : bv 32 := 0x01293423.
Lemma F_a4fdc : F! 0xa6d90 W_a4fdc.
Proof. vm_refl. Qed.
Lemma D_a4fdc : D! W_a4fdc (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_a4fe0 : bv 32 := 0x01293823.
Lemma F_a4fe0 : F! 0xa6d94 W_a4fe0.
Proof. vm_refl. Qed.
Lemma D_a4fe0 : D! W_a4fe0 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_a4fe4 : bv 32 := 0x00a93c23.
Lemma F_a4fe4 : F! 0xa6d98 W_a4fe4.
Proof. vm_refl. Qed.
Lemma D_a4fe4 : D! W_a4fe4 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_a4fe8 : bv 32 := 0x0080006f.
Lemma F_a4fe8 : F! 0xa6d9c W_a4fe8.
Proof. vm_refl. Qed.
Lemma D_a4fe8 : D! W_a4fe8 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_a4ff0 : bv 32 := 0x03813083.
Lemma F_a4ff0 : F! 0xa6da4 W_a4ff0.
Proof. vm_refl. Qed.
Lemma D_a4ff0 : D! W_a4ff0 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_a4ff4 : bv 32 := 0x03013403.
Lemma F_a4ff4 : F! 0xa6da8 W_a4ff4.
Proof. vm_refl. Qed.
Lemma D_a4ff4 : D! W_a4ff4 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_a4ff8 : bv 32 := 0x02813483.
Lemma F_a4ff8 : F! 0xa6dac W_a4ff8.
Proof. vm_refl. Qed.
Lemma D_a4ff8 : D! W_a4ff8 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_a4ffc : bv 32 := 0x02013903.
Lemma F_a4ffc : F! 0xa6db0 W_a4ffc.
Proof. vm_refl. Qed.
Lemma D_a4ffc : D! W_a4ffc (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_a5000 : bv 32 := 0x01813983.
Lemma F_a5000 : F! 0xa6db4 W_a5000.
Proof. vm_refl. Qed.
Lemma D_a5000 : D! W_a5000 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_a5004 : bv 32 := 0x01013a03.
Lemma F_a5004 : F! 0xa6db8 W_a5004.
Proof. vm_refl. Qed.
Lemma D_a5004 : D! W_a5004 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_a5008 : bv 32 := 0x00813a83.
Lemma F_a5008 : F! 0xa6dbc W_a5008.
Proof. vm_refl. Qed.
Lemma D_a5008 : D! W_a5008 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_a500c : bv 32 := 0x04010113.
Lemma F_a500c : F! 0xa6dc0 W_a500c.
Proof. vm_refl. Qed.
Lemma D_a500c : D! W_a500c (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_a5010 : bv 32 := 0x00008067.
Lemma F_a5010 : F! 0xa6dc4 W_a5010.
Proof. vm_refl. Qed.
Lemma D_a5010 : D! W_a5010 (Jalr 0 1 0).
Proof. vm_refl. Qed.
