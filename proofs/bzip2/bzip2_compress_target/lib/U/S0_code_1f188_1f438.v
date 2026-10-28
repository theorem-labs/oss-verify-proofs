From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
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
Definition W_1f188 : bv 32 := 0xfc010113.
Lemma F_1f188 : F! 0x28c4c W_1f188.
Proof. vm_refl. Qed.
Lemma D_1f188 : D! W_1f188 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_1f18c : bv 32 := 0x02113c23.
Lemma F_1f18c : F! 0x28c50 W_1f18c.
Proof. vm_refl. Qed.
Lemma D_1f18c : D! W_1f18c (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_1f190 : bv 32 := 0x02813823.
Lemma F_1f190 : F! 0x28c54 W_1f190.
Proof. vm_refl. Qed.
Lemma D_1f190 : D! W_1f190 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_1f194 : bv 32 := 0x02913423.
Lemma F_1f194 : F! 0x28c58 W_1f194.
Proof. vm_refl. Qed.
Lemma D_1f194 : D! W_1f194 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_1f198 : bv 32 := 0x03213023.
Lemma F_1f198 : F! 0x28c5c W_1f198.
Proof. vm_refl. Qed.
Lemma D_1f198 : D! W_1f198 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_1f19c : bv 32 := 0x01313c23.
Lemma F_1f19c : F! 0x28c60 W_1f19c.
Proof. vm_refl. Qed.
Lemma D_1f19c : D! W_1f19c (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_1f1a0 : bv 32 := 0x01413823.
Lemma F_1f1a0 : F! 0x28c64 W_1f1a0.
Proof. vm_refl. Qed.
Lemma D_1f1a0 : D! W_1f1a0 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_1f1a4 : bv 32 := 0x01513423.
Lemma F_1f1a4 : F! 0x28c68 W_1f1a4.
Proof. vm_refl. Qed.
Lemma D_1f1a4 : D! W_1f1a4 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_1f1a8 : bv 32 := 0x02853683.
Lemma F_1f1a8 : F! 0x28c6c W_1f1a8.
Proof. vm_refl. Qed.
Lemma D_1f1a8 : D! W_1f1a8 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_1f1ac : bv 32 := 0x0003b597.
Lemma F_1f1ac : F! 0x28c70 W_1f1ac.
Proof. vm_refl. Qed.
Lemma D_1f1ac : D! W_1f1ac (Auipc 11 59).
Proof. vm_refl. Qed.
Definition W_1f1b0 : bv 32 := 0x57858593.
Lemma F_1f1b0 : F! 0x28c74 W_1f1b0.
Proof. vm_refl. Qed.
Lemma D_1f1b0 : D! W_1f1b0 (OpImm ALU_ADD 11 11 1400).
Proof. vm_refl. Qed.
Definition W_1f1b4 : bv 32 := 0x0003b617.
Lemma F_1f1b4 : F! 0x28c78 W_1f1b4.
Proof. vm_refl. Qed.
Lemma D_1f1b4 : D! W_1f1b4 (Auipc 12 59).
Proof. vm_refl. Qed.
Definition W_1f1b8 : bv 32 := 0x7f860493.
Lemma F_1f1b8 : F! 0x28c7c W_1f1b8.
Proof. vm_refl. Qed.
Lemma D_1f1b8 : D! W_1f1b8 (OpImm ALU_ADD 9 12 2040).
Proof. vm_refl. Qed.
Definition W_1f1bc : bv 32 := 0x0c068e63.
Lemma F_1f1bc : F! 0x28c80 W_1f1bc.
Proof. vm_refl. Qed.
Lemma D_1f1bc : D! W_1f1bc (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_1f1c0 : bv 32 := 0x00000613.
Lemma F_1f1c0 : F! 0x28c84 W_1f1c0.
Proof. vm_refl. Qed.
Lemma D_1f1c0 : D! W_1f1c0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_1f1c4 : bv 32 := 0x00000893.
Lemma F_1f1c4 : F! 0x28c88 W_1f1c4.
Proof. vm_refl. Qed.
Lemma D_1f1c4 : D! W_1f1c4 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_1f1c8 : bv 32 := 0x0000b717.
Lemma F_1f1c8 : F! 0x28c8c W_1f1c8.
Proof. vm_refl. Qed.
Lemma D_1f1c8 : D! W_1f1c8 (Auipc 14 11).
Proof. vm_refl. Qed.
Definition W_1f1cc : bv 32 := 0x01853783.
Lemma F_1f1cc : F! 0x28c90 W_1f1cc.
Proof. vm_refl. Qed.
Lemma D_1f1cc : D! W_1f1cc (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_1f1d0 : bv 32 := 0x02053503.
Lemma F_1f1d0 : F! 0x28c94 W_1f1d0.
Proof. vm_refl. Qed.
Lemma D_1f1d0 : D! W_1f1d0 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_1f1d4 : bv 32 := 0x00600813.
Lemma F_1f1d4 : F! 0x28c98 W_1f1d4.
Proof. vm_refl. Qed.
Lemma D_1f1d4 : D! W_1f1d4 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_1f1d8 : bv 32 := 0x00009297.
Lemma F_1f1d8 : F! 0x28c9c W_1f1d8.
Proof. vm_refl. Qed.
Lemma D_1f1d8 : D! W_1f1d8 (Auipc 5 9).
Proof. vm_refl. Qed.
Definition W_1f1dc : bv 32 := 0x3f476f03.
Lemma F_1f1dc : F! 0x28ca0 W_1f1dc.
Proof. vm_refl. Qed.
Lemma D_1f1dc : D! W_1f1dc (Load SZ4 false 30 14 1012).
Proof. vm_refl. Qed.
Definition W_1f1e0 : bv 32 := 0x4142b283.
Lemma F_1f1e0 : F! 0x28ca4 W_1f1e0.
Proof. vm_refl. Qed.
Lemma D_1f1e0 : D! W_1f1e0 (Load SZ8 true 5 5 1044).
Proof. vm_refl. Qed.
Definition W_1f1e4 : bv 32 := 0x00200313.
Lemma F_1f1e4 : F! 0x28ca8 W_1f1e4.
Proof. vm_refl. Qed.
Lemma D_1f1e4 : D! W_1f1e4 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_1f1e8 : bv 32 := 0x00700393.
Lemma F_1f1e8 : F! 0x28cac W_1f1e8.
Proof. vm_refl. Qed.
Lemma D_1f1e8 : D! W_1f1e8 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_1f1ec : bv 32 := 0x6474ee37.
Lemma F_1f1ec : F! 0x28cb0 W_1f1ec.
Proof. vm_refl. Qed.
Lemma D_1f1ec : D! W_1f1ec (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_1f1f0 : bv 32 := 0x551e0e1b.
Lemma F_1f1f0 : F! 0x28cb4 W_1f1f0.
Proof. vm_refl. Qed.
Lemma D_1f1f0 : D! W_1f1f0 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_1f1f4 : bv 32 := 0x00078e93.
Lemma F_1f1f4 : F! 0x28cb8 W_1f1f4.
Proof. vm_refl. Qed.
Lemma D_1f1f4 : D! W_1f1f4 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_1f1f8 : bv 32 := 0x0180006f.
Lemma F_1f1f8 : F! 0x28cbc W_1f1f8.
Proof. vm_refl. Qed.
Lemma D_1f1f8 : D! W_1f1f8 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_1f1fc : bv 32 := 0x010eb603.
Lemma F_1f1fc : F! 0x28cc0 W_1f1fc.
Proof. vm_refl. Qed.
Lemma D_1f1fc : D! W_1f1fc (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_1f200 : bv 32 := 0x40c78633.
Lemma F_1f200 : F! 0x28cc4 W_1f200.
Proof. vm_refl. Qed.
Lemma D_1f200 : D! W_1f200 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_1f204 : bv 32 := 0xfff68693.
Lemma F_1f204 : F! 0x28cc8 W_1f204.
Proof. vm_refl. Qed.
Lemma D_1f204 : D! W_1f204 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_1f208 : bv 32 := 0x00ae8eb3.
Lemma F_1f208 : F! 0x28ccc W_1f208.
Proof. vm_refl. Qed.
Lemma D_1f208 : D! W_1f208 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_1f20c : bv 32 := 0x04068a63.
Lemma F_1f20c : F! 0x28cd0 W_1f20c.
Proof. vm_refl. Qed.
Lemma D_1f20c : D! W_1f20c (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_1f210 : bv 32 := 0x000ea403.
Lemma F_1f210 : F! 0x28cd4 W_1f210.
Proof. vm_refl. Qed.
Lemma D_1f210 : D! W_1f210 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_1f214 : bv 32 := 0xff0404e3.
Lemma F_1f214 : F! 0x28cd8 W_1f214.
Proof. vm_refl. Qed.
Lemma D_1f214 : D! W_1f214 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_1f218 : bv 32 := 0x00028a63.
Lemma F_1f218 : F! 0x28cdc W_1f218.
Proof. vm_refl. Qed.
Lemma D_1f218 : D! W_1f218 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_1f22c : bv 32 := 0x000e8f93.
Lemma F_1f22c : F! 0x28cf0 W_1f22c.
Proof. vm_refl. Qed.
Lemma D_1f22c : D! W_1f22c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_1f230 : bv 32 := 0x00740463.
Lemma F_1f230 : F! 0x28cf4 W_1f230.
Proof. vm_refl. Qed.
Lemma D_1f230 : D! W_1f230 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_1f234 : bv 32 := 0x00088f93.
Lemma F_1f234 : F! 0x28cf8 W_1f234.
Proof. vm_refl. Qed.
Lemma D_1f234 : D! W_1f234 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_1f238 : bv 32 := 0x03c41063.
Lemma F_1f238 : F! 0x28cfc W_1f238.
Proof. vm_refl. Qed.
Lemma D_1f238 : D! W_1f238 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_1f23c : bv 32 := 0x028eb883.
Lemma F_1f23c : F! 0x28d00 W_1f23c.
Proof. vm_refl. Qed.
Lemma D_1f23c : D! W_1f23c (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_1f240 : bv 32 := 0x011f7c63.
Lemma F_1f240 : F! 0x28d04 W_1f240.
Proof. vm_refl. Qed.
Lemma D_1f240 : D! W_1f240 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_1f258 : bv 32 := 0x000f8893.
Lemma F_1f258 : F! 0x28d1c W_1f258.
Proof. vm_refl. Qed.
Lemma D_1f258 : D! W_1f258 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_1f25c : bv 32 := 0xfa9ff06f.
Lemma F_1f25c : F! 0x28d20 W_1f25c.
Proof. vm_refl. Qed.
Lemma D_1f25c : D! W_1f25c (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_1f260 : bv 32 := 0x02088c63.
Lemma F_1f260 : F! 0x28d24 W_1f260.
Proof. vm_refl. Qed.
Lemma D_1f260 : D! W_1f260 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_1f298 : bv 32 := 0x0105b603.
Lemma F_1f298 : F! 0x28d5c W_1f298.
Proof. vm_refl. Qed.
Lemma D_1f298 : D! W_1f298 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_1f29c : bv 32 := 0x0205b683.
Lemma F_1f29c : F! 0x28d60 W_1f29c.
Proof. vm_refl. Qed.
Lemma D_1f29c : D! W_1f29c (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_1f2a0 : bv 32 := 0x0285b503.
Lemma F_1f2a0 : F! 0x28d64 W_1f2a0.
Proof. vm_refl. Qed.
Lemma D_1f2a0 : D! W_1f2a0 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_1f2a4 : bv 32 := 0x00c68733.
Lemma F_1f2a4 : F! 0x28d68 W_1f2a4.
Proof. vm_refl. Qed.
Lemma D_1f2a4 : D! W_1f2a4 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_1f2a8 : bv 32 := 0xfff50793.
Lemma F_1f2a8 : F! 0x28d6c W_1f2a8.
Proof. vm_refl. Qed.
Lemma D_1f2a8 : D! W_1f2a8 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_1f2ac : bv 32 := 0x40e00733.
Lemma F_1f2ac : F! 0x28d70 W_1f2ac.
Proof. vm_refl. Qed.
Lemma D_1f2ac : D! W_1f2ac (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_1f2b0 : bv 32 := 0x00c7f633.
Lemma F_1f2b0 : F! 0x28d74 W_1f2b0.
Proof. vm_refl. Qed.
Lemma D_1f2b0 : D! W_1f2b0 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_1f2b4 : bv 32 := 0x00e7f733.
Lemma F_1f2b4 : F! 0x28d78 W_1f2b4.
Proof. vm_refl. Qed.
Lemma D_1f2b4 : D! W_1f2b4 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_1f2b8 : bv 32 := 0x00700793.
Lemma F_1f2b8 : F! 0x28d7c W_1f2b8.
Proof. vm_refl. Qed.
Lemma D_1f2b8 : D! W_1f2b8 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_1f2bc : bv 32 := 0x00d706b3.
Lemma F_1f2bc : F! 0x28d80 W_1f2bc.
Proof. vm_refl. Qed.
Lemma D_1f2bc : D! W_1f2bc (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_1f2c0 : bv 32 := 0x02d5b023.
Lemma F_1f2c0 : F! 0x28d84 W_1f2c0.
Proof. vm_refl. Qed.
Lemma D_1f2c0 : D! W_1f2c0 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_1f2c4 : bv 32 := 0x02c5b823.
Lemma F_1f2c4 : F! 0x28d88 W_1f2c4.
Proof. vm_refl. Qed.
Lemma D_1f2c4 : D! W_1f2c4 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_1f2c8 : bv 32 := 0x00a7e663.
Lemma F_1f2c8 : F! 0x28d8c W_1f2c8.
Proof. vm_refl. Qed.
Lemma D_1f2c8 : D! W_1f2c8 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_1f2cc : bv 32 := 0x00800513.
Lemma F_1f2cc : F! 0x28d90 W_1f2cc.
Proof. vm_refl. Qed.
Lemma D_1f2cc : D! W_1f2cc (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_1f2d0 : bv 32 := 0x02a5b423.
Lemma F_1f2d0 : F! 0x28d94 W_1f2d0.
Proof. vm_refl. Qed.
Lemma D_1f2d0 : D! W_1f2d0 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_1f2d4 : bv 32 := 0x00d60633.
Lemma F_1f2d4 : F! 0x28d98 W_1f2d4.
Proof. vm_refl. Qed.
Lemma D_1f2d4 : D! W_1f2d4 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_1f2d8 : bv 32 := 0x000205b7.
Lemma F_1f2d8 : F! 0x28d9c W_1f2d8.
Proof. vm_refl. Qed.
Lemma D_1f2d8 : D! W_1f2d8 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_1f2dc : bv 32 := 0x00a60633.
Lemma F_1f2dc : F! 0x28da0 W_1f2dc.
Proof. vm_refl. Qed.
Lemma D_1f2dc : D! W_1f2dc (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_1f2e0 : bv 32 := 0x0d15869b.
Lemma F_1f2e0 : F! 0x28da4 W_1f2e0.
Proof. vm_refl. Qed.
Lemma D_1f2e0 : D! W_1f2e0 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_1f2e4 : bv 32 := 0x0df60593.
Lemma F_1f2e4 : F! 0x28da8 W_1f2e4.
Proof. vm_refl. Qed.
Lemma D_1f2e4 : D! W_1f2e4 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_1f2e8 : bv 32 := 0xff85f593.
Lemma F_1f2e8 : F! 0x28dac W_1f2e8.
Proof. vm_refl. Qed.
Lemma D_1f2e8 : D! W_1f2e8 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_1f2ec : bv 32 := 0x00b4bc23.
Lemma F_1f2ec : F! 0x28db0 W_1f2ec.
Proof. vm_refl. Qed.
Lemma D_1f2ec : D! W_1f2ec (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_1f2f0 : bv 32 := 0x02a4b023.
Lemma F_1f2f0 : F! 0x28db4 W_1f2f0.
Proof. vm_refl. Qed.
Lemma D_1f2f0 : D! W_1f2f0 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_1f2f4 : bv 32 := 0x02d5ea63.
Lemma F_1f2f4 : F! 0x28db8 W_1f2f4.
Proof. vm_refl. Qed.
Lemma D_1f2f4 : D! W_1f2f4 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_1f328 : bv 32 := 0x0001b697.
Lemma F_1f328 : F! 0x28dec W_1f328.
Proof. vm_refl. Qed.
Lemma D_1f328 : D! W_1f328 (Auipc 13 27).
Proof. vm_refl. Qed.
Definition W_1f32c : bv 32 := 0x0104b983.
Lemma F_1f32c : F! 0x28df0 W_1f32c.
Proof. vm_refl. Qed.
Lemma D_1f32c : D! W_1f32c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_1f330 : bv 32 := 0x0284b603.
Lemma F_1f330 : F! 0x28df4 W_1f330.
Proof. vm_refl. Qed.
Lemma D_1f330 : D! W_1f330 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_1f334 : bv 32 := 0xfff50713.
Lemma F_1f334 : F! 0x28df8 W_1f334.
Proof. vm_refl. Qed.
Lemma D_1f334 : D! W_1f334 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_1f338 : bv 32 := 0xf3800793.
Lemma F_1f338 : F! 0x28dfc W_1f338.
Proof. vm_refl. Qed.
Lemma D_1f338 : D! W_1f338 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_1f33c : bv 32 := 0x32c68513.
Lemma F_1f33c : F! 0x28e00 W_1f33c.
Proof. vm_refl. Qed.
Lemma D_1f33c : D! W_1f33c (OpImm ALU_ADD 10 13 812).
Proof. vm_refl. Qed.
Definition W_1f340 : bv 32 := 0x40a787b3.
Lemma F_1f340 : F! 0x28e04 W_1f340.
Proof. vm_refl. Qed.
Lemma D_1f340 : D! W_1f340 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_1f344 : bv 32 := 0x00f77733.
Lemma F_1f344 : F! 0x28e08 W_1f344.
Proof. vm_refl. Qed.
Lemma D_1f344 : D! W_1f344 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_1f348 : bv 32 := 0xfff64693.
Lemma F_1f348 : F! 0x28e0c W_1f348.
Proof. vm_refl. Qed.
Lemma D_1f348 : D! W_1f348 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_1f34c : bv 32 := 0x00e50933.
Lemma F_1f34c : F! 0x28e10 W_1f34c.
Proof. vm_refl. Qed.
Lemma D_1f34c : D! W_1f34c (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_1f350 : bv 32 := 0x00369693.
Lemma F_1f350 : F! 0x28e14 W_1f350.
Proof. vm_refl. Qed.
Lemma D_1f350 : D! W_1f350 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_1f354 : bv 32 := 0x00d506b3.
Lemma F_1f354 : F! 0x28e18 W_1f354.
Proof. vm_refl. Qed.
Lemma D_1f354 : D! W_1f354 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_1f358 : bv 32 := 0x00b68a33.
Lemma F_1f358 : F! 0x28e1c W_1f358.
Proof. vm_refl. Qed.
Lemma D_1f358 : D! W_1f358 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_1f35c : bv 32 := 0x0c890413.
Lemma F_1f35c : F! 0x28e20 W_1f35c.
Proof. vm_refl. Qed.
Lemma D_1f35c : D! W_1f35c (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_1f360 : bv 32 := 0x04098463.
Lemma F_1f360 : F! 0x28e24 W_1f360.
Proof. vm_refl. Qed.
Lemma D_1f360 : D! W_1f360 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_1f3a8 : bv 32 := 0x00ca3023.
Lemma F_1f3a8 : F! 0x28e6c W_1f3a8.
Proof. vm_refl. Qed.
Lemma D_1f3a8 : D! W_1f3a8 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_1f3ac : bv 32 := 0x0d493023.
Lemma F_1f3ac : F! 0x28e70 W_1f3ac.
Proof. vm_refl. Qed.
Lemma D_1f3ac : D! W_1f3ac (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_1f3b0 : bv 32 := 0x01293023.
Lemma F_1f3b0 : F! 0x28e74 W_1f3b0.
Proof. vm_refl. Qed.
Lemma D_1f3b0 : D! W_1f3b0 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_1f3b4 : bv 32 := 0x00040513.
Lemma F_1f3b4 : F! 0x28e78 W_1f3b4.
Proof. vm_refl. Qed.
Lemma D_1f3b4 : D! W_1f3b4 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_1f3b8 : bv 32 := 0x160080ef.
Lemma F_1f3b8 : F! 0x28e7c W_1f3b8.
Proof. vm_refl. Qed.
Lemma D_1f3b8 : D! W_1f3b8 (Jal 1 33120).
Proof. vm_refl. Qed.
Definition W_1f3bc : bv 32 := 0x04054a63.
Lemma F_1f3bc : F! 0x28e80 W_1f3bc.
Proof. vm_refl. Qed.
Lemma D_1f3bc : D! W_1f3bc (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_1f3c0 : bv 32 := 0x00051663.
Lemma F_1f3c0 : F! 0x28e84 W_1f3c0.
Proof. vm_refl. Qed.
Lemma D_1f3c0 : D! W_1f3c0 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_1f3c4 : bv 32 := 0x00100513.
Lemma F_1f3c4 : F! 0x28e88 W_1f3c4.
Proof. vm_refl. Qed.
Lemma D_1f3c4 : D! W_1f3c4 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_1f3c8 : bv 32 := 0x00a48023.
Lemma F_1f3c8 : F! 0x28e8c W_1f3c8.
Proof. vm_refl. Qed.
Lemma D_1f3c8 : D! W_1f3c8 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_1f3cc : bv 32 := 0x00200513.
Lemma F_1f3cc : F! 0x28e90 W_1f3cc.
Proof. vm_refl. Qed.
Lemma D_1f3cc : D! W_1f3cc (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_1f3d0 : bv 32 := 0x0003b597.
Lemma F_1f3d0 : F! 0x28e94 W_1f3d0.
Proof. vm_refl. Qed.
Lemma D_1f3d0 : D! W_1f3d0 (Auipc 11 59).
Proof. vm_refl. Qed.
Definition W_1f3d4 : bv 32 := 0x02a92423.
Lemma F_1f3d4 : F! 0x28e98 W_1f3d4.
Proof. vm_refl. Qed.
Lemma D_1f3d4 : D! W_1f3d4 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_1f3d8 : bv 32 := 0x06000893.
Lemma F_1f3d8 : F! 0x28e9c W_1f3d8.
Proof. vm_refl. Qed.
Lemma D_1f3d8 : D! W_1f3d8 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_1f3dc : bv 32 := 0x35458513.
Lemma F_1f3dc : F! 0x28ea0 W_1f3dc.
Proof. vm_refl. Qed.
Lemma D_1f3dc : D! W_1f3dc (OpImm ALU_ADD 10 11 852).
Proof. vm_refl. Qed.
Definition W_1f3e0 : bv 32 := 0x03848593.
Lemma F_1f3e0 : F! 0x28ea4 W_1f3e0.
Proof. vm_refl. Qed.
Lemma D_1f3e0 : D! W_1f3e0 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_1f3e4 : bv 32 := 0x00000073.
Lemma F_1f3e4 : F! 0x28ea8 W_1f3e4.
Proof. vm_refl. Qed.
Lemma E_1f3e4 : is_ecall W_1f3e4 = true.
Proof. reflexivity. Qed.
Definition W_1f3e8 : bv 32 := 0x07890613.
Lemma F_1f3e8 : F! 0x28eac W_1f3e8.
Proof. vm_refl. Qed.
Lemma D_1f3e8 : D! W_1f3e8 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_1f3ec : bv 32 := 0x02a92023.
Lemma F_1f3ec : F! 0x28eb0 W_1f3ec.
Proof. vm_refl. Qed.
Lemma D_1f3ec : D! W_1f3ec (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_1f3f0 : bv 32 := 0x08b93c23.
Lemma F_1f3f0 : F! 0x28eb4 W_1f3f0.
Proof. vm_refl. Qed.
Lemma D_1f3f0 : D! W_1f3f0 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_1f3f4 : bv 32 := 0x06c93c23.
Lemma F_1f3f4 : F! 0x28eb8 W_1f3f4.
Proof. vm_refl. Qed.
Lemma D_1f3f4 : D! W_1f3f4 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_1f3f8 : bv 32 := 0x0003b517.
Lemma F_1f3f8 : F! 0x28ebc W_1f3f8.
Proof. vm_refl. Qed.
Lemma D_1f3f8 : D! W_1f3f8 (Auipc 10 59).
Proof. vm_refl. Qed.
Definition W_1f3fc : bv 32 := 0x59c53503.
Lemma F_1f3fc : F! 0x28ec0 W_1f3fc.
Proof. vm_refl. Qed.
Lemma D_1f3fc : D! W_1f3fc (Load SZ8 true 10 10 1436).
Proof. vm_refl. Qed.
Definition W_1f400 : bv 32 := 0x01293423.
Lemma F_1f400 : F! 0x28ec4 W_1f400.
Proof. vm_refl. Qed.
Lemma D_1f400 : D! W_1f400 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_1f404 : bv 32 := 0x01293823.
Lemma F_1f404 : F! 0x28ec8 W_1f404.
Proof. vm_refl. Qed.
Lemma D_1f404 : D! W_1f404 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_1f408 : bv 32 := 0x00a93c23.
Lemma F_1f408 : F! 0x28ecc W_1f408.
Proof. vm_refl. Qed.
Lemma D_1f408 : D! W_1f408 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_1f40c : bv 32 := 0x0080006f.
Lemma F_1f40c : F! 0x28ed0 W_1f40c.
Proof. vm_refl. Qed.
Lemma D_1f40c : D! W_1f40c (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_1f414 : bv 32 := 0x03813083.
Lemma F_1f414 : F! 0x28ed8 W_1f414.
Proof. vm_refl. Qed.
Lemma D_1f414 : D! W_1f414 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_1f418 : bv 32 := 0x03013403.
Lemma F_1f418 : F! 0x28edc W_1f418.
Proof. vm_refl. Qed.
Lemma D_1f418 : D! W_1f418 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_1f41c : bv 32 := 0x02813483.
Lemma F_1f41c : F! 0x28ee0 W_1f41c.
Proof. vm_refl. Qed.
Lemma D_1f41c : D! W_1f41c (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_1f420 : bv 32 := 0x02013903.
Lemma F_1f420 : F! 0x28ee4 W_1f420.
Proof. vm_refl. Qed.
Lemma D_1f420 : D! W_1f420 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_1f424 : bv 32 := 0x01813983.
Lemma F_1f424 : F! 0x28ee8 W_1f424.
Proof. vm_refl. Qed.
Lemma D_1f424 : D! W_1f424 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_1f428 : bv 32 := 0x01013a03.
Lemma F_1f428 : F! 0x28eec W_1f428.
Proof. vm_refl. Qed.
Lemma D_1f428 : D! W_1f428 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_1f42c : bv 32 := 0x00813a83.
Lemma F_1f42c : F! 0x28ef0 W_1f42c.
Proof. vm_refl. Qed.
Lemma D_1f42c : D! W_1f42c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_1f430 : bv 32 := 0x04010113.
Lemma F_1f430 : F! 0x28ef4 W_1f430.
Proof. vm_refl. Qed.
Lemma D_1f430 : D! W_1f430 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_1f434 : bv 32 := 0x00008067.
Lemma F_1f434 : F! 0x28ef8 W_1f434.
Proof. vm_refl. Qed.
Lemma D_1f434 : D! W_1f434 (Jalr 0 1 0).
Proof. vm_refl. Qed.
