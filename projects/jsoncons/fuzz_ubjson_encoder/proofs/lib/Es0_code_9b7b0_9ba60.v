(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) =>
(lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Local Notation "'F!' a w" := (fetch_word Plain.M.loaded_segments (a : word) = Some w) (at level 200, a at level 0, w at level 0, only parsing).
Local Notation "'D!' w i" := (decode_any w = Some (i, 4%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Local Notation "'D2!' w i" := (decode_any w = Some (i, 2%Z)) (at level 200, w at level 0, i at level 0, only parsing).
Definition W_9b7b0 : bv 32 := 0xfc010113.
Lemma F_9b7b0 : F! 0x9b7b0 W_9b7b0.
Proof. vm_refl. Qed.
Lemma D_9b7b0 : D! W_9b7b0 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_9b7b4 : bv 32 := 0x02113c23.
Lemma F_9b7b4 : F! 0x9b7b4 W_9b7b4.
Proof. vm_refl. Qed.
Lemma D_9b7b4 : D! W_9b7b4 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_9b7b8 : bv 32 := 0x02813823.
Lemma F_9b7b8 : F! 0x9b7b8 W_9b7b8.
Proof. vm_refl. Qed.
Lemma D_9b7b8 : D! W_9b7b8 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_9b7bc : bv 32 := 0x02913423.
Lemma F_9b7bc : F! 0x9b7bc W_9b7bc.
Proof. vm_refl. Qed.
Lemma D_9b7bc : D! W_9b7bc (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_9b7c0 : bv 32 := 0x03213023.
Lemma F_9b7c0 : F! 0x9b7c0 W_9b7c0.
Proof. vm_refl. Qed.
Lemma D_9b7c0 : D! W_9b7c0 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_9b7c4 : bv 32 := 0x01313c23.
Lemma F_9b7c4 : F! 0x9b7c4 W_9b7c4.
Proof. vm_refl. Qed.
Lemma D_9b7c4 : D! W_9b7c4 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_9b7c8 : bv 32 := 0x01413823.
Lemma F_9b7c8 : F! 0x9b7c8 W_9b7c8.
Proof. vm_refl. Qed.
Lemma D_9b7c8 : D! W_9b7c8 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_9b7cc : bv 32 := 0x01513423.
Lemma F_9b7cc : F! 0x9b7cc W_9b7cc.
Proof. vm_refl. Qed.
Lemma D_9b7cc : D! W_9b7cc (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_9b7d0 : bv 32 := 0x02853683.
Lemma F_9b7d0 : F! 0x9b7d0 W_9b7d0.
Proof. vm_refl. Qed.
Lemma D_9b7d0 : D! W_9b7d0 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_9b7d4 : bv 32 := 0x00050597.
Lemma F_9b7d4 : F! 0x9b7d4 W_9b7d4.
Proof. vm_refl. Qed.
Lemma D_9b7d4 : D! W_9b7d4 (Auipc 11 80).
Proof. vm_refl. Qed.
Definition W_9b7d8 : bv 32 := 0x87458593.
Lemma F_9b7d8 : F! 0x9b7d8 W_9b7d8.
Proof. vm_refl. Qed.
Lemma D_9b7d8 : D! W_9b7d8 (OpImm ALU_ADD 11 11 2164).
Proof. vm_refl. Qed.
Definition W_9b7dc : bv 32 := 0x00050617.
Lemma F_9b7dc : F! 0x9b7dc W_9b7dc.
Proof. vm_refl. Qed.
Lemma D_9b7dc : D! W_9b7dc (Auipc 12 80).
Proof. vm_refl. Qed.
Definition W_9b7e0 : bv 32 := 0xaf460493.
Lemma F_9b7e0 : F! 0x9b7e0 W_9b7e0.
Proof. vm_refl. Qed.
Lemma D_9b7e0 : D! W_9b7e0 (OpImm ALU_ADD 9 12 2804).
Proof. vm_refl. Qed.
Definition W_9b7e4 : bv 32 := 0x0c068e63.
Lemma F_9b7e4 : F! 0x9b7e4 W_9b7e4.
Proof. vm_refl. Qed.
Lemma D_9b7e4 : D! W_9b7e4 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_9b7e8 : bv 32 := 0x00000613.
Lemma F_9b7e8 : F! 0x9b7e8 W_9b7e8.
Proof. vm_refl. Qed.
Lemma D_9b7e8 : D! W_9b7e8 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_9b7ec : bv 32 := 0x00000893.
Lemma F_9b7ec : F! 0x9b7ec W_9b7ec.
Proof. vm_refl. Qed.
Lemma D_9b7ec : D! W_9b7ec (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_9b7f0 : bv 32 := 0x0001e717.
Lemma F_9b7f0 : F! 0x9b7f0 W_9b7f0.
Proof. vm_refl. Qed.
Lemma D_9b7f0 : D! W_9b7f0 (Auipc 14 30).
Proof. vm_refl. Qed.
Definition W_9b7f4 : bv 32 := 0x01853783.
Lemma F_9b7f4 : F! 0x9b7f4 W_9b7f4.
Proof. vm_refl. Qed.
Lemma D_9b7f4 : D! W_9b7f4 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_9b7f8 : bv 32 := 0x02053503.
Lemma F_9b7f8 : F! 0x9b7f8 W_9b7f8.
Proof. vm_refl. Qed.
Lemma D_9b7f8 : D! W_9b7f8 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_9b7fc : bv 32 := 0x00600813.
Lemma F_9b7fc : F! 0x9b7fc W_9b7fc.
Proof. vm_refl. Qed.
Lemma D_9b7fc : D! W_9b7fc (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_9b800 : bv 32 := 0x0001d297.
Lemma F_9b800 : F! 0x9b800 W_9b800.
Proof. vm_refl. Qed.
Lemma D_9b800 : D! W_9b800 (Auipc 5 29).
Proof. vm_refl. Qed.
Definition W_9b804 : bv 32 := 0xda876f03.
Lemma F_9b804 : F! 0x9b804 W_9b804.
Proof. vm_refl. Qed.
Lemma D_9b804 : D! W_9b804 (Load SZ4 false 30 14 3496).
Proof. vm_refl. Qed.
Definition W_9b808 : bv 32 := 0x9102b283.
Lemma F_9b808 : F! 0x9b808 W_9b808.
Proof. vm_refl. Qed.
Lemma D_9b808 : D! W_9b808 (Load SZ8 true 5 5 2320).
Proof. vm_refl. Qed.
Definition W_9b80c : bv 32 := 0x00200313.
Lemma F_9b80c : F! 0x9b80c W_9b80c.
Proof. vm_refl. Qed.
Lemma D_9b80c : D! W_9b80c (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_9b810 : bv 32 := 0x00700393.
Lemma F_9b810 : F! 0x9b810 W_9b810.
Proof. vm_refl. Qed.
Lemma D_9b810 : D! W_9b810 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_9b814 : bv 32 := 0x6474ee37.
Lemma F_9b814 : F! 0x9b814 W_9b814.
Proof. vm_refl. Qed.
Lemma D_9b814 : D! W_9b814 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_9b818 : bv 32 := 0x551e0e1b.
Lemma F_9b818 : F! 0x9b818 W_9b818.
Proof. vm_refl. Qed.
Lemma D_9b818 : D! W_9b818 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_9b81c : bv 32 := 0x00078e93.
Lemma F_9b81c : F! 0x9b81c W_9b81c.
Proof. vm_refl. Qed.
Lemma D_9b81c : D! W_9b81c (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_9b820 : bv 32 := 0x0180006f.
Lemma F_9b820 : F! 0x9b820 W_9b820.
Proof. vm_refl. Qed.
Lemma D_9b820 : D! W_9b820 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_9b824 : bv 32 := 0x010eb603.
Lemma F_9b824 : F! 0x9b824 W_9b824.
Proof. vm_refl. Qed.
Lemma D_9b824 : D! W_9b824 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_9b828 : bv 32 := 0x40c78633.
Lemma F_9b828 : F! 0x9b828 W_9b828.
Proof. vm_refl. Qed.
Lemma D_9b828 : D! W_9b828 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_9b82c : bv 32 := 0xfff68693.
Lemma F_9b82c : F! 0x9b82c W_9b82c.
Proof. vm_refl. Qed.
Lemma D_9b82c : D! W_9b82c (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_9b830 : bv 32 := 0x00ae8eb3.
Lemma F_9b830 : F! 0x9b830 W_9b830.
Proof. vm_refl. Qed.
Lemma D_9b830 : D! W_9b830 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_9b834 : bv 32 := 0x04068a63.
Lemma F_9b834 : F! 0x9b834 W_9b834.
Proof. vm_refl. Qed.
Lemma D_9b834 : D! W_9b834 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_9b838 : bv 32 := 0x000ea403.
Lemma F_9b838 : F! 0x9b838 W_9b838.
Proof. vm_refl. Qed.
Lemma D_9b838 : D! W_9b838 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_9b83c : bv 32 := 0xff0404e3.
Lemma F_9b83c : F! 0x9b83c W_9b83c.
Proof. vm_refl. Qed.
Lemma D_9b83c : D! W_9b83c (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_9b840 : bv 32 := 0x00028a63.
Lemma F_9b840 : F! 0x9b840 W_9b840.
Proof. vm_refl. Qed.
Lemma D_9b840 : D! W_9b840 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_9b854 : bv 32 := 0x000e8f93.
Lemma F_9b854 : F! 0x9b854 W_9b854.
Proof. vm_refl. Qed.
Lemma D_9b854 : D! W_9b854 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_9b858 : bv 32 := 0x00740463.
Lemma F_9b858 : F! 0x9b858 W_9b858.
Proof. vm_refl. Qed.
Lemma D_9b858 : D! W_9b858 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_9b85c : bv 32 := 0x00088f93.
Lemma F_9b85c : F! 0x9b85c W_9b85c.
Proof. vm_refl. Qed.
Lemma D_9b85c : D! W_9b85c (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_9b860 : bv 32 := 0x03c41063.
Lemma F_9b860 : F! 0x9b860 W_9b860.
Proof. vm_refl. Qed.
Lemma D_9b860 : D! W_9b860 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_9b864 : bv 32 := 0x028eb883.
Lemma F_9b864 : F! 0x9b864 W_9b864.
Proof. vm_refl. Qed.
Lemma D_9b864 : D! W_9b864 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_9b868 : bv 32 := 0x011f7c63.
Lemma F_9b868 : F! 0x9b868 W_9b868.
Proof. vm_refl. Qed.
Lemma D_9b868 : D! W_9b868 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_9b880 : bv 32 := 0x000f8893.
Lemma F_9b880 : F! 0x9b880 W_9b880.
Proof. vm_refl. Qed.
Lemma D_9b880 : D! W_9b880 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_9b884 : bv 32 := 0xfa9ff06f.
Lemma F_9b884 : F! 0x9b884 W_9b884.
Proof. vm_refl. Qed.
Lemma D_9b884 : D! W_9b884 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_9b888 : bv 32 := 0x02088c63.
Lemma F_9b888 : F! 0x9b888 W_9b888.
Proof. vm_refl. Qed.
Lemma D_9b888 : D! W_9b888 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_9b8c0 : bv 32 := 0x0105b603.
Lemma F_9b8c0 : F! 0x9b8c0 W_9b8c0.
Proof. vm_refl. Qed.
Lemma D_9b8c0 : D! W_9b8c0 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_9b8c4 : bv 32 := 0x0205b683.
Lemma F_9b8c4 : F! 0x9b8c4 W_9b8c4.
Proof. vm_refl. Qed.
Lemma D_9b8c4 : D! W_9b8c4 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_9b8c8 : bv 32 := 0x0285b503.
Lemma F_9b8c8 : F! 0x9b8c8 W_9b8c8.
Proof. vm_refl. Qed.
Lemma D_9b8c8 : D! W_9b8c8 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_9b8cc : bv 32 := 0x00c68733.
Lemma F_9b8cc : F! 0x9b8cc W_9b8cc.
Proof. vm_refl. Qed.
Lemma D_9b8cc : D! W_9b8cc (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_9b8d0 : bv 32 := 0xfff50793.
Lemma F_9b8d0 : F! 0x9b8d0 W_9b8d0.
Proof. vm_refl. Qed.
Lemma D_9b8d0 : D! W_9b8d0 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_9b8d4 : bv 32 := 0x40e00733.
Lemma F_9b8d4 : F! 0x9b8d4 W_9b8d4.
Proof. vm_refl. Qed.
Lemma D_9b8d4 : D! W_9b8d4 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_9b8d8 : bv 32 := 0x00c7f633.
Lemma F_9b8d8 : F! 0x9b8d8 W_9b8d8.
Proof. vm_refl. Qed.
Lemma D_9b8d8 : D! W_9b8d8 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_9b8dc : bv 32 := 0x00e7f733.
Lemma F_9b8dc : F! 0x9b8dc W_9b8dc.
Proof. vm_refl. Qed.
Lemma D_9b8dc : D! W_9b8dc (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_9b8e0 : bv 32 := 0x00700793.
Lemma F_9b8e0 : F! 0x9b8e0 W_9b8e0.
Proof. vm_refl. Qed.
Lemma D_9b8e0 : D! W_9b8e0 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_9b8e4 : bv 32 := 0x00d706b3.
Lemma F_9b8e4 : F! 0x9b8e4 W_9b8e4.
Proof. vm_refl. Qed.
Lemma D_9b8e4 : D! W_9b8e4 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_9b8e8 : bv 32 := 0x02d5b023.
Lemma F_9b8e8 : F! 0x9b8e8 W_9b8e8.
Proof. vm_refl. Qed.
Lemma D_9b8e8 : D! W_9b8e8 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_9b8ec : bv 32 := 0x02c5b823.
Lemma F_9b8ec : F! 0x9b8ec W_9b8ec.
Proof. vm_refl. Qed.
Lemma D_9b8ec : D! W_9b8ec (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_9b8f0 : bv 32 := 0x00a7e663.
Lemma F_9b8f0 : F! 0x9b8f0 W_9b8f0.
Proof. vm_refl. Qed.
Lemma D_9b8f0 : D! W_9b8f0 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_9b8f4 : bv 32 := 0x00800513.
Lemma F_9b8f4 : F! 0x9b8f4 W_9b8f4.
Proof. vm_refl. Qed.
Lemma D_9b8f4 : D! W_9b8f4 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_9b8f8 : bv 32 := 0x02a5b423.
Lemma F_9b8f8 : F! 0x9b8f8 W_9b8f8.
Proof. vm_refl. Qed.
Lemma D_9b8f8 : D! W_9b8f8 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_9b8fc : bv 32 := 0x00d60633.
Lemma F_9b8fc : F! 0x9b8fc W_9b8fc.
Proof. vm_refl. Qed.
Lemma D_9b8fc : D! W_9b8fc (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_9b900 : bv 32 := 0x000205b7.
Lemma F_9b900 : F! 0x9b900 W_9b900.
Proof. vm_refl. Qed.
Lemma D_9b900 : D! W_9b900 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_9b904 : bv 32 := 0x00a60633.
Lemma F_9b904 : F! 0x9b904 W_9b904.
Proof. vm_refl. Qed.
Lemma D_9b904 : D! W_9b904 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_9b908 : bv 32 := 0x0d15869b.
Lemma F_9b908 : F! 0x9b908 W_9b908.
Proof. vm_refl. Qed.
Lemma D_9b908 : D! W_9b908 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_9b90c : bv 32 := 0x0df60593.
Lemma F_9b90c : F! 0x9b90c W_9b90c.
Proof. vm_refl. Qed.
Lemma D_9b90c : D! W_9b90c (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_9b910 : bv 32 := 0xff85f593.
Lemma F_9b910 : F! 0x9b910 W_9b910.
Proof. vm_refl. Qed.
Lemma D_9b910 : D! W_9b910 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_9b914 : bv 32 := 0x00b4bc23.
Lemma F_9b914 : F! 0x9b914 W_9b914.
Proof. vm_refl. Qed.
Lemma D_9b914 : D! W_9b914 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_9b918 : bv 32 := 0x02a4b023.
Lemma F_9b918 : F! 0x9b918 W_9b918.
Proof. vm_refl. Qed.
Lemma D_9b918 : D! W_9b918 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_9b91c : bv 32 := 0x02d5ea63.
Lemma F_9b91c : F! 0x9b91c W_9b91c.
Proof. vm_refl. Qed.
Lemma D_9b91c : D! W_9b91c (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_9b950 : bv 32 := 0x0002f697.
Lemma F_9b950 : F! 0x9b950 W_9b950.
Proof. vm_refl. Qed.
Lemma D_9b950 : D! W_9b950 (Auipc 13 47).
Proof. vm_refl. Qed.
Definition W_9b954 : bv 32 := 0x0104b983.
Lemma F_9b954 : F! 0x9b954 W_9b954.
Proof. vm_refl. Qed.
Lemma D_9b954 : D! W_9b954 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_9b958 : bv 32 := 0x0284b603.
Lemma F_9b958 : F! 0x9b958 W_9b958.
Proof. vm_refl. Qed.
Lemma D_9b958 : D! W_9b958 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_9b95c : bv 32 := 0xfff50713.
Lemma F_9b95c : F! 0x9b95c W_9b95c.
Proof. vm_refl. Qed.
Lemma D_9b95c : D! W_9b95c (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_9b960 : bv 32 := 0xf3800793.
Lemma F_9b960 : F! 0x9b960 W_9b960.
Proof. vm_refl. Qed.
Lemma D_9b960 : D! W_9b960 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_9b964 : bv 32 := 0x62868513.
Lemma F_9b964 : F! 0x9b964 W_9b964.
Proof. vm_refl. Qed.
Lemma D_9b964 : D! W_9b964 (OpImm ALU_ADD 10 13 1576).
Proof. vm_refl. Qed.
Definition W_9b968 : bv 32 := 0x40a787b3.
Lemma F_9b968 : F! 0x9b968 W_9b968.
Proof. vm_refl. Qed.
Lemma D_9b968 : D! W_9b968 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_9b96c : bv 32 := 0x00f77733.
Lemma F_9b96c : F! 0x9b96c W_9b96c.
Proof. vm_refl. Qed.
Lemma D_9b96c : D! W_9b96c (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_9b970 : bv 32 := 0xfff64693.
Lemma F_9b970 : F! 0x9b970 W_9b970.
Proof. vm_refl. Qed.
Lemma D_9b970 : D! W_9b970 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_9b974 : bv 32 := 0x00e50933.
Lemma F_9b974 : F! 0x9b974 W_9b974.
Proof. vm_refl. Qed.
Lemma D_9b974 : D! W_9b974 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_9b978 : bv 32 := 0x00369693.
Lemma F_9b978 : F! 0x9b978 W_9b978.
Proof. vm_refl. Qed.
Lemma D_9b978 : D! W_9b978 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_9b97c : bv 32 := 0x00d506b3.
Lemma F_9b97c : F! 0x9b97c W_9b97c.
Proof. vm_refl. Qed.
Lemma D_9b97c : D! W_9b97c (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_9b980 : bv 32 := 0x00b68a33.
Lemma F_9b980 : F! 0x9b980 W_9b980.
Proof. vm_refl. Qed.
Lemma D_9b980 : D! W_9b980 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_9b984 : bv 32 := 0x0c890413.
Lemma F_9b984 : F! 0x9b984 W_9b984.
Proof. vm_refl. Qed.
Lemma D_9b984 : D! W_9b984 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_9b988 : bv 32 := 0x04098463.
Lemma F_9b988 : F! 0x9b988 W_9b988.
Proof. vm_refl. Qed.
Lemma D_9b988 : D! W_9b988 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_9b9d0 : bv 32 := 0x00ca3023.
Lemma F_9b9d0 : F! 0x9b9d0 W_9b9d0.
Proof. vm_refl. Qed.
Lemma D_9b9d0 : D! W_9b9d0 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_9b9d4 : bv 32 := 0x0d493023.
Lemma F_9b9d4 : F! 0x9b9d4 W_9b9d4.
Proof. vm_refl. Qed.
Lemma D_9b9d4 : D! W_9b9d4 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_9b9d8 : bv 32 := 0x01293023.
Lemma F_9b9d8 : F! 0x9b9d8 W_9b9d8.
Proof. vm_refl. Qed.
Lemma D_9b9d8 : D! W_9b9d8 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_9b9dc : bv 32 := 0x00040513.
Lemma F_9b9dc : F! 0x9b9dc W_9b9dc.
Proof. vm_refl. Qed.
Lemma D_9b9dc : D! W_9b9dc (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_9b9e0 : bv 32 := 0x16c130ef.
Lemma F_9b9e0 : F! 0x9b9e0 W_9b9e0.
Proof. vm_refl. Qed.
Lemma D_9b9e0 : D! W_9b9e0 (Jal 1 78188).
Proof. vm_refl. Qed.
Definition W_9b9e4 : bv 32 := 0x04054a63.
Lemma F_9b9e4 : F! 0x9b9e4 W_9b9e4.
Proof. vm_refl. Qed.
Lemma D_9b9e4 : D! W_9b9e4 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_9b9e8 : bv 32 := 0x00051663.
Lemma F_9b9e8 : F! 0x9b9e8 W_9b9e8.
Proof. vm_refl. Qed.
Lemma D_9b9e8 : D! W_9b9e8 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_9b9ec : bv 32 := 0x00100513.
Lemma F_9b9ec : F! 0x9b9ec W_9b9ec.
Proof. vm_refl. Qed.
Lemma D_9b9ec : D! W_9b9ec (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_9b9f0 : bv 32 := 0x00a48023.
Lemma F_9b9f0 : F! 0x9b9f0 W_9b9f0.
Proof. vm_refl. Qed.
Lemma D_9b9f0 : D! W_9b9f0 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_9b9f4 : bv 32 := 0x00200513.
Lemma F_9b9f4 : F! 0x9b9f4 W_9b9f4.
Proof. vm_refl. Qed.
Lemma D_9b9f4 : D! W_9b9f4 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_9b9f8 : bv 32 := 0x0004f597.
Lemma F_9b9f8 : F! 0x9b9f8 W_9b9f8.
Proof. vm_refl. Qed.
Lemma D_9b9f8 : D! W_9b9f8 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_9b9fc : bv 32 := 0x02a92423.
Lemma F_9b9fc : F! 0x9b9fc W_9b9fc.
Proof. vm_refl. Qed.
Lemma D_9b9fc : D! W_9b9fc (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_9ba00 : bv 32 := 0x06000893.
Lemma F_9ba00 : F! 0x9ba00 W_9ba00.
Proof. vm_refl. Qed.
Lemma D_9ba00 : D! W_9ba00 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_9ba04 : bv 32 := 0x65058513.
Lemma F_9ba04 : F! 0x9ba04 W_9ba04.
Proof. vm_refl. Qed.
Lemma D_9ba04 : D! W_9ba04 (OpImm ALU_ADD 10 11 1616).
Proof. vm_refl. Qed.
Definition W_9ba08 : bv 32 := 0x03848593.
Lemma F_9ba08 : F! 0x9ba08 W_9ba08.
Proof. vm_refl. Qed.
Lemma D_9ba08 : D! W_9ba08 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_9ba0c : bv 32 := 0x00000073.
Lemma F_9ba0c : F! 0x9ba0c W_9ba0c.
Proof. vm_refl. Qed.
Lemma E_9ba0c : is_ecall W_9ba0c = true.
Proof. reflexivity. Qed.
Definition W_9ba10 : bv 32 := 0x07890613.
Lemma F_9ba10 : F! 0x9ba10 W_9ba10.
Proof. vm_refl. Qed.
Lemma D_9ba10 : D! W_9ba10 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_9ba14 : bv 32 := 0x02a92023.
Lemma F_9ba14 : F! 0x9ba14 W_9ba14.
Proof. vm_refl. Qed.
Lemma D_9ba14 : D! W_9ba14 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_9ba18 : bv 32 := 0x08b93c23.
Lemma F_9ba18 : F! 0x9ba18 W_9ba18.
Proof. vm_refl. Qed.
Lemma D_9ba18 : D! W_9ba18 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_9ba1c : bv 32 := 0x06c93c23.
Lemma F_9ba1c : F! 0x9ba1c W_9ba1c.
Proof. vm_refl. Qed.
Lemma D_9ba1c : D! W_9ba1c (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_9ba20 : bv 32 := 0x00050517.
Lemma F_9ba20 : F! 0x9ba20 W_9ba20.
Proof. vm_refl. Qed.
Lemma D_9ba20 : D! W_9ba20 (Auipc 10 80).
Proof. vm_refl. Qed.
Definition W_9ba24 : bv 32 := 0x89853503.
Lemma F_9ba24 : F! 0x9ba24 W_9ba24.
Proof. vm_refl. Qed.
Lemma D_9ba24 : D! W_9ba24 (Load SZ8 true 10 10 2200).
Proof. vm_refl. Qed.
Definition W_9ba28 : bv 32 := 0x01293423.
Lemma F_9ba28 : F! 0x9ba28 W_9ba28.
Proof. vm_refl. Qed.
Lemma D_9ba28 : D! W_9ba28 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_9ba2c : bv 32 := 0x01293823.
Lemma F_9ba2c : F! 0x9ba2c W_9ba2c.
Proof. vm_refl. Qed.
Lemma D_9ba2c : D! W_9ba2c (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_9ba30 : bv 32 := 0x00a93c23.
Lemma F_9ba30 : F! 0x9ba30 W_9ba30.
Proof. vm_refl. Qed.
Lemma D_9ba30 : D! W_9ba30 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_9ba34 : bv 32 := 0x0080006f.
Lemma F_9ba34 : F! 0x9ba34 W_9ba34.
Proof. vm_refl. Qed.
Lemma D_9ba34 : D! W_9ba34 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_9ba3c : bv 32 := 0x03813083.
Lemma F_9ba3c : F! 0x9ba3c W_9ba3c.
Proof. vm_refl. Qed.
Lemma D_9ba3c : D! W_9ba3c (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_9ba40 : bv 32 := 0x03013403.
Lemma F_9ba40 : F! 0x9ba40 W_9ba40.
Proof. vm_refl. Qed.
Lemma D_9ba40 : D! W_9ba40 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_9ba44 : bv 32 := 0x02813483.
Lemma F_9ba44 : F! 0x9ba44 W_9ba44.
Proof. vm_refl. Qed.
Lemma D_9ba44 : D! W_9ba44 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_9ba48 : bv 32 := 0x02013903.
Lemma F_9ba48 : F! 0x9ba48 W_9ba48.
Proof. vm_refl. Qed.
Lemma D_9ba48 : D! W_9ba48 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_9ba4c : bv 32 := 0x01813983.
Lemma F_9ba4c : F! 0x9ba4c W_9ba4c.
Proof. vm_refl. Qed.
Lemma D_9ba4c : D! W_9ba4c (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_9ba50 : bv 32 := 0x01013a03.
Lemma F_9ba50 : F! 0x9ba50 W_9ba50.
Proof. vm_refl. Qed.
Lemma D_9ba50 : D! W_9ba50 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_9ba54 : bv 32 := 0x00813a83.
Lemma F_9ba54 : F! 0x9ba54 W_9ba54.
Proof. vm_refl. Qed.
Lemma D_9ba54 : D! W_9ba54 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_9ba58 : bv 32 := 0x04010113.
Lemma F_9ba58 : F! 0x9ba58 W_9ba58.
Proof. vm_refl. Qed.
Lemma D_9ba58 : D! W_9ba58 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_9ba5c : bv 32 := 0x00008067.
Lemma F_9ba5c : F! 0x9ba5c W_9ba5c.
Proof. vm_refl. Qed.
Lemma D_9ba5c : D! W_9ba5c (Jalr 0 1 0).
Proof. vm_refl. Qed.
