(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
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
Definition W_a9980 : bv 32 := 0xfc010113.
Lemma F_a9980 : F! 0xa9980 W_a9980.
Proof. vm_refl. Qed.
Lemma D_a9980 : D! W_a9980 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_a9984 : bv 32 := 0x02113c23.
Lemma F_a9984 : F! 0xa9984 W_a9984.
Proof. vm_refl. Qed.
Lemma D_a9984 : D! W_a9984 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_a9988 : bv 32 := 0x02813823.
Lemma F_a9988 : F! 0xa9988 W_a9988.
Proof. vm_refl. Qed.
Lemma D_a9988 : D! W_a9988 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_a998c : bv 32 := 0x02913423.
Lemma F_a998c : F! 0xa998c W_a998c.
Proof. vm_refl. Qed.
Lemma D_a998c : D! W_a998c (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_a9990 : bv 32 := 0x03213023.
Lemma F_a9990 : F! 0xa9990 W_a9990.
Proof. vm_refl. Qed.
Lemma D_a9990 : D! W_a9990 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_a9994 : bv 32 := 0x01313c23.
Lemma F_a9994 : F! 0xa9994 W_a9994.
Proof. vm_refl. Qed.
Lemma D_a9994 : D! W_a9994 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_a9998 : bv 32 := 0x01413823.
Lemma F_a9998 : F! 0xa9998 W_a9998.
Proof. vm_refl. Qed.
Lemma D_a9998 : D! W_a9998 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_a999c : bv 32 := 0x01513423.
Lemma F_a999c : F! 0xa999c W_a999c.
Proof. vm_refl. Qed.
Lemma D_a999c : D! W_a999c (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_a99a0 : bv 32 := 0x02853683.
Lemma F_a99a0 : F! 0xa99a0 W_a99a0.
Proof. vm_refl. Qed.
Lemma D_a99a0 : D! W_a99a0 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_a99a4 : bv 32 := 0x00050597.
Lemma F_a99a4 : F! 0xa99a4 W_a99a4.
Proof. vm_refl. Qed.
Lemma D_a99a4 : D! W_a99a4 (Auipc 11 80).
Proof. vm_refl. Qed.
Definition W_a99a8 : bv 32 := 0xc8458593.
Lemma F_a99a8 : F! 0xa99a8 W_a99a8.
Proof. vm_refl. Qed.
Lemma D_a99a8 : D! W_a99a8 (OpImm ALU_ADD 11 11 3204).
Proof. vm_refl. Qed.
Definition W_a99ac : bv 32 := 0x00050617.
Lemma F_a99ac : F! 0xa99ac W_a99ac.
Proof. vm_refl. Qed.
Lemma D_a99ac : D! W_a99ac (Auipc 12 80).
Proof. vm_refl. Qed.
Definition W_a99b0 : bv 32 := 0xf0460493.
Lemma F_a99b0 : F! 0xa99b0 W_a99b0.
Proof. vm_refl. Qed.
Lemma D_a99b0 : D! W_a99b0 (OpImm ALU_ADD 9 12 3844).
Proof. vm_refl. Qed.
Definition W_a99b4 : bv 32 := 0x0c068e63.
Lemma F_a99b4 : F! 0xa99b4 W_a99b4.
Proof. vm_refl. Qed.
Lemma D_a99b4 : D! W_a99b4 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_a99b8 : bv 32 := 0x00000613.
Lemma F_a99b8 : F! 0xa99b8 W_a99b8.
Proof. vm_refl. Qed.
Lemma D_a99b8 : D! W_a99b8 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_a99bc : bv 32 := 0x00000893.
Lemma F_a99bc : F! 0xa99bc W_a99bc.
Proof. vm_refl. Qed.
Lemma D_a99bc : D! W_a99bc (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_a99c0 : bv 32 := 0x0001e717.
Lemma F_a99c0 : F! 0xa99c0 W_a99c0.
Proof. vm_refl. Qed.
Lemma D_a99c0 : D! W_a99c0 (Auipc 14 30).
Proof. vm_refl. Qed.
Definition W_a99c4 : bv 32 := 0x01853783.
Lemma F_a99c4 : F! 0xa99c4 W_a99c4.
Proof. vm_refl. Qed.
Lemma D_a99c4 : D! W_a99c4 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_a99c8 : bv 32 := 0x02053503.
Lemma F_a99c8 : F! 0xa99c8 W_a99c8.
Proof. vm_refl. Qed.
Lemma D_a99c8 : D! W_a99c8 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_a99cc : bv 32 := 0x00600813.
Lemma F_a99cc : F! 0xa99cc W_a99cc.
Proof. vm_refl. Qed.
Lemma D_a99cc : D! W_a99cc (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_a99d0 : bv 32 := 0x0001d297.
Lemma F_a99d0 : F! 0xa99d0 W_a99d0.
Proof. vm_refl. Qed.
Lemma D_a99d0 : D! W_a99d0 (Auipc 5 29).
Proof. vm_refl. Qed.
Definition W_a99d4 : bv 32 := 0x16876f03.
Lemma F_a99d4 : F! 0xa99d4 W_a99d4.
Proof. vm_refl. Qed.
Lemma D_a99d4 : D! W_a99d4 (Load SZ4 false 30 14 360).
Proof. vm_refl. Qed.
Definition W_a99d8 : bv 32 := 0xca82b283.
Lemma F_a99d8 : F! 0xa99d8 W_a99d8.
Proof. vm_refl. Qed.
Lemma D_a99d8 : D! W_a99d8 (Load SZ8 true 5 5 3240).
Proof. vm_refl. Qed.
Definition W_a99dc : bv 32 := 0x00200313.
Lemma F_a99dc : F! 0xa99dc W_a99dc.
Proof. vm_refl. Qed.
Lemma D_a99dc : D! W_a99dc (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_a99e0 : bv 32 := 0x00700393.
Lemma F_a99e0 : F! 0xa99e0 W_a99e0.
Proof. vm_refl. Qed.
Lemma D_a99e0 : D! W_a99e0 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_a99e4 : bv 32 := 0x6474ee37.
Lemma F_a99e4 : F! 0xa99e4 W_a99e4.
Proof. vm_refl. Qed.
Lemma D_a99e4 : D! W_a99e4 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_a99e8 : bv 32 := 0x551e0e1b.
Lemma F_a99e8 : F! 0xa99e8 W_a99e8.
Proof. vm_refl. Qed.
Lemma D_a99e8 : D! W_a99e8 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_a99ec : bv 32 := 0x00078e93.
Lemma F_a99ec : F! 0xa99ec W_a99ec.
Proof. vm_refl. Qed.
Lemma D_a99ec : D! W_a99ec (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_a99f0 : bv 32 := 0x0180006f.
Lemma F_a99f0 : F! 0xa99f0 W_a99f0.
Proof. vm_refl. Qed.
Lemma D_a99f0 : D! W_a99f0 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_a99f4 : bv 32 := 0x010eb603.
Lemma F_a99f4 : F! 0xa99f4 W_a99f4.
Proof. vm_refl. Qed.
Lemma D_a99f4 : D! W_a99f4 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_a99f8 : bv 32 := 0x40c78633.
Lemma F_a99f8 : F! 0xa99f8 W_a99f8.
Proof. vm_refl. Qed.
Lemma D_a99f8 : D! W_a99f8 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_a99fc : bv 32 := 0xfff68693.
Lemma F_a99fc : F! 0xa99fc W_a99fc.
Proof. vm_refl. Qed.
Lemma D_a99fc : D! W_a99fc (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_a9a00 : bv 32 := 0x00ae8eb3.
Lemma F_a9a00 : F! 0xa9a00 W_a9a00.
Proof. vm_refl. Qed.
Lemma D_a9a00 : D! W_a9a00 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_a9a04 : bv 32 := 0x04068a63.
Lemma F_a9a04 : F! 0xa9a04 W_a9a04.
Proof. vm_refl. Qed.
Lemma D_a9a04 : D! W_a9a04 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_a9a08 : bv 32 := 0x000ea403.
Lemma F_a9a08 : F! 0xa9a08 W_a9a08.
Proof. vm_refl. Qed.
Lemma D_a9a08 : D! W_a9a08 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_a9a0c : bv 32 := 0xff0404e3.
Lemma F_a9a0c : F! 0xa9a0c W_a9a0c.
Proof. vm_refl. Qed.
Lemma D_a9a0c : D! W_a9a0c (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_a9a10 : bv 32 := 0x00028a63.
Lemma F_a9a10 : F! 0xa9a10 W_a9a10.
Proof. vm_refl. Qed.
Lemma D_a9a10 : D! W_a9a10 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_a9a24 : bv 32 := 0x000e8f93.
Lemma F_a9a24 : F! 0xa9a24 W_a9a24.
Proof. vm_refl. Qed.
Lemma D_a9a24 : D! W_a9a24 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_a9a28 : bv 32 := 0x00740463.
Lemma F_a9a28 : F! 0xa9a28 W_a9a28.
Proof. vm_refl. Qed.
Lemma D_a9a28 : D! W_a9a28 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_a9a2c : bv 32 := 0x00088f93.
Lemma F_a9a2c : F! 0xa9a2c W_a9a2c.
Proof. vm_refl. Qed.
Lemma D_a9a2c : D! W_a9a2c (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_a9a30 : bv 32 := 0x03c41063.
Lemma F_a9a30 : F! 0xa9a30 W_a9a30.
Proof. vm_refl. Qed.
Lemma D_a9a30 : D! W_a9a30 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_a9a34 : bv 32 := 0x028eb883.
Lemma F_a9a34 : F! 0xa9a34 W_a9a34.
Proof. vm_refl. Qed.
Lemma D_a9a34 : D! W_a9a34 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_a9a38 : bv 32 := 0x011f7c63.
Lemma F_a9a38 : F! 0xa9a38 W_a9a38.
Proof. vm_refl. Qed.
Lemma D_a9a38 : D! W_a9a38 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_a9a50 : bv 32 := 0x000f8893.
Lemma F_a9a50 : F! 0xa9a50 W_a9a50.
Proof. vm_refl. Qed.
Lemma D_a9a50 : D! W_a9a50 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_a9a54 : bv 32 := 0xfa9ff06f.
Lemma F_a9a54 : F! 0xa9a54 W_a9a54.
Proof. vm_refl. Qed.
Lemma D_a9a54 : D! W_a9a54 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_a9a58 : bv 32 := 0x02088c63.
Lemma F_a9a58 : F! 0xa9a58 W_a9a58.
Proof. vm_refl. Qed.
Lemma D_a9a58 : D! W_a9a58 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_a9a90 : bv 32 := 0x0105b603.
Lemma F_a9a90 : F! 0xa9a90 W_a9a90.
Proof. vm_refl. Qed.
Lemma D_a9a90 : D! W_a9a90 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_a9a94 : bv 32 := 0x0205b683.
Lemma F_a9a94 : F! 0xa9a94 W_a9a94.
Proof. vm_refl. Qed.
Lemma D_a9a94 : D! W_a9a94 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_a9a98 : bv 32 := 0x0285b503.
Lemma F_a9a98 : F! 0xa9a98 W_a9a98.
Proof. vm_refl. Qed.
Lemma D_a9a98 : D! W_a9a98 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_a9a9c : bv 32 := 0x00c68733.
Lemma F_a9a9c : F! 0xa9a9c W_a9a9c.
Proof. vm_refl. Qed.
Lemma D_a9a9c : D! W_a9a9c (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_a9aa0 : bv 32 := 0xfff50793.
Lemma F_a9aa0 : F! 0xa9aa0 W_a9aa0.
Proof. vm_refl. Qed.
Lemma D_a9aa0 : D! W_a9aa0 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_a9aa4 : bv 32 := 0x40e00733.
Lemma F_a9aa4 : F! 0xa9aa4 W_a9aa4.
Proof. vm_refl. Qed.
Lemma D_a9aa4 : D! W_a9aa4 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_a9aa8 : bv 32 := 0x00c7f633.
Lemma F_a9aa8 : F! 0xa9aa8 W_a9aa8.
Proof. vm_refl. Qed.
Lemma D_a9aa8 : D! W_a9aa8 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_a9aac : bv 32 := 0x00e7f733.
Lemma F_a9aac : F! 0xa9aac W_a9aac.
Proof. vm_refl. Qed.
Lemma D_a9aac : D! W_a9aac (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_a9ab0 : bv 32 := 0x00700793.
Lemma F_a9ab0 : F! 0xa9ab0 W_a9ab0.
Proof. vm_refl. Qed.
Lemma D_a9ab0 : D! W_a9ab0 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_a9ab4 : bv 32 := 0x00d706b3.
Lemma F_a9ab4 : F! 0xa9ab4 W_a9ab4.
Proof. vm_refl. Qed.
Lemma D_a9ab4 : D! W_a9ab4 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_a9ab8 : bv 32 := 0x02d5b023.
Lemma F_a9ab8 : F! 0xa9ab8 W_a9ab8.
Proof. vm_refl. Qed.
Lemma D_a9ab8 : D! W_a9ab8 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_a9abc : bv 32 := 0x02c5b823.
Lemma F_a9abc : F! 0xa9abc W_a9abc.
Proof. vm_refl. Qed.
Lemma D_a9abc : D! W_a9abc (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_a9ac0 : bv 32 := 0x00a7e663.
Lemma F_a9ac0 : F! 0xa9ac0 W_a9ac0.
Proof. vm_refl. Qed.
Lemma D_a9ac0 : D! W_a9ac0 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_a9ac4 : bv 32 := 0x00800513.
Lemma F_a9ac4 : F! 0xa9ac4 W_a9ac4.
Proof. vm_refl. Qed.
Lemma D_a9ac4 : D! W_a9ac4 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_a9ac8 : bv 32 := 0x02a5b423.
Lemma F_a9ac8 : F! 0xa9ac8 W_a9ac8.
Proof. vm_refl. Qed.
Lemma D_a9ac8 : D! W_a9ac8 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_a9acc : bv 32 := 0x00d60633.
Lemma F_a9acc : F! 0xa9acc W_a9acc.
Proof. vm_refl. Qed.
Lemma D_a9acc : D! W_a9acc (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_a9ad0 : bv 32 := 0x000205b7.
Lemma F_a9ad0 : F! 0xa9ad0 W_a9ad0.
Proof. vm_refl. Qed.
Lemma D_a9ad0 : D! W_a9ad0 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_a9ad4 : bv 32 := 0x00a60633.
Lemma F_a9ad4 : F! 0xa9ad4 W_a9ad4.
Proof. vm_refl. Qed.
Lemma D_a9ad4 : D! W_a9ad4 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_a9ad8 : bv 32 := 0x0d15869b.
Lemma F_a9ad8 : F! 0xa9ad8 W_a9ad8.
Proof. vm_refl. Qed.
Lemma D_a9ad8 : D! W_a9ad8 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_a9adc : bv 32 := 0x0df60593.
Lemma F_a9adc : F! 0xa9adc W_a9adc.
Proof. vm_refl. Qed.
Lemma D_a9adc : D! W_a9adc (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_a9ae0 : bv 32 := 0xff85f593.
Lemma F_a9ae0 : F! 0xa9ae0 W_a9ae0.
Proof. vm_refl. Qed.
Lemma D_a9ae0 : D! W_a9ae0 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_a9ae4 : bv 32 := 0x00b4bc23.
Lemma F_a9ae4 : F! 0xa9ae4 W_a9ae4.
Proof. vm_refl. Qed.
Lemma D_a9ae4 : D! W_a9ae4 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_a9ae8 : bv 32 := 0x02a4b023.
Lemma F_a9ae8 : F! 0xa9ae8 W_a9ae8.
Proof. vm_refl. Qed.
Lemma D_a9ae8 : D! W_a9ae8 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_a9aec : bv 32 := 0x02d5ea63.
Lemma F_a9aec : F! 0xa9aec W_a9aec.
Proof. vm_refl. Qed.
Lemma D_a9aec : D! W_a9aec (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_a9b20 : bv 32 := 0x00030697.
Lemma F_a9b20 : F! 0xa9b20 W_a9b20.
Proof. vm_refl. Qed.
Lemma D_a9b20 : D! W_a9b20 (Auipc 13 48).
Proof. vm_refl. Qed.
Definition W_a9b24 : bv 32 := 0x0104b983.
Lemma F_a9b24 : F! 0xa9b24 W_a9b24.
Proof. vm_refl. Qed.
Lemma D_a9b24 : D! W_a9b24 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_a9b28 : bv 32 := 0x0284b603.
Lemma F_a9b28 : F! 0xa9b28 W_a9b28.
Proof. vm_refl. Qed.
Lemma D_a9b28 : D! W_a9b28 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_a9b2c : bv 32 := 0xfff50713.
Lemma F_a9b2c : F! 0xa9b2c W_a9b2c.
Proof. vm_refl. Qed.
Lemma D_a9b2c : D! W_a9b2c (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_a9b30 : bv 32 := 0xf3800793.
Lemma F_a9b30 : F! 0xa9b30 W_a9b30.
Proof. vm_refl. Qed.
Lemma D_a9b30 : D! W_a9b30 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_a9b34 : bv 32 := 0xa3868513.
Lemma F_a9b34 : F! 0xa9b34 W_a9b34.
Proof. vm_refl. Qed.
Lemma D_a9b34 : D! W_a9b34 (OpImm ALU_ADD 10 13 2616).
Proof. vm_refl. Qed.
Definition W_a9b38 : bv 32 := 0x40a787b3.
Lemma F_a9b38 : F! 0xa9b38 W_a9b38.
Proof. vm_refl. Qed.
Lemma D_a9b38 : D! W_a9b38 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_a9b3c : bv 32 := 0x00f77733.
Lemma F_a9b3c : F! 0xa9b3c W_a9b3c.
Proof. vm_refl. Qed.
Lemma D_a9b3c : D! W_a9b3c (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_a9b40 : bv 32 := 0xfff64693.
Lemma F_a9b40 : F! 0xa9b40 W_a9b40.
Proof. vm_refl. Qed.
Lemma D_a9b40 : D! W_a9b40 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_a9b44 : bv 32 := 0x00e50933.
Lemma F_a9b44 : F! 0xa9b44 W_a9b44.
Proof. vm_refl. Qed.
Lemma D_a9b44 : D! W_a9b44 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_a9b48 : bv 32 := 0x00369693.
Lemma F_a9b48 : F! 0xa9b48 W_a9b48.
Proof. vm_refl. Qed.
Lemma D_a9b48 : D! W_a9b48 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_a9b4c : bv 32 := 0x00d506b3.
Lemma F_a9b4c : F! 0xa9b4c W_a9b4c.
Proof. vm_refl. Qed.
Lemma D_a9b4c : D! W_a9b4c (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_a9b50 : bv 32 := 0x00b68a33.
Lemma F_a9b50 : F! 0xa9b50 W_a9b50.
Proof. vm_refl. Qed.
Lemma D_a9b50 : D! W_a9b50 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_a9b54 : bv 32 := 0x0c890413.
Lemma F_a9b54 : F! 0xa9b54 W_a9b54.
Proof. vm_refl. Qed.
Lemma D_a9b54 : D! W_a9b54 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_a9b58 : bv 32 := 0x04098463.
Lemma F_a9b58 : F! 0xa9b58 W_a9b58.
Proof. vm_refl. Qed.
Lemma D_a9b58 : D! W_a9b58 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_a9ba0 : bv 32 := 0x00ca3023.
Lemma F_a9ba0 : F! 0xa9ba0 W_a9ba0.
Proof. vm_refl. Qed.
Lemma D_a9ba0 : D! W_a9ba0 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_a9ba4 : bv 32 := 0x0d493023.
Lemma F_a9ba4 : F! 0xa9ba4 W_a9ba4.
Proof. vm_refl. Qed.
Lemma D_a9ba4 : D! W_a9ba4 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_a9ba8 : bv 32 := 0x01293023.
Lemma F_a9ba8 : F! 0xa9ba8 W_a9ba8.
Proof. vm_refl. Qed.
Lemma D_a9ba8 : D! W_a9ba8 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_a9bac : bv 32 := 0x00040513.
Lemma F_a9bac : F! 0xa9bac W_a9bac.
Proof. vm_refl. Qed.
Lemma D_a9bac : D! W_a9bac (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_a9bb0 : bv 32 := 0x16c130ef.
Lemma F_a9bb0 : F! 0xa9bb0 W_a9bb0.
Proof. vm_refl. Qed.
Lemma D_a9bb0 : D! W_a9bb0 (Jal 1 78188).
Proof. vm_refl. Qed.
Definition W_a9bb4 : bv 32 := 0x04054a63.
Lemma F_a9bb4 : F! 0xa9bb4 W_a9bb4.
Proof. vm_refl. Qed.
Lemma D_a9bb4 : D! W_a9bb4 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_a9bb8 : bv 32 := 0x00051663.
Lemma F_a9bb8 : F! 0xa9bb8 W_a9bb8.
Proof. vm_refl. Qed.
Lemma D_a9bb8 : D! W_a9bb8 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_a9bbc : bv 32 := 0x00100513.
Lemma F_a9bbc : F! 0xa9bbc W_a9bbc.
Proof. vm_refl. Qed.
Lemma D_a9bbc : D! W_a9bbc (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_a9bc0 : bv 32 := 0x00a48023.
Lemma F_a9bc0 : F! 0xa9bc0 W_a9bc0.
Proof. vm_refl. Qed.
Lemma D_a9bc0 : D! W_a9bc0 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_a9bc4 : bv 32 := 0x00200513.
Lemma F_a9bc4 : F! 0xa9bc4 W_a9bc4.
Proof. vm_refl. Qed.
Lemma D_a9bc4 : D! W_a9bc4 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_a9bc8 : bv 32 := 0x00050597.
Lemma F_a9bc8 : F! 0xa9bc8 W_a9bc8.
Proof. vm_refl. Qed.
Lemma D_a9bc8 : D! W_a9bc8 (Auipc 11 80).
Proof. vm_refl. Qed.
Definition W_a9bcc : bv 32 := 0x02a92423.
Lemma F_a9bcc : F! 0xa9bcc W_a9bcc.
Proof. vm_refl. Qed.
Lemma D_a9bcc : D! W_a9bcc (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_a9bd0 : bv 32 := 0x06000893.
Lemma F_a9bd0 : F! 0xa9bd0 W_a9bd0.
Proof. vm_refl. Qed.
Lemma D_a9bd0 : D! W_a9bd0 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_a9bd4 : bv 32 := 0xa6058513.
Lemma F_a9bd4 : F! 0xa9bd4 W_a9bd4.
Proof. vm_refl. Qed.
Lemma D_a9bd4 : D! W_a9bd4 (OpImm ALU_ADD 10 11 2656).
Proof. vm_refl. Qed.
Definition W_a9bd8 : bv 32 := 0x03848593.
Lemma F_a9bd8 : F! 0xa9bd8 W_a9bd8.
Proof. vm_refl. Qed.
Lemma D_a9bd8 : D! W_a9bd8 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_a9bdc : bv 32 := 0x00000073.
Lemma F_a9bdc : F! 0xa9bdc W_a9bdc.
Proof. vm_refl. Qed.
Lemma E_a9bdc : is_ecall W_a9bdc = true.
Proof. reflexivity. Qed.
Definition W_a9be0 : bv 32 := 0x07890613.
Lemma F_a9be0 : F! 0xa9be0 W_a9be0.
Proof. vm_refl. Qed.
Lemma D_a9be0 : D! W_a9be0 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_a9be4 : bv 32 := 0x02a92023.
Lemma F_a9be4 : F! 0xa9be4 W_a9be4.
Proof. vm_refl. Qed.
Lemma D_a9be4 : D! W_a9be4 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_a9be8 : bv 32 := 0x08b93c23.
Lemma F_a9be8 : F! 0xa9be8 W_a9be8.
Proof. vm_refl. Qed.
Lemma D_a9be8 : D! W_a9be8 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_a9bec : bv 32 := 0x06c93c23.
Lemma F_a9bec : F! 0xa9bec W_a9bec.
Proof. vm_refl. Qed.
Lemma D_a9bec : D! W_a9bec (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_a9bf0 : bv 32 := 0x00050517.
Lemma F_a9bf0 : F! 0xa9bf0 W_a9bf0.
Proof. vm_refl. Qed.
Lemma D_a9bf0 : D! W_a9bf0 (Auipc 10 80).
Proof. vm_refl. Qed.
Definition W_a9bf4 : bv 32 := 0xca853503.
Lemma F_a9bf4 : F! 0xa9bf4 W_a9bf4.
Proof. vm_refl. Qed.
Lemma D_a9bf4 : D! W_a9bf4 (Load SZ8 true 10 10 3240).
Proof. vm_refl. Qed.
Definition W_a9bf8 : bv 32 := 0x01293423.
Lemma F_a9bf8 : F! 0xa9bf8 W_a9bf8.
Proof. vm_refl. Qed.
Lemma D_a9bf8 : D! W_a9bf8 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_a9bfc : bv 32 := 0x01293823.
Lemma F_a9bfc : F! 0xa9bfc W_a9bfc.
Proof. vm_refl. Qed.
Lemma D_a9bfc : D! W_a9bfc (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_a9c00 : bv 32 := 0x00a93c23.
Lemma F_a9c00 : F! 0xa9c00 W_a9c00.
Proof. vm_refl. Qed.
Lemma D_a9c00 : D! W_a9c00 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_a9c04 : bv 32 := 0x0080006f.
Lemma F_a9c04 : F! 0xa9c04 W_a9c04.
Proof. vm_refl. Qed.
Lemma D_a9c04 : D! W_a9c04 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_a9c0c : bv 32 := 0x03813083.
Lemma F_a9c0c : F! 0xa9c0c W_a9c0c.
Proof. vm_refl. Qed.
Lemma D_a9c0c : D! W_a9c0c (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_a9c10 : bv 32 := 0x03013403.
Lemma F_a9c10 : F! 0xa9c10 W_a9c10.
Proof. vm_refl. Qed.
Lemma D_a9c10 : D! W_a9c10 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_a9c14 : bv 32 := 0x02813483.
Lemma F_a9c14 : F! 0xa9c14 W_a9c14.
Proof. vm_refl. Qed.
Lemma D_a9c14 : D! W_a9c14 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_a9c18 : bv 32 := 0x02013903.
Lemma F_a9c18 : F! 0xa9c18 W_a9c18.
Proof. vm_refl. Qed.
Lemma D_a9c18 : D! W_a9c18 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_a9c1c : bv 32 := 0x01813983.
Lemma F_a9c1c : F! 0xa9c1c W_a9c1c.
Proof. vm_refl. Qed.
Lemma D_a9c1c : D! W_a9c1c (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_a9c20 : bv 32 := 0x01013a03.
Lemma F_a9c20 : F! 0xa9c20 W_a9c20.
Proof. vm_refl. Qed.
Lemma D_a9c20 : D! W_a9c20 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_a9c24 : bv 32 := 0x00813a83.
Lemma F_a9c24 : F! 0xa9c24 W_a9c24.
Proof. vm_refl. Qed.
Lemma D_a9c24 : D! W_a9c24 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_a9c28 : bv 32 := 0x04010113.
Lemma F_a9c28 : F! 0xa9c28 W_a9c28.
Proof. vm_refl. Qed.
Lemma D_a9c28 : D! W_a9c28 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_a9c2c : bv 32 := 0x00008067.
Lemma F_a9c2c : F! 0xa9c2c W_a9c2c.
Proof. vm_refl. Qed.
Lemma D_a9c2c : D! W_a9c2c (Jalr 0 1 0).
Proof. vm_refl. Qed.
