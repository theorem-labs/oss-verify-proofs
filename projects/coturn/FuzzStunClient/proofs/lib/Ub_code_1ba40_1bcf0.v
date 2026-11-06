(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
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
Definition W_1ba40 : bv 32 := 0xfc010113.
Lemma F_1ba40 : F! 0x1ba40 W_1ba40.
Proof. vm_refl. Qed.
Lemma D_1ba40 : D! W_1ba40 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_1ba44 : bv 32 := 0x02113c23.
Lemma F_1ba44 : F! 0x1ba44 W_1ba44.
Proof. vm_refl. Qed.
Lemma D_1ba44 : D! W_1ba44 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_1ba48 : bv 32 := 0x02813823.
Lemma F_1ba48 : F! 0x1ba48 W_1ba48.
Proof. vm_refl. Qed.
Lemma D_1ba48 : D! W_1ba48 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_1ba4c : bv 32 := 0x02913423.
Lemma F_1ba4c : F! 0x1ba4c W_1ba4c.
Proof. vm_refl. Qed.
Lemma D_1ba4c : D! W_1ba4c (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_1ba50 : bv 32 := 0x03213023.
Lemma F_1ba50 : F! 0x1ba50 W_1ba50.
Proof. vm_refl. Qed.
Lemma D_1ba50 : D! W_1ba50 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_1ba54 : bv 32 := 0x01313c23.
Lemma F_1ba54 : F! 0x1ba54 W_1ba54.
Proof. vm_refl. Qed.
Lemma D_1ba54 : D! W_1ba54 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_1ba58 : bv 32 := 0x01413823.
Lemma F_1ba58 : F! 0x1ba58 W_1ba58.
Proof. vm_refl. Qed.
Lemma D_1ba58 : D! W_1ba58 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_1ba5c : bv 32 := 0x01513423.
Lemma F_1ba5c : F! 0x1ba5c W_1ba5c.
Proof. vm_refl. Qed.
Lemma D_1ba5c : D! W_1ba5c (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_1ba60 : bv 32 := 0x02853683.
Lemma F_1ba60 : F! 0x1ba60 W_1ba60.
Proof. vm_refl. Qed.
Lemma D_1ba60 : D! W_1ba60 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_1ba64 : bv 32 := 0x0003b597.
Lemma F_1ba64 : F! 0x1ba64 W_1ba64.
Proof. vm_refl. Qed.
Lemma D_1ba64 : D! W_1ba64 (Auipc 11 59).
Proof. vm_refl. Qed.
Definition W_1ba68 : bv 32 := 0x20458593.
Lemma F_1ba68 : F! 0x1ba68 W_1ba68.
Proof. vm_refl. Qed.
Lemma D_1ba68 : D! W_1ba68 (OpImm ALU_ADD 11 11 516).
Proof. vm_refl. Qed.
Definition W_1ba6c : bv 32 := 0x0003b617.
Lemma F_1ba6c : F! 0x1ba6c W_1ba6c.
Proof. vm_refl. Qed.
Lemma D_1ba6c : D! W_1ba6c (Auipc 12 59).
Proof. vm_refl. Qed.
Definition W_1ba70 : bv 32 := 0x47c60493.
Lemma F_1ba70 : F! 0x1ba70 W_1ba70.
Proof. vm_refl. Qed.
Lemma D_1ba70 : D! W_1ba70 (OpImm ALU_ADD 9 12 1148).
Proof. vm_refl. Qed.
Definition W_1ba74 : bv 32 := 0x0c068e63.
Lemma F_1ba74 : F! 0x1ba74 W_1ba74.
Proof. vm_refl. Qed.
Lemma D_1ba74 : D! W_1ba74 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_1ba78 : bv 32 := 0x00000613.
Lemma F_1ba78 : F! 0x1ba78 W_1ba78.
Proof. vm_refl. Qed.
Lemma D_1ba78 : D! W_1ba78 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_1ba7c : bv 32 := 0x00000893.
Lemma F_1ba7c : F! 0x1ba7c W_1ba7c.
Proof. vm_refl. Qed.
Lemma D_1ba7c : D! W_1ba7c (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_1ba80 : bv 32 := 0x0000b717.
Lemma F_1ba80 : F! 0x1ba80 W_1ba80.
Proof. vm_refl. Qed.
Lemma D_1ba80 : D! W_1ba80 (Auipc 14 11).
Proof. vm_refl. Qed.
Definition W_1ba84 : bv 32 := 0x01853783.
Lemma F_1ba84 : F! 0x1ba84 W_1ba84.
Proof. vm_refl. Qed.
Lemma D_1ba84 : D! W_1ba84 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_1ba88 : bv 32 := 0x02053503.
Lemma F_1ba88 : F! 0x1ba88 W_1ba88.
Proof. vm_refl. Qed.
Lemma D_1ba88 : D! W_1ba88 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_1ba8c : bv 32 := 0x00600813.
Lemma F_1ba8c : F! 0x1ba8c W_1ba8c.
Proof. vm_refl. Qed.
Lemma D_1ba8c : D! W_1ba8c (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_1ba90 : bv 32 := 0x0000a297.
Lemma F_1ba90 : F! 0x1ba90 W_1ba90.
Proof. vm_refl. Qed.
Lemma D_1ba90 : D! W_1ba90 (Auipc 5 10).
Proof. vm_refl. Qed.
Definition W_1ba94 : bv 32 := 0x06076f03.
Lemma F_1ba94 : F! 0x1ba94 W_1ba94.
Proof. vm_refl. Qed.
Lemma D_1ba94 : D! W_1ba94 (Load SZ4 false 30 14 96).
Proof. vm_refl. Qed.
Definition W_1ba98 : bv 32 := 0xcc02b283.
Lemma F_1ba98 : F! 0x1ba98 W_1ba98.
Proof. vm_refl. Qed.
Lemma D_1ba98 : D! W_1ba98 (Load SZ8 true 5 5 3264).
Proof. vm_refl. Qed.
Definition W_1ba9c : bv 32 := 0x00200313.
Lemma F_1ba9c : F! 0x1ba9c W_1ba9c.
Proof. vm_refl. Qed.
Lemma D_1ba9c : D! W_1ba9c (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_1baa0 : bv 32 := 0x00700393.
Lemma F_1baa0 : F! 0x1baa0 W_1baa0.
Proof. vm_refl. Qed.
Lemma D_1baa0 : D! W_1baa0 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_1baa4 : bv 32 := 0x6474ee37.
Lemma F_1baa4 : F! 0x1baa4 W_1baa4.
Proof. vm_refl. Qed.
Lemma D_1baa4 : D! W_1baa4 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_1baa8 : bv 32 := 0x551e0e1b.
Lemma F_1baa8 : F! 0x1baa8 W_1baa8.
Proof. vm_refl. Qed.
Lemma D_1baa8 : D! W_1baa8 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_1baac : bv 32 := 0x00078e93.
Lemma F_1baac : F! 0x1baac W_1baac.
Proof. vm_refl. Qed.
Lemma D_1baac : D! W_1baac (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_1bab0 : bv 32 := 0x0180006f.
Lemma F_1bab0 : F! 0x1bab0 W_1bab0.
Proof. vm_refl. Qed.
Lemma D_1bab0 : D! W_1bab0 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_1bab4 : bv 32 := 0x010eb603.
Lemma F_1bab4 : F! 0x1bab4 W_1bab4.
Proof. vm_refl. Qed.
Lemma D_1bab4 : D! W_1bab4 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_1bab8 : bv 32 := 0x40c78633.
Lemma F_1bab8 : F! 0x1bab8 W_1bab8.
Proof. vm_refl. Qed.
Lemma D_1bab8 : D! W_1bab8 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_1babc : bv 32 := 0xfff68693.
Lemma F_1babc : F! 0x1babc W_1babc.
Proof. vm_refl. Qed.
Lemma D_1babc : D! W_1babc (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_1bac0 : bv 32 := 0x00ae8eb3.
Lemma F_1bac0 : F! 0x1bac0 W_1bac0.
Proof. vm_refl. Qed.
Lemma D_1bac0 : D! W_1bac0 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_1bac4 : bv 32 := 0x04068a63.
Lemma F_1bac4 : F! 0x1bac4 W_1bac4.
Proof. vm_refl. Qed.
Lemma D_1bac4 : D! W_1bac4 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_1bac8 : bv 32 := 0x000ea403.
Lemma F_1bac8 : F! 0x1bac8 W_1bac8.
Proof. vm_refl. Qed.
Lemma D_1bac8 : D! W_1bac8 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_1bacc : bv 32 := 0xff0404e3.
Lemma F_1bacc : F! 0x1bacc W_1bacc.
Proof. vm_refl. Qed.
Lemma D_1bacc : D! W_1bacc (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_1bad0 : bv 32 := 0x00028a63.
Lemma F_1bad0 : F! 0x1bad0 W_1bad0.
Proof. vm_refl. Qed.
Lemma D_1bad0 : D! W_1bad0 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_1bae4 : bv 32 := 0x000e8f93.
Lemma F_1bae4 : F! 0x1bae4 W_1bae4.
Proof. vm_refl. Qed.
Lemma D_1bae4 : D! W_1bae4 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_1bae8 : bv 32 := 0x00740463.
Lemma F_1bae8 : F! 0x1bae8 W_1bae8.
Proof. vm_refl. Qed.
Lemma D_1bae8 : D! W_1bae8 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_1baec : bv 32 := 0x00088f93.
Lemma F_1baec : F! 0x1baec W_1baec.
Proof. vm_refl. Qed.
Lemma D_1baec : D! W_1baec (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_1baf0 : bv 32 := 0x03c41063.
Lemma F_1baf0 : F! 0x1baf0 W_1baf0.
Proof. vm_refl. Qed.
Lemma D_1baf0 : D! W_1baf0 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_1baf4 : bv 32 := 0x028eb883.
Lemma F_1baf4 : F! 0x1baf4 W_1baf4.
Proof. vm_refl. Qed.
Lemma D_1baf4 : D! W_1baf4 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_1baf8 : bv 32 := 0x011f7c63.
Lemma F_1baf8 : F! 0x1baf8 W_1baf8.
Proof. vm_refl. Qed.
Lemma D_1baf8 : D! W_1baf8 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_1bb10 : bv 32 := 0x000f8893.
Lemma F_1bb10 : F! 0x1bb10 W_1bb10.
Proof. vm_refl. Qed.
Lemma D_1bb10 : D! W_1bb10 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_1bb14 : bv 32 := 0xfa9ff06f.
Lemma F_1bb14 : F! 0x1bb14 W_1bb14.
Proof. vm_refl. Qed.
Lemma D_1bb14 : D! W_1bb14 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_1bb18 : bv 32 := 0x02088c63.
Lemma F_1bb18 : F! 0x1bb18 W_1bb18.
Proof. vm_refl. Qed.
Lemma D_1bb18 : D! W_1bb18 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_1bb50 : bv 32 := 0x0105b603.
Lemma F_1bb50 : F! 0x1bb50 W_1bb50.
Proof. vm_refl. Qed.
Lemma D_1bb50 : D! W_1bb50 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_1bb54 : bv 32 := 0x0205b683.
Lemma F_1bb54 : F! 0x1bb54 W_1bb54.
Proof. vm_refl. Qed.
Lemma D_1bb54 : D! W_1bb54 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_1bb58 : bv 32 := 0x0285b503.
Lemma F_1bb58 : F! 0x1bb58 W_1bb58.
Proof. vm_refl. Qed.
Lemma D_1bb58 : D! W_1bb58 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_1bb5c : bv 32 := 0x00c68733.
Lemma F_1bb5c : F! 0x1bb5c W_1bb5c.
Proof. vm_refl. Qed.
Lemma D_1bb5c : D! W_1bb5c (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_1bb60 : bv 32 := 0xfff50793.
Lemma F_1bb60 : F! 0x1bb60 W_1bb60.
Proof. vm_refl. Qed.
Lemma D_1bb60 : D! W_1bb60 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_1bb64 : bv 32 := 0x40e00733.
Lemma F_1bb64 : F! 0x1bb64 W_1bb64.
Proof. vm_refl. Qed.
Lemma D_1bb64 : D! W_1bb64 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_1bb68 : bv 32 := 0x00c7f633.
Lemma F_1bb68 : F! 0x1bb68 W_1bb68.
Proof. vm_refl. Qed.
Lemma D_1bb68 : D! W_1bb68 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_1bb6c : bv 32 := 0x00e7f733.
Lemma F_1bb6c : F! 0x1bb6c W_1bb6c.
Proof. vm_refl. Qed.
Lemma D_1bb6c : D! W_1bb6c (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_1bb70 : bv 32 := 0x00700793.
Lemma F_1bb70 : F! 0x1bb70 W_1bb70.
Proof. vm_refl. Qed.
Lemma D_1bb70 : D! W_1bb70 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_1bb74 : bv 32 := 0x00d706b3.
Lemma F_1bb74 : F! 0x1bb74 W_1bb74.
Proof. vm_refl. Qed.
Lemma D_1bb74 : D! W_1bb74 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_1bb78 : bv 32 := 0x02d5b023.
Lemma F_1bb78 : F! 0x1bb78 W_1bb78.
Proof. vm_refl. Qed.
Lemma D_1bb78 : D! W_1bb78 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_1bb7c : bv 32 := 0x02c5b823.
Lemma F_1bb7c : F! 0x1bb7c W_1bb7c.
Proof. vm_refl. Qed.
Lemma D_1bb7c : D! W_1bb7c (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_1bb80 : bv 32 := 0x00a7e663.
Lemma F_1bb80 : F! 0x1bb80 W_1bb80.
Proof. vm_refl. Qed.
Lemma D_1bb80 : D! W_1bb80 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_1bb84 : bv 32 := 0x00800513.
Lemma F_1bb84 : F! 0x1bb84 W_1bb84.
Proof. vm_refl. Qed.
Lemma D_1bb84 : D! W_1bb84 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_1bb88 : bv 32 := 0x02a5b423.
Lemma F_1bb88 : F! 0x1bb88 W_1bb88.
Proof. vm_refl. Qed.
Lemma D_1bb88 : D! W_1bb88 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_1bb8c : bv 32 := 0x00d60633.
Lemma F_1bb8c : F! 0x1bb8c W_1bb8c.
Proof. vm_refl. Qed.
Lemma D_1bb8c : D! W_1bb8c (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_1bb90 : bv 32 := 0x000205b7.
Lemma F_1bb90 : F! 0x1bb90 W_1bb90.
Proof. vm_refl. Qed.
Lemma D_1bb90 : D! W_1bb90 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_1bb94 : bv 32 := 0x00a60633.
Lemma F_1bb94 : F! 0x1bb94 W_1bb94.
Proof. vm_refl. Qed.
Lemma D_1bb94 : D! W_1bb94 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_1bb98 : bv 32 := 0x0d15869b.
Lemma F_1bb98 : F! 0x1bb98 W_1bb98.
Proof. vm_refl. Qed.
Lemma D_1bb98 : D! W_1bb98 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_1bb9c : bv 32 := 0x0df60593.
Lemma F_1bb9c : F! 0x1bb9c W_1bb9c.
Proof. vm_refl. Qed.
Lemma D_1bb9c : D! W_1bb9c (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_1bba0 : bv 32 := 0xff85f593.
Lemma F_1bba0 : F! 0x1bba0 W_1bba0.
Proof. vm_refl. Qed.
Lemma D_1bba0 : D! W_1bba0 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_1bba4 : bv 32 := 0x00b4bc23.
Lemma F_1bba4 : F! 0x1bba4 W_1bba4.
Proof. vm_refl. Qed.
Lemma D_1bba4 : D! W_1bba4 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_1bba8 : bv 32 := 0x02a4b023.
Lemma F_1bba8 : F! 0x1bba8 W_1bba8.
Proof. vm_refl. Qed.
Lemma D_1bba8 : D! W_1bba8 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_1bbac : bv 32 := 0x02d5ea63.
Lemma F_1bbac : F! 0x1bbac W_1bbac.
Proof. vm_refl. Qed.
Lemma D_1bbac : D! W_1bbac (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_1bbe0 : bv 32 := 0x0001b697.
Lemma F_1bbe0 : F! 0x1bbe0 W_1bbe0.
Proof. vm_refl. Qed.
Lemma D_1bbe0 : D! W_1bbe0 (Auipc 13 27).
Proof. vm_refl. Qed.
Definition W_1bbe4 : bv 32 := 0x0104b983.
Lemma F_1bbe4 : F! 0x1bbe4 W_1bbe4.
Proof. vm_refl. Qed.
Lemma D_1bbe4 : D! W_1bbe4 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_1bbe8 : bv 32 := 0x0284b603.
Lemma F_1bbe8 : F! 0x1bbe8 W_1bbe8.
Proof. vm_refl. Qed.
Lemma D_1bbe8 : D! W_1bbe8 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_1bbec : bv 32 := 0xfff50713.
Lemma F_1bbec : F! 0x1bbec W_1bbec.
Proof. vm_refl. Qed.
Lemma D_1bbec : D! W_1bbec (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_1bbf0 : bv 32 := 0xf3800793.
Lemma F_1bbf0 : F! 0x1bbf0 W_1bbf0.
Proof. vm_refl. Qed.
Lemma D_1bbf0 : D! W_1bbf0 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_1bbf4 : bv 32 := 0xfb868513.
Lemma F_1bbf4 : F! 0x1bbf4 W_1bbf4.
Proof. vm_refl. Qed.
Lemma D_1bbf4 : D! W_1bbf4 (OpImm ALU_ADD 10 13 4024).
Proof. vm_refl. Qed.
Definition W_1bbf8 : bv 32 := 0x40a787b3.
Lemma F_1bbf8 : F! 0x1bbf8 W_1bbf8.
Proof. vm_refl. Qed.
Lemma D_1bbf8 : D! W_1bbf8 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_1bbfc : bv 32 := 0x00f77733.
Lemma F_1bbfc : F! 0x1bbfc W_1bbfc.
Proof. vm_refl. Qed.
Lemma D_1bbfc : D! W_1bbfc (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_1bc00 : bv 32 := 0xfff64693.
Lemma F_1bc00 : F! 0x1bc00 W_1bc00.
Proof. vm_refl. Qed.
Lemma D_1bc00 : D! W_1bc00 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_1bc04 : bv 32 := 0x00e50933.
Lemma F_1bc04 : F! 0x1bc04 W_1bc04.
Proof. vm_refl. Qed.
Lemma D_1bc04 : D! W_1bc04 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_1bc08 : bv 32 := 0x00369693.
Lemma F_1bc08 : F! 0x1bc08 W_1bc08.
Proof. vm_refl. Qed.
Lemma D_1bc08 : D! W_1bc08 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_1bc0c : bv 32 := 0x00d506b3.
Lemma F_1bc0c : F! 0x1bc0c W_1bc0c.
Proof. vm_refl. Qed.
Lemma D_1bc0c : D! W_1bc0c (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_1bc10 : bv 32 := 0x00b68a33.
Lemma F_1bc10 : F! 0x1bc10 W_1bc10.
Proof. vm_refl. Qed.
Lemma D_1bc10 : D! W_1bc10 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_1bc14 : bv 32 := 0x0c890413.
Lemma F_1bc14 : F! 0x1bc14 W_1bc14.
Proof. vm_refl. Qed.
Lemma D_1bc14 : D! W_1bc14 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_1bc18 : bv 32 := 0x04098463.
Lemma F_1bc18 : F! 0x1bc18 W_1bc18.
Proof. vm_refl. Qed.
Lemma D_1bc18 : D! W_1bc18 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_1bc60 : bv 32 := 0x00ca3023.
Lemma F_1bc60 : F! 0x1bc60 W_1bc60.
Proof. vm_refl. Qed.
Lemma D_1bc60 : D! W_1bc60 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_1bc64 : bv 32 := 0x0d493023.
Lemma F_1bc64 : F! 0x1bc64 W_1bc64.
Proof. vm_refl. Qed.
Lemma D_1bc64 : D! W_1bc64 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_1bc68 : bv 32 := 0x01293023.
Lemma F_1bc68 : F! 0x1bc68 W_1bc68.
Proof. vm_refl. Qed.
Lemma D_1bc68 : D! W_1bc68 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_1bc6c : bv 32 := 0x00040513.
Lemma F_1bc6c : F! 0x1bc6c W_1bc6c.
Proof. vm_refl. Qed.
Lemma D_1bc6c : D! W_1bc6c (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_1bc70 : bv 32 := 0x1b9080ef.
Lemma F_1bc70 : F! 0x1bc70 W_1bc70.
Proof. vm_refl. Qed.
Lemma D_1bc70 : D! W_1bc70 (Jal 1 35256).
Proof. vm_refl. Qed.
Definition W_1bc74 : bv 32 := 0x04054a63.
Lemma F_1bc74 : F! 0x1bc74 W_1bc74.
Proof. vm_refl. Qed.
Lemma D_1bc74 : D! W_1bc74 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_1bc78 : bv 32 := 0x00051663.
Lemma F_1bc78 : F! 0x1bc78 W_1bc78.
Proof. vm_refl. Qed.
Lemma D_1bc78 : D! W_1bc78 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_1bc7c : bv 32 := 0x00100513.
Lemma F_1bc7c : F! 0x1bc7c W_1bc7c.
Proof. vm_refl. Qed.
Lemma D_1bc7c : D! W_1bc7c (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_1bc80 : bv 32 := 0x00a48023.
Lemma F_1bc80 : F! 0x1bc80 W_1bc80.
Proof. vm_refl. Qed.
Lemma D_1bc80 : D! W_1bc80 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_1bc84 : bv 32 := 0x00200513.
Lemma F_1bc84 : F! 0x1bc84 W_1bc84.
Proof. vm_refl. Qed.
Lemma D_1bc84 : D! W_1bc84 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_1bc88 : bv 32 := 0x0003b597.
Lemma F_1bc88 : F! 0x1bc88 W_1bc88.
Proof. vm_refl. Qed.
Lemma D_1bc88 : D! W_1bc88 (Auipc 11 59).
Proof. vm_refl. Qed.
Definition W_1bc8c : bv 32 := 0x02a92423.
Lemma F_1bc8c : F! 0x1bc8c W_1bc8c.
Proof. vm_refl. Qed.
Lemma D_1bc8c : D! W_1bc8c (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_1bc90 : bv 32 := 0x06000893.
Lemma F_1bc90 : F! 0x1bc90 W_1bc90.
Proof. vm_refl. Qed.
Lemma D_1bc90 : D! W_1bc90 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_1bc94 : bv 32 := 0xfe058513.
Lemma F_1bc94 : F! 0x1bc94 W_1bc94.
Proof. vm_refl. Qed.
Lemma D_1bc94 : D! W_1bc94 (OpImm ALU_ADD 10 11 4064).
Proof. vm_refl. Qed.
Definition W_1bc98 : bv 32 := 0x03848593.
Lemma F_1bc98 : F! 0x1bc98 W_1bc98.
Proof. vm_refl. Qed.
Lemma D_1bc98 : D! W_1bc98 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_1bc9c : bv 32 := 0x00000073.
Lemma F_1bc9c : F! 0x1bc9c W_1bc9c.
Proof. vm_refl. Qed.
Lemma E_1bc9c : is_ecall W_1bc9c = true.
Proof. reflexivity. Qed.
Definition W_1bca0 : bv 32 := 0x07890613.
Lemma F_1bca0 : F! 0x1bca0 W_1bca0.
Proof. vm_refl. Qed.
Lemma D_1bca0 : D! W_1bca0 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_1bca4 : bv 32 := 0x02a92023.
Lemma F_1bca4 : F! 0x1bca4 W_1bca4.
Proof. vm_refl. Qed.
Lemma D_1bca4 : D! W_1bca4 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_1bca8 : bv 32 := 0x08b93c23.
Lemma F_1bca8 : F! 0x1bca8 W_1bca8.
Proof. vm_refl. Qed.
Lemma D_1bca8 : D! W_1bca8 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_1bcac : bv 32 := 0x06c93c23.
Lemma F_1bcac : F! 0x1bcac W_1bcac.
Proof. vm_refl. Qed.
Lemma D_1bcac : D! W_1bcac (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_1bcb0 : bv 32 := 0x0003b517.
Lemma F_1bcb0 : F! 0x1bcb0 W_1bcb0.
Proof. vm_refl. Qed.
Lemma D_1bcb0 : D! W_1bcb0 (Auipc 10 59).
Proof. vm_refl. Qed.
Definition W_1bcb4 : bv 32 := 0x22053503.
Lemma F_1bcb4 : F! 0x1bcb4 W_1bcb4.
Proof. vm_refl. Qed.
Lemma D_1bcb4 : D! W_1bcb4 (Load SZ8 true 10 10 544).
Proof. vm_refl. Qed.
Definition W_1bcb8 : bv 32 := 0x01293423.
Lemma F_1bcb8 : F! 0x1bcb8 W_1bcb8.
Proof. vm_refl. Qed.
Lemma D_1bcb8 : D! W_1bcb8 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_1bcbc : bv 32 := 0x01293823.
Lemma F_1bcbc : F! 0x1bcbc W_1bcbc.
Proof. vm_refl. Qed.
Lemma D_1bcbc : D! W_1bcbc (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_1bcc0 : bv 32 := 0x00a93c23.
Lemma F_1bcc0 : F! 0x1bcc0 W_1bcc0.
Proof. vm_refl. Qed.
Lemma D_1bcc0 : D! W_1bcc0 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_1bcc4 : bv 32 := 0x0080006f.
Lemma F_1bcc4 : F! 0x1bcc4 W_1bcc4.
Proof. vm_refl. Qed.
Lemma D_1bcc4 : D! W_1bcc4 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_1bccc : bv 32 := 0x03813083.
Lemma F_1bccc : F! 0x1bccc W_1bccc.
Proof. vm_refl. Qed.
Lemma D_1bccc : D! W_1bccc (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_1bcd0 : bv 32 := 0x03013403.
Lemma F_1bcd0 : F! 0x1bcd0 W_1bcd0.
Proof. vm_refl. Qed.
Lemma D_1bcd0 : D! W_1bcd0 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_1bcd4 : bv 32 := 0x02813483.
Lemma F_1bcd4 : F! 0x1bcd4 W_1bcd4.
Proof. vm_refl. Qed.
Lemma D_1bcd4 : D! W_1bcd4 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_1bcd8 : bv 32 := 0x02013903.
Lemma F_1bcd8 : F! 0x1bcd8 W_1bcd8.
Proof. vm_refl. Qed.
Lemma D_1bcd8 : D! W_1bcd8 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_1bcdc : bv 32 := 0x01813983.
Lemma F_1bcdc : F! 0x1bcdc W_1bcdc.
Proof. vm_refl. Qed.
Lemma D_1bcdc : D! W_1bcdc (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_1bce0 : bv 32 := 0x01013a03.
Lemma F_1bce0 : F! 0x1bce0 W_1bce0.
Proof. vm_refl. Qed.
Lemma D_1bce0 : D! W_1bce0 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_1bce4 : bv 32 := 0x00813a83.
Lemma F_1bce4 : F! 0x1bce4 W_1bce4.
Proof. vm_refl. Qed.
Lemma D_1bce4 : D! W_1bce4 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_1bce8 : bv 32 := 0x04010113.
Lemma F_1bce8 : F! 0x1bce8 W_1bce8.
Proof. vm_refl. Qed.
Lemma D_1bce8 : D! W_1bce8 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_1bcec : bv 32 := 0x00008067.
Lemma F_1bcec : F! 0x1bcec W_1bcec.
Proof. vm_refl. Qed.
Lemma D_1bcec : D! W_1bcec (Jalr 0 1 0).
Proof. vm_refl. Qed.
