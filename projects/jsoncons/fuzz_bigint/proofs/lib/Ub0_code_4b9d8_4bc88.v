(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
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
Definition W_4b9d8 : bv 32 := 0xfc010113.
Lemma F_4b9d8 : F! 0x4b9d8 W_4b9d8.
Proof. vm_refl. Qed.
Lemma D_4b9d8 : D! W_4b9d8 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_4b9dc : bv 32 := 0x02113c23.
Lemma F_4b9dc : F! 0x4b9dc W_4b9dc.
Proof. vm_refl. Qed.
Lemma D_4b9dc : D! W_4b9dc (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_4b9e0 : bv 32 := 0x02813823.
Lemma F_4b9e0 : F! 0x4b9e0 W_4b9e0.
Proof. vm_refl. Qed.
Lemma D_4b9e0 : D! W_4b9e0 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_4b9e4 : bv 32 := 0x02913423.
Lemma F_4b9e4 : F! 0x4b9e4 W_4b9e4.
Proof. vm_refl. Qed.
Lemma D_4b9e4 : D! W_4b9e4 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_4b9e8 : bv 32 := 0x03213023.
Lemma F_4b9e8 : F! 0x4b9e8 W_4b9e8.
Proof. vm_refl. Qed.
Lemma D_4b9e8 : D! W_4b9e8 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_4b9ec : bv 32 := 0x01313c23.
Lemma F_4b9ec : F! 0x4b9ec W_4b9ec.
Proof. vm_refl. Qed.
Lemma D_4b9ec : D! W_4b9ec (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_4b9f0 : bv 32 := 0x01413823.
Lemma F_4b9f0 : F! 0x4b9f0 W_4b9f0.
Proof. vm_refl. Qed.
Lemma D_4b9f0 : D! W_4b9f0 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_4b9f4 : bv 32 := 0x01513423.
Lemma F_4b9f4 : F! 0x4b9f4 W_4b9f4.
Proof. vm_refl. Qed.
Lemma D_4b9f4 : D! W_4b9f4 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_4b9f8 : bv 32 := 0x02853683.
Lemma F_4b9f8 : F! 0x4b9f8 W_4b9f8.
Proof. vm_refl. Qed.
Lemma D_4b9f8 : D! W_4b9f8 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_4b9fc : bv 32 := 0x00045597.
Lemma F_4b9fc : F! 0x4b9fc W_4b9fc.
Proof. vm_refl. Qed.
Lemma D_4b9fc : D! W_4b9fc (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_4ba00 : bv 32 := 0x54458593.
Lemma F_4ba00 : F! 0x4ba00 W_4ba00.
Proof. vm_refl. Qed.
Lemma D_4ba00 : D! W_4ba00 (OpImm ALU_ADD 11 11 1348).
Proof. vm_refl. Qed.
Definition W_4ba04 : bv 32 := 0x00045617.
Lemma F_4ba04 : F! 0x4ba04 W_4ba04.
Proof. vm_refl. Qed.
Lemma D_4ba04 : D! W_4ba04 (Auipc 12 69).
Proof. vm_refl. Qed.
Definition W_4ba08 : bv 32 := 0x7c460493.
Lemma F_4ba08 : F! 0x4ba08 W_4ba08.
Proof. vm_refl. Qed.
Lemma D_4ba08 : D! W_4ba08 (OpImm ALU_ADD 9 12 1988).
Proof. vm_refl. Qed.
Definition W_4ba0c : bv 32 := 0x0c068e63.
Lemma F_4ba0c : F! 0x4ba0c W_4ba0c.
Proof. vm_refl. Qed.
Lemma D_4ba0c : D! W_4ba0c (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_4ba10 : bv 32 := 0x00000613.
Lemma F_4ba10 : F! 0x4ba10 W_4ba10.
Proof. vm_refl. Qed.
Lemma D_4ba10 : D! W_4ba10 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_4ba14 : bv 32 := 0x00000893.
Lemma F_4ba14 : F! 0x4ba14 W_4ba14.
Proof. vm_refl. Qed.
Lemma D_4ba14 : D! W_4ba14 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_4ba18 : bv 32 := 0x00015717.
Lemma F_4ba18 : F! 0x4ba18 W_4ba18.
Proof. vm_refl. Qed.
Lemma D_4ba18 : D! W_4ba18 (Auipc 14 21).
Proof. vm_refl. Qed.
Definition W_4ba1c : bv 32 := 0x01853783.
Lemma F_4ba1c : F! 0x4ba1c W_4ba1c.
Proof. vm_refl. Qed.
Lemma D_4ba1c : D! W_4ba1c (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_4ba20 : bv 32 := 0x02053503.
Lemma F_4ba20 : F! 0x4ba20 W_4ba20.
Proof. vm_refl. Qed.
Lemma D_4ba20 : D! W_4ba20 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_4ba24 : bv 32 := 0x00600813.
Lemma F_4ba24 : F! 0x4ba24 W_4ba24.
Proof. vm_refl. Qed.
Lemma D_4ba24 : D! W_4ba24 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_4ba28 : bv 32 := 0x00013297.
Lemma F_4ba28 : F! 0x4ba28 W_4ba28.
Proof. vm_refl. Qed.
Lemma D_4ba28 : D! W_4ba28 (Auipc 5 19).
Proof. vm_refl. Qed.
Definition W_4ba2c : bv 32 := 0x94076f03.
Lemma F_4ba2c : F! 0x4ba2c W_4ba2c.
Proof. vm_refl. Qed.
Lemma D_4ba2c : D! W_4ba2c (Load SZ4 false 30 14 2368).
Proof. vm_refl. Qed.
Definition W_4ba30 : bv 32 := 0x5702b283.
Lemma F_4ba30 : F! 0x4ba30 W_4ba30.
Proof. vm_refl. Qed.
Lemma D_4ba30 : D! W_4ba30 (Load SZ8 true 5 5 1392).
Proof. vm_refl. Qed.
Definition W_4ba34 : bv 32 := 0x00200313.
Lemma F_4ba34 : F! 0x4ba34 W_4ba34.
Proof. vm_refl. Qed.
Lemma D_4ba34 : D! W_4ba34 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_4ba38 : bv 32 := 0x00700393.
Lemma F_4ba38 : F! 0x4ba38 W_4ba38.
Proof. vm_refl. Qed.
Lemma D_4ba38 : D! W_4ba38 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_4ba3c : bv 32 := 0x6474ee37.
Lemma F_4ba3c : F! 0x4ba3c W_4ba3c.
Proof. vm_refl. Qed.
Lemma D_4ba3c : D! W_4ba3c (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_4ba40 : bv 32 := 0x551e0e1b.
Lemma F_4ba40 : F! 0x4ba40 W_4ba40.
Proof. vm_refl. Qed.
Lemma D_4ba40 : D! W_4ba40 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_4ba44 : bv 32 := 0x00078e93.
Lemma F_4ba44 : F! 0x4ba44 W_4ba44.
Proof. vm_refl. Qed.
Lemma D_4ba44 : D! W_4ba44 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_4ba48 : bv 32 := 0x0180006f.
Lemma F_4ba48 : F! 0x4ba48 W_4ba48.
Proof. vm_refl. Qed.
Lemma D_4ba48 : D! W_4ba48 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_4ba4c : bv 32 := 0x010eb603.
Lemma F_4ba4c : F! 0x4ba4c W_4ba4c.
Proof. vm_refl. Qed.
Lemma D_4ba4c : D! W_4ba4c (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_4ba50 : bv 32 := 0x40c78633.
Lemma F_4ba50 : F! 0x4ba50 W_4ba50.
Proof. vm_refl. Qed.
Lemma D_4ba50 : D! W_4ba50 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_4ba54 : bv 32 := 0xfff68693.
Lemma F_4ba54 : F! 0x4ba54 W_4ba54.
Proof. vm_refl. Qed.
Lemma D_4ba54 : D! W_4ba54 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_4ba58 : bv 32 := 0x00ae8eb3.
Lemma F_4ba58 : F! 0x4ba58 W_4ba58.
Proof. vm_refl. Qed.
Lemma D_4ba58 : D! W_4ba58 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_4ba5c : bv 32 := 0x04068a63.
Lemma F_4ba5c : F! 0x4ba5c W_4ba5c.
Proof. vm_refl. Qed.
Lemma D_4ba5c : D! W_4ba5c (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_4ba60 : bv 32 := 0x000ea403.
Lemma F_4ba60 : F! 0x4ba60 W_4ba60.
Proof. vm_refl. Qed.
Lemma D_4ba60 : D! W_4ba60 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_4ba64 : bv 32 := 0xff0404e3.
Lemma F_4ba64 : F! 0x4ba64 W_4ba64.
Proof. vm_refl. Qed.
Lemma D_4ba64 : D! W_4ba64 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_4ba68 : bv 32 := 0x00028a63.
Lemma F_4ba68 : F! 0x4ba68 W_4ba68.
Proof. vm_refl. Qed.
Lemma D_4ba68 : D! W_4ba68 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_4ba7c : bv 32 := 0x000e8f93.
Lemma F_4ba7c : F! 0x4ba7c W_4ba7c.
Proof. vm_refl. Qed.
Lemma D_4ba7c : D! W_4ba7c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_4ba80 : bv 32 := 0x00740463.
Lemma F_4ba80 : F! 0x4ba80 W_4ba80.
Proof. vm_refl. Qed.
Lemma D_4ba80 : D! W_4ba80 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_4ba84 : bv 32 := 0x00088f93.
Lemma F_4ba84 : F! 0x4ba84 W_4ba84.
Proof. vm_refl. Qed.
Lemma D_4ba84 : D! W_4ba84 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_4ba88 : bv 32 := 0x03c41063.
Lemma F_4ba88 : F! 0x4ba88 W_4ba88.
Proof. vm_refl. Qed.
Lemma D_4ba88 : D! W_4ba88 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_4ba8c : bv 32 := 0x028eb883.
Lemma F_4ba8c : F! 0x4ba8c W_4ba8c.
Proof. vm_refl. Qed.
Lemma D_4ba8c : D! W_4ba8c (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_4ba90 : bv 32 := 0x011f7c63.
Lemma F_4ba90 : F! 0x4ba90 W_4ba90.
Proof. vm_refl. Qed.
Lemma D_4ba90 : D! W_4ba90 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_4baa8 : bv 32 := 0x000f8893.
Lemma F_4baa8 : F! 0x4baa8 W_4baa8.
Proof. vm_refl. Qed.
Lemma D_4baa8 : D! W_4baa8 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_4baac : bv 32 := 0xfa9ff06f.
Lemma F_4baac : F! 0x4baac W_4baac.
Proof. vm_refl. Qed.
Lemma D_4baac : D! W_4baac (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_4bab0 : bv 32 := 0x02088c63.
Lemma F_4bab0 : F! 0x4bab0 W_4bab0.
Proof. vm_refl. Qed.
Lemma D_4bab0 : D! W_4bab0 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_4bae8 : bv 32 := 0x0105b603.
Lemma F_4bae8 : F! 0x4bae8 W_4bae8.
Proof. vm_refl. Qed.
Lemma D_4bae8 : D! W_4bae8 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_4baec : bv 32 := 0x0205b683.
Lemma F_4baec : F! 0x4baec W_4baec.
Proof. vm_refl. Qed.
Lemma D_4baec : D! W_4baec (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_4baf0 : bv 32 := 0x0285b503.
Lemma F_4baf0 : F! 0x4baf0 W_4baf0.
Proof. vm_refl. Qed.
Lemma D_4baf0 : D! W_4baf0 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_4baf4 : bv 32 := 0x00c68733.
Lemma F_4baf4 : F! 0x4baf4 W_4baf4.
Proof. vm_refl. Qed.
Lemma D_4baf4 : D! W_4baf4 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_4baf8 : bv 32 := 0xfff50793.
Lemma F_4baf8 : F! 0x4baf8 W_4baf8.
Proof. vm_refl. Qed.
Lemma D_4baf8 : D! W_4baf8 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_4bafc : bv 32 := 0x40e00733.
Lemma F_4bafc : F! 0x4bafc W_4bafc.
Proof. vm_refl. Qed.
Lemma D_4bafc : D! W_4bafc (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_4bb00 : bv 32 := 0x00c7f633.
Lemma F_4bb00 : F! 0x4bb00 W_4bb00.
Proof. vm_refl. Qed.
Lemma D_4bb00 : D! W_4bb00 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_4bb04 : bv 32 := 0x00e7f733.
Lemma F_4bb04 : F! 0x4bb04 W_4bb04.
Proof. vm_refl. Qed.
Lemma D_4bb04 : D! W_4bb04 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_4bb08 : bv 32 := 0x00700793.
Lemma F_4bb08 : F! 0x4bb08 W_4bb08.
Proof. vm_refl. Qed.
Lemma D_4bb08 : D! W_4bb08 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_4bb0c : bv 32 := 0x00d706b3.
Lemma F_4bb0c : F! 0x4bb0c W_4bb0c.
Proof. vm_refl. Qed.
Lemma D_4bb0c : D! W_4bb0c (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_4bb10 : bv 32 := 0x02d5b023.
Lemma F_4bb10 : F! 0x4bb10 W_4bb10.
Proof. vm_refl. Qed.
Lemma D_4bb10 : D! W_4bb10 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_4bb14 : bv 32 := 0x02c5b823.
Lemma F_4bb14 : F! 0x4bb14 W_4bb14.
Proof. vm_refl. Qed.
Lemma D_4bb14 : D! W_4bb14 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_4bb18 : bv 32 := 0x00a7e663.
Lemma F_4bb18 : F! 0x4bb18 W_4bb18.
Proof. vm_refl. Qed.
Lemma D_4bb18 : D! W_4bb18 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_4bb1c : bv 32 := 0x00800513.
Lemma F_4bb1c : F! 0x4bb1c W_4bb1c.
Proof. vm_refl. Qed.
Lemma D_4bb1c : D! W_4bb1c (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_4bb20 : bv 32 := 0x02a5b423.
Lemma F_4bb20 : F! 0x4bb20 W_4bb20.
Proof. vm_refl. Qed.
Lemma D_4bb20 : D! W_4bb20 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_4bb24 : bv 32 := 0x00d60633.
Lemma F_4bb24 : F! 0x4bb24 W_4bb24.
Proof. vm_refl. Qed.
Lemma D_4bb24 : D! W_4bb24 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_4bb28 : bv 32 := 0x000205b7.
Lemma F_4bb28 : F! 0x4bb28 W_4bb28.
Proof. vm_refl. Qed.
Lemma D_4bb28 : D! W_4bb28 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_4bb2c : bv 32 := 0x00a60633.
Lemma F_4bb2c : F! 0x4bb2c W_4bb2c.
Proof. vm_refl. Qed.
Lemma D_4bb2c : D! W_4bb2c (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_4bb30 : bv 32 := 0x0d15869b.
Lemma F_4bb30 : F! 0x4bb30 W_4bb30.
Proof. vm_refl. Qed.
Lemma D_4bb30 : D! W_4bb30 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_4bb34 : bv 32 := 0x0df60593.
Lemma F_4bb34 : F! 0x4bb34 W_4bb34.
Proof. vm_refl. Qed.
Lemma D_4bb34 : D! W_4bb34 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_4bb38 : bv 32 := 0xff85f593.
Lemma F_4bb38 : F! 0x4bb38 W_4bb38.
Proof. vm_refl. Qed.
Lemma D_4bb38 : D! W_4bb38 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_4bb3c : bv 32 := 0x00b4bc23.
Lemma F_4bb3c : F! 0x4bb3c W_4bb3c.
Proof. vm_refl. Qed.
Lemma D_4bb3c : D! W_4bb3c (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_4bb40 : bv 32 := 0x02a4b023.
Lemma F_4bb40 : F! 0x4bb40 W_4bb40.
Proof. vm_refl. Qed.
Lemma D_4bb40 : D! W_4bb40 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_4bb44 : bv 32 := 0x02d5ea63.
Lemma F_4bb44 : F! 0x4bb44 W_4bb44.
Proof. vm_refl. Qed.
Lemma D_4bb44 : D! W_4bb44 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_4bb78 : bv 32 := 0x00025697.
Lemma F_4bb78 : F! 0x4bb78 W_4bb78.
Proof. vm_refl. Qed.
Lemma D_4bb78 : D! W_4bb78 (Auipc 13 37).
Proof. vm_refl. Qed.
Definition W_4bb7c : bv 32 := 0x0104b983.
Lemma F_4bb7c : F! 0x4bb7c W_4bb7c.
Proof. vm_refl. Qed.
Lemma D_4bb7c : D! W_4bb7c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_4bb80 : bv 32 := 0x0284b603.
Lemma F_4bb80 : F! 0x4bb80 W_4bb80.
Proof. vm_refl. Qed.
Lemma D_4bb80 : D! W_4bb80 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_4bb84 : bv 32 := 0xfff50713.
Lemma F_4bb84 : F! 0x4bb84 W_4bb84.
Proof. vm_refl. Qed.
Lemma D_4bb84 : D! W_4bb84 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_4bb88 : bv 32 := 0xf3800793.
Lemma F_4bb88 : F! 0x4bb88 W_4bb88.
Proof. vm_refl. Qed.
Lemma D_4bb88 : D! W_4bb88 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_4bb8c : bv 32 := 0x2f868513.
Lemma F_4bb8c : F! 0x4bb8c W_4bb8c.
Proof. vm_refl. Qed.
Lemma D_4bb8c : D! W_4bb8c (OpImm ALU_ADD 10 13 760).
Proof. vm_refl. Qed.
Definition W_4bb90 : bv 32 := 0x40a787b3.
Lemma F_4bb90 : F! 0x4bb90 W_4bb90.
Proof. vm_refl. Qed.
Lemma D_4bb90 : D! W_4bb90 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_4bb94 : bv 32 := 0x00f77733.
Lemma F_4bb94 : F! 0x4bb94 W_4bb94.
Proof. vm_refl. Qed.
Lemma D_4bb94 : D! W_4bb94 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_4bb98 : bv 32 := 0xfff64693.
Lemma F_4bb98 : F! 0x4bb98 W_4bb98.
Proof. vm_refl. Qed.
Lemma D_4bb98 : D! W_4bb98 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_4bb9c : bv 32 := 0x00e50933.
Lemma F_4bb9c : F! 0x4bb9c W_4bb9c.
Proof. vm_refl. Qed.
Lemma D_4bb9c : D! W_4bb9c (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_4bba0 : bv 32 := 0x00369693.
Lemma F_4bba0 : F! 0x4bba0 W_4bba0.
Proof. vm_refl. Qed.
Lemma D_4bba0 : D! W_4bba0 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_4bba4 : bv 32 := 0x00d506b3.
Lemma F_4bba4 : F! 0x4bba4 W_4bba4.
Proof. vm_refl. Qed.
Lemma D_4bba4 : D! W_4bba4 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_4bba8 : bv 32 := 0x00b68a33.
Lemma F_4bba8 : F! 0x4bba8 W_4bba8.
Proof. vm_refl. Qed.
Lemma D_4bba8 : D! W_4bba8 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_4bbac : bv 32 := 0x0c890413.
Lemma F_4bbac : F! 0x4bbac W_4bbac.
Proof. vm_refl. Qed.
Lemma D_4bbac : D! W_4bbac (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_4bbb0 : bv 32 := 0x04098463.
Lemma F_4bbb0 : F! 0x4bbb0 W_4bbb0.
Proof. vm_refl. Qed.
Lemma D_4bbb0 : D! W_4bbb0 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_4bbf8 : bv 32 := 0x00ca3023.
Lemma F_4bbf8 : F! 0x4bbf8 W_4bbf8.
Proof. vm_refl. Qed.
Lemma D_4bbf8 : D! W_4bbf8 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_4bbfc : bv 32 := 0x0d493023.
Lemma F_4bbfc : F! 0x4bbfc W_4bbfc.
Proof. vm_refl. Qed.
Lemma D_4bbfc : D! W_4bbfc (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_4bc00 : bv 32 := 0x01293023.
Lemma F_4bc00 : F! 0x4bc00 W_4bc00.
Proof. vm_refl. Qed.
Lemma D_4bc00 : D! W_4bc00 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_4bc04 : bv 32 := 0x00040513.
Lemma F_4bc04 : F! 0x4bc04 W_4bc04.
Proof. vm_refl. Qed.
Lemma D_4bc04 : D! W_4bc04 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_4bc08 : bv 32 := 0x23d0e0ef.
Lemma F_4bc08 : F! 0x4bc08 W_4bc08.
Proof. vm_refl. Qed.
Lemma D_4bc08 : D! W_4bc08 (Jal 1 59964).
Proof. vm_refl. Qed.
Definition W_4bc0c : bv 32 := 0x04054a63.
Lemma F_4bc0c : F! 0x4bc0c W_4bc0c.
Proof. vm_refl. Qed.
Lemma D_4bc0c : D! W_4bc0c (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_4bc10 : bv 32 := 0x00051663.
Lemma F_4bc10 : F! 0x4bc10 W_4bc10.
Proof. vm_refl. Qed.
Lemma D_4bc10 : D! W_4bc10 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_4bc14 : bv 32 := 0x00100513.
Lemma F_4bc14 : F! 0x4bc14 W_4bc14.
Proof. vm_refl. Qed.
Lemma D_4bc14 : D! W_4bc14 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_4bc18 : bv 32 := 0x00a48023.
Lemma F_4bc18 : F! 0x4bc18 W_4bc18.
Proof. vm_refl. Qed.
Lemma D_4bc18 : D! W_4bc18 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_4bc1c : bv 32 := 0x00200513.
Lemma F_4bc1c : F! 0x4bc1c W_4bc1c.
Proof. vm_refl. Qed.
Lemma D_4bc1c : D! W_4bc1c (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_4bc20 : bv 32 := 0x00045597.
Lemma F_4bc20 : F! 0x4bc20 W_4bc20.
Proof. vm_refl. Qed.
Lemma D_4bc20 : D! W_4bc20 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_4bc24 : bv 32 := 0x02a92423.
Lemma F_4bc24 : F! 0x4bc24 W_4bc24.
Proof. vm_refl. Qed.
Lemma D_4bc24 : D! W_4bc24 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_4bc28 : bv 32 := 0x06000893.
Lemma F_4bc28 : F! 0x4bc28 W_4bc28.
Proof. vm_refl. Qed.
Lemma D_4bc28 : D! W_4bc28 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_4bc2c : bv 32 := 0x32058513.
Lemma F_4bc2c : F! 0x4bc2c W_4bc2c.
Proof. vm_refl. Qed.
Lemma D_4bc2c : D! W_4bc2c (OpImm ALU_ADD 10 11 800).
Proof. vm_refl. Qed.
Definition W_4bc30 : bv 32 := 0x03848593.
Lemma F_4bc30 : F! 0x4bc30 W_4bc30.
Proof. vm_refl. Qed.
Lemma D_4bc30 : D! W_4bc30 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_4bc34 : bv 32 := 0x00000073.
Lemma F_4bc34 : F! 0x4bc34 W_4bc34.
Proof. vm_refl. Qed.
Lemma E_4bc34 : is_ecall W_4bc34 = true.
Proof. reflexivity. Qed.
Definition W_4bc38 : bv 32 := 0x07890613.
Lemma F_4bc38 : F! 0x4bc38 W_4bc38.
Proof. vm_refl. Qed.
Lemma D_4bc38 : D! W_4bc38 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_4bc3c : bv 32 := 0x02a92023.
Lemma F_4bc3c : F! 0x4bc3c W_4bc3c.
Proof. vm_refl. Qed.
Lemma D_4bc3c : D! W_4bc3c (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_4bc40 : bv 32 := 0x08b93c23.
Lemma F_4bc40 : F! 0x4bc40 W_4bc40.
Proof. vm_refl. Qed.
Lemma D_4bc40 : D! W_4bc40 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_4bc44 : bv 32 := 0x06c93c23.
Lemma F_4bc44 : F! 0x4bc44 W_4bc44.
Proof. vm_refl. Qed.
Lemma D_4bc44 : D! W_4bc44 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_4bc48 : bv 32 := 0x00045517.
Lemma F_4bc48 : F! 0x4bc48 W_4bc48.
Proof. vm_refl. Qed.
Lemma D_4bc48 : D! W_4bc48 (Auipc 10 69).
Proof. vm_refl. Qed.
Definition W_4bc4c : bv 32 := 0x56853503.
Lemma F_4bc4c : F! 0x4bc4c W_4bc4c.
Proof. vm_refl. Qed.
Lemma D_4bc4c : D! W_4bc4c (Load SZ8 true 10 10 1384).
Proof. vm_refl. Qed.
Definition W_4bc50 : bv 32 := 0x01293423.
Lemma F_4bc50 : F! 0x4bc50 W_4bc50.
Proof. vm_refl. Qed.
Lemma D_4bc50 : D! W_4bc50 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_4bc54 : bv 32 := 0x01293823.
Lemma F_4bc54 : F! 0x4bc54 W_4bc54.
Proof. vm_refl. Qed.
Lemma D_4bc54 : D! W_4bc54 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_4bc58 : bv 32 := 0x00a93c23.
Lemma F_4bc58 : F! 0x4bc58 W_4bc58.
Proof. vm_refl. Qed.
Lemma D_4bc58 : D! W_4bc58 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_4bc5c : bv 32 := 0x0080006f.
Lemma F_4bc5c : F! 0x4bc5c W_4bc5c.
Proof. vm_refl. Qed.
Lemma D_4bc5c : D! W_4bc5c (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_4bc64 : bv 32 := 0x03813083.
Lemma F_4bc64 : F! 0x4bc64 W_4bc64.
Proof. vm_refl. Qed.
Lemma D_4bc64 : D! W_4bc64 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_4bc68 : bv 32 := 0x03013403.
Lemma F_4bc68 : F! 0x4bc68 W_4bc68.
Proof. vm_refl. Qed.
Lemma D_4bc68 : D! W_4bc68 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_4bc6c : bv 32 := 0x02813483.
Lemma F_4bc6c : F! 0x4bc6c W_4bc6c.
Proof. vm_refl. Qed.
Lemma D_4bc6c : D! W_4bc6c (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_4bc70 : bv 32 := 0x02013903.
Lemma F_4bc70 : F! 0x4bc70 W_4bc70.
Proof. vm_refl. Qed.
Lemma D_4bc70 : D! W_4bc70 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_4bc74 : bv 32 := 0x01813983.
Lemma F_4bc74 : F! 0x4bc74 W_4bc74.
Proof. vm_refl. Qed.
Lemma D_4bc74 : D! W_4bc74 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_4bc78 : bv 32 := 0x01013a03.
Lemma F_4bc78 : F! 0x4bc78 W_4bc78.
Proof. vm_refl. Qed.
Lemma D_4bc78 : D! W_4bc78 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_4bc7c : bv 32 := 0x00813a83.
Lemma F_4bc7c : F! 0x4bc7c W_4bc7c.
Proof. vm_refl. Qed.
Lemma D_4bc7c : D! W_4bc7c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_4bc80 : bv 32 := 0x04010113.
Lemma F_4bc80 : F! 0x4bc80 W_4bc80.
Proof. vm_refl. Qed.
Lemma D_4bc80 : D! W_4bc80 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_4bc84 : bv 32 := 0x00008067.
Lemma F_4bc84 : F! 0x4bc84 W_4bc84.
Proof. vm_refl. Qed.
Lemma D_4bc84 : D! W_4bc84 (Jalr 0 1 0).
Proof. vm_refl. Qed.
