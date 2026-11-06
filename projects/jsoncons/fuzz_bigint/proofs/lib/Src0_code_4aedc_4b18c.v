(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
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
Definition W_4aedc : bv 32 := 0xfc010113.
Lemma F_4aedc : F! 0x4aedc W_4aedc.
Proof. vm_refl. Qed.
Lemma D_4aedc : D! W_4aedc (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_4aee0 : bv 32 := 0x02113c23.
Lemma F_4aee0 : F! 0x4aee0 W_4aee0.
Proof. vm_refl. Qed.
Lemma D_4aee0 : D! W_4aee0 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_4aee4 : bv 32 := 0x02813823.
Lemma F_4aee4 : F! 0x4aee4 W_4aee4.
Proof. vm_refl. Qed.
Lemma D_4aee4 : D! W_4aee4 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_4aee8 : bv 32 := 0x02913423.
Lemma F_4aee8 : F! 0x4aee8 W_4aee8.
Proof. vm_refl. Qed.
Lemma D_4aee8 : D! W_4aee8 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_4aeec : bv 32 := 0x03213023.
Lemma F_4aeec : F! 0x4aeec W_4aeec.
Proof. vm_refl. Qed.
Lemma D_4aeec : D! W_4aeec (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_4aef0 : bv 32 := 0x01313c23.
Lemma F_4aef0 : F! 0x4aef0 W_4aef0.
Proof. vm_refl. Qed.
Lemma D_4aef0 : D! W_4aef0 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_4aef4 : bv 32 := 0x01413823.
Lemma F_4aef4 : F! 0x4aef4 W_4aef4.
Proof. vm_refl. Qed.
Lemma D_4aef4 : D! W_4aef4 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_4aef8 : bv 32 := 0x01513423.
Lemma F_4aef8 : F! 0x4aef8 W_4aef8.
Proof. vm_refl. Qed.
Lemma D_4aef8 : D! W_4aef8 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_4aefc : bv 32 := 0x02853683.
Lemma F_4aefc : F! 0x4aefc W_4aefc.
Proof. vm_refl. Qed.
Lemma D_4aefc : D! W_4aefc (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_4af00 : bv 32 := 0x00045597.
Lemma F_4af00 : F! 0x4af00 W_4af00.
Proof. vm_refl. Qed.
Lemma D_4af00 : D! W_4af00 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_4af04 : bv 32 := 0x54058593.
Lemma F_4af04 : F! 0x4af04 W_4af04.
Proof. vm_refl. Qed.
Lemma D_4af04 : D! W_4af04 (OpImm ALU_ADD 11 11 1344).
Proof. vm_refl. Qed.
Definition W_4af08 : bv 32 := 0x00045617.
Lemma F_4af08 : F! 0x4af08 W_4af08.
Proof. vm_refl. Qed.
Lemma D_4af08 : D! W_4af08 (Auipc 12 69).
Proof. vm_refl. Qed.
Definition W_4af0c : bv 32 := 0x7c060493.
Lemma F_4af0c : F! 0x4af0c W_4af0c.
Proof. vm_refl. Qed.
Lemma D_4af0c : D! W_4af0c (OpImm ALU_ADD 9 12 1984).
Proof. vm_refl. Qed.
Definition W_4af10 : bv 32 := 0x0c068e63.
Lemma F_4af10 : F! 0x4af10 W_4af10.
Proof. vm_refl. Qed.
Lemma D_4af10 : D! W_4af10 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_4af14 : bv 32 := 0x00000613.
Lemma F_4af14 : F! 0x4af14 W_4af14.
Proof. vm_refl. Qed.
Lemma D_4af14 : D! W_4af14 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_4af18 : bv 32 := 0x00000893.
Lemma F_4af18 : F! 0x4af18 W_4af18.
Proof. vm_refl. Qed.
Lemma D_4af18 : D! W_4af18 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_4af1c : bv 32 := 0x00015717.
Lemma F_4af1c : F! 0x4af1c W_4af1c.
Proof. vm_refl. Qed.
Lemma D_4af1c : D! W_4af1c (Auipc 14 21).
Proof. vm_refl. Qed.
Definition W_4af20 : bv 32 := 0x01853783.
Lemma F_4af20 : F! 0x4af20 W_4af20.
Proof. vm_refl. Qed.
Lemma D_4af20 : D! W_4af20 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_4af24 : bv 32 := 0x02053503.
Lemma F_4af24 : F! 0x4af24 W_4af24.
Proof. vm_refl. Qed.
Lemma D_4af24 : D! W_4af24 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_4af28 : bv 32 := 0x00600813.
Lemma F_4af28 : F! 0x4af28 W_4af28.
Proof. vm_refl. Qed.
Lemma D_4af28 : D! W_4af28 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_4af2c : bv 32 := 0x00013297.
Lemma F_4af2c : F! 0x4af2c W_4af2c.
Proof. vm_refl. Qed.
Lemma D_4af2c : D! W_4af2c (Auipc 5 19).
Proof. vm_refl. Qed.
Definition W_4af30 : bv 32 := 0x94476f03.
Lemma F_4af30 : F! 0x4af30 W_4af30.
Proof. vm_refl. Qed.
Lemma D_4af30 : D! W_4af30 (Load SZ4 false 30 14 2372).
Proof. vm_refl. Qed.
Definition W_4af34 : bv 32 := 0x5742b283.
Lemma F_4af34 : F! 0x4af34 W_4af34.
Proof. vm_refl. Qed.
Lemma D_4af34 : D! W_4af34 (Load SZ8 true 5 5 1396).
Proof. vm_refl. Qed.
Definition W_4af38 : bv 32 := 0x00200313.
Lemma F_4af38 : F! 0x4af38 W_4af38.
Proof. vm_refl. Qed.
Lemma D_4af38 : D! W_4af38 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_4af3c : bv 32 := 0x00700393.
Lemma F_4af3c : F! 0x4af3c W_4af3c.
Proof. vm_refl. Qed.
Lemma D_4af3c : D! W_4af3c (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_4af40 : bv 32 := 0x6474ee37.
Lemma F_4af40 : F! 0x4af40 W_4af40.
Proof. vm_refl. Qed.
Lemma D_4af40 : D! W_4af40 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_4af44 : bv 32 := 0x551e0e1b.
Lemma F_4af44 : F! 0x4af44 W_4af44.
Proof. vm_refl. Qed.
Lemma D_4af44 : D! W_4af44 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_4af48 : bv 32 := 0x00078e93.
Lemma F_4af48 : F! 0x4af48 W_4af48.
Proof. vm_refl. Qed.
Lemma D_4af48 : D! W_4af48 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_4af4c : bv 32 := 0x0180006f.
Lemma F_4af4c : F! 0x4af4c W_4af4c.
Proof. vm_refl. Qed.
Lemma D_4af4c : D! W_4af4c (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_4af50 : bv 32 := 0x010eb603.
Lemma F_4af50 : F! 0x4af50 W_4af50.
Proof. vm_refl. Qed.
Lemma D_4af50 : D! W_4af50 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_4af54 : bv 32 := 0x40c78633.
Lemma F_4af54 : F! 0x4af54 W_4af54.
Proof. vm_refl. Qed.
Lemma D_4af54 : D! W_4af54 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_4af58 : bv 32 := 0xfff68693.
Lemma F_4af58 : F! 0x4af58 W_4af58.
Proof. vm_refl. Qed.
Lemma D_4af58 : D! W_4af58 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_4af5c : bv 32 := 0x00ae8eb3.
Lemma F_4af5c : F! 0x4af5c W_4af5c.
Proof. vm_refl. Qed.
Lemma D_4af5c : D! W_4af5c (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_4af60 : bv 32 := 0x04068a63.
Lemma F_4af60 : F! 0x4af60 W_4af60.
Proof. vm_refl. Qed.
Lemma D_4af60 : D! W_4af60 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_4af64 : bv 32 := 0x000ea403.
Lemma F_4af64 : F! 0x4af64 W_4af64.
Proof. vm_refl. Qed.
Lemma D_4af64 : D! W_4af64 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_4af68 : bv 32 := 0xff0404e3.
Lemma F_4af68 : F! 0x4af68 W_4af68.
Proof. vm_refl. Qed.
Lemma D_4af68 : D! W_4af68 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_4af6c : bv 32 := 0x00028a63.
Lemma F_4af6c : F! 0x4af6c W_4af6c.
Proof. vm_refl. Qed.
Lemma D_4af6c : D! W_4af6c (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_4af80 : bv 32 := 0x000e8f93.
Lemma F_4af80 : F! 0x4af80 W_4af80.
Proof. vm_refl. Qed.
Lemma D_4af80 : D! W_4af80 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_4af84 : bv 32 := 0x00740463.
Lemma F_4af84 : F! 0x4af84 W_4af84.
Proof. vm_refl. Qed.
Lemma D_4af84 : D! W_4af84 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_4af88 : bv 32 := 0x00088f93.
Lemma F_4af88 : F! 0x4af88 W_4af88.
Proof. vm_refl. Qed.
Lemma D_4af88 : D! W_4af88 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_4af8c : bv 32 := 0x03c41063.
Lemma F_4af8c : F! 0x4af8c W_4af8c.
Proof. vm_refl. Qed.
Lemma D_4af8c : D! W_4af8c (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_4af90 : bv 32 := 0x028eb883.
Lemma F_4af90 : F! 0x4af90 W_4af90.
Proof. vm_refl. Qed.
Lemma D_4af90 : D! W_4af90 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_4af94 : bv 32 := 0x011f7c63.
Lemma F_4af94 : F! 0x4af94 W_4af94.
Proof. vm_refl. Qed.
Lemma D_4af94 : D! W_4af94 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_4afac : bv 32 := 0x000f8893.
Lemma F_4afac : F! 0x4afac W_4afac.
Proof. vm_refl. Qed.
Lemma D_4afac : D! W_4afac (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_4afb0 : bv 32 := 0xfa9ff06f.
Lemma F_4afb0 : F! 0x4afb0 W_4afb0.
Proof. vm_refl. Qed.
Lemma D_4afb0 : D! W_4afb0 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_4afb4 : bv 32 := 0x02088c63.
Lemma F_4afb4 : F! 0x4afb4 W_4afb4.
Proof. vm_refl. Qed.
Lemma D_4afb4 : D! W_4afb4 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_4afec : bv 32 := 0x0105b603.
Lemma F_4afec : F! 0x4afec W_4afec.
Proof. vm_refl. Qed.
Lemma D_4afec : D! W_4afec (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_4aff0 : bv 32 := 0x0205b683.
Lemma F_4aff0 : F! 0x4aff0 W_4aff0.
Proof. vm_refl. Qed.
Lemma D_4aff0 : D! W_4aff0 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_4aff4 : bv 32 := 0x0285b503.
Lemma F_4aff4 : F! 0x4aff4 W_4aff4.
Proof. vm_refl. Qed.
Lemma D_4aff4 : D! W_4aff4 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_4aff8 : bv 32 := 0x00c68733.
Lemma F_4aff8 : F! 0x4aff8 W_4aff8.
Proof. vm_refl. Qed.
Lemma D_4aff8 : D! W_4aff8 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_4affc : bv 32 := 0xfff50793.
Lemma F_4affc : F! 0x4affc W_4affc.
Proof. vm_refl. Qed.
Lemma D_4affc : D! W_4affc (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_4b000 : bv 32 := 0x40e00733.
Lemma F_4b000 : F! 0x4b000 W_4b000.
Proof. vm_refl. Qed.
Lemma D_4b000 : D! W_4b000 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_4b004 : bv 32 := 0x00c7f633.
Lemma F_4b004 : F! 0x4b004 W_4b004.
Proof. vm_refl. Qed.
Lemma D_4b004 : D! W_4b004 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_4b008 : bv 32 := 0x00e7f733.
Lemma F_4b008 : F! 0x4b008 W_4b008.
Proof. vm_refl. Qed.
Lemma D_4b008 : D! W_4b008 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_4b00c : bv 32 := 0x00700793.
Lemma F_4b00c : F! 0x4b00c W_4b00c.
Proof. vm_refl. Qed.
Lemma D_4b00c : D! W_4b00c (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_4b010 : bv 32 := 0x00d706b3.
Lemma F_4b010 : F! 0x4b010 W_4b010.
Proof. vm_refl. Qed.
Lemma D_4b010 : D! W_4b010 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_4b014 : bv 32 := 0x02d5b023.
Lemma F_4b014 : F! 0x4b014 W_4b014.
Proof. vm_refl. Qed.
Lemma D_4b014 : D! W_4b014 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_4b018 : bv 32 := 0x02c5b823.
Lemma F_4b018 : F! 0x4b018 W_4b018.
Proof. vm_refl. Qed.
Lemma D_4b018 : D! W_4b018 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_4b01c : bv 32 := 0x00a7e663.
Lemma F_4b01c : F! 0x4b01c W_4b01c.
Proof. vm_refl. Qed.
Lemma D_4b01c : D! W_4b01c (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_4b020 : bv 32 := 0x00800513.
Lemma F_4b020 : F! 0x4b020 W_4b020.
Proof. vm_refl. Qed.
Lemma D_4b020 : D! W_4b020 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_4b024 : bv 32 := 0x02a5b423.
Lemma F_4b024 : F! 0x4b024 W_4b024.
Proof. vm_refl. Qed.
Lemma D_4b024 : D! W_4b024 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_4b028 : bv 32 := 0x00d60633.
Lemma F_4b028 : F! 0x4b028 W_4b028.
Proof. vm_refl. Qed.
Lemma D_4b028 : D! W_4b028 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_4b02c : bv 32 := 0x000205b7.
Lemma F_4b02c : F! 0x4b02c W_4b02c.
Proof. vm_refl. Qed.
Lemma D_4b02c : D! W_4b02c (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_4b030 : bv 32 := 0x00a60633.
Lemma F_4b030 : F! 0x4b030 W_4b030.
Proof. vm_refl. Qed.
Lemma D_4b030 : D! W_4b030 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_4b034 : bv 32 := 0x0d15869b.
Lemma F_4b034 : F! 0x4b034 W_4b034.
Proof. vm_refl. Qed.
Lemma D_4b034 : D! W_4b034 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_4b038 : bv 32 := 0x0df60593.
Lemma F_4b038 : F! 0x4b038 W_4b038.
Proof. vm_refl. Qed.
Lemma D_4b038 : D! W_4b038 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_4b03c : bv 32 := 0xff85f593.
Lemma F_4b03c : F! 0x4b03c W_4b03c.
Proof. vm_refl. Qed.
Lemma D_4b03c : D! W_4b03c (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_4b040 : bv 32 := 0x00b4bc23.
Lemma F_4b040 : F! 0x4b040 W_4b040.
Proof. vm_refl. Qed.
Lemma D_4b040 : D! W_4b040 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_4b044 : bv 32 := 0x02a4b023.
Lemma F_4b044 : F! 0x4b044 W_4b044.
Proof. vm_refl. Qed.
Lemma D_4b044 : D! W_4b044 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_4b048 : bv 32 := 0x02d5ea63.
Lemma F_4b048 : F! 0x4b048 W_4b048.
Proof. vm_refl. Qed.
Lemma D_4b048 : D! W_4b048 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_4b07c : bv 32 := 0x00025697.
Lemma F_4b07c : F! 0x4b07c W_4b07c.
Proof. vm_refl. Qed.
Lemma D_4b07c : D! W_4b07c (Auipc 13 37).
Proof. vm_refl. Qed.
Definition W_4b080 : bv 32 := 0x0104b983.
Lemma F_4b080 : F! 0x4b080 W_4b080.
Proof. vm_refl. Qed.
Lemma D_4b080 : D! W_4b080 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_4b084 : bv 32 := 0x0284b603.
Lemma F_4b084 : F! 0x4b084 W_4b084.
Proof. vm_refl. Qed.
Lemma D_4b084 : D! W_4b084 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_4b088 : bv 32 := 0xfff50713.
Lemma F_4b088 : F! 0x4b088 W_4b088.
Proof. vm_refl. Qed.
Lemma D_4b088 : D! W_4b088 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_4b08c : bv 32 := 0xf3800793.
Lemma F_4b08c : F! 0x4b08c W_4b08c.
Proof. vm_refl. Qed.
Lemma D_4b08c : D! W_4b08c (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_4b090 : bv 32 := 0x2f468513.
Lemma F_4b090 : F! 0x4b090 W_4b090.
Proof. vm_refl. Qed.
Lemma D_4b090 : D! W_4b090 (OpImm ALU_ADD 10 13 756).
Proof. vm_refl. Qed.
Definition W_4b094 : bv 32 := 0x40a787b3.
Lemma F_4b094 : F! 0x4b094 W_4b094.
Proof. vm_refl. Qed.
Lemma D_4b094 : D! W_4b094 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_4b098 : bv 32 := 0x00f77733.
Lemma F_4b098 : F! 0x4b098 W_4b098.
Proof. vm_refl. Qed.
Lemma D_4b098 : D! W_4b098 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_4b09c : bv 32 := 0xfff64693.
Lemma F_4b09c : F! 0x4b09c W_4b09c.
Proof. vm_refl. Qed.
Lemma D_4b09c : D! W_4b09c (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_4b0a0 : bv 32 := 0x00e50933.
Lemma F_4b0a0 : F! 0x4b0a0 W_4b0a0.
Proof. vm_refl. Qed.
Lemma D_4b0a0 : D! W_4b0a0 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_4b0a4 : bv 32 := 0x00369693.
Lemma F_4b0a4 : F! 0x4b0a4 W_4b0a4.
Proof. vm_refl. Qed.
Lemma D_4b0a4 : D! W_4b0a4 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_4b0a8 : bv 32 := 0x00d506b3.
Lemma F_4b0a8 : F! 0x4b0a8 W_4b0a8.
Proof. vm_refl. Qed.
Lemma D_4b0a8 : D! W_4b0a8 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_4b0ac : bv 32 := 0x00b68a33.
Lemma F_4b0ac : F! 0x4b0ac W_4b0ac.
Proof. vm_refl. Qed.
Lemma D_4b0ac : D! W_4b0ac (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_4b0b0 : bv 32 := 0x0c890413.
Lemma F_4b0b0 : F! 0x4b0b0 W_4b0b0.
Proof. vm_refl. Qed.
Lemma D_4b0b0 : D! W_4b0b0 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_4b0b4 : bv 32 := 0x04098463.
Lemma F_4b0b4 : F! 0x4b0b4 W_4b0b4.
Proof. vm_refl. Qed.
Lemma D_4b0b4 : D! W_4b0b4 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_4b0fc : bv 32 := 0x00ca3023.
Lemma F_4b0fc : F! 0x4b0fc W_4b0fc.
Proof. vm_refl. Qed.
Lemma D_4b0fc : D! W_4b0fc (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_4b100 : bv 32 := 0x0d493023.
Lemma F_4b100 : F! 0x4b100 W_4b100.
Proof. vm_refl. Qed.
Lemma D_4b100 : D! W_4b100 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_4b104 : bv 32 := 0x01293023.
Lemma F_4b104 : F! 0x4b104 W_4b104.
Proof. vm_refl. Qed.
Lemma D_4b104 : D! W_4b104 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_4b108 : bv 32 := 0x00040513.
Lemma F_4b108 : F! 0x4b108 W_4b108.
Proof. vm_refl. Qed.
Lemma D_4b108 : D! W_4b108 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_4b10c : bv 32 := 0x23d0e0ef.
Lemma F_4b10c : F! 0x4b10c W_4b10c.
Proof. vm_refl. Qed.
Lemma D_4b10c : D! W_4b10c (Jal 1 59964).
Proof. vm_refl. Qed.
Definition W_4b110 : bv 32 := 0x04054a63.
Lemma F_4b110 : F! 0x4b110 W_4b110.
Proof. vm_refl. Qed.
Lemma D_4b110 : D! W_4b110 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_4b114 : bv 32 := 0x00051663.
Lemma F_4b114 : F! 0x4b114 W_4b114.
Proof. vm_refl. Qed.
Lemma D_4b114 : D! W_4b114 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_4b118 : bv 32 := 0x00100513.
Lemma F_4b118 : F! 0x4b118 W_4b118.
Proof. vm_refl. Qed.
Lemma D_4b118 : D! W_4b118 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_4b11c : bv 32 := 0x00a48023.
Lemma F_4b11c : F! 0x4b11c W_4b11c.
Proof. vm_refl. Qed.
Lemma D_4b11c : D! W_4b11c (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_4b120 : bv 32 := 0x00200513.
Lemma F_4b120 : F! 0x4b120 W_4b120.
Proof. vm_refl. Qed.
Lemma D_4b120 : D! W_4b120 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_4b124 : bv 32 := 0x00045597.
Lemma F_4b124 : F! 0x4b124 W_4b124.
Proof. vm_refl. Qed.
Lemma D_4b124 : D! W_4b124 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_4b128 : bv 32 := 0x02a92423.
Lemma F_4b128 : F! 0x4b128 W_4b128.
Proof. vm_refl. Qed.
Lemma D_4b128 : D! W_4b128 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_4b12c : bv 32 := 0x06000893.
Lemma F_4b12c : F! 0x4b12c W_4b12c.
Proof. vm_refl. Qed.
Lemma D_4b12c : D! W_4b12c (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_4b130 : bv 32 := 0x31c58513.
Lemma F_4b130 : F! 0x4b130 W_4b130.
Proof. vm_refl. Qed.
Lemma D_4b130 : D! W_4b130 (OpImm ALU_ADD 10 11 796).
Proof. vm_refl. Qed.
Definition W_4b134 : bv 32 := 0x03848593.
Lemma F_4b134 : F! 0x4b134 W_4b134.
Proof. vm_refl. Qed.
Lemma D_4b134 : D! W_4b134 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_4b138 : bv 32 := 0x00000073.
Lemma F_4b138 : F! 0x4b138 W_4b138.
Proof. vm_refl. Qed.
Lemma E_4b138 : is_ecall W_4b138 = true.
Proof. reflexivity. Qed.
Definition W_4b13c : bv 32 := 0x07890613.
Lemma F_4b13c : F! 0x4b13c W_4b13c.
Proof. vm_refl. Qed.
Lemma D_4b13c : D! W_4b13c (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_4b140 : bv 32 := 0x02a92023.
Lemma F_4b140 : F! 0x4b140 W_4b140.
Proof. vm_refl. Qed.
Lemma D_4b140 : D! W_4b140 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_4b144 : bv 32 := 0x08b93c23.
Lemma F_4b144 : F! 0x4b144 W_4b144.
Proof. vm_refl. Qed.
Lemma D_4b144 : D! W_4b144 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_4b148 : bv 32 := 0x06c93c23.
Lemma F_4b148 : F! 0x4b148 W_4b148.
Proof. vm_refl. Qed.
Lemma D_4b148 : D! W_4b148 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_4b14c : bv 32 := 0x00045517.
Lemma F_4b14c : F! 0x4b14c W_4b14c.
Proof. vm_refl. Qed.
Lemma D_4b14c : D! W_4b14c (Auipc 10 69).
Proof. vm_refl. Qed.
Definition W_4b150 : bv 32 := 0x56453503.
Lemma F_4b150 : F! 0x4b150 W_4b150.
Proof. vm_refl. Qed.
Lemma D_4b150 : D! W_4b150 (Load SZ8 true 10 10 1380).
Proof. vm_refl. Qed.
Definition W_4b154 : bv 32 := 0x01293423.
Lemma F_4b154 : F! 0x4b154 W_4b154.
Proof. vm_refl. Qed.
Lemma D_4b154 : D! W_4b154 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_4b158 : bv 32 := 0x01293823.
Lemma F_4b158 : F! 0x4b158 W_4b158.
Proof. vm_refl. Qed.
Lemma D_4b158 : D! W_4b158 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_4b15c : bv 32 := 0x00a93c23.
Lemma F_4b15c : F! 0x4b15c W_4b15c.
Proof. vm_refl. Qed.
Lemma D_4b15c : D! W_4b15c (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_4b160 : bv 32 := 0x0080006f.
Lemma F_4b160 : F! 0x4b160 W_4b160.
Proof. vm_refl. Qed.
Lemma D_4b160 : D! W_4b160 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_4b168 : bv 32 := 0x03813083.
Lemma F_4b168 : F! 0x4b168 W_4b168.
Proof. vm_refl. Qed.
Lemma D_4b168 : D! W_4b168 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_4b16c : bv 32 := 0x03013403.
Lemma F_4b16c : F! 0x4b16c W_4b16c.
Proof. vm_refl. Qed.
Lemma D_4b16c : D! W_4b16c (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_4b170 : bv 32 := 0x02813483.
Lemma F_4b170 : F! 0x4b170 W_4b170.
Proof. vm_refl. Qed.
Lemma D_4b170 : D! W_4b170 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_4b174 : bv 32 := 0x02013903.
Lemma F_4b174 : F! 0x4b174 W_4b174.
Proof. vm_refl. Qed.
Lemma D_4b174 : D! W_4b174 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_4b178 : bv 32 := 0x01813983.
Lemma F_4b178 : F! 0x4b178 W_4b178.
Proof. vm_refl. Qed.
Lemma D_4b178 : D! W_4b178 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_4b17c : bv 32 := 0x01013a03.
Lemma F_4b17c : F! 0x4b17c W_4b17c.
Proof. vm_refl. Qed.
Lemma D_4b17c : D! W_4b17c (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_4b180 : bv 32 := 0x00813a83.
Lemma F_4b180 : F! 0x4b180 W_4b180.
Proof. vm_refl. Qed.
Lemma D_4b180 : D! W_4b180 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_4b184 : bv 32 := 0x04010113.
Lemma F_4b184 : F! 0x4b184 W_4b184.
Proof. vm_refl. Qed.
Lemma D_4b184 : D! W_4b184 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_4b188 : bv 32 := 0x00008067.
Lemma F_4b188 : F! 0x4b188 W_4b188.
Proof. vm_refl. Qed.
Lemma D_4b188 : D! W_4b188 (Jalr 0 1 0).
Proof. vm_refl. Qed.
