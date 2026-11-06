(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
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
Definition W_1b598 : bv 32 := 0xfc010113.
Lemma F_1b598 : F! 0x1b598 W_1b598.
Proof. vm_refl. Qed.
Lemma D_1b598 : D! W_1b598 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_1b59c : bv 32 := 0x02113c23.
Lemma F_1b59c : F! 0x1b59c W_1b59c.
Proof. vm_refl. Qed.
Lemma D_1b59c : D! W_1b59c (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_1b5a0 : bv 32 := 0x02813823.
Lemma F_1b5a0 : F! 0x1b5a0 W_1b5a0.
Proof. vm_refl. Qed.
Lemma D_1b5a0 : D! W_1b5a0 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_1b5a4 : bv 32 := 0x02913423.
Lemma F_1b5a4 : F! 0x1b5a4 W_1b5a4.
Proof. vm_refl. Qed.
Lemma D_1b5a4 : D! W_1b5a4 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_1b5a8 : bv 32 := 0x03213023.
Lemma F_1b5a8 : F! 0x1b5a8 W_1b5a8.
Proof. vm_refl. Qed.
Lemma D_1b5a8 : D! W_1b5a8 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_1b5ac : bv 32 := 0x01313c23.
Lemma F_1b5ac : F! 0x1b5ac W_1b5ac.
Proof. vm_refl. Qed.
Lemma D_1b5ac : D! W_1b5ac (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_1b5b0 : bv 32 := 0x01413823.
Lemma F_1b5b0 : F! 0x1b5b0 W_1b5b0.
Proof. vm_refl. Qed.
Lemma D_1b5b0 : D! W_1b5b0 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_1b5b4 : bv 32 := 0x01513423.
Lemma F_1b5b4 : F! 0x1b5b4 W_1b5b4.
Proof. vm_refl. Qed.
Lemma D_1b5b4 : D! W_1b5b4 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_1b5b8 : bv 32 := 0x02853683.
Lemma F_1b5b8 : F! 0x1b5b8 W_1b5b8.
Proof. vm_refl. Qed.
Lemma D_1b5b8 : D! W_1b5b8 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_1b5bc : bv 32 := 0x0003b597.
Lemma F_1b5bc : F! 0x1b5bc W_1b5bc.
Proof. vm_refl. Qed.
Lemma D_1b5bc : D! W_1b5bc (Auipc 11 59).
Proof. vm_refl. Qed.
Definition W_1b5c0 : bv 32 := 0x1fc58593.
Lemma F_1b5c0 : F! 0x1b5c0 W_1b5c0.
Proof. vm_refl. Qed.
Lemma D_1b5c0 : D! W_1b5c0 (OpImm ALU_ADD 11 11 508).
Proof. vm_refl. Qed.
Definition W_1b5c4 : bv 32 := 0x0003b617.
Lemma F_1b5c4 : F! 0x1b5c4 W_1b5c4.
Proof. vm_refl. Qed.
Lemma D_1b5c4 : D! W_1b5c4 (Auipc 12 59).
Proof. vm_refl. Qed.
Definition W_1b5c8 : bv 32 := 0x47460493.
Lemma F_1b5c8 : F! 0x1b5c8 W_1b5c8.
Proof. vm_refl. Qed.
Lemma D_1b5c8 : D! W_1b5c8 (OpImm ALU_ADD 9 12 1140).
Proof. vm_refl. Qed.
Definition W_1b5cc : bv 32 := 0x0c068e63.
Lemma F_1b5cc : F! 0x1b5cc W_1b5cc.
Proof. vm_refl. Qed.
Lemma D_1b5cc : D! W_1b5cc (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_1b5d0 : bv 32 := 0x00000613.
Lemma F_1b5d0 : F! 0x1b5d0 W_1b5d0.
Proof. vm_refl. Qed.
Lemma D_1b5d0 : D! W_1b5d0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_1b5d4 : bv 32 := 0x00000893.
Lemma F_1b5d4 : F! 0x1b5d4 W_1b5d4.
Proof. vm_refl. Qed.
Lemma D_1b5d4 : D! W_1b5d4 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_1b5d8 : bv 32 := 0x0000b717.
Lemma F_1b5d8 : F! 0x1b5d8 W_1b5d8.
Proof. vm_refl. Qed.
Lemma D_1b5d8 : D! W_1b5d8 (Auipc 14 11).
Proof. vm_refl. Qed.
Definition W_1b5dc : bv 32 := 0x01853783.
Lemma F_1b5dc : F! 0x1b5dc W_1b5dc.
Proof. vm_refl. Qed.
Lemma D_1b5dc : D! W_1b5dc (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_1b5e0 : bv 32 := 0x02053503.
Lemma F_1b5e0 : F! 0x1b5e0 W_1b5e0.
Proof. vm_refl. Qed.
Lemma D_1b5e0 : D! W_1b5e0 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_1b5e4 : bv 32 := 0x00600813.
Lemma F_1b5e4 : F! 0x1b5e4 W_1b5e4.
Proof. vm_refl. Qed.
Lemma D_1b5e4 : D! W_1b5e4 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_1b5e8 : bv 32 := 0x0000a297.
Lemma F_1b5e8 : F! 0x1b5e8 W_1b5e8.
Proof. vm_refl. Qed.
Lemma D_1b5e8 : D! W_1b5e8 (Auipc 5 10).
Proof. vm_refl. Qed.
Definition W_1b5ec : bv 32 := 0x06076f03.
Lemma F_1b5ec : F! 0x1b5ec W_1b5ec.
Proof. vm_refl. Qed.
Lemma D_1b5ec : D! W_1b5ec (Load SZ4 false 30 14 96).
Proof. vm_refl. Qed.
Definition W_1b5f0 : bv 32 := 0xcc02b283.
Lemma F_1b5f0 : F! 0x1b5f0 W_1b5f0.
Proof. vm_refl. Qed.
Lemma D_1b5f0 : D! W_1b5f0 (Load SZ8 true 5 5 3264).
Proof. vm_refl. Qed.
Definition W_1b5f4 : bv 32 := 0x00200313.
Lemma F_1b5f4 : F! 0x1b5f4 W_1b5f4.
Proof. vm_refl. Qed.
Lemma D_1b5f4 : D! W_1b5f4 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_1b5f8 : bv 32 := 0x00700393.
Lemma F_1b5f8 : F! 0x1b5f8 W_1b5f8.
Proof. vm_refl. Qed.
Lemma D_1b5f8 : D! W_1b5f8 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_1b5fc : bv 32 := 0x6474ee37.
Lemma F_1b5fc : F! 0x1b5fc W_1b5fc.
Proof. vm_refl. Qed.
Lemma D_1b5fc : D! W_1b5fc (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_1b600 : bv 32 := 0x551e0e1b.
Lemma F_1b600 : F! 0x1b600 W_1b600.
Proof. vm_refl. Qed.
Lemma D_1b600 : D! W_1b600 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_1b604 : bv 32 := 0x00078e93.
Lemma F_1b604 : F! 0x1b604 W_1b604.
Proof. vm_refl. Qed.
Lemma D_1b604 : D! W_1b604 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_1b608 : bv 32 := 0x0180006f.
Lemma F_1b608 : F! 0x1b608 W_1b608.
Proof. vm_refl. Qed.
Lemma D_1b608 : D! W_1b608 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_1b60c : bv 32 := 0x010eb603.
Lemma F_1b60c : F! 0x1b60c W_1b60c.
Proof. vm_refl. Qed.
Lemma D_1b60c : D! W_1b60c (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_1b610 : bv 32 := 0x40c78633.
Lemma F_1b610 : F! 0x1b610 W_1b610.
Proof. vm_refl. Qed.
Lemma D_1b610 : D! W_1b610 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_1b614 : bv 32 := 0xfff68693.
Lemma F_1b614 : F! 0x1b614 W_1b614.
Proof. vm_refl. Qed.
Lemma D_1b614 : D! W_1b614 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_1b618 : bv 32 := 0x00ae8eb3.
Lemma F_1b618 : F! 0x1b618 W_1b618.
Proof. vm_refl. Qed.
Lemma D_1b618 : D! W_1b618 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_1b61c : bv 32 := 0x04068a63.
Lemma F_1b61c : F! 0x1b61c W_1b61c.
Proof. vm_refl. Qed.
Lemma D_1b61c : D! W_1b61c (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_1b620 : bv 32 := 0x000ea403.
Lemma F_1b620 : F! 0x1b620 W_1b620.
Proof. vm_refl. Qed.
Lemma D_1b620 : D! W_1b620 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_1b624 : bv 32 := 0xff0404e3.
Lemma F_1b624 : F! 0x1b624 W_1b624.
Proof. vm_refl. Qed.
Lemma D_1b624 : D! W_1b624 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_1b628 : bv 32 := 0x00028a63.
Lemma F_1b628 : F! 0x1b628 W_1b628.
Proof. vm_refl. Qed.
Lemma D_1b628 : D! W_1b628 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_1b63c : bv 32 := 0x000e8f93.
Lemma F_1b63c : F! 0x1b63c W_1b63c.
Proof. vm_refl. Qed.
Lemma D_1b63c : D! W_1b63c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_1b640 : bv 32 := 0x00740463.
Lemma F_1b640 : F! 0x1b640 W_1b640.
Proof. vm_refl. Qed.
Lemma D_1b640 : D! W_1b640 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_1b644 : bv 32 := 0x00088f93.
Lemma F_1b644 : F! 0x1b644 W_1b644.
Proof. vm_refl. Qed.
Lemma D_1b644 : D! W_1b644 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_1b648 : bv 32 := 0x03c41063.
Lemma F_1b648 : F! 0x1b648 W_1b648.
Proof. vm_refl. Qed.
Lemma D_1b648 : D! W_1b648 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_1b64c : bv 32 := 0x028eb883.
Lemma F_1b64c : F! 0x1b64c W_1b64c.
Proof. vm_refl. Qed.
Lemma D_1b64c : D! W_1b64c (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_1b650 : bv 32 := 0x011f7c63.
Lemma F_1b650 : F! 0x1b650 W_1b650.
Proof. vm_refl. Qed.
Lemma D_1b650 : D! W_1b650 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_1b668 : bv 32 := 0x000f8893.
Lemma F_1b668 : F! 0x1b668 W_1b668.
Proof. vm_refl. Qed.
Lemma D_1b668 : D! W_1b668 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_1b66c : bv 32 := 0xfa9ff06f.
Lemma F_1b66c : F! 0x1b66c W_1b66c.
Proof. vm_refl. Qed.
Lemma D_1b66c : D! W_1b66c (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_1b670 : bv 32 := 0x02088c63.
Lemma F_1b670 : F! 0x1b670 W_1b670.
Proof. vm_refl. Qed.
Lemma D_1b670 : D! W_1b670 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_1b6a8 : bv 32 := 0x0105b603.
Lemma F_1b6a8 : F! 0x1b6a8 W_1b6a8.
Proof. vm_refl. Qed.
Lemma D_1b6a8 : D! W_1b6a8 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_1b6ac : bv 32 := 0x0205b683.
Lemma F_1b6ac : F! 0x1b6ac W_1b6ac.
Proof. vm_refl. Qed.
Lemma D_1b6ac : D! W_1b6ac (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_1b6b0 : bv 32 := 0x0285b503.
Lemma F_1b6b0 : F! 0x1b6b0 W_1b6b0.
Proof. vm_refl. Qed.
Lemma D_1b6b0 : D! W_1b6b0 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_1b6b4 : bv 32 := 0x00c68733.
Lemma F_1b6b4 : F! 0x1b6b4 W_1b6b4.
Proof. vm_refl. Qed.
Lemma D_1b6b4 : D! W_1b6b4 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_1b6b8 : bv 32 := 0xfff50793.
Lemma F_1b6b8 : F! 0x1b6b8 W_1b6b8.
Proof. vm_refl. Qed.
Lemma D_1b6b8 : D! W_1b6b8 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_1b6bc : bv 32 := 0x40e00733.
Lemma F_1b6bc : F! 0x1b6bc W_1b6bc.
Proof. vm_refl. Qed.
Lemma D_1b6bc : D! W_1b6bc (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_1b6c0 : bv 32 := 0x00c7f633.
Lemma F_1b6c0 : F! 0x1b6c0 W_1b6c0.
Proof. vm_refl. Qed.
Lemma D_1b6c0 : D! W_1b6c0 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_1b6c4 : bv 32 := 0x00e7f733.
Lemma F_1b6c4 : F! 0x1b6c4 W_1b6c4.
Proof. vm_refl. Qed.
Lemma D_1b6c4 : D! W_1b6c4 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_1b6c8 : bv 32 := 0x00700793.
Lemma F_1b6c8 : F! 0x1b6c8 W_1b6c8.
Proof. vm_refl. Qed.
Lemma D_1b6c8 : D! W_1b6c8 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_1b6cc : bv 32 := 0x00d706b3.
Lemma F_1b6cc : F! 0x1b6cc W_1b6cc.
Proof. vm_refl. Qed.
Lemma D_1b6cc : D! W_1b6cc (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_1b6d0 : bv 32 := 0x02d5b023.
Lemma F_1b6d0 : F! 0x1b6d0 W_1b6d0.
Proof. vm_refl. Qed.
Lemma D_1b6d0 : D! W_1b6d0 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_1b6d4 : bv 32 := 0x02c5b823.
Lemma F_1b6d4 : F! 0x1b6d4 W_1b6d4.
Proof. vm_refl. Qed.
Lemma D_1b6d4 : D! W_1b6d4 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_1b6d8 : bv 32 := 0x00a7e663.
Lemma F_1b6d8 : F! 0x1b6d8 W_1b6d8.
Proof. vm_refl. Qed.
Lemma D_1b6d8 : D! W_1b6d8 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_1b6dc : bv 32 := 0x00800513.
Lemma F_1b6dc : F! 0x1b6dc W_1b6dc.
Proof. vm_refl. Qed.
Lemma D_1b6dc : D! W_1b6dc (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_1b6e0 : bv 32 := 0x02a5b423.
Lemma F_1b6e0 : F! 0x1b6e0 W_1b6e0.
Proof. vm_refl. Qed.
Lemma D_1b6e0 : D! W_1b6e0 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_1b6e4 : bv 32 := 0x00d60633.
Lemma F_1b6e4 : F! 0x1b6e4 W_1b6e4.
Proof. vm_refl. Qed.
Lemma D_1b6e4 : D! W_1b6e4 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_1b6e8 : bv 32 := 0x000205b7.
Lemma F_1b6e8 : F! 0x1b6e8 W_1b6e8.
Proof. vm_refl. Qed.
Lemma D_1b6e8 : D! W_1b6e8 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_1b6ec : bv 32 := 0x00a60633.
Lemma F_1b6ec : F! 0x1b6ec W_1b6ec.
Proof. vm_refl. Qed.
Lemma D_1b6ec : D! W_1b6ec (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_1b6f0 : bv 32 := 0x0d15869b.
Lemma F_1b6f0 : F! 0x1b6f0 W_1b6f0.
Proof. vm_refl. Qed.
Lemma D_1b6f0 : D! W_1b6f0 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_1b6f4 : bv 32 := 0x0df60593.
Lemma F_1b6f4 : F! 0x1b6f4 W_1b6f4.
Proof. vm_refl. Qed.
Lemma D_1b6f4 : D! W_1b6f4 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_1b6f8 : bv 32 := 0xff85f593.
Lemma F_1b6f8 : F! 0x1b6f8 W_1b6f8.
Proof. vm_refl. Qed.
Lemma D_1b6f8 : D! W_1b6f8 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_1b6fc : bv 32 := 0x00b4bc23.
Lemma F_1b6fc : F! 0x1b6fc W_1b6fc.
Proof. vm_refl. Qed.
Lemma D_1b6fc : D! W_1b6fc (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_1b700 : bv 32 := 0x02a4b023.
Lemma F_1b700 : F! 0x1b700 W_1b700.
Proof. vm_refl. Qed.
Lemma D_1b700 : D! W_1b700 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_1b704 : bv 32 := 0x02d5ea63.
Lemma F_1b704 : F! 0x1b704 W_1b704.
Proof. vm_refl. Qed.
Lemma D_1b704 : D! W_1b704 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_1b738 : bv 32 := 0x0001b697.
Lemma F_1b738 : F! 0x1b738 W_1b738.
Proof. vm_refl. Qed.
Lemma D_1b738 : D! W_1b738 (Auipc 13 27).
Proof. vm_refl. Qed.
Definition W_1b73c : bv 32 := 0x0104b983.
Lemma F_1b73c : F! 0x1b73c W_1b73c.
Proof. vm_refl. Qed.
Lemma D_1b73c : D! W_1b73c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_1b740 : bv 32 := 0x0284b603.
Lemma F_1b740 : F! 0x1b740 W_1b740.
Proof. vm_refl. Qed.
Lemma D_1b740 : D! W_1b740 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_1b744 : bv 32 := 0xfff50713.
Lemma F_1b744 : F! 0x1b744 W_1b744.
Proof. vm_refl. Qed.
Lemma D_1b744 : D! W_1b744 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_1b748 : bv 32 := 0xf3800793.
Lemma F_1b748 : F! 0x1b748 W_1b748.
Proof. vm_refl. Qed.
Lemma D_1b748 : D! W_1b748 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_1b74c : bv 32 := 0xfb068513.
Lemma F_1b74c : F! 0x1b74c W_1b74c.
Proof. vm_refl. Qed.
Lemma D_1b74c : D! W_1b74c (OpImm ALU_ADD 10 13 4016).
Proof. vm_refl. Qed.
Definition W_1b750 : bv 32 := 0x40a787b3.
Lemma F_1b750 : F! 0x1b750 W_1b750.
Proof. vm_refl. Qed.
Lemma D_1b750 : D! W_1b750 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_1b754 : bv 32 := 0x00f77733.
Lemma F_1b754 : F! 0x1b754 W_1b754.
Proof. vm_refl. Qed.
Lemma D_1b754 : D! W_1b754 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_1b758 : bv 32 := 0xfff64693.
Lemma F_1b758 : F! 0x1b758 W_1b758.
Proof. vm_refl. Qed.
Lemma D_1b758 : D! W_1b758 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_1b75c : bv 32 := 0x00e50933.
Lemma F_1b75c : F! 0x1b75c W_1b75c.
Proof. vm_refl. Qed.
Lemma D_1b75c : D! W_1b75c (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_1b760 : bv 32 := 0x00369693.
Lemma F_1b760 : F! 0x1b760 W_1b760.
Proof. vm_refl. Qed.
Lemma D_1b760 : D! W_1b760 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_1b764 : bv 32 := 0x00d506b3.
Lemma F_1b764 : F! 0x1b764 W_1b764.
Proof. vm_refl. Qed.
Lemma D_1b764 : D! W_1b764 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_1b768 : bv 32 := 0x00b68a33.
Lemma F_1b768 : F! 0x1b768 W_1b768.
Proof. vm_refl. Qed.
Lemma D_1b768 : D! W_1b768 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_1b76c : bv 32 := 0x0c890413.
Lemma F_1b76c : F! 0x1b76c W_1b76c.
Proof. vm_refl. Qed.
Lemma D_1b76c : D! W_1b76c (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_1b770 : bv 32 := 0x04098463.
Lemma F_1b770 : F! 0x1b770 W_1b770.
Proof. vm_refl. Qed.
Lemma D_1b770 : D! W_1b770 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_1b7b8 : bv 32 := 0x00ca3023.
Lemma F_1b7b8 : F! 0x1b7b8 W_1b7b8.
Proof. vm_refl. Qed.
Lemma D_1b7b8 : D! W_1b7b8 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_1b7bc : bv 32 := 0x0d493023.
Lemma F_1b7bc : F! 0x1b7bc W_1b7bc.
Proof. vm_refl. Qed.
Lemma D_1b7bc : D! W_1b7bc (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_1b7c0 : bv 32 := 0x01293023.
Lemma F_1b7c0 : F! 0x1b7c0 W_1b7c0.
Proof. vm_refl. Qed.
Lemma D_1b7c0 : D! W_1b7c0 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_1b7c4 : bv 32 := 0x00040513.
Lemma F_1b7c4 : F! 0x1b7c4 W_1b7c4.
Proof. vm_refl. Qed.
Lemma D_1b7c4 : D! W_1b7c4 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_1b7c8 : bv 32 := 0x1b9080ef.
Lemma F_1b7c8 : F! 0x1b7c8 W_1b7c8.
Proof. vm_refl. Qed.
Lemma D_1b7c8 : D! W_1b7c8 (Jal 1 35256).
Proof. vm_refl. Qed.
Definition W_1b7cc : bv 32 := 0x04054a63.
Lemma F_1b7cc : F! 0x1b7cc W_1b7cc.
Proof. vm_refl. Qed.
Lemma D_1b7cc : D! W_1b7cc (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_1b7d0 : bv 32 := 0x00051663.
Lemma F_1b7d0 : F! 0x1b7d0 W_1b7d0.
Proof. vm_refl. Qed.
Lemma D_1b7d0 : D! W_1b7d0 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_1b7d4 : bv 32 := 0x00100513.
Lemma F_1b7d4 : F! 0x1b7d4 W_1b7d4.
Proof. vm_refl. Qed.
Lemma D_1b7d4 : D! W_1b7d4 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_1b7d8 : bv 32 := 0x00a48023.
Lemma F_1b7d8 : F! 0x1b7d8 W_1b7d8.
Proof. vm_refl. Qed.
Lemma D_1b7d8 : D! W_1b7d8 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_1b7dc : bv 32 := 0x00200513.
Lemma F_1b7dc : F! 0x1b7dc W_1b7dc.
Proof. vm_refl. Qed.
Lemma D_1b7dc : D! W_1b7dc (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_1b7e0 : bv 32 := 0x0003b597.
Lemma F_1b7e0 : F! 0x1b7e0 W_1b7e0.
Proof. vm_refl. Qed.
Lemma D_1b7e0 : D! W_1b7e0 (Auipc 11 59).
Proof. vm_refl. Qed.
Definition W_1b7e4 : bv 32 := 0x02a92423.
Lemma F_1b7e4 : F! 0x1b7e4 W_1b7e4.
Proof. vm_refl. Qed.
Lemma D_1b7e4 : D! W_1b7e4 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_1b7e8 : bv 32 := 0x06000893.
Lemma F_1b7e8 : F! 0x1b7e8 W_1b7e8.
Proof. vm_refl. Qed.
Lemma D_1b7e8 : D! W_1b7e8 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_1b7ec : bv 32 := 0xfd858513.
Lemma F_1b7ec : F! 0x1b7ec W_1b7ec.
Proof. vm_refl. Qed.
Lemma D_1b7ec : D! W_1b7ec (OpImm ALU_ADD 10 11 4056).
Proof. vm_refl. Qed.
Definition W_1b7f0 : bv 32 := 0x03848593.
Lemma F_1b7f0 : F! 0x1b7f0 W_1b7f0.
Proof. vm_refl. Qed.
Lemma D_1b7f0 : D! W_1b7f0 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_1b7f4 : bv 32 := 0x00000073.
Lemma F_1b7f4 : F! 0x1b7f4 W_1b7f4.
Proof. vm_refl. Qed.
Lemma E_1b7f4 : is_ecall W_1b7f4 = true.
Proof. reflexivity. Qed.
Definition W_1b7f8 : bv 32 := 0x07890613.
Lemma F_1b7f8 : F! 0x1b7f8 W_1b7f8.
Proof. vm_refl. Qed.
Lemma D_1b7f8 : D! W_1b7f8 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_1b7fc : bv 32 := 0x02a92023.
Lemma F_1b7fc : F! 0x1b7fc W_1b7fc.
Proof. vm_refl. Qed.
Lemma D_1b7fc : D! W_1b7fc (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_1b800 : bv 32 := 0x08b93c23.
Lemma F_1b800 : F! 0x1b800 W_1b800.
Proof. vm_refl. Qed.
Lemma D_1b800 : D! W_1b800 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_1b804 : bv 32 := 0x06c93c23.
Lemma F_1b804 : F! 0x1b804 W_1b804.
Proof. vm_refl. Qed.
Lemma D_1b804 : D! W_1b804 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_1b808 : bv 32 := 0x0003b517.
Lemma F_1b808 : F! 0x1b808 W_1b808.
Proof. vm_refl. Qed.
Lemma D_1b808 : D! W_1b808 (Auipc 10 59).
Proof. vm_refl. Qed.
Definition W_1b80c : bv 32 := 0x21853503.
Lemma F_1b80c : F! 0x1b80c W_1b80c.
Proof. vm_refl. Qed.
Lemma D_1b80c : D! W_1b80c (Load SZ8 true 10 10 536).
Proof. vm_refl. Qed.
Definition W_1b810 : bv 32 := 0x01293423.
Lemma F_1b810 : F! 0x1b810 W_1b810.
Proof. vm_refl. Qed.
Lemma D_1b810 : D! W_1b810 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_1b814 : bv 32 := 0x01293823.
Lemma F_1b814 : F! 0x1b814 W_1b814.
Proof. vm_refl. Qed.
Lemma D_1b814 : D! W_1b814 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_1b818 : bv 32 := 0x00a93c23.
Lemma F_1b818 : F! 0x1b818 W_1b818.
Proof. vm_refl. Qed.
Lemma D_1b818 : D! W_1b818 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_1b81c : bv 32 := 0x0080006f.
Lemma F_1b81c : F! 0x1b81c W_1b81c.
Proof. vm_refl. Qed.
Lemma D_1b81c : D! W_1b81c (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_1b824 : bv 32 := 0x03813083.
Lemma F_1b824 : F! 0x1b824 W_1b824.
Proof. vm_refl. Qed.
Lemma D_1b824 : D! W_1b824 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_1b828 : bv 32 := 0x03013403.
Lemma F_1b828 : F! 0x1b828 W_1b828.
Proof. vm_refl. Qed.
Lemma D_1b828 : D! W_1b828 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_1b82c : bv 32 := 0x02813483.
Lemma F_1b82c : F! 0x1b82c W_1b82c.
Proof. vm_refl. Qed.
Lemma D_1b82c : D! W_1b82c (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_1b830 : bv 32 := 0x02013903.
Lemma F_1b830 : F! 0x1b830 W_1b830.
Proof. vm_refl. Qed.
Lemma D_1b830 : D! W_1b830 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_1b834 : bv 32 := 0x01813983.
Lemma F_1b834 : F! 0x1b834 W_1b834.
Proof. vm_refl. Qed.
Lemma D_1b834 : D! W_1b834 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_1b838 : bv 32 := 0x01013a03.
Lemma F_1b838 : F! 0x1b838 W_1b838.
Proof. vm_refl. Qed.
Lemma D_1b838 : D! W_1b838 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_1b83c : bv 32 := 0x00813a83.
Lemma F_1b83c : F! 0x1b83c W_1b83c.
Proof. vm_refl. Qed.
Lemma D_1b83c : D! W_1b83c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_1b840 : bv 32 := 0x04010113.
Lemma F_1b840 : F! 0x1b840 W_1b840.
Proof. vm_refl. Qed.
Lemma D_1b840 : D! W_1b840 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_1b844 : bv 32 := 0x00008067.
Lemma F_1b844 : F! 0x1b844 W_1b844.
Proof. vm_refl. Qed.
Lemma D_1b844 : D! W_1b844 (Jalr 0 1 0).
Proof. vm_refl. Qed.
