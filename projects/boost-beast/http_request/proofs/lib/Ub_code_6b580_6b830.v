(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
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
Definition W_6b580 : bv 32 := 0xfc010113.
Lemma F_6b580 : F! 0x6b580 W_6b580.
Proof. vm_refl. Qed.
Lemma D_6b580 : D! W_6b580 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_6b584 : bv 32 := 0x02113c23.
Lemma F_6b584 : F! 0x6b584 W_6b584.
Proof. vm_refl. Qed.
Lemma D_6b584 : D! W_6b584 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_6b588 : bv 32 := 0x02813823.
Lemma F_6b588 : F! 0x6b588 W_6b588.
Proof. vm_refl. Qed.
Lemma D_6b588 : D! W_6b588 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_6b58c : bv 32 := 0x02913423.
Lemma F_6b58c : F! 0x6b58c W_6b58c.
Proof. vm_refl. Qed.
Lemma D_6b58c : D! W_6b58c (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_6b590 : bv 32 := 0x03213023.
Lemma F_6b590 : F! 0x6b590 W_6b590.
Proof. vm_refl. Qed.
Lemma D_6b590 : D! W_6b590 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_6b594 : bv 32 := 0x01313c23.
Lemma F_6b594 : F! 0x6b594 W_6b594.
Proof. vm_refl. Qed.
Lemma D_6b594 : D! W_6b594 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_6b598 : bv 32 := 0x01413823.
Lemma F_6b598 : F! 0x6b598 W_6b598.
Proof. vm_refl. Qed.
Lemma D_6b598 : D! W_6b598 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_6b59c : bv 32 := 0x01513423.
Lemma F_6b59c : F! 0x6b59c W_6b59c.
Proof. vm_refl. Qed.
Lemma D_6b59c : D! W_6b59c (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_6b5a0 : bv 32 := 0x02853683.
Lemma F_6b5a0 : F! 0x6b5a0 W_6b5a0.
Proof. vm_refl. Qed.
Lemma D_6b5a0 : D! W_6b5a0 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_6b5a4 : bv 32 := 0x0004b597.
Lemma F_6b5a4 : F! 0x6b5a4 W_6b5a4.
Proof. vm_refl. Qed.
Lemma D_6b5a4 : D! W_6b5a4 (Auipc 11 75).
Proof. vm_refl. Qed.
Definition W_6b5a8 : bv 32 := 0x3d458593.
Lemma F_6b5a8 : F! 0x6b5a8 W_6b5a8.
Proof. vm_refl. Qed.
Lemma D_6b5a8 : D! W_6b5a8 (OpImm ALU_ADD 11 11 980).
Proof. vm_refl. Qed.
Definition W_6b5ac : bv 32 := 0x0004b617.
Lemma F_6b5ac : F! 0x6b5ac W_6b5ac.
Proof. vm_refl. Qed.
Lemma D_6b5ac : D! W_6b5ac (Auipc 12 75).
Proof. vm_refl. Qed.
Definition W_6b5b0 : bv 32 := 0x65460493.
Lemma F_6b5b0 : F! 0x6b5b0 W_6b5b0.
Proof. vm_refl. Qed.
Lemma D_6b5b0 : D! W_6b5b0 (OpImm ALU_ADD 9 12 1620).
Proof. vm_refl. Qed.
Definition W_6b5b4 : bv 32 := 0x0c068e63.
Lemma F_6b5b4 : F! 0x6b5b4 W_6b5b4.
Proof. vm_refl. Qed.
Lemma D_6b5b4 : D! W_6b5b4 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_6b5b8 : bv 32 := 0x00000613.
Lemma F_6b5b8 : F! 0x6b5b8 W_6b5b8.
Proof. vm_refl. Qed.
Lemma D_6b5b8 : D! W_6b5b8 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_6b5bc : bv 32 := 0x00000893.
Lemma F_6b5bc : F! 0x6b5bc W_6b5bc.
Proof. vm_refl. Qed.
Lemma D_6b5bc : D! W_6b5bc (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_6b5c0 : bv 32 := 0x0001a717.
Lemma F_6b5c0 : F! 0x6b5c0 W_6b5c0.
Proof. vm_refl. Qed.
Lemma D_6b5c0 : D! W_6b5c0 (Auipc 14 26).
Proof. vm_refl. Qed.
Definition W_6b5c4 : bv 32 := 0x01853783.
Lemma F_6b5c4 : F! 0x6b5c4 W_6b5c4.
Proof. vm_refl. Qed.
Lemma D_6b5c4 : D! W_6b5c4 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_6b5c8 : bv 32 := 0x02053503.
Lemma F_6b5c8 : F! 0x6b5c8 W_6b5c8.
Proof. vm_refl. Qed.
Lemma D_6b5c8 : D! W_6b5c8 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_6b5cc : bv 32 := 0x00600813.
Lemma F_6b5cc : F! 0x6b5cc W_6b5cc.
Proof. vm_refl. Qed.
Lemma D_6b5cc : D! W_6b5cc (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_6b5d0 : bv 32 := 0x00018297.
Lemma F_6b5d0 : F! 0x6b5d0 W_6b5d0.
Proof. vm_refl. Qed.
Lemma D_6b5d0 : D! W_6b5d0 (Auipc 5 24).
Proof. vm_refl. Qed.
Definition W_6b5d4 : bv 32 := 0x96876f03.
Lemma F_6b5d4 : F! 0x6b5d4 W_6b5d4.
Proof. vm_refl. Qed.
Lemma D_6b5d4 : D! W_6b5d4 (Load SZ4 false 30 14 2408).
Proof. vm_refl. Qed.
Definition W_6b5d8 : bv 32 := 0x4302b283.
Lemma F_6b5d8 : F! 0x6b5d8 W_6b5d8.
Proof. vm_refl. Qed.
Lemma D_6b5d8 : D! W_6b5d8 (Load SZ8 true 5 5 1072).
Proof. vm_refl. Qed.
Definition W_6b5dc : bv 32 := 0x00200313.
Lemma F_6b5dc : F! 0x6b5dc W_6b5dc.
Proof. vm_refl. Qed.
Lemma D_6b5dc : D! W_6b5dc (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_6b5e0 : bv 32 := 0x00700393.
Lemma F_6b5e0 : F! 0x6b5e0 W_6b5e0.
Proof. vm_refl. Qed.
Lemma D_6b5e0 : D! W_6b5e0 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_6b5e4 : bv 32 := 0x6474ee37.
Lemma F_6b5e4 : F! 0x6b5e4 W_6b5e4.
Proof. vm_refl. Qed.
Lemma D_6b5e4 : D! W_6b5e4 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_6b5e8 : bv 32 := 0x551e0e1b.
Lemma F_6b5e8 : F! 0x6b5e8 W_6b5e8.
Proof. vm_refl. Qed.
Lemma D_6b5e8 : D! W_6b5e8 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_6b5ec : bv 32 := 0x00078e93.
Lemma F_6b5ec : F! 0x6b5ec W_6b5ec.
Proof. vm_refl. Qed.
Lemma D_6b5ec : D! W_6b5ec (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_6b5f0 : bv 32 := 0x0180006f.
Lemma F_6b5f0 : F! 0x6b5f0 W_6b5f0.
Proof. vm_refl. Qed.
Lemma D_6b5f0 : D! W_6b5f0 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_6b5f4 : bv 32 := 0x010eb603.
Lemma F_6b5f4 : F! 0x6b5f4 W_6b5f4.
Proof. vm_refl. Qed.
Lemma D_6b5f4 : D! W_6b5f4 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_6b5f8 : bv 32 := 0x40c78633.
Lemma F_6b5f8 : F! 0x6b5f8 W_6b5f8.
Proof. vm_refl. Qed.
Lemma D_6b5f8 : D! W_6b5f8 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_6b5fc : bv 32 := 0xfff68693.
Lemma F_6b5fc : F! 0x6b5fc W_6b5fc.
Proof. vm_refl. Qed.
Lemma D_6b5fc : D! W_6b5fc (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_6b600 : bv 32 := 0x00ae8eb3.
Lemma F_6b600 : F! 0x6b600 W_6b600.
Proof. vm_refl. Qed.
Lemma D_6b600 : D! W_6b600 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_6b604 : bv 32 := 0x04068a63.
Lemma F_6b604 : F! 0x6b604 W_6b604.
Proof. vm_refl. Qed.
Lemma D_6b604 : D! W_6b604 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_6b608 : bv 32 := 0x000ea403.
Lemma F_6b608 : F! 0x6b608 W_6b608.
Proof. vm_refl. Qed.
Lemma D_6b608 : D! W_6b608 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_6b60c : bv 32 := 0xff0404e3.
Lemma F_6b60c : F! 0x6b60c W_6b60c.
Proof. vm_refl. Qed.
Lemma D_6b60c : D! W_6b60c (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_6b610 : bv 32 := 0x00028a63.
Lemma F_6b610 : F! 0x6b610 W_6b610.
Proof. vm_refl. Qed.
Lemma D_6b610 : D! W_6b610 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_6b624 : bv 32 := 0x000e8f93.
Lemma F_6b624 : F! 0x6b624 W_6b624.
Proof. vm_refl. Qed.
Lemma D_6b624 : D! W_6b624 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_6b628 : bv 32 := 0x00740463.
Lemma F_6b628 : F! 0x6b628 W_6b628.
Proof. vm_refl. Qed.
Lemma D_6b628 : D! W_6b628 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_6b62c : bv 32 := 0x00088f93.
Lemma F_6b62c : F! 0x6b62c W_6b62c.
Proof. vm_refl. Qed.
Lemma D_6b62c : D! W_6b62c (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_6b630 : bv 32 := 0x03c41063.
Lemma F_6b630 : F! 0x6b630 W_6b630.
Proof. vm_refl. Qed.
Lemma D_6b630 : D! W_6b630 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_6b634 : bv 32 := 0x028eb883.
Lemma F_6b634 : F! 0x6b634 W_6b634.
Proof. vm_refl. Qed.
Lemma D_6b634 : D! W_6b634 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_6b638 : bv 32 := 0x011f7c63.
Lemma F_6b638 : F! 0x6b638 W_6b638.
Proof. vm_refl. Qed.
Lemma D_6b638 : D! W_6b638 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_6b650 : bv 32 := 0x000f8893.
Lemma F_6b650 : F! 0x6b650 W_6b650.
Proof. vm_refl. Qed.
Lemma D_6b650 : D! W_6b650 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_6b654 : bv 32 := 0xfa9ff06f.
Lemma F_6b654 : F! 0x6b654 W_6b654.
Proof. vm_refl. Qed.
Lemma D_6b654 : D! W_6b654 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_6b658 : bv 32 := 0x02088c63.
Lemma F_6b658 : F! 0x6b658 W_6b658.
Proof. vm_refl. Qed.
Lemma D_6b658 : D! W_6b658 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_6b65c : bv 32 := 0x00858713.
Lemma F_6b65c : F! 0x6b65c W_6b65c.
Proof. vm_refl. Qed.
Lemma D_6b65c : D! W_6b65c (OpImm ALU_ADD 14 11 8).
Proof. vm_refl. Qed.
Definition W_6b660 : bv 32 := 0x0108b783.
Lemma F_6b660 : F! 0x6b660 W_6b660.
Proof. vm_refl. Qed.
Lemma D_6b660 : D! W_6b660 (Load SZ8 true 15 17 16).
Proof. vm_refl. Qed.
Definition W_6b664 : bv 32 := 0x0208b803.
Lemma F_6b664 : F! 0x6b664 W_6b664.
Proof. vm_refl. Qed.
Lemma D_6b664 : D! W_6b664 (Load SZ8 true 16 17 32).
Proof. vm_refl. Qed.
Definition W_6b668 : bv 32 := 0x0288b683.
Lemma F_6b668 : F! 0x6b668 W_6b668.
Proof. vm_refl. Qed.
Lemma D_6b668 : D! W_6b668 (Load SZ8 true 13 17 40).
Proof. vm_refl. Qed.
Definition W_6b66c : bv 32 := 0x0308b503.
Lemma F_6b66c : F! 0x6b66c W_6b66c.
Proof. vm_refl. Qed.
Lemma D_6b66c : D! W_6b66c (Load SZ8 true 10 17 48).
Proof. vm_refl. Qed.
Definition W_6b670 : bv 32 := 0x00c78633.
Lemma F_6b670 : F! 0x6b670 W_6b670.
Proof. vm_refl. Qed.
Lemma D_6b670 : D! W_6b670 (Op ALU_ADD 12 15 12).
Proof. vm_refl. Qed.
Definition W_6b674 : bv 32 := 0x00100793.
Lemma F_6b674 : F! 0x6b674 W_6b674.
Proof. vm_refl. Qed.
Lemma D_6b674 : D! W_6b674 (OpImm ALU_ADD 15 0 1).
Proof. vm_refl. Qed.
Definition W_6b678 : bv 32 := 0x00c5b823.
Lemma F_6b678 : F! 0x6b678 W_6b678.
Proof. vm_refl. Qed.
Lemma D_6b678 : D! W_6b678 (Store SZ8 11 12 16).
Proof. vm_refl. Qed.
Definition W_6b67c : bv 32 := 0x0105bc23.
Lemma F_6b67c : F! 0x6b67c W_6b67c.
Proof. vm_refl. Qed.
Lemma D_6b67c : D! W_6b67c (Store SZ8 11 16 24).
Proof. vm_refl. Qed.
Definition W_6b680 : bv 32 := 0x02a5b423.
Lemma F_6b680 : F! 0x6b680 W_6b680.
Proof. vm_refl. Qed.
Lemma D_6b680 : D! W_6b680 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_6b684 : bv 32 := 0x00e4b823.
Lemma F_6b684 : F! 0x6b684 W_6b684.
Proof. vm_refl. Qed.
Lemma D_6b684 : D! W_6b684 (Store SZ8 9 14 16).
Proof. vm_refl. Qed.
Definition W_6b688 : bv 32 := 0x02f4b423.
Lemma F_6b688 : F! 0x6b688 W_6b688.
Proof. vm_refl. Qed.
Lemma D_6b688 : D! W_6b688 (Store SZ8 9 15 40).
Proof. vm_refl. Qed.
Definition W_6b68c : bv 32 := 0x0100006f.
Lemma F_6b68c : F! 0x6b68c W_6b68c.
Proof. vm_refl. Qed.
Lemma D_6b68c : D! W_6b68c (Jal 0 16).
Proof. vm_refl. Qed.
Definition W_6b69c : bv 32 := 0x00c68733.
Lemma F_6b69c : F! 0x6b69c W_6b69c.
Proof. vm_refl. Qed.
Lemma D_6b69c : D! W_6b69c (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_6b6a0 : bv 32 := 0xfff50793.
Lemma F_6b6a0 : F! 0x6b6a0 W_6b6a0.
Proof. vm_refl. Qed.
Lemma D_6b6a0 : D! W_6b6a0 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_6b6a4 : bv 32 := 0x40e00733.
Lemma F_6b6a4 : F! 0x6b6a4 W_6b6a4.
Proof. vm_refl. Qed.
Lemma D_6b6a4 : D! W_6b6a4 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_6b6a8 : bv 32 := 0x00c7f633.
Lemma F_6b6a8 : F! 0x6b6a8 W_6b6a8.
Proof. vm_refl. Qed.
Lemma D_6b6a8 : D! W_6b6a8 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_6b6ac : bv 32 := 0x00e7f733.
Lemma F_6b6ac : F! 0x6b6ac W_6b6ac.
Proof. vm_refl. Qed.
Lemma D_6b6ac : D! W_6b6ac (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_6b6b0 : bv 32 := 0x00700793.
Lemma F_6b6b0 : F! 0x6b6b0 W_6b6b0.
Proof. vm_refl. Qed.
Lemma D_6b6b0 : D! W_6b6b0 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_6b6b4 : bv 32 := 0x00d706b3.
Lemma F_6b6b4 : F! 0x6b6b4 W_6b6b4.
Proof. vm_refl. Qed.
Lemma D_6b6b4 : D! W_6b6b4 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_6b6b8 : bv 32 := 0x02d5b023.
Lemma F_6b6b8 : F! 0x6b6b8 W_6b6b8.
Proof. vm_refl. Qed.
Lemma D_6b6b8 : D! W_6b6b8 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_6b6bc : bv 32 := 0x02c5b823.
Lemma F_6b6bc : F! 0x6b6bc W_6b6bc.
Proof. vm_refl. Qed.
Lemma D_6b6bc : D! W_6b6bc (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_6b6c0 : bv 32 := 0x00a7e663.
Lemma F_6b6c0 : F! 0x6b6c0 W_6b6c0.
Proof. vm_refl. Qed.
Lemma D_6b6c0 : D! W_6b6c0 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_6b6cc : bv 32 := 0x00d60633.
Lemma F_6b6cc : F! 0x6b6cc W_6b6cc.
Proof. vm_refl. Qed.
Lemma D_6b6cc : D! W_6b6cc (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_6b6d0 : bv 32 := 0x000205b7.
Lemma F_6b6d0 : F! 0x6b6d0 W_6b6d0.
Proof. vm_refl. Qed.
Lemma D_6b6d0 : D! W_6b6d0 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_6b6d4 : bv 32 := 0x00a60633.
Lemma F_6b6d4 : F! 0x6b6d4 W_6b6d4.
Proof. vm_refl. Qed.
Lemma D_6b6d4 : D! W_6b6d4 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_6b6d8 : bv 32 := 0x0d15869b.
Lemma F_6b6d8 : F! 0x6b6d8 W_6b6d8.
Proof. vm_refl. Qed.
Lemma D_6b6d8 : D! W_6b6d8 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_6b6dc : bv 32 := 0x0df60593.
Lemma F_6b6dc : F! 0x6b6dc W_6b6dc.
Proof. vm_refl. Qed.
Lemma D_6b6dc : D! W_6b6dc (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_6b6e0 : bv 32 := 0xff85f593.
Lemma F_6b6e0 : F! 0x6b6e0 W_6b6e0.
Proof. vm_refl. Qed.
Lemma D_6b6e0 : D! W_6b6e0 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_6b6e4 : bv 32 := 0x00b4bc23.
Lemma F_6b6e4 : F! 0x6b6e4 W_6b6e4.
Proof. vm_refl. Qed.
Lemma D_6b6e4 : D! W_6b6e4 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_6b6e8 : bv 32 := 0x02a4b023.
Lemma F_6b6e8 : F! 0x6b6e8 W_6b6e8.
Proof. vm_refl. Qed.
Lemma D_6b6e8 : D! W_6b6e8 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_6b6ec : bv 32 := 0x02d5ea63.
Lemma F_6b6ec : F! 0x6b6ec W_6b6ec.
Proof. vm_refl. Qed.
Lemma D_6b6ec : D! W_6b6ec (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_6b720 : bv 32 := 0x0002b697.
Lemma F_6b720 : F! 0x6b720 W_6b720.
Proof. vm_refl. Qed.
Lemma D_6b720 : D! W_6b720 (Auipc 13 43).
Proof. vm_refl. Qed.
Definition W_6b724 : bv 32 := 0x0104b983.
Lemma F_6b724 : F! 0x6b724 W_6b724.
Proof. vm_refl. Qed.
Lemma D_6b724 : D! W_6b724 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_6b728 : bv 32 := 0x0284b603.
Lemma F_6b728 : F! 0x6b728 W_6b728.
Proof. vm_refl. Qed.
Lemma D_6b728 : D! W_6b728 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_6b72c : bv 32 := 0xfff50713.
Lemma F_6b72c : F! 0x6b72c W_6b72c.
Proof. vm_refl. Qed.
Lemma D_6b72c : D! W_6b72c (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_6b730 : bv 32 := 0xf3800793.
Lemma F_6b730 : F! 0x6b730 W_6b730.
Proof. vm_refl. Qed.
Lemma D_6b730 : D! W_6b730 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_6b734 : bv 32 := 0x18868513.
Lemma F_6b734 : F! 0x6b734 W_6b734.
Proof. vm_refl. Qed.
Lemma D_6b734 : D! W_6b734 (OpImm ALU_ADD 10 13 392).
Proof. vm_refl. Qed.
Definition W_6b738 : bv 32 := 0x40a787b3.
Lemma F_6b738 : F! 0x6b738 W_6b738.
Proof. vm_refl. Qed.
Lemma D_6b738 : D! W_6b738 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_6b73c : bv 32 := 0x00f77733.
Lemma F_6b73c : F! 0x6b73c W_6b73c.
Proof. vm_refl. Qed.
Lemma D_6b73c : D! W_6b73c (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_6b740 : bv 32 := 0xfff64693.
Lemma F_6b740 : F! 0x6b740 W_6b740.
Proof. vm_refl. Qed.
Lemma D_6b740 : D! W_6b740 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_6b744 : bv 32 := 0x00e50933.
Lemma F_6b744 : F! 0x6b744 W_6b744.
Proof. vm_refl. Qed.
Lemma D_6b744 : D! W_6b744 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_6b748 : bv 32 := 0x00369693.
Lemma F_6b748 : F! 0x6b748 W_6b748.
Proof. vm_refl. Qed.
Lemma D_6b748 : D! W_6b748 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_6b74c : bv 32 := 0x00d506b3.
Lemma F_6b74c : F! 0x6b74c W_6b74c.
Proof. vm_refl. Qed.
Lemma D_6b74c : D! W_6b74c (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_6b750 : bv 32 := 0x00b68a33.
Lemma F_6b750 : F! 0x6b750 W_6b750.
Proof. vm_refl. Qed.
Lemma D_6b750 : D! W_6b750 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_6b754 : bv 32 := 0x0c890413.
Lemma F_6b754 : F! 0x6b754 W_6b754.
Proof. vm_refl. Qed.
Lemma D_6b754 : D! W_6b754 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_6b758 : bv 32 := 0x04098463.
Lemma F_6b758 : F! 0x6b758 W_6b758.
Proof. vm_refl. Qed.
Lemma D_6b758 : D! W_6b758 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_6b75c : bv 32 := 0x00361613.
Lemma F_6b75c : F! 0x6b75c W_6b75c.
Proof. vm_refl. Qed.
Lemma D_6b75c : D! W_6b75c (ShiftImm ALU_SLL 12 12 3).
Proof. vm_refl. Qed.
Definition W_6b760 : bv 32 := 0x40c50533.
Lemma F_6b760 : F! 0x6b760 W_6b760.
Proof. vm_refl. Qed.
Lemma D_6b760 : D! W_6b760 (Op ALU_SUB 10 10 12).
Proof. vm_refl. Qed.
Definition W_6b764 : bv 32 := 0x00b50ab3.
Lemma F_6b764 : F! 0x6b764 W_6b764.
Proof. vm_refl. Qed.
Lemma D_6b764 : D! W_6b764 (Op ALU_ADD 21 10 11).
Proof. vm_refl. Qed.
Definition W_6b768 : bv 32 := 0x0289b503.
Lemma F_6b768 : F! 0x6b768 W_6b768.
Proof. vm_refl. Qed.
Lemma D_6b768 : D! W_6b768 (Load SZ8 true 10 19 40).
Proof. vm_refl. Qed.
Definition W_6b76c : bv 32 := 0x00a40533.
Lemma F_6b76c : F! 0x6b76c W_6b76c.
Proof. vm_refl. Qed.
Lemma D_6b76c : D! W_6b76c (Op ALU_ADD 10 8 10).
Proof. vm_refl. Qed.
Definition W_6b770 : bv 32 := 0x7ff50513.
Lemma F_6b770 : F! 0x6b770 W_6b770.
Proof. vm_refl. Qed.
Lemma D_6b770 : D! W_6b770 (OpImm ALU_ADD 10 10 2047).
Proof. vm_refl. Qed.
Definition W_6b774 : bv 32 := 0x00150513.
Lemma F_6b774 : F! 0x6b774 W_6b774.
Proof. vm_refl. Qed.
Lemma D_6b774 : D! W_6b774 (OpImm ALU_ADD 10 10 1).
Proof. vm_refl. Qed.
Definition W_6b778 : bv 32 := 0x00aab023.
Lemma F_6b778 : F! 0x6b778 W_6b778.
Proof. vm_refl. Qed.
Lemma D_6b778 : D! W_6b778 (Store SZ8 21 10 0).
Proof. vm_refl. Qed.
Definition W_6b77c : bv 32 := 0x0289b503.
Lemma F_6b77c : F! 0x6b77c W_6b77c.
Proof. vm_refl. Qed.
Lemma D_6b77c : D! W_6b77c (Load SZ8 true 10 19 40).
Proof. vm_refl. Qed.
Definition W_6b780 : bv 32 := 0x0089b583.
Lemma F_6b780 : F! 0x6b780 W_6b780.
Proof. vm_refl. Qed.
Lemma D_6b780 : D! W_6b780 (Load SZ8 true 11 19 8).
Proof. vm_refl. Qed.
Definition W_6b784 : bv 32 := 0x0109b603.
Lemma F_6b784 : F! 0x6b784 W_6b784.
Proof. vm_refl. Qed.
Lemma D_6b784 : D! W_6b784 (Load SZ8 true 12 19 16).
Proof. vm_refl. Qed.
Definition W_6b788 : bv 32 := 0x00a40533.
Lemma F_6b788 : F! 0x6b788 W_6b788.
Proof. vm_refl. Qed.
Lemma D_6b788 : D! W_6b788 (Op ALU_ADD 10 8 10).
Proof. vm_refl. Qed.
Definition W_6b78c : bv 32 := 0x5c50d0ef.
Lemma F_6b78c : F! 0x6b78c W_6b78c.
Proof. vm_refl. Qed.
Lemma D_6b78c : D! W_6b78c (Jal 1 56772).
Proof. vm_refl. Qed.
Definition W_6b790 : bv 32 := 0x0009b983.
Lemma F_6b790 : F! 0x6b790 W_6b790.
Proof. vm_refl. Qed.
Lemma D_6b790 : D! W_6b790 (Load SZ8 true 19 19 0).
Proof. vm_refl. Qed.
Definition W_6b794 : bv 32 := 0x008a8a93.
Lemma F_6b794 : F! 0x6b794 W_6b794.
Proof. vm_refl. Qed.
Lemma D_6b794 : D! W_6b794 (OpImm ALU_ADD 21 21 8).
Proof. vm_refl. Qed.
Definition W_6b798 : bv 32 := 0xfc0998e3.
Lemma F_6b798 : F! 0x6b798 W_6b798.
Proof. vm_refl. Qed.
Lemma D_6b798 : D! W_6b798 (Branch BC_NE 19 0 8144).
Proof. vm_refl. Qed.
Definition W_6b79c : bv 32 := 0x0284b603.
Lemma F_6b79c : F! 0x6b79c W_6b79c.
Proof. vm_refl. Qed.
Lemma D_6b79c : D! W_6b79c (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_6b7a0 : bv 32 := 0x00ca3023.
Lemma F_6b7a0 : F! 0x6b7a0 W_6b7a0.
Proof. vm_refl. Qed.
Lemma D_6b7a0 : D! W_6b7a0 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_6b7a4 : bv 32 := 0x0d493023.
Lemma F_6b7a4 : F! 0x6b7a4 W_6b7a4.
Proof. vm_refl. Qed.
Lemma D_6b7a4 : D! W_6b7a4 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_6b7a8 : bv 32 := 0x01293023.
Lemma F_6b7a8 : F! 0x6b7a8 W_6b7a8.
Proof. vm_refl. Qed.
Lemma D_6b7a8 : D! W_6b7a8 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_6b7ac : bv 32 := 0x00040513.
Lemma F_6b7ac : F! 0x6b7ac W_6b7ac.
Proof. vm_refl. Qed.
Lemma D_6b7ac : D! W_6b7ac (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_6b7b0 : bv 32 := 0x430110ef.
Lemma F_6b7b0 : F! 0x6b7b0 W_6b7b0.
Proof. vm_refl. Qed.
Lemma D_6b7b0 : D! W_6b7b0 (Jal 1 70704).
Proof. vm_refl. Qed.
Definition W_6b7b4 : bv 32 := 0x04054a63.
Lemma F_6b7b4 : F! 0x6b7b4 W_6b7b4.
Proof. vm_refl. Qed.
Lemma D_6b7b4 : D! W_6b7b4 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_6b7b8 : bv 32 := 0x00051663.
Lemma F_6b7b8 : F! 0x6b7b8 W_6b7b8.
Proof. vm_refl. Qed.
Lemma D_6b7b8 : D! W_6b7b8 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_6b7bc : bv 32 := 0x00100513.
Lemma F_6b7bc : F! 0x6b7bc W_6b7bc.
Proof. vm_refl. Qed.
Lemma D_6b7bc : D! W_6b7bc (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_6b7c0 : bv 32 := 0x00a48023.
Lemma F_6b7c0 : F! 0x6b7c0 W_6b7c0.
Proof. vm_refl. Qed.
Lemma D_6b7c0 : D! W_6b7c0 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_6b7c4 : bv 32 := 0x00200513.
Lemma F_6b7c4 : F! 0x6b7c4 W_6b7c4.
Proof. vm_refl. Qed.
Lemma D_6b7c4 : D! W_6b7c4 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_6b7c8 : bv 32 := 0x0004b597.
Lemma F_6b7c8 : F! 0x6b7c8 W_6b7c8.
Proof. vm_refl. Qed.
Lemma D_6b7c8 : D! W_6b7c8 (Auipc 11 75).
Proof. vm_refl. Qed.
Definition W_6b7cc : bv 32 := 0x02a92423.
Lemma F_6b7cc : F! 0x6b7cc W_6b7cc.
Proof. vm_refl. Qed.
Lemma D_6b7cc : D! W_6b7cc (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_6b7d0 : bv 32 := 0x06000893.
Lemma F_6b7d0 : F! 0x6b7d0 W_6b7d0.
Proof. vm_refl. Qed.
Lemma D_6b7d0 : D! W_6b7d0 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_6b7d4 : bv 32 := 0x1b058513.
Lemma F_6b7d4 : F! 0x6b7d4 W_6b7d4.
Proof. vm_refl. Qed.
Lemma D_6b7d4 : D! W_6b7d4 (OpImm ALU_ADD 10 11 432).
Proof. vm_refl. Qed.
Definition W_6b7d8 : bv 32 := 0x03848593.
Lemma F_6b7d8 : F! 0x6b7d8 W_6b7d8.
Proof. vm_refl. Qed.
Lemma D_6b7d8 : D! W_6b7d8 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_6b7dc : bv 32 := 0x00000073.
Lemma F_6b7dc : F! 0x6b7dc W_6b7dc.
Proof. vm_refl. Qed.
Lemma E_6b7dc : is_ecall W_6b7dc = true.
Proof. reflexivity. Qed.
Definition W_6b7e0 : bv 32 := 0x07890613.
Lemma F_6b7e0 : F! 0x6b7e0 W_6b7e0.
Proof. vm_refl. Qed.
Lemma D_6b7e0 : D! W_6b7e0 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_6b7e4 : bv 32 := 0x02a92023.
Lemma F_6b7e4 : F! 0x6b7e4 W_6b7e4.
Proof. vm_refl. Qed.
Lemma D_6b7e4 : D! W_6b7e4 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_6b7e8 : bv 32 := 0x08b93c23.
Lemma F_6b7e8 : F! 0x6b7e8 W_6b7e8.
Proof. vm_refl. Qed.
Lemma D_6b7e8 : D! W_6b7e8 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_6b7ec : bv 32 := 0x06c93c23.
Lemma F_6b7ec : F! 0x6b7ec W_6b7ec.
Proof. vm_refl. Qed.
Lemma D_6b7ec : D! W_6b7ec (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_6b7f0 : bv 32 := 0x0004b517.
Lemma F_6b7f0 : F! 0x6b7f0 W_6b7f0.
Proof. vm_refl. Qed.
Lemma D_6b7f0 : D! W_6b7f0 (Auipc 10 75).
Proof. vm_refl. Qed.
Definition W_6b7f4 : bv 32 := 0x3f853503.
Lemma F_6b7f4 : F! 0x6b7f4 W_6b7f4.
Proof. vm_refl. Qed.
Lemma D_6b7f4 : D! W_6b7f4 (Load SZ8 true 10 10 1016).
Proof. vm_refl. Qed.
Definition W_6b7f8 : bv 32 := 0x01293423.
Lemma F_6b7f8 : F! 0x6b7f8 W_6b7f8.
Proof. vm_refl. Qed.
Lemma D_6b7f8 : D! W_6b7f8 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_6b7fc : bv 32 := 0x01293823.
Lemma F_6b7fc : F! 0x6b7fc W_6b7fc.
Proof. vm_refl. Qed.
Lemma D_6b7fc : D! W_6b7fc (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_6b800 : bv 32 := 0x00a93c23.
Lemma F_6b800 : F! 0x6b800 W_6b800.
Proof. vm_refl. Qed.
Lemma D_6b800 : D! W_6b800 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_6b804 : bv 32 := 0x0080006f.
Lemma F_6b804 : F! 0x6b804 W_6b804.
Proof. vm_refl. Qed.
Lemma D_6b804 : D! W_6b804 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_6b80c : bv 32 := 0x03813083.
Lemma F_6b80c : F! 0x6b80c W_6b80c.
Proof. vm_refl. Qed.
Lemma D_6b80c : D! W_6b80c (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_6b810 : bv 32 := 0x03013403.
Lemma F_6b810 : F! 0x6b810 W_6b810.
Proof. vm_refl. Qed.
Lemma D_6b810 : D! W_6b810 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_6b814 : bv 32 := 0x02813483.
Lemma F_6b814 : F! 0x6b814 W_6b814.
Proof. vm_refl. Qed.
Lemma D_6b814 : D! W_6b814 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_6b818 : bv 32 := 0x02013903.
Lemma F_6b818 : F! 0x6b818 W_6b818.
Proof. vm_refl. Qed.
Lemma D_6b818 : D! W_6b818 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_6b81c : bv 32 := 0x01813983.
Lemma F_6b81c : F! 0x6b81c W_6b81c.
Proof. vm_refl. Qed.
Lemma D_6b81c : D! W_6b81c (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_6b820 : bv 32 := 0x01013a03.
Lemma F_6b820 : F! 0x6b820 W_6b820.
Proof. vm_refl. Qed.
Lemma D_6b820 : D! W_6b820 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_6b824 : bv 32 := 0x00813a83.
Lemma F_6b824 : F! 0x6b824 W_6b824.
Proof. vm_refl. Qed.
Lemma D_6b824 : D! W_6b824 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_6b828 : bv 32 := 0x04010113.
Lemma F_6b828 : F! 0x6b828 W_6b828.
Proof. vm_refl. Qed.
Lemma D_6b828 : D! W_6b828 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_6b82c : bv 32 := 0x00008067.
Lemma F_6b82c : F! 0x6b82c W_6b82c.
Proof. vm_refl. Qed.
Lemma D_6b82c : D! W_6b82c (Jalr 0 1 0).
Proof. vm_refl. Qed.
