(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
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
Definition W_52660 : bv 32 := 0xfc010113.
Lemma F_52660 : F! 0x52660 W_52660.
Proof. vm_refl. Qed.
Lemma D_52660 : D! W_52660 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_52664 : bv 32 := 0x02113c23.
Lemma F_52664 : F! 0x52664 W_52664.
Proof. vm_refl. Qed.
Lemma D_52664 : D! W_52664 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_52668 : bv 32 := 0x02813823.
Lemma F_52668 : F! 0x52668 W_52668.
Proof. vm_refl. Qed.
Lemma D_52668 : D! W_52668 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_5266c : bv 32 := 0x02913423.
Lemma F_5266c : F! 0x5266c W_5266c.
Proof. vm_refl. Qed.
Lemma D_5266c : D! W_5266c (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_52670 : bv 32 := 0x03213023.
Lemma F_52670 : F! 0x52670 W_52670.
Proof. vm_refl. Qed.
Lemma D_52670 : D! W_52670 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_52674 : bv 32 := 0x01313c23.
Lemma F_52674 : F! 0x52674 W_52674.
Proof. vm_refl. Qed.
Lemma D_52674 : D! W_52674 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_52678 : bv 32 := 0x01413823.
Lemma F_52678 : F! 0x52678 W_52678.
Proof. vm_refl. Qed.
Lemma D_52678 : D! W_52678 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_5267c : bv 32 := 0x01513423.
Lemma F_5267c : F! 0x5267c W_5267c.
Proof. vm_refl. Qed.
Lemma D_5267c : D! W_5267c (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_52680 : bv 32 := 0x02853683.
Lemma F_52680 : F! 0x52680 W_52680.
Proof. vm_refl. Qed.
Lemma D_52680 : D! W_52680 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_52684 : bv 32 := 0x00045597.
Lemma F_52684 : F! 0x52684 W_52684.
Proof. vm_refl. Qed.
Lemma D_52684 : D! W_52684 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_52688 : bv 32 := 0x31458593.
Lemma F_52688 : F! 0x52688 W_52688.
Proof. vm_refl. Qed.
Lemma D_52688 : D! W_52688 (OpImm ALU_ADD 11 11 788).
Proof. vm_refl. Qed.
Definition W_5268c : bv 32 := 0x00045617.
Lemma F_5268c : F! 0x5268c W_5268c.
Proof. vm_refl. Qed.
Lemma D_5268c : D! W_5268c (Auipc 12 69).
Proof. vm_refl. Qed.
Definition W_52690 : bv 32 := 0x59460493.
Lemma F_52690 : F! 0x52690 W_52690.
Proof. vm_refl. Qed.
Lemma D_52690 : D! W_52690 (OpImm ALU_ADD 9 12 1428).
Proof. vm_refl. Qed.
Definition W_52694 : bv 32 := 0x0c068e63.
Lemma F_52694 : F! 0x52694 W_52694.
Proof. vm_refl. Qed.
Lemma D_52694 : D! W_52694 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_52698 : bv 32 := 0x00000613.
Lemma F_52698 : F! 0x52698 W_52698.
Proof. vm_refl. Qed.
Lemma D_52698 : D! W_52698 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_5269c : bv 32 := 0x00000893.
Lemma F_5269c : F! 0x5269c W_5269c.
Proof. vm_refl. Qed.
Lemma D_5269c : D! W_5269c (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_526a0 : bv 32 := 0x00014717.
Lemma F_526a0 : F! 0x526a0 W_526a0.
Proof. vm_refl. Qed.
Lemma D_526a0 : D! W_526a0 (Auipc 14 20).
Proof. vm_refl. Qed.
Definition W_526a4 : bv 32 := 0x01853783.
Lemma F_526a4 : F! 0x526a4 W_526a4.
Proof. vm_refl. Qed.
Lemma D_526a4 : D! W_526a4 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_526a8 : bv 32 := 0x02053503.
Lemma F_526a8 : F! 0x526a8 W_526a8.
Proof. vm_refl. Qed.
Lemma D_526a8 : D! W_526a8 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_526ac : bv 32 := 0x00600813.
Lemma F_526ac : F! 0x526ac W_526ac.
Proof. vm_refl. Qed.
Lemma D_526ac : D! W_526ac (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_526b0 : bv 32 := 0x00013297.
Lemma F_526b0 : F! 0x526b0 W_526b0.
Proof. vm_refl. Qed.
Lemma D_526b0 : D! W_526b0 (Auipc 5 19).
Proof. vm_refl. Qed.
Definition W_526b4 : bv 32 := 0x71876f03.
Lemma F_526b4 : F! 0x526b4 W_526b4.
Proof. vm_refl. Qed.
Lemma D_526b4 : D! W_526b4 (Load SZ4 false 30 14 1816).
Proof. vm_refl. Qed.
Definition W_526b8 : bv 32 := 0x3702b283.
Lemma F_526b8 : F! 0x526b8 W_526b8.
Proof. vm_refl. Qed.
Lemma D_526b8 : D! W_526b8 (Load SZ8 true 5 5 880).
Proof. vm_refl. Qed.
Definition W_526bc : bv 32 := 0x00200313.
Lemma F_526bc : F! 0x526bc W_526bc.
Proof. vm_refl. Qed.
Lemma D_526bc : D! W_526bc (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_526c0 : bv 32 := 0x00700393.
Lemma F_526c0 : F! 0x526c0 W_526c0.
Proof. vm_refl. Qed.
Lemma D_526c0 : D! W_526c0 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_526c4 : bv 32 := 0x6474ee37.
Lemma F_526c4 : F! 0x526c4 W_526c4.
Proof. vm_refl. Qed.
Lemma D_526c4 : D! W_526c4 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_526c8 : bv 32 := 0x551e0e1b.
Lemma F_526c8 : F! 0x526c8 W_526c8.
Proof. vm_refl. Qed.
Lemma D_526c8 : D! W_526c8 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_526cc : bv 32 := 0x00078e93.
Lemma F_526cc : F! 0x526cc W_526cc.
Proof. vm_refl. Qed.
Lemma D_526cc : D! W_526cc (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_526d0 : bv 32 := 0x0180006f.
Lemma F_526d0 : F! 0x526d0 W_526d0.
Proof. vm_refl. Qed.
Lemma D_526d0 : D! W_526d0 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_526d4 : bv 32 := 0x010eb603.
Lemma F_526d4 : F! 0x526d4 W_526d4.
Proof. vm_refl. Qed.
Lemma D_526d4 : D! W_526d4 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_526d8 : bv 32 := 0x40c78633.
Lemma F_526d8 : F! 0x526d8 W_526d8.
Proof. vm_refl. Qed.
Lemma D_526d8 : D! W_526d8 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_526dc : bv 32 := 0xfff68693.
Lemma F_526dc : F! 0x526dc W_526dc.
Proof. vm_refl. Qed.
Lemma D_526dc : D! W_526dc (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_526e0 : bv 32 := 0x00ae8eb3.
Lemma F_526e0 : F! 0x526e0 W_526e0.
Proof. vm_refl. Qed.
Lemma D_526e0 : D! W_526e0 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_526e4 : bv 32 := 0x04068a63.
Lemma F_526e4 : F! 0x526e4 W_526e4.
Proof. vm_refl. Qed.
Lemma D_526e4 : D! W_526e4 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_526e8 : bv 32 := 0x000ea403.
Lemma F_526e8 : F! 0x526e8 W_526e8.
Proof. vm_refl. Qed.
Lemma D_526e8 : D! W_526e8 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_526ec : bv 32 := 0xff0404e3.
Lemma F_526ec : F! 0x526ec W_526ec.
Proof. vm_refl. Qed.
Lemma D_526ec : D! W_526ec (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_526f0 : bv 32 := 0x00028a63.
Lemma F_526f0 : F! 0x526f0 W_526f0.
Proof. vm_refl. Qed.
Lemma D_526f0 : D! W_526f0 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_52704 : bv 32 := 0x000e8f93.
Lemma F_52704 : F! 0x52704 W_52704.
Proof. vm_refl. Qed.
Lemma D_52704 : D! W_52704 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_52708 : bv 32 := 0x00740463.
Lemma F_52708 : F! 0x52708 W_52708.
Proof. vm_refl. Qed.
Lemma D_52708 : D! W_52708 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_5270c : bv 32 := 0x00088f93.
Lemma F_5270c : F! 0x5270c W_5270c.
Proof. vm_refl. Qed.
Lemma D_5270c : D! W_5270c (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_52710 : bv 32 := 0x03c41063.
Lemma F_52710 : F! 0x52710 W_52710.
Proof. vm_refl. Qed.
Lemma D_52710 : D! W_52710 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_52714 : bv 32 := 0x028eb883.
Lemma F_52714 : F! 0x52714 W_52714.
Proof. vm_refl. Qed.
Lemma D_52714 : D! W_52714 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_52718 : bv 32 := 0x011f7c63.
Lemma F_52718 : F! 0x52718 W_52718.
Proof. vm_refl. Qed.
Lemma D_52718 : D! W_52718 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_52730 : bv 32 := 0x000f8893.
Lemma F_52730 : F! 0x52730 W_52730.
Proof. vm_refl. Qed.
Lemma D_52730 : D! W_52730 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_52734 : bv 32 := 0xfa9ff06f.
Lemma F_52734 : F! 0x52734 W_52734.
Proof. vm_refl. Qed.
Lemma D_52734 : D! W_52734 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_52738 : bv 32 := 0x02088c63.
Lemma F_52738 : F! 0x52738 W_52738.
Proof. vm_refl. Qed.
Lemma D_52738 : D! W_52738 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_52770 : bv 32 := 0x0105b603.
Lemma F_52770 : F! 0x52770 W_52770.
Proof. vm_refl. Qed.
Lemma D_52770 : D! W_52770 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_52774 : bv 32 := 0x0205b683.
Lemma F_52774 : F! 0x52774 W_52774.
Proof. vm_refl. Qed.
Lemma D_52774 : D! W_52774 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_52778 : bv 32 := 0x0285b503.
Lemma F_52778 : F! 0x52778 W_52778.
Proof. vm_refl. Qed.
Lemma D_52778 : D! W_52778 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_5277c : bv 32 := 0x00c68733.
Lemma F_5277c : F! 0x5277c W_5277c.
Proof. vm_refl. Qed.
Lemma D_5277c : D! W_5277c (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_52780 : bv 32 := 0xfff50793.
Lemma F_52780 : F! 0x52780 W_52780.
Proof. vm_refl. Qed.
Lemma D_52780 : D! W_52780 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_52784 : bv 32 := 0x40e00733.
Lemma F_52784 : F! 0x52784 W_52784.
Proof. vm_refl. Qed.
Lemma D_52784 : D! W_52784 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_52788 : bv 32 := 0x00c7f633.
Lemma F_52788 : F! 0x52788 W_52788.
Proof. vm_refl. Qed.
Lemma D_52788 : D! W_52788 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_5278c : bv 32 := 0x00e7f733.
Lemma F_5278c : F! 0x5278c W_5278c.
Proof. vm_refl. Qed.
Lemma D_5278c : D! W_5278c (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_52790 : bv 32 := 0x00700793.
Lemma F_52790 : F! 0x52790 W_52790.
Proof. vm_refl. Qed.
Lemma D_52790 : D! W_52790 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_52794 : bv 32 := 0x00d706b3.
Lemma F_52794 : F! 0x52794 W_52794.
Proof. vm_refl. Qed.
Lemma D_52794 : D! W_52794 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_52798 : bv 32 := 0x02d5b023.
Lemma F_52798 : F! 0x52798 W_52798.
Proof. vm_refl. Qed.
Lemma D_52798 : D! W_52798 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_5279c : bv 32 := 0x02c5b823.
Lemma F_5279c : F! 0x5279c W_5279c.
Proof. vm_refl. Qed.
Lemma D_5279c : D! W_5279c (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_527a0 : bv 32 := 0x00a7e663.
Lemma F_527a0 : F! 0x527a0 W_527a0.
Proof. vm_refl. Qed.
Lemma D_527a0 : D! W_527a0 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_527a4 : bv 32 := 0x00800513.
Lemma F_527a4 : F! 0x527a4 W_527a4.
Proof. vm_refl. Qed.
Lemma D_527a4 : D! W_527a4 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_527a8 : bv 32 := 0x02a5b423.
Lemma F_527a8 : F! 0x527a8 W_527a8.
Proof. vm_refl. Qed.
Lemma D_527a8 : D! W_527a8 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_527ac : bv 32 := 0x00d60633.
Lemma F_527ac : F! 0x527ac W_527ac.
Proof. vm_refl. Qed.
Lemma D_527ac : D! W_527ac (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_527b0 : bv 32 := 0x000205b7.
Lemma F_527b0 : F! 0x527b0 W_527b0.
Proof. vm_refl. Qed.
Lemma D_527b0 : D! W_527b0 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_527b4 : bv 32 := 0x00a60633.
Lemma F_527b4 : F! 0x527b4 W_527b4.
Proof. vm_refl. Qed.
Lemma D_527b4 : D! W_527b4 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_527b8 : bv 32 := 0x0d15869b.
Lemma F_527b8 : F! 0x527b8 W_527b8.
Proof. vm_refl. Qed.
Lemma D_527b8 : D! W_527b8 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_527bc : bv 32 := 0x0df60593.
Lemma F_527bc : F! 0x527bc W_527bc.
Proof. vm_refl. Qed.
Lemma D_527bc : D! W_527bc (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_527c0 : bv 32 := 0xff85f593.
Lemma F_527c0 : F! 0x527c0 W_527c0.
Proof. vm_refl. Qed.
Lemma D_527c0 : D! W_527c0 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_527c4 : bv 32 := 0x00b4bc23.
Lemma F_527c4 : F! 0x527c4 W_527c4.
Proof. vm_refl. Qed.
Lemma D_527c4 : D! W_527c4 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_527c8 : bv 32 := 0x02a4b023.
Lemma F_527c8 : F! 0x527c8 W_527c8.
Proof. vm_refl. Qed.
Lemma D_527c8 : D! W_527c8 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_527cc : bv 32 := 0x02d5ea63.
Lemma F_527cc : F! 0x527cc W_527cc.
Proof. vm_refl. Qed.
Lemma D_527cc : D! W_527cc (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_52800 : bv 32 := 0x00025697.
Lemma F_52800 : F! 0x52800 W_52800.
Proof. vm_refl. Qed.
Lemma D_52800 : D! W_52800 (Auipc 13 37).
Proof. vm_refl. Qed.
Definition W_52804 : bv 32 := 0x0104b983.
Lemma F_52804 : F! 0x52804 W_52804.
Proof. vm_refl. Qed.
Lemma D_52804 : D! W_52804 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_52808 : bv 32 := 0x0284b603.
Lemma F_52808 : F! 0x52808 W_52808.
Proof. vm_refl. Qed.
Lemma D_52808 : D! W_52808 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_5280c : bv 32 := 0xfff50713.
Lemma F_5280c : F! 0x5280c W_5280c.
Proof. vm_refl. Qed.
Lemma D_5280c : D! W_5280c (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_52810 : bv 32 := 0xf3800793.
Lemma F_52810 : F! 0x52810 W_52810.
Proof. vm_refl. Qed.
Lemma D_52810 : D! W_52810 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_52814 : bv 32 := 0x0c868513.
Lemma F_52814 : F! 0x52814 W_52814.
Proof. vm_refl. Qed.
Lemma D_52814 : D! W_52814 (OpImm ALU_ADD 10 13 200).
Proof. vm_refl. Qed.
Definition W_52818 : bv 32 := 0x40a787b3.
Lemma F_52818 : F! 0x52818 W_52818.
Proof. vm_refl. Qed.
Lemma D_52818 : D! W_52818 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_5281c : bv 32 := 0x00f77733.
Lemma F_5281c : F! 0x5281c W_5281c.
Proof. vm_refl. Qed.
Lemma D_5281c : D! W_5281c (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_52820 : bv 32 := 0xfff64693.
Lemma F_52820 : F! 0x52820 W_52820.
Proof. vm_refl. Qed.
Lemma D_52820 : D! W_52820 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_52824 : bv 32 := 0x00e50933.
Lemma F_52824 : F! 0x52824 W_52824.
Proof. vm_refl. Qed.
Lemma D_52824 : D! W_52824 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_52828 : bv 32 := 0x00369693.
Lemma F_52828 : F! 0x52828 W_52828.
Proof. vm_refl. Qed.
Lemma D_52828 : D! W_52828 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_5282c : bv 32 := 0x00d506b3.
Lemma F_5282c : F! 0x5282c W_5282c.
Proof. vm_refl. Qed.
Lemma D_5282c : D! W_5282c (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_52830 : bv 32 := 0x00b68a33.
Lemma F_52830 : F! 0x52830 W_52830.
Proof. vm_refl. Qed.
Lemma D_52830 : D! W_52830 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_52834 : bv 32 := 0x0c890413.
Lemma F_52834 : F! 0x52834 W_52834.
Proof. vm_refl. Qed.
Lemma D_52834 : D! W_52834 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_52838 : bv 32 := 0x04098463.
Lemma F_52838 : F! 0x52838 W_52838.
Proof. vm_refl. Qed.
Lemma D_52838 : D! W_52838 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_52880 : bv 32 := 0x00ca3023.
Lemma F_52880 : F! 0x52880 W_52880.
Proof. vm_refl. Qed.
Lemma D_52880 : D! W_52880 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_52884 : bv 32 := 0x0d493023.
Lemma F_52884 : F! 0x52884 W_52884.
Proof. vm_refl. Qed.
Lemma D_52884 : D! W_52884 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_52888 : bv 32 := 0x01293023.
Lemma F_52888 : F! 0x52888 W_52888.
Proof. vm_refl. Qed.
Lemma D_52888 : D! W_52888 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_5288c : bv 32 := 0x00040513.
Lemma F_5288c : F! 0x5288c W_5288c.
Proof. vm_refl. Qed.
Lemma D_5288c : D! W_5288c (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_52890 : bv 32 := 0x1a50e0ef.
Lemma F_52890 : F! 0x52890 W_52890.
Proof. vm_refl. Qed.
Lemma D_52890 : D! W_52890 (Jal 1 59812).
Proof. vm_refl. Qed.
Definition W_52894 : bv 32 := 0x04054a63.
Lemma F_52894 : F! 0x52894 W_52894.
Proof. vm_refl. Qed.
Lemma D_52894 : D! W_52894 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_52898 : bv 32 := 0x00051663.
Lemma F_52898 : F! 0x52898 W_52898.
Proof. vm_refl. Qed.
Lemma D_52898 : D! W_52898 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_5289c : bv 32 := 0x00100513.
Lemma F_5289c : F! 0x5289c W_5289c.
Proof. vm_refl. Qed.
Lemma D_5289c : D! W_5289c (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_528a0 : bv 32 := 0x00a48023.
Lemma F_528a0 : F! 0x528a0 W_528a0.
Proof. vm_refl. Qed.
Lemma D_528a0 : D! W_528a0 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_528a4 : bv 32 := 0x00200513.
Lemma F_528a4 : F! 0x528a4 W_528a4.
Proof. vm_refl. Qed.
Lemma D_528a4 : D! W_528a4 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_528a8 : bv 32 := 0x00045597.
Lemma F_528a8 : F! 0x528a8 W_528a8.
Proof. vm_refl. Qed.
Lemma D_528a8 : D! W_528a8 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_528ac : bv 32 := 0x02a92423.
Lemma F_528ac : F! 0x528ac W_528ac.
Proof. vm_refl. Qed.
Lemma D_528ac : D! W_528ac (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_528b0 : bv 32 := 0x06000893.
Lemma F_528b0 : F! 0x528b0 W_528b0.
Proof. vm_refl. Qed.
Lemma D_528b0 : D! W_528b0 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_528b4 : bv 32 := 0x0f058513.
Lemma F_528b4 : F! 0x528b4 W_528b4.
Proof. vm_refl. Qed.
Lemma D_528b4 : D! W_528b4 (OpImm ALU_ADD 10 11 240).
Proof. vm_refl. Qed.
Definition W_528b8 : bv 32 := 0x03848593.
Lemma F_528b8 : F! 0x528b8 W_528b8.
Proof. vm_refl. Qed.
Lemma D_528b8 : D! W_528b8 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_528bc : bv 32 := 0x00000073.
Lemma F_528bc : F! 0x528bc W_528bc.
Proof. vm_refl. Qed.
Lemma E_528bc : is_ecall W_528bc = true.
Proof. reflexivity. Qed.
Definition W_528c0 : bv 32 := 0x07890613.
Lemma F_528c0 : F! 0x528c0 W_528c0.
Proof. vm_refl. Qed.
Lemma D_528c0 : D! W_528c0 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_528c4 : bv 32 := 0x02a92023.
Lemma F_528c4 : F! 0x528c4 W_528c4.
Proof. vm_refl. Qed.
Lemma D_528c4 : D! W_528c4 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_528c8 : bv 32 := 0x08b93c23.
Lemma F_528c8 : F! 0x528c8 W_528c8.
Proof. vm_refl. Qed.
Lemma D_528c8 : D! W_528c8 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_528cc : bv 32 := 0x06c93c23.
Lemma F_528cc : F! 0x528cc W_528cc.
Proof. vm_refl. Qed.
Lemma D_528cc : D! W_528cc (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_528d0 : bv 32 := 0x00045517.
Lemma F_528d0 : F! 0x528d0 W_528d0.
Proof. vm_refl. Qed.
Lemma D_528d0 : D! W_528d0 (Auipc 10 69).
Proof. vm_refl. Qed.
Definition W_528d4 : bv 32 := 0x33853503.
Lemma F_528d4 : F! 0x528d4 W_528d4.
Proof. vm_refl. Qed.
Lemma D_528d4 : D! W_528d4 (Load SZ8 true 10 10 824).
Proof. vm_refl. Qed.
Definition W_528d8 : bv 32 := 0x01293423.
Lemma F_528d8 : F! 0x528d8 W_528d8.
Proof. vm_refl. Qed.
Lemma D_528d8 : D! W_528d8 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_528dc : bv 32 := 0x01293823.
Lemma F_528dc : F! 0x528dc W_528dc.
Proof. vm_refl. Qed.
Lemma D_528dc : D! W_528dc (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_528e0 : bv 32 := 0x00a93c23.
Lemma F_528e0 : F! 0x528e0 W_528e0.
Proof. vm_refl. Qed.
Lemma D_528e0 : D! W_528e0 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_528e4 : bv 32 := 0x0080006f.
Lemma F_528e4 : F! 0x528e4 W_528e4.
Proof. vm_refl. Qed.
Lemma D_528e4 : D! W_528e4 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_528ec : bv 32 := 0x03813083.
Lemma F_528ec : F! 0x528ec W_528ec.
Proof. vm_refl. Qed.
Lemma D_528ec : D! W_528ec (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_528f0 : bv 32 := 0x03013403.
Lemma F_528f0 : F! 0x528f0 W_528f0.
Proof. vm_refl. Qed.
Lemma D_528f0 : D! W_528f0 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_528f4 : bv 32 := 0x02813483.
Lemma F_528f4 : F! 0x528f4 W_528f4.
Proof. vm_refl. Qed.
Lemma D_528f4 : D! W_528f4 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_528f8 : bv 32 := 0x02013903.
Lemma F_528f8 : F! 0x528f8 W_528f8.
Proof. vm_refl. Qed.
Lemma D_528f8 : D! W_528f8 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_528fc : bv 32 := 0x01813983.
Lemma F_528fc : F! 0x528fc W_528fc.
Proof. vm_refl. Qed.
Lemma D_528fc : D! W_528fc (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_52900 : bv 32 := 0x01013a03.
Lemma F_52900 : F! 0x52900 W_52900.
Proof. vm_refl. Qed.
Lemma D_52900 : D! W_52900 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_52904 : bv 32 := 0x00813a83.
Lemma F_52904 : F! 0x52904 W_52904.
Proof. vm_refl. Qed.
Lemma D_52904 : D! W_52904 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_52908 : bv 32 := 0x04010113.
Lemma F_52908 : F! 0x52908 W_52908.
Proof. vm_refl. Qed.
Lemma D_52908 : D! W_52908 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_5290c : bv 32 := 0x00008067.
Lemma F_5290c : F! 0x5290c W_5290c.
Proof. vm_refl. Qed.
Lemma D_5290c : D! W_5290c (Jalr 0 1 0).
Proof. vm_refl. Qed.
