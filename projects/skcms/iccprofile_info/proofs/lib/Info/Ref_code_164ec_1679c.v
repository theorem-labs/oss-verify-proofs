(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
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
Definition W_164ec : bv 32 := 0xfc010113.
Lemma F_164ec : F! 0x164ec W_164ec.
Proof. vm_refl. Qed.
Lemma D_164ec : D! W_164ec (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_164f0 : bv 32 := 0x02113c23.
Lemma F_164f0 : F! 0x164f0 W_164f0.
Proof. vm_refl. Qed.
Lemma D_164f0 : D! W_164f0 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_164f4 : bv 32 := 0x02813823.
Lemma F_164f4 : F! 0x164f4 W_164f4.
Proof. vm_refl. Qed.
Lemma D_164f4 : D! W_164f4 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_164f8 : bv 32 := 0x02913423.
Lemma F_164f8 : F! 0x164f8 W_164f8.
Proof. vm_refl. Qed.
Lemma D_164f8 : D! W_164f8 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_164fc : bv 32 := 0x03213023.
Lemma F_164fc : F! 0x164fc W_164fc.
Proof. vm_refl. Qed.
Lemma D_164fc : D! W_164fc (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_16500 : bv 32 := 0x01313c23.
Lemma F_16500 : F! 0x16500 W_16500.
Proof. vm_refl. Qed.
Lemma D_16500 : D! W_16500 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_16504 : bv 32 := 0x01413823.
Lemma F_16504 : F! 0x16504 W_16504.
Proof. vm_refl. Qed.
Lemma D_16504 : D! W_16504 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_16508 : bv 32 := 0x01513423.
Lemma F_16508 : F! 0x16508 W_16508.
Proof. vm_refl. Qed.
Lemma D_16508 : D! W_16508 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_1650c : bv 32 := 0x02853683.
Lemma F_1650c : F! 0x1650c W_1650c.
Proof. vm_refl. Qed.
Lemma D_1650c : D! W_1650c (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_16510 : bv 32 := 0x0003a597.
Lemma F_16510 : F! 0x16510 W_16510.
Proof. vm_refl. Qed.
Lemma D_16510 : D! W_16510 (Auipc 11 58).
Proof. vm_refl. Qed.
Definition W_16514 : bv 32 := 0x4e058593.
Lemma F_16514 : F! 0x16514 W_16514.
Proof. vm_refl. Qed.
Lemma D_16514 : D! W_16514 (OpImm ALU_ADD 11 11 1248).
Proof. vm_refl. Qed.
Definition W_16518 : bv 32 := 0x0003a617.
Lemma F_16518 : F! 0x16518 W_16518.
Proof. vm_refl. Qed.
Lemma D_16518 : D! W_16518 (Auipc 12 58).
Proof. vm_refl. Qed.
Definition W_1651c : bv 32 := 0x76060493.
Lemma F_1651c : F! 0x1651c W_1651c.
Proof. vm_refl. Qed.
Lemma D_1651c : D! W_1651c (OpImm ALU_ADD 9 12 1888).
Proof. vm_refl. Qed.
Definition W_16520 : bv 32 := 0x0c068e63.
Lemma F_16520 : F! 0x16520 W_16520.
Proof. vm_refl. Qed.
Lemma D_16520 : D! W_16520 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_16524 : bv 32 := 0x00000613.
Lemma F_16524 : F! 0x16524 W_16524.
Proof. vm_refl. Qed.
Lemma D_16524 : D! W_16524 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_16528 : bv 32 := 0x00000893.
Lemma F_16528 : F! 0x16528 W_16528.
Proof. vm_refl. Qed.
Lemma D_16528 : D! W_16528 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_1652c : bv 32 := 0x0000a717.
Lemma F_1652c : F! 0x1652c W_1652c.
Proof. vm_refl. Qed.
Lemma D_1652c : D! W_1652c (Auipc 14 10).
Proof. vm_refl. Qed.
Definition W_16530 : bv 32 := 0x01853783.
Lemma F_16530 : F! 0x16530 W_16530.
Proof. vm_refl. Qed.
Lemma D_16530 : D! W_16530 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_16534 : bv 32 := 0x02053503.
Lemma F_16534 : F! 0x16534 W_16534.
Proof. vm_refl. Qed.
Lemma D_16534 : D! W_16534 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_16538 : bv 32 := 0x00600813.
Lemma F_16538 : F! 0x16538 W_16538.
Proof. vm_refl. Qed.
Lemma D_16538 : D! W_16538 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_1653c : bv 32 := 0x00009297.
Lemma F_1653c : F! 0x1653c W_1653c.
Proof. vm_refl. Qed.
Lemma D_1653c : D! W_1653c (Auipc 5 9).
Proof. vm_refl. Qed.
Definition W_16540 : bv 32 := 0x35476f03.
Lemma F_16540 : F! 0x16540 W_16540.
Proof. vm_refl. Qed.
Lemma D_16540 : D! W_16540 (Load SZ4 false 30 14 852).
Proof. vm_refl. Qed.
Definition W_16544 : bv 32 := 0x0ac2b283.
Lemma F_16544 : F! 0x16544 W_16544.
Proof. vm_refl. Qed.
Lemma D_16544 : D! W_16544 (Load SZ8 true 5 5 172).
Proof. vm_refl. Qed.
Definition W_16548 : bv 32 := 0x00200313.
Lemma F_16548 : F! 0x16548 W_16548.
Proof. vm_refl. Qed.
Lemma D_16548 : D! W_16548 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_1654c : bv 32 := 0x00700393.
Lemma F_1654c : F! 0x1654c W_1654c.
Proof. vm_refl. Qed.
Lemma D_1654c : D! W_1654c (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_16550 : bv 32 := 0x6474ee37.
Lemma F_16550 : F! 0x16550 W_16550.
Proof. vm_refl. Qed.
Lemma D_16550 : D! W_16550 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_16554 : bv 32 := 0x551e0e1b.
Lemma F_16554 : F! 0x16554 W_16554.
Proof. vm_refl. Qed.
Lemma D_16554 : D! W_16554 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_16558 : bv 32 := 0x00078e93.
Lemma F_16558 : F! 0x16558 W_16558.
Proof. vm_refl. Qed.
Lemma D_16558 : D! W_16558 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_1655c : bv 32 := 0x0180006f.
Lemma F_1655c : F! 0x1655c W_1655c.
Proof. vm_refl. Qed.
Lemma D_1655c : D! W_1655c (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_16560 : bv 32 := 0x010eb603.
Lemma F_16560 : F! 0x16560 W_16560.
Proof. vm_refl. Qed.
Lemma D_16560 : D! W_16560 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_16564 : bv 32 := 0x40c78633.
Lemma F_16564 : F! 0x16564 W_16564.
Proof. vm_refl. Qed.
Lemma D_16564 : D! W_16564 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_16568 : bv 32 := 0xfff68693.
Lemma F_16568 : F! 0x16568 W_16568.
Proof. vm_refl. Qed.
Lemma D_16568 : D! W_16568 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_1656c : bv 32 := 0x00ae8eb3.
Lemma F_1656c : F! 0x1656c W_1656c.
Proof. vm_refl. Qed.
Lemma D_1656c : D! W_1656c (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_16570 : bv 32 := 0x04068a63.
Lemma F_16570 : F! 0x16570 W_16570.
Proof. vm_refl. Qed.
Lemma D_16570 : D! W_16570 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_16574 : bv 32 := 0x000ea403.
Lemma F_16574 : F! 0x16574 W_16574.
Proof. vm_refl. Qed.
Lemma D_16574 : D! W_16574 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_16578 : bv 32 := 0xff0404e3.
Lemma F_16578 : F! 0x16578 W_16578.
Proof. vm_refl. Qed.
Lemma D_16578 : D! W_16578 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_1657c : bv 32 := 0x00028a63.
Lemma F_1657c : F! 0x1657c W_1657c.
Proof. vm_refl. Qed.
Lemma D_1657c : D! W_1657c (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_16590 : bv 32 := 0x000e8f93.
Lemma F_16590 : F! 0x16590 W_16590.
Proof. vm_refl. Qed.
Lemma D_16590 : D! W_16590 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_16594 : bv 32 := 0x00740463.
Lemma F_16594 : F! 0x16594 W_16594.
Proof. vm_refl. Qed.
Lemma D_16594 : D! W_16594 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_16598 : bv 32 := 0x00088f93.
Lemma F_16598 : F! 0x16598 W_16598.
Proof. vm_refl. Qed.
Lemma D_16598 : D! W_16598 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_1659c : bv 32 := 0x03c41063.
Lemma F_1659c : F! 0x1659c W_1659c.
Proof. vm_refl. Qed.
Lemma D_1659c : D! W_1659c (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_165a0 : bv 32 := 0x028eb883.
Lemma F_165a0 : F! 0x165a0 W_165a0.
Proof. vm_refl. Qed.
Lemma D_165a0 : D! W_165a0 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_165a4 : bv 32 := 0x011f7c63.
Lemma F_165a4 : F! 0x165a4 W_165a4.
Proof. vm_refl. Qed.
Lemma D_165a4 : D! W_165a4 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_165bc : bv 32 := 0x000f8893.
Lemma F_165bc : F! 0x165bc W_165bc.
Proof. vm_refl. Qed.
Lemma D_165bc : D! W_165bc (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_165c0 : bv 32 := 0xfa9ff06f.
Lemma F_165c0 : F! 0x165c0 W_165c0.
Proof. vm_refl. Qed.
Lemma D_165c0 : D! W_165c0 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_165c4 : bv 32 := 0x02088c63.
Lemma F_165c4 : F! 0x165c4 W_165c4.
Proof. vm_refl. Qed.
Lemma D_165c4 : D! W_165c4 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_165fc : bv 32 := 0x0105b603.
Lemma F_165fc : F! 0x165fc W_165fc.
Proof. vm_refl. Qed.
Lemma D_165fc : D! W_165fc (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_16600 : bv 32 := 0x0205b683.
Lemma F_16600 : F! 0x16600 W_16600.
Proof. vm_refl. Qed.
Lemma D_16600 : D! W_16600 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_16604 : bv 32 := 0x0285b503.
Lemma F_16604 : F! 0x16604 W_16604.
Proof. vm_refl. Qed.
Lemma D_16604 : D! W_16604 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_16608 : bv 32 := 0x00c68733.
Lemma F_16608 : F! 0x16608 W_16608.
Proof. vm_refl. Qed.
Lemma D_16608 : D! W_16608 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_1660c : bv 32 := 0xfff50793.
Lemma F_1660c : F! 0x1660c W_1660c.
Proof. vm_refl. Qed.
Lemma D_1660c : D! W_1660c (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_16610 : bv 32 := 0x40e00733.
Lemma F_16610 : F! 0x16610 W_16610.
Proof. vm_refl. Qed.
Lemma D_16610 : D! W_16610 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_16614 : bv 32 := 0x00c7f633.
Lemma F_16614 : F! 0x16614 W_16614.
Proof. vm_refl. Qed.
Lemma D_16614 : D! W_16614 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_16618 : bv 32 := 0x00e7f733.
Lemma F_16618 : F! 0x16618 W_16618.
Proof. vm_refl. Qed.
Lemma D_16618 : D! W_16618 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_1661c : bv 32 := 0x00700793.
Lemma F_1661c : F! 0x1661c W_1661c.
Proof. vm_refl. Qed.
Lemma D_1661c : D! W_1661c (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_16620 : bv 32 := 0x00d706b3.
Lemma F_16620 : F! 0x16620 W_16620.
Proof. vm_refl. Qed.
Lemma D_16620 : D! W_16620 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_16624 : bv 32 := 0x02d5b023.
Lemma F_16624 : F! 0x16624 W_16624.
Proof. vm_refl. Qed.
Lemma D_16624 : D! W_16624 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_16628 : bv 32 := 0x02c5b823.
Lemma F_16628 : F! 0x16628 W_16628.
Proof. vm_refl. Qed.
Lemma D_16628 : D! W_16628 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_1662c : bv 32 := 0x00a7e663.
Lemma F_1662c : F! 0x1662c W_1662c.
Proof. vm_refl. Qed.
Lemma D_1662c : D! W_1662c (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_16630 : bv 32 := 0x00800513.
Lemma F_16630 : F! 0x16630 W_16630.
Proof. vm_refl. Qed.
Lemma D_16630 : D! W_16630 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_16634 : bv 32 := 0x02a5b423.
Lemma F_16634 : F! 0x16634 W_16634.
Proof. vm_refl. Qed.
Lemma D_16634 : D! W_16634 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_16638 : bv 32 := 0x00d60633.
Lemma F_16638 : F! 0x16638 W_16638.
Proof. vm_refl. Qed.
Lemma D_16638 : D! W_16638 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_1663c : bv 32 := 0x000205b7.
Lemma F_1663c : F! 0x1663c W_1663c.
Proof. vm_refl. Qed.
Lemma D_1663c : D! W_1663c (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_16640 : bv 32 := 0x00a60633.
Lemma F_16640 : F! 0x16640 W_16640.
Proof. vm_refl. Qed.
Lemma D_16640 : D! W_16640 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_16644 : bv 32 := 0x0d15869b.
Lemma F_16644 : F! 0x16644 W_16644.
Proof. vm_refl. Qed.
Lemma D_16644 : D! W_16644 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_16648 : bv 32 := 0x0df60593.
Lemma F_16648 : F! 0x16648 W_16648.
Proof. vm_refl. Qed.
Lemma D_16648 : D! W_16648 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_1664c : bv 32 := 0xff85f593.
Lemma F_1664c : F! 0x1664c W_1664c.
Proof. vm_refl. Qed.
Lemma D_1664c : D! W_1664c (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_16650 : bv 32 := 0x00b4bc23.
Lemma F_16650 : F! 0x16650 W_16650.
Proof. vm_refl. Qed.
Lemma D_16650 : D! W_16650 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_16654 : bv 32 := 0x02a4b023.
Lemma F_16654 : F! 0x16654 W_16654.
Proof. vm_refl. Qed.
Lemma D_16654 : D! W_16654 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_16658 : bv 32 := 0x02d5ea63.
Lemma F_16658 : F! 0x16658 W_16658.
Proof. vm_refl. Qed.
Lemma D_16658 : D! W_16658 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_1668c : bv 32 := 0x0001a697.
Lemma F_1668c : F! 0x1668c W_1668c.
Proof. vm_refl. Qed.
Lemma D_1668c : D! W_1668c (Auipc 13 26).
Proof. vm_refl. Qed.
Definition W_16690 : bv 32 := 0x0104b983.
Lemma F_16690 : F! 0x16690 W_16690.
Proof. vm_refl. Qed.
Lemma D_16690 : D! W_16690 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_16694 : bv 32 := 0x0284b603.
Lemma F_16694 : F! 0x16694 W_16694.
Proof. vm_refl. Qed.
Lemma D_16694 : D! W_16694 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_16698 : bv 32 := 0xfff50713.
Lemma F_16698 : F! 0x16698 W_16698.
Proof. vm_refl. Qed.
Lemma D_16698 : D! W_16698 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_1669c : bv 32 := 0xf3800793.
Lemma F_1669c : F! 0x1669c W_1669c.
Proof. vm_refl. Qed.
Lemma D_1669c : D! W_1669c (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_166a0 : bv 32 := 0x29468513.
Lemma F_166a0 : F! 0x166a0 W_166a0.
Proof. vm_refl. Qed.
Lemma D_166a0 : D! W_166a0 (OpImm ALU_ADD 10 13 660).
Proof. vm_refl. Qed.
Definition W_166a4 : bv 32 := 0x40a787b3.
Lemma F_166a4 : F! 0x166a4 W_166a4.
Proof. vm_refl. Qed.
Lemma D_166a4 : D! W_166a4 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_166a8 : bv 32 := 0x00f77733.
Lemma F_166a8 : F! 0x166a8 W_166a8.
Proof. vm_refl. Qed.
Lemma D_166a8 : D! W_166a8 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_166ac : bv 32 := 0xfff64693.
Lemma F_166ac : F! 0x166ac W_166ac.
Proof. vm_refl. Qed.
Lemma D_166ac : D! W_166ac (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_166b0 : bv 32 := 0x00e50933.
Lemma F_166b0 : F! 0x166b0 W_166b0.
Proof. vm_refl. Qed.
Lemma D_166b0 : D! W_166b0 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_166b4 : bv 32 := 0x00369693.
Lemma F_166b4 : F! 0x166b4 W_166b4.
Proof. vm_refl. Qed.
Lemma D_166b4 : D! W_166b4 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_166b8 : bv 32 := 0x00d506b3.
Lemma F_166b8 : F! 0x166b8 W_166b8.
Proof. vm_refl. Qed.
Lemma D_166b8 : D! W_166b8 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_166bc : bv 32 := 0x00b68a33.
Lemma F_166bc : F! 0x166bc W_166bc.
Proof. vm_refl. Qed.
Lemma D_166bc : D! W_166bc (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_166c0 : bv 32 := 0x0c890413.
Lemma F_166c0 : F! 0x166c0 W_166c0.
Proof. vm_refl. Qed.
Lemma D_166c0 : D! W_166c0 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_166c4 : bv 32 := 0x04098463.
Lemma F_166c4 : F! 0x166c4 W_166c4.
Proof. vm_refl. Qed.
Lemma D_166c4 : D! W_166c4 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_1670c : bv 32 := 0x00ca3023.
Lemma F_1670c : F! 0x1670c W_1670c.
Proof. vm_refl. Qed.
Lemma D_1670c : D! W_1670c (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_16710 : bv 32 := 0x0d493023.
Lemma F_16710 : F! 0x16710 W_16710.
Proof. vm_refl. Qed.
Lemma D_16710 : D! W_16710 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_16714 : bv 32 := 0x01293023.
Lemma F_16714 : F! 0x16714 W_16714.
Proof. vm_refl. Qed.
Lemma D_16714 : D! W_16714 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_16718 : bv 32 := 0x00040513.
Lemma F_16718 : F! 0x16718 W_16718.
Proof. vm_refl. Qed.
Lemma D_16718 : D! W_16718 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_1671c : bv 32 := 0x5f5070ef.
Lemma F_1671c : F! 0x1671c W_1671c.
Proof. vm_refl. Qed.
Lemma D_1671c : D! W_1671c (Jal 1 32244).
Proof. vm_refl. Qed.
Definition W_16720 : bv 32 := 0x04054a63.
Lemma F_16720 : F! 0x16720 W_16720.
Proof. vm_refl. Qed.
Lemma D_16720 : D! W_16720 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_16724 : bv 32 := 0x00051663.
Lemma F_16724 : F! 0x16724 W_16724.
Proof. vm_refl. Qed.
Lemma D_16724 : D! W_16724 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_16728 : bv 32 := 0x00100513.
Lemma F_16728 : F! 0x16728 W_16728.
Proof. vm_refl. Qed.
Lemma D_16728 : D! W_16728 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_1672c : bv 32 := 0x00a48023.
Lemma F_1672c : F! 0x1672c W_1672c.
Proof. vm_refl. Qed.
Lemma D_1672c : D! W_1672c (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_16730 : bv 32 := 0x00200513.
Lemma F_16730 : F! 0x16730 W_16730.
Proof. vm_refl. Qed.
Lemma D_16730 : D! W_16730 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_16734 : bv 32 := 0x0003a597.
Lemma F_16734 : F! 0x16734 W_16734.
Proof. vm_refl. Qed.
Lemma D_16734 : D! W_16734 (Auipc 11 58).
Proof. vm_refl. Qed.
Definition W_16738 : bv 32 := 0x02a92423.
Lemma F_16738 : F! 0x16738 W_16738.
Proof. vm_refl. Qed.
Lemma D_16738 : D! W_16738 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_1673c : bv 32 := 0x06000893.
Lemma F_1673c : F! 0x1673c W_1673c.
Proof. vm_refl. Qed.
Lemma D_1673c : D! W_1673c (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_16740 : bv 32 := 0x2bc58513.
Lemma F_16740 : F! 0x16740 W_16740.
Proof. vm_refl. Qed.
Lemma D_16740 : D! W_16740 (OpImm ALU_ADD 10 11 700).
Proof. vm_refl. Qed.
Definition W_16744 : bv 32 := 0x03848593.
Lemma F_16744 : F! 0x16744 W_16744.
Proof. vm_refl. Qed.
Lemma D_16744 : D! W_16744 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_16748 : bv 32 := 0x00000073.
Lemma F_16748 : F! 0x16748 W_16748.
Proof. vm_refl. Qed.
Lemma E_16748 : is_ecall W_16748 = true.
Proof. reflexivity. Qed.
Definition W_1674c : bv 32 := 0x07890613.
Lemma F_1674c : F! 0x1674c W_1674c.
Proof. vm_refl. Qed.
Lemma D_1674c : D! W_1674c (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_16750 : bv 32 := 0x02a92023.
Lemma F_16750 : F! 0x16750 W_16750.
Proof. vm_refl. Qed.
Lemma D_16750 : D! W_16750 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_16754 : bv 32 := 0x08b93c23.
Lemma F_16754 : F! 0x16754 W_16754.
Proof. vm_refl. Qed.
Lemma D_16754 : D! W_16754 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_16758 : bv 32 := 0x06c93c23.
Lemma F_16758 : F! 0x16758 W_16758.
Proof. vm_refl. Qed.
Lemma D_16758 : D! W_16758 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_1675c : bv 32 := 0x0003a517.
Lemma F_1675c : F! 0x1675c W_1675c.
Proof. vm_refl. Qed.
Lemma D_1675c : D! W_1675c (Auipc 10 58).
Proof. vm_refl. Qed.
Definition W_16760 : bv 32 := 0x50453503.
Lemma F_16760 : F! 0x16760 W_16760.
Proof. vm_refl. Qed.
Lemma D_16760 : D! W_16760 (Load SZ8 true 10 10 1284).
Proof. vm_refl. Qed.
Definition W_16764 : bv 32 := 0x01293423.
Lemma F_16764 : F! 0x16764 W_16764.
Proof. vm_refl. Qed.
Lemma D_16764 : D! W_16764 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_16768 : bv 32 := 0x01293823.
Lemma F_16768 : F! 0x16768 W_16768.
Proof. vm_refl. Qed.
Lemma D_16768 : D! W_16768 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_1676c : bv 32 := 0x00a93c23.
Lemma F_1676c : F! 0x1676c W_1676c.
Proof. vm_refl. Qed.
Lemma D_1676c : D! W_1676c (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_16770 : bv 32 := 0x0080006f.
Lemma F_16770 : F! 0x16770 W_16770.
Proof. vm_refl. Qed.
Lemma D_16770 : D! W_16770 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_16778 : bv 32 := 0x03813083.
Lemma F_16778 : F! 0x16778 W_16778.
Proof. vm_refl. Qed.
Lemma D_16778 : D! W_16778 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_1677c : bv 32 := 0x03013403.
Lemma F_1677c : F! 0x1677c W_1677c.
Proof. vm_refl. Qed.
Lemma D_1677c : D! W_1677c (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_16780 : bv 32 := 0x02813483.
Lemma F_16780 : F! 0x16780 W_16780.
Proof. vm_refl. Qed.
Lemma D_16780 : D! W_16780 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_16784 : bv 32 := 0x02013903.
Lemma F_16784 : F! 0x16784 W_16784.
Proof. vm_refl. Qed.
Lemma D_16784 : D! W_16784 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_16788 : bv 32 := 0x01813983.
Lemma F_16788 : F! 0x16788 W_16788.
Proof. vm_refl. Qed.
Lemma D_16788 : D! W_16788 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_1678c : bv 32 := 0x01013a03.
Lemma F_1678c : F! 0x1678c W_1678c.
Proof. vm_refl. Qed.
Lemma D_1678c : D! W_1678c (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_16790 : bv 32 := 0x00813a83.
Lemma F_16790 : F! 0x16790 W_16790.
Proof. vm_refl. Qed.
Lemma D_16790 : D! W_16790 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_16794 : bv 32 := 0x04010113.
Lemma F_16794 : F! 0x16794 W_16794.
Proof. vm_refl. Qed.
Lemma D_16794 : D! W_16794 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_16798 : bv 32 := 0x00008067.
Lemma F_16798 : F! 0x16798 W_16798.
Proof. vm_refl. Qed.
Lemma D_16798 : D! W_16798 (Jalr 0 1 0).
Proof. vm_refl. Qed.
