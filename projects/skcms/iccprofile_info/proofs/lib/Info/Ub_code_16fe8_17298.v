(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
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
Definition W_16fe8 : bv 32 := 0xfc010113.
Lemma F_16fe8 : F! 0x16fe8 W_16fe8.
Proof. vm_refl. Qed.
Lemma D_16fe8 : D! W_16fe8 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_16fec : bv 32 := 0x02113c23.
Lemma F_16fec : F! 0x16fec W_16fec.
Proof. vm_refl. Qed.
Lemma D_16fec : D! W_16fec (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_16ff0 : bv 32 := 0x02813823.
Lemma F_16ff0 : F! 0x16ff0 W_16ff0.
Proof. vm_refl. Qed.
Lemma D_16ff0 : D! W_16ff0 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_16ff4 : bv 32 := 0x02913423.
Lemma F_16ff4 : F! 0x16ff4 W_16ff4.
Proof. vm_refl. Qed.
Lemma D_16ff4 : D! W_16ff4 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_16ff8 : bv 32 := 0x03213023.
Lemma F_16ff8 : F! 0x16ff8 W_16ff8.
Proof. vm_refl. Qed.
Lemma D_16ff8 : D! W_16ff8 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_16ffc : bv 32 := 0x01313c23.
Lemma F_16ffc : F! 0x16ffc W_16ffc.
Proof. vm_refl. Qed.
Lemma D_16ffc : D! W_16ffc (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_17000 : bv 32 := 0x01413823.
Lemma F_17000 : F! 0x17000 W_17000.
Proof. vm_refl. Qed.
Lemma D_17000 : D! W_17000 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_17004 : bv 32 := 0x01513423.
Lemma F_17004 : F! 0x17004 W_17004.
Proof. vm_refl. Qed.
Lemma D_17004 : D! W_17004 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_17008 : bv 32 := 0x02853683.
Lemma F_17008 : F! 0x17008 W_17008.
Proof. vm_refl. Qed.
Lemma D_17008 : D! W_17008 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_1700c : bv 32 := 0x0003a597.
Lemma F_1700c : F! 0x1700c W_1700c.
Proof. vm_refl. Qed.
Lemma D_1700c : D! W_1700c (Auipc 11 58).
Proof. vm_refl. Qed.
Definition W_17010 : bv 32 := 0x4d458593.
Lemma F_17010 : F! 0x17010 W_17010.
Proof. vm_refl. Qed.
Lemma D_17010 : D! W_17010 (OpImm ALU_ADD 11 11 1236).
Proof. vm_refl. Qed.
Definition W_17014 : bv 32 := 0x0003a617.
Lemma F_17014 : F! 0x17014 W_17014.
Proof. vm_refl. Qed.
Lemma D_17014 : D! W_17014 (Auipc 12 58).
Proof. vm_refl. Qed.
Definition W_17018 : bv 32 := 0x75460493.
Lemma F_17018 : F! 0x17018 W_17018.
Proof. vm_refl. Qed.
Lemma D_17018 : D! W_17018 (OpImm ALU_ADD 9 12 1876).
Proof. vm_refl. Qed.
Definition W_1701c : bv 32 := 0x0c068e63.
Lemma F_1701c : F! 0x1701c W_1701c.
Proof. vm_refl. Qed.
Lemma D_1701c : D! W_1701c (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_17020 : bv 32 := 0x00000613.
Lemma F_17020 : F! 0x17020 W_17020.
Proof. vm_refl. Qed.
Lemma D_17020 : D! W_17020 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_17024 : bv 32 := 0x00000893.
Lemma F_17024 : F! 0x17024 W_17024.
Proof. vm_refl. Qed.
Lemma D_17024 : D! W_17024 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_17028 : bv 32 := 0x0000a717.
Lemma F_17028 : F! 0x17028 W_17028.
Proof. vm_refl. Qed.
Lemma D_17028 : D! W_17028 (Auipc 14 10).
Proof. vm_refl. Qed.
Definition W_1702c : bv 32 := 0x01853783.
Lemma F_1702c : F! 0x1702c W_1702c.
Proof. vm_refl. Qed.
Lemma D_1702c : D! W_1702c (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_17030 : bv 32 := 0x02053503.
Lemma F_17030 : F! 0x17030 W_17030.
Proof. vm_refl. Qed.
Lemma D_17030 : D! W_17030 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_17034 : bv 32 := 0x00600813.
Lemma F_17034 : F! 0x17034 W_17034.
Proof. vm_refl. Qed.
Lemma D_17034 : D! W_17034 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_17038 : bv 32 := 0x00009297.
Lemma F_17038 : F! 0x17038 W_17038.
Proof. vm_refl. Qed.
Lemma D_17038 : D! W_17038 (Auipc 5 9).
Proof. vm_refl. Qed.
Definition W_1703c : bv 32 := 0x35076f03.
Lemma F_1703c : F! 0x1703c W_1703c.
Proof. vm_refl. Qed.
Lemma D_1703c : D! W_1703c (Load SZ4 false 30 14 848).
Proof. vm_refl. Qed.
Definition W_17040 : bv 32 := 0x0a82b283.
Lemma F_17040 : F! 0x17040 W_17040.
Proof. vm_refl. Qed.
Lemma D_17040 : D! W_17040 (Load SZ8 true 5 5 168).
Proof. vm_refl. Qed.
Definition W_17044 : bv 32 := 0x00200313.
Lemma F_17044 : F! 0x17044 W_17044.
Proof. vm_refl. Qed.
Lemma D_17044 : D! W_17044 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_17048 : bv 32 := 0x00700393.
Lemma F_17048 : F! 0x17048 W_17048.
Proof. vm_refl. Qed.
Lemma D_17048 : D! W_17048 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_1704c : bv 32 := 0x6474ee37.
Lemma F_1704c : F! 0x1704c W_1704c.
Proof. vm_refl. Qed.
Lemma D_1704c : D! W_1704c (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_17050 : bv 32 := 0x551e0e1b.
Lemma F_17050 : F! 0x17050 W_17050.
Proof. vm_refl. Qed.
Lemma D_17050 : D! W_17050 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_17054 : bv 32 := 0x00078e93.
Lemma F_17054 : F! 0x17054 W_17054.
Proof. vm_refl. Qed.
Lemma D_17054 : D! W_17054 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_17058 : bv 32 := 0x0180006f.
Lemma F_17058 : F! 0x17058 W_17058.
Proof. vm_refl. Qed.
Lemma D_17058 : D! W_17058 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_1705c : bv 32 := 0x010eb603.
Lemma F_1705c : F! 0x1705c W_1705c.
Proof. vm_refl. Qed.
Lemma D_1705c : D! W_1705c (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_17060 : bv 32 := 0x40c78633.
Lemma F_17060 : F! 0x17060 W_17060.
Proof. vm_refl. Qed.
Lemma D_17060 : D! W_17060 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_17064 : bv 32 := 0xfff68693.
Lemma F_17064 : F! 0x17064 W_17064.
Proof. vm_refl. Qed.
Lemma D_17064 : D! W_17064 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_17068 : bv 32 := 0x00ae8eb3.
Lemma F_17068 : F! 0x17068 W_17068.
Proof. vm_refl. Qed.
Lemma D_17068 : D! W_17068 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_1706c : bv 32 := 0x04068a63.
Lemma F_1706c : F! 0x1706c W_1706c.
Proof. vm_refl. Qed.
Lemma D_1706c : D! W_1706c (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_17070 : bv 32 := 0x000ea403.
Lemma F_17070 : F! 0x17070 W_17070.
Proof. vm_refl. Qed.
Lemma D_17070 : D! W_17070 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_17074 : bv 32 := 0xff0404e3.
Lemma F_17074 : F! 0x17074 W_17074.
Proof. vm_refl. Qed.
Lemma D_17074 : D! W_17074 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_17078 : bv 32 := 0x00028a63.
Lemma F_17078 : F! 0x17078 W_17078.
Proof. vm_refl. Qed.
Lemma D_17078 : D! W_17078 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_1708c : bv 32 := 0x000e8f93.
Lemma F_1708c : F! 0x1708c W_1708c.
Proof. vm_refl. Qed.
Lemma D_1708c : D! W_1708c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_17090 : bv 32 := 0x00740463.
Lemma F_17090 : F! 0x17090 W_17090.
Proof. vm_refl. Qed.
Lemma D_17090 : D! W_17090 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_17094 : bv 32 := 0x00088f93.
Lemma F_17094 : F! 0x17094 W_17094.
Proof. vm_refl. Qed.
Lemma D_17094 : D! W_17094 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_17098 : bv 32 := 0x03c41063.
Lemma F_17098 : F! 0x17098 W_17098.
Proof. vm_refl. Qed.
Lemma D_17098 : D! W_17098 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_1709c : bv 32 := 0x028eb883.
Lemma F_1709c : F! 0x1709c W_1709c.
Proof. vm_refl. Qed.
Lemma D_1709c : D! W_1709c (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_170a0 : bv 32 := 0x011f7c63.
Lemma F_170a0 : F! 0x170a0 W_170a0.
Proof. vm_refl. Qed.
Lemma D_170a0 : D! W_170a0 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_170b8 : bv 32 := 0x000f8893.
Lemma F_170b8 : F! 0x170b8 W_170b8.
Proof. vm_refl. Qed.
Lemma D_170b8 : D! W_170b8 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_170bc : bv 32 := 0xfa9ff06f.
Lemma F_170bc : F! 0x170bc W_170bc.
Proof. vm_refl. Qed.
Lemma D_170bc : D! W_170bc (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_170c0 : bv 32 := 0x02088c63.
Lemma F_170c0 : F! 0x170c0 W_170c0.
Proof. vm_refl. Qed.
Lemma D_170c0 : D! W_170c0 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_170f8 : bv 32 := 0x0105b603.
Lemma F_170f8 : F! 0x170f8 W_170f8.
Proof. vm_refl. Qed.
Lemma D_170f8 : D! W_170f8 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_170fc : bv 32 := 0x0205b683.
Lemma F_170fc : F! 0x170fc W_170fc.
Proof. vm_refl. Qed.
Lemma D_170fc : D! W_170fc (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_17100 : bv 32 := 0x0285b503.
Lemma F_17100 : F! 0x17100 W_17100.
Proof. vm_refl. Qed.
Lemma D_17100 : D! W_17100 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_17104 : bv 32 := 0x00c68733.
Lemma F_17104 : F! 0x17104 W_17104.
Proof. vm_refl. Qed.
Lemma D_17104 : D! W_17104 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_17108 : bv 32 := 0xfff50793.
Lemma F_17108 : F! 0x17108 W_17108.
Proof. vm_refl. Qed.
Lemma D_17108 : D! W_17108 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_1710c : bv 32 := 0x40e00733.
Lemma F_1710c : F! 0x1710c W_1710c.
Proof. vm_refl. Qed.
Lemma D_1710c : D! W_1710c (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_17110 : bv 32 := 0x00c7f633.
Lemma F_17110 : F! 0x17110 W_17110.
Proof. vm_refl. Qed.
Lemma D_17110 : D! W_17110 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_17114 : bv 32 := 0x00e7f733.
Lemma F_17114 : F! 0x17114 W_17114.
Proof. vm_refl. Qed.
Lemma D_17114 : D! W_17114 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_17118 : bv 32 := 0x00700793.
Lemma F_17118 : F! 0x17118 W_17118.
Proof. vm_refl. Qed.
Lemma D_17118 : D! W_17118 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_1711c : bv 32 := 0x00d706b3.
Lemma F_1711c : F! 0x1711c W_1711c.
Proof. vm_refl. Qed.
Lemma D_1711c : D! W_1711c (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_17120 : bv 32 := 0x02d5b023.
Lemma F_17120 : F! 0x17120 W_17120.
Proof. vm_refl. Qed.
Lemma D_17120 : D! W_17120 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_17124 : bv 32 := 0x02c5b823.
Lemma F_17124 : F! 0x17124 W_17124.
Proof. vm_refl. Qed.
Lemma D_17124 : D! W_17124 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_17128 : bv 32 := 0x00a7e663.
Lemma F_17128 : F! 0x17128 W_17128.
Proof. vm_refl. Qed.
Lemma D_17128 : D! W_17128 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_1712c : bv 32 := 0x00800513.
Lemma F_1712c : F! 0x1712c W_1712c.
Proof. vm_refl. Qed.
Lemma D_1712c : D! W_1712c (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_17130 : bv 32 := 0x02a5b423.
Lemma F_17130 : F! 0x17130 W_17130.
Proof. vm_refl. Qed.
Lemma D_17130 : D! W_17130 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_17134 : bv 32 := 0x00d60633.
Lemma F_17134 : F! 0x17134 W_17134.
Proof. vm_refl. Qed.
Lemma D_17134 : D! W_17134 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_17138 : bv 32 := 0x000205b7.
Lemma F_17138 : F! 0x17138 W_17138.
Proof. vm_refl. Qed.
Lemma D_17138 : D! W_17138 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_1713c : bv 32 := 0x00a60633.
Lemma F_1713c : F! 0x1713c W_1713c.
Proof. vm_refl. Qed.
Lemma D_1713c : D! W_1713c (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_17140 : bv 32 := 0x0d15869b.
Lemma F_17140 : F! 0x17140 W_17140.
Proof. vm_refl. Qed.
Lemma D_17140 : D! W_17140 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_17144 : bv 32 := 0x0df60593.
Lemma F_17144 : F! 0x17144 W_17144.
Proof. vm_refl. Qed.
Lemma D_17144 : D! W_17144 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_17148 : bv 32 := 0xff85f593.
Lemma F_17148 : F! 0x17148 W_17148.
Proof. vm_refl. Qed.
Lemma D_17148 : D! W_17148 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_1714c : bv 32 := 0x00b4bc23.
Lemma F_1714c : F! 0x1714c W_1714c.
Proof. vm_refl. Qed.
Lemma D_1714c : D! W_1714c (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_17150 : bv 32 := 0x02a4b023.
Lemma F_17150 : F! 0x17150 W_17150.
Proof. vm_refl. Qed.
Lemma D_17150 : D! W_17150 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_17154 : bv 32 := 0x02d5ea63.
Lemma F_17154 : F! 0x17154 W_17154.
Proof. vm_refl. Qed.
Lemma D_17154 : D! W_17154 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_17188 : bv 32 := 0x0001a697.
Lemma F_17188 : F! 0x17188 W_17188.
Proof. vm_refl. Qed.
Lemma D_17188 : D! W_17188 (Auipc 13 26).
Proof. vm_refl. Qed.
Definition W_1718c : bv 32 := 0x0104b983.
Lemma F_1718c : F! 0x1718c W_1718c.
Proof. vm_refl. Qed.
Lemma D_1718c : D! W_1718c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_17190 : bv 32 := 0x0284b603.
Lemma F_17190 : F! 0x17190 W_17190.
Proof. vm_refl. Qed.
Lemma D_17190 : D! W_17190 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_17194 : bv 32 := 0xfff50713.
Lemma F_17194 : F! 0x17194 W_17194.
Proof. vm_refl. Qed.
Lemma D_17194 : D! W_17194 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_17198 : bv 32 := 0xf3800793.
Lemma F_17198 : F! 0x17198 W_17198.
Proof. vm_refl. Qed.
Lemma D_17198 : D! W_17198 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_1719c : bv 32 := 0x28868513.
Lemma F_1719c : F! 0x1719c W_1719c.
Proof. vm_refl. Qed.
Lemma D_1719c : D! W_1719c (OpImm ALU_ADD 10 13 648).
Proof. vm_refl. Qed.
Definition W_171a0 : bv 32 := 0x40a787b3.
Lemma F_171a0 : F! 0x171a0 W_171a0.
Proof. vm_refl. Qed.
Lemma D_171a0 : D! W_171a0 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_171a4 : bv 32 := 0x00f77733.
Lemma F_171a4 : F! 0x171a4 W_171a4.
Proof. vm_refl. Qed.
Lemma D_171a4 : D! W_171a4 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_171a8 : bv 32 := 0xfff64693.
Lemma F_171a8 : F! 0x171a8 W_171a8.
Proof. vm_refl. Qed.
Lemma D_171a8 : D! W_171a8 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_171ac : bv 32 := 0x00e50933.
Lemma F_171ac : F! 0x171ac W_171ac.
Proof. vm_refl. Qed.
Lemma D_171ac : D! W_171ac (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_171b0 : bv 32 := 0x00369693.
Lemma F_171b0 : F! 0x171b0 W_171b0.
Proof. vm_refl. Qed.
Lemma D_171b0 : D! W_171b0 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_171b4 : bv 32 := 0x00d506b3.
Lemma F_171b4 : F! 0x171b4 W_171b4.
Proof. vm_refl. Qed.
Lemma D_171b4 : D! W_171b4 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_171b8 : bv 32 := 0x00b68a33.
Lemma F_171b8 : F! 0x171b8 W_171b8.
Proof. vm_refl. Qed.
Lemma D_171b8 : D! W_171b8 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_171bc : bv 32 := 0x0c890413.
Lemma F_171bc : F! 0x171bc W_171bc.
Proof. vm_refl. Qed.
Lemma D_171bc : D! W_171bc (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_171c0 : bv 32 := 0x04098463.
Lemma F_171c0 : F! 0x171c0 W_171c0.
Proof. vm_refl. Qed.
Lemma D_171c0 : D! W_171c0 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_17208 : bv 32 := 0x00ca3023.
Lemma F_17208 : F! 0x17208 W_17208.
Proof. vm_refl. Qed.
Lemma D_17208 : D! W_17208 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_1720c : bv 32 := 0x0d493023.
Lemma F_1720c : F! 0x1720c W_1720c.
Proof. vm_refl. Qed.
Lemma D_1720c : D! W_1720c (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_17210 : bv 32 := 0x01293023.
Lemma F_17210 : F! 0x17210 W_17210.
Proof. vm_refl. Qed.
Lemma D_17210 : D! W_17210 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_17214 : bv 32 := 0x00040513.
Lemma F_17214 : F! 0x17214 W_17214.
Proof. vm_refl. Qed.
Lemma D_17214 : D! W_17214 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_17218 : bv 32 := 0x5f5070ef.
Lemma F_17218 : F! 0x17218 W_17218.
Proof. vm_refl. Qed.
Lemma D_17218 : D! W_17218 (Jal 1 32244).
Proof. vm_refl. Qed.
Definition W_1721c : bv 32 := 0x04054a63.
Lemma F_1721c : F! 0x1721c W_1721c.
Proof. vm_refl. Qed.
Lemma D_1721c : D! W_1721c (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_17220 : bv 32 := 0x00051663.
Lemma F_17220 : F! 0x17220 W_17220.
Proof. vm_refl. Qed.
Lemma D_17220 : D! W_17220 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_17224 : bv 32 := 0x00100513.
Lemma F_17224 : F! 0x17224 W_17224.
Proof. vm_refl. Qed.
Lemma D_17224 : D! W_17224 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_17228 : bv 32 := 0x00a48023.
Lemma F_17228 : F! 0x17228 W_17228.
Proof. vm_refl. Qed.
Lemma D_17228 : D! W_17228 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_1722c : bv 32 := 0x00200513.
Lemma F_1722c : F! 0x1722c W_1722c.
Proof. vm_refl. Qed.
Lemma D_1722c : D! W_1722c (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_17230 : bv 32 := 0x0003a597.
Lemma F_17230 : F! 0x17230 W_17230.
Proof. vm_refl. Qed.
Lemma D_17230 : D! W_17230 (Auipc 11 58).
Proof. vm_refl. Qed.
Definition W_17234 : bv 32 := 0x02a92423.
Lemma F_17234 : F! 0x17234 W_17234.
Proof. vm_refl. Qed.
Lemma D_17234 : D! W_17234 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_17238 : bv 32 := 0x06000893.
Lemma F_17238 : F! 0x17238 W_17238.
Proof. vm_refl. Qed.
Lemma D_17238 : D! W_17238 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_1723c : bv 32 := 0x2b058513.
Lemma F_1723c : F! 0x1723c W_1723c.
Proof. vm_refl. Qed.
Lemma D_1723c : D! W_1723c (OpImm ALU_ADD 10 11 688).
Proof. vm_refl. Qed.
Definition W_17240 : bv 32 := 0x03848593.
Lemma F_17240 : F! 0x17240 W_17240.
Proof. vm_refl. Qed.
Lemma D_17240 : D! W_17240 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_17244 : bv 32 := 0x00000073.
Lemma F_17244 : F! 0x17244 W_17244.
Proof. vm_refl. Qed.
Lemma E_17244 : is_ecall W_17244 = true.
Proof. reflexivity. Qed.
Definition W_17248 : bv 32 := 0x07890613.
Lemma F_17248 : F! 0x17248 W_17248.
Proof. vm_refl. Qed.
Lemma D_17248 : D! W_17248 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_1724c : bv 32 := 0x02a92023.
Lemma F_1724c : F! 0x1724c W_1724c.
Proof. vm_refl. Qed.
Lemma D_1724c : D! W_1724c (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_17250 : bv 32 := 0x08b93c23.
Lemma F_17250 : F! 0x17250 W_17250.
Proof. vm_refl. Qed.
Lemma D_17250 : D! W_17250 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_17254 : bv 32 := 0x06c93c23.
Lemma F_17254 : F! 0x17254 W_17254.
Proof. vm_refl. Qed.
Lemma D_17254 : D! W_17254 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_17258 : bv 32 := 0x0003a517.
Lemma F_17258 : F! 0x17258 W_17258.
Proof. vm_refl. Qed.
Lemma D_17258 : D! W_17258 (Auipc 10 58).
Proof. vm_refl. Qed.
Definition W_1725c : bv 32 := 0x4f853503.
Lemma F_1725c : F! 0x1725c W_1725c.
Proof. vm_refl. Qed.
Lemma D_1725c : D! W_1725c (Load SZ8 true 10 10 1272).
Proof. vm_refl. Qed.
Definition W_17260 : bv 32 := 0x01293423.
Lemma F_17260 : F! 0x17260 W_17260.
Proof. vm_refl. Qed.
Lemma D_17260 : D! W_17260 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_17264 : bv 32 := 0x01293823.
Lemma F_17264 : F! 0x17264 W_17264.
Proof. vm_refl. Qed.
Lemma D_17264 : D! W_17264 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_17268 : bv 32 := 0x00a93c23.
Lemma F_17268 : F! 0x17268 W_17268.
Proof. vm_refl. Qed.
Lemma D_17268 : D! W_17268 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_1726c : bv 32 := 0x0080006f.
Lemma F_1726c : F! 0x1726c W_1726c.
Proof. vm_refl. Qed.
Lemma D_1726c : D! W_1726c (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_17274 : bv 32 := 0x03813083.
Lemma F_17274 : F! 0x17274 W_17274.
Proof. vm_refl. Qed.
Lemma D_17274 : D! W_17274 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_17278 : bv 32 := 0x03013403.
Lemma F_17278 : F! 0x17278 W_17278.
Proof. vm_refl. Qed.
Lemma D_17278 : D! W_17278 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_1727c : bv 32 := 0x02813483.
Lemma F_1727c : F! 0x1727c W_1727c.
Proof. vm_refl. Qed.
Lemma D_1727c : D! W_1727c (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_17280 : bv 32 := 0x02013903.
Lemma F_17280 : F! 0x17280 W_17280.
Proof. vm_refl. Qed.
Lemma D_17280 : D! W_17280 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_17284 : bv 32 := 0x01813983.
Lemma F_17284 : F! 0x17284 W_17284.
Proof. vm_refl. Qed.
Lemma D_17284 : D! W_17284 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_17288 : bv 32 := 0x01013a03.
Lemma F_17288 : F! 0x17288 W_17288.
Proof. vm_refl. Qed.
Lemma D_17288 : D! W_17288 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_1728c : bv 32 := 0x00813a83.
Lemma F_1728c : F! 0x1728c W_1728c.
Proof. vm_refl. Qed.
Lemma D_1728c : D! W_1728c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_17290 : bv 32 := 0x04010113.
Lemma F_17290 : F! 0x17290 W_17290.
Proof. vm_refl. Qed.
Lemma D_17290 : D! W_17290 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_17294 : bv 32 := 0x00008067.
Lemma F_17294 : F! 0x17294 W_17294.
Proof. vm_refl. Qed.
Lemma D_17294 : D! W_17294 (Jalr 0 1 0).
Proof. vm_refl. Qed.
