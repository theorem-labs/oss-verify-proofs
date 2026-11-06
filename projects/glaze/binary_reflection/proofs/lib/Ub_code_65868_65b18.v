(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
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
Definition W_65868 : bv 32 := 0xfc010113.
Lemma F_65868 : F! 0x65868 W_65868.
Proof. vm_refl. Qed.
Lemma D_65868 : D! W_65868 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_6586c : bv 32 := 0x02113c23.
Lemma F_6586c : F! 0x6586c W_6586c.
Proof. vm_refl. Qed.
Lemma D_6586c : D! W_6586c (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_65870 : bv 32 := 0x02813823.
Lemma F_65870 : F! 0x65870 W_65870.
Proof. vm_refl. Qed.
Lemma D_65870 : D! W_65870 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_65874 : bv 32 := 0x02913423.
Lemma F_65874 : F! 0x65874 W_65874.
Proof. vm_refl. Qed.
Lemma D_65874 : D! W_65874 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_65878 : bv 32 := 0x03213023.
Lemma F_65878 : F! 0x65878 W_65878.
Proof. vm_refl. Qed.
Lemma D_65878 : D! W_65878 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_6587c : bv 32 := 0x01313c23.
Lemma F_6587c : F! 0x6587c W_6587c.
Proof. vm_refl. Qed.
Lemma D_6587c : D! W_6587c (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_65880 : bv 32 := 0x01413823.
Lemma F_65880 : F! 0x65880 W_65880.
Proof. vm_refl. Qed.
Lemma D_65880 : D! W_65880 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_65884 : bv 32 := 0x01513423.
Lemma F_65884 : F! 0x65884 W_65884.
Proof. vm_refl. Qed.
Lemma D_65884 : D! W_65884 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_65888 : bv 32 := 0x02853683.
Lemma F_65888 : F! 0x65888 W_65888.
Proof. vm_refl. Qed.
Lemma D_65888 : D! W_65888 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_6588c : bv 32 := 0x00045597.
Lemma F_6588c : F! 0x6588c W_6588c.
Proof. vm_refl. Qed.
Lemma D_6588c : D! W_6588c (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_65890 : bv 32 := 0x30c58593.
Lemma F_65890 : F! 0x65890 W_65890.
Proof. vm_refl. Qed.
Lemma D_65890 : D! W_65890 (OpImm ALU_ADD 11 11 780).
Proof. vm_refl. Qed.
Definition W_65894 : bv 32 := 0x00045617.
Lemma F_65894 : F! 0x65894 W_65894.
Proof. vm_refl. Qed.
Lemma D_65894 : D! W_65894 (Auipc 12 69).
Proof. vm_refl. Qed.
Definition W_65898 : bv 32 := 0x58c60493.
Lemma F_65898 : F! 0x65898 W_65898.
Proof. vm_refl. Qed.
Lemma D_65898 : D! W_65898 (OpImm ALU_ADD 9 12 1420).
Proof. vm_refl. Qed.
Definition W_6589c : bv 32 := 0x0c068e63.
Lemma F_6589c : F! 0x6589c W_6589c.
Proof. vm_refl. Qed.
Lemma D_6589c : D! W_6589c (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_658a0 : bv 32 := 0x00000613.
Lemma F_658a0 : F! 0x658a0 W_658a0.
Proof. vm_refl. Qed.
Lemma D_658a0 : D! W_658a0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_658a4 : bv 32 := 0x00000893.
Lemma F_658a4 : F! 0x658a4 W_658a4.
Proof. vm_refl. Qed.
Lemma D_658a4 : D! W_658a4 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_658a8 : bv 32 := 0x00014717.
Lemma F_658a8 : F! 0x658a8 W_658a8.
Proof. vm_refl. Qed.
Lemma D_658a8 : D! W_658a8 (Auipc 14 20).
Proof. vm_refl. Qed.
Definition W_658ac : bv 32 := 0x01853783.
Lemma F_658ac : F! 0x658ac W_658ac.
Proof. vm_refl. Qed.
Lemma D_658ac : D! W_658ac (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_658b0 : bv 32 := 0x02053503.
Lemma F_658b0 : F! 0x658b0 W_658b0.
Proof. vm_refl. Qed.
Lemma D_658b0 : D! W_658b0 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_658b4 : bv 32 := 0x00600813.
Lemma F_658b4 : F! 0x658b4 W_658b4.
Proof. vm_refl. Qed.
Lemma D_658b4 : D! W_658b4 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_658b8 : bv 32 := 0x00013297.
Lemma F_658b8 : F! 0x658b8 W_658b8.
Proof. vm_refl. Qed.
Lemma D_658b8 : D! W_658b8 (Auipc 5 19).
Proof. vm_refl. Qed.
Definition W_658bc : bv 32 := 0x71076f03.
Lemma F_658bc : F! 0x658bc W_658bc.
Proof. vm_refl. Qed.
Lemma D_658bc : D! W_658bc (Load SZ4 false 30 14 1808).
Proof. vm_refl. Qed.
Definition W_658c0 : bv 32 := 0x3702b283.
Lemma F_658c0 : F! 0x658c0 W_658c0.
Proof. vm_refl. Qed.
Lemma D_658c0 : D! W_658c0 (Load SZ8 true 5 5 880).
Proof. vm_refl. Qed.
Definition W_658c4 : bv 32 := 0x00200313.
Lemma F_658c4 : F! 0x658c4 W_658c4.
Proof. vm_refl. Qed.
Lemma D_658c4 : D! W_658c4 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_658c8 : bv 32 := 0x00700393.
Lemma F_658c8 : F! 0x658c8 W_658c8.
Proof. vm_refl. Qed.
Lemma D_658c8 : D! W_658c8 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_658cc : bv 32 := 0x6474ee37.
Lemma F_658cc : F! 0x658cc W_658cc.
Proof. vm_refl. Qed.
Lemma D_658cc : D! W_658cc (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_658d0 : bv 32 := 0x551e0e1b.
Lemma F_658d0 : F! 0x658d0 W_658d0.
Proof. vm_refl. Qed.
Lemma D_658d0 : D! W_658d0 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_658d4 : bv 32 := 0x00078e93.
Lemma F_658d4 : F! 0x658d4 W_658d4.
Proof. vm_refl. Qed.
Lemma D_658d4 : D! W_658d4 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_658d8 : bv 32 := 0x0180006f.
Lemma F_658d8 : F! 0x658d8 W_658d8.
Proof. vm_refl. Qed.
Lemma D_658d8 : D! W_658d8 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_658dc : bv 32 := 0x010eb603.
Lemma F_658dc : F! 0x658dc W_658dc.
Proof. vm_refl. Qed.
Lemma D_658dc : D! W_658dc (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_658e0 : bv 32 := 0x40c78633.
Lemma F_658e0 : F! 0x658e0 W_658e0.
Proof. vm_refl. Qed.
Lemma D_658e0 : D! W_658e0 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_658e4 : bv 32 := 0xfff68693.
Lemma F_658e4 : F! 0x658e4 W_658e4.
Proof. vm_refl. Qed.
Lemma D_658e4 : D! W_658e4 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_658e8 : bv 32 := 0x00ae8eb3.
Lemma F_658e8 : F! 0x658e8 W_658e8.
Proof. vm_refl. Qed.
Lemma D_658e8 : D! W_658e8 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_658ec : bv 32 := 0x04068a63.
Lemma F_658ec : F! 0x658ec W_658ec.
Proof. vm_refl. Qed.
Lemma D_658ec : D! W_658ec (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_658f0 : bv 32 := 0x000ea403.
Lemma F_658f0 : F! 0x658f0 W_658f0.
Proof. vm_refl. Qed.
Lemma D_658f0 : D! W_658f0 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_658f4 : bv 32 := 0xff0404e3.
Lemma F_658f4 : F! 0x658f4 W_658f4.
Proof. vm_refl. Qed.
Lemma D_658f4 : D! W_658f4 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_658f8 : bv 32 := 0x00028a63.
Lemma F_658f8 : F! 0x658f8 W_658f8.
Proof. vm_refl. Qed.
Lemma D_658f8 : D! W_658f8 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_6590c : bv 32 := 0x000e8f93.
Lemma F_6590c : F! 0x6590c W_6590c.
Proof. vm_refl. Qed.
Lemma D_6590c : D! W_6590c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_65910 : bv 32 := 0x00740463.
Lemma F_65910 : F! 0x65910 W_65910.
Proof. vm_refl. Qed.
Lemma D_65910 : D! W_65910 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_65914 : bv 32 := 0x00088f93.
Lemma F_65914 : F! 0x65914 W_65914.
Proof. vm_refl. Qed.
Lemma D_65914 : D! W_65914 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_65918 : bv 32 := 0x03c41063.
Lemma F_65918 : F! 0x65918 W_65918.
Proof. vm_refl. Qed.
Lemma D_65918 : D! W_65918 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_6591c : bv 32 := 0x028eb883.
Lemma F_6591c : F! 0x6591c W_6591c.
Proof. vm_refl. Qed.
Lemma D_6591c : D! W_6591c (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_65920 : bv 32 := 0x011f7c63.
Lemma F_65920 : F! 0x65920 W_65920.
Proof. vm_refl. Qed.
Lemma D_65920 : D! W_65920 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_65938 : bv 32 := 0x000f8893.
Lemma F_65938 : F! 0x65938 W_65938.
Proof. vm_refl. Qed.
Lemma D_65938 : D! W_65938 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_6593c : bv 32 := 0xfa9ff06f.
Lemma F_6593c : F! 0x6593c W_6593c.
Proof. vm_refl. Qed.
Lemma D_6593c : D! W_6593c (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_65940 : bv 32 := 0x02088c63.
Lemma F_65940 : F! 0x65940 W_65940.
Proof. vm_refl. Qed.
Lemma D_65940 : D! W_65940 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_65978 : bv 32 := 0x0105b603.
Lemma F_65978 : F! 0x65978 W_65978.
Proof. vm_refl. Qed.
Lemma D_65978 : D! W_65978 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_6597c : bv 32 := 0x0205b683.
Lemma F_6597c : F! 0x6597c W_6597c.
Proof. vm_refl. Qed.
Lemma D_6597c : D! W_6597c (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_65980 : bv 32 := 0x0285b503.
Lemma F_65980 : F! 0x65980 W_65980.
Proof. vm_refl. Qed.
Lemma D_65980 : D! W_65980 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_65984 : bv 32 := 0x00c68733.
Lemma F_65984 : F! 0x65984 W_65984.
Proof. vm_refl. Qed.
Lemma D_65984 : D! W_65984 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_65988 : bv 32 := 0xfff50793.
Lemma F_65988 : F! 0x65988 W_65988.
Proof. vm_refl. Qed.
Lemma D_65988 : D! W_65988 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_6598c : bv 32 := 0x40e00733.
Lemma F_6598c : F! 0x6598c W_6598c.
Proof. vm_refl. Qed.
Lemma D_6598c : D! W_6598c (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_65990 : bv 32 := 0x00c7f633.
Lemma F_65990 : F! 0x65990 W_65990.
Proof. vm_refl. Qed.
Lemma D_65990 : D! W_65990 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_65994 : bv 32 := 0x00e7f733.
Lemma F_65994 : F! 0x65994 W_65994.
Proof. vm_refl. Qed.
Lemma D_65994 : D! W_65994 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_65998 : bv 32 := 0x00700793.
Lemma F_65998 : F! 0x65998 W_65998.
Proof. vm_refl. Qed.
Lemma D_65998 : D! W_65998 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_6599c : bv 32 := 0x00d706b3.
Lemma F_6599c : F! 0x6599c W_6599c.
Proof. vm_refl. Qed.
Lemma D_6599c : D! W_6599c (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_659a0 : bv 32 := 0x02d5b023.
Lemma F_659a0 : F! 0x659a0 W_659a0.
Proof. vm_refl. Qed.
Lemma D_659a0 : D! W_659a0 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_659a4 : bv 32 := 0x02c5b823.
Lemma F_659a4 : F! 0x659a4 W_659a4.
Proof. vm_refl. Qed.
Lemma D_659a4 : D! W_659a4 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_659a8 : bv 32 := 0x00a7e663.
Lemma F_659a8 : F! 0x659a8 W_659a8.
Proof. vm_refl. Qed.
Lemma D_659a8 : D! W_659a8 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_659ac : bv 32 := 0x00800513.
Lemma F_659ac : F! 0x659ac W_659ac.
Proof. vm_refl. Qed.
Lemma D_659ac : D! W_659ac (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_659b0 : bv 32 := 0x02a5b423.
Lemma F_659b0 : F! 0x659b0 W_659b0.
Proof. vm_refl. Qed.
Lemma D_659b0 : D! W_659b0 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_659b4 : bv 32 := 0x00d60633.
Lemma F_659b4 : F! 0x659b4 W_659b4.
Proof. vm_refl. Qed.
Lemma D_659b4 : D! W_659b4 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_659b8 : bv 32 := 0x000205b7.
Lemma F_659b8 : F! 0x659b8 W_659b8.
Proof. vm_refl. Qed.
Lemma D_659b8 : D! W_659b8 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_659bc : bv 32 := 0x00a60633.
Lemma F_659bc : F! 0x659bc W_659bc.
Proof. vm_refl. Qed.
Lemma D_659bc : D! W_659bc (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_659c0 : bv 32 := 0x0d15869b.
Lemma F_659c0 : F! 0x659c0 W_659c0.
Proof. vm_refl. Qed.
Lemma D_659c0 : D! W_659c0 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_659c4 : bv 32 := 0x0df60593.
Lemma F_659c4 : F! 0x659c4 W_659c4.
Proof. vm_refl. Qed.
Lemma D_659c4 : D! W_659c4 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_659c8 : bv 32 := 0xff85f593.
Lemma F_659c8 : F! 0x659c8 W_659c8.
Proof. vm_refl. Qed.
Lemma D_659c8 : D! W_659c8 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_659cc : bv 32 := 0x00b4bc23.
Lemma F_659cc : F! 0x659cc W_659cc.
Proof. vm_refl. Qed.
Lemma D_659cc : D! W_659cc (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_659d0 : bv 32 := 0x02a4b023.
Lemma F_659d0 : F! 0x659d0 W_659d0.
Proof. vm_refl. Qed.
Lemma D_659d0 : D! W_659d0 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_659d4 : bv 32 := 0x02d5ea63.
Lemma F_659d4 : F! 0x659d4 W_659d4.
Proof. vm_refl. Qed.
Lemma D_659d4 : D! W_659d4 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_65a08 : bv 32 := 0x00025697.
Lemma F_65a08 : F! 0x65a08 W_65a08.
Proof. vm_refl. Qed.
Lemma D_65a08 : D! W_65a08 (Auipc 13 37).
Proof. vm_refl. Qed.
Definition W_65a0c : bv 32 := 0x0104b983.
Lemma F_65a0c : F! 0x65a0c W_65a0c.
Proof. vm_refl. Qed.
Lemma D_65a0c : D! W_65a0c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_65a10 : bv 32 := 0x0284b603.
Lemma F_65a10 : F! 0x65a10 W_65a10.
Proof. vm_refl. Qed.
Lemma D_65a10 : D! W_65a10 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_65a14 : bv 32 := 0xfff50713.
Lemma F_65a14 : F! 0x65a14 W_65a14.
Proof. vm_refl. Qed.
Lemma D_65a14 : D! W_65a14 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_65a18 : bv 32 := 0xf3800793.
Lemma F_65a18 : F! 0x65a18 W_65a18.
Proof. vm_refl. Qed.
Lemma D_65a18 : D! W_65a18 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_65a1c : bv 32 := 0x0c068513.
Lemma F_65a1c : F! 0x65a1c W_65a1c.
Proof. vm_refl. Qed.
Lemma D_65a1c : D! W_65a1c (OpImm ALU_ADD 10 13 192).
Proof. vm_refl. Qed.
Definition W_65a20 : bv 32 := 0x40a787b3.
Lemma F_65a20 : F! 0x65a20 W_65a20.
Proof. vm_refl. Qed.
Lemma D_65a20 : D! W_65a20 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_65a24 : bv 32 := 0x00f77733.
Lemma F_65a24 : F! 0x65a24 W_65a24.
Proof. vm_refl. Qed.
Lemma D_65a24 : D! W_65a24 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_65a28 : bv 32 := 0xfff64693.
Lemma F_65a28 : F! 0x65a28 W_65a28.
Proof. vm_refl. Qed.
Lemma D_65a28 : D! W_65a28 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_65a2c : bv 32 := 0x00e50933.
Lemma F_65a2c : F! 0x65a2c W_65a2c.
Proof. vm_refl. Qed.
Lemma D_65a2c : D! W_65a2c (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_65a30 : bv 32 := 0x00369693.
Lemma F_65a30 : F! 0x65a30 W_65a30.
Proof. vm_refl. Qed.
Lemma D_65a30 : D! W_65a30 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_65a34 : bv 32 := 0x00d506b3.
Lemma F_65a34 : F! 0x65a34 W_65a34.
Proof. vm_refl. Qed.
Lemma D_65a34 : D! W_65a34 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_65a38 : bv 32 := 0x00b68a33.
Lemma F_65a38 : F! 0x65a38 W_65a38.
Proof. vm_refl. Qed.
Lemma D_65a38 : D! W_65a38 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_65a3c : bv 32 := 0x0c890413.
Lemma F_65a3c : F! 0x65a3c W_65a3c.
Proof. vm_refl. Qed.
Lemma D_65a3c : D! W_65a3c (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_65a40 : bv 32 := 0x04098463.
Lemma F_65a40 : F! 0x65a40 W_65a40.
Proof. vm_refl. Qed.
Lemma D_65a40 : D! W_65a40 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_65a88 : bv 32 := 0x00ca3023.
Lemma F_65a88 : F! 0x65a88 W_65a88.
Proof. vm_refl. Qed.
Lemma D_65a88 : D! W_65a88 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_65a8c : bv 32 := 0x0d493023.
Lemma F_65a8c : F! 0x65a8c W_65a8c.
Proof. vm_refl. Qed.
Lemma D_65a8c : D! W_65a8c (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_65a90 : bv 32 := 0x01293023.
Lemma F_65a90 : F! 0x65a90 W_65a90.
Proof. vm_refl. Qed.
Lemma D_65a90 : D! W_65a90 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_65a94 : bv 32 := 0x00040513.
Lemma F_65a94 : F! 0x65a94 W_65a94.
Proof. vm_refl. Qed.
Lemma D_65a94 : D! W_65a94 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_65a98 : bv 32 := 0x1a50e0ef.
Lemma F_65a98 : F! 0x65a98 W_65a98.
Proof. vm_refl. Qed.
Lemma D_65a98 : D! W_65a98 (Jal 1 59812).
Proof. vm_refl. Qed.
Definition W_65a9c : bv 32 := 0x04054a63.
Lemma F_65a9c : F! 0x65a9c W_65a9c.
Proof. vm_refl. Qed.
Lemma D_65a9c : D! W_65a9c (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_65aa0 : bv 32 := 0x00051663.
Lemma F_65aa0 : F! 0x65aa0 W_65aa0.
Proof. vm_refl. Qed.
Lemma D_65aa0 : D! W_65aa0 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_65aa4 : bv 32 := 0x00100513.
Lemma F_65aa4 : F! 0x65aa4 W_65aa4.
Proof. vm_refl. Qed.
Lemma D_65aa4 : D! W_65aa4 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_65aa8 : bv 32 := 0x00a48023.
Lemma F_65aa8 : F! 0x65aa8 W_65aa8.
Proof. vm_refl. Qed.
Lemma D_65aa8 : D! W_65aa8 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_65aac : bv 32 := 0x00200513.
Lemma F_65aac : F! 0x65aac W_65aac.
Proof. vm_refl. Qed.
Lemma D_65aac : D! W_65aac (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_65ab0 : bv 32 := 0x00045597.
Lemma F_65ab0 : F! 0x65ab0 W_65ab0.
Proof. vm_refl. Qed.
Lemma D_65ab0 : D! W_65ab0 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_65ab4 : bv 32 := 0x02a92423.
Lemma F_65ab4 : F! 0x65ab4 W_65ab4.
Proof. vm_refl. Qed.
Lemma D_65ab4 : D! W_65ab4 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_65ab8 : bv 32 := 0x06000893.
Lemma F_65ab8 : F! 0x65ab8 W_65ab8.
Proof. vm_refl. Qed.
Lemma D_65ab8 : D! W_65ab8 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_65abc : bv 32 := 0x0e858513.
Lemma F_65abc : F! 0x65abc W_65abc.
Proof. vm_refl. Qed.
Lemma D_65abc : D! W_65abc (OpImm ALU_ADD 10 11 232).
Proof. vm_refl. Qed.
Definition W_65ac0 : bv 32 := 0x03848593.
Lemma F_65ac0 : F! 0x65ac0 W_65ac0.
Proof. vm_refl. Qed.
Lemma D_65ac0 : D! W_65ac0 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_65ac4 : bv 32 := 0x00000073.
Lemma F_65ac4 : F! 0x65ac4 W_65ac4.
Proof. vm_refl. Qed.
Lemma E_65ac4 : is_ecall W_65ac4 = true.
Proof. reflexivity. Qed.
Definition W_65ac8 : bv 32 := 0x07890613.
Lemma F_65ac8 : F! 0x65ac8 W_65ac8.
Proof. vm_refl. Qed.
Lemma D_65ac8 : D! W_65ac8 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_65acc : bv 32 := 0x02a92023.
Lemma F_65acc : F! 0x65acc W_65acc.
Proof. vm_refl. Qed.
Lemma D_65acc : D! W_65acc (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_65ad0 : bv 32 := 0x08b93c23.
Lemma F_65ad0 : F! 0x65ad0 W_65ad0.
Proof. vm_refl. Qed.
Lemma D_65ad0 : D! W_65ad0 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_65ad4 : bv 32 := 0x06c93c23.
Lemma F_65ad4 : F! 0x65ad4 W_65ad4.
Proof. vm_refl. Qed.
Lemma D_65ad4 : D! W_65ad4 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_65ad8 : bv 32 := 0x00045517.
Lemma F_65ad8 : F! 0x65ad8 W_65ad8.
Proof. vm_refl. Qed.
Lemma D_65ad8 : D! W_65ad8 (Auipc 10 69).
Proof. vm_refl. Qed.
Definition W_65adc : bv 32 := 0x33053503.
Lemma F_65adc : F! 0x65adc W_65adc.
Proof. vm_refl. Qed.
Lemma D_65adc : D! W_65adc (Load SZ8 true 10 10 816).
Proof. vm_refl. Qed.
Definition W_65ae0 : bv 32 := 0x01293423.
Lemma F_65ae0 : F! 0x65ae0 W_65ae0.
Proof. vm_refl. Qed.
Lemma D_65ae0 : D! W_65ae0 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_65ae4 : bv 32 := 0x01293823.
Lemma F_65ae4 : F! 0x65ae4 W_65ae4.
Proof. vm_refl. Qed.
Lemma D_65ae4 : D! W_65ae4 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_65ae8 : bv 32 := 0x00a93c23.
Lemma F_65ae8 : F! 0x65ae8 W_65ae8.
Proof. vm_refl. Qed.
Lemma D_65ae8 : D! W_65ae8 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_65aec : bv 32 := 0x0080006f.
Lemma F_65aec : F! 0x65aec W_65aec.
Proof. vm_refl. Qed.
Lemma D_65aec : D! W_65aec (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_65af4 : bv 32 := 0x03813083.
Lemma F_65af4 : F! 0x65af4 W_65af4.
Proof. vm_refl. Qed.
Lemma D_65af4 : D! W_65af4 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_65af8 : bv 32 := 0x03013403.
Lemma F_65af8 : F! 0x65af8 W_65af8.
Proof. vm_refl. Qed.
Lemma D_65af8 : D! W_65af8 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_65afc : bv 32 := 0x02813483.
Lemma F_65afc : F! 0x65afc W_65afc.
Proof. vm_refl. Qed.
Lemma D_65afc : D! W_65afc (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_65b00 : bv 32 := 0x02013903.
Lemma F_65b00 : F! 0x65b00 W_65b00.
Proof. vm_refl. Qed.
Lemma D_65b00 : D! W_65b00 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_65b04 : bv 32 := 0x01813983.
Lemma F_65b04 : F! 0x65b04 W_65b04.
Proof. vm_refl. Qed.
Lemma D_65b04 : D! W_65b04 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_65b08 : bv 32 := 0x01013a03.
Lemma F_65b08 : F! 0x65b08 W_65b08.
Proof. vm_refl. Qed.
Lemma D_65b08 : D! W_65b08 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_65b0c : bv 32 := 0x00813a83.
Lemma F_65b0c : F! 0x65b0c W_65b0c.
Proof. vm_refl. Qed.
Lemma D_65b0c : D! W_65b0c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_65b10 : bv 32 := 0x04010113.
Lemma F_65b10 : F! 0x65b10 W_65b10.
Proof. vm_refl. Qed.
Lemma D_65b10 : D! W_65b10 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_65b14 : bv 32 := 0x00008067.
Lemma F_65b14 : F! 0x65b14 W_65b14.
Proof. vm_refl. Qed.
Lemma D_65b14 : D! W_65b14 (Jalr 0 1 0).
Proof. vm_refl. Qed.
