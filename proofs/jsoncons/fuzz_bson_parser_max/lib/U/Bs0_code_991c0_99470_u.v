(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
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
Definition W_991c0 : bv 32 := 0xfc010113.
Lemma F_991c0 : F! 0x9a7a8 W_991c0.
Proof. vm_refl. Qed.
Lemma D_991c0 : D! W_991c0 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_991c4 : bv 32 := 0x02113c23.
Lemma F_991c4 : F! 0x9a7ac W_991c4.
Proof. vm_refl. Qed.
Lemma D_991c4 : D! W_991c4 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_991c8 : bv 32 := 0x02813823.
Lemma F_991c8 : F! 0x9a7b0 W_991c8.
Proof. vm_refl. Qed.
Lemma D_991c8 : D! W_991c8 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_991cc : bv 32 := 0x02913423.
Lemma F_991cc : F! 0x9a7b4 W_991cc.
Proof. vm_refl. Qed.
Lemma D_991cc : D! W_991cc (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_991d0 : bv 32 := 0x03213023.
Lemma F_991d0 : F! 0x9a7b8 W_991d0.
Proof. vm_refl. Qed.
Lemma D_991d0 : D! W_991d0 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_991d4 : bv 32 := 0x01313c23.
Lemma F_991d4 : F! 0x9a7bc W_991d4.
Proof. vm_refl. Qed.
Lemma D_991d4 : D! W_991d4 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_991d8 : bv 32 := 0x01413823.
Lemma F_991d8 : F! 0x9a7c0 W_991d8.
Proof. vm_refl. Qed.
Lemma D_991d8 : D! W_991d8 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_991dc : bv 32 := 0x01513423.
Lemma F_991dc : F! 0x9a7c4 W_991dc.
Proof. vm_refl. Qed.
Lemma D_991dc : D! W_991dc (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_991e0 : bv 32 := 0x02853683.
Lemma F_991e0 : F! 0x9a7c8 W_991e0.
Proof. vm_refl. Qed.
Lemma D_991e0 : D! W_991e0 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_991e4 : bv 32 := 0x0004f597.
Lemma F_991e4 : F! 0x9a7cc W_991e4.
Proof. vm_refl. Qed.
Lemma D_991e4 : D! W_991e4 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_991e8 : bv 32 := 0x7fc58593.
Lemma F_991e8 : F! 0x9a7d0 W_991e8.
Proof. vm_refl. Qed.
Lemma D_991e8 : D! W_991e8 (OpImm ALU_ADD 11 11 2044).
Proof. vm_refl. Qed.
Definition W_991ec : bv 32 := 0x00050617.
Lemma F_991ec : F! 0x9a7d4 W_991ec.
Proof. vm_refl. Qed.
Lemma D_991ec : D! W_991ec (Auipc 12 80).
Proof. vm_refl. Qed.
Definition W_991f0 : bv 32 := 0xa7c60493.
Lemma F_991f0 : F! 0x9a7d8 W_991f0.
Proof. vm_refl. Qed.
Lemma D_991f0 : D! W_991f0 (OpImm ALU_ADD 9 12 2684).
Proof. vm_refl. Qed.
Definition W_991f4 : bv 32 := 0x0c068e63.
Lemma F_991f4 : F! 0x9a7dc W_991f4.
Proof. vm_refl. Qed.
Lemma D_991f4 : D! W_991f4 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_991f8 : bv 32 := 0x00000613.
Lemma F_991f8 : F! 0x9a7e0 W_991f8.
Proof. vm_refl. Qed.
Lemma D_991f8 : D! W_991f8 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_991fc : bv 32 := 0x00000893.
Lemma F_991fc : F! 0x9a7e4 W_991fc.
Proof. vm_refl. Qed.
Lemma D_991fc : D! W_991fc (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_99200 : bv 32 := 0x0001e717.
Lemma F_99200 : F! 0x9a7e8 W_99200.
Proof. vm_refl. Qed.
Lemma D_99200 : D! W_99200 (Auipc 14 30).
Proof. vm_refl. Qed.
Definition W_99204 : bv 32 := 0x01853783.
Lemma F_99204 : F! 0x9a7ec W_99204.
Proof. vm_refl. Qed.
Lemma D_99204 : D! W_99204 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_99208 : bv 32 := 0x02053503.
Lemma F_99208 : F! 0x9a7f0 W_99208.
Proof. vm_refl. Qed.
Lemma D_99208 : D! W_99208 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_9920c : bv 32 := 0x00600813.
Lemma F_9920c : F! 0x9a7f4 W_9920c.
Proof. vm_refl. Qed.
Lemma D_9920c : D! W_9920c (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_99210 : bv 32 := 0x0001d297.
Lemma F_99210 : F! 0x9a7f8 W_99210.
Proof. vm_refl. Qed.
Lemma D_99210 : D! W_99210 (Auipc 5 29).
Proof. vm_refl. Qed.
Definition W_99214 : bv 32 := 0xcf876f03.
Lemma F_99214 : F! 0x9a7fc W_99214.
Proof. vm_refl. Qed.
Lemma D_99214 : D! W_99214 (Load SZ4 false 30 14 3320).
Proof. vm_refl. Qed.
Definition W_99218 : bv 32 := 0x8602b283.
Lemma F_99218 : F! 0x9a800 W_99218.
Proof. vm_refl. Qed.
Lemma D_99218 : D! W_99218 (Load SZ8 true 5 5 2144).
Proof. vm_refl. Qed.
Definition W_9921c : bv 32 := 0x00200313.
Lemma F_9921c : F! 0x9a804 W_9921c.
Proof. vm_refl. Qed.
Lemma D_9921c : D! W_9921c (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_99220 : bv 32 := 0x00700393.
Lemma F_99220 : F! 0x9a808 W_99220.
Proof. vm_refl. Qed.
Lemma D_99220 : D! W_99220 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_99224 : bv 32 := 0x6474ee37.
Lemma F_99224 : F! 0x9a80c W_99224.
Proof. vm_refl. Qed.
Lemma D_99224 : D! W_99224 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_99228 : bv 32 := 0x551e0e1b.
Lemma F_99228 : F! 0x9a810 W_99228.
Proof. vm_refl. Qed.
Lemma D_99228 : D! W_99228 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_9922c : bv 32 := 0x00078e93.
Lemma F_9922c : F! 0x9a814 W_9922c.
Proof. vm_refl. Qed.
Lemma D_9922c : D! W_9922c (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_99230 : bv 32 := 0x0180006f.
Lemma F_99230 : F! 0x9a818 W_99230.
Proof. vm_refl. Qed.
Lemma D_99230 : D! W_99230 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_99234 : bv 32 := 0x010eb603.
Lemma F_99234 : F! 0x9a81c W_99234.
Proof. vm_refl. Qed.
Lemma D_99234 : D! W_99234 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_99238 : bv 32 := 0x40c78633.
Lemma F_99238 : F! 0x9a820 W_99238.
Proof. vm_refl. Qed.
Lemma D_99238 : D! W_99238 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_9923c : bv 32 := 0xfff68693.
Lemma F_9923c : F! 0x9a824 W_9923c.
Proof. vm_refl. Qed.
Lemma D_9923c : D! W_9923c (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_99240 : bv 32 := 0x00ae8eb3.
Lemma F_99240 : F! 0x9a828 W_99240.
Proof. vm_refl. Qed.
Lemma D_99240 : D! W_99240 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_99244 : bv 32 := 0x04068a63.
Lemma F_99244 : F! 0x9a82c W_99244.
Proof. vm_refl. Qed.
Lemma D_99244 : D! W_99244 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_99248 : bv 32 := 0x000ea403.
Lemma F_99248 : F! 0x9a830 W_99248.
Proof. vm_refl. Qed.
Lemma D_99248 : D! W_99248 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_9924c : bv 32 := 0xff0404e3.
Lemma F_9924c : F! 0x9a834 W_9924c.
Proof. vm_refl. Qed.
Lemma D_9924c : D! W_9924c (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_99250 : bv 32 := 0x00028a63.
Lemma F_99250 : F! 0x9a838 W_99250.
Proof. vm_refl. Qed.
Lemma D_99250 : D! W_99250 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_99264 : bv 32 := 0x000e8f93.
Lemma F_99264 : F! 0x9a84c W_99264.
Proof. vm_refl. Qed.
Lemma D_99264 : D! W_99264 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_99268 : bv 32 := 0x00740463.
Lemma F_99268 : F! 0x9a850 W_99268.
Proof. vm_refl. Qed.
Lemma D_99268 : D! W_99268 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_9926c : bv 32 := 0x00088f93.
Lemma F_9926c : F! 0x9a854 W_9926c.
Proof. vm_refl. Qed.
Lemma D_9926c : D! W_9926c (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_99270 : bv 32 := 0x03c41063.
Lemma F_99270 : F! 0x9a858 W_99270.
Proof. vm_refl. Qed.
Lemma D_99270 : D! W_99270 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_99274 : bv 32 := 0x028eb883.
Lemma F_99274 : F! 0x9a85c W_99274.
Proof. vm_refl. Qed.
Lemma D_99274 : D! W_99274 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_99278 : bv 32 := 0x011f7c63.
Lemma F_99278 : F! 0x9a860 W_99278.
Proof. vm_refl. Qed.
Lemma D_99278 : D! W_99278 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_99290 : bv 32 := 0x000f8893.
Lemma F_99290 : F! 0x9a878 W_99290.
Proof. vm_refl. Qed.
Lemma D_99290 : D! W_99290 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_99294 : bv 32 := 0xfa9ff06f.
Lemma F_99294 : F! 0x9a87c W_99294.
Proof. vm_refl. Qed.
Lemma D_99294 : D! W_99294 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_99298 : bv 32 := 0x02088c63.
Lemma F_99298 : F! 0x9a880 W_99298.
Proof. vm_refl. Qed.
Lemma D_99298 : D! W_99298 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_992d0 : bv 32 := 0x0105b603.
Lemma F_992d0 : F! 0x9a8b8 W_992d0.
Proof. vm_refl. Qed.
Lemma D_992d0 : D! W_992d0 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_992d4 : bv 32 := 0x0205b683.
Lemma F_992d4 : F! 0x9a8bc W_992d4.
Proof. vm_refl. Qed.
Lemma D_992d4 : D! W_992d4 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_992d8 : bv 32 := 0x0285b503.
Lemma F_992d8 : F! 0x9a8c0 W_992d8.
Proof. vm_refl. Qed.
Lemma D_992d8 : D! W_992d8 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_992dc : bv 32 := 0x00c68733.
Lemma F_992dc : F! 0x9a8c4 W_992dc.
Proof. vm_refl. Qed.
Lemma D_992dc : D! W_992dc (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_992e0 : bv 32 := 0xfff50793.
Lemma F_992e0 : F! 0x9a8c8 W_992e0.
Proof. vm_refl. Qed.
Lemma D_992e0 : D! W_992e0 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_992e4 : bv 32 := 0x40e00733.
Lemma F_992e4 : F! 0x9a8cc W_992e4.
Proof. vm_refl. Qed.
Lemma D_992e4 : D! W_992e4 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_992e8 : bv 32 := 0x00c7f633.
Lemma F_992e8 : F! 0x9a8d0 W_992e8.
Proof. vm_refl. Qed.
Lemma D_992e8 : D! W_992e8 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_992ec : bv 32 := 0x00e7f733.
Lemma F_992ec : F! 0x9a8d4 W_992ec.
Proof. vm_refl. Qed.
Lemma D_992ec : D! W_992ec (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_992f0 : bv 32 := 0x00700793.
Lemma F_992f0 : F! 0x9a8d8 W_992f0.
Proof. vm_refl. Qed.
Lemma D_992f0 : D! W_992f0 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_992f4 : bv 32 := 0x00d706b3.
Lemma F_992f4 : F! 0x9a8dc W_992f4.
Proof. vm_refl. Qed.
Lemma D_992f4 : D! W_992f4 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_992f8 : bv 32 := 0x02d5b023.
Lemma F_992f8 : F! 0x9a8e0 W_992f8.
Proof. vm_refl. Qed.
Lemma D_992f8 : D! W_992f8 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_992fc : bv 32 := 0x02c5b823.
Lemma F_992fc : F! 0x9a8e4 W_992fc.
Proof. vm_refl. Qed.
Lemma D_992fc : D! W_992fc (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_99300 : bv 32 := 0x00a7e663.
Lemma F_99300 : F! 0x9a8e8 W_99300.
Proof. vm_refl. Qed.
Lemma D_99300 : D! W_99300 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_99304 : bv 32 := 0x00800513.
Lemma F_99304 : F! 0x9a8ec W_99304.
Proof. vm_refl. Qed.
Lemma D_99304 : D! W_99304 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_99308 : bv 32 := 0x02a5b423.
Lemma F_99308 : F! 0x9a8f0 W_99308.
Proof. vm_refl. Qed.
Lemma D_99308 : D! W_99308 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_9930c : bv 32 := 0x00d60633.
Lemma F_9930c : F! 0x9a8f4 W_9930c.
Proof. vm_refl. Qed.
Lemma D_9930c : D! W_9930c (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_99310 : bv 32 := 0x000205b7.
Lemma F_99310 : F! 0x9a8f8 W_99310.
Proof. vm_refl. Qed.
Lemma D_99310 : D! W_99310 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_99314 : bv 32 := 0x00a60633.
Lemma F_99314 : F! 0x9a8fc W_99314.
Proof. vm_refl. Qed.
Lemma D_99314 : D! W_99314 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_99318 : bv 32 := 0x0d15869b.
Lemma F_99318 : F! 0x9a900 W_99318.
Proof. vm_refl. Qed.
Lemma D_99318 : D! W_99318 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_9931c : bv 32 := 0x0df60593.
Lemma F_9931c : F! 0x9a904 W_9931c.
Proof. vm_refl. Qed.
Lemma D_9931c : D! W_9931c (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_99320 : bv 32 := 0xff85f593.
Lemma F_99320 : F! 0x9a908 W_99320.
Proof. vm_refl. Qed.
Lemma D_99320 : D! W_99320 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_99324 : bv 32 := 0x00b4bc23.
Lemma F_99324 : F! 0x9a90c W_99324.
Proof. vm_refl. Qed.
Lemma D_99324 : D! W_99324 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_99328 : bv 32 := 0x02a4b023.
Lemma F_99328 : F! 0x9a910 W_99328.
Proof. vm_refl. Qed.
Lemma D_99328 : D! W_99328 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_9932c : bv 32 := 0x02d5ea63.
Lemma F_9932c : F! 0x9a914 W_9932c.
Proof. vm_refl. Qed.
Lemma D_9932c : D! W_9932c (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_99360 : bv 32 := 0x0002f697.
Lemma F_99360 : F! 0x9a948 W_99360.
Proof. vm_refl. Qed.
Lemma D_99360 : D! W_99360 (Auipc 13 47).
Proof. vm_refl. Qed.
Definition W_99364 : bv 32 := 0x0104b983.
Lemma F_99364 : F! 0x9a94c W_99364.
Proof. vm_refl. Qed.
Lemma D_99364 : D! W_99364 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_99368 : bv 32 := 0x0284b603.
Lemma F_99368 : F! 0x9a950 W_99368.
Proof. vm_refl. Qed.
Lemma D_99368 : D! W_99368 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_9936c : bv 32 := 0xfff50713.
Lemma F_9936c : F! 0x9a954 W_9936c.
Proof. vm_refl. Qed.
Lemma D_9936c : D! W_9936c (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_99370 : bv 32 := 0xf3800793.
Lemma F_99370 : F! 0x9a958 W_99370.
Proof. vm_refl. Qed.
Lemma D_99370 : D! W_99370 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_99374 : bv 32 := 0x5b068513.
Lemma F_99374 : F! 0x9a95c W_99374.
Proof. vm_refl. Qed.
Lemma D_99374 : D! W_99374 (OpImm ALU_ADD 10 13 1456).
Proof. vm_refl. Qed.
Definition W_99378 : bv 32 := 0x40a787b3.
Lemma F_99378 : F! 0x9a960 W_99378.
Proof. vm_refl. Qed.
Lemma D_99378 : D! W_99378 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_9937c : bv 32 := 0x00f77733.
Lemma F_9937c : F! 0x9a964 W_9937c.
Proof. vm_refl. Qed.
Lemma D_9937c : D! W_9937c (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_99380 : bv 32 := 0xfff64693.
Lemma F_99380 : F! 0x9a968 W_99380.
Proof. vm_refl. Qed.
Lemma D_99380 : D! W_99380 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_99384 : bv 32 := 0x00e50933.
Lemma F_99384 : F! 0x9a96c W_99384.
Proof. vm_refl. Qed.
Lemma D_99384 : D! W_99384 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_99388 : bv 32 := 0x00369693.
Lemma F_99388 : F! 0x9a970 W_99388.
Proof. vm_refl. Qed.
Lemma D_99388 : D! W_99388 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_9938c : bv 32 := 0x00d506b3.
Lemma F_9938c : F! 0x9a974 W_9938c.
Proof. vm_refl. Qed.
Lemma D_9938c : D! W_9938c (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_99390 : bv 32 := 0x00b68a33.
Lemma F_99390 : F! 0x9a978 W_99390.
Proof. vm_refl. Qed.
Lemma D_99390 : D! W_99390 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_99394 : bv 32 := 0x0c890413.
Lemma F_99394 : F! 0x9a97c W_99394.
Proof. vm_refl. Qed.
Lemma D_99394 : D! W_99394 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_99398 : bv 32 := 0x04098463.
Lemma F_99398 : F! 0x9a980 W_99398.
Proof. vm_refl. Qed.
Lemma D_99398 : D! W_99398 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_993e0 : bv 32 := 0x00ca3023.
Lemma F_993e0 : F! 0x9a9c8 W_993e0.
Proof. vm_refl. Qed.
Lemma D_993e0 : D! W_993e0 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_993e4 : bv 32 := 0x0d493023.
Lemma F_993e4 : F! 0x9a9cc W_993e4.
Proof. vm_refl. Qed.
Lemma D_993e4 : D! W_993e4 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_993e8 : bv 32 := 0x01293023.
Lemma F_993e8 : F! 0x9a9d0 W_993e8.
Proof. vm_refl. Qed.
Lemma D_993e8 : D! W_993e8 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_993ec : bv 32 := 0x00040513.
Lemma F_993ec : F! 0x9a9d4 W_993ec.
Proof. vm_refl. Qed.
Lemma D_993ec : D! W_993ec (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_993f0 : bv 32 := 0x168130ef.
Lemma F_993f0 : F! 0x9a9d8 W_993f0.
Proof. vm_refl. Qed.
Lemma D_993f0 : D! W_993f0 (Jal 1 78184).
Proof. vm_refl. Qed.
Definition W_993f4 : bv 32 := 0x04054a63.
Lemma F_993f4 : F! 0x9a9dc W_993f4.
Proof. vm_refl. Qed.
Lemma D_993f4 : D! W_993f4 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_993f8 : bv 32 := 0x00051663.
Lemma F_993f8 : F! 0x9a9e0 W_993f8.
Proof. vm_refl. Qed.
Lemma D_993f8 : D! W_993f8 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_993fc : bv 32 := 0x00100513.
Lemma F_993fc : F! 0x9a9e4 W_993fc.
Proof. vm_refl. Qed.
Lemma D_993fc : D! W_993fc (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_99400 : bv 32 := 0x00a48023.
Lemma F_99400 : F! 0x9a9e8 W_99400.
Proof. vm_refl. Qed.
Lemma D_99400 : D! W_99400 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_99404 : bv 32 := 0x00200513.
Lemma F_99404 : F! 0x9a9ec W_99404.
Proof. vm_refl. Qed.
Lemma D_99404 : D! W_99404 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_99408 : bv 32 := 0x0004f597.
Lemma F_99408 : F! 0x9a9f0 W_99408.
Proof. vm_refl. Qed.
Lemma D_99408 : D! W_99408 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_9940c : bv 32 := 0x02a92423.
Lemma F_9940c : F! 0x9a9f4 W_9940c.
Proof. vm_refl. Qed.
Lemma D_9940c : D! W_9940c (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_99410 : bv 32 := 0x06000893.
Lemma F_99410 : F! 0x9a9f8 W_99410.
Proof. vm_refl. Qed.
Lemma D_99410 : D! W_99410 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_99414 : bv 32 := 0x5d858513.
Lemma F_99414 : F! 0x9a9fc W_99414.
Proof. vm_refl. Qed.
Lemma D_99414 : D! W_99414 (OpImm ALU_ADD 10 11 1496).
Proof. vm_refl. Qed.
Definition W_99418 : bv 32 := 0x03848593.
Lemma F_99418 : F! 0x9aa00 W_99418.
Proof. vm_refl. Qed.
Lemma D_99418 : D! W_99418 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_9941c : bv 32 := 0x00000073.
Lemma F_9941c : F! 0x9aa04 W_9941c.
Proof. vm_refl. Qed.
Lemma E_9941c : is_ecall W_9941c = true.
Proof. reflexivity. Qed.
Definition W_99420 : bv 32 := 0x07890613.
Lemma F_99420 : F! 0x9aa08 W_99420.
Proof. vm_refl. Qed.
Lemma D_99420 : D! W_99420 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_99424 : bv 32 := 0x02a92023.
Lemma F_99424 : F! 0x9aa0c W_99424.
Proof. vm_refl. Qed.
Lemma D_99424 : D! W_99424 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_99428 : bv 32 := 0x08b93c23.
Lemma F_99428 : F! 0x9aa10 W_99428.
Proof. vm_refl. Qed.
Lemma D_99428 : D! W_99428 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_9942c : bv 32 := 0x06c93c23.
Lemma F_9942c : F! 0x9aa14 W_9942c.
Proof. vm_refl. Qed.
Lemma D_9942c : D! W_9942c (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_99430 : bv 32 := 0x00050517.
Lemma F_99430 : F! 0x9aa18 W_99430.
Proof. vm_refl. Qed.
Lemma D_99430 : D! W_99430 (Auipc 10 80).
Proof. vm_refl. Qed.
Definition W_99434 : bv 32 := 0x82053503.
Lemma F_99434 : F! 0x9aa1c W_99434.
Proof. vm_refl. Qed.
Lemma D_99434 : D! W_99434 (Load SZ8 true 10 10 2080).
Proof. vm_refl. Qed.
Definition W_99438 : bv 32 := 0x01293423.
Lemma F_99438 : F! 0x9aa20 W_99438.
Proof. vm_refl. Qed.
Lemma D_99438 : D! W_99438 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_9943c : bv 32 := 0x01293823.
Lemma F_9943c : F! 0x9aa24 W_9943c.
Proof. vm_refl. Qed.
Lemma D_9943c : D! W_9943c (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_99440 : bv 32 := 0x00a93c23.
Lemma F_99440 : F! 0x9aa28 W_99440.
Proof. vm_refl. Qed.
Lemma D_99440 : D! W_99440 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_99444 : bv 32 := 0x0080006f.
Lemma F_99444 : F! 0x9aa2c W_99444.
Proof. vm_refl. Qed.
Lemma D_99444 : D! W_99444 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_9944c : bv 32 := 0x03813083.
Lemma F_9944c : F! 0x9aa34 W_9944c.
Proof. vm_refl. Qed.
Lemma D_9944c : D! W_9944c (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_99450 : bv 32 := 0x03013403.
Lemma F_99450 : F! 0x9aa38 W_99450.
Proof. vm_refl. Qed.
Lemma D_99450 : D! W_99450 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_99454 : bv 32 := 0x02813483.
Lemma F_99454 : F! 0x9aa3c W_99454.
Proof. vm_refl. Qed.
Lemma D_99454 : D! W_99454 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_99458 : bv 32 := 0x02013903.
Lemma F_99458 : F! 0x9aa40 W_99458.
Proof. vm_refl. Qed.
Lemma D_99458 : D! W_99458 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_9945c : bv 32 := 0x01813983.
Lemma F_9945c : F! 0x9aa44 W_9945c.
Proof. vm_refl. Qed.
Lemma D_9945c : D! W_9945c (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_99460 : bv 32 := 0x01013a03.
Lemma F_99460 : F! 0x9aa48 W_99460.
Proof. vm_refl. Qed.
Lemma D_99460 : D! W_99460 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_99464 : bv 32 := 0x00813a83.
Lemma F_99464 : F! 0x9aa4c W_99464.
Proof. vm_refl. Qed.
Lemma D_99464 : D! W_99464 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_99468 : bv 32 := 0x04010113.
Lemma F_99468 : F! 0x9aa50 W_99468.
Proof. vm_refl. Qed.
Lemma D_99468 : D! W_99468 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_9946c : bv 32 := 0x00008067.
Lemma F_9946c : F! 0x9aa54 W_9946c.
Proof. vm_refl. Qed.
Lemma D_9946c : D! W_9946c (Jalr 0 1 0).
Proof. vm_refl. Qed.
