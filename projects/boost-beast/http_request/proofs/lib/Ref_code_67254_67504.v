(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
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
Definition W_67254 : bv 32 := 0xfc010113.
Lemma F_67254 : F! 0x67254 W_67254.
Proof. vm_refl. Qed.
Lemma D_67254 : D! W_67254 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_67258 : bv 32 := 0x02113c23.
Lemma F_67258 : F! 0x67258 W_67258.
Proof. vm_refl. Qed.
Lemma D_67258 : D! W_67258 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_6725c : bv 32 := 0x02813823.
Lemma F_6725c : F! 0x6725c W_6725c.
Proof. vm_refl. Qed.
Lemma D_6725c : D! W_6725c (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_67260 : bv 32 := 0x02913423.
Lemma F_67260 : F! 0x67260 W_67260.
Proof. vm_refl. Qed.
Lemma D_67260 : D! W_67260 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_67264 : bv 32 := 0x03213023.
Lemma F_67264 : F! 0x67264 W_67264.
Proof. vm_refl. Qed.
Lemma D_67264 : D! W_67264 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_67268 : bv 32 := 0x01313c23.
Lemma F_67268 : F! 0x67268 W_67268.
Proof. vm_refl. Qed.
Lemma D_67268 : D! W_67268 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_6726c : bv 32 := 0x01413823.
Lemma F_6726c : F! 0x6726c W_6726c.
Proof. vm_refl. Qed.
Lemma D_6726c : D! W_6726c (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_67270 : bv 32 := 0x01513423.
Lemma F_67270 : F! 0x67270 W_67270.
Proof. vm_refl. Qed.
Lemma D_67270 : D! W_67270 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_67274 : bv 32 := 0x02853683.
Lemma F_67274 : F! 0x67274 W_67274.
Proof. vm_refl. Qed.
Lemma D_67274 : D! W_67274 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_67278 : bv 32 := 0x0004b597.
Lemma F_67278 : F! 0x67278 W_67278.
Proof. vm_refl. Qed.
Lemma D_67278 : D! W_67278 (Auipc 11 75).
Proof. vm_refl. Qed.
Definition W_6727c : bv 32 := 0x3e058593.
Lemma F_6727c : F! 0x6727c W_6727c.
Proof. vm_refl. Qed.
Lemma D_6727c : D! W_6727c (OpImm ALU_ADD 11 11 992).
Proof. vm_refl. Qed.
Definition W_67280 : bv 32 := 0x0004b617.
Lemma F_67280 : F! 0x67280 W_67280.
Proof. vm_refl. Qed.
Lemma D_67280 : D! W_67280 (Auipc 12 75).
Proof. vm_refl. Qed.
Definition W_67284 : bv 32 := 0x66060493.
Lemma F_67284 : F! 0x67284 W_67284.
Proof. vm_refl. Qed.
Lemma D_67284 : D! W_67284 (OpImm ALU_ADD 9 12 1632).
Proof. vm_refl. Qed.
Definition W_67288 : bv 32 := 0x0c068e63.
Lemma F_67288 : F! 0x67288 W_67288.
Proof. vm_refl. Qed.
Lemma D_67288 : D! W_67288 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_6728c : bv 32 := 0x00000613.
Lemma F_6728c : F! 0x6728c W_6728c.
Proof. vm_refl. Qed.
Lemma D_6728c : D! W_6728c (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_67290 : bv 32 := 0x00000893.
Lemma F_67290 : F! 0x67290 W_67290.
Proof. vm_refl. Qed.
Lemma D_67290 : D! W_67290 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_67294 : bv 32 := 0x0001a717.
Lemma F_67294 : F! 0x67294 W_67294.
Proof. vm_refl. Qed.
Lemma D_67294 : D! W_67294 (Auipc 14 26).
Proof. vm_refl. Qed.
Definition W_67298 : bv 32 := 0x01853783.
Lemma F_67298 : F! 0x67298 W_67298.
Proof. vm_refl. Qed.
Lemma D_67298 : D! W_67298 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_6729c : bv 32 := 0x02053503.
Lemma F_6729c : F! 0x6729c W_6729c.
Proof. vm_refl. Qed.
Lemma D_6729c : D! W_6729c (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_672a0 : bv 32 := 0x00600813.
Lemma F_672a0 : F! 0x672a0 W_672a0.
Proof. vm_refl. Qed.
Lemma D_672a0 : D! W_672a0 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_672a4 : bv 32 := 0x00018297.
Lemma F_672a4 : F! 0x672a4 W_672a4.
Proof. vm_refl. Qed.
Lemma D_672a4 : D! W_672a4 (Auipc 5 24).
Proof. vm_refl. Qed.
Definition W_672a8 : bv 32 := 0x96c76f03.
Lemma F_672a8 : F! 0x672a8 W_672a8.
Proof. vm_refl. Qed.
Lemma D_672a8 : D! W_672a8 (Load SZ4 false 30 14 2412).
Proof. vm_refl. Qed.
Definition W_672ac : bv 32 := 0x4342b283.
Lemma F_672ac : F! 0x672ac W_672ac.
Proof. vm_refl. Qed.
Lemma D_672ac : D! W_672ac (Load SZ8 true 5 5 1076).
Proof. vm_refl. Qed.
Definition W_672b0 : bv 32 := 0x00200313.
Lemma F_672b0 : F! 0x672b0 W_672b0.
Proof. vm_refl. Qed.
Lemma D_672b0 : D! W_672b0 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_672b4 : bv 32 := 0x00700393.
Lemma F_672b4 : F! 0x672b4 W_672b4.
Proof. vm_refl. Qed.
Lemma D_672b4 : D! W_672b4 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_672b8 : bv 32 := 0x6474ee37.
Lemma F_672b8 : F! 0x672b8 W_672b8.
Proof. vm_refl. Qed.
Lemma D_672b8 : D! W_672b8 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_672bc : bv 32 := 0x551e0e1b.
Lemma F_672bc : F! 0x672bc W_672bc.
Proof. vm_refl. Qed.
Lemma D_672bc : D! W_672bc (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_672c0 : bv 32 := 0x00078e93.
Lemma F_672c0 : F! 0x672c0 W_672c0.
Proof. vm_refl. Qed.
Lemma D_672c0 : D! W_672c0 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_672c4 : bv 32 := 0x0180006f.
Lemma F_672c4 : F! 0x672c4 W_672c4.
Proof. vm_refl. Qed.
Lemma D_672c4 : D! W_672c4 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_672c8 : bv 32 := 0x010eb603.
Lemma F_672c8 : F! 0x672c8 W_672c8.
Proof. vm_refl. Qed.
Lemma D_672c8 : D! W_672c8 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_672cc : bv 32 := 0x40c78633.
Lemma F_672cc : F! 0x672cc W_672cc.
Proof. vm_refl. Qed.
Lemma D_672cc : D! W_672cc (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_672d0 : bv 32 := 0xfff68693.
Lemma F_672d0 : F! 0x672d0 W_672d0.
Proof. vm_refl. Qed.
Lemma D_672d0 : D! W_672d0 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_672d4 : bv 32 := 0x00ae8eb3.
Lemma F_672d4 : F! 0x672d4 W_672d4.
Proof. vm_refl. Qed.
Lemma D_672d4 : D! W_672d4 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_672d8 : bv 32 := 0x04068a63.
Lemma F_672d8 : F! 0x672d8 W_672d8.
Proof. vm_refl. Qed.
Lemma D_672d8 : D! W_672d8 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_672dc : bv 32 := 0x000ea403.
Lemma F_672dc : F! 0x672dc W_672dc.
Proof. vm_refl. Qed.
Lemma D_672dc : D! W_672dc (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_672e0 : bv 32 := 0xff0404e3.
Lemma F_672e0 : F! 0x672e0 W_672e0.
Proof. vm_refl. Qed.
Lemma D_672e0 : D! W_672e0 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_672e4 : bv 32 := 0x00028a63.
Lemma F_672e4 : F! 0x672e4 W_672e4.
Proof. vm_refl. Qed.
Lemma D_672e4 : D! W_672e4 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_672f8 : bv 32 := 0x000e8f93.
Lemma F_672f8 : F! 0x672f8 W_672f8.
Proof. vm_refl. Qed.
Lemma D_672f8 : D! W_672f8 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_672fc : bv 32 := 0x00740463.
Lemma F_672fc : F! 0x672fc W_672fc.
Proof. vm_refl. Qed.
Lemma D_672fc : D! W_672fc (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_67300 : bv 32 := 0x00088f93.
Lemma F_67300 : F! 0x67300 W_67300.
Proof. vm_refl. Qed.
Lemma D_67300 : D! W_67300 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_67304 : bv 32 := 0x03c41063.
Lemma F_67304 : F! 0x67304 W_67304.
Proof. vm_refl. Qed.
Lemma D_67304 : D! W_67304 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_67308 : bv 32 := 0x028eb883.
Lemma F_67308 : F! 0x67308 W_67308.
Proof. vm_refl. Qed.
Lemma D_67308 : D! W_67308 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_6730c : bv 32 := 0x011f7c63.
Lemma F_6730c : F! 0x6730c W_6730c.
Proof. vm_refl. Qed.
Lemma D_6730c : D! W_6730c (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_67324 : bv 32 := 0x000f8893.
Lemma F_67324 : F! 0x67324 W_67324.
Proof. vm_refl. Qed.
Lemma D_67324 : D! W_67324 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_67328 : bv 32 := 0xfa9ff06f.
Lemma F_67328 : F! 0x67328 W_67328.
Proof. vm_refl. Qed.
Lemma D_67328 : D! W_67328 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_6732c : bv 32 := 0x02088c63.
Lemma F_6732c : F! 0x6732c W_6732c.
Proof. vm_refl. Qed.
Lemma D_6732c : D! W_6732c (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_67330 : bv 32 := 0x00858713.
Lemma F_67330 : F! 0x67330 W_67330.
Proof. vm_refl. Qed.
Lemma D_67330 : D! W_67330 (OpImm ALU_ADD 14 11 8).
Proof. vm_refl. Qed.
Definition W_67334 : bv 32 := 0x0108b783.
Lemma F_67334 : F! 0x67334 W_67334.
Proof. vm_refl. Qed.
Lemma D_67334 : D! W_67334 (Load SZ8 true 15 17 16).
Proof. vm_refl. Qed.
Definition W_67338 : bv 32 := 0x0208b803.
Lemma F_67338 : F! 0x67338 W_67338.
Proof. vm_refl. Qed.
Lemma D_67338 : D! W_67338 (Load SZ8 true 16 17 32).
Proof. vm_refl. Qed.
Definition W_6733c : bv 32 := 0x0288b683.
Lemma F_6733c : F! 0x6733c W_6733c.
Proof. vm_refl. Qed.
Lemma D_6733c : D! W_6733c (Load SZ8 true 13 17 40).
Proof. vm_refl. Qed.
Definition W_67340 : bv 32 := 0x0308b503.
Lemma F_67340 : F! 0x67340 W_67340.
Proof. vm_refl. Qed.
Lemma D_67340 : D! W_67340 (Load SZ8 true 10 17 48).
Proof. vm_refl. Qed.
Definition W_67344 : bv 32 := 0x00c78633.
Lemma F_67344 : F! 0x67344 W_67344.
Proof. vm_refl. Qed.
Lemma D_67344 : D! W_67344 (Op ALU_ADD 12 15 12).
Proof. vm_refl. Qed.
Definition W_67348 : bv 32 := 0x00100793.
Lemma F_67348 : F! 0x67348 W_67348.
Proof. vm_refl. Qed.
Lemma D_67348 : D! W_67348 (OpImm ALU_ADD 15 0 1).
Proof. vm_refl. Qed.
Definition W_6734c : bv 32 := 0x00c5b823.
Lemma F_6734c : F! 0x6734c W_6734c.
Proof. vm_refl. Qed.
Lemma D_6734c : D! W_6734c (Store SZ8 11 12 16).
Proof. vm_refl. Qed.
Definition W_67350 : bv 32 := 0x0105bc23.
Lemma F_67350 : F! 0x67350 W_67350.
Proof. vm_refl. Qed.
Lemma D_67350 : D! W_67350 (Store SZ8 11 16 24).
Proof. vm_refl. Qed.
Definition W_67354 : bv 32 := 0x02a5b423.
Lemma F_67354 : F! 0x67354 W_67354.
Proof. vm_refl. Qed.
Lemma D_67354 : D! W_67354 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_67358 : bv 32 := 0x00e4b823.
Lemma F_67358 : F! 0x67358 W_67358.
Proof. vm_refl. Qed.
Lemma D_67358 : D! W_67358 (Store SZ8 9 14 16).
Proof. vm_refl. Qed.
Definition W_6735c : bv 32 := 0x02f4b423.
Lemma F_6735c : F! 0x6735c W_6735c.
Proof. vm_refl. Qed.
Lemma D_6735c : D! W_6735c (Store SZ8 9 15 40).
Proof. vm_refl. Qed.
Definition W_67360 : bv 32 := 0x0100006f.
Lemma F_67360 : F! 0x67360 W_67360.
Proof. vm_refl. Qed.
Lemma D_67360 : D! W_67360 (Jal 0 16).
Proof. vm_refl. Qed.
Definition W_67370 : bv 32 := 0x00c68733.
Lemma F_67370 : F! 0x67370 W_67370.
Proof. vm_refl. Qed.
Lemma D_67370 : D! W_67370 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_67374 : bv 32 := 0xfff50793.
Lemma F_67374 : F! 0x67374 W_67374.
Proof. vm_refl. Qed.
Lemma D_67374 : D! W_67374 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_67378 : bv 32 := 0x40e00733.
Lemma F_67378 : F! 0x67378 W_67378.
Proof. vm_refl. Qed.
Lemma D_67378 : D! W_67378 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_6737c : bv 32 := 0x00c7f633.
Lemma F_6737c : F! 0x6737c W_6737c.
Proof. vm_refl. Qed.
Lemma D_6737c : D! W_6737c (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_67380 : bv 32 := 0x00e7f733.
Lemma F_67380 : F! 0x67380 W_67380.
Proof. vm_refl. Qed.
Lemma D_67380 : D! W_67380 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_67384 : bv 32 := 0x00700793.
Lemma F_67384 : F! 0x67384 W_67384.
Proof. vm_refl. Qed.
Lemma D_67384 : D! W_67384 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_67388 : bv 32 := 0x00d706b3.
Lemma F_67388 : F! 0x67388 W_67388.
Proof. vm_refl. Qed.
Lemma D_67388 : D! W_67388 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_6738c : bv 32 := 0x02d5b023.
Lemma F_6738c : F! 0x6738c W_6738c.
Proof. vm_refl. Qed.
Lemma D_6738c : D! W_6738c (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_67390 : bv 32 := 0x02c5b823.
Lemma F_67390 : F! 0x67390 W_67390.
Proof. vm_refl. Qed.
Lemma D_67390 : D! W_67390 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_67394 : bv 32 := 0x00a7e663.
Lemma F_67394 : F! 0x67394 W_67394.
Proof. vm_refl. Qed.
Lemma D_67394 : D! W_67394 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_673a0 : bv 32 := 0x00d60633.
Lemma F_673a0 : F! 0x673a0 W_673a0.
Proof. vm_refl. Qed.
Lemma D_673a0 : D! W_673a0 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_673a4 : bv 32 := 0x000205b7.
Lemma F_673a4 : F! 0x673a4 W_673a4.
Proof. vm_refl. Qed.
Lemma D_673a4 : D! W_673a4 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_673a8 : bv 32 := 0x00a60633.
Lemma F_673a8 : F! 0x673a8 W_673a8.
Proof. vm_refl. Qed.
Lemma D_673a8 : D! W_673a8 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_673ac : bv 32 := 0x0d15869b.
Lemma F_673ac : F! 0x673ac W_673ac.
Proof. vm_refl. Qed.
Lemma D_673ac : D! W_673ac (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_673b0 : bv 32 := 0x0df60593.
Lemma F_673b0 : F! 0x673b0 W_673b0.
Proof. vm_refl. Qed.
Lemma D_673b0 : D! W_673b0 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_673b4 : bv 32 := 0xff85f593.
Lemma F_673b4 : F! 0x673b4 W_673b4.
Proof. vm_refl. Qed.
Lemma D_673b4 : D! W_673b4 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_673b8 : bv 32 := 0x00b4bc23.
Lemma F_673b8 : F! 0x673b8 W_673b8.
Proof. vm_refl. Qed.
Lemma D_673b8 : D! W_673b8 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_673bc : bv 32 := 0x02a4b023.
Lemma F_673bc : F! 0x673bc W_673bc.
Proof. vm_refl. Qed.
Lemma D_673bc : D! W_673bc (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_673c0 : bv 32 := 0x02d5ea63.
Lemma F_673c0 : F! 0x673c0 W_673c0.
Proof. vm_refl. Qed.
Lemma D_673c0 : D! W_673c0 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_673f4 : bv 32 := 0x0002b697.
Lemma F_673f4 : F! 0x673f4 W_673f4.
Proof. vm_refl. Qed.
Lemma D_673f4 : D! W_673f4 (Auipc 13 43).
Proof. vm_refl. Qed.
Definition W_673f8 : bv 32 := 0x0104b983.
Lemma F_673f8 : F! 0x673f8 W_673f8.
Proof. vm_refl. Qed.
Lemma D_673f8 : D! W_673f8 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_673fc : bv 32 := 0x0284b603.
Lemma F_673fc : F! 0x673fc W_673fc.
Proof. vm_refl. Qed.
Lemma D_673fc : D! W_673fc (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_67400 : bv 32 := 0xfff50713.
Lemma F_67400 : F! 0x67400 W_67400.
Proof. vm_refl. Qed.
Lemma D_67400 : D! W_67400 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_67404 : bv 32 := 0xf3800793.
Lemma F_67404 : F! 0x67404 W_67404.
Proof. vm_refl. Qed.
Lemma D_67404 : D! W_67404 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_67408 : bv 32 := 0x19468513.
Lemma F_67408 : F! 0x67408 W_67408.
Proof. vm_refl. Qed.
Lemma D_67408 : D! W_67408 (OpImm ALU_ADD 10 13 404).
Proof. vm_refl. Qed.
Definition W_6740c : bv 32 := 0x40a787b3.
Lemma F_6740c : F! 0x6740c W_6740c.
Proof. vm_refl. Qed.
Lemma D_6740c : D! W_6740c (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_67410 : bv 32 := 0x00f77733.
Lemma F_67410 : F! 0x67410 W_67410.
Proof. vm_refl. Qed.
Lemma D_67410 : D! W_67410 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_67414 : bv 32 := 0xfff64693.
Lemma F_67414 : F! 0x67414 W_67414.
Proof. vm_refl. Qed.
Lemma D_67414 : D! W_67414 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_67418 : bv 32 := 0x00e50933.
Lemma F_67418 : F! 0x67418 W_67418.
Proof. vm_refl. Qed.
Lemma D_67418 : D! W_67418 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_6741c : bv 32 := 0x00369693.
Lemma F_6741c : F! 0x6741c W_6741c.
Proof. vm_refl. Qed.
Lemma D_6741c : D! W_6741c (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_67420 : bv 32 := 0x00d506b3.
Lemma F_67420 : F! 0x67420 W_67420.
Proof. vm_refl. Qed.
Lemma D_67420 : D! W_67420 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_67424 : bv 32 := 0x00b68a33.
Lemma F_67424 : F! 0x67424 W_67424.
Proof. vm_refl. Qed.
Lemma D_67424 : D! W_67424 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_67428 : bv 32 := 0x0c890413.
Lemma F_67428 : F! 0x67428 W_67428.
Proof. vm_refl. Qed.
Lemma D_67428 : D! W_67428 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_6742c : bv 32 := 0x04098463.
Lemma F_6742c : F! 0x6742c W_6742c.
Proof. vm_refl. Qed.
Lemma D_6742c : D! W_6742c (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_67430 : bv 32 := 0x00361613.
Lemma F_67430 : F! 0x67430 W_67430.
Proof. vm_refl. Qed.
Lemma D_67430 : D! W_67430 (ShiftImm ALU_SLL 12 12 3).
Proof. vm_refl. Qed.
Definition W_67434 : bv 32 := 0x40c50533.
Lemma F_67434 : F! 0x67434 W_67434.
Proof. vm_refl. Qed.
Lemma D_67434 : D! W_67434 (Op ALU_SUB 10 10 12).
Proof. vm_refl. Qed.
Definition W_67438 : bv 32 := 0x00b50ab3.
Lemma F_67438 : F! 0x67438 W_67438.
Proof. vm_refl. Qed.
Lemma D_67438 : D! W_67438 (Op ALU_ADD 21 10 11).
Proof. vm_refl. Qed.
Definition W_6743c : bv 32 := 0x0289b503.
Lemma F_6743c : F! 0x6743c W_6743c.
Proof. vm_refl. Qed.
Lemma D_6743c : D! W_6743c (Load SZ8 true 10 19 40).
Proof. vm_refl. Qed.
Definition W_67440 : bv 32 := 0x00a40533.
Lemma F_67440 : F! 0x67440 W_67440.
Proof. vm_refl. Qed.
Lemma D_67440 : D! W_67440 (Op ALU_ADD 10 8 10).
Proof. vm_refl. Qed.
Definition W_67444 : bv 32 := 0x7ff50513.
Lemma F_67444 : F! 0x67444 W_67444.
Proof. vm_refl. Qed.
Lemma D_67444 : D! W_67444 (OpImm ALU_ADD 10 10 2047).
Proof. vm_refl. Qed.
Definition W_67448 : bv 32 := 0x00150513.
Lemma F_67448 : F! 0x67448 W_67448.
Proof. vm_refl. Qed.
Lemma D_67448 : D! W_67448 (OpImm ALU_ADD 10 10 1).
Proof. vm_refl. Qed.
Definition W_6744c : bv 32 := 0x00aab023.
Lemma F_6744c : F! 0x6744c W_6744c.
Proof. vm_refl. Qed.
Lemma D_6744c : D! W_6744c (Store SZ8 21 10 0).
Proof. vm_refl. Qed.
Definition W_67450 : bv 32 := 0x0289b503.
Lemma F_67450 : F! 0x67450 W_67450.
Proof. vm_refl. Qed.
Lemma D_67450 : D! W_67450 (Load SZ8 true 10 19 40).
Proof. vm_refl. Qed.
Definition W_67454 : bv 32 := 0x0089b583.
Lemma F_67454 : F! 0x67454 W_67454.
Proof. vm_refl. Qed.
Lemma D_67454 : D! W_67454 (Load SZ8 true 11 19 8).
Proof. vm_refl. Qed.
Definition W_67458 : bv 32 := 0x0109b603.
Lemma F_67458 : F! 0x67458 W_67458.
Proof. vm_refl. Qed.
Lemma D_67458 : D! W_67458 (Load SZ8 true 12 19 16).
Proof. vm_refl. Qed.
Definition W_6745c : bv 32 := 0x00a40533.
Lemma F_6745c : F! 0x6745c W_6745c.
Proof. vm_refl. Qed.
Lemma D_6745c : D! W_6745c (Op ALU_ADD 10 8 10).
Proof. vm_refl. Qed.
Definition W_67460 : bv 32 := 0x5c50d0ef.
Lemma F_67460 : F! 0x67460 W_67460.
Proof. vm_refl. Qed.
Lemma D_67460 : D! W_67460 (Jal 1 56772).
Proof. vm_refl. Qed.
Definition W_67464 : bv 32 := 0x0009b983.
Lemma F_67464 : F! 0x67464 W_67464.
Proof. vm_refl. Qed.
Lemma D_67464 : D! W_67464 (Load SZ8 true 19 19 0).
Proof. vm_refl. Qed.
Definition W_67468 : bv 32 := 0x008a8a93.
Lemma F_67468 : F! 0x67468 W_67468.
Proof. vm_refl. Qed.
Lemma D_67468 : D! W_67468 (OpImm ALU_ADD 21 21 8).
Proof. vm_refl. Qed.
Definition W_6746c : bv 32 := 0xfc0998e3.
Lemma F_6746c : F! 0x6746c W_6746c.
Proof. vm_refl. Qed.
Lemma D_6746c : D! W_6746c (Branch BC_NE 19 0 8144).
Proof. vm_refl. Qed.
Definition W_67470 : bv 32 := 0x0284b603.
Lemma F_67470 : F! 0x67470 W_67470.
Proof. vm_refl. Qed.
Lemma D_67470 : D! W_67470 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_67474 : bv 32 := 0x00ca3023.
Lemma F_67474 : F! 0x67474 W_67474.
Proof. vm_refl. Qed.
Lemma D_67474 : D! W_67474 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_67478 : bv 32 := 0x0d493023.
Lemma F_67478 : F! 0x67478 W_67478.
Proof. vm_refl. Qed.
Lemma D_67478 : D! W_67478 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_6747c : bv 32 := 0x01293023.
Lemma F_6747c : F! 0x6747c W_6747c.
Proof. vm_refl. Qed.
Lemma D_6747c : D! W_6747c (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_67480 : bv 32 := 0x00040513.
Lemma F_67480 : F! 0x67480 W_67480.
Proof. vm_refl. Qed.
Lemma D_67480 : D! W_67480 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_67484 : bv 32 := 0x430110ef.
Lemma F_67484 : F! 0x67484 W_67484.
Proof. vm_refl. Qed.
Lemma D_67484 : D! W_67484 (Jal 1 70704).
Proof. vm_refl. Qed.
Definition W_67488 : bv 32 := 0x04054a63.
Lemma F_67488 : F! 0x67488 W_67488.
Proof. vm_refl. Qed.
Lemma D_67488 : D! W_67488 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_6748c : bv 32 := 0x00051663.
Lemma F_6748c : F! 0x6748c W_6748c.
Proof. vm_refl. Qed.
Lemma D_6748c : D! W_6748c (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_67490 : bv 32 := 0x00100513.
Lemma F_67490 : F! 0x67490 W_67490.
Proof. vm_refl. Qed.
Lemma D_67490 : D! W_67490 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_67494 : bv 32 := 0x00a48023.
Lemma F_67494 : F! 0x67494 W_67494.
Proof. vm_refl. Qed.
Lemma D_67494 : D! W_67494 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_67498 : bv 32 := 0x00200513.
Lemma F_67498 : F! 0x67498 W_67498.
Proof. vm_refl. Qed.
Lemma D_67498 : D! W_67498 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_6749c : bv 32 := 0x0004b597.
Lemma F_6749c : F! 0x6749c W_6749c.
Proof. vm_refl. Qed.
Lemma D_6749c : D! W_6749c (Auipc 11 75).
Proof. vm_refl. Qed.
Definition W_674a0 : bv 32 := 0x02a92423.
Lemma F_674a0 : F! 0x674a0 W_674a0.
Proof. vm_refl. Qed.
Lemma D_674a0 : D! W_674a0 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_674a4 : bv 32 := 0x06000893.
Lemma F_674a4 : F! 0x674a4 W_674a4.
Proof. vm_refl. Qed.
Lemma D_674a4 : D! W_674a4 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_674a8 : bv 32 := 0x1bc58513.
Lemma F_674a8 : F! 0x674a8 W_674a8.
Proof. vm_refl. Qed.
Lemma D_674a8 : D! W_674a8 (OpImm ALU_ADD 10 11 444).
Proof. vm_refl. Qed.
Definition W_674ac : bv 32 := 0x03848593.
Lemma F_674ac : F! 0x674ac W_674ac.
Proof. vm_refl. Qed.
Lemma D_674ac : D! W_674ac (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_674b0 : bv 32 := 0x00000073.
Lemma F_674b0 : F! 0x674b0 W_674b0.
Proof. vm_refl. Qed.
Lemma E_674b0 : is_ecall W_674b0 = true.
Proof. reflexivity. Qed.
Definition W_674b4 : bv 32 := 0x07890613.
Lemma F_674b4 : F! 0x674b4 W_674b4.
Proof. vm_refl. Qed.
Lemma D_674b4 : D! W_674b4 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_674b8 : bv 32 := 0x02a92023.
Lemma F_674b8 : F! 0x674b8 W_674b8.
Proof. vm_refl. Qed.
Lemma D_674b8 : D! W_674b8 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_674bc : bv 32 := 0x08b93c23.
Lemma F_674bc : F! 0x674bc W_674bc.
Proof. vm_refl. Qed.
Lemma D_674bc : D! W_674bc (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_674c0 : bv 32 := 0x06c93c23.
Lemma F_674c0 : F! 0x674c0 W_674c0.
Proof. vm_refl. Qed.
Lemma D_674c0 : D! W_674c0 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_674c4 : bv 32 := 0x0004b517.
Lemma F_674c4 : F! 0x674c4 W_674c4.
Proof. vm_refl. Qed.
Lemma D_674c4 : D! W_674c4 (Auipc 10 75).
Proof. vm_refl. Qed.
Definition W_674c8 : bv 32 := 0x40453503.
Lemma F_674c8 : F! 0x674c8 W_674c8.
Proof. vm_refl. Qed.
Lemma D_674c8 : D! W_674c8 (Load SZ8 true 10 10 1028).
Proof. vm_refl. Qed.
Definition W_674cc : bv 32 := 0x01293423.
Lemma F_674cc : F! 0x674cc W_674cc.
Proof. vm_refl. Qed.
Lemma D_674cc : D! W_674cc (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_674d0 : bv 32 := 0x01293823.
Lemma F_674d0 : F! 0x674d0 W_674d0.
Proof. vm_refl. Qed.
Lemma D_674d0 : D! W_674d0 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_674d4 : bv 32 := 0x00a93c23.
Lemma F_674d4 : F! 0x674d4 W_674d4.
Proof. vm_refl. Qed.
Lemma D_674d4 : D! W_674d4 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_674d8 : bv 32 := 0x0080006f.
Lemma F_674d8 : F! 0x674d8 W_674d8.
Proof. vm_refl. Qed.
Lemma D_674d8 : D! W_674d8 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_674e0 : bv 32 := 0x03813083.
Lemma F_674e0 : F! 0x674e0 W_674e0.
Proof. vm_refl. Qed.
Lemma D_674e0 : D! W_674e0 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_674e4 : bv 32 := 0x03013403.
Lemma F_674e4 : F! 0x674e4 W_674e4.
Proof. vm_refl. Qed.
Lemma D_674e4 : D! W_674e4 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_674e8 : bv 32 := 0x02813483.
Lemma F_674e8 : F! 0x674e8 W_674e8.
Proof. vm_refl. Qed.
Lemma D_674e8 : D! W_674e8 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_674ec : bv 32 := 0x02013903.
Lemma F_674ec : F! 0x674ec W_674ec.
Proof. vm_refl. Qed.
Lemma D_674ec : D! W_674ec (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_674f0 : bv 32 := 0x01813983.
Lemma F_674f0 : F! 0x674f0 W_674f0.
Proof. vm_refl. Qed.
Lemma D_674f0 : D! W_674f0 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_674f4 : bv 32 := 0x01013a03.
Lemma F_674f4 : F! 0x674f4 W_674f4.
Proof. vm_refl. Qed.
Lemma D_674f4 : D! W_674f4 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_674f8 : bv 32 := 0x00813a83.
Lemma F_674f8 : F! 0x674f8 W_674f8.
Proof. vm_refl. Qed.
Lemma D_674f8 : D! W_674f8 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_674fc : bv 32 := 0x04010113.
Lemma F_674fc : F! 0x674fc W_674fc.
Proof. vm_refl. Qed.
Lemma D_674fc : D! W_674fc (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_67500 : bv 32 := 0x00008067.
Lemma F_67500 : F! 0x67500 W_67500.
Proof. vm_refl. Qed.
Lemma D_67500 : D! W_67500 (Jalr 0 1 0).
Proof. vm_refl. Qed.
