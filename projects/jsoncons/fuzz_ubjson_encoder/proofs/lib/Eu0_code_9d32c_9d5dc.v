(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
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
Definition W_9d32c : bv 32 := 0xfc010113.
Lemma F_9d32c : F! 0x9d32c W_9d32c.
Proof. vm_refl. Qed.
Lemma D_9d32c : D! W_9d32c (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_9d330 : bv 32 := 0x02113c23.
Lemma F_9d330 : F! 0x9d330 W_9d330.
Proof. vm_refl. Qed.
Lemma D_9d330 : D! W_9d330 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_9d334 : bv 32 := 0x02813823.
Lemma F_9d334 : F! 0x9d334 W_9d334.
Proof. vm_refl. Qed.
Lemma D_9d334 : D! W_9d334 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_9d338 : bv 32 := 0x02913423.
Lemma F_9d338 : F! 0x9d338 W_9d338.
Proof. vm_refl. Qed.
Lemma D_9d338 : D! W_9d338 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_9d33c : bv 32 := 0x03213023.
Lemma F_9d33c : F! 0x9d33c W_9d33c.
Proof. vm_refl. Qed.
Lemma D_9d33c : D! W_9d33c (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_9d340 : bv 32 := 0x01313c23.
Lemma F_9d340 : F! 0x9d340 W_9d340.
Proof. vm_refl. Qed.
Lemma D_9d340 : D! W_9d340 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_9d344 : bv 32 := 0x01413823.
Lemma F_9d344 : F! 0x9d344 W_9d344.
Proof. vm_refl. Qed.
Lemma D_9d344 : D! W_9d344 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_9d348 : bv 32 := 0x01513423.
Lemma F_9d348 : F! 0x9d348 W_9d348.
Proof. vm_refl. Qed.
Lemma D_9d348 : D! W_9d348 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_9d34c : bv 32 := 0x02853683.
Lemma F_9d34c : F! 0x9d34c W_9d34c.
Proof. vm_refl. Qed.
Lemma D_9d34c : D! W_9d34c (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_9d350 : bv 32 := 0x00050597.
Lemma F_9d350 : F! 0x9d350 W_9d350.
Proof. vm_refl. Qed.
Lemma D_9d350 : D! W_9d350 (Auipc 11 80).
Proof. vm_refl. Qed.
Definition W_9d354 : bv 32 := 0x87858593.
Lemma F_9d354 : F! 0x9d354 W_9d354.
Proof. vm_refl. Qed.
Lemma D_9d354 : D! W_9d354 (OpImm ALU_ADD 11 11 2168).
Proof. vm_refl. Qed.
Definition W_9d358 : bv 32 := 0x00050617.
Lemma F_9d358 : F! 0x9d358 W_9d358.
Proof. vm_refl. Qed.
Lemma D_9d358 : D! W_9d358 (Auipc 12 80).
Proof. vm_refl. Qed.
Definition W_9d35c : bv 32 := 0xaf860493.
Lemma F_9d35c : F! 0x9d35c W_9d35c.
Proof. vm_refl. Qed.
Lemma D_9d35c : D! W_9d35c (OpImm ALU_ADD 9 12 2808).
Proof. vm_refl. Qed.
Definition W_9d360 : bv 32 := 0x0c068e63.
Lemma F_9d360 : F! 0x9d360 W_9d360.
Proof. vm_refl. Qed.
Lemma D_9d360 : D! W_9d360 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_9d364 : bv 32 := 0x00000613.
Lemma F_9d364 : F! 0x9d364 W_9d364.
Proof. vm_refl. Qed.
Lemma D_9d364 : D! W_9d364 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_9d368 : bv 32 := 0x00000893.
Lemma F_9d368 : F! 0x9d368 W_9d368.
Proof. vm_refl. Qed.
Lemma D_9d368 : D! W_9d368 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_9d36c : bv 32 := 0x0001e717.
Lemma F_9d36c : F! 0x9d36c W_9d36c.
Proof. vm_refl. Qed.
Lemma D_9d36c : D! W_9d36c (Auipc 14 30).
Proof. vm_refl. Qed.
Definition W_9d370 : bv 32 := 0x01853783.
Lemma F_9d370 : F! 0x9d370 W_9d370.
Proof. vm_refl. Qed.
Lemma D_9d370 : D! W_9d370 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_9d374 : bv 32 := 0x02053503.
Lemma F_9d374 : F! 0x9d374 W_9d374.
Proof. vm_refl. Qed.
Lemma D_9d374 : D! W_9d374 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_9d378 : bv 32 := 0x00600813.
Lemma F_9d378 : F! 0x9d378 W_9d378.
Proof. vm_refl. Qed.
Lemma D_9d378 : D! W_9d378 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_9d37c : bv 32 := 0x0001d297.
Lemma F_9d37c : F! 0x9d37c W_9d37c.
Proof. vm_refl. Qed.
Lemma D_9d37c : D! W_9d37c (Auipc 5 29).
Proof. vm_refl. Qed.
Definition W_9d380 : bv 32 := 0xdac76f03.
Lemma F_9d380 : F! 0x9d380 W_9d380.
Proof. vm_refl. Qed.
Lemma D_9d380 : D! W_9d380 (Load SZ4 false 30 14 3500).
Proof. vm_refl. Qed.
Definition W_9d384 : bv 32 := 0x9142b283.
Lemma F_9d384 : F! 0x9d384 W_9d384.
Proof. vm_refl. Qed.
Lemma D_9d384 : D! W_9d384 (Load SZ8 true 5 5 2324).
Proof. vm_refl. Qed.
Definition W_9d388 : bv 32 := 0x00200313.
Lemma F_9d388 : F! 0x9d388 W_9d388.
Proof. vm_refl. Qed.
Lemma D_9d388 : D! W_9d388 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_9d38c : bv 32 := 0x00700393.
Lemma F_9d38c : F! 0x9d38c W_9d38c.
Proof. vm_refl. Qed.
Lemma D_9d38c : D! W_9d38c (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_9d390 : bv 32 := 0x6474ee37.
Lemma F_9d390 : F! 0x9d390 W_9d390.
Proof. vm_refl. Qed.
Lemma D_9d390 : D! W_9d390 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_9d394 : bv 32 := 0x551e0e1b.
Lemma F_9d394 : F! 0x9d394 W_9d394.
Proof. vm_refl. Qed.
Lemma D_9d394 : D! W_9d394 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_9d398 : bv 32 := 0x00078e93.
Lemma F_9d398 : F! 0x9d398 W_9d398.
Proof. vm_refl. Qed.
Lemma D_9d398 : D! W_9d398 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_9d39c : bv 32 := 0x0180006f.
Lemma F_9d39c : F! 0x9d39c W_9d39c.
Proof. vm_refl. Qed.
Lemma D_9d39c : D! W_9d39c (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_9d3a0 : bv 32 := 0x010eb603.
Lemma F_9d3a0 : F! 0x9d3a0 W_9d3a0.
Proof. vm_refl. Qed.
Lemma D_9d3a0 : D! W_9d3a0 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_9d3a4 : bv 32 := 0x40c78633.
Lemma F_9d3a4 : F! 0x9d3a4 W_9d3a4.
Proof. vm_refl. Qed.
Lemma D_9d3a4 : D! W_9d3a4 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_9d3a8 : bv 32 := 0xfff68693.
Lemma F_9d3a8 : F! 0x9d3a8 W_9d3a8.
Proof. vm_refl. Qed.
Lemma D_9d3a8 : D! W_9d3a8 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_9d3ac : bv 32 := 0x00ae8eb3.
Lemma F_9d3ac : F! 0x9d3ac W_9d3ac.
Proof. vm_refl. Qed.
Lemma D_9d3ac : D! W_9d3ac (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_9d3b0 : bv 32 := 0x04068a63.
Lemma F_9d3b0 : F! 0x9d3b0 W_9d3b0.
Proof. vm_refl. Qed.
Lemma D_9d3b0 : D! W_9d3b0 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_9d3b4 : bv 32 := 0x000ea403.
Lemma F_9d3b4 : F! 0x9d3b4 W_9d3b4.
Proof. vm_refl. Qed.
Lemma D_9d3b4 : D! W_9d3b4 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_9d3b8 : bv 32 := 0xff0404e3.
Lemma F_9d3b8 : F! 0x9d3b8 W_9d3b8.
Proof. vm_refl. Qed.
Lemma D_9d3b8 : D! W_9d3b8 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_9d3bc : bv 32 := 0x00028a63.
Lemma F_9d3bc : F! 0x9d3bc W_9d3bc.
Proof. vm_refl. Qed.
Lemma D_9d3bc : D! W_9d3bc (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_9d3d0 : bv 32 := 0x000e8f93.
Lemma F_9d3d0 : F! 0x9d3d0 W_9d3d0.
Proof. vm_refl. Qed.
Lemma D_9d3d0 : D! W_9d3d0 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_9d3d4 : bv 32 := 0x00740463.
Lemma F_9d3d4 : F! 0x9d3d4 W_9d3d4.
Proof. vm_refl. Qed.
Lemma D_9d3d4 : D! W_9d3d4 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_9d3d8 : bv 32 := 0x00088f93.
Lemma F_9d3d8 : F! 0x9d3d8 W_9d3d8.
Proof. vm_refl. Qed.
Lemma D_9d3d8 : D! W_9d3d8 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_9d3dc : bv 32 := 0x03c41063.
Lemma F_9d3dc : F! 0x9d3dc W_9d3dc.
Proof. vm_refl. Qed.
Lemma D_9d3dc : D! W_9d3dc (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_9d3e0 : bv 32 := 0x028eb883.
Lemma F_9d3e0 : F! 0x9d3e0 W_9d3e0.
Proof. vm_refl. Qed.
Lemma D_9d3e0 : D! W_9d3e0 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_9d3e4 : bv 32 := 0x011f7c63.
Lemma F_9d3e4 : F! 0x9d3e4 W_9d3e4.
Proof. vm_refl. Qed.
Lemma D_9d3e4 : D! W_9d3e4 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_9d3fc : bv 32 := 0x000f8893.
Lemma F_9d3fc : F! 0x9d3fc W_9d3fc.
Proof. vm_refl. Qed.
Lemma D_9d3fc : D! W_9d3fc (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_9d400 : bv 32 := 0xfa9ff06f.
Lemma F_9d400 : F! 0x9d400 W_9d400.
Proof. vm_refl. Qed.
Lemma D_9d400 : D! W_9d400 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_9d404 : bv 32 := 0x02088c63.
Lemma F_9d404 : F! 0x9d404 W_9d404.
Proof. vm_refl. Qed.
Lemma D_9d404 : D! W_9d404 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_9d43c : bv 32 := 0x0105b603.
Lemma F_9d43c : F! 0x9d43c W_9d43c.
Proof. vm_refl. Qed.
Lemma D_9d43c : D! W_9d43c (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_9d440 : bv 32 := 0x0205b683.
Lemma F_9d440 : F! 0x9d440 W_9d440.
Proof. vm_refl. Qed.
Lemma D_9d440 : D! W_9d440 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_9d444 : bv 32 := 0x0285b503.
Lemma F_9d444 : F! 0x9d444 W_9d444.
Proof. vm_refl. Qed.
Lemma D_9d444 : D! W_9d444 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_9d448 : bv 32 := 0x00c68733.
Lemma F_9d448 : F! 0x9d448 W_9d448.
Proof. vm_refl. Qed.
Lemma D_9d448 : D! W_9d448 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_9d44c : bv 32 := 0xfff50793.
Lemma F_9d44c : F! 0x9d44c W_9d44c.
Proof. vm_refl. Qed.
Lemma D_9d44c : D! W_9d44c (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_9d450 : bv 32 := 0x40e00733.
Lemma F_9d450 : F! 0x9d450 W_9d450.
Proof. vm_refl. Qed.
Lemma D_9d450 : D! W_9d450 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_9d454 : bv 32 := 0x00c7f633.
Lemma F_9d454 : F! 0x9d454 W_9d454.
Proof. vm_refl. Qed.
Lemma D_9d454 : D! W_9d454 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_9d458 : bv 32 := 0x00e7f733.
Lemma F_9d458 : F! 0x9d458 W_9d458.
Proof. vm_refl. Qed.
Lemma D_9d458 : D! W_9d458 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_9d45c : bv 32 := 0x00700793.
Lemma F_9d45c : F! 0x9d45c W_9d45c.
Proof. vm_refl. Qed.
Lemma D_9d45c : D! W_9d45c (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_9d460 : bv 32 := 0x00d706b3.
Lemma F_9d460 : F! 0x9d460 W_9d460.
Proof. vm_refl. Qed.
Lemma D_9d460 : D! W_9d460 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_9d464 : bv 32 := 0x02d5b023.
Lemma F_9d464 : F! 0x9d464 W_9d464.
Proof. vm_refl. Qed.
Lemma D_9d464 : D! W_9d464 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_9d468 : bv 32 := 0x02c5b823.
Lemma F_9d468 : F! 0x9d468 W_9d468.
Proof. vm_refl. Qed.
Lemma D_9d468 : D! W_9d468 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_9d46c : bv 32 := 0x00a7e663.
Lemma F_9d46c : F! 0x9d46c W_9d46c.
Proof. vm_refl. Qed.
Lemma D_9d46c : D! W_9d46c (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_9d470 : bv 32 := 0x00800513.
Lemma F_9d470 : F! 0x9d470 W_9d470.
Proof. vm_refl. Qed.
Lemma D_9d470 : D! W_9d470 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_9d474 : bv 32 := 0x02a5b423.
Lemma F_9d474 : F! 0x9d474 W_9d474.
Proof. vm_refl. Qed.
Lemma D_9d474 : D! W_9d474 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_9d478 : bv 32 := 0x00d60633.
Lemma F_9d478 : F! 0x9d478 W_9d478.
Proof. vm_refl. Qed.
Lemma D_9d478 : D! W_9d478 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_9d47c : bv 32 := 0x000205b7.
Lemma F_9d47c : F! 0x9d47c W_9d47c.
Proof. vm_refl. Qed.
Lemma D_9d47c : D! W_9d47c (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_9d480 : bv 32 := 0x00a60633.
Lemma F_9d480 : F! 0x9d480 W_9d480.
Proof. vm_refl. Qed.
Lemma D_9d480 : D! W_9d480 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_9d484 : bv 32 := 0x0d15869b.
Lemma F_9d484 : F! 0x9d484 W_9d484.
Proof. vm_refl. Qed.
Lemma D_9d484 : D! W_9d484 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_9d488 : bv 32 := 0x0df60593.
Lemma F_9d488 : F! 0x9d488 W_9d488.
Proof. vm_refl. Qed.
Lemma D_9d488 : D! W_9d488 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_9d48c : bv 32 := 0xff85f593.
Lemma F_9d48c : F! 0x9d48c W_9d48c.
Proof. vm_refl. Qed.
Lemma D_9d48c : D! W_9d48c (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_9d490 : bv 32 := 0x00b4bc23.
Lemma F_9d490 : F! 0x9d490 W_9d490.
Proof. vm_refl. Qed.
Lemma D_9d490 : D! W_9d490 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_9d494 : bv 32 := 0x02a4b023.
Lemma F_9d494 : F! 0x9d494 W_9d494.
Proof. vm_refl. Qed.
Lemma D_9d494 : D! W_9d494 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_9d498 : bv 32 := 0x02d5ea63.
Lemma F_9d498 : F! 0x9d498 W_9d498.
Proof. vm_refl. Qed.
Lemma D_9d498 : D! W_9d498 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_9d4cc : bv 32 := 0x0002f697.
Lemma F_9d4cc : F! 0x9d4cc W_9d4cc.
Proof. vm_refl. Qed.
Lemma D_9d4cc : D! W_9d4cc (Auipc 13 47).
Proof. vm_refl. Qed.
Definition W_9d4d0 : bv 32 := 0x0104b983.
Lemma F_9d4d0 : F! 0x9d4d0 W_9d4d0.
Proof. vm_refl. Qed.
Lemma D_9d4d0 : D! W_9d4d0 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_9d4d4 : bv 32 := 0x0284b603.
Lemma F_9d4d4 : F! 0x9d4d4 W_9d4d4.
Proof. vm_refl. Qed.
Lemma D_9d4d4 : D! W_9d4d4 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_9d4d8 : bv 32 := 0xfff50713.
Lemma F_9d4d8 : F! 0x9d4d8 W_9d4d8.
Proof. vm_refl. Qed.
Lemma D_9d4d8 : D! W_9d4d8 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_9d4dc : bv 32 := 0xf3800793.
Lemma F_9d4dc : F! 0x9d4dc W_9d4dc.
Proof. vm_refl. Qed.
Lemma D_9d4dc : D! W_9d4dc (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_9d4e0 : bv 32 := 0x62c68513.
Lemma F_9d4e0 : F! 0x9d4e0 W_9d4e0.
Proof. vm_refl. Qed.
Lemma D_9d4e0 : D! W_9d4e0 (OpImm ALU_ADD 10 13 1580).
Proof. vm_refl. Qed.
Definition W_9d4e4 : bv 32 := 0x40a787b3.
Lemma F_9d4e4 : F! 0x9d4e4 W_9d4e4.
Proof. vm_refl. Qed.
Lemma D_9d4e4 : D! W_9d4e4 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_9d4e8 : bv 32 := 0x00f77733.
Lemma F_9d4e8 : F! 0x9d4e8 W_9d4e8.
Proof. vm_refl. Qed.
Lemma D_9d4e8 : D! W_9d4e8 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_9d4ec : bv 32 := 0xfff64693.
Lemma F_9d4ec : F! 0x9d4ec W_9d4ec.
Proof. vm_refl. Qed.
Lemma D_9d4ec : D! W_9d4ec (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_9d4f0 : bv 32 := 0x00e50933.
Lemma F_9d4f0 : F! 0x9d4f0 W_9d4f0.
Proof. vm_refl. Qed.
Lemma D_9d4f0 : D! W_9d4f0 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_9d4f4 : bv 32 := 0x00369693.
Lemma F_9d4f4 : F! 0x9d4f4 W_9d4f4.
Proof. vm_refl. Qed.
Lemma D_9d4f4 : D! W_9d4f4 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_9d4f8 : bv 32 := 0x00d506b3.
Lemma F_9d4f8 : F! 0x9d4f8 W_9d4f8.
Proof. vm_refl. Qed.
Lemma D_9d4f8 : D! W_9d4f8 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_9d4fc : bv 32 := 0x00b68a33.
Lemma F_9d4fc : F! 0x9d4fc W_9d4fc.
Proof. vm_refl. Qed.
Lemma D_9d4fc : D! W_9d4fc (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_9d500 : bv 32 := 0x0c890413.
Lemma F_9d500 : F! 0x9d500 W_9d500.
Proof. vm_refl. Qed.
Lemma D_9d500 : D! W_9d500 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_9d504 : bv 32 := 0x04098463.
Lemma F_9d504 : F! 0x9d504 W_9d504.
Proof. vm_refl. Qed.
Lemma D_9d504 : D! W_9d504 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_9d54c : bv 32 := 0x00ca3023.
Lemma F_9d54c : F! 0x9d54c W_9d54c.
Proof. vm_refl. Qed.
Lemma D_9d54c : D! W_9d54c (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_9d550 : bv 32 := 0x0d493023.
Lemma F_9d550 : F! 0x9d550 W_9d550.
Proof. vm_refl. Qed.
Lemma D_9d550 : D! W_9d550 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_9d554 : bv 32 := 0x01293023.
Lemma F_9d554 : F! 0x9d554 W_9d554.
Proof. vm_refl. Qed.
Lemma D_9d554 : D! W_9d554 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_9d558 : bv 32 := 0x00040513.
Lemma F_9d558 : F! 0x9d558 W_9d558.
Proof. vm_refl. Qed.
Lemma D_9d558 : D! W_9d558 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_9d55c : bv 32 := 0x16c130ef.
Lemma F_9d55c : F! 0x9d55c W_9d55c.
Proof. vm_refl. Qed.
Lemma D_9d55c : D! W_9d55c (Jal 1 78188).
Proof. vm_refl. Qed.
Definition W_9d560 : bv 32 := 0x04054a63.
Lemma F_9d560 : F! 0x9d560 W_9d560.
Proof. vm_refl. Qed.
Lemma D_9d560 : D! W_9d560 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_9d564 : bv 32 := 0x00051663.
Lemma F_9d564 : F! 0x9d564 W_9d564.
Proof. vm_refl. Qed.
Lemma D_9d564 : D! W_9d564 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_9d568 : bv 32 := 0x00100513.
Lemma F_9d568 : F! 0x9d568 W_9d568.
Proof. vm_refl. Qed.
Lemma D_9d568 : D! W_9d568 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_9d56c : bv 32 := 0x00a48023.
Lemma F_9d56c : F! 0x9d56c W_9d56c.
Proof. vm_refl. Qed.
Lemma D_9d56c : D! W_9d56c (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_9d570 : bv 32 := 0x00200513.
Lemma F_9d570 : F! 0x9d570 W_9d570.
Proof. vm_refl. Qed.
Lemma D_9d570 : D! W_9d570 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_9d574 : bv 32 := 0x0004f597.
Lemma F_9d574 : F! 0x9d574 W_9d574.
Proof. vm_refl. Qed.
Lemma D_9d574 : D! W_9d574 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_9d578 : bv 32 := 0x02a92423.
Lemma F_9d578 : F! 0x9d578 W_9d578.
Proof. vm_refl. Qed.
Lemma D_9d578 : D! W_9d578 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_9d57c : bv 32 := 0x06000893.
Lemma F_9d57c : F! 0x9d57c W_9d57c.
Proof. vm_refl. Qed.
Lemma D_9d57c : D! W_9d57c (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_9d580 : bv 32 := 0x65458513.
Lemma F_9d580 : F! 0x9d580 W_9d580.
Proof. vm_refl. Qed.
Lemma D_9d580 : D! W_9d580 (OpImm ALU_ADD 10 11 1620).
Proof. vm_refl. Qed.
Definition W_9d584 : bv 32 := 0x03848593.
Lemma F_9d584 : F! 0x9d584 W_9d584.
Proof. vm_refl. Qed.
Lemma D_9d584 : D! W_9d584 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_9d588 : bv 32 := 0x00000073.
Lemma F_9d588 : F! 0x9d588 W_9d588.
Proof. vm_refl. Qed.
Lemma E_9d588 : is_ecall W_9d588 = true.
Proof. reflexivity. Qed.
Definition W_9d58c : bv 32 := 0x07890613.
Lemma F_9d58c : F! 0x9d58c W_9d58c.
Proof. vm_refl. Qed.
Lemma D_9d58c : D! W_9d58c (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_9d590 : bv 32 := 0x02a92023.
Lemma F_9d590 : F! 0x9d590 W_9d590.
Proof. vm_refl. Qed.
Lemma D_9d590 : D! W_9d590 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_9d594 : bv 32 := 0x08b93c23.
Lemma F_9d594 : F! 0x9d594 W_9d594.
Proof. vm_refl. Qed.
Lemma D_9d594 : D! W_9d594 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_9d598 : bv 32 := 0x06c93c23.
Lemma F_9d598 : F! 0x9d598 W_9d598.
Proof. vm_refl. Qed.
Lemma D_9d598 : D! W_9d598 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_9d59c : bv 32 := 0x00050517.
Lemma F_9d59c : F! 0x9d59c W_9d59c.
Proof. vm_refl. Qed.
Lemma D_9d59c : D! W_9d59c (Auipc 10 80).
Proof. vm_refl. Qed.
Definition W_9d5a0 : bv 32 := 0x89c53503.
Lemma F_9d5a0 : F! 0x9d5a0 W_9d5a0.
Proof. vm_refl. Qed.
Lemma D_9d5a0 : D! W_9d5a0 (Load SZ8 true 10 10 2204).
Proof. vm_refl. Qed.
Definition W_9d5a4 : bv 32 := 0x01293423.
Lemma F_9d5a4 : F! 0x9d5a4 W_9d5a4.
Proof. vm_refl. Qed.
Lemma D_9d5a4 : D! W_9d5a4 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_9d5a8 : bv 32 := 0x01293823.
Lemma F_9d5a8 : F! 0x9d5a8 W_9d5a8.
Proof. vm_refl. Qed.
Lemma D_9d5a8 : D! W_9d5a8 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_9d5ac : bv 32 := 0x00a93c23.
Lemma F_9d5ac : F! 0x9d5ac W_9d5ac.
Proof. vm_refl. Qed.
Lemma D_9d5ac : D! W_9d5ac (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_9d5b0 : bv 32 := 0x0080006f.
Lemma F_9d5b0 : F! 0x9d5b0 W_9d5b0.
Proof. vm_refl. Qed.
Lemma D_9d5b0 : D! W_9d5b0 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_9d5b8 : bv 32 := 0x03813083.
Lemma F_9d5b8 : F! 0x9d5b8 W_9d5b8.
Proof. vm_refl. Qed.
Lemma D_9d5b8 : D! W_9d5b8 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_9d5bc : bv 32 := 0x03013403.
Lemma F_9d5bc : F! 0x9d5bc W_9d5bc.
Proof. vm_refl. Qed.
Lemma D_9d5bc : D! W_9d5bc (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_9d5c0 : bv 32 := 0x02813483.
Lemma F_9d5c0 : F! 0x9d5c0 W_9d5c0.
Proof. vm_refl. Qed.
Lemma D_9d5c0 : D! W_9d5c0 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_9d5c4 : bv 32 := 0x02013903.
Lemma F_9d5c4 : F! 0x9d5c4 W_9d5c4.
Proof. vm_refl. Qed.
Lemma D_9d5c4 : D! W_9d5c4 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_9d5c8 : bv 32 := 0x01813983.
Lemma F_9d5c8 : F! 0x9d5c8 W_9d5c8.
Proof. vm_refl. Qed.
Lemma D_9d5c8 : D! W_9d5c8 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_9d5cc : bv 32 := 0x01013a03.
Lemma F_9d5cc : F! 0x9d5cc W_9d5cc.
Proof. vm_refl. Qed.
Lemma D_9d5cc : D! W_9d5cc (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_9d5d0 : bv 32 := 0x00813a83.
Lemma F_9d5d0 : F! 0x9d5d0 W_9d5d0.
Proof. vm_refl. Qed.
Lemma D_9d5d0 : D! W_9d5d0 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_9d5d4 : bv 32 := 0x04010113.
Lemma F_9d5d4 : F! 0x9d5d4 W_9d5d4.
Proof. vm_refl. Qed.
Lemma D_9d5d4 : D! W_9d5d4 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_9d5d8 : bv 32 := 0x00008067.
Lemma F_9d5d8 : F! 0x9d5d8 W_9d5d8.
Proof. vm_refl. Qed.
Lemma D_9d5d8 : D! W_9d5d8 (Jalr 0 1 0).
Proof. vm_refl. Qed.
