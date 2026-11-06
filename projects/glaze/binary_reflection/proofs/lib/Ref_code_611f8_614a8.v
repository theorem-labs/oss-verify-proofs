(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
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
Definition W_611f8 : bv 32 := 0xfc010113.
Lemma F_611f8 : F! 0x611f8 W_611f8.
Proof. vm_refl. Qed.
Lemma D_611f8 : D! W_611f8 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_611fc : bv 32 := 0x02113c23.
Lemma F_611fc : F! 0x611fc W_611fc.
Proof. vm_refl. Qed.
Lemma D_611fc : D! W_611fc (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_61200 : bv 32 := 0x02813823.
Lemma F_61200 : F! 0x61200 W_61200.
Proof. vm_refl. Qed.
Lemma D_61200 : D! W_61200 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_61204 : bv 32 := 0x02913423.
Lemma F_61204 : F! 0x61204 W_61204.
Proof. vm_refl. Qed.
Lemma D_61204 : D! W_61204 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_61208 : bv 32 := 0x03213023.
Lemma F_61208 : F! 0x61208 W_61208.
Proof. vm_refl. Qed.
Lemma D_61208 : D! W_61208 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_6120c : bv 32 := 0x01313c23.
Lemma F_6120c : F! 0x6120c W_6120c.
Proof. vm_refl. Qed.
Lemma D_6120c : D! W_6120c (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_61210 : bv 32 := 0x01413823.
Lemma F_61210 : F! 0x61210 W_61210.
Proof. vm_refl. Qed.
Lemma D_61210 : D! W_61210 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_61214 : bv 32 := 0x01513423.
Lemma F_61214 : F! 0x61214 W_61214.
Proof. vm_refl. Qed.
Lemma D_61214 : D! W_61214 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_61218 : bv 32 := 0x02853683.
Lemma F_61218 : F! 0x61218 W_61218.
Proof. vm_refl. Qed.
Lemma D_61218 : D! W_61218 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_6121c : bv 32 := 0x00045597.
Lemma F_6121c : F! 0x6121c W_6121c.
Proof. vm_refl. Qed.
Lemma D_6121c : D! W_6121c (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_61220 : bv 32 := 0x30c58593.
Lemma F_61220 : F! 0x61220 W_61220.
Proof. vm_refl. Qed.
Lemma D_61220 : D! W_61220 (OpImm ALU_ADD 11 11 780).
Proof. vm_refl. Qed.
Definition W_61224 : bv 32 := 0x00045617.
Lemma F_61224 : F! 0x61224 W_61224.
Proof. vm_refl. Qed.
Lemma D_61224 : D! W_61224 (Auipc 12 69).
Proof. vm_refl. Qed.
Definition W_61228 : bv 32 := 0x58c60493.
Lemma F_61228 : F! 0x61228 W_61228.
Proof. vm_refl. Qed.
Lemma D_61228 : D! W_61228 (OpImm ALU_ADD 9 12 1420).
Proof. vm_refl. Qed.
Definition W_6122c : bv 32 := 0x0c068e63.
Lemma F_6122c : F! 0x6122c W_6122c.
Proof. vm_refl. Qed.
Lemma D_6122c : D! W_6122c (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_61230 : bv 32 := 0x00000613.
Lemma F_61230 : F! 0x61230 W_61230.
Proof. vm_refl. Qed.
Lemma D_61230 : D! W_61230 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_61234 : bv 32 := 0x00000893.
Lemma F_61234 : F! 0x61234 W_61234.
Proof. vm_refl. Qed.
Lemma D_61234 : D! W_61234 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_61238 : bv 32 := 0x00014717.
Lemma F_61238 : F! 0x61238 W_61238.
Proof. vm_refl. Qed.
Lemma D_61238 : D! W_61238 (Auipc 14 20).
Proof. vm_refl. Qed.
Definition W_6123c : bv 32 := 0x01853783.
Lemma F_6123c : F! 0x6123c W_6123c.
Proof. vm_refl. Qed.
Lemma D_6123c : D! W_6123c (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_61240 : bv 32 := 0x02053503.
Lemma F_61240 : F! 0x61240 W_61240.
Proof. vm_refl. Qed.
Lemma D_61240 : D! W_61240 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_61244 : bv 32 := 0x00600813.
Lemma F_61244 : F! 0x61244 W_61244.
Proof. vm_refl. Qed.
Lemma D_61244 : D! W_61244 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_61248 : bv 32 := 0x00013297.
Lemma F_61248 : F! 0x61248 W_61248.
Proof. vm_refl. Qed.
Lemma D_61248 : D! W_61248 (Auipc 5 19).
Proof. vm_refl. Qed.
Definition W_6124c : bv 32 := 0x71076f03.
Lemma F_6124c : F! 0x6124c W_6124c.
Proof. vm_refl. Qed.
Lemma D_6124c : D! W_6124c (Load SZ4 false 30 14 1808).
Proof. vm_refl. Qed.
Definition W_61250 : bv 32 := 0x3702b283.
Lemma F_61250 : F! 0x61250 W_61250.
Proof. vm_refl. Qed.
Lemma D_61250 : D! W_61250 (Load SZ8 true 5 5 880).
Proof. vm_refl. Qed.
Definition W_61254 : bv 32 := 0x00200313.
Lemma F_61254 : F! 0x61254 W_61254.
Proof. vm_refl. Qed.
Lemma D_61254 : D! W_61254 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_61258 : bv 32 := 0x00700393.
Lemma F_61258 : F! 0x61258 W_61258.
Proof. vm_refl. Qed.
Lemma D_61258 : D! W_61258 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_6125c : bv 32 := 0x6474ee37.
Lemma F_6125c : F! 0x6125c W_6125c.
Proof. vm_refl. Qed.
Lemma D_6125c : D! W_6125c (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_61260 : bv 32 := 0x551e0e1b.
Lemma F_61260 : F! 0x61260 W_61260.
Proof. vm_refl. Qed.
Lemma D_61260 : D! W_61260 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_61264 : bv 32 := 0x00078e93.
Lemma F_61264 : F! 0x61264 W_61264.
Proof. vm_refl. Qed.
Lemma D_61264 : D! W_61264 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_61268 : bv 32 := 0x0180006f.
Lemma F_61268 : F! 0x61268 W_61268.
Proof. vm_refl. Qed.
Lemma D_61268 : D! W_61268 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_6126c : bv 32 := 0x010eb603.
Lemma F_6126c : F! 0x6126c W_6126c.
Proof. vm_refl. Qed.
Lemma D_6126c : D! W_6126c (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_61270 : bv 32 := 0x40c78633.
Lemma F_61270 : F! 0x61270 W_61270.
Proof. vm_refl. Qed.
Lemma D_61270 : D! W_61270 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_61274 : bv 32 := 0xfff68693.
Lemma F_61274 : F! 0x61274 W_61274.
Proof. vm_refl. Qed.
Lemma D_61274 : D! W_61274 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_61278 : bv 32 := 0x00ae8eb3.
Lemma F_61278 : F! 0x61278 W_61278.
Proof. vm_refl. Qed.
Lemma D_61278 : D! W_61278 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_6127c : bv 32 := 0x04068a63.
Lemma F_6127c : F! 0x6127c W_6127c.
Proof. vm_refl. Qed.
Lemma D_6127c : D! W_6127c (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_61280 : bv 32 := 0x000ea403.
Lemma F_61280 : F! 0x61280 W_61280.
Proof. vm_refl. Qed.
Lemma D_61280 : D! W_61280 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_61284 : bv 32 := 0xff0404e3.
Lemma F_61284 : F! 0x61284 W_61284.
Proof. vm_refl. Qed.
Lemma D_61284 : D! W_61284 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_61288 : bv 32 := 0x00028a63.
Lemma F_61288 : F! 0x61288 W_61288.
Proof. vm_refl. Qed.
Lemma D_61288 : D! W_61288 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_6129c : bv 32 := 0x000e8f93.
Lemma F_6129c : F! 0x6129c W_6129c.
Proof. vm_refl. Qed.
Lemma D_6129c : D! W_6129c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_612a0 : bv 32 := 0x00740463.
Lemma F_612a0 : F! 0x612a0 W_612a0.
Proof. vm_refl. Qed.
Lemma D_612a0 : D! W_612a0 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_612a4 : bv 32 := 0x00088f93.
Lemma F_612a4 : F! 0x612a4 W_612a4.
Proof. vm_refl. Qed.
Lemma D_612a4 : D! W_612a4 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_612a8 : bv 32 := 0x03c41063.
Lemma F_612a8 : F! 0x612a8 W_612a8.
Proof. vm_refl. Qed.
Lemma D_612a8 : D! W_612a8 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_612ac : bv 32 := 0x028eb883.
Lemma F_612ac : F! 0x612ac W_612ac.
Proof. vm_refl. Qed.
Lemma D_612ac : D! W_612ac (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_612b0 : bv 32 := 0x011f7c63.
Lemma F_612b0 : F! 0x612b0 W_612b0.
Proof. vm_refl. Qed.
Lemma D_612b0 : D! W_612b0 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_612c8 : bv 32 := 0x000f8893.
Lemma F_612c8 : F! 0x612c8 W_612c8.
Proof. vm_refl. Qed.
Lemma D_612c8 : D! W_612c8 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_612cc : bv 32 := 0xfa9ff06f.
Lemma F_612cc : F! 0x612cc W_612cc.
Proof. vm_refl. Qed.
Lemma D_612cc : D! W_612cc (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_612d0 : bv 32 := 0x02088c63.
Lemma F_612d0 : F! 0x612d0 W_612d0.
Proof. vm_refl. Qed.
Lemma D_612d0 : D! W_612d0 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_61308 : bv 32 := 0x0105b603.
Lemma F_61308 : F! 0x61308 W_61308.
Proof. vm_refl. Qed.
Lemma D_61308 : D! W_61308 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_6130c : bv 32 := 0x0205b683.
Lemma F_6130c : F! 0x6130c W_6130c.
Proof. vm_refl. Qed.
Lemma D_6130c : D! W_6130c (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_61310 : bv 32 := 0x0285b503.
Lemma F_61310 : F! 0x61310 W_61310.
Proof. vm_refl. Qed.
Lemma D_61310 : D! W_61310 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_61314 : bv 32 := 0x00c68733.
Lemma F_61314 : F! 0x61314 W_61314.
Proof. vm_refl. Qed.
Lemma D_61314 : D! W_61314 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_61318 : bv 32 := 0xfff50793.
Lemma F_61318 : F! 0x61318 W_61318.
Proof. vm_refl. Qed.
Lemma D_61318 : D! W_61318 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_6131c : bv 32 := 0x40e00733.
Lemma F_6131c : F! 0x6131c W_6131c.
Proof. vm_refl. Qed.
Lemma D_6131c : D! W_6131c (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_61320 : bv 32 := 0x00c7f633.
Lemma F_61320 : F! 0x61320 W_61320.
Proof. vm_refl. Qed.
Lemma D_61320 : D! W_61320 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_61324 : bv 32 := 0x00e7f733.
Lemma F_61324 : F! 0x61324 W_61324.
Proof. vm_refl. Qed.
Lemma D_61324 : D! W_61324 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_61328 : bv 32 := 0x00700793.
Lemma F_61328 : F! 0x61328 W_61328.
Proof. vm_refl. Qed.
Lemma D_61328 : D! W_61328 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_6132c : bv 32 := 0x00d706b3.
Lemma F_6132c : F! 0x6132c W_6132c.
Proof. vm_refl. Qed.
Lemma D_6132c : D! W_6132c (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_61330 : bv 32 := 0x02d5b023.
Lemma F_61330 : F! 0x61330 W_61330.
Proof. vm_refl. Qed.
Lemma D_61330 : D! W_61330 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_61334 : bv 32 := 0x02c5b823.
Lemma F_61334 : F! 0x61334 W_61334.
Proof. vm_refl. Qed.
Lemma D_61334 : D! W_61334 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_61338 : bv 32 := 0x00a7e663.
Lemma F_61338 : F! 0x61338 W_61338.
Proof. vm_refl. Qed.
Lemma D_61338 : D! W_61338 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_6133c : bv 32 := 0x00800513.
Lemma F_6133c : F! 0x6133c W_6133c.
Proof. vm_refl. Qed.
Lemma D_6133c : D! W_6133c (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_61340 : bv 32 := 0x02a5b423.
Lemma F_61340 : F! 0x61340 W_61340.
Proof. vm_refl. Qed.
Lemma D_61340 : D! W_61340 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_61344 : bv 32 := 0x00d60633.
Lemma F_61344 : F! 0x61344 W_61344.
Proof. vm_refl. Qed.
Lemma D_61344 : D! W_61344 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_61348 : bv 32 := 0x000205b7.
Lemma F_61348 : F! 0x61348 W_61348.
Proof. vm_refl. Qed.
Lemma D_61348 : D! W_61348 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_6134c : bv 32 := 0x00a60633.
Lemma F_6134c : F! 0x6134c W_6134c.
Proof. vm_refl. Qed.
Lemma D_6134c : D! W_6134c (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_61350 : bv 32 := 0x0d15869b.
Lemma F_61350 : F! 0x61350 W_61350.
Proof. vm_refl. Qed.
Lemma D_61350 : D! W_61350 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_61354 : bv 32 := 0x0df60593.
Lemma F_61354 : F! 0x61354 W_61354.
Proof. vm_refl. Qed.
Lemma D_61354 : D! W_61354 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_61358 : bv 32 := 0xff85f593.
Lemma F_61358 : F! 0x61358 W_61358.
Proof. vm_refl. Qed.
Lemma D_61358 : D! W_61358 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_6135c : bv 32 := 0x00b4bc23.
Lemma F_6135c : F! 0x6135c W_6135c.
Proof. vm_refl. Qed.
Lemma D_6135c : D! W_6135c (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_61360 : bv 32 := 0x02a4b023.
Lemma F_61360 : F! 0x61360 W_61360.
Proof. vm_refl. Qed.
Lemma D_61360 : D! W_61360 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_61364 : bv 32 := 0x02d5ea63.
Lemma F_61364 : F! 0x61364 W_61364.
Proof. vm_refl. Qed.
Lemma D_61364 : D! W_61364 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_61398 : bv 32 := 0x00025697.
Lemma F_61398 : F! 0x61398 W_61398.
Proof. vm_refl. Qed.
Lemma D_61398 : D! W_61398 (Auipc 13 37).
Proof. vm_refl. Qed.
Definition W_6139c : bv 32 := 0x0104b983.
Lemma F_6139c : F! 0x6139c W_6139c.
Proof. vm_refl. Qed.
Lemma D_6139c : D! W_6139c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_613a0 : bv 32 := 0x0284b603.
Lemma F_613a0 : F! 0x613a0 W_613a0.
Proof. vm_refl. Qed.
Lemma D_613a0 : D! W_613a0 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_613a4 : bv 32 := 0xfff50713.
Lemma F_613a4 : F! 0x613a4 W_613a4.
Proof. vm_refl. Qed.
Lemma D_613a4 : D! W_613a4 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_613a8 : bv 32 := 0xf3800793.
Lemma F_613a8 : F! 0x613a8 W_613a8.
Proof. vm_refl. Qed.
Lemma D_613a8 : D! W_613a8 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_613ac : bv 32 := 0x0c068513.
Lemma F_613ac : F! 0x613ac W_613ac.
Proof. vm_refl. Qed.
Lemma D_613ac : D! W_613ac (OpImm ALU_ADD 10 13 192).
Proof. vm_refl. Qed.
Definition W_613b0 : bv 32 := 0x40a787b3.
Lemma F_613b0 : F! 0x613b0 W_613b0.
Proof. vm_refl. Qed.
Lemma D_613b0 : D! W_613b0 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_613b4 : bv 32 := 0x00f77733.
Lemma F_613b4 : F! 0x613b4 W_613b4.
Proof. vm_refl. Qed.
Lemma D_613b4 : D! W_613b4 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_613b8 : bv 32 := 0xfff64693.
Lemma F_613b8 : F! 0x613b8 W_613b8.
Proof. vm_refl. Qed.
Lemma D_613b8 : D! W_613b8 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_613bc : bv 32 := 0x00e50933.
Lemma F_613bc : F! 0x613bc W_613bc.
Proof. vm_refl. Qed.
Lemma D_613bc : D! W_613bc (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_613c0 : bv 32 := 0x00369693.
Lemma F_613c0 : F! 0x613c0 W_613c0.
Proof. vm_refl. Qed.
Lemma D_613c0 : D! W_613c0 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_613c4 : bv 32 := 0x00d506b3.
Lemma F_613c4 : F! 0x613c4 W_613c4.
Proof. vm_refl. Qed.
Lemma D_613c4 : D! W_613c4 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_613c8 : bv 32 := 0x00b68a33.
Lemma F_613c8 : F! 0x613c8 W_613c8.
Proof. vm_refl. Qed.
Lemma D_613c8 : D! W_613c8 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_613cc : bv 32 := 0x0c890413.
Lemma F_613cc : F! 0x613cc W_613cc.
Proof. vm_refl. Qed.
Lemma D_613cc : D! W_613cc (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_613d0 : bv 32 := 0x04098463.
Lemma F_613d0 : F! 0x613d0 W_613d0.
Proof. vm_refl. Qed.
Lemma D_613d0 : D! W_613d0 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_61418 : bv 32 := 0x00ca3023.
Lemma F_61418 : F! 0x61418 W_61418.
Proof. vm_refl. Qed.
Lemma D_61418 : D! W_61418 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_6141c : bv 32 := 0x0d493023.
Lemma F_6141c : F! 0x6141c W_6141c.
Proof. vm_refl. Qed.
Lemma D_6141c : D! W_6141c (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_61420 : bv 32 := 0x01293023.
Lemma F_61420 : F! 0x61420 W_61420.
Proof. vm_refl. Qed.
Lemma D_61420 : D! W_61420 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_61424 : bv 32 := 0x00040513.
Lemma F_61424 : F! 0x61424 W_61424.
Proof. vm_refl. Qed.
Lemma D_61424 : D! W_61424 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_61428 : bv 32 := 0x1a50e0ef.
Lemma F_61428 : F! 0x61428 W_61428.
Proof. vm_refl. Qed.
Lemma D_61428 : D! W_61428 (Jal 1 59812).
Proof. vm_refl. Qed.
Definition W_6142c : bv 32 := 0x04054a63.
Lemma F_6142c : F! 0x6142c W_6142c.
Proof. vm_refl. Qed.
Lemma D_6142c : D! W_6142c (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_61430 : bv 32 := 0x00051663.
Lemma F_61430 : F! 0x61430 W_61430.
Proof. vm_refl. Qed.
Lemma D_61430 : D! W_61430 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_61434 : bv 32 := 0x00100513.
Lemma F_61434 : F! 0x61434 W_61434.
Proof. vm_refl. Qed.
Lemma D_61434 : D! W_61434 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_61438 : bv 32 := 0x00a48023.
Lemma F_61438 : F! 0x61438 W_61438.
Proof. vm_refl. Qed.
Lemma D_61438 : D! W_61438 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_6143c : bv 32 := 0x00200513.
Lemma F_6143c : F! 0x6143c W_6143c.
Proof. vm_refl. Qed.
Lemma D_6143c : D! W_6143c (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_61440 : bv 32 := 0x00045597.
Lemma F_61440 : F! 0x61440 W_61440.
Proof. vm_refl. Qed.
Lemma D_61440 : D! W_61440 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_61444 : bv 32 := 0x02a92423.
Lemma F_61444 : F! 0x61444 W_61444.
Proof. vm_refl. Qed.
Lemma D_61444 : D! W_61444 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_61448 : bv 32 := 0x06000893.
Lemma F_61448 : F! 0x61448 W_61448.
Proof. vm_refl. Qed.
Lemma D_61448 : D! W_61448 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_6144c : bv 32 := 0x0e858513.
Lemma F_6144c : F! 0x6144c W_6144c.
Proof. vm_refl. Qed.
Lemma D_6144c : D! W_6144c (OpImm ALU_ADD 10 11 232).
Proof. vm_refl. Qed.
Definition W_61450 : bv 32 := 0x03848593.
Lemma F_61450 : F! 0x61450 W_61450.
Proof. vm_refl. Qed.
Lemma D_61450 : D! W_61450 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_61454 : bv 32 := 0x00000073.
Lemma F_61454 : F! 0x61454 W_61454.
Proof. vm_refl. Qed.
Lemma E_61454 : is_ecall W_61454 = true.
Proof. reflexivity. Qed.
Definition W_61458 : bv 32 := 0x07890613.
Lemma F_61458 : F! 0x61458 W_61458.
Proof. vm_refl. Qed.
Lemma D_61458 : D! W_61458 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_6145c : bv 32 := 0x02a92023.
Lemma F_6145c : F! 0x6145c W_6145c.
Proof. vm_refl. Qed.
Lemma D_6145c : D! W_6145c (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_61460 : bv 32 := 0x08b93c23.
Lemma F_61460 : F! 0x61460 W_61460.
Proof. vm_refl. Qed.
Lemma D_61460 : D! W_61460 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_61464 : bv 32 := 0x06c93c23.
Lemma F_61464 : F! 0x61464 W_61464.
Proof. vm_refl. Qed.
Lemma D_61464 : D! W_61464 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_61468 : bv 32 := 0x00045517.
Lemma F_61468 : F! 0x61468 W_61468.
Proof. vm_refl. Qed.
Lemma D_61468 : D! W_61468 (Auipc 10 69).
Proof. vm_refl. Qed.
Definition W_6146c : bv 32 := 0x33053503.
Lemma F_6146c : F! 0x6146c W_6146c.
Proof. vm_refl. Qed.
Lemma D_6146c : D! W_6146c (Load SZ8 true 10 10 816).
Proof. vm_refl. Qed.
Definition W_61470 : bv 32 := 0x01293423.
Lemma F_61470 : F! 0x61470 W_61470.
Proof. vm_refl. Qed.
Lemma D_61470 : D! W_61470 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_61474 : bv 32 := 0x01293823.
Lemma F_61474 : F! 0x61474 W_61474.
Proof. vm_refl. Qed.
Lemma D_61474 : D! W_61474 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_61478 : bv 32 := 0x00a93c23.
Lemma F_61478 : F! 0x61478 W_61478.
Proof. vm_refl. Qed.
Lemma D_61478 : D! W_61478 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_6147c : bv 32 := 0x0080006f.
Lemma F_6147c : F! 0x6147c W_6147c.
Proof. vm_refl. Qed.
Lemma D_6147c : D! W_6147c (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_61484 : bv 32 := 0x03813083.
Lemma F_61484 : F! 0x61484 W_61484.
Proof. vm_refl. Qed.
Lemma D_61484 : D! W_61484 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_61488 : bv 32 := 0x03013403.
Lemma F_61488 : F! 0x61488 W_61488.
Proof. vm_refl. Qed.
Lemma D_61488 : D! W_61488 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_6148c : bv 32 := 0x02813483.
Lemma F_6148c : F! 0x6148c W_6148c.
Proof. vm_refl. Qed.
Lemma D_6148c : D! W_6148c (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_61490 : bv 32 := 0x02013903.
Lemma F_61490 : F! 0x61490 W_61490.
Proof. vm_refl. Qed.
Lemma D_61490 : D! W_61490 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_61494 : bv 32 := 0x01813983.
Lemma F_61494 : F! 0x61494 W_61494.
Proof. vm_refl. Qed.
Lemma D_61494 : D! W_61494 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_61498 : bv 32 := 0x01013a03.
Lemma F_61498 : F! 0x61498 W_61498.
Proof. vm_refl. Qed.
Lemma D_61498 : D! W_61498 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_6149c : bv 32 := 0x00813a83.
Lemma F_6149c : F! 0x6149c W_6149c.
Proof. vm_refl. Qed.
Lemma D_6149c : D! W_6149c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_614a0 : bv 32 := 0x04010113.
Lemma F_614a0 : F! 0x614a0 W_614a0.
Proof. vm_refl. Qed.
Lemma D_614a0 : D! W_614a0 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_614a4 : bv 32 := 0x00008067.
Lemma F_614a4 : F! 0x614a4 W_614a4.
Proof. vm_refl. Qed.
Lemma D_614a4 : D! W_614a4 (Jalr 0 1 0).
Proof. vm_refl. Qed.
