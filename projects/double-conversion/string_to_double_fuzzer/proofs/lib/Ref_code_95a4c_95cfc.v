(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.double_conversion.string_to_double_fuzzer.images Require Import Plain.
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
Definition W_95a4c : bv 32 := 0xfc010113.
Lemma F_95a4c : F! 0x95a4c W_95a4c.
Proof. vm_refl. Qed.
Lemma D_95a4c : D! W_95a4c (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_95a50 : bv 32 := 0x02113c23.
Lemma F_95a50 : F! 0x95a50 W_95a50.
Proof. vm_refl. Qed.
Lemma D_95a50 : D! W_95a50 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_95a54 : bv 32 := 0x02813823.
Lemma F_95a54 : F! 0x95a54 W_95a54.
Proof. vm_refl. Qed.
Lemma D_95a54 : D! W_95a54 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_95a58 : bv 32 := 0x02913423.
Lemma F_95a58 : F! 0x95a58 W_95a58.
Proof. vm_refl. Qed.
Lemma D_95a58 : D! W_95a58 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_95a5c : bv 32 := 0x03213023.
Lemma F_95a5c : F! 0x95a5c W_95a5c.
Proof. vm_refl. Qed.
Lemma D_95a5c : D! W_95a5c (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_95a60 : bv 32 := 0x01313c23.
Lemma F_95a60 : F! 0x95a60 W_95a60.
Proof. vm_refl. Qed.
Lemma D_95a60 : D! W_95a60 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_95a64 : bv 32 := 0x01413823.
Lemma F_95a64 : F! 0x95a64 W_95a64.
Proof. vm_refl. Qed.
Lemma D_95a64 : D! W_95a64 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_95a68 : bv 32 := 0x01513423.
Lemma F_95a68 : F! 0x95a68 W_95a68.
Proof. vm_refl. Qed.
Lemma D_95a68 : D! W_95a68 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_95a6c : bv 32 := 0x02853683.
Lemma F_95a6c : F! 0x95a6c W_95a6c.
Proof. vm_refl. Qed.
Lemma D_95a6c : D! W_95a6c (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_95a70 : bv 32 := 0x0004f597.
Lemma F_95a70 : F! 0x95a70 W_95a70.
Proof. vm_refl. Qed.
Lemma D_95a70 : D! W_95a70 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_95a74 : bv 32 := 0xeb058593.
Lemma F_95a74 : F! 0x95a74 W_95a74.
Proof. vm_refl. Qed.
Lemma D_95a74 : D! W_95a74 (OpImm ALU_ADD 11 11 3760).
Proof. vm_refl. Qed.
Definition W_95a78 : bv 32 := 0x0004f617.
Lemma F_95a78 : F! 0x95a78 W_95a78.
Proof. vm_refl. Qed.
Lemma D_95a78 : D! W_95a78 (Auipc 12 79).
Proof. vm_refl. Qed.
Definition W_95a7c : bv 32 := 0x13060493.
Lemma F_95a7c : F! 0x95a7c W_95a7c.
Proof. vm_refl. Qed.
Lemma D_95a7c : D! W_95a7c (OpImm ALU_ADD 9 12 304).
Proof. vm_refl. Qed.
Definition W_95a80 : bv 32 := 0x0c068e63.
Lemma F_95a80 : F! 0x95a80 W_95a80.
Proof. vm_refl. Qed.
Lemma D_95a80 : D! W_95a80 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_95a84 : bv 32 := 0x00000613.
Lemma F_95a84 : F! 0x95a84 W_95a84.
Proof. vm_refl. Qed.
Lemma D_95a84 : D! W_95a84 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_95a88 : bv 32 := 0x00000893.
Lemma F_95a88 : F! 0x95a88 W_95a88.
Proof. vm_refl. Qed.
Lemma D_95a88 : D! W_95a88 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_95a8c : bv 32 := 0x0001d717.
Lemma F_95a8c : F! 0x95a8c W_95a8c.
Proof. vm_refl. Qed.
Lemma D_95a8c : D! W_95a8c (Auipc 14 29).
Proof. vm_refl. Qed.
Definition W_95a90 : bv 32 := 0x01853783.
Lemma F_95a90 : F! 0x95a90 W_95a90.
Proof. vm_refl. Qed.
Lemma D_95a90 : D! W_95a90 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_95a94 : bv 32 := 0x02053503.
Lemma F_95a94 : F! 0x95a94 W_95a94.
Proof. vm_refl. Qed.
Lemma D_95a94 : D! W_95a94 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_95a98 : bv 32 := 0x00600813.
Lemma F_95a98 : F! 0x95a98 W_95a98.
Proof. vm_refl. Qed.
Lemma D_95a98 : D! W_95a98 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_95a9c : bv 32 := 0x0001c297.
Lemma F_95a9c : F! 0x95a9c W_95a9c.
Proof. vm_refl. Qed.
Lemma D_95a9c : D! W_95a9c (Auipc 5 28).
Proof. vm_refl. Qed.
Definition W_95aa0 : bv 32 := 0x3f476f03.
Lemma F_95aa0 : F! 0x95aa0 W_95aa0.
Proof. vm_refl. Qed.
Lemma D_95aa0 : D! W_95aa0 (Load SZ4 false 30 14 1012).
Proof. vm_refl. Qed.
Definition W_95aa4 : bv 32 := 0xfac2b283.
Lemma F_95aa4 : F! 0x95aa4 W_95aa4.
Proof. vm_refl. Qed.
Lemma D_95aa4 : D! W_95aa4 (Load SZ8 true 5 5 4012).
Proof. vm_refl. Qed.
Definition W_95aa8 : bv 32 := 0x00200313.
Lemma F_95aa8 : F! 0x95aa8 W_95aa8.
Proof. vm_refl. Qed.
Lemma D_95aa8 : D! W_95aa8 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_95aac : bv 32 := 0x00700393.
Lemma F_95aac : F! 0x95aac W_95aac.
Proof. vm_refl. Qed.
Lemma D_95aac : D! W_95aac (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_95ab0 : bv 32 := 0x6474ee37.
Lemma F_95ab0 : F! 0x95ab0 W_95ab0.
Proof. vm_refl. Qed.
Lemma D_95ab0 : D! W_95ab0 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_95ab4 : bv 32 := 0x551e0e1b.
Lemma F_95ab4 : F! 0x95ab4 W_95ab4.
Proof. vm_refl. Qed.
Lemma D_95ab4 : D! W_95ab4 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_95ab8 : bv 32 := 0x00078e93.
Lemma F_95ab8 : F! 0x95ab8 W_95ab8.
Proof. vm_refl. Qed.
Lemma D_95ab8 : D! W_95ab8 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_95abc : bv 32 := 0x0180006f.
Lemma F_95abc : F! 0x95abc W_95abc.
Proof. vm_refl. Qed.
Lemma D_95abc : D! W_95abc (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_95ac0 : bv 32 := 0x010eb603.
Lemma F_95ac0 : F! 0x95ac0 W_95ac0.
Proof. vm_refl. Qed.
Lemma D_95ac0 : D! W_95ac0 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_95ac4 : bv 32 := 0x40c78633.
Lemma F_95ac4 : F! 0x95ac4 W_95ac4.
Proof. vm_refl. Qed.
Lemma D_95ac4 : D! W_95ac4 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_95ac8 : bv 32 := 0xfff68693.
Lemma F_95ac8 : F! 0x95ac8 W_95ac8.
Proof. vm_refl. Qed.
Lemma D_95ac8 : D! W_95ac8 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_95acc : bv 32 := 0x00ae8eb3.
Lemma F_95acc : F! 0x95acc W_95acc.
Proof. vm_refl. Qed.
Lemma D_95acc : D! W_95acc (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_95ad0 : bv 32 := 0x04068a63.
Lemma F_95ad0 : F! 0x95ad0 W_95ad0.
Proof. vm_refl. Qed.
Lemma D_95ad0 : D! W_95ad0 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_95ad4 : bv 32 := 0x000ea403.
Lemma F_95ad4 : F! 0x95ad4 W_95ad4.
Proof. vm_refl. Qed.
Lemma D_95ad4 : D! W_95ad4 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_95ad8 : bv 32 := 0xff0404e3.
Lemma F_95ad8 : F! 0x95ad8 W_95ad8.
Proof. vm_refl. Qed.
Lemma D_95ad8 : D! W_95ad8 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_95adc : bv 32 := 0x00028a63.
Lemma F_95adc : F! 0x95adc W_95adc.
Proof. vm_refl. Qed.
Lemma D_95adc : D! W_95adc (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_95af0 : bv 32 := 0x000e8f93.
Lemma F_95af0 : F! 0x95af0 W_95af0.
Proof. vm_refl. Qed.
Lemma D_95af0 : D! W_95af0 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_95af4 : bv 32 := 0x00740463.
Lemma F_95af4 : F! 0x95af4 W_95af4.
Proof. vm_refl. Qed.
Lemma D_95af4 : D! W_95af4 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_95af8 : bv 32 := 0x00088f93.
Lemma F_95af8 : F! 0x95af8 W_95af8.
Proof. vm_refl. Qed.
Lemma D_95af8 : D! W_95af8 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_95afc : bv 32 := 0x03c41063.
Lemma F_95afc : F! 0x95afc W_95afc.
Proof. vm_refl. Qed.
Lemma D_95afc : D! W_95afc (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_95b00 : bv 32 := 0x028eb883.
Lemma F_95b00 : F! 0x95b00 W_95b00.
Proof. vm_refl. Qed.
Lemma D_95b00 : D! W_95b00 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_95b04 : bv 32 := 0x011f7c63.
Lemma F_95b04 : F! 0x95b04 W_95b04.
Proof. vm_refl. Qed.
Lemma D_95b04 : D! W_95b04 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_95b1c : bv 32 := 0x000f8893.
Lemma F_95b1c : F! 0x95b1c W_95b1c.
Proof. vm_refl. Qed.
Lemma D_95b1c : D! W_95b1c (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_95b20 : bv 32 := 0xfa9ff06f.
Lemma F_95b20 : F! 0x95b20 W_95b20.
Proof. vm_refl. Qed.
Lemma D_95b20 : D! W_95b20 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_95b24 : bv 32 := 0x02088c63.
Lemma F_95b24 : F! 0x95b24 W_95b24.
Proof. vm_refl. Qed.
Lemma D_95b24 : D! W_95b24 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_95b5c : bv 32 := 0x0105b603.
Lemma F_95b5c : F! 0x95b5c W_95b5c.
Proof. vm_refl. Qed.
Lemma D_95b5c : D! W_95b5c (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_95b60 : bv 32 := 0x0205b683.
Lemma F_95b60 : F! 0x95b60 W_95b60.
Proof. vm_refl. Qed.
Lemma D_95b60 : D! W_95b60 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_95b64 : bv 32 := 0x0285b503.
Lemma F_95b64 : F! 0x95b64 W_95b64.
Proof. vm_refl. Qed.
Lemma D_95b64 : D! W_95b64 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_95b68 : bv 32 := 0x00c68733.
Lemma F_95b68 : F! 0x95b68 W_95b68.
Proof. vm_refl. Qed.
Lemma D_95b68 : D! W_95b68 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_95b6c : bv 32 := 0xfff50793.
Lemma F_95b6c : F! 0x95b6c W_95b6c.
Proof. vm_refl. Qed.
Lemma D_95b6c : D! W_95b6c (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_95b70 : bv 32 := 0x40e00733.
Lemma F_95b70 : F! 0x95b70 W_95b70.
Proof. vm_refl. Qed.
Lemma D_95b70 : D! W_95b70 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_95b74 : bv 32 := 0x00c7f633.
Lemma F_95b74 : F! 0x95b74 W_95b74.
Proof. vm_refl. Qed.
Lemma D_95b74 : D! W_95b74 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_95b78 : bv 32 := 0x00e7f733.
Lemma F_95b78 : F! 0x95b78 W_95b78.
Proof. vm_refl. Qed.
Lemma D_95b78 : D! W_95b78 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_95b7c : bv 32 := 0x00700793.
Lemma F_95b7c : F! 0x95b7c W_95b7c.
Proof. vm_refl. Qed.
Lemma D_95b7c : D! W_95b7c (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_95b80 : bv 32 := 0x00d706b3.
Lemma F_95b80 : F! 0x95b80 W_95b80.
Proof. vm_refl. Qed.
Lemma D_95b80 : D! W_95b80 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_95b84 : bv 32 := 0x02d5b023.
Lemma F_95b84 : F! 0x95b84 W_95b84.
Proof. vm_refl. Qed.
Lemma D_95b84 : D! W_95b84 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_95b88 : bv 32 := 0x02c5b823.
Lemma F_95b88 : F! 0x95b88 W_95b88.
Proof. vm_refl. Qed.
Lemma D_95b88 : D! W_95b88 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_95b8c : bv 32 := 0x00a7e663.
Lemma F_95b8c : F! 0x95b8c W_95b8c.
Proof. vm_refl. Qed.
Lemma D_95b8c : D! W_95b8c (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_95b90 : bv 32 := 0x00800513.
Lemma F_95b90 : F! 0x95b90 W_95b90.
Proof. vm_refl. Qed.
Lemma D_95b90 : D! W_95b90 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_95b94 : bv 32 := 0x02a5b423.
Lemma F_95b94 : F! 0x95b94 W_95b94.
Proof. vm_refl. Qed.
Lemma D_95b94 : D! W_95b94 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_95b98 : bv 32 := 0x00d60633.
Lemma F_95b98 : F! 0x95b98 W_95b98.
Proof. vm_refl. Qed.
Lemma D_95b98 : D! W_95b98 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_95b9c : bv 32 := 0x000205b7.
Lemma F_95b9c : F! 0x95b9c W_95b9c.
Proof. vm_refl. Qed.
Lemma D_95b9c : D! W_95b9c (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_95ba0 : bv 32 := 0x00a60633.
Lemma F_95ba0 : F! 0x95ba0 W_95ba0.
Proof. vm_refl. Qed.
Lemma D_95ba0 : D! W_95ba0 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_95ba4 : bv 32 := 0x0d15869b.
Lemma F_95ba4 : F! 0x95ba4 W_95ba4.
Proof. vm_refl. Qed.
Lemma D_95ba4 : D! W_95ba4 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_95ba8 : bv 32 := 0x0df60593.
Lemma F_95ba8 : F! 0x95ba8 W_95ba8.
Proof. vm_refl. Qed.
Lemma D_95ba8 : D! W_95ba8 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_95bac : bv 32 := 0xff85f593.
Lemma F_95bac : F! 0x95bac W_95bac.
Proof. vm_refl. Qed.
Lemma D_95bac : D! W_95bac (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_95bb0 : bv 32 := 0x00b4bc23.
Lemma F_95bb0 : F! 0x95bb0 W_95bb0.
Proof. vm_refl. Qed.
Lemma D_95bb0 : D! W_95bb0 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_95bb4 : bv 32 := 0x02a4b023.
Lemma F_95bb4 : F! 0x95bb4 W_95bb4.
Proof. vm_refl. Qed.
Lemma D_95bb4 : D! W_95bb4 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_95bb8 : bv 32 := 0x02d5ea63.
Lemma F_95bb8 : F! 0x95bb8 W_95bb8.
Proof. vm_refl. Qed.
Lemma D_95bb8 : D! W_95bb8 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_95bec : bv 32 := 0x0002f697.
Lemma F_95bec : F! 0x95bec W_95bec.
Proof. vm_refl. Qed.
Lemma D_95bec : D! W_95bec (Auipc 13 47).
Proof. vm_refl. Qed.
Definition W_95bf0 : bv 32 := 0x0104b983.
Lemma F_95bf0 : F! 0x95bf0 W_95bf0.
Proof. vm_refl. Qed.
Lemma D_95bf0 : D! W_95bf0 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_95bf4 : bv 32 := 0x0284b603.
Lemma F_95bf4 : F! 0x95bf4 W_95bf4.
Proof. vm_refl. Qed.
Lemma D_95bf4 : D! W_95bf4 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_95bf8 : bv 32 := 0xfff50713.
Lemma F_95bf8 : F! 0x95bf8 W_95bf8.
Proof. vm_refl. Qed.
Lemma D_95bf8 : D! W_95bf8 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_95bfc : bv 32 := 0xf3800793.
Lemma F_95bfc : F! 0x95bfc W_95bfc.
Proof. vm_refl. Qed.
Lemma D_95bfc : D! W_95bfc (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_95c00 : bv 32 := 0xc6468513.
Lemma F_95c00 : F! 0x95c00 W_95c00.
Proof. vm_refl. Qed.
Lemma D_95c00 : D! W_95c00 (OpImm ALU_ADD 10 13 3172).
Proof. vm_refl. Qed.
Definition W_95c04 : bv 32 := 0x40a787b3.
Lemma F_95c04 : F! 0x95c04 W_95c04.
Proof. vm_refl. Qed.
Lemma D_95c04 : D! W_95c04 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_95c08 : bv 32 := 0x00f77733.
Lemma F_95c08 : F! 0x95c08 W_95c08.
Proof. vm_refl. Qed.
Lemma D_95c08 : D! W_95c08 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_95c0c : bv 32 := 0xfff64693.
Lemma F_95c0c : F! 0x95c0c W_95c0c.
Proof. vm_refl. Qed.
Lemma D_95c0c : D! W_95c0c (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_95c10 : bv 32 := 0x00e50933.
Lemma F_95c10 : F! 0x95c10 W_95c10.
Proof. vm_refl. Qed.
Lemma D_95c10 : D! W_95c10 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_95c14 : bv 32 := 0x00369693.
Lemma F_95c14 : F! 0x95c14 W_95c14.
Proof. vm_refl. Qed.
Lemma D_95c14 : D! W_95c14 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_95c18 : bv 32 := 0x00d506b3.
Lemma F_95c18 : F! 0x95c18 W_95c18.
Proof. vm_refl. Qed.
Lemma D_95c18 : D! W_95c18 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_95c1c : bv 32 := 0x00b68a33.
Lemma F_95c1c : F! 0x95c1c W_95c1c.
Proof. vm_refl. Qed.
Lemma D_95c1c : D! W_95c1c (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_95c20 : bv 32 := 0x0c890413.
Lemma F_95c20 : F! 0x95c20 W_95c20.
Proof. vm_refl. Qed.
Lemma D_95c20 : D! W_95c20 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_95c24 : bv 32 := 0x04098463.
Lemma F_95c24 : F! 0x95c24 W_95c24.
Proof. vm_refl. Qed.
Lemma D_95c24 : D! W_95c24 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_95c6c : bv 32 := 0x00ca3023.
Lemma F_95c6c : F! 0x95c6c W_95c6c.
Proof. vm_refl. Qed.
Lemma D_95c6c : D! W_95c6c (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_95c70 : bv 32 := 0x0d493023.
Lemma F_95c70 : F! 0x95c70 W_95c70.
Proof. vm_refl. Qed.
Lemma D_95c70 : D! W_95c70 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_95c74 : bv 32 := 0x01293023.
Lemma F_95c74 : F! 0x95c74 W_95c74.
Proof. vm_refl. Qed.
Lemma D_95c74 : D! W_95c74 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_95c78 : bv 32 := 0x00040513.
Lemma F_95c78 : F! 0x95c78 W_95c78.
Proof. vm_refl. Qed.
Lemma D_95c78 : D! W_95c78 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_95c7c : bv 32 := 0x0d4130ef.
Lemma F_95c7c : F! 0x95c7c W_95c7c.
Proof. vm_refl. Qed.
Lemma D_95c7c : D! W_95c7c (Jal 1 78036).
Proof. vm_refl. Qed.
Definition W_95c80 : bv 32 := 0x04054a63.
Lemma F_95c80 : F! 0x95c80 W_95c80.
Proof. vm_refl. Qed.
Lemma D_95c80 : D! W_95c80 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_95c84 : bv 32 := 0x00051663.
Lemma F_95c84 : F! 0x95c84 W_95c84.
Proof. vm_refl. Qed.
Lemma D_95c84 : D! W_95c84 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_95c88 : bv 32 := 0x00100513.
Lemma F_95c88 : F! 0x95c88 W_95c88.
Proof. vm_refl. Qed.
Lemma D_95c88 : D! W_95c88 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_95c8c : bv 32 := 0x00a48023.
Lemma F_95c8c : F! 0x95c8c W_95c8c.
Proof. vm_refl. Qed.
Lemma D_95c8c : D! W_95c8c (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_95c90 : bv 32 := 0x00200513.
Lemma F_95c90 : F! 0x95c90 W_95c90.
Proof. vm_refl. Qed.
Lemma D_95c90 : D! W_95c90 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_95c94 : bv 32 := 0x0004f597.
Lemma F_95c94 : F! 0x95c94 W_95c94.
Proof. vm_refl. Qed.
Lemma D_95c94 : D! W_95c94 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_95c98 : bv 32 := 0x02a92423.
Lemma F_95c98 : F! 0x95c98 W_95c98.
Proof. vm_refl. Qed.
Lemma D_95c98 : D! W_95c98 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_95c9c : bv 32 := 0x06000893.
Lemma F_95c9c : F! 0x95c9c W_95c9c.
Proof. vm_refl. Qed.
Lemma D_95c9c : D! W_95c9c (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_95ca0 : bv 32 := 0xc8c58513.
Lemma F_95ca0 : F! 0x95ca0 W_95ca0.
Proof. vm_refl. Qed.
Lemma D_95ca0 : D! W_95ca0 (OpImm ALU_ADD 10 11 3212).
Proof. vm_refl. Qed.
Definition W_95ca4 : bv 32 := 0x03848593.
Lemma F_95ca4 : F! 0x95ca4 W_95ca4.
Proof. vm_refl. Qed.
Lemma D_95ca4 : D! W_95ca4 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_95ca8 : bv 32 := 0x00000073.
Lemma F_95ca8 : F! 0x95ca8 W_95ca8.
Proof. vm_refl. Qed.
Lemma E_95ca8 : is_ecall W_95ca8 = true.
Proof. reflexivity. Qed.
Definition W_95cac : bv 32 := 0x07890613.
Lemma F_95cac : F! 0x95cac W_95cac.
Proof. vm_refl. Qed.
Lemma D_95cac : D! W_95cac (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_95cb0 : bv 32 := 0x02a92023.
Lemma F_95cb0 : F! 0x95cb0 W_95cb0.
Proof. vm_refl. Qed.
Lemma D_95cb0 : D! W_95cb0 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_95cb4 : bv 32 := 0x08b93c23.
Lemma F_95cb4 : F! 0x95cb4 W_95cb4.
Proof. vm_refl. Qed.
Lemma D_95cb4 : D! W_95cb4 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_95cb8 : bv 32 := 0x06c93c23.
Lemma F_95cb8 : F! 0x95cb8 W_95cb8.
Proof. vm_refl. Qed.
Lemma D_95cb8 : D! W_95cb8 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_95cbc : bv 32 := 0x0004f517.
Lemma F_95cbc : F! 0x95cbc W_95cbc.
Proof. vm_refl. Qed.
Lemma D_95cbc : D! W_95cbc (Auipc 10 79).
Proof. vm_refl. Qed.
Definition W_95cc0 : bv 32 := 0xed453503.
Lemma F_95cc0 : F! 0x95cc0 W_95cc0.
Proof. vm_refl. Qed.
Lemma D_95cc0 : D! W_95cc0 (Load SZ8 true 10 10 3796).
Proof. vm_refl. Qed.
Definition W_95cc4 : bv 32 := 0x01293423.
Lemma F_95cc4 : F! 0x95cc4 W_95cc4.
Proof. vm_refl. Qed.
Lemma D_95cc4 : D! W_95cc4 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_95cc8 : bv 32 := 0x01293823.
Lemma F_95cc8 : F! 0x95cc8 W_95cc8.
Proof. vm_refl. Qed.
Lemma D_95cc8 : D! W_95cc8 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_95ccc : bv 32 := 0x00a93c23.
Lemma F_95ccc : F! 0x95ccc W_95ccc.
Proof. vm_refl. Qed.
Lemma D_95ccc : D! W_95ccc (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_95cd0 : bv 32 := 0x0080006f.
Lemma F_95cd0 : F! 0x95cd0 W_95cd0.
Proof. vm_refl. Qed.
Lemma D_95cd0 : D! W_95cd0 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_95cd8 : bv 32 := 0x03813083.
Lemma F_95cd8 : F! 0x95cd8 W_95cd8.
Proof. vm_refl. Qed.
Lemma D_95cd8 : D! W_95cd8 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_95cdc : bv 32 := 0x03013403.
Lemma F_95cdc : F! 0x95cdc W_95cdc.
Proof. vm_refl. Qed.
Lemma D_95cdc : D! W_95cdc (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_95ce0 : bv 32 := 0x02813483.
Lemma F_95ce0 : F! 0x95ce0 W_95ce0.
Proof. vm_refl. Qed.
Lemma D_95ce0 : D! W_95ce0 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_95ce4 : bv 32 := 0x02013903.
Lemma F_95ce4 : F! 0x95ce4 W_95ce4.
Proof. vm_refl. Qed.
Lemma D_95ce4 : D! W_95ce4 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_95ce8 : bv 32 := 0x01813983.
Lemma F_95ce8 : F! 0x95ce8 W_95ce8.
Proof. vm_refl. Qed.
Lemma D_95ce8 : D! W_95ce8 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_95cec : bv 32 := 0x01013a03.
Lemma F_95cec : F! 0x95cec W_95cec.
Proof. vm_refl. Qed.
Lemma D_95cec : D! W_95cec (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_95cf0 : bv 32 := 0x00813a83.
Lemma F_95cf0 : F! 0x95cf0 W_95cf0.
Proof. vm_refl. Qed.
Lemma D_95cf0 : D! W_95cf0 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_95cf4 : bv 32 := 0x04010113.
Lemma F_95cf4 : F! 0x95cf4 W_95cf4.
Proof. vm_refl. Qed.
Lemma D_95cf4 : D! W_95cf4 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_95cf8 : bv 32 := 0x00008067.
Lemma F_95cf8 : F! 0x95cf8 W_95cf8.
Proof. vm_refl. Qed.
Lemma D_95cf8 : D! W_95cf8 (Jalr 0 1 0).
Proof. vm_refl. Qed.
