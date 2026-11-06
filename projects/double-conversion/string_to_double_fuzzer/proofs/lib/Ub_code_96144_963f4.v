(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.double_conversion.string_to_double_fuzzer.images Require Import Ubsan.
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
Definition W_96144 : bv 32 := 0xfc010113.
Lemma F_96144 : F! 0x96144 W_96144.
Proof. vm_refl. Qed.
Lemma D_96144 : D! W_96144 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_96148 : bv 32 := 0x02113c23.
Lemma F_96148 : F! 0x96148 W_96148.
Proof. vm_refl. Qed.
Lemma D_96148 : D! W_96148 (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_9614c : bv 32 := 0x02813823.
Lemma F_9614c : F! 0x9614c W_9614c.
Proof. vm_refl. Qed.
Lemma D_9614c : D! W_9614c (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_96150 : bv 32 := 0x02913423.
Lemma F_96150 : F! 0x96150 W_96150.
Proof. vm_refl. Qed.
Lemma D_96150 : D! W_96150 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_96154 : bv 32 := 0x03213023.
Lemma F_96154 : F! 0x96154 W_96154.
Proof. vm_refl. Qed.
Lemma D_96154 : D! W_96154 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_96158 : bv 32 := 0x01313c23.
Lemma F_96158 : F! 0x96158 W_96158.
Proof. vm_refl. Qed.
Lemma D_96158 : D! W_96158 (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_9615c : bv 32 := 0x01413823.
Lemma F_9615c : F! 0x9615c W_9615c.
Proof. vm_refl. Qed.
Lemma D_9615c : D! W_9615c (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_96160 : bv 32 := 0x01513423.
Lemma F_96160 : F! 0x96160 W_96160.
Proof. vm_refl. Qed.
Lemma D_96160 : D! W_96160 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_96164 : bv 32 := 0x02853683.
Lemma F_96164 : F! 0x96164 W_96164.
Proof. vm_refl. Qed.
Lemma D_96164 : D! W_96164 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_96168 : bv 32 := 0x0004f597.
Lemma F_96168 : F! 0x96168 W_96168.
Proof. vm_refl. Qed.
Lemma D_96168 : D! W_96168 (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_9616c : bv 32 := 0xeb858593.
Lemma F_9616c : F! 0x9616c W_9616c.
Proof. vm_refl. Qed.
Lemma D_9616c : D! W_9616c (OpImm ALU_ADD 11 11 3768).
Proof. vm_refl. Qed.
Definition W_96170 : bv 32 := 0x0004f617.
Lemma F_96170 : F! 0x96170 W_96170.
Proof. vm_refl. Qed.
Lemma D_96170 : D! W_96170 (Auipc 12 79).
Proof. vm_refl. Qed.
Definition W_96174 : bv 32 := 0x13860493.
Lemma F_96174 : F! 0x96174 W_96174.
Proof. vm_refl. Qed.
Lemma D_96174 : D! W_96174 (OpImm ALU_ADD 9 12 312).
Proof. vm_refl. Qed.
Definition W_96178 : bv 32 := 0x0c068e63.
Lemma F_96178 : F! 0x96178 W_96178.
Proof. vm_refl. Qed.
Lemma D_96178 : D! W_96178 (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_9617c : bv 32 := 0x00000613.
Lemma F_9617c : F! 0x9617c W_9617c.
Proof. vm_refl. Qed.
Lemma D_9617c : D! W_9617c (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_96180 : bv 32 := 0x00000893.
Lemma F_96180 : F! 0x96180 W_96180.
Proof. vm_refl. Qed.
Lemma D_96180 : D! W_96180 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_96184 : bv 32 := 0x0001d717.
Lemma F_96184 : F! 0x96184 W_96184.
Proof. vm_refl. Qed.
Lemma D_96184 : D! W_96184 (Auipc 14 29).
Proof. vm_refl. Qed.
Definition W_96188 : bv 32 := 0x01853783.
Lemma F_96188 : F! 0x96188 W_96188.
Proof. vm_refl. Qed.
Lemma D_96188 : D! W_96188 (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_9618c : bv 32 := 0x02053503.
Lemma F_9618c : F! 0x9618c W_9618c.
Proof. vm_refl. Qed.
Lemma D_9618c : D! W_9618c (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_96190 : bv 32 := 0x00600813.
Lemma F_96190 : F! 0x96190 W_96190.
Proof. vm_refl. Qed.
Lemma D_96190 : D! W_96190 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_96194 : bv 32 := 0x0001c297.
Lemma F_96194 : F! 0x96194 W_96194.
Proof. vm_refl. Qed.
Lemma D_96194 : D! W_96194 (Auipc 5 28).
Proof. vm_refl. Qed.
Definition W_96198 : bv 32 := 0x3f476f03.
Lemma F_96198 : F! 0x96198 W_96198.
Proof. vm_refl. Qed.
Lemma D_96198 : D! W_96198 (Load SZ4 false 30 14 1012).
Proof. vm_refl. Qed.
Definition W_9619c : bv 32 := 0xfac2b283.
Lemma F_9619c : F! 0x9619c W_9619c.
Proof. vm_refl. Qed.
Lemma D_9619c : D! W_9619c (Load SZ8 true 5 5 4012).
Proof. vm_refl. Qed.
Definition W_961a0 : bv 32 := 0x00200313.
Lemma F_961a0 : F! 0x961a0 W_961a0.
Proof. vm_refl. Qed.
Lemma D_961a0 : D! W_961a0 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_961a4 : bv 32 := 0x00700393.
Lemma F_961a4 : F! 0x961a4 W_961a4.
Proof. vm_refl. Qed.
Lemma D_961a4 : D! W_961a4 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_961a8 : bv 32 := 0x6474ee37.
Lemma F_961a8 : F! 0x961a8 W_961a8.
Proof. vm_refl. Qed.
Lemma D_961a8 : D! W_961a8 (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_961ac : bv 32 := 0x551e0e1b.
Lemma F_961ac : F! 0x961ac W_961ac.
Proof. vm_refl. Qed.
Lemma D_961ac : D! W_961ac (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_961b0 : bv 32 := 0x00078e93.
Lemma F_961b0 : F! 0x961b0 W_961b0.
Proof. vm_refl. Qed.
Lemma D_961b0 : D! W_961b0 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_961b4 : bv 32 := 0x0180006f.
Lemma F_961b4 : F! 0x961b4 W_961b4.
Proof. vm_refl. Qed.
Lemma D_961b4 : D! W_961b4 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_961b8 : bv 32 := 0x010eb603.
Lemma F_961b8 : F! 0x961b8 W_961b8.
Proof. vm_refl. Qed.
Lemma D_961b8 : D! W_961b8 (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_961bc : bv 32 := 0x40c78633.
Lemma F_961bc : F! 0x961bc W_961bc.
Proof. vm_refl. Qed.
Lemma D_961bc : D! W_961bc (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_961c0 : bv 32 := 0xfff68693.
Lemma F_961c0 : F! 0x961c0 W_961c0.
Proof. vm_refl. Qed.
Lemma D_961c0 : D! W_961c0 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_961c4 : bv 32 := 0x00ae8eb3.
Lemma F_961c4 : F! 0x961c4 W_961c4.
Proof. vm_refl. Qed.
Lemma D_961c4 : D! W_961c4 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_961c8 : bv 32 := 0x04068a63.
Lemma F_961c8 : F! 0x961c8 W_961c8.
Proof. vm_refl. Qed.
Lemma D_961c8 : D! W_961c8 (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_961cc : bv 32 := 0x000ea403.
Lemma F_961cc : F! 0x961cc W_961cc.
Proof. vm_refl. Qed.
Lemma D_961cc : D! W_961cc (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_961d0 : bv 32 := 0xff0404e3.
Lemma F_961d0 : F! 0x961d0 W_961d0.
Proof. vm_refl. Qed.
Lemma D_961d0 : D! W_961d0 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_961d4 : bv 32 := 0x00028a63.
Lemma F_961d4 : F! 0x961d4 W_961d4.
Proof. vm_refl. Qed.
Lemma D_961d4 : D! W_961d4 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_961e8 : bv 32 := 0x000e8f93.
Lemma F_961e8 : F! 0x961e8 W_961e8.
Proof. vm_refl. Qed.
Lemma D_961e8 : D! W_961e8 (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_961ec : bv 32 := 0x00740463.
Lemma F_961ec : F! 0x961ec W_961ec.
Proof. vm_refl. Qed.
Lemma D_961ec : D! W_961ec (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_961f0 : bv 32 := 0x00088f93.
Lemma F_961f0 : F! 0x961f0 W_961f0.
Proof. vm_refl. Qed.
Lemma D_961f0 : D! W_961f0 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_961f4 : bv 32 := 0x03c41063.
Lemma F_961f4 : F! 0x961f4 W_961f4.
Proof. vm_refl. Qed.
Lemma D_961f4 : D! W_961f4 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_961f8 : bv 32 := 0x028eb883.
Lemma F_961f8 : F! 0x961f8 W_961f8.
Proof. vm_refl. Qed.
Lemma D_961f8 : D! W_961f8 (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_961fc : bv 32 := 0x011f7c63.
Lemma F_961fc : F! 0x961fc W_961fc.
Proof. vm_refl. Qed.
Lemma D_961fc : D! W_961fc (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_96214 : bv 32 := 0x000f8893.
Lemma F_96214 : F! 0x96214 W_96214.
Proof. vm_refl. Qed.
Lemma D_96214 : D! W_96214 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_96218 : bv 32 := 0xfa9ff06f.
Lemma F_96218 : F! 0x96218 W_96218.
Proof. vm_refl. Qed.
Lemma D_96218 : D! W_96218 (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_9621c : bv 32 := 0x02088c63.
Lemma F_9621c : F! 0x9621c W_9621c.
Proof. vm_refl. Qed.
Lemma D_9621c : D! W_9621c (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_96254 : bv 32 := 0x0105b603.
Lemma F_96254 : F! 0x96254 W_96254.
Proof. vm_refl. Qed.
Lemma D_96254 : D! W_96254 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_96258 : bv 32 := 0x0205b683.
Lemma F_96258 : F! 0x96258 W_96258.
Proof. vm_refl. Qed.
Lemma D_96258 : D! W_96258 (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_9625c : bv 32 := 0x0285b503.
Lemma F_9625c : F! 0x9625c W_9625c.
Proof. vm_refl. Qed.
Lemma D_9625c : D! W_9625c (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_96260 : bv 32 := 0x00c68733.
Lemma F_96260 : F! 0x96260 W_96260.
Proof. vm_refl. Qed.
Lemma D_96260 : D! W_96260 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_96264 : bv 32 := 0xfff50793.
Lemma F_96264 : F! 0x96264 W_96264.
Proof. vm_refl. Qed.
Lemma D_96264 : D! W_96264 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_96268 : bv 32 := 0x40e00733.
Lemma F_96268 : F! 0x96268 W_96268.
Proof. vm_refl. Qed.
Lemma D_96268 : D! W_96268 (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_9626c : bv 32 := 0x00c7f633.
Lemma F_9626c : F! 0x9626c W_9626c.
Proof. vm_refl. Qed.
Lemma D_9626c : D! W_9626c (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_96270 : bv 32 := 0x00e7f733.
Lemma F_96270 : F! 0x96270 W_96270.
Proof. vm_refl. Qed.
Lemma D_96270 : D! W_96270 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_96274 : bv 32 := 0x00700793.
Lemma F_96274 : F! 0x96274 W_96274.
Proof. vm_refl. Qed.
Lemma D_96274 : D! W_96274 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_96278 : bv 32 := 0x00d706b3.
Lemma F_96278 : F! 0x96278 W_96278.
Proof. vm_refl. Qed.
Lemma D_96278 : D! W_96278 (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_9627c : bv 32 := 0x02d5b023.
Lemma F_9627c : F! 0x9627c W_9627c.
Proof. vm_refl. Qed.
Lemma D_9627c : D! W_9627c (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_96280 : bv 32 := 0x02c5b823.
Lemma F_96280 : F! 0x96280 W_96280.
Proof. vm_refl. Qed.
Lemma D_96280 : D! W_96280 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_96284 : bv 32 := 0x00a7e663.
Lemma F_96284 : F! 0x96284 W_96284.
Proof. vm_refl. Qed.
Lemma D_96284 : D! W_96284 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_96288 : bv 32 := 0x00800513.
Lemma F_96288 : F! 0x96288 W_96288.
Proof. vm_refl. Qed.
Lemma D_96288 : D! W_96288 (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_9628c : bv 32 := 0x02a5b423.
Lemma F_9628c : F! 0x9628c W_9628c.
Proof. vm_refl. Qed.
Lemma D_9628c : D! W_9628c (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_96290 : bv 32 := 0x00d60633.
Lemma F_96290 : F! 0x96290 W_96290.
Proof. vm_refl. Qed.
Lemma D_96290 : D! W_96290 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_96294 : bv 32 := 0x000205b7.
Lemma F_96294 : F! 0x96294 W_96294.
Proof. vm_refl. Qed.
Lemma D_96294 : D! W_96294 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_96298 : bv 32 := 0x00a60633.
Lemma F_96298 : F! 0x96298 W_96298.
Proof. vm_refl. Qed.
Lemma D_96298 : D! W_96298 (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_9629c : bv 32 := 0x0d15869b.
Lemma F_9629c : F! 0x9629c W_9629c.
Proof. vm_refl. Qed.
Lemma D_9629c : D! W_9629c (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_962a0 : bv 32 := 0x0df60593.
Lemma F_962a0 : F! 0x962a0 W_962a0.
Proof. vm_refl. Qed.
Lemma D_962a0 : D! W_962a0 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_962a4 : bv 32 := 0xff85f593.
Lemma F_962a4 : F! 0x962a4 W_962a4.
Proof. vm_refl. Qed.
Lemma D_962a4 : D! W_962a4 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_962a8 : bv 32 := 0x00b4bc23.
Lemma F_962a8 : F! 0x962a8 W_962a8.
Proof. vm_refl. Qed.
Lemma D_962a8 : D! W_962a8 (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_962ac : bv 32 := 0x02a4b023.
Lemma F_962ac : F! 0x962ac W_962ac.
Proof. vm_refl. Qed.
Lemma D_962ac : D! W_962ac (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_962b0 : bv 32 := 0x02d5ea63.
Lemma F_962b0 : F! 0x962b0 W_962b0.
Proof. vm_refl. Qed.
Lemma D_962b0 : D! W_962b0 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_962e4 : bv 32 := 0x0002f697.
Lemma F_962e4 : F! 0x962e4 W_962e4.
Proof. vm_refl. Qed.
Lemma D_962e4 : D! W_962e4 (Auipc 13 47).
Proof. vm_refl. Qed.
Definition W_962e8 : bv 32 := 0x0104b983.
Lemma F_962e8 : F! 0x962e8 W_962e8.
Proof. vm_refl. Qed.
Lemma D_962e8 : D! W_962e8 (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_962ec : bv 32 := 0x0284b603.
Lemma F_962ec : F! 0x962ec W_962ec.
Proof. vm_refl. Qed.
Lemma D_962ec : D! W_962ec (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_962f0 : bv 32 := 0xfff50713.
Lemma F_962f0 : F! 0x962f0 W_962f0.
Proof. vm_refl. Qed.
Lemma D_962f0 : D! W_962f0 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_962f4 : bv 32 := 0xf3800793.
Lemma F_962f4 : F! 0x962f4 W_962f4.
Proof. vm_refl. Qed.
Lemma D_962f4 : D! W_962f4 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_962f8 : bv 32 := 0xc6c68513.
Lemma F_962f8 : F! 0x962f8 W_962f8.
Proof. vm_refl. Qed.
Lemma D_962f8 : D! W_962f8 (OpImm ALU_ADD 10 13 3180).
Proof. vm_refl. Qed.
Definition W_962fc : bv 32 := 0x40a787b3.
Lemma F_962fc : F! 0x962fc W_962fc.
Proof. vm_refl. Qed.
Lemma D_962fc : D! W_962fc (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_96300 : bv 32 := 0x00f77733.
Lemma F_96300 : F! 0x96300 W_96300.
Proof. vm_refl. Qed.
Lemma D_96300 : D! W_96300 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_96304 : bv 32 := 0xfff64693.
Lemma F_96304 : F! 0x96304 W_96304.
Proof. vm_refl. Qed.
Lemma D_96304 : D! W_96304 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_96308 : bv 32 := 0x00e50933.
Lemma F_96308 : F! 0x96308 W_96308.
Proof. vm_refl. Qed.
Lemma D_96308 : D! W_96308 (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_9630c : bv 32 := 0x00369693.
Lemma F_9630c : F! 0x9630c W_9630c.
Proof. vm_refl. Qed.
Lemma D_9630c : D! W_9630c (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_96310 : bv 32 := 0x00d506b3.
Lemma F_96310 : F! 0x96310 W_96310.
Proof. vm_refl. Qed.
Lemma D_96310 : D! W_96310 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_96314 : bv 32 := 0x00b68a33.
Lemma F_96314 : F! 0x96314 W_96314.
Proof. vm_refl. Qed.
Lemma D_96314 : D! W_96314 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_96318 : bv 32 := 0x0c890413.
Lemma F_96318 : F! 0x96318 W_96318.
Proof. vm_refl. Qed.
Lemma D_96318 : D! W_96318 (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_9631c : bv 32 := 0x04098463.
Lemma F_9631c : F! 0x9631c W_9631c.
Proof. vm_refl. Qed.
Lemma D_9631c : D! W_9631c (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_96364 : bv 32 := 0x00ca3023.
Lemma F_96364 : F! 0x96364 W_96364.
Proof. vm_refl. Qed.
Lemma D_96364 : D! W_96364 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_96368 : bv 32 := 0x0d493023.
Lemma F_96368 : F! 0x96368 W_96368.
Proof. vm_refl. Qed.
Lemma D_96368 : D! W_96368 (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_9636c : bv 32 := 0x01293023.
Lemma F_9636c : F! 0x9636c W_9636c.
Proof. vm_refl. Qed.
Lemma D_9636c : D! W_9636c (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_96370 : bv 32 := 0x00040513.
Lemma F_96370 : F! 0x96370 W_96370.
Proof. vm_refl. Qed.
Lemma D_96370 : D! W_96370 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_96374 : bv 32 := 0x0d4130ef.
Lemma F_96374 : F! 0x96374 W_96374.
Proof. vm_refl. Qed.
Lemma D_96374 : D! W_96374 (Jal 1 78036).
Proof. vm_refl. Qed.
Definition W_96378 : bv 32 := 0x04054a63.
Lemma F_96378 : F! 0x96378 W_96378.
Proof. vm_refl. Qed.
Lemma D_96378 : D! W_96378 (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_9637c : bv 32 := 0x00051663.
Lemma F_9637c : F! 0x9637c W_9637c.
Proof. vm_refl. Qed.
Lemma D_9637c : D! W_9637c (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_96380 : bv 32 := 0x00100513.
Lemma F_96380 : F! 0x96380 W_96380.
Proof. vm_refl. Qed.
Lemma D_96380 : D! W_96380 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_96384 : bv 32 := 0x00a48023.
Lemma F_96384 : F! 0x96384 W_96384.
Proof. vm_refl. Qed.
Lemma D_96384 : D! W_96384 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_96388 : bv 32 := 0x00200513.
Lemma F_96388 : F! 0x96388 W_96388.
Proof. vm_refl. Qed.
Lemma D_96388 : D! W_96388 (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_9638c : bv 32 := 0x0004f597.
Lemma F_9638c : F! 0x9638c W_9638c.
Proof. vm_refl. Qed.
Lemma D_9638c : D! W_9638c (Auipc 11 79).
Proof. vm_refl. Qed.
Definition W_96390 : bv 32 := 0x02a92423.
Lemma F_96390 : F! 0x96390 W_96390.
Proof. vm_refl. Qed.
Lemma D_96390 : D! W_96390 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_96394 : bv 32 := 0x06000893.
Lemma F_96394 : F! 0x96394 W_96394.
Proof. vm_refl. Qed.
Lemma D_96394 : D! W_96394 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_96398 : bv 32 := 0xc9458513.
Lemma F_96398 : F! 0x96398 W_96398.
Proof. vm_refl. Qed.
Lemma D_96398 : D! W_96398 (OpImm ALU_ADD 10 11 3220).
Proof. vm_refl. Qed.
Definition W_9639c : bv 32 := 0x03848593.
Lemma F_9639c : F! 0x9639c W_9639c.
Proof. vm_refl. Qed.
Lemma D_9639c : D! W_9639c (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_963a0 : bv 32 := 0x00000073.
Lemma F_963a0 : F! 0x963a0 W_963a0.
Proof. vm_refl. Qed.
Lemma E_963a0 : is_ecall W_963a0 = true.
Proof. reflexivity. Qed.
Definition W_963a4 : bv 32 := 0x07890613.
Lemma F_963a4 : F! 0x963a4 W_963a4.
Proof. vm_refl. Qed.
Lemma D_963a4 : D! W_963a4 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_963a8 : bv 32 := 0x02a92023.
Lemma F_963a8 : F! 0x963a8 W_963a8.
Proof. vm_refl. Qed.
Lemma D_963a8 : D! W_963a8 (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_963ac : bv 32 := 0x08b93c23.
Lemma F_963ac : F! 0x963ac W_963ac.
Proof. vm_refl. Qed.
Lemma D_963ac : D! W_963ac (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_963b0 : bv 32 := 0x06c93c23.
Lemma F_963b0 : F! 0x963b0 W_963b0.
Proof. vm_refl. Qed.
Lemma D_963b0 : D! W_963b0 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_963b4 : bv 32 := 0x0004f517.
Lemma F_963b4 : F! 0x963b4 W_963b4.
Proof. vm_refl. Qed.
Lemma D_963b4 : D! W_963b4 (Auipc 10 79).
Proof. vm_refl. Qed.
Definition W_963b8 : bv 32 := 0xedc53503.
Lemma F_963b8 : F! 0x963b8 W_963b8.
Proof. vm_refl. Qed.
Lemma D_963b8 : D! W_963b8 (Load SZ8 true 10 10 3804).
Proof. vm_refl. Qed.
Definition W_963bc : bv 32 := 0x01293423.
Lemma F_963bc : F! 0x963bc W_963bc.
Proof. vm_refl. Qed.
Lemma D_963bc : D! W_963bc (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_963c0 : bv 32 := 0x01293823.
Lemma F_963c0 : F! 0x963c0 W_963c0.
Proof. vm_refl. Qed.
Lemma D_963c0 : D! W_963c0 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_963c4 : bv 32 := 0x00a93c23.
Lemma F_963c4 : F! 0x963c4 W_963c4.
Proof. vm_refl. Qed.
Lemma D_963c4 : D! W_963c4 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_963c8 : bv 32 := 0x0080006f.
Lemma F_963c8 : F! 0x963c8 W_963c8.
Proof. vm_refl. Qed.
Lemma D_963c8 : D! W_963c8 (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_963d0 : bv 32 := 0x03813083.
Lemma F_963d0 : F! 0x963d0 W_963d0.
Proof. vm_refl. Qed.
Lemma D_963d0 : D! W_963d0 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_963d4 : bv 32 := 0x03013403.
Lemma F_963d4 : F! 0x963d4 W_963d4.
Proof. vm_refl. Qed.
Lemma D_963d4 : D! W_963d4 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_963d8 : bv 32 := 0x02813483.
Lemma F_963d8 : F! 0x963d8 W_963d8.
Proof. vm_refl. Qed.
Lemma D_963d8 : D! W_963d8 (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_963dc : bv 32 := 0x02013903.
Lemma F_963dc : F! 0x963dc W_963dc.
Proof. vm_refl. Qed.
Lemma D_963dc : D! W_963dc (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_963e0 : bv 32 := 0x01813983.
Lemma F_963e0 : F! 0x963e0 W_963e0.
Proof. vm_refl. Qed.
Lemma D_963e0 : D! W_963e0 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_963e4 : bv 32 := 0x01013a03.
Lemma F_963e4 : F! 0x963e4 W_963e4.
Proof. vm_refl. Qed.
Lemma D_963e4 : D! W_963e4 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_963e8 : bv 32 := 0x00813a83.
Lemma F_963e8 : F! 0x963e8 W_963e8.
Proof. vm_refl. Qed.
Lemma D_963e8 : D! W_963e8 (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_963ec : bv 32 := 0x04010113.
Lemma F_963ec : F! 0x963ec W_963ec.
Proof. vm_refl. Qed.
Lemma D_963ec : D! W_963ec (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_963f0 : bv 32 := 0x00008067.
Lemma F_963f0 : F! 0x963f0 W_963f0.
Proof. vm_refl. Qed.
Lemma D_963f0 : D! W_963f0 (Jalr 0 1 0).
Proof. vm_refl. Qed.
