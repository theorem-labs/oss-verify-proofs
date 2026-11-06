(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
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
Definition W_508a8 : bv 32 := 0xfc010113.
Lemma F_508a8 : F! 0x508a8 W_508a8.
Proof. vm_refl. Qed.
Lemma D_508a8 : D! W_508a8 (OpImm ALU_ADD 2 2 4032).
Proof. vm_refl. Qed.
Definition W_508ac : bv 32 := 0x02113c23.
Lemma F_508ac : F! 0x508ac W_508ac.
Proof. vm_refl. Qed.
Lemma D_508ac : D! W_508ac (Store SZ8 2 1 56).
Proof. vm_refl. Qed.
Definition W_508b0 : bv 32 := 0x02813823.
Lemma F_508b0 : F! 0x508b0 W_508b0.
Proof. vm_refl. Qed.
Lemma D_508b0 : D! W_508b0 (Store SZ8 2 8 48).
Proof. vm_refl. Qed.
Definition W_508b4 : bv 32 := 0x02913423.
Lemma F_508b4 : F! 0x508b4 W_508b4.
Proof. vm_refl. Qed.
Lemma D_508b4 : D! W_508b4 (Store SZ8 2 9 40).
Proof. vm_refl. Qed.
Definition W_508b8 : bv 32 := 0x03213023.
Lemma F_508b8 : F! 0x508b8 W_508b8.
Proof. vm_refl. Qed.
Lemma D_508b8 : D! W_508b8 (Store SZ8 2 18 32).
Proof. vm_refl. Qed.
Definition W_508bc : bv 32 := 0x01313c23.
Lemma F_508bc : F! 0x508bc W_508bc.
Proof. vm_refl. Qed.
Lemma D_508bc : D! W_508bc (Store SZ8 2 19 24).
Proof. vm_refl. Qed.
Definition W_508c0 : bv 32 := 0x01413823.
Lemma F_508c0 : F! 0x508c0 W_508c0.
Proof. vm_refl. Qed.
Lemma D_508c0 : D! W_508c0 (Store SZ8 2 20 16).
Proof. vm_refl. Qed.
Definition W_508c4 : bv 32 := 0x01513423.
Lemma F_508c4 : F! 0x508c4 W_508c4.
Proof. vm_refl. Qed.
Lemma D_508c4 : D! W_508c4 (Store SZ8 2 21 8).
Proof. vm_refl. Qed.
Definition W_508c8 : bv 32 := 0x02853683.
Lemma F_508c8 : F! 0x508c8 W_508c8.
Proof. vm_refl. Qed.
Lemma D_508c8 : D! W_508c8 (Load SZ8 true 13 10 40).
Proof. vm_refl. Qed.
Definition W_508cc : bv 32 := 0x00045597.
Lemma F_508cc : F! 0x508cc W_508cc.
Proof. vm_refl. Qed.
Lemma D_508cc : D! W_508cc (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_508d0 : bv 32 := 0x30c58593.
Lemma F_508d0 : F! 0x508d0 W_508d0.
Proof. vm_refl. Qed.
Lemma D_508d0 : D! W_508d0 (OpImm ALU_ADD 11 11 780).
Proof. vm_refl. Qed.
Definition W_508d4 : bv 32 := 0x00045617.
Lemma F_508d4 : F! 0x508d4 W_508d4.
Proof. vm_refl. Qed.
Lemma D_508d4 : D! W_508d4 (Auipc 12 69).
Proof. vm_refl. Qed.
Definition W_508d8 : bv 32 := 0x58c60493.
Lemma F_508d8 : F! 0x508d8 W_508d8.
Proof. vm_refl. Qed.
Lemma D_508d8 : D! W_508d8 (OpImm ALU_ADD 9 12 1420).
Proof. vm_refl. Qed.
Definition W_508dc : bv 32 := 0x0c068e63.
Lemma F_508dc : F! 0x508dc W_508dc.
Proof. vm_refl. Qed.
Lemma D_508dc : D! W_508dc (Branch BC_EQ 13 0 220).
Proof. vm_refl. Qed.
Definition W_508e0 : bv 32 := 0x00000613.
Lemma F_508e0 : F! 0x508e0 W_508e0.
Proof. vm_refl. Qed.
Lemma D_508e0 : D! W_508e0 (OpImm ALU_ADD 12 0 0).
Proof. vm_refl. Qed.
Definition W_508e4 : bv 32 := 0x00000893.
Lemma F_508e4 : F! 0x508e4 W_508e4.
Proof. vm_refl. Qed.
Lemma D_508e4 : D! W_508e4 (OpImm ALU_ADD 17 0 0).
Proof. vm_refl. Qed.
Definition W_508e8 : bv 32 := 0x00014717.
Lemma F_508e8 : F! 0x508e8 W_508e8.
Proof. vm_refl. Qed.
Lemma D_508e8 : D! W_508e8 (Auipc 14 20).
Proof. vm_refl. Qed.
Definition W_508ec : bv 32 := 0x01853783.
Lemma F_508ec : F! 0x508ec W_508ec.
Proof. vm_refl. Qed.
Lemma D_508ec : D! W_508ec (Load SZ8 true 15 10 24).
Proof. vm_refl. Qed.
Definition W_508f0 : bv 32 := 0x02053503.
Lemma F_508f0 : F! 0x508f0 W_508f0.
Proof. vm_refl. Qed.
Lemma D_508f0 : D! W_508f0 (Load SZ8 true 10 10 32).
Proof. vm_refl. Qed.
Definition W_508f4 : bv 32 := 0x00600813.
Lemma F_508f4 : F! 0x508f4 W_508f4.
Proof. vm_refl. Qed.
Lemma D_508f4 : D! W_508f4 (OpImm ALU_ADD 16 0 6).
Proof. vm_refl. Qed.
Definition W_508f8 : bv 32 := 0x00013297.
Lemma F_508f8 : F! 0x508f8 W_508f8.
Proof. vm_refl. Qed.
Lemma D_508f8 : D! W_508f8 (Auipc 5 19).
Proof. vm_refl. Qed.
Definition W_508fc : bv 32 := 0x71876f03.
Lemma F_508fc : F! 0x508fc W_508fc.
Proof. vm_refl. Qed.
Lemma D_508fc : D! W_508fc (Load SZ4 false 30 14 1816).
Proof. vm_refl. Qed.
Definition W_50900 : bv 32 := 0x3702b283.
Lemma F_50900 : F! 0x50900 W_50900.
Proof. vm_refl. Qed.
Lemma D_50900 : D! W_50900 (Load SZ8 true 5 5 880).
Proof. vm_refl. Qed.
Definition W_50904 : bv 32 := 0x00200313.
Lemma F_50904 : F! 0x50904 W_50904.
Proof. vm_refl. Qed.
Lemma D_50904 : D! W_50904 (OpImm ALU_ADD 6 0 2).
Proof. vm_refl. Qed.
Definition W_50908 : bv 32 := 0x00700393.
Lemma F_50908 : F! 0x50908 W_50908.
Proof. vm_refl. Qed.
Lemma D_50908 : D! W_50908 (OpImm ALU_ADD 7 0 7).
Proof. vm_refl. Qed.
Definition W_5090c : bv 32 := 0x6474ee37.
Lemma F_5090c : F! 0x5090c W_5090c.
Proof. vm_refl. Qed.
Lemma D_5090c : D! W_5090c (Lui 28 411470).
Proof. vm_refl. Qed.
Definition W_50910 : bv 32 := 0x551e0e1b.
Lemma F_50910 : F! 0x50910 W_50910.
Proof. vm_refl. Qed.
Lemma D_50910 : D! W_50910 (OpImm32 28 28 1361).
Proof. vm_refl. Qed.
Definition W_50914 : bv 32 := 0x00078e93.
Lemma F_50914 : F! 0x50914 W_50914.
Proof. vm_refl. Qed.
Lemma D_50914 : D! W_50914 (OpImm ALU_ADD 29 15 0).
Proof. vm_refl. Qed.
Definition W_50918 : bv 32 := 0x0180006f.
Lemma F_50918 : F! 0x50918 W_50918.
Proof. vm_refl. Qed.
Lemma D_50918 : D! W_50918 (Jal 0 24).
Proof. vm_refl. Qed.
Definition W_5091c : bv 32 := 0x010eb603.
Lemma F_5091c : F! 0x5091c W_5091c.
Proof. vm_refl. Qed.
Lemma D_5091c : D! W_5091c (Load SZ8 true 12 29 16).
Proof. vm_refl. Qed.
Definition W_50920 : bv 32 := 0x40c78633.
Lemma F_50920 : F! 0x50920 W_50920.
Proof. vm_refl. Qed.
Lemma D_50920 : D! W_50920 (Op ALU_SUB 12 15 12).
Proof. vm_refl. Qed.
Definition W_50924 : bv 32 := 0xfff68693.
Lemma F_50924 : F! 0x50924 W_50924.
Proof. vm_refl. Qed.
Lemma D_50924 : D! W_50924 (OpImm ALU_ADD 13 13 4095).
Proof. vm_refl. Qed.
Definition W_50928 : bv 32 := 0x00ae8eb3.
Lemma F_50928 : F! 0x50928 W_50928.
Proof. vm_refl. Qed.
Lemma D_50928 : D! W_50928 (Op ALU_ADD 29 29 10).
Proof. vm_refl. Qed.
Definition W_5092c : bv 32 := 0x04068a63.
Lemma F_5092c : F! 0x5092c W_5092c.
Proof. vm_refl. Qed.
Lemma D_5092c : D! W_5092c (Branch BC_EQ 13 0 84).
Proof. vm_refl. Qed.
Definition W_50930 : bv 32 := 0x000ea403.
Lemma F_50930 : F! 0x50930 W_50930.
Proof. vm_refl. Qed.
Lemma D_50930 : D! W_50930 (Load SZ4 true 8 29 0).
Proof. vm_refl. Qed.
Definition W_50934 : bv 32 := 0xff0404e3.
Lemma F_50934 : F! 0x50934 W_50934.
Proof. vm_refl. Qed.
Lemma D_50934 : D! W_50934 (Branch BC_EQ 8 16 8168).
Proof. vm_refl. Qed.
Definition W_50938 : bv 32 := 0x00028a63.
Lemma F_50938 : F! 0x50938 W_50938.
Proof. vm_refl. Qed.
Lemma D_50938 : D! W_50938 (Branch BC_EQ 5 0 20).
Proof. vm_refl. Qed.
Definition W_5094c : bv 32 := 0x000e8f93.
Lemma F_5094c : F! 0x5094c W_5094c.
Proof. vm_refl. Qed.
Lemma D_5094c : D! W_5094c (OpImm ALU_ADD 31 29 0).
Proof. vm_refl. Qed.
Definition W_50950 : bv 32 := 0x00740463.
Lemma F_50950 : F! 0x50950 W_50950.
Proof. vm_refl. Qed.
Lemma D_50950 : D! W_50950 (Branch BC_EQ 8 7 8).
Proof. vm_refl. Qed.
Definition W_50954 : bv 32 := 0x00088f93.
Lemma F_50954 : F! 0x50954 W_50954.
Proof. vm_refl. Qed.
Lemma D_50954 : D! W_50954 (OpImm ALU_ADD 31 17 0).
Proof. vm_refl. Qed.
Definition W_50958 : bv 32 := 0x03c41063.
Lemma F_50958 : F! 0x50958 W_50958.
Proof. vm_refl. Qed.
Lemma D_50958 : D! W_50958 (Branch BC_NE 8 28 32).
Proof. vm_refl. Qed.
Definition W_5095c : bv 32 := 0x028eb883.
Lemma F_5095c : F! 0x5095c W_5095c.
Proof. vm_refl. Qed.
Lemma D_5095c : D! W_5095c (Load SZ8 true 17 29 40).
Proof. vm_refl. Qed.
Definition W_50960 : bv 32 := 0x011f7c63.
Lemma F_50960 : F! 0x50960 W_50960.
Proof. vm_refl. Qed.
Lemma D_50960 : D! W_50960 (Branch BC_GEU 30 17 24).
Proof. vm_refl. Qed.
Definition W_50978 : bv 32 := 0x000f8893.
Lemma F_50978 : F! 0x50978 W_50978.
Proof. vm_refl. Qed.
Lemma D_50978 : D! W_50978 (OpImm ALU_ADD 17 31 0).
Proof. vm_refl. Qed.
Definition W_5097c : bv 32 := 0xfa9ff06f.
Lemma F_5097c : F! 0x5097c W_5097c.
Proof. vm_refl. Qed.
Lemma D_5097c : D! W_5097c (Jal 0 2097064).
Proof. vm_refl. Qed.
Definition W_50980 : bv 32 := 0x02088c63.
Lemma F_50980 : F! 0x50980 W_50980.
Proof. vm_refl. Qed.
Lemma D_50980 : D! W_50980 (Branch BC_EQ 17 0 56).
Proof. vm_refl. Qed.
Definition W_509b8 : bv 32 := 0x0105b603.
Lemma F_509b8 : F! 0x509b8 W_509b8.
Proof. vm_refl. Qed.
Lemma D_509b8 : D! W_509b8 (Load SZ8 true 12 11 16).
Proof. vm_refl. Qed.
Definition W_509bc : bv 32 := 0x0205b683.
Lemma F_509bc : F! 0x509bc W_509bc.
Proof. vm_refl. Qed.
Lemma D_509bc : D! W_509bc (Load SZ8 true 13 11 32).
Proof. vm_refl. Qed.
Definition W_509c0 : bv 32 := 0x0285b503.
Lemma F_509c0 : F! 0x509c0 W_509c0.
Proof. vm_refl. Qed.
Lemma D_509c0 : D! W_509c0 (Load SZ8 true 10 11 40).
Proof. vm_refl. Qed.
Definition W_509c4 : bv 32 := 0x00c68733.
Lemma F_509c4 : F! 0x509c4 W_509c4.
Proof. vm_refl. Qed.
Lemma D_509c4 : D! W_509c4 (Op ALU_ADD 14 13 12).
Proof. vm_refl. Qed.
Definition W_509c8 : bv 32 := 0xfff50793.
Lemma F_509c8 : F! 0x509c8 W_509c8.
Proof. vm_refl. Qed.
Lemma D_509c8 : D! W_509c8 (OpImm ALU_ADD 15 10 4095).
Proof. vm_refl. Qed.
Definition W_509cc : bv 32 := 0x40e00733.
Lemma F_509cc : F! 0x509cc W_509cc.
Proof. vm_refl. Qed.
Lemma D_509cc : D! W_509cc (Op ALU_SUB 14 0 14).
Proof. vm_refl. Qed.
Definition W_509d0 : bv 32 := 0x00c7f633.
Lemma F_509d0 : F! 0x509d0 W_509d0.
Proof. vm_refl. Qed.
Lemma D_509d0 : D! W_509d0 (Op ALU_AND 12 15 12).
Proof. vm_refl. Qed.
Definition W_509d4 : bv 32 := 0x00e7f733.
Lemma F_509d4 : F! 0x509d4 W_509d4.
Proof. vm_refl. Qed.
Lemma D_509d4 : D! W_509d4 (Op ALU_AND 14 15 14).
Proof. vm_refl. Qed.
Definition W_509d8 : bv 32 := 0x00700793.
Lemma F_509d8 : F! 0x509d8 W_509d8.
Proof. vm_refl. Qed.
Lemma D_509d8 : D! W_509d8 (OpImm ALU_ADD 15 0 7).
Proof. vm_refl. Qed.
Definition W_509dc : bv 32 := 0x00d706b3.
Lemma F_509dc : F! 0x509dc W_509dc.
Proof. vm_refl. Qed.
Lemma D_509dc : D! W_509dc (Op ALU_ADD 13 14 13).
Proof. vm_refl. Qed.
Definition W_509e0 : bv 32 := 0x02d5b023.
Lemma F_509e0 : F! 0x509e0 W_509e0.
Proof. vm_refl. Qed.
Lemma D_509e0 : D! W_509e0 (Store SZ8 11 13 32).
Proof. vm_refl. Qed.
Definition W_509e4 : bv 32 := 0x02c5b823.
Lemma F_509e4 : F! 0x509e4 W_509e4.
Proof. vm_refl. Qed.
Lemma D_509e4 : D! W_509e4 (Store SZ8 11 12 48).
Proof. vm_refl. Qed.
Definition W_509e8 : bv 32 := 0x00a7e663.
Lemma F_509e8 : F! 0x509e8 W_509e8.
Proof. vm_refl. Qed.
Lemma D_509e8 : D! W_509e8 (Branch BC_LTU 15 10 12).
Proof. vm_refl. Qed.
Definition W_509ec : bv 32 := 0x00800513.
Lemma F_509ec : F! 0x509ec W_509ec.
Proof. vm_refl. Qed.
Lemma D_509ec : D! W_509ec (OpImm ALU_ADD 10 0 8).
Proof. vm_refl. Qed.
Definition W_509f0 : bv 32 := 0x02a5b423.
Lemma F_509f0 : F! 0x509f0 W_509f0.
Proof. vm_refl. Qed.
Lemma D_509f0 : D! W_509f0 (Store SZ8 11 10 40).
Proof. vm_refl. Qed.
Definition W_509f4 : bv 32 := 0x00d60633.
Lemma F_509f4 : F! 0x509f4 W_509f4.
Proof. vm_refl. Qed.
Lemma D_509f4 : D! W_509f4 (Op ALU_ADD 12 12 13).
Proof. vm_refl. Qed.
Definition W_509f8 : bv 32 := 0x000205b7.
Lemma F_509f8 : F! 0x509f8 W_509f8.
Proof. vm_refl. Qed.
Lemma D_509f8 : D! W_509f8 (Lui 11 32).
Proof. vm_refl. Qed.
Definition W_509fc : bv 32 := 0x00a60633.
Lemma F_509fc : F! 0x509fc W_509fc.
Proof. vm_refl. Qed.
Lemma D_509fc : D! W_509fc (Op ALU_ADD 12 12 10).
Proof. vm_refl. Qed.
Definition W_50a00 : bv 32 := 0x0d15869b.
Lemma F_50a00 : F! 0x50a00 W_50a00.
Proof. vm_refl. Qed.
Lemma D_50a00 : D! W_50a00 (OpImm32 13 11 209).
Proof. vm_refl. Qed.
Definition W_50a04 : bv 32 := 0x0df60593.
Lemma F_50a04 : F! 0x50a04 W_50a04.
Proof. vm_refl. Qed.
Lemma D_50a04 : D! W_50a04 (OpImm ALU_ADD 11 12 223).
Proof. vm_refl. Qed.
Definition W_50a08 : bv 32 := 0xff85f593.
Lemma F_50a08 : F! 0x50a08 W_50a08.
Proof. vm_refl. Qed.
Lemma D_50a08 : D! W_50a08 (OpImm ALU_AND 11 11 4088).
Proof. vm_refl. Qed.
Definition W_50a0c : bv 32 := 0x00b4bc23.
Lemma F_50a0c : F! 0x50a0c W_50a0c.
Proof. vm_refl. Qed.
Lemma D_50a0c : D! W_50a0c (Store SZ8 9 11 24).
Proof. vm_refl. Qed.
Definition W_50a10 : bv 32 := 0x02a4b023.
Lemma F_50a10 : F! 0x50a10 W_50a10.
Proof. vm_refl. Qed.
Lemma D_50a10 : D! W_50a10 (Store SZ8 9 10 32).
Proof. vm_refl. Qed.
Definition W_50a14 : bv 32 := 0x02d5ea63.
Lemma F_50a14 : F! 0x50a14 W_50a14.
Proof. vm_refl. Qed.
Lemma D_50a14 : D! W_50a14 (Branch BC_LTU 11 13 52).
Proof. vm_refl. Qed.
Definition W_50a48 : bv 32 := 0x00025697.
Lemma F_50a48 : F! 0x50a48 W_50a48.
Proof. vm_refl. Qed.
Lemma D_50a48 : D! W_50a48 (Auipc 13 37).
Proof. vm_refl. Qed.
Definition W_50a4c : bv 32 := 0x0104b983.
Lemma F_50a4c : F! 0x50a4c W_50a4c.
Proof. vm_refl. Qed.
Lemma D_50a4c : D! W_50a4c (Load SZ8 true 19 9 16).
Proof. vm_refl. Qed.
Definition W_50a50 : bv 32 := 0x0284b603.
Lemma F_50a50 : F! 0x50a50 W_50a50.
Proof. vm_refl. Qed.
Lemma D_50a50 : D! W_50a50 (Load SZ8 true 12 9 40).
Proof. vm_refl. Qed.
Definition W_50a54 : bv 32 := 0xfff50713.
Lemma F_50a54 : F! 0x50a54 W_50a54.
Proof. vm_refl. Qed.
Lemma D_50a54 : D! W_50a54 (OpImm ALU_ADD 14 10 4095).
Proof. vm_refl. Qed.
Definition W_50a58 : bv 32 := 0xf3800793.
Lemma F_50a58 : F! 0x50a58 W_50a58.
Proof. vm_refl. Qed.
Lemma D_50a58 : D! W_50a58 (OpImm ALU_ADD 15 0 3896).
Proof. vm_refl. Qed.
Definition W_50a5c : bv 32 := 0x0c068513.
Lemma F_50a5c : F! 0x50a5c W_50a5c.
Proof. vm_refl. Qed.
Lemma D_50a5c : D! W_50a5c (OpImm ALU_ADD 10 13 192).
Proof. vm_refl. Qed.
Definition W_50a60 : bv 32 := 0x40a787b3.
Lemma F_50a60 : F! 0x50a60 W_50a60.
Proof. vm_refl. Qed.
Lemma D_50a60 : D! W_50a60 (Op ALU_SUB 15 15 10).
Proof. vm_refl. Qed.
Definition W_50a64 : bv 32 := 0x00f77733.
Lemma F_50a64 : F! 0x50a64 W_50a64.
Proof. vm_refl. Qed.
Lemma D_50a64 : D! W_50a64 (Op ALU_AND 14 14 15).
Proof. vm_refl. Qed.
Definition W_50a68 : bv 32 := 0xfff64693.
Lemma F_50a68 : F! 0x50a68 W_50a68.
Proof. vm_refl. Qed.
Lemma D_50a68 : D! W_50a68 (OpImm ALU_XOR 13 12 4095).
Proof. vm_refl. Qed.
Definition W_50a6c : bv 32 := 0x00e50933.
Lemma F_50a6c : F! 0x50a6c W_50a6c.
Proof. vm_refl. Qed.
Lemma D_50a6c : D! W_50a6c (Op ALU_ADD 18 10 14).
Proof. vm_refl. Qed.
Definition W_50a70 : bv 32 := 0x00369693.
Lemma F_50a70 : F! 0x50a70 W_50a70.
Proof. vm_refl. Qed.
Lemma D_50a70 : D! W_50a70 (ShiftImm ALU_SLL 13 13 3).
Proof. vm_refl. Qed.
Definition W_50a74 : bv 32 := 0x00d506b3.
Lemma F_50a74 : F! 0x50a74 W_50a74.
Proof. vm_refl. Qed.
Lemma D_50a74 : D! W_50a74 (Op ALU_ADD 13 10 13).
Proof. vm_refl. Qed.
Definition W_50a78 : bv 32 := 0x00b68a33.
Lemma F_50a78 : F! 0x50a78 W_50a78.
Proof. vm_refl. Qed.
Lemma D_50a78 : D! W_50a78 (Op ALU_ADD 20 13 11).
Proof. vm_refl. Qed.
Definition W_50a7c : bv 32 := 0x0c890413.
Lemma F_50a7c : F! 0x50a7c W_50a7c.
Proof. vm_refl. Qed.
Lemma D_50a7c : D! W_50a7c (OpImm ALU_ADD 8 18 200).
Proof. vm_refl. Qed.
Definition W_50a80 : bv 32 := 0x04098463.
Lemma F_50a80 : F! 0x50a80 W_50a80.
Proof. vm_refl. Qed.
Lemma D_50a80 : D! W_50a80 (Branch BC_EQ 19 0 72).
Proof. vm_refl. Qed.
Definition W_50ac8 : bv 32 := 0x00ca3023.
Lemma F_50ac8 : F! 0x50ac8 W_50ac8.
Proof. vm_refl. Qed.
Lemma D_50ac8 : D! W_50ac8 (Store SZ8 20 12 0).
Proof. vm_refl. Qed.
Definition W_50acc : bv 32 := 0x0d493023.
Lemma F_50acc : F! 0x50acc W_50acc.
Proof. vm_refl. Qed.
Lemma D_50acc : D! W_50acc (Store SZ8 18 20 192).
Proof. vm_refl. Qed.
Definition W_50ad0 : bv 32 := 0x01293023.
Lemma F_50ad0 : F! 0x50ad0 W_50ad0.
Proof. vm_refl. Qed.
Lemma D_50ad0 : D! W_50ad0 (Store SZ8 18 18 0).
Proof. vm_refl. Qed.
Definition W_50ad4 : bv 32 := 0x00040513.
Lemma F_50ad4 : F! 0x50ad4 W_50ad4.
Proof. vm_refl. Qed.
Lemma D_50ad4 : D! W_50ad4 (OpImm ALU_ADD 10 8 0).
Proof. vm_refl. Qed.
Definition W_50ad8 : bv 32 := 0x1a50e0ef.
Lemma F_50ad8 : F! 0x50ad8 W_50ad8.
Proof. vm_refl. Qed.
Lemma D_50ad8 : D! W_50ad8 (Jal 1 59812).
Proof. vm_refl. Qed.
Definition W_50adc : bv 32 := 0x04054a63.
Lemma F_50adc : F! 0x50adc W_50adc.
Proof. vm_refl. Qed.
Lemma D_50adc : D! W_50adc (Branch BC_LT 10 0 84).
Proof. vm_refl. Qed.
Definition W_50ae0 : bv 32 := 0x00051663.
Lemma F_50ae0 : F! 0x50ae0 W_50ae0.
Proof. vm_refl. Qed.
Lemma D_50ae0 : D! W_50ae0 (Branch BC_NE 10 0 12).
Proof. vm_refl. Qed.
Definition W_50ae4 : bv 32 := 0x00100513.
Lemma F_50ae4 : F! 0x50ae4 W_50ae4.
Proof. vm_refl. Qed.
Lemma D_50ae4 : D! W_50ae4 (OpImm ALU_ADD 10 0 1).
Proof. vm_refl. Qed.
Definition W_50ae8 : bv 32 := 0x00a48023.
Lemma F_50ae8 : F! 0x50ae8 W_50ae8.
Proof. vm_refl. Qed.
Lemma D_50ae8 : D! W_50ae8 (Store SZ1 9 10 0).
Proof. vm_refl. Qed.
Definition W_50aec : bv 32 := 0x00200513.
Lemma F_50aec : F! 0x50aec W_50aec.
Proof. vm_refl. Qed.
Lemma D_50aec : D! W_50aec (OpImm ALU_ADD 10 0 2).
Proof. vm_refl. Qed.
Definition W_50af0 : bv 32 := 0x00045597.
Lemma F_50af0 : F! 0x50af0 W_50af0.
Proof. vm_refl. Qed.
Lemma D_50af0 : D! W_50af0 (Auipc 11 69).
Proof. vm_refl. Qed.
Definition W_50af4 : bv 32 := 0x02a92423.
Lemma F_50af4 : F! 0x50af4 W_50af4.
Proof. vm_refl. Qed.
Lemma D_50af4 : D! W_50af4 (Store SZ4 18 10 40).
Proof. vm_refl. Qed.
Definition W_50af8 : bv 32 := 0x06000893.
Lemma F_50af8 : F! 0x50af8 W_50af8.
Proof. vm_refl. Qed.
Lemma D_50af8 : D! W_50af8 (OpImm ALU_ADD 17 0 96).
Proof. vm_refl. Qed.
Definition W_50afc : bv 32 := 0x0e858513.
Lemma F_50afc : F! 0x50afc W_50afc.
Proof. vm_refl. Qed.
Lemma D_50afc : D! W_50afc (OpImm ALU_ADD 10 11 232).
Proof. vm_refl. Qed.
Definition W_50b00 : bv 32 := 0x03848593.
Lemma F_50b00 : F! 0x50b00 W_50b00.
Proof. vm_refl. Qed.
Lemma D_50b00 : D! W_50b00 (OpImm ALU_ADD 11 9 56).
Proof. vm_refl. Qed.
Definition W_50b04 : bv 32 := 0x00000073.
Lemma F_50b04 : F! 0x50b04 W_50b04.
Proof. vm_refl. Qed.
Lemma E_50b04 : is_ecall W_50b04 = true.
Proof. reflexivity. Qed.
Definition W_50b08 : bv 32 := 0x07890613.
Lemma F_50b08 : F! 0x50b08 W_50b08.
Proof. vm_refl. Qed.
Lemma D_50b08 : D! W_50b08 (OpImm ALU_ADD 12 18 120).
Proof. vm_refl. Qed.
Definition W_50b0c : bv 32 := 0x02a92023.
Lemma F_50b0c : F! 0x50b0c W_50b0c.
Proof. vm_refl. Qed.
Lemma D_50b0c : D! W_50b0c (Store SZ4 18 10 32).
Proof. vm_refl. Qed.
Definition W_50b10 : bv 32 := 0x08b93c23.
Lemma F_50b10 : F! 0x50b10 W_50b10.
Proof. vm_refl. Qed.
Lemma D_50b10 : D! W_50b10 (Store SZ8 18 11 152).
Proof. vm_refl. Qed.
Definition W_50b14 : bv 32 := 0x06c93c23.
Lemma F_50b14 : F! 0x50b14 W_50b14.
Proof. vm_refl. Qed.
Lemma D_50b14 : D! W_50b14 (Store SZ8 18 12 120).
Proof. vm_refl. Qed.
Definition W_50b18 : bv 32 := 0x00045517.
Lemma F_50b18 : F! 0x50b18 W_50b18.
Proof. vm_refl. Qed.
Lemma D_50b18 : D! W_50b18 (Auipc 10 69).
Proof. vm_refl. Qed.
Definition W_50b1c : bv 32 := 0x33053503.
Lemma F_50b1c : F! 0x50b1c W_50b1c.
Proof. vm_refl. Qed.
Lemma D_50b1c : D! W_50b1c (Load SZ8 true 10 10 816).
Proof. vm_refl. Qed.
Definition W_50b20 : bv 32 := 0x01293423.
Lemma F_50b20 : F! 0x50b20 W_50b20.
Proof. vm_refl. Qed.
Lemma D_50b20 : D! W_50b20 (Store SZ8 18 18 8).
Proof. vm_refl. Qed.
Definition W_50b24 : bv 32 := 0x01293823.
Lemma F_50b24 : F! 0x50b24 W_50b24.
Proof. vm_refl. Qed.
Lemma D_50b24 : D! W_50b24 (Store SZ8 18 18 16).
Proof. vm_refl. Qed.
Definition W_50b28 : bv 32 := 0x00a93c23.
Lemma F_50b28 : F! 0x50b28 W_50b28.
Proof. vm_refl. Qed.
Lemma D_50b28 : D! W_50b28 (Store SZ8 18 10 24).
Proof. vm_refl. Qed.
Definition W_50b2c : bv 32 := 0x0080006f.
Lemma F_50b2c : F! 0x50b2c W_50b2c.
Proof. vm_refl. Qed.
Lemma D_50b2c : D! W_50b2c (Jal 0 8).
Proof. vm_refl. Qed.
Definition W_50b34 : bv 32 := 0x03813083.
Lemma F_50b34 : F! 0x50b34 W_50b34.
Proof. vm_refl. Qed.
Lemma D_50b34 : D! W_50b34 (Load SZ8 true 1 2 56).
Proof. vm_refl. Qed.
Definition W_50b38 : bv 32 := 0x03013403.
Lemma F_50b38 : F! 0x50b38 W_50b38.
Proof. vm_refl. Qed.
Lemma D_50b38 : D! W_50b38 (Load SZ8 true 8 2 48).
Proof. vm_refl. Qed.
Definition W_50b3c : bv 32 := 0x02813483.
Lemma F_50b3c : F! 0x50b3c W_50b3c.
Proof. vm_refl. Qed.
Lemma D_50b3c : D! W_50b3c (Load SZ8 true 9 2 40).
Proof. vm_refl. Qed.
Definition W_50b40 : bv 32 := 0x02013903.
Lemma F_50b40 : F! 0x50b40 W_50b40.
Proof. vm_refl. Qed.
Lemma D_50b40 : D! W_50b40 (Load SZ8 true 18 2 32).
Proof. vm_refl. Qed.
Definition W_50b44 : bv 32 := 0x01813983.
Lemma F_50b44 : F! 0x50b44 W_50b44.
Proof. vm_refl. Qed.
Lemma D_50b44 : D! W_50b44 (Load SZ8 true 19 2 24).
Proof. vm_refl. Qed.
Definition W_50b48 : bv 32 := 0x01013a03.
Lemma F_50b48 : F! 0x50b48 W_50b48.
Proof. vm_refl. Qed.
Lemma D_50b48 : D! W_50b48 (Load SZ8 true 20 2 16).
Proof. vm_refl. Qed.
Definition W_50b4c : bv 32 := 0x00813a83.
Lemma F_50b4c : F! 0x50b4c W_50b4c.
Proof. vm_refl. Qed.
Lemma D_50b4c : D! W_50b4c (Load SZ8 true 21 2 8).
Proof. vm_refl. Qed.
Definition W_50b50 : bv 32 := 0x04010113.
Lemma F_50b50 : F! 0x50b50 W_50b50.
Proof. vm_refl. Qed.
Lemma D_50b50 : D! W_50b50 (OpImm ALU_ADD 2 2 64).
Proof. vm_refl. Qed.
Definition W_50b54 : bv 32 := 0x00008067.
Lemma F_50b54 : F! 0x50b54 W_50b54.
Proof. vm_refl. Qed.
Lemma D_50b54 : D! W_50b54 (Jalr 0 1 0).
Proof. vm_refl. Qed.
