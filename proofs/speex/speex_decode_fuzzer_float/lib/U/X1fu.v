(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1nq X1mc X1ft.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Lemma qmf_synth_320 : qmf_synth_stmt_N 320.
Proof.
unfold qmf_synth_stmt_N. intros until m.
intros X LX G0C LG0 G1C LG1 STK8 ST LO GLO SP63 GLY WG0 WG1 AYS AG0S AG1S AYG0 AYG1 AG01 -> -> -> -> -> -> -> -> MI FRM YM4 G0P G0M4 G1P G1M4.
unfold QMF_DEPTH in LO. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO', GLY, WG0, WG1. unfold A_qmf_synth, A_h0, QMF_ORDER.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32, LX in BX.
pose proof (rw_cells_bound _ _ _ _ G0C) as BG0. rewrite cells_size_f32, LG0 in BG0.
pose proof (rw_cells_bound _ _ _ _ G1C) as BG1. rewrite cells_size_f32, LG1 in BG1.
pose proof (munch_refl [(lo, bv_unsigned sp); (Y, Y + 4 * 320); (G0, G0 + 256); (G1, G1 + 256)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (u32arr_of_f32 rsegs _ _ _ X) as YA. pose proof (u32arr_of_f32 rsegs _ _ _ G0C) as G0A.
pose proof (u32arr_of_f32 rsegs _ _ _ G1C) as G1A. clear X G0C G1C.

zstep.
carve_frame 104%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 13%nat _ FR) as (fw & Lfw & FR'); clear FR.
destruct fw as [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|? ?]]]]]]]]]]]]]]; cbn in Lfw; try lia.
cbn [map] in FR'. rename FR' into FR.
carve_frame 8%nat ST. rename FR0 into C6. carve_frame 8%nat ST. rename FR0 into C5. carve_frame 8%nat ST. rename FR0 into C4.
carve_frame 8%nat ST. rename FR0 into C3. carve_frame 8%nat ST. rename FR0 into C2. carve_frame 8%nat ST. rename FR0 into C1.
carve_frame 8%nat ST. rename FR0 into C0.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C6) as (pw6 & Lp6 & C6'); clear C6. destruct pw6 as [|w6 [|? ?]]; cbn in Lp6; try lia. cbn [map] in C6'. rename C6' into C6.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C5) as (pw5 & Lp5 & C5'); clear C5. destruct pw5 as [|w5 [|? ?]]; cbn in Lp5; try lia. cbn [map] in C5'. rename C5' into C5.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C4) as (pw4 & Lp4 & C4'); clear C4. destruct pw4 as [|w4 [|? ?]]; cbn in Lp4; try lia. cbn [map] in C4'. rename C4' into C4.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C3) as (pw3 & Lp3 & C3'); clear C3. destruct pw3 as [|w3 [|? ?]]; cbn in Lp3; try lia. cbn [map] in C3'. rename C3' into C3.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C2) as (pw2 & Lp2 & C2'); clear C2. destruct pw2 as [|w2 [|? ?]]; cbn in Lp2; try lia. cbn [map] in C2'. rename C2' into C2.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C1) as (pw1 & Lp1 & C1'); clear C1. destruct pw1 as [|w1 [|? ?]]; cbn in Lp1; try lia. cbn [map] in C1'. rename C1' into C1.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ C0) as (pw0 & Lp0 & C0'); clear C0. destruct pw0 as [|w0 [|? ?]]; cbn in Lp0; try lia. cbn [map] in C0'. rename C0' into C0.
clear Lfw Lp0 Lp1 Lp2 Lp3 Lp4 Lp5 Lp6.
lstep. do 13 zstep.
do 4 zstep. zstep. ub_dec.
do 2 zstep. lstep.
do 5 zstep. replace (bv_unsigned sp + -160 + - (768)) with (bv_unsigned sp + -928) by lia.
replace (bv_unsigned sp + -160 + - (4096)) with (bv_unsigned sp + -4256) by lia.
probe_store ST (bv_unsigned sp + -4256).
zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -928) (bv_unsigned sp + -4256) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB.
zstep. zstep. zstep. zstep.
replace (bv_unsigned sp + -928 + - (768)) with (bv_unsigned sp + -1696) by lia.
replace (bv_unsigned sp + -928 + - (4096)) with (bv_unsigned sp + -5024) by lia.
probe_store ST (bv_unsigned sp + -5024).
zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -1696) (bv_unsigned sp + -5024) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB.
zstep.
zstep. zstep. zstep. ub_dec. zstep. zstep. zstep. zstep.
carve_frame 768%nat ST. rename FR0 into XX1. carve_frame 768%nat ST. rename FR0 into XX2.
change 768%nat with (4 * 192)%nat in XX1, XX2.
destruct (rw_cells_CB_f32 rsegs _ _ 192%nat _ XX1) as (xx1 & Lxx1 & XX1'); clear XX1.
destruct (rw_cells_CB_f32 rsegs _ _ 192%nat _ XX2) as (xx2 & Lxx2 & XX2'); clear XX2.
pose proof (u32arr_of_f32 rsegs _ _ _ XX1') as X1A. pose proof (u32arr_of_f32 rsegs _ _ _ XX2') as X2A. clear XX1' XX2'.
replace (Z.b2z (0 <? Y)) with 1 by (destruct (Z.ltb_spec 0 Y); cbn; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -928)) with (Z_to_bv 64 (bv_unsigned sp + -928 + 4 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -928, bv_unsigned sp + -928 + 4 * Z.of_nat 192)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L1 ra gp tp sp 160 0 160 Y (bv_unsigned sp + -928) 192 ys xx1 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX; lia).
all: try (f_equal; lia).
clear MUL WML Lxx1. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -928) ?c, L : length ?c = 192%nat |- _ => rename H into X1A; rename L into Lxx1 end.
replace (bv_unsigned sp + -928 + 4 * 0) with (bv_unsigned sp + -928) by lia.
zstep. rewrite (land3_al G0 G0M4). lstep.
zstep. zstep. ub_dec. do 9 zstep. balits.
replace (Z_to_bv 64 (G0 + 4)) with (Z_to_bv 64 (G0 + 4 + 8 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -928, bv_unsigned sp + -928 + 4 * Z.of_nat 192)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L2 ra gp tp sp 32 0 160 G0 (bv_unsigned sp + -928) 192 g0 _ [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try reflexivity. all: try (f_equal; lia).
clear MUL WML Lxx1. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -928) ?c, L : length ?c = 192%nat |- _ => rename H into X1A; rename L into Lxx1 end.
zstep. zstep. ub_dec. do 4 zstep.
replace (Z.b2z (0 <? Y + 640)) with 1 by (destruct (Z.ltb_spec 0 (Y + 640)); cbn; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -1696)) with (Z_to_bv 64 (bv_unsigned sp + -1696 + 4 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -1696, bv_unsigned sp + -1696 + 4 * Z.of_nat 192)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L3 ra gp tp sp 160 0 160 Y (bv_unsigned sp + -1696) 192 ys _ [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try reflexivity. all: try (f_equal; lia).
clear MUL WML Lxx2. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -1696) ?c, L : length ?c = 192%nat |- _ => rename H into X2A; rename L into Lxx2 end.
replace (bv_unsigned sp + -1696 + 4 * 0) with (bv_unsigned sp + -1696) by lia.
zstep. rewrite (land3_al G1 G1M4). lstep.
zstep. ub_dec. do 9 zstep. balits.
replace (Z_to_bv 64 (G1 + 4)) with (Z_to_bv 64 (G1 + 4 + 8 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -1696, bv_unsigned sp + -1696 + 4 * Z.of_nat 192)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L4 ra gp tp sp 32 0 160 G1 (bv_unsigned sp + -1696) 192 g1 _ [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try reflexivity. all: try (f_equal; lia).
clear MUL WML Lxx2. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -1696) ?c, L : length ?c = 192%nat |- _ => rename H into X2A; rename L into Lxx2 end.
zstep. ub_dec. do 9 zstep. balits.
replace (Z.b2z (0 <? Y)) with 1 by (destruct (Z.ltb_spec 0 Y); cbn; lia). rewrite (land3_al Y YM4).
lstep. zstep. zstep. zstep. balits. lstep. zstep. balits. lstep. zstep.
destruct (h0_ro _ MI) as [HB LHB].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(Y, Y + 8 * 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_outer gp tp sp (Z_to_bv 64 G0) (Z_to_bv 64 G1) 80 0 0 160 (bv_unsigned sp + -928) (bv_unsigned sp + -1696) Y
192 _ _ ys h0_bytes [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try reflexivity. all: try (f_equal; lia).
all: try (rewrite LX; reflexivity).
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ Y ?c, L : Z.of_nat (length ?c) = 2 * 160 |- _ => rename H into YA2; rename L into LY2 end.
zstep. ub_dec. do 5 zstep.
replace (Z_to_bv 64 (G0 + 4)) with (Z_to_bv 64 (G0 + 4 + 8 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(G0, G0 + 256)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L5 _ gp tp sp _ _ 32 0 (bv_unsigned sp + -928) G0 192 _ g0 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try reflexivity. all: try (f_equal; lia).
clear MUL WML. try rename MI0 into MI.
zstep. zstep.
replace (Z_to_bv 64 (G1 + 4)) with (Z_to_bv 64 (G1 + 4 + 8 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(G1, G1 + 256)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L6 _ gp tp sp _ _ 32 0 (bv_unsigned sp + -1696) G1 192 _ g1 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try reflexivity. all: try (f_equal; lia).
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ G0 ?c, L : length ?c = 64%nat |- _ => rename H into G0A'; rename L into LG0' end.
match goal with H : u32arr rsegs _ G1 ?c, L : length ?c = 64%nat |- _ => rename H into G1A'; rename L into LG1' end.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -928) ?c, L : length ?c = 192%nat |- _ => rename H into X1F; rename L into LX1F end.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -1696) ?c, L : length ?c = 192%nat |- _ => rename H into X2F; rename L into LX2F end.

zstep. do 13 zstep. zstep. zstep.

pose proof (f32_of_u32arr rsegs _ _ _ X2F) as X2C. pose proof (f32_of_u32arr rsegs _ _ _ X1F) as X1C. clear X2F X1F.
eapply stk_release in X2C; [| exact ST| lia]. rewrite cells_size_f32, LX2F in X2C. clear ST.
replace (bv_unsigned sp + -1696 + Z.of_nat (4 * 192)) with (bv_unsigned sp + -928) in X2C by lia.
eapply stk_release in X1C; [| exact X2C| lia]. rewrite cells_size_f32, LX1F in X1C. clear X2C.
replace (bv_unsigned sp + -928 + Z.of_nat (4 * 192)) with (bv_unsigned sp + -160) in X1C by lia.
rename X1C into ST.
release_frame C0 ST (bv_unsigned sp + -152). release_frame C1 ST (bv_unsigned sp + -144).
release_frame C2 ST (bv_unsigned sp + -136). release_frame C3 ST (bv_unsigned sp + -128).
release_frame C4 ST (bv_unsigned sp + -120). release_frame C5 ST (bv_unsigned sp + -112).
release_frame C6 ST (bv_unsigned sp + -104). release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold qmf_synth_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact ST|].
split; [apply f32_of_u32arr; exact YA2|]. split; [lia|].
split; [apply f32_of_u32arr; exact G0A'|]. split; [exact LG0'|].
split; [apply f32_of_u32arr; exact G1A'|]. exact LG1'.
Qed.
