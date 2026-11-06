(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1m2 X1nj X1nk X1ho X1hm X1nq X1mc X1ft.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1re.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Lemma qmf_synth_640 : qmf_synth_stmt_N 640.
Proof.
unfold qmf_synth_stmt_N. intros until m.
intros X LX G0C LG0 G1C LG1 STK8 ST LO GLO SP63 GLY WG0 WG1 AYS AG0S AG1S AYG0 AYG1 AG01 -> -> -> -> -> -> -> -> MI FRM.
unfold QMF_DEPTH in LO. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO', GLY, WG0, WG1. unfold A_qmf_synth, A_h0, QMF_ORDER.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32, LX in BX.
pose proof (rw_cells_bound _ _ _ _ G0C) as BG0. rewrite cells_size_f32, LG0 in BG0.
pose proof (rw_cells_bound _ _ _ _ G1C) as BG1. rewrite cells_size_f32, LG1 in BG1.
pose proof (munch_refl [(lo, bv_unsigned sp); (Y, Y + 4 * 640); (G0, G0 + 256); (G1, G1 + 256)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (u32arr_of_f32 rsegs _ _ _ X) as YA. pose proof (u32arr_of_f32 rsegs _ _ _ G0C) as G0A.
pose proof (u32arr_of_f32 rsegs _ _ _ G1C) as G1A. clear X G0C G1C.

zstep. carve_frame 96%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 12%nat _ FR) as (fw & Lfw & FR'); clear FR.
destruct fw as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|? ?]]]]]]]]]]]]]; cbn in Lfw; try lia.
cbn [map] in FR'. rename FR' into FR.
lstep. do 11 zstep. zstep.

do 8 zstep. replace (bv_unsigned sp + -96 + - (1408)) with (bv_unsigned sp + -1504) by lia.
zstep. zstep. replace (bv_unsigned sp + -96 + - (4096)) with (bv_unsigned sp + -4192) by lia.
probe_store ST (bv_unsigned sp + -4192).
zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -1504) (bv_unsigned sp + -4192) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB.
zstep. zstep. replace (bv_unsigned sp + -1504 + - (1408)) with (bv_unsigned sp + -2912) by lia.
zstep. zstep. replace (bv_unsigned sp + -1504 + - (4096)) with (bv_unsigned sp + -5600) by lia.
probe_store ST (bv_unsigned sp + -5600).
zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -2912) (bv_unsigned sp + -5600) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB.
zstep.

carve_frame 1408%nat ST. rename FR0 into XX1. carve_frame 1408%nat ST. rename FR0 into XX2.
change 1408%nat with (4 * 352)%nat in XX1, XX2.
destruct (rw_cells_CB_f32 rsegs _ _ 352%nat _ XX1) as (xx1 & Lxx1 & XX1'); clear XX1.
destruct (rw_cells_CB_f32 rsegs _ _ 352%nat _ XX2) as (xx2 & Lxx2 & XX2'); clear XX2.
pose proof (u32arr_of_f32 rsegs _ _ _ XX1') as X1A. pose proof (u32arr_of_f32 rsegs _ _ _ XX2') as X2A. clear XX1' XX2'.

zstep. zstep. if_false_x. zstep. zstep. zstep.
replace (Z_to_bv 64 (Y + 1276)) with (Z_to_bv 64 (Y + 4 * 319)) by (f_equal; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -1504)) with (Z_to_bv 64 (bv_unsigned sp + -1504 + 4 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -1504, bv_unsigned sp + -1504 + 4 * Z.of_nat 352)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L1 ra gp tp sp 320 0 319 Y (bv_unsigned sp + -1504) 352 ys xx1 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX; lia).
clear MUL WML Lxx1. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -1504) ?c, L : length ?c = 352%nat |- _ => rename H into X1A; rename L into Lxx1' end.

zstep. zstep. if_false_x. zstep. zstep. zstep. zstep.
replace (Z_to_bv 64 (bv_unsigned sp + -224)) with (Z_to_bv 64 (bv_unsigned sp + -1504 + 4 * 320)) by (f_equal; lia).
replace (Z_to_bv 64 (G0 + 4)) with (Z_to_bv 64 (G0 + 4 * 1)) by (f_equal; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -96)) with (Z_to_bv 64 (bv_unsigned sp + -1504 + 4 * Z.of_nat 352)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -1504, bv_unsigned sp + -1504 + 4 * Z.of_nat 352)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L2 ra gp tp sp 32 320 1 G0 (bv_unsigned sp + -1504) 352 g0 _ [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
clear MUL WML Lxx1'. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -1504) ?c, L : length ?c = 352%nat |- _ => rename H into X1A; rename L into Lxx1' end.

zstep. if_false_x. zstep. zstep. zstep.
replace (Z_to_bv 64 (Y + 1276 + 1280)) with (Z_to_bv 64 (Y + 4 * 639)) by (f_equal; lia).
replace (Z_to_bv 64 (Y + 1276)) with (Z_to_bv 64 (Y + 4 * 320 + -4)) by (f_equal; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -2912)) with (Z_to_bv 64 (bv_unsigned sp + -2912 + 4 * 0)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -2912, bv_unsigned sp + -2912 + 4 * Z.of_nat 352)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L3 ra gp tp sp 320 0 639 320 Y (bv_unsigned sp + -2912) 352 ys xx2 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
clear MUL WML Lxx2. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -2912) ?c, L : length ?c = 352%nat |- _ => rename H into X2A; rename L into Lxx2 end.

zstep. if_false_x. zstep. zstep. zstep. zstep.
replace (Z_to_bv 64 (bv_unsigned sp + -1632)) with (Z_to_bv 64 (bv_unsigned sp + -2912 + 4 * 320)) by (f_equal; lia).
replace (Z_to_bv 64 (G1 + 4)) with (Z_to_bv 64 (G1 + 4 * 1)) by (f_equal; lia).
replace (Z_to_bv 64 (bv_unsigned sp + -1504)) with (Z_to_bv 64 (bv_unsigned sp + -2912 + 4 * Z.of_nat 352)) by (f_equal; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(bv_unsigned sp + -2912, bv_unsigned sp + -2912 + 4 * Z.of_nat 352)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L4 ra gp tp sp 32 320 1 G1 (bv_unsigned sp + -2912) 352 g1 _ [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
clear MUL WML Lxx2. try rename MI0 into MI.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -2912) ?c, L : length ?c = 352%nat |- _ => rename H into X2A; rename L into Lxx2 end.

replace (bv_unsigned sp + -2912 + 4 * Z.of_nat 352) with (bv_unsigned sp + -1504) by lia.
zstep. if_false_x. do 16 zstep.
do 5 zstep.
destruct (h0_ro _ MI) as [HB LHB].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(Y, Y + 8 * 320)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_outer ra gp tp sp (Z_to_bv 64 G0) (Z_to_bv 64 G1) s10 s11 160 0 0 320 (bv_unsigned sp + -1504) (bv_unsigned sp + -2912) Y
_ _ _ _ _ 352 _ _ ys h0_bytes [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
all: try (rewrite LX; reflexivity).
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ Y ?c, L : Z.of_nat (length ?c) = 2 * 320 |- _ => rename H into YA2; rename L into LY2 end.

zstep. if_false_x. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(G0, G0 + 256)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L5 ra gp tp sp s10 s11 32 0 (bv_unsigned sp + -1504) G0 _ _ _ 352 _ g0 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
clear MUL WML. try rename MI0 into MI.

zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(G1, G1 + 256)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (qmf_L6 ra gp tp sp s10 s11 32 0 (bv_unsigned sp + -2912) G1 _ _ _ 352 _ g1 [] mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption. all: try (unfold apart in *; rewrite ?LX, ?LG0, ?LG1; lia).
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ G0 ?c, L : length ?c = 64%nat |- _ => rename H into G0A'; rename L into LG0' end.
match goal with H : u32arr rsegs _ G1 ?c, L : length ?c = 64%nat |- _ => rename H into G1A'; rename L into LG1' end.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -1504) ?c, L : length ?c = 352%nat |- _ => rename H into X1F; rename L into LX1F end.
match goal with H : u32arr rsegs _ (bv_unsigned sp + -2912) ?c, L : length ?c = 352%nat |- _ => rename H into X2F; rename L into LX2F end.

zstep. do 11 zstep. zstep. zstep.

pose proof (f32_of_u32arr rsegs _ _ _ X2F) as X2C. pose proof (f32_of_u32arr rsegs _ _ _ X1F) as X1C. clear X2F X1F.
eapply stk_release in X2C; [| exact ST| lia]. rewrite cells_size_f32, LX2F in X2C. clear ST.
replace (bv_unsigned sp + -2912 + Z.of_nat (4 * 352)) with (bv_unsigned sp + -1504) in X2C by lia.
eapply stk_release in X1C; [| exact X2C| lia]. rewrite cells_size_f32, LX1F in X1C. clear X2C.
replace (bv_unsigned sp + -1504 + Z.of_nat (4 * 352)) with (bv_unsigned sp + -96) in X1C by lia.
release_frame FR X1C (bv_unsigned sp). rename X1C into ST.
apply evt_done. unfold qmf_synth_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact ST|].
split; [apply f32_of_u32arr; exact YA2|]. split; [lia|].
split; [apply f32_of_u32arr; exact G0A'|]. split; [exact LG0'|].
split; [apply f32_of_u32arr; exact G1A'|]. exact LG1'.
Qed.

