(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1f7 X1f8.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma lts_ge_false a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.

Lemma lsp_to_lpc_proof : lsp_to_lpc_stmt.
Proof.
intros IQ AK lo qs aks stk8. intros until m. intros X LQ A LA ST LOW GLO SP63 AI AA AAI -> -> -> -> MI FRM IQ0 IQ4 AK0 AK4 SP16.
pose proof AI as AI'. pose proof AA as AA'. pose proof AAI as AAI'. unfold apart in AI', AA', AAI'.
unfold LSP2LPC_DEPTH in LOW. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO'. unfold A_lsp_to_lpc.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
pose proof (munch_refl [(lo, bv_unsigned sp); (AK, AK + 40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
zstep. carve_frame 80%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 10%nat _ FR) as (fw8 & Lfw & FR'); clear FR.
destruct fw8 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|? ?]]]]]]]]]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
carve_frame 8%nat ST. rename FR0 into PADA.
carve_frame 88%nat ST. rename FR0 into WP.
carve_frame 8%nat ST. rename FR0 into PADB.
carve_frame 40%nat ST. rename FR0 into XF.
carve_frame 3944%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
carve_frame 88%nat ST. rename FR0 into JK2.
carve_frame 8%nat ST. rename FR0 into P2.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ P1) as (pw1 & Lp1 & P1'); clear P1. destruct pw1 as [|p1w [|? ?]]; cbn in Lp1; try lia. cbn [map] in P1'. rename P1' into P1.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ P2) as (pw2 & Lp2 & P2'); clear P2. destruct pw2 as [|p2w [|? ?]]; cbn in Lp2; try lia. cbn [map] in P2'. rename P2' into P2.
destruct (rw_cells_CB_f32 rsegs _ _ 22%nat _ WP) as (wp & Lwp & WP'); clear WP; rename WP' into WP.
destruct wp as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 [|v6 [|v7 [|v8 [|v9 [|v10 [|v11 [|v12 [|v13 [|v14 [|v15 [|v16 [|v17 [|v18 [|v19 [|v20 [|v21 [|? ?]]]]]]]]]]]]]]]]]]]]]]];
cbn in Lwp; try lia. rewrite !f32_cons, f32_nil in WP.
lstep. do 10 zstep. zstep.
do 4 zstep. zstep. if_false_x.
zstep. zstep. if_false_x.
do 5 zstep. replace (bv_unsigned sp + -80 - 96) with (bv_unsigned sp + -176) by lia.
zstep. zstep. replace (bv_unsigned sp + -80 - 4096) with (bv_unsigned sp + -4176) by lia.
lstep. zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -176) (bv_unsigned sp + -4176) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB.
do 4 zstep.
do 21 (zstep; if_false_x; zstep; zstep; lstep; zstep; zstep; if_true_x).
zstep. if_false_x. zstep. zstep. lstep. zstep. zstep. if_false_x.
zstep. if_false_x.
do 4 zstep. replace (bv_unsigned sp + -176 - 48) with (bv_unsigned sp + -224) by lia.
zstep. zstep. replace (bv_unsigned sp + -176 - 4096) with (bv_unsigned sp + -4272) by lia.
lstep. zstep. unshelve epose proof (lts_ge_false (bv_unsigned sp + -224) (bv_unsigned sp + -4272) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB.
zstep.
do 14 zstep. rewrite zb_lxor_ones by lia.
do 5 zstep. cond_prep.
destruct (rw_cells_CB_f32 rsegs _ _ 10%nat _ XF) as (xf & Lxf & XF'); clear XF; rename XF' into XF.
destruct xf as [|xf0 xf]; [cbn in Lxf; lia|]. cbn [length] in Lxf.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. cbn [length] in LQ.
chunk_cat P2 JK2. chunk_cat P2 P1. chunk_cat P2 JK1. rename P2 into LJ.
eapply (xloop IQ AK lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16
9%nat aks [] xf qs [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] (bv_unsigned sp + -224) IQ 0 10);
[ exact LA | lia | lia | reflexivity | reflexivity | cbn [length]; lia | cbn [length]; lia | cbn [length]; lia | cbn [length Z.of_nat]; lia
| assumption | assumption | assumption | assumption | exact ST | exact FR | exact PADA | exact WP | exact PADB
| apply rw_cells_nil; lia | exact XF | exact LJ | exact A | exact X ].
Qed.
