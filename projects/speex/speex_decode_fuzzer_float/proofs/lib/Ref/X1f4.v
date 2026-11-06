(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1hm X1ht X1ff X1f5 X1f6.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Lemma lts_ge_false8 a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.

Lemma lsp_to_lpc8_spec : lsp_to_lpc8_stmt_copy.
Proof.
unfold lsp_to_lpc8_stmt_copy. intros IQ AK lo qs aks stk8. intros until m. intros X LQ A LA ST LOW GLO SP63 AI AA AAI -> -> -> -> MI FRM.
pose proof AI as AI'. pose proof AA as AA'. pose proof AAI as AAI'. unfold apart in AI', AA', AAI'.
unfold LSP2LPC_DEPTH in LOW. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO'. unfold A_lsp_to_lpc.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
pose proof (munch_refl [(lo, bv_unsigned sp); (AK, AK + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
zstep. carve_frame 64%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 8%nat _ FR) as (fw8 & Lfw & FR'); clear FR.
destruct fw8 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|? ?]]]]]]]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
carve_frame 8%nat ST. rename FR0 into PADA.
carve_frame 72%nat ST. rename FR0 into WP.
carve_frame 32%nat ST. rename FR0 into XF.
carve_frame 3976%nat ST. rename FR0 into JK1.
carve_frame 8%nat ST. rename FR0 into P1.
carve_frame 72%nat ST. rename FR0 into JK2.
carve_frame 8%nat ST. rename FR0 into P2.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ P1) as (pw1 & Lp1 & P1'); clear P1. destruct pw1 as [|p1w [|? ?]]; cbn in Lp1; try lia. cbn [map] in P1'. rename P1' into P1.
destruct (rw_cells_CB_C8s rsegs _ _ 1%nat _ P2) as (pw2 & Lp2 & P2'); clear P2. destruct pw2 as [|p2w [|? ?]]; cbn in Lp2; try lia. cbn [map] in P2'. rename P2' into P2.
lstep. do 7 zstep.
do 13 zstep. replace (bv_unsigned sp + -64 - 80) with (bv_unsigned sp + -144) by lia.
zstep. zstep. replace (bv_unsigned sp + -64 - 4096) with (bv_unsigned sp + -4160) by lia.
lstep. zstep. unshelve epose proof (lts_ge_false8 (bv_unsigned sp + -144) (bv_unsigned sp + -4160) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB. zstep. zstep. if_false_x.
do 8 zstep.
match goal with |- context [Z.shiftl (Z.land ?x 17) 2 + 4] => replace (Z.shiftl (Z.land x 17) 2 + 4) with 72 by reflexivity end.
zstep. call (nmemset_specZ (bv_unsigned sp + -144) 72 0 junk1); [exact WP | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
rename POST into WP.
do 6 zstep. replace (bv_unsigned sp + -144 - 32) with (bv_unsigned sp + -176) by lia.
zstep. zstep. replace (bv_unsigned sp + -144 - 4096) with (bv_unsigned sp + -4240) by lia.
lstep. zstep. unshelve epose proof (lts_ge_false8 (bv_unsigned sp + -176) (bv_unsigned sp + -4240) _ _ _) as PB; [lia|lia|lia|].
if_false_by PB. clear PB. zstep. zstep. if_false_x.
do 12 zstep.
zstep. zstep. zstep. replace (bv_unsigned sp + -176 + 32) with (bv_unsigned sp + -144) by lia.
change (Z.to_nat 72) with (4 * 18)%nat in WP.
destruct (rw_cells_CB_f32 rsegs _ _ 18%nat _ WP) as (wp & Lwp & WP'); clear WP; rename WP' into WP.
destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ XF) as (xf & Lxf & XF'); clear XF; rename XF' into XF.
destruct xf as [|xf0 xf]; [cbn in Lxf; lia|]. cbn [length] in Lxf.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. cbn [length] in LQ.
chunk_cat P2 JK2. chunk_cat P2 P1. chunk_cat P2 JK1. rename P2 into LJ.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (xloop IQ AK lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW GLO SP63 AI AA AAI
7%nat aks [] xf qs wp (bv_unsigned sp + -176) IQ) end;
[ exact LA | lia | lia | reflexivity | exact Lwp | cbn [length]; lia | cbn [length]; lia
| exact FRM | | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP
| apply rw_cells_nil; lia | exact XF | exact LJ | exact A | exact X ]; assumption.
Qed.
