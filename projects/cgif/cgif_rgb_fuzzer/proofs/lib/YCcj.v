(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcp YCcv YCcu YCcw YCcr.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rf_M2 : rf_from B ss_C (INV_C B) -> rf_from B ss_F (INV_F B) -> rf_from B ss_M2 (INV_M2 B).
Proof.
intros RC RF. rf_prelude.
pose proof HINV as (Hk0 & HOK & fmt & img & HIMG). pose proof HIMG as (Efmt & Hfmt & Eimg & Hr4096 & HrHi & HrCeil & Hr16 & Ebl & Timg & Aimg).
cbn [x_N x_lyc x_Sc x_FP x_ly x_S x_STK x_sp0 x_own] in Efmt, Hfmt, Eimg, Hr4096, HrHi, HrCeil, Hr16, Ebl, Timg, Aimg.
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; left; exact Hpdc).
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
srr_branch_tok tratbl_lib_ok HS SHOK RBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
rewrite branch_geu_U in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (UA3 : U Ex (SAlu ALU_ADD (SMd M_MUL (SOff 12 0) (SOff 86 0)) (SOff 35 7)) = N * fmt + (cur + 7));
[ rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw];
rewrite (U_atom Ex 12 N ltac:(enorm; exact E12)), (U_atom Ex 86 fmt ltac:(enorm; exact Efmt)), (U_atom_off Ex 35 cur 7 ltac:(enorm; exact E35)) by (unfold RGB_NMAX in HN; lia);
rewrite (zcanon_id (N * fmt)) by (unfold M64, RGB_NMAX in *; clear - HN Hfmt; nia); apply zcanon_id; unfold M64, RGB_NMAX in *; clear - HN Hfmt Hcur HnbM; nia |];
rewrite UA3, (U_atom Ex 34 nb ltac:(enorm; exact E34)) in Hc by lia end.
assert (HENO : cur + 7 + fmt * N <= nb) by (destruct (nb <? N * fmt + (cur + 7)) eqn:Hlt; [discriminate | apply Z.ltb_ge in Hlt; clear - Hlt; lia]). clear Hc UA3.
norm_ss HS.
rf_hand RC HS.
split; [exact Hk0|]. exists fmt, img. split; [exact HENO | exact HIMG].
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
rf_hand RF HS.
split; [exact Hk0|]. split; [exact HOK|]. exists fmt, img.
unfold rf_img. cbn [x_N x_lyc x_Sc x_FP x_ly x_S x_STK x_sp0 x_own].
split; [rewrite ?ew_ewset_other by lia; exact Efmt|]. split; [exact Hfmt|]. split; [rewrite ?ew_ewset_other by lia; exact Eimg|].
split; [exact Hr4096|]. split; [exact HrHi|]. split; [exact HrCeil|]. split; [exact Hr16|]. split; [exact Ebl|]. split; [exact Timg | exact Aimg].
Qed.
End b.
End a.
