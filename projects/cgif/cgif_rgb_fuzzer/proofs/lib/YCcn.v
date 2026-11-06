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
Lemma rf_R4 : rf_from B ss_RET (INV_RET B) -> rf_from B ss_M (INV_M B) -> rf_from B ss_R4 (INV_R B 6).
Proof.
intros RRET RN. rf_prelude.
pose proof HINV as (Hk0 & Eab3 & Hin).
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpdc).
reshok HS.
srr_branch_tok tratbl_lib_ok HS SHOK RBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
rewrite branch_geu_U in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => rewrite (U_atom Ex 34 nb ltac:(enorm; exact E34)), (U_atom_off Ex 35 cur 7 ltac:(enorm; exact E35)) in Hc by lia end.
assert (HOK : cur + 7 <= nb) by (destruct (nb <? cur + 7) eqn:Hlt; [discriminate | apply Z.ltb_ge in Hlt; lia]). clear Hc.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rf_pay HS HJ3 Hpd3 6 1 HOK E36 Usp B10 B11.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
lazymatch goal with Ebx : ew _ 86 = Z_to_bv 64 ?v |- _ => rename Ebx into Efmt; set (fmt := v) in *; assert (Rfmt : 0 <= fmt < 256) by (subst fmt; apply abyte_range) end.
srr_branch_tok tratbl_lib_ok HS SHOK RBspan.
+
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RBspan 0x81988.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rf_stream_words HS B10 E33 E34 (cur + 7) ltac:(rewrite denot_lit_U; f_equal; apply U_atom_off; [exact E35 | lia | lia]) Vp Vn Vc.
rf_obj_at HS B11 0 ltac:(reflexivity) 0 ltac:(reflexivity) OBJ.
rfj_join HS ss_RET 310%nat rf_RET_deads_bv.
rf_hand RRET HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists (2 ^ 64 - 1), (cur + 7).
split; [exact Ra0|]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcur HOK; lia|].
left. split; [reflexivity|]. split; [rewrite Eab3; exact HPerm|]. exact OBJ.
+
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
rewrite branch_ltu_U in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => rewrite (U_lit Ex 1) in Hc by lia end.
rewrite U_SOff in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite Efmt in Hc. rewrite unsigned_lit_small in Hc by (clear - Rfmt; lia).
assert (Hfmt : fmt = 3 \/ fmt = 4).
{ apply Z.ltb_ge in Hc. unfold zcanon, M64 in Hc. clear - Hc Rfmt. destruct (Z_lt_ge_dec fmt 3) as [Hl|Hg].
- exfalso. replace (fmt + -3) with ((fmt + -3 + 2 ^ 64) + (-1) * 2 ^ 64) in Hc by lia. rewrite Z_mod_plus_full in Hc. rewrite Z.mod_small in Hc by lia. lia.
- rewrite Z.mod_small in Hc by lia. lia. }
clear Hc.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RBspan.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
rf_hand RN HS.
split; [exact Hk0|]. split; [exact Eab3|]. split; [exact HOK|]. exists fmt. split; [rewrite ?ew_ewset_other by lia; exact Efmt | exact Hfmt].
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
rewrite branch_geu_U in Hc.
lazymatch type of HS with st_ok _ ?Ex _ _ => rewrite (U_atom Ex 34 nb ltac:(enorm; exact E34)), (U_atom_off Ex 35 cur 7 ltac:(enorm; exact E35)) in Hc by lia end.
assert (HKO : nb < cur + 7) by (destruct (nb <? cur + 7) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia | discriminate]). clear Hc.
norm_ss HS.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RBspan 0x81988.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA3. }
rf_after_run Usp B10 B11.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rf_stream_words HS B10 E33 E34 nb ltac:(rewrite sv_denot_SOff0; exact E34) Vp Vn Vc.
rf_obj_at HS B11 0 ltac:(reflexivity) 0 ltac:(reflexivity) OBJ.
rfj_join HS ss_RET 310%nat rf_RET_deads_bv.
rf_hand RRET HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists (2 ^ 64 - 1), nb.
split; [exact Ra0|]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcur; lia|].
left. split; [reflexivity|]. split; [rewrite Eab3; exact HPerm|]. exact OBJ.
Qed.
End b.
End a.
