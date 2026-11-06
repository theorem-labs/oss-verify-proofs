(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1n8 X1ho X1hm X1hu X1ht X1ih X1nr X1mc X1mv X1mb X1ma X1mw X1mg X1mh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1ff X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Section Seg.
Context {RCEIL : RunCeiling}.
Variable k : nat.
Variable X : sbinv.
Hypothesis IH : sb_ihyps k X.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X). Local Notation b0 := (x_b0 X). Local Notation canary := (x_canary X). Local Notation st := (x_st X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation FS := (sbd_subframeSize (x_s X)).
Local Notation mo := (sbd_mode (x_s X)).

Ltac close_ctxE EFS MU := unfold sbctx, sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES; rewrite ?EFS; repeat match goal with |- _ /\ _ => split end; first [close_goal MU | congruence].

#[using="RCEIL k IH"] Lemma sbL2f_80 : FS = 80 -> forall low dtx s1 r sub b ms, sm_innovation_unquant (smr_sm r) = None ->
at_L1_80 X low dtx s1 r sub b ms -> evt rsegs (at_L2_80 X low dtx s1 r sub (ub b 5)) ms.
Proof.
intros EFS low dtx s1 r sub b ms HKI AT.
first [ sf_destruct 40%nat AT as Fx fc m kk xra xa0 xs11 j ows stb fr vpi ver vq viq vak vexc -> FRM CTX ST FRA LFR F104e F112e SAT Hsub Exs11 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak VEXC Lvexc | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & -> & FRM & CTX & ST & FRA & LFR & F104e & F112e & SAT & Hsub & Exs11 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak & VEXC & Lvexc) ].
pose proof LFR as sfP_; first [ sf_destruct 16%nat sfP_ as F0e F8e F16e F24e F32e F40e F48e F56e F64e F72e F80e F88e F96e F120e Fdtx DTX01 | sf_fb; destruct sfP_ as (F0e & F8e & F16e & F24e & F32e & F40e & F48e & F56e & F64e & F72e & F80e & F88e & F96e & F120e & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-752) ltac:(lia)) as USPX.
set (id := sbd_submodeID s1) in *.
first [ pose proof (sb_smrec_at_some mo id r SAT) as sfP_; sf_destruct 6%nat sfP_ as INr SMS Hid SPE LSPH UWBN | sf_fb; destruct (sb_smrec_at_some mo id r SAT) as (INr & SMS & Hid & SPE & LSPH & UWBN) ].

zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ TR _ | sf_fb; destruct sfP_ as (_ & _ & TR & _) ] end.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. clear RD. rewrite SPE.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC. cbn [innov_entry] in SMC.
unfold A_split_cb_shape_sign_unquant, A_noise_codebook_unquant in SMC.
zstep. clear SMC TR.

zstep. try if_true_x.

zstep. zstep. rewrite F120e. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 5); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 5) in *. cbn [fst snd] in *. after_bits REP (ub b 5).
pose proof (ub_ok b 5 BOK ltac:(lia)) as BOK5. pose proof (ub_same b 5) as (U5sz & U5o & U5c).
pose proof (speex_bits_unpack_unsigned_ok b 5 _ _ BOK ltac:(lia) (unpack_eta b 5)) as (_ & Q32 & _).
match goal with H : ?v = Z_to_bv 64 (uv b 5) |- _ => subst v end.
name_post. try rename FRMc into FRM. try rename STc into ST. try rewrite USPX in ST.

zstep. zstep. zstep. zstep. zstep.
call ((h_exp _ (ih_hyps _ _ IH)) lo); [rewrite USPX; exact ST | rewrite USPX; unfold EXP_DEPTH; lia | exact MI | exact FRM |].
cbv beta delta [callR]. clear FRM. name_post. rename FRMc into FRM. rename STc into ST. rewrite USPX in ST.

zstep. zstep. fp_join 0x286d4.
{ zstep. if_cases Kc; [apply evt_done; eexists; reflexivity | zstep; apply evt_done; eexists; reflexivity]. }
cbv beta. intros ms1 (Fx1 & ->).

zstep. rewrite Efs. rewrite (sx32_lit 80) by lia. zstep. rewrite (lts_zero_lit 80) by lia. if_false_x. zstep.

zstep. rewrite F24e.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ _ _ TWB TUWB | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TWB & TUWB) ] end.
rewrite (proj1 (FS80_mode k X IH EFS)). cbn [sbmode_struct].
unfold A_sb_wb_mode, A_sb_uwb_mode in TWB, TUWB |- *. cbv delta [sb_wb_mode_cells sb_uwb_mode_cells] in TWB, TUWB.
zstep. clear TWB TUWB.

zstep. rewrite (swrap32_small (80 * sub)) by lia.
zstep. zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 (80 * sub) 2) by lia. change (2 ^ 2) with 4.
zstep. zstep. zstep. rewrite F16e. rewrite Hfs. zstep. zstep.
replace (Z.land (Z.shiftl 80 2 + -4) (-8)) with 312 by reflexivity.
zstep. rewrite F8e. rewrite Hfs. zstep. zstep.

pose proof (f32_split rsegs _ _ ows (Z.to_nat (320 + 80 * sub)) ltac:(rewrite Lows; lia) XO) as [_ XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (320 + 80 * sub)) ows) 80%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XSRC _]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub))) with (OUT + 1280 + 320 * sub) in XSRC by lia.
assert (LSRC : length (firstn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows)) = 80%nat) by (rewrite length_firstn, length_skipn, Lows; lia).
set (src := firstn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows)) in *. clearbody src.
remember (OUT + 1280 + 320 * sub) as PSRC eqn:EPS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (fold_loop X PSRC (usp + -752) 80%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc 39%nat src [] vexc []);
[ exact LSRC | rewrite Lvexc; symmetry; exact LSRC | reflexivity | cbn [length]; lia | cbn [length]; lia | cbn [length]; subst PSRC; lia | subst PSRC; lia
| lia | subst PSRC; lia | subst PSRC; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| exact MI | apply munch_refl | apply wmono_refl | exact FRM
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC
| rewrite f32_nil; apply rw_cells_nil; subst PSRC; lia | exact_at XSRC | ] end.
cbv beta. clear FRM. try clear VEXC. clear XSRC. name_post. rename FRMc into FRM. try rename STc into ST.
cbn [app] in *.
replace (PSRC + 4 * Z.of_nat 80%nat + 4) with (OUT + 1280 + 320 * sub + 320 + 4) by lia. subst PSRC.
set (XS11V := xs11) in *. set (OWSV := ows) in *.
apply evt_done. unfold at_L2_80.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, XS11V.
lazymatch goal with P : rw_cells _ _ (S + 132) [C4 ?sd] |- _ =>
exists (SBJ (sj_last_ener j) sd (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) end.
exists OWSV, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
lazymatch goal with H : rw_cells _ _ (usp + -752) (f32 ?w) |- _ => exists w end.
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split. { exact LFR. }
cbn [f_104 f_112]. split; [exact F104e|]. split; [exact F112e|].
split; [exact SAT|]. split; [exact Hsub|]. split; [exact Exs11|].
split; [exact VPI|]. split; [exact Lvpi|]. split; [exact VER|]. split; [exact Lver|]. split; [exact VQ|]. split; [exact Lvq|].
split; [exact VIQ|]. split; [exact Lviq|]. split; [exact VAK|]. split; [exact Lvak|].
split; [assumption | first [assumption | lia]].

Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
