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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1n8 X1ho X1hm X1hu X1ht X1ih X1nr X1mc X1mv X1mb X1ma X1mw X1mo X1mh X1mk.
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

#[using="RCEIL k IH"] Lemma sbT_80 : FS = 80 -> forall low dtx s1 b ms, at_T X low dtx s1 b ms -> evt rsegs (at_X X 0 (set_sbd_first s1 0) low b) ms.
Proof.
intros EFS low dtx s1 b ms AT.
first [ sf_destruct 40%nat AT as Fx fc m kk xra xa0 xs2 xs3 xs6 xs7 xs8 xs10 xs11 j ows stb fr vpi ver vq viq vak -> FRM CTX ST FRA F0e Fdtx DTX01 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs2 & xs3 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & -> & FRM & CTX & ST & FRA & F0e & Fdtx & DTX01 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
assert (Hffs1 : sbd_full_frame_size s1 = 8 * FS) by (rewrite Iffs1, Hfs1; lia). clear Iffs1.
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-432) ltac:(lia)) as USP432. pose proof (USPk _ _ IH (-448) ltac:(lia)) as USP448.

zstep. zstep. rewrite Hffs1. rewrite (sx32_lit (8 * 80)) by lia. zstep. rewrite Hfs1. rewrite (sx32_lit (4 * 80)) by lia.
zstep. zstep. lstep.

zstep. replace (Z.shiftl (4 * 80) 2) with 1280 by reflexivity. zstep. zstep.
carve_frame 16%nat ST.
apply (rw_cells_split_CB rsegs _ _ [] 16 _ _ [8;8]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.

zstep. zstep. zstep. lstep. zstep. zstep. zstep.
chunk_splitk FR at 1%nat as FR8.
pose proof (f32_split rsegs _ _ ows 640%nat ltac:(rewrite Lows; lia) XO) as [XOY XO3]. clear XO.
replace (OUT + 4 * Z.of_nat 640%nat) with (OUT + 2560) in XO3 by lia.
assert (LY : length (firstn 640%nat ows) = Z.to_nat 640) by (rewrite length_firstn, Lows; lia).
assert (LC : length (skipn 640%nat ows) = (2000 - 640%nat)%nat) by (rewrite length_skipn, Lows; lia).
set (owsY := firstn 640%nat ows) in *. set (owsC := skipn 640%nat ows) in *. clearbody owsY owsC.
call ((h_qmf _ (ih_hyps _ _ IH)) OUT 640 (a_g0 a) (a_g1 a) lo owsY (sj_g0 j) (sj_g1 j) (Z_to_bv 64 0));
[ exact XOY | exact LY | lia | exact BG0 | exact Lg0 | exact BG1 | exact Lg1
| rewrite USP448; exact FR8
| rewrite USP448; exact ST | rewrite USP448; unfold QMF_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USP448; lia
| unfold NB_GLOBALS_TOP; lia
| pose proof (lay_img_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); unfold NB_GLOBALS_TOP; lia
| pose proof (lay_img_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); unfold NB_GLOBALS_TOP; lia
| rewrite USP448; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP448; unfold apart; lia | rewrite USP448; unfold apart; lia
| unfold apart; lia | unfold apart; lia
| unfold apart; pose proof (lay_G0_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact MI | exact FRM | ].
cbv beta delta [callR]. clear FRM. try clear ST. try clear XOY; try clear LY; try clear BG0; try clear BG1. name_post. rename FRMc into FRM. rename STc into ST. rewrite USP448 in ST.
match goal with H : rw_cells _ _ OUT (f32 ?w), L : length ?w = _ |- _ => rename H into XOY; rename L into LY; rename w into owsY2 end.
match goal with H : rw_cells _ _ (a_g0 a) (f32 ?w), L : length ?w = _ |- _ => rename H into BG0; rename L into Lg0'; rename w into g0' end.
match goal with H : rw_cells _ _ (a_g1 a) (f32 ?w), L : length ?w = _ |- _ => rename H into BG1; rename L into Lg1'; rename w into g1' end.
pose proof (f32_join rsegs _ _ _ _ XOY ltac:(rewrite LY; replace (OUT + 4 * Z.of_nat (Z.to_nat 640)) with (OUT + 2560) by lia; exact XO3)) as XO. clear XOY XO3.
assert (Lows' : length (owsY2 ++ owsC) = 2000%nat) by (rewrite length_app, LY, LC; lia).
set (owsN := owsY2 ++ owsC) in *. clearbody owsN.

zstep. chunk_cat FR8 FR. release_frame FR8 ST (usp + -432).

zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia. zstep. rewrite (lts_zero_lit 8) by lia. if_false_x.
zstep. zstep. zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (cp3_loop X (usp + -368) (a_oq a) (a_oq a + 32) 8%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (sj_oq j) vq [] [] (a_oq a) (usp + -368));
[ cbn [length]; rewrite Loq; lia | rewrite Lvq, Loq; reflexivity | reflexivity | rewrite Loq; lia
| cbn [length]; lia | cbn [length]; lia | lia
| lia | lia | unfold apart; lia
| exact MI | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at BOQ
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VQ | ] end.
cbv beta. try clear BOQ; try clear VQ. name_post. try rename STc into ST. try rename FRMc into FRM. cbn [app] in *.
match goal with H : rw_cells _ _ (a_oq a) (f32 ?w), L : length ?w = _ |- _ => rename H into BOQ; rename L into LoqN; rename w into oqN end.
match goal with H : rw_cells _ _ (usp + -368) (f32 vq) |- _ => rename H into VQ end.

lstep. zstep. rewrite F0e.

pose proof (f32_as_blob _ _ _ 8%nat VAK Lvak) as B1. pose proof (f32_as_blob _ _ _ 8%nat VIQ Lviq) as B2. pose proof (f32_as_blob _ _ _ 8%nat VQ Lvq) as B3.
pose proof (f32_as_blob _ _ _ 4%nat VER Lver) as B4. pose proof (f32_as_blob _ _ _ 4%nat VPI Lvpi) as B5.
change (Z.to_nat (4 * Z.of_nat 8%nat)) with 32%nat in B1, B2, B3. change (Z.to_nat (4 * Z.of_nat 4%nat)) with 16%nat in B4, B5.
clear VAK VIQ VQ VER VPI.
chunk_cat B1 B2. chunk_cat B1 B3. chunk_cat B1 B4. chunk_cat B1 B5.
release_frame B1 ST (usp + -304).

zstep.
apply evt_done. unfold at_X.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 13%nat.
lazymatch goal with P : rw_cells _ _ (S + 128) [C4 ?le] |- _ =>
exists (SBJ le (sj_seed j) (sj_pad1 j) (sj_pad2 j) g0' g1' (sj_exc j) oqN (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) end.
exists owsN, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|]. lia.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
