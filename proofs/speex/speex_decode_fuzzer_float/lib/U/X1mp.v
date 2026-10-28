(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mo X1mh X1mk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).
Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Local Ltac bdec_in K := repeat match type of K with
| context [?x <? ?y] => first [ replace (x <? y) with true in K by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y) with false in K by (symmetry; apply Z.ltb_ge; lia) ]
| context [?x =? ?y] => first [ replace (x =? y) with true in K by (symmetry; apply Z.eqb_eq; lia) | replace (x =? y) with false in K by (symmetry; apply Z.eqb_neq; lia) ]
end.
Local Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia;
rewrite ?unsigned_lit in K by lia; rewrite ?land3_mod4 in K; bdec_in K;
[ first [ exfalso; lia | exfalso; vm_compute in K; first [ discriminate K | lia ] ] | clear K ].
Local Ltac rfl := first [ reflexivity | f_equal; lia ].
Local Ltac cpit := zstep; zstep; ntk; zstep; zstep; ntk; zstep; zstep; zstep; ntk; zstep; zstep; zstep; zstep; ntk; zstep; ntk;
zstep; zstep; zstep; ntk; zstep; zstep; step; zstep; step; zstep.

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

#[using="RCEIL k IH"] Lemma sbT_40 : FS = 40 -> forall low dtx s1 b ms, at_T X low dtx s1 b ms -> evt rsegs (at_X X 0 (set_sbd_first s1 0) low b) ms.
Proof.
intros EFS low dtx s1 b ms AT.
first [ sf_destruct 48%nat AT as Fx fc m kk xra xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 j ows stb fr vpi ver vq viq vak -> FRM CTX ST FRA F0e F144 F152 F176 F184 F208 Fdtx DTX01 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs9 & xs10 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & -> & FRM & CTX & ST & FRA & F0e & F144 & F152 & F176 & F184 & F208 & Fdtx & DTX01 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
rewrite F0e, F144, F152, F176, F184, F208 in FL.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
assert (Hffs1 : sbd_full_frame_size s1 = 8 * FS) by (rewrite Iffs1, Hfs1; lia). clear Iffs1.
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-512) ltac:(lia)) as USP512. pose proof (USPk _ _ IH (-528) ltac:(lia)) as USP528.
pose proof (ih_out4 _ _ IH) as OUT4.
pose proof (ih_range _ _ IH) as RNG.
pose proof (RNG (sbd_g0_mem s0, a_g0 a, 256) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; right; left; reflexivity)) as RG0.
pose proof (RNG (sbd_g1_mem s0, a_g1 a, 256) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; right; right; left; reflexivity)) as RG1.
pose proof (RNG (sbd_old_qlsp s0, a_oq a, 32) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; do 4 right; left; reflexivity)) as ROQ.
unfold rblock_range in RG0, RG1, ROQ. cbn in RG0, RG1, ROQ. clear RNG.
pose proof (rw_cells_bound _ _ _ _ BOQ) as BBOQ. rewrite cells_size_f32, Loq in BBOQ.

zstep. rewrite Hfs1. rewrite (sx32_lit (4 * 40)) by lia.
zstep. zstep. replace (Z.shiftl (4 * 40) 2) with 640 by reflexivity.
zstep. zstep. lstep.
zstep. zstep. ntk.
zstep. zstep. zstep. zstep. zstep. ntk.
zstep. rewrite Hffs1. rewrite (sx32_lit (8 * 40)) by lia.
zstep. zstep. zstep.
carve_frame 16%nat ST.
apply (rw_cells_split_CB rsegs _ _ [] 16 _ _ [8;8]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.
zstep. zstep. zstep. zstep. lstep. zstep. zstep. zstep.
chunk_splitk FR at 1%nat as FR8.
pose proof (f32_split rsegs _ _ ows 320%nat ltac:(rewrite Lows; lia) XO) as [XOY XO3]. clear XO.
replace (OUT + 4 * Z.of_nat 320%nat) with (OUT + 1280) in XO3 by lia.
assert (LY : length (firstn 320%nat ows) = Z.to_nat 320) by (rewrite length_firstn, Lows; lia).
assert (LC : length (skipn 320%nat ows) = (2000 - 320%nat)%nat) by (rewrite length_skipn, Lows; lia).
set (owsY := firstn 320%nat ows) in *. set (owsC := skipn 320%nat ows) in *. clearbody owsY owsC.
call ((h_qmf _ (ih_hyps _ _ IH)) OUT 320 (a_g0 a) (a_g1 a) lo owsY (sj_g0 j) (sj_g1 j) (Z_to_bv 64 0));
[ exact XOY | exact LY | lia | exact BG0 | exact Lg0 | exact BG1 | exact Lg1
| rewrite USP528; exact FR8
| rewrite USP528; exact ST | rewrite USP528; unfold QMF_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USP528; lia
| unfold NB_GLOBALS_TOP; lia
| pose proof (lay_img_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); unfold NB_GLOBALS_TOP; lia
| pose proof (lay_img_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); unfold NB_GLOBALS_TOP; lia
| rewrite USP528; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP528; unfold apart; lia | rewrite USP528; unfold apart; lia
| unfold apart; lia | unfold apart; lia
| unfold apart; pose proof (lay_G0_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
| exact MI | exact FRM
| exact OUT4 | lia | lia | lia | lia | ].
cbv beta delta [callR]. clear FRM. try clear ST. try clear XOY; try clear LY; try clear BG0; try clear BG1. name_post. rename FRMc into FRM. rename STc into ST. rewrite USP528 in ST.
match goal with H : rw_cells _ _ OUT (f32 ?w), L : length ?w = _ |- _ => rename H into XOY; rename L into LY; rename w into owsY2 end.
match goal with H : rw_cells _ _ (a_g0 a) (f32 ?w), L : length ?w = _ |- _ => rename H into BG0; rename L into Lg0'; rename w into g0' end.
match goal with H : rw_cells _ _ (a_g1 a) (f32 ?w), L : length ?w = _ |- _ => rename H into BG1; rename L into Lg1'; rename w into g1' end.
pose proof (f32_join rsegs _ _ _ _ XOY ltac:(rewrite LY; replace (OUT + 4 * Z.of_nat (Z.to_nat 320)) with (OUT + 1280) by lia; exact XO3)) as XO. clear XOY XO3.
assert (Lows' : length (owsY2 ++ owsC) = 2000%nat) by (rewrite length_app, LY, LC; lia).
set (owsN := owsY2 ++ owsC) in *. clearbody owsN.

zstep. chunk_cat FR8 FR. release_frame FR8 ST (usp + -512).

zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia. zstep. rewrite (lts_zero_lit 8) by lia. if_false_x.
zstep. zstep.

remember (sj_oq j) as oq0 eqn:Eoq0.
destruct oq0 as [|o0 [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|o7 [|oo oq']]]]]]]]]; try (cbn in Loq; lia).
destruct vq as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|qq vq']]]]]]]]]; try (cbn in Lvq; lia).
rewrite !f32_cons, f32_nil in BOQ, VQ.
cpit. if_true_x. cpit. if_true_x. cpit. if_true_x. cpit. if_true_x.
cpit. if_true_x. cpit. if_true_x. cpit. if_true_x. cpit. if_false_x.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of BOQ with rw_cells _ _ _ [C4 ?v0; C4 ?v1; C4 ?v2; C4 ?v3; C4 ?v4; C4 ?v5; C4 ?v6; C4 ?v7] =>
assert (BOQ' : rw_cells rsegs mm (a_oq a) (f32 [v0; v1; v2; v3; v4; v5; v6; v7])) by (rewrite !f32_cons, f32_nil; exact BOQ) end;
assert (VQ' : rw_cells rsegs mm (usp + -448) (f32 [q0; q1; q2; q3; q4; q5; q6; q7])) by (rewrite !f32_cons, f32_nil; exact VQ)
end.
clear BOQ VQ. rename BOQ' into BOQ. rename VQ' into VQ.
lazymatch type of BOQ with rw_cells _ _ _ (f32 ?l) => assert (LoqN : length l = 8%nat) by reflexivity; set (oqN := l) in *; clearbody oqN end.

lstep. zstep.

pose proof (f32_as_blob _ _ _ 8%nat VAK Lvak) as B1. pose proof (f32_as_blob _ _ _ 8%nat VIQ Lviq) as B2. pose proof (f32_as_blob _ _ _ 8%nat VQ Lvq) as B3.
pose proof (f32_as_blob _ _ _ 4%nat VER Lver) as B4. pose proof (f32_as_blob _ _ _ 4%nat VPI Lvpi) as B5.
change (Z.to_nat (4 * Z.of_nat 8%nat)) with 32%nat in B1, B2, B3. change (Z.to_nat (4 * Z.of_nat 4%nat)) with 16%nat in B4, B5.
clear VAK VIQ VQ VER VPI.
chunk_cat B1 B2. chunk_cat B1 B3. chunk_cat B1 B4. chunk_cat B1 B5.
release_frame B1 ST (usp + -384).

zstep.
apply evt_done. unfold at_X.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 13%nat.
lazymatch goal with P : rw_cells _ _ (S + 128) [C4 ?le] |- _ =>
exists (SBJ le (sj_seed j) (sj_pad1 j) (sj_pad2 j) g0' g1' (sj_exc j) oqN (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) end.
exists owsN, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|]. lia.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
