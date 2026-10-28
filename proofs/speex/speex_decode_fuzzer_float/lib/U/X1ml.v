(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1ms X1mh X1mk.
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
Local Ltac bdec_goal := repeat match goal with
| |- context [?x <? ?y] => first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]
| |- context [?x =? ?y] => first [ replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia) | replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia) ]
end.
Local Ltac weq := first [ reflexivity | f_equal; lia
| rewrite ?zb_lxor_ones by lia; first [ reflexivity | f_equal; lia ]
| f_equal; rewrite ?unsigned_lit by lia; rewrite ?land3_mod4; rewrite ?zb_lxor_ones by lia; bdec_goal; first [ reflexivity | lia ] ].

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

#[using="RCEIL k IH"] Lemma sbL3_80 : FS = 80 -> forall low dtx s1 r sub b ms, at_L2_80 X low dtx s1 r sub b ms -> evt rsegs (QL3 X low dtx s1 r sub b) ms.
Proof.
intros EFS low dtx s1 r sub b ms AT.
first [ sf_destruct 46%nat AT as Fx fc m kk xra xa0 xs2 xs3 xs4 xs9 xs11 j ows stb fr vpi ver vq viq vak vexc -> FRM CTX ST FRA LFR F136e F168e F192e F200e SAT Hsub Exs9 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak VEXC Lvexc | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs2 & xs3 & xs4 & xs9 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & -> & FRM & CTX & ST & FRA & LFR & F136e & F168e & F192e & F200e & SAT & Hsub & Exs9 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak & VEXC & Lvexc) ].
pose proof LFR as sfP_; first [ sf_destruct 25%nat sfP_ as F0e F8e F16e F24e F32e F40e F56e F64e F72e F80e F88e F96e F104e F112e F120e F128e F144e F152e F160e F176e F184e F208e F216e Fdtx DTX01 | sf_fb; destruct sfP_ as (F0e & F8e & F16e & F24e & F32e & F40e & F56e & F64e & F72e & F80e & F88e & F96e & F104e & F112e & F120e & F128e & F144e & F152e & F160e & F176e & F184e & F208e & F216e & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
rewrite F0e, F8e, F16e, F24e, F32e, F40e, F56e, F64e, F72e, F80e, F88e, F96e, F104e, F112e, F120e, F128e, F136e, F144e, F152e, F160e, F168e, F176e, F184e, F192e, F200e, F208e, F216e in FL.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-832) ltac:(lia)) as USPX. pose proof (USPk _ _ IH (-512) ltac:(lia)) as USP512.
pose proof (ih_isave _ _ IH) as KK. rewrite EFS in KK.
pose proof (ih_out4 _ _ IH) as OUT4.
pose proof (ih_range _ _ IH) as RNG.
pose proof (RNG (sbd_excBuf s0, a_exc a, 4 * sbd_subframeSize s0) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; do 3 right; left; reflexivity)) as REXC.
pose proof (RNG (sbd_interp_qlpc s0, a_iq a, 32) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; do 5 right; left; reflexivity)) as RIQ.
pose proof (RNG (sbd_exc_rms s0, a_er a, 16) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; do 7 right; left; reflexivity)) as RER.
pose proof (RNG (sbd_mem_sp s0, a_msp a, 64) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; do 8 right; left; reflexivity)) as RMSP.
unfold rblock_range in REXC, RIQ, RER, RMSP. cbn in REXC, RIQ, RER, RMSP. clear RNG.
destruct REXC as (REXC0 & REXC16 & _). destruct RIQ as (RIQ0 & RIQ16 & _). destruct RER as (RER0 & RER16 & _). destruct RMSP as (RMSP0 & RMSP16 & _).

zstep. unfold sb_isave_ptr. rewrite Eis. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(OUT, OUT + 8000)] mm) as MUJ; pose proof (wmono_refl rsegs mm) as WMJ end.

lazymatch type of MUJ with munch _ ?MMM _ =>
eapply (evt_cut rsegs (fun ms1 => exists (Fx1 : bvmap 5 word) (m1 : mem) (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 : word) (ows1 : list word),
ms1 = MS (mkR xra (Z_to_bv 64 (usp + -832)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
xs2 xs3 xs4 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 320)
(Z_to_bv 64 (usp + -832)) xs9 (Z_to_bv 64 (usp + -512)) xs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx1 (Z_to_bv 64 0x2f92c) fc None m1 (seg_rom rsegs)
/\ mem_inv rsegs m1 /\ munch [(OUT, OUT + 8000)] MMM m1 /\ wmono rsegs MMM m1
/\ rw_cells rsegs m1 OUT (f32 ows1) /\ length ows1 = 2000%nat)) end.
{ destruct (sbd_innov_save s0) as [kk0|] eqn:EISV.
- subst kk0. if_false_x.
try (rewrite EISV in Exs9); cbv iota in Exs9. subst xs9.
zstep. rewrite ?Efs. rewrite ?(sx32_lit 80) by lia. zstep. rewrite (lts_zero_lit 80) by lia. if_false_x.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
pose proof (f32_split rsegs _ _ ows (Z.to_nat (640 + 160 * sub)) ltac:(rewrite Lows; lia) XO) as [XO1 XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (640 + 160 * sub)) ows) 160%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XO2a XO3]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (640 + 160 * sub)) + 4 * Z.of_nat 160%nat) with (OUT + 2560 + 640 * sub + 640) in XO3 by lia.
replace (OUT + 4 * Z.of_nat (Z.to_nat (640 + 160 * sub))) with (OUT + 2560 + 640 * sub) in XO2a by lia.
set (owsA := firstn (Z.to_nat (640 + 160 * sub)) ows) in *.
assert (LA : Z.of_nat (length owsA) = 640 + 160 * sub) by (subst owsA; rewrite length_firstn, Lows; lia).
set (owsB := firstn 160%nat (skipn (Z.to_nat (640 + 160 * sub)) ows)) in *.
assert (LB : length owsB = 160%nat) by (subst owsB; rewrite length_firstn, length_skipn, Lows; lia).
set (owsC := skipn 160%nat (skipn (Z.to_nat (640 + 160 * sub)) ows)) in *.
assert (LC : Z.of_nat (length owsC) = 2000 - 160 - (640 + 160 * sub)) by (subst owsC; rewrite !length_skipn, Lows; lia).
clearbody owsA owsB owsC. clear XO.
remember (OUT + 2560 + 640 * sub) as ISV eqn:EISVA.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FLf : rw_cells rsegs mm (usp + -384) (sframe_cells fr))
by (unfold sframe_cells; rewrite F0e, F8e, F16e, F24e, F32e, F40e, F56e, F64e, F72e, F80e, F88e, F96e, F104e, F112e, F120e, F128e, F136e, F144e, F152e, F160e, F168e, F176e, F184e, F192e, F200e, F208e, F216e; exact FL) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (isv_loop X (usp + -832) ISV 320 fr 80%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc vexc owsB [] [] ISV (usp + -832));
[ cbn [length]; lia | reflexivity | rewrite LB, Lvexc; reflexivity | lia
| cbn [length]; lia | cbn [length]; lia | weq | weq | weq
| subst ISV; lia | subst ISV; lia | subst ISV; lia | lia | lia | lia | lia
| exact F216e
| subst ISV; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| subst ISV; unfold apart, sframe_cells; cbn [cells_size csize Nat.add]; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| weq | weq | weq | weq
| exact MI | apply munch_refl | apply wmono_refl | exact FLf
| rewrite f32_nil; apply rw_cells_nil; subst ISV; lia | exact_at XO2a
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC | ] end.
cbv beta. try clear XO2a. clear LB FLf. name_post. try rename STc into ST. try rename FRMc into FRM.
cbn [app] in *.
match goal with H : rw_cells _ _ ISV (f32 ?w), L : length ?w = _ |- _ => rename H into XO2; rename L into LB2; rename w into owsB2 end.
match goal with H : rw_cells _ _ (usp + -832) (f32 vexc) |- _ => rename H into VEXC end.
subst ISV.
pose proof (f32_join rsegs _ _ _ _ XO1 ltac:(replace (OUT + 4 * Z.of_nat (length owsA)) with (OUT + 2560 + 640 * sub) by lia; exact XO2)) as XO12.
pose proof (f32_join rsegs _ _ _ _ XO12 ltac:(rewrite length_app, LB2; replace (OUT + 4 * Z.of_nat (length owsA + (2 * 80%nat))) with (OUT + 2560 + 640 * sub + 640) by lia; exact XO3)) as XO.
clear XO1 XO12 XO2 XO3.
assert (LowsN : length ((owsA ++ owsB2) ++ owsC) = 2000%nat) by (rewrite !length_app, LB2; lia).
apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, ((owsA ++ owsB2) ++ owsC).
split; [reflexivity|]. split; [exact MI|]. split; [exact MUJ|]. split; [exact WMJ|].
split; [exact XO| exact LowsN].
- if_true_x.
apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, ows.
split; [reflexivity|]. split; [exact MI|]. split; [exact MUJ|]. split; [exact WMJ|].
split; [exact XO| exact Lows]. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 17%nat sfH_ as Fx1 m1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ows1 -> MI1 MUJ' WMJ' XO1 Lows1 | sf_fb; destruct sfH_ as (Fx1 & m1 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ows1 & -> & MI1 & MUJ' & WMJ' & XO1 & Lows1) ].
clear XO Lows. lazymatch type of MUJ' with munch _ ?ma ?mb => transport_after_call rsegs ma mb MUJ' WMJ' end.
clear MUJ' WMJ' MUJ WMJ. try clear MI. rename MI1 into MI. rename XO1 into XO. rename Lows1 into Lows. rename ows1 into ows'.

zstep. rewrite ?Efs. rewrite ?(sx32_lit 80) by lia. zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia.
zstep. zstep. zstep. zstep. zstep. zstep.
pose proof (f32_split rsegs _ _ ows' (Z.to_nat (320 + 80 * sub)) ltac:(rewrite Lows; lia) XO) as [XA XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (320 + 80 * sub)) ows') 80%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [YS XC]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub)) + 4 * Z.of_nat 80%nat) with (OUT + 1280 + 320 * sub + 320) in XC by lia.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub))) with (OUT + 1280 + 320 * sub) in YS by lia.
set (oA := firstn (Z.to_nat (320 + 80 * sub)) ows') in *.
assert (LoA : Z.of_nat (length oA) = 320 + 80 * sub) by (subst oA; rewrite length_firstn, Lows; lia).
set (ys := firstn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows')) in *.
assert (Lys : length ys = 80%nat) by (subst ys; rewrite length_firstn, length_skipn, Lows; lia).
set (oC := skipn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows')) in *.
assert (LoC : Z.of_nat (length oC) = 2000 - 80 - (320 + 80 * sub)) by (subst oC; rewrite !length_skipn, Lows; lia).
clearbody oA ys oC. clear XO Lows.
pose proof (f32_split rsegs _ _ (sj_msp j) 8%nat ltac:(rewrite Lmsp; lia) BMSP) as [BM1 BM2]. clear BMSP.
replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) in BM2 by lia.
assert (LM1 : length (firstn 8 (sj_msp j)) = 8%nat) by (rewrite length_firstn, Lmsp; reflexivity).
assert (LM2 : length (skipn 8 (sj_msp j)) = 8%nat) by (rewrite length_skipn, Lmsp; reflexivity).
remember (OUT + 1280 + 320 * sub) as PY eqn:EPY.
call ((h_iir _ (ih_hyps _ _ IH)) (a_exc a) (a_iq a) PY (a_msp a) 80 lo (sj_exc j) (sj_iq j) ys (firstn 8 (sj_msp j)) (Z_to_bv 64 0));
[ exact BEXC
| lia
| exact BIQ
| exact Liq
| exact BM1
| exact LM1
| right; split; [subst PY; unfold apart; lia | split; [exact YS | exact Lys]]
| lia
| subst PY; unfold apart; lia
| subst PY; unfold apart; lia
| unfold apart; slia
| unfold apart; slia
| lia
| lia
| lia
| lia
| subst PY; lia
| subst PY; lia
| lia
| lia
| rewrite USPX; exact ST
| rewrite USPX; unfold IIR_DEPTH; lia
| unfold NB_GLOBALS_TOP; lia
| rewrite USPX; lia
| rewrite USPX; unfold apart; lia
| subst PY; rewrite USPX; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USPX; unfold apart; lia
| rewrite USPX; unfold apart; lia
| rfl
| rfl
| rfl
| rfl
| rfl
| rfl
| rfl
| exact MI | exact FRM | ].
cbv beta delta [callR]. clear FRM. try clear ST. try clear YS; try clear Lys; try clear BM1; try clear LM1. name_post. rename FRMc into FRM. try rename STc into ST. rewrite ?USPX in ST.
match goal with H : rw_cells _ _ PY (f32 ?w), L : length ?w = _ |- _ => rename H into YS; rename L into Lys; rename w into ys2 end.
match goal with H : rw_cells _ _ (a_msp a) (f32 ?w), L : length ?w = _ |- _ => rename H into BM1; rename L into LM1; rename w into msp1 end.
change (Z.to_nat 80) with 80%nat in Lys.
subst PY.
pose proof (f32_join rsegs _ _ _ _ XA ltac:(replace (OUT + 4 * Z.of_nat (length oA)) with (OUT + 1280 + 320 * sub) by lia; exact YS)) as XAY.
pose proof (f32_join rsegs _ _ _ _ XAY ltac:(rewrite length_app, Lys; replace (OUT + 4 * Z.of_nat (length oA + 80%nat)) with (OUT + 1280 + 320 * sub + 320) by lia; exact XC)) as XO.
clear XA XAY YS XC.
assert (Lows : length ((oA ++ ys2) ++ oC) = 2000%nat) by (rewrite !length_app, Lys; lia).
set (ows2 := (oA ++ ys2) ++ oC) in *. clearbody ows2.
pose proof (f32_join rsegs _ _ _ _ BM1 ltac:(rewrite LM1; replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) by lia; exact BM2)) as BMSP. clear BM1 BM2.
assert (Lmsp' : length (msp1 ++ skipn 8 (sj_msp j)) = 16%nat) by (rewrite length_app, LM1, LM2; reflexivity).
set (mspN := msp1 ++ skipn 8 (sj_msp j)) in *. clearbody mspN.

zstep. zstep. rewrite ?Efs. rewrite ?(sx32_lit 80) by lia. zstep. rewrite (lts_zero_lit 80) by lia. if_false_x.
zstep. zstep. zstep. replace (Z.shiftl 80 2) with 320 by reflexivity.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (P2f : rw_cells rsegs mm (S + 40) (sbp_ptrs s1 a OUT)) by (unfold sbp_ptrs; exact P2) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (cp1_loop X S (usp + -832) (a_exc a) 320 OUT s1 a 80%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (sj_exc j) vexc [] [] (a_exc a) (usp + -832) _);
[ cbn [length]; lia | lia | reflexivity | lia
| cbn [length]; lia | cbn [length]; lia | weq
| reflexivity | lia | lia | lia | lia | lia | lia | lia
| unfold sbp_ptrs; cbn [cells_size csize Nat.add]; lia
| unfold apart; lia
| unfold apart, sbp_ptrs; cbn [cells_size csize Nat.add]; slia
| weq | weq
| exact MI | apply munch_refl | apply wmono_refl | exact P2f
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at BEXC
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC | ] end.
cbv beta. try clear BEXC; try clear VEXC; try clear P2f. name_post. try rename STc into ST. try rename FRMc into FRM. cbn [app] in *.
match goal with H : rw_cells _ _ (a_exc a) (f32 ?w), L : length ?w = _ |- _ => rename H into BEXC; rename L into LexcN; rename w into excN end.
match goal with H : rw_cells _ _ (usp + -832) (f32 vexc) |- _ => rename H into VEXC end.
match goal with H : rw_cells _ _ (S + 40) (sbp_ptrs _ _ _) |- _ => rename H into P2f end.

zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia. zstep. rewrite (lts_zero_lit 8) by lia. if_false_x.
zstep. zstep. replace (Z.shiftl 8 2) with 32 by reflexivity.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (cp2_loop X S (usp + -512) (a_iq a) 32 OUT s1 a 8%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (sj_iq j) vak [] [] (a_iq a) (usp + -512) _);
[ cbn [length]; rewrite Liq; lia | rewrite Lvak, Liq; reflexivity | reflexivity | rewrite Liq; lia
| cbn [length]; lia | cbn [length]; lia | weq
| reflexivity | lia | lia | lia | lia | lia | lia | lia
| unfold sbp_ptrs; cbn [cells_size csize Nat.add]; lia
| unfold apart; lia
| unfold apart, sbp_ptrs; cbn [cells_size csize Nat.add]; slia
| weq
| exact MI | apply munch_refl | apply wmono_refl | exact P2f
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at BIQ
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VAK | ] end.
cbv beta. try clear BIQ; try clear VAK; try clear P2f. name_post. try rename STc into ST. try rename FRMc into FRM. cbn [app] in *.
match goal with H : rw_cells _ _ (a_iq a) (f32 ?w), L : length ?w = _ |- _ => rename H into BIQ; rename L into LiqN; rename w into iqN end.
match goal with H : rw_cells _ _ (usp + -512) (f32 vak) |- _ => rename H into VAK end.
repeat match goal with H : rw_cells _ _ (S + 40) (sbp_ptrs _ _ _) |- _ => unfold sbp_ptrs in H end.

zstep. zstep.
call ((h_rms _ (ih_hyps _ _ IH)) (a_exc a) 80 excN); [exact BEXC | rewrite LexcN; reflexivity | lia | lia | lia | weq | weq | exact MI | exact FRM | ].
cbv beta delta [callR]. clear FRM. try clear BEXC; try clear LexcN. name_post. rename FRMc into FRM. try rename STc into ST.
match goal with H : rw_cells _ _ (a_exc a) (f32 ?w), L : length ?w = _ |- _ => rename H into BEXC; rename L into LexcN; rename w into excM end.
change (Z.to_nat 80) with 80%nat in LexcN.

zstep. zstep. zstep. zstep. zstep. zstep.
zstep. ntk. zstep. ntk. zstep. ntk. zstep. zstep. ntk.
pose proof (f32_split rsegs _ _ (sj_er j) (Z.to_nat sub) ltac:(rewrite Ler; lia) BER) as [QER1 QER2]. clear BER.
replace (a_er a + 4 * Z.of_nat (Z.to_nat sub)) with (a_er a + sub * 4) in QER2 by lia.
assert (LER1 : Z.of_nat (length (firstn (Z.to_nat sub) (sj_er j))) = sub) by (rewrite length_firstn, Ler; lia).
destruct (skipn (Z.to_nat sub) (sj_er j)) as [|er0 errest] eqn:EERR.
{ exfalso. pose proof (f_equal (@length _) EERR) as LL. rewrite length_skipn, Ler in LL. cbn in LL. lia. }
assert (LERR : Z.of_nat (length errest) = 3 - sub).
{ pose proof (f_equal (@length _) EERR) as LL. rewrite length_skipn, Ler in LL. cbn in LL. lia. }
clear EERR. set (erdone := firstn (Z.to_nat sub) (sj_er j)) in *. clearbody erdone.
remember (a_er a + sub * 4) as ERA eqn:EERA.
pose proof (rw_cells_bound _ _ _ _ QER2) as BQER2. rewrite cells_size_f32 in BQER2. cbn [length] in BQER2. rewrite f32_cons in QER2.
lstep.
lazymatch type of QER2 with rw_cells _ _ _ (C4 ?v :: f32 errest) =>
rewrite <- (f32_cons v errest) in QER2;
pose proof (f32_join rsegs _ _ _ _ QER1 ltac:(replace (a_er a + 4 * Z.of_nat (length erdone)) with ERA by lia; exact QER2)) as BER end.
lazymatch type of BER with rw_cells _ _ _ (f32 ?erl) => set (ernew := erl) in BER end.
assert (Ler' : length ernew = 4%nat) by (subst ernew; rewrite length_app; cbn [length]; lia). clearbody ernew.
clear QER1 QER2. subst ERA.
zstep. ntk.
zstep.
pose proof (f32_as_blob _ _ _ 80%nat VEXC Lvexc) as INB. clear VEXC. change (Z.to_nat (4 * Z.of_nat 80%nat)) with 320%nat in INB.
release_frame INB ST (usp + -512).
zstep. zstep. zstep. ntk.
zstep. rewrite Inb1. rewrite (sx32_lit 4) by lia. zstep. rewrite Inb1. rewrite (sx32_lit 4) by lia.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
destruct (Z.eq_dec sub 3) as [E3 | NE3].
-
rewrite (lts_ge_false' (sub + 1) 4) by lia. zstep.
apply evt_done. right. split; [exact E3|]. unfold at_T.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _, _, _, _, _, _.
exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) excM (sj_oq j) iqN mspN (sj_pg j) ernew).
exists ows2, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
repeat match goal with |- _ /\ _ => split end; first [ reflexivity | assumption ].
-
rewrite (lts_true' (sub + 1) 4) by lia.
apply evt_done. left. split; [lia|]. unfold at_L.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _, _, _.
exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) excM (sj_oq j) iqN mspN (sj_pg j) ernew).
exists ows2, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
repeat match goal with |- _ /\ _ => split end; first [ reflexivity | assumption | lia ].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
