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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1n8 X1ho X1hm X1hu X1ht X1ih X1nr X1mc X1mv X1mb X1ma X1mw X1mr X1mf X1mg X1mh X1mi.
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

#[using="RCEIL k IH"] Lemma sbL2i_40 : FS = 40 -> forall low dtx s1 r sub b ms p, sm_innovation_unquant (smr_sm r) = Some (InnovSplitCbShapeSignUnquant p) ->
at_L1_40 X low dtx s1 r sub b ms -> evt rsegs (at_L2_40 X low dtx s1 r sub (sbsub_bits (smr_sm r) b)) ms.
Proof.
intros EFS low dtx s1 r sub b ms p HKI AT.
first [ sf_destruct 40%nat AT as Fx fc m kk xra xa0 xs11 j ows stb fr vpi ver vq viq vak vexc -> FRM CTX ST FRA LFR F104e F112e SAT Hsub Exs11 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak VEXC Lvexc | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & -> & FRM & CTX & ST & FRA & LFR & F104e & F112e & SAT & Hsub & Exs11 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak & VEXC & Lvexc) ].
pose proof LFR as sfP_; first [ sf_destruct 16%nat sfP_ as F0e F8e F16e F24e F32e F40e F48e F56e F64e F72e F80e F88e F96e F120e Fdtx DTX01 | sf_fb; destruct sfP_ as (F0e & F8e & F16e & F24e & F32e & F40e & F48e & F56e & F64e & F72e & F80e & F88e & F96e & F120e & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-592) ltac:(lia)) as USPX.
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

pose proof (sb_smrecs_facts r INr) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ INNOVD DCB | sf_fb; destruct sfP_ as (_ & _ & INNOVD & DCB) ].
destruct INNOVD as [[X0 _] | (p' & E' & POK & PARlo & PARhi)]; [rewrite HKI in X0; discriminate|].
rewrite HKI in E'. injection E' as Ep. subst p'.
unfold RTABLES_LO in PARlo. unfold RTABLES_HI in PARhi.

zstep. if_false_x.

zstep. zstep. rewrite F120e. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 4); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 4) in *. cbn [fst snd] in *. after_bits REP (ub b 4).
pose proof (ub_ok b 4 BOK ltac:(lia)) as BOK4. pose proof (ub_same b 4) as (U4sz & U4o & U4c).
pose proof (speex_bits_unpack_unsigned_ok b 4 _ _ BOK ltac:(lia) (unpack_eta b 4)) as (_ & Q16 & _).
match goal with H : ?v = Z_to_bv 64 (uv b 4) |- _ => subst v end.
name_post. try rename FRMc into FRM. try rename STc into ST. try rewrite USPX in ST.

zstep. rewrite (Z.shiftl_mul_pow2 (uv b 4) 2) by lia. change (2 ^ 2) with 4. zstep. zstep. zstep.
destruct (gcqb_cell _ (uv b 4) MI ltac:(lia)) as (tbs & Ltbs & TRO).
replace (78708 + uv b 4 * 4) with (78708 + 4 * uv b 4) by lia.
remember (78708 + 4 * uv b 4) as TQ eqn:ETQ.
step. subst TQ. clear TRO.

zstep. zstep. zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. zstep. zstep. zstep. zstep. if_true_x.

zstep. rewrite F40e. zstep. zstep. rewrite F64e. zstep.
pose proof (f32_split rsegs _ _ ver (Z.to_nat sub) ltac:(rewrite Lver; lia) VER) as [_ VER2].
replace (usp + -336 + 4 * Z.of_nat (Z.to_nat sub)) with (usp + -336 + sub * 4) in VER2 by lia.
destruct (skipn (Z.to_nat sub) ver) as [|er0 errest] eqn:EER.
{ exfalso. pose proof (f_equal (@length _) EER) as LL. rewrite length_skipn, Lver in LL. cbn in LL. lia. }
clear EER. rewrite f32_cons in VER2. remember (usp + -336 + sub * 4) as ERA eqn:EERA.
zstep. clear VER2. subst ERA.

zstep. fp_join 0x28560.
{ zstep. if_cases Kc; [apply evt_done; eexists; reflexivity | zstep; apply evt_done; eexists; reflexivity]. }
cbv beta. intros ms1 (Fx1 & ->).

zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ TR TB4 _ | sf_fb; destruct sfP_ as (_ & _ & TR & TB4 & _) ] end.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. clear RD. rewrite SPE.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC. cbn [innov_entry] in SMC.
unfold A_split_cb_shape_sign_unquant, A_noise_codebook_unquant in SMC.

zstep. zstep.

zstep. zstep. zstep. zstep. rewrite F120e. zstep. zstep. rewrite F88e. zstep.
lazymatch goal with P : rw_cells _ _ (S + 132) [C4 ?sd] |- _ =>
call ((h_innov _ (ih_hyps _ _ IH) p POK) A D (ub b 4) (usp + -592) (S + 132) (smr_innov_par r) lo vexc sd (Z_to_bv 64 0));
[ exact REP | assumption | exact VEXC | exact Lvexc | exact P
| exact (TB4 r p INr HKI)
| unfold NB_GLOBALS_TOP; lia | unfold NB_GLOBALS_TOP; lia
| rewrite USPX; exact ST | rewrite USPX; unfold INNOV_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USPX; lia
| rewrite USPX; unfold apart; lia
| rewrite USPX; unfold apart; lia
| rewrite USPX; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USPX, U4sz, BSZ; unfold apart; lia
| unfold apart; lia
| unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite U4sz, BSZ; unfold apart; lia
| unfold apart, BITS_SIZEOF; lia
| rewrite U4sz, BSZ; unfold apart; slia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact MI | exact FRM | ] end.
cbv beta delta [callR]. clear FRM. try clear VEXC; try clear Lvexc. try clear TB4; try clear SMC; try clear TR. name_post. rename FRMc into FRM. rename STc into ST. rewrite USPX in ST.
match goal with H : rw_cells _ _ (usp + -592) (f32 ?w), L : length ?w = 40%nat |- _ => rename H into VEXC; rename L into Lvexc end.
match goal with H : rw_cells _ _ (S + 132) [C4 ?sd] |- _ => rename H into P4 end.
after_bits REP (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4)).
match goal with H : bits_ok (innov_bits _ (ub b 4)) |- _ => rename H into BOKi end.

pose proof (innov_bits_same (InnovSplitCbShapeSignUnquant p) (ub b 4)) as (UIsz & UIo & UIc). rewrite U4sz in UIsz. rewrite U4o in UIo. rewrite U4c in UIc.

zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. zstep. zstep. zstep.
lazymatch type of VEXC with rw_cells _ _ _ (f32 ?is1) =>
call ((h_smul _ (ih_hyps _ _ IH)) (usp + -592) is1); [exact VEXC | exact Lvexc | reflexivity | reflexivity | reflexivity | exact MI | exact FRM | ] end.
cbv beta delta [callR]. clear FRM. try clear VEXC; try clear Lvexc. name_post. rename FRMc into FRM. try rename STc into ST.
match goal with H : rw_cells _ _ (usp + -592) (f32 ?w), L : length ?w = 40%nat |- _ => rename H into VEXC; rename L into Lvexc end.

zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ TR TB4 _ | sf_fb; destruct sfP_ as (_ & _ & TR & TB4 & _) ] end.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. clear RD. rewrite SPE.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC. cbn [innov_entry] in SMC.
unfold A_split_cb_shape_sign_unquant, A_noise_codebook_unquant in SMC.

zstep. rewrite (sx32_lit (sm_double_codebook (smr_sm r))) by lia. clear SMC TR TB4.
zstep. rewrite Efs. rewrite (zx32_small 40) by lia.
zstep. rewrite (eqb_zero_lit (sm_double_codebook (smr_sm r))) by lia.
destruct DCB as [ED | [ED _]]; rewrite ED.
-
if_true_x.
replace (sbsub_bits (smr_sm r) b) with (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4)) by (unfold sbsub_bits; rewrite HKI, ED; reflexivity).
apply evt_done. unfold at_L2_40.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, xs11.
lazymatch goal with P : rw_cells _ _ (S + 132) [C4 ?sd] |- _ =>
exists (SBJ (sj_last_ener j) sd (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) end.
exists ows, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
lazymatch goal with H : rw_cells _ _ (usp + -592) (f32 ?w) |- _ => exists w end.
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split. { exact LFR. }
cbn [f_104 f_112]. split; [exact F104e|]. split; [exact F112e|].
split; [exact SAT|]. split; [exact Hsub|]. split; [exact Exs11|].
split; [exact VPI|]. split; [exact Lvpi|]. split; [exact VER|]. split; [exact Lver|]. split; [exact VQ|]. split; [exact Lvq|].
split; [exact VIQ|]. split; [exact Lviq|]. split; [exact VAK|]. split; [exact Lvak|].
split; [assumption | first [assumption | lia]].

-
if_false_x.

zstep. zstep. zstep. zstep. zstep. replace (Z.land (Z.shiftl 40 2 + 15) (-16)) with 160 by reflexivity. zstep.
match goal with |- context [Z_to_bv 64 (usp + -592 + ?e)] => replace (usp + -592 + e) with (usp + -752) by lia end.

zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -592 + ?e)] => replace (usp + -592 + e) with (usp + -4688) by lia end.
probe_store ST (usp + -4688).
zstep. rewrite (lts_ge_false' (usp + -752) (usp + -4688)) by lia. zstep.
carve_frame 160%nat ST.
pose proof (USPk _ _ IH (-752) ltac:(lia)) as USPY.

zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. zstep. zstep. zstep.
call (nmemset_specZ (usp + -752) 160 0); [exact FR | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try clear FR. try rename MI0 into MI.
match goal with H : rw_cells _ _ (usp + -752) [CB _ _] |- _ =>
change (Z.to_nat 160) with (4 * 40)%nat in H at 1; destruct (rw_cells_CB_f32 rsegs _ _ 40%nat _ H) as (in2 & Lin2 & VIN2); clear H end.

zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ TR TB4 _ | sf_fb; destruct sfP_ as (_ & _ & TR & TB4 & _) ] end.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. clear RD. rewrite SPE.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC. cbn [innov_entry] in SMC.
unfold A_split_cb_shape_sign_unquant, A_noise_codebook_unquant in SMC.

zstep. zstep.

zstep. zstep. zstep. rewrite F120e. zstep. zstep. zstep. rewrite F88e. zstep.
lazymatch goal with P : rw_cells _ _ (S + 132) [C4 ?sd] |- _ =>
call ((h_innov _ (ih_hyps _ _ IH) p POK) A D (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4)) (usp + -752) (S + 132) (smr_innov_par r) lo in2 sd (Z_to_bv 64 0));
[ exact REP | assumption | exact VIN2 | exact Lin2 | exact P
| exact (TB4 r p INr HKI)
| unfold NB_GLOBALS_TOP; lia | unfold NB_GLOBALS_TOP; lia
| rewrite USPY; exact ST | rewrite USPY; unfold INNOV_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USPY; lia
| rewrite USPY; unfold apart; lia
| rewrite USPY; unfold apart; lia
| rewrite USPY; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USPY, UIsz; unfold apart; lia
| unfold apart; lia
| unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite UIsz; unfold apart; lia
| unfold apart, BITS_SIZEOF; lia
| rewrite UIsz; unfold apart; slia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact MI | exact FRM | ] end.
cbv beta delta [callR]. clear FRM. try clear VIN2; try clear Lin2. try clear TB4; try clear SMC; try clear TR. name_post. rename FRMc into FRM. rename STc into ST. rewrite USPY in ST.
match goal with H : rw_cells _ _ (usp + -752) (f32 ?w), L : length ?w = 40%nat |- _ => rename H into VIN2; rename L into Lin2 end.
match goal with H : rw_cells _ _ (S + 132) [C4 ?sd] |- _ => rename H into P4 end.
after_bits REP (innov_bits (InnovSplitCbShapeSignUnquant p) (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4))).
match goal with H : bits_ok (innov_bits _ (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4))) |- _ => rename H into BOKii end.

pose proof (innov_bits_same (InnovSplitCbShapeSignUnquant p) (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4))) as (UJsz & UJo & UJc).
rewrite UIsz in UJsz. rewrite UIo in UJo. rewrite UIc in UJc.

zstep. zstep. zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. zstep. zstep. zstep.
lazymatch type of VIN2 with rw_cells _ _ _ (f32 ?is1) =>
call ((h_smul _ (ih_hyps _ _ IH)) (usp + -752) is1); [exact VIN2 | exact Lin2 | reflexivity | reflexivity | reflexivity | exact MI | exact FRM | ] end.
cbv beta delta [callR]. clear FRM. try clear VIN2; try clear Lin2. name_post. rename FRMc into FRM. try rename STc into ST.
match goal with H : rw_cells _ _ (usp + -752) (f32 ?w), L : length ?w = 40%nat |- _ => rename H into VIN2; rename L into Lin2 end.

zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. rewrite (lts_zero_lit 40) by lia. if_false_x.
zstep. zstep. zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of VEXC with rw_cells _ _ _ (f32 ?ev) => lazymatch type of VIN2 with rw_cells _ _ _ (f32 ?iv) =>
call (dadd_loop X (usp + -592) (usp + -752) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc ev iv [] []);
[ cbn [length]; lia | lia | reflexivity | lia
| cbn [length]; lia | cbn [length]; lia | lia
| lia | lia | unfold apart; lia
| exact MI | apply munch_refl | apply wmono_refl | exact FRM
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC | rewrite f32_nil; apply rw_cells_nil; lia | exact_at VIN2 | ] end end end.
cbv beta. clear FRM. try clear VEXC; try clear Lvexc; try clear VIN2; try clear Lin2. name_post. rename FRMc into FRM. try rename STc into ST.
match goal with H : rw_cells _ _ (usp + -592) (f32 ?w), L : length ?w = 40%nat |- _ => rename H into VEXC; rename L into Lvexc end.
match goal with H : rw_cells _ _ (usp + -752) (f32 ?w), L : length ?w = 40%nat |- _ =>
pose proof (f32_as_blob _ _ _ 40%nat H L) as INB; clear H; clear L; change (Z.to_nat (4 * Z.of_nat 40%nat)) with 160%nat in INB end.

zstep. release_frame INB ST (usp + -592).

zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. rewrite F32e. zstep. rewrite F96e. zstep.
replace (sbsub_bits (smr_sm r) b) with (innov_bits (InnovSplitCbShapeSignUnquant p) (innov_bits (InnovSplitCbShapeSignUnquant p) (ub b 4)))
by (unfold sbsub_bits; rewrite HKI, ED; reflexivity).
apply evt_done. unfold at_L2_40.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, xs11.
lazymatch goal with P : rw_cells _ _ (S + 132) [C4 ?sd] |- _ =>
exists (SBJ (sj_last_ener j) sd (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) end.
exists ows, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
lazymatch goal with H : rw_cells _ _ (usp + -592) (f32 ?w) |- _ => exists w end.
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

#[using="RCEIL k IH"] Lemma sbL2_40 : FS = 40 -> forall low dtx s1 r sub b ms,
at_L1_40 X low dtx s1 r sub b ms -> evt rsegs (at_L2_40 X low dtx s1 r sub (sbsub_bits (smr_sm r) b)) ms.
Proof.
intros EFS low dtx s1 r sub b ms AT.
assert (SAT : sb_smrec_at mo (sbd_submodeID s1) = Some r) by (first [ sf_destruct 27%nat AT as Fx fc m kk xra xa0 xs11 j ows stb fr vpi ver vq viq vak vexc _ _ _ _ _ _ _ _ SAT _ | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & _ & _ & _ & _ & _ & _ & _ & _ & SAT & _) ]; exact SAT).
destruct (sb_smrec_at_some mo _ r SAT) as (INr & _).
pose proof (sb_smrecs_facts r INr) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ INNOVD _ | sf_fb; destruct sfP_ as (_ & _ & INNOVD & _) ].
destruct INNOVD as [[HKI _] | (p & HKI & _)].
- replace (sbsub_bits (smr_sm r) b) with (ub b 5) by (unfold sbsub_bits; rewrite HKI; reflexivity).
eapply sbL2f_40; eassumption.
- eapply sbL2i_40; eassumption.
Qed.
#[using="RCEIL k IH"] Lemma sbL2_80 : FS = 80 -> forall low dtx s1 r sub b ms,
at_L1_80 X low dtx s1 r sub b ms -> evt rsegs (at_L2_80 X low dtx s1 r sub (sbsub_bits (smr_sm r) b)) ms.
Proof.
intros EFS low dtx s1 r sub b ms AT.
assert (SAT : sb_smrec_at mo (sbd_submodeID s1) = Some r) by (first [ sf_destruct 27%nat AT as Fx fc m kk xra xa0 xs11 j ows stb fr vpi ver vq viq vak vexc _ _ _ _ _ _ _ _ SAT _ | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & _ & _ & _ & _ & _ & _ & _ & _ & SAT & _) ]; exact SAT).
first [ pose proof (sb_smrec_at_some mo _ r SAT) as sfP_; sf_destruct 6%nat sfP_ as INr _ _ _ _ UWBN | sf_fb; destruct (sb_smrec_at_some mo _ r SAT) as (INr & _ & _ & _ & _ & UWBN) ].
pose proof (UWBN (proj1 (FS80_mode k X IH EFS))) as HKI.
replace (sbsub_bits (smr_sm r) b) with (ub b 5) by (unfold sbsub_bits; rewrite HKI; reflexivity).
eapply sbL2f_80; eassumption.
Qed.

End Seg.
