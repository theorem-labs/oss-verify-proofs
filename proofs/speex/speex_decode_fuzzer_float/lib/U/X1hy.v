(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1g6 X1g7 X1g0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Seg.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable notify : list Z -> X1qx.M PState unit.
Variable STR_TOP : Z.
Variable X : nbinv ptr.
Hypothesis NH : nb_hyps notify STR_TOP X.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation st0 := (x_st0 X). Local Notation b0 := (x_b0 X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation unpackM := (@bits_unpack_unsigned_M PState ptr).
Local Notation advanceM := (@bits_advance_M PState ptr).
Local Notation remainingM := (@bits_remaining_M PState ptr).
Local Notation HN := (h_notify _ _ _ NH).
Local Notation HIB := (h_inband _ _ _ NH).
Local Notation HUH := (h_userh _ _ _ NH).

#[using="STR_TOP NH"] Lemma nbA_tail : forall fuel (s : PState) b ms,
(forall b' ms', at_A X 0x20d54 b' ms' -> implM rsegs (nb_mode_search notify unpackM advanceM remainingM fuel st0 b') s (QA X s) ms') ->
at_A X 0x20cf8 b ms ->
implM rsegs (nbs_tail notify fuel st0 b) s (QA X s) ms.
Proof.
intros fuel s b ms IH AT.
first [ sf_destruct 22%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK.
rewrite E48, E80, E88, E112, E120 in FL.
unfold nbs_tail. eapply implM_bind_run; [reflexivity|]. cbv beta.

apply implM_from_evt.
zstep. zstep. call (X1g6.speex_bits_remaining_spec A D b); [exact REP | exact BOK | exact MI |].
after_bits REP b. match goal with H : ?v = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst v end.
zstep. if_cases K4; zify_cond K4; rewrite ?signed_lit_small in K4 by lia.
2:{
zstep. apply evt_done. replace (speex_bits_remaining b <? 4) with true by (symmetry; apply Z.ltb_lt; lia).
apply implM_ret. close_X. }
replace (speex_bits_remaining b <? 4) with false by (symmetry; apply Z.ltb_ge; lia).

zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 4); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 4) in *. cbn [fst snd] in *. after_bits REP (ub b 4).
match goal with H : ?v = Z_to_bv 64 (uv b 4) |- _ => subst v end.
pose proof (speex_bits_unpack_unsigned_ok b 4 _ _ BOK ltac:(lia) (unpack_eta b 4)) as sfP_; first [ sf_destruct 6%nat sfP_ as BOK1 Hm4 _ _ Hbs4 _ | sf_fb; destruct sfP_ as (BOK1 & Hm4 & _ & _ & Hbs4 & _) ].
apply evt_done. eapply implM_bind_run; [unfold bits_unpack_unsigned_M, mret; rewrite unpack_eta; reflexivity|]. cbv beta iota.
apply implM_from_evt.
zstep. if_cases K13; zify_cond K13.
{
zstep. zstep. zstep. zstep. zstep.
replace (ret_pc (Z_to_bv 64 A_speex_default_user_handler)) with (Z_to_bv 64 A_speex_default_user_handler)
by (unfold A_speex_default_user_handler; symmetry; apply ret_pc_even; [lia| reflexivity]).
call (HUH A D (ub b 4) ST lo); [exact REP | exact BOK1 | rewrite USP; exact STK | rewrite USP; unfold USERH_DEPTH; lia | exact T0
| rewrite USP; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP, Hbs4, BSZ; unfold apart; pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | reflexivity | reflexivity | exact MI | exact FRM | ].
after_bits REP (user_handler_bits (ub b 4)). rewrite USP in *.
zstep. if_true. apply evt_done.
replace (uv b 4 =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 14) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 13) with true by (symmetry; apply Z.eqb_eq; lia).
eapply implM_bind_run; [apply user_handler_run|]. cbv beta iota. cbn [Z.eqb negb].
pose proof (user_handler_bits_size (ub b 4)) as BSZ1.
apply IH. close_A. }
zstep. zstep. if_cases K14; zify_cond K14.
2:{
zstep. zstep. zstep. if_cases K15; zify_cond K15.
{
apply evt_done. replace (uv b 4 =? 15) with true by (symmetry; apply Z.eqb_eq; lia).
apply implM_ret. close_X. }
zstep. zstep. if_cases K9; zify_cond K9; rewrite ?signed_lit_small in K9 by lia.
{
pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ TG TS _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & TG & TS & _) ]. unfold NB_GOT_STDERR, NB_STDERR_VAR, NB_RSTDERR in TG, TS.
do 9 zstep.
apply evt_done.
replace (uv b 4 =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 14) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 13) with false by (symmetry; apply Z.eqb_neq; lia).
replace (8 <? uv b 4) with true by (symmetry; apply Z.ltb_lt; lia).
clear TG TS.
eapply implM_bind.
{ eapply HN with (lo := lo); try reflexivity.
- apply cstr_invalid_mode; [exact MI| exact T0| exact (h_strtop _ _ _ NH)].
- eapply ctx_serr; eassumption.
- rewrite USP. exact STK.
- rewrite USP. unfold NB_FPRINTF_DEPTH. lia.
- exact T0.
- rewrite USP. lia.
- eapply ctx_sspc; eassumption.
- exact MI.
- assumption. }
cbv beta. intros [] s2 ms2 PN.
first [ sf_destruct 28%nat PN as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 Ft fc2 m2 -> MUn WMn MI2 FRM2 _ ST2 SE2 SSP2 -> | sf_fb; destruct PN as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & Ft & fc2 & m2 & -> & MUn & WMn & MI2 & FRM2 & _ & ST2 & SE2 & SSP2 & ->) ].
rewrite USP in MUn, ST2.
rewrite <- (nbW_eq X) in MU. apply (munch_nbW_full X) in MU. unfold nb_W, NBSTATE_SIZEOF, BITS_SIZEOF, NB_RSTDERR in MU. unfold NB_RSTDERR in MUn.
lazymatch type of MUn with munch _ ?m1 _ => transport_after_call rsegs m1 m2 MUn WMn end.
clear MUn WMn.
replace (ret_pc (Z_to_bv 64 140272)) with (Z_to_bv 64 140272) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply implM_from_evt. zstep. zstep. apply evt_done.
apply implM_ret. close_X. }

zstep. zstep.
apply evt_done.
replace (uv b 4 =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 14) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 13) with false by (symmetry; apply Z.eqb_neq; lia).
replace (8 <? uv b 4) with false by (symmetry; apply Z.ltb_ge; lia).
apply implM_ret. apply evt_done. split; [reflexivity|]. cbv beta iota. close_B. }
zstep. zstep. zstep.
pose proof CBS as sfP_; first [ sf_destruct 4%nat sfP_ as js Ljs Fjs Ecbs | sf_fb; destruct sfP_ as (js & Ljs & Fjs & Ecbs) ].
lazymatch type of P15 with rw_cells _ ?mc _ _ =>
assert (CBH : rw_cells rsegs mc (ST + 2256) (cbs_cells 16 A_speex_std_stereo_request_handler STEREO (nb_stereo_cb st0) js)) end.
{ eapply rw_cells_recast; [exact P15 | apply cbs_cells_wf; exact Fjs | cbn [cells_bytes cbytes]; rewrite app_nil_r; symmetry; exact Ecbs]. }
call (HIB (nb_stereo_cb st0) A D (ub b 4) (ST + 2256) ST STEREO lo js sws);
[ exact REP | exact BOK1 | exact CBH | exact Ljs | exact Fjs | exact XS | exact Lsws
| rewrite USP; exact STK | rewrite USP; unfold INBAND_DEPTH; lia | exact T0
| rewrite USP; unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP; unfold apart; pose proof (lay_STEREO_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP, Hbs4, BSZ; unfold apart; pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart, BITS_SIZEOF; pose proof (lay_ST_A _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; pose proof (lay_ST_STEREO _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart, BITS_SIZEOF; pose proof (lay_A_STEREO _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite Hbs4, BSZ; unfold apart; pose proof (lay_D_STEREO _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | reflexivity | reflexivity | exact MI | assumption
| lia | pose proof (h_stal _ _ _ NH); lia | lia | exact (h_ster4 _ _ _ NH) | ].
try clear CBH. after_bits REP (inband_bits (nb_stereo_cb st0) (ub b 4)). rewrite USP in *.
zstep. if_true. apply evt_done.
replace (uv b 4 =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (uv b 4 =? 14) with true by (symmetry; apply Z.eqb_eq; lia).
eapply implM_bind_run; [apply inband_run|]. cbv beta iota. cbn [Z.eqb negb].
pose proof (inband_bits_size (nb_stereo_cb st0) (ub b 4)) as BSZ1.
apply IH. close_A.
Qed.
End Seg.
