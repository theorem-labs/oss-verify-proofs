(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1hy X1g6 X1g7 X1g0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma wb_skip_read : forall m i, mem_inv rsegs m -> 0 <= i < 8 ->
ov_read_bytes rsegs m (wa (A_wb_skip_table + 4 * i)) 4 = Some (le4 (Z_to_bv 64 (znth wb_skip_table i))).
Proof.
intros m i MI Hi. unfold A_wb_skip_table.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
match goal with |- ov_read_bytes _ _ (wa ?a) 4 = Some (le4 (Z_to_bv 64 ?v)) =>
let av := eval vm_compute in a in let vv := eval vm_compute in v in
change a with av; change v with vv;
pose proof (ro_cells_image rsegs m av (le4 (Z_to_bv 64 vv)) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RO;
exact (ro_cells_read_at rsegs m av _ 0%nat _ 4 _ RO ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
end.
Qed.
Lemma wb_skip_range : forall i, 0 <= i < 8 -> 0 <= znth wb_skip_table i <= 352.
Proof.
intros i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
match goal with |- 0 <= ?x <= 352 => let v := eval vm_compute in x in change x with v end; lia.
Qed.

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

#[using="notify STR_TOP NH"] Lemma nbA_skip : forall (pc : Z) (b : bits_st ptr) Q,
(pc = 0x20c4c \/ pc = 0x20ca8) ->
4 <= speex_bits_remaining b -> 1 <= bits_pos b ->
(forall ms', at_A X (pc + 60) (skip_bits b) ms' -> evt rsegs Q ms') ->
forall ms, at_A X pc b ms -> evt rsegs Q ms.
Proof.
intros pc b Q Hpc HR4 HP1 K ms AT.
first [ sf_destruct 22%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK.
rewrite E48, E80, E88, E112, E120 in FL.
assert (PCS : Z_to_bv 64 pc = Z_to_bv 64 0x20c4c /\ pc + 60 = 0x20c88 \/ Z_to_bv 64 pc = Z_to_bv 64 0x20ca8 /\ pc + 60 = 0x20ce4)
by (destruct Hpc as [-> | ->]; [left|right]; split; reflexivity).
destruct PCS as [[-> EK] | [-> EK]]; rewrite EK in K; clear EK Hpc.
{
zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 3); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 3) in *. cbn [fst snd] in *. after_bits REP (ub b 3).
match goal with H : ?v = Z_to_bv 64 (uv b 3) |- _ => subst v end.
pose proof (speex_bits_unpack_unsigned_ok b 3 _ _ BOK ltac:(lia) (unpack_eta b 3)) as sfP_; first [ sf_destruct 6%nat sfP_ as BOK1 Hs3 _ _ Hbs3 _ | sf_fb; destruct sfP_ as (BOK1 & Hs3 & _ & _ & Hbs3 & _) ].
pose proof (ub_exact b 3 BOK ltac:(lia) ltac:(lia)) as sfP_; first [ sf_destruct 4%nat sfP_ as Hov3 Hpos3 Hnb3 Hrem3 | sf_fb; destruct sfP_ as (Hov3 & Hpos3 & Hnb3 & Hrem3) ].
pose proof (proj1 (speex_bits_advance_ok (ub b 3) (znth wb_skip_table (uv b 3) + -4) BOK1 ltac:(pose proof (wb_skip_range (uv b 3) ltac:(lia)); lia))) as BOK2.
pose proof (adv_size (ub b 3) (znth wb_skip_table (uv b 3) + -4)) as Hbs4. rewrite Hbs3 in Hbs4.
pose proof (wb_skip_read _ (uv b 3) MI ltac:(lia)) as TBL. pose proof (wb_skip_range (uv b 3) ltac:(lia)) as TR.
unfold A_wb_skip_table in TBL |- *.
zstep. ub_dec.
zstep. zstep. ub_dec.
zstep. zstep.
rewrite Z.shiftl_mul_pow2 in * by lia. change (2 ^ 2) with 4 in *.
replace (68784 + uv b 3 * 4) with (68784 + 4 * uv b 3) by lia.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. rewrite swrap32_small by lia.
zstep. zstep. zstep.
call (X1g0.speex_bits_advance_spec A D (ub b 3) (znth wb_skip_table (uv b 3) + -4));
[exact REP | exact BOK1 | exact MI | lia |].
after_bits REP (speex_bits_advance (ub b 3) (znth wb_skip_table (uv b 3) + -4)).
apply K. close_A.
}
{
zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 3); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 3) in *. cbn [fst snd] in *. after_bits REP (ub b 3).
match goal with H : ?v = Z_to_bv 64 (uv b 3) |- _ => subst v end.
pose proof (speex_bits_unpack_unsigned_ok b 3 _ _ BOK ltac:(lia) (unpack_eta b 3)) as sfP_; first [ sf_destruct 6%nat sfP_ as BOK1 Hs3 _ _ Hbs3 _ | sf_fb; destruct sfP_ as (BOK1 & Hs3 & _ & _ & Hbs3 & _) ].
pose proof (ub_exact b 3 BOK ltac:(lia) ltac:(lia)) as sfP_; first [ sf_destruct 4%nat sfP_ as Hov3 Hpos3 Hnb3 Hrem3 | sf_fb; destruct sfP_ as (Hov3 & Hpos3 & Hnb3 & Hrem3) ].
pose proof (proj1 (speex_bits_advance_ok (ub b 3) (znth wb_skip_table (uv b 3) + -4) BOK1 ltac:(pose proof (wb_skip_range (uv b 3) ltac:(lia)); lia))) as BOK2.
pose proof (adv_size (ub b 3) (znth wb_skip_table (uv b 3) + -4)) as Hbs4. rewrite Hbs3 in Hbs4.
pose proof (wb_skip_read _ (uv b 3) MI ltac:(lia)) as TBL. pose proof (wb_skip_range (uv b 3) ltac:(lia)) as TR.
unfold A_wb_skip_table in TBL |- *.
zstep. ub_dec.
zstep. zstep. ub_dec.
zstep. zstep.
rewrite Z.shiftl_mul_pow2 in * by lia. change (2 ^ 2) with 4 in *.
replace (68784 + uv b 3 * 4) with (68784 + 4 * uv b 3) by lia.
zstep. rewrite sx32_small by (unfold int31; lia).
zstep. rewrite swrap32_small by lia.
zstep. zstep. zstep.
call (X1g0.speex_bits_advance_spec A D (ub b 3) (znth wb_skip_table (uv b 3) + -4));
[exact REP | exact BOK1 | exact MI | lia |].
after_bits REP (speex_bits_advance (ub b 3) (znth wb_skip_table (uv b 3) + -4)).
apply K. close_A.
}
Qed.

Definition QW (s : PState) : (bits_st ptr + nb_search_res) -> PState -> machine_state -> Prop :=
fun wb s' ms => s' = s /\
match wb with
| inl b' => at_A X 0x20cf8 b' ms
| inr (NbReturn r b') => at_X X r st0 b' ms
| inr (NbMode _ _) => False
end.

Local Notation HTAIL := (nbA_tail notify STR_TOP X NH).

#[using="STR_TOP NH"] Lemma nbA_body : forall fuel (s : PState) b ms,
(forall b' ms', at_A X 0x20d54 b' ms' -> implM rsegs (nb_mode_search notify unpackM advanceM remainingM fuel st0 b') s (QA X s) ms') ->
5 <= speex_bits_remaining b ->
at_A X 0x20c3c b ms ->
implM rsegs (nb_mode_search notify unpackM advanceM remainingM (S fuel) st0 b) s (QA X s) ms.
Proof.
intros fuel s b ms IH R5 AT.
rewrite nb_mode_search_S. eapply implM_bind_run; [reflexivity|]. cbv beta.
replace (speex_bits_remaining b <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
eapply implM_bind_run; [unfold bits_unpack_unsigned_M, mret; rewrite unpack_eta; reflexivity|]. cbv beta iota.

eapply (implM_bind rsegs _ _ s (QW s)).
2:{ intros wb s' ms' [-> HQ]. destruct wb as [b'|[r b'|mo b']]; [ | | destruct HQ].
- apply HTAIL; [exact IH| exact HQ].
- apply implM_ret. apply evt_done. split; [reflexivity|]. exact HQ. }
first [ sf_destruct 22%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK.
pose proof (ub_exact b 1 BOK ltac:(lia) ltac:(lia)) as sfP_; first [ sf_destruct 4%nat sfP_ as Hov1 Hpos1 Hnb1 Hrem1 | sf_fb; destruct sfP_ as (Hov1 & Hpos1 & Hnb1 & Hrem1) ].
pose proof (speex_bits_unpack_unsigned_ok b 1 _ _ BOK ltac:(lia) (unpack_eta b 1)) as sfP_; first [ sf_destruct 6%nat sfP_ as BOK1 Hw1 _ _ Hbs1 _ | sf_fb; destruct sfP_ as (BOK1 & Hw1 & _ & _ & Hbs1 & _) ].

apply implM_from_evt.
zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 1); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 1) in *. cbn [fst snd] in *. after_bits REP (ub b 1).
match goal with H : ?v = Z_to_bv 64 (uv b 1) |- _ => subst v end.
zstep. if_cases Kw1; zify_cond Kw1.
{
apply evt_done. unfold nbs_wb. replace (uv b 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
apply implM_ret. apply evt_done. split; [reflexivity|]. cbv beta iota. close_A. }

apply evt_done. unfold nbs_wb. replace (uv b 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
eapply implM_bind_run; [apply nbs_skip_run|]. cbv beta.
eapply implM_bind_run; [reflexivity|]. cbv beta.
apply implM_from_evt.
eapply (nbA_skip 0x20c4c (ub b 1)); [left; reflexivity | lia | unfold bits_pos in *; lia | | close_A].
clear - NH IH R5 BSZ BOK1 Hov1 Hpos1 Hnb1 Hrem1 Hw1 Hbs1 Kw1.
intros ms' AT.
first [ sf_destruct 22%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
set (b2 := skip_bits (ub b 1)) in *.
open_bits REP BOK.

zstep. zstep. call (X1g6.speex_bits_remaining_spec A D b2); [exact REP | exact BOK | exact MI |].
after_bits REP b2. match goal with H : ?v = Z_to_bv 64 (speex_bits_remaining b2) |- _ => subst v end.
zstep. if_cases K5; zify_cond K5; rewrite ?signed_lit_small in K5 by lia.
2:{
zstep. apply evt_done. replace (speex_bits_remaining b2 <? 5) with true by (symmetry; apply Z.ltb_lt; lia).
apply implM_ret. close_X. }
replace (speex_bits_remaining b2 <? 5) with false by (symmetry; apply Z.ltb_ge; lia).

pose proof (ub_exact b2 1 BOK ltac:(lia) ltac:(lia)) as sfP_; first [ sf_destruct 4%nat sfP_ as Hov2 Hpos2 Hnb2 Hrem2 | sf_fb; destruct sfP_ as (Hov2 & Hpos2 & Hnb2 & Hrem2) ].
pose proof (speex_bits_unpack_unsigned_ok b2 1 _ _ BOK ltac:(lia) (unpack_eta b2 1)) as sfP_; first [ sf_destruct 6%nat sfP_ as BOK2 Hw2 _ _ Hbs2 _ | sf_fb; destruct sfP_ as (BOK2 & Hw2 & _ & _ & Hbs2 & _) ].
zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b2 1); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b2 1) in *. cbn [fst snd] in *. after_bits REP (ub b2 1).
match goal with H : ?v = Z_to_bv 64 (uv b2 1) |- _ => subst v end.
apply evt_done. eapply implM_bind_run; [unfold bits_unpack_unsigned_M, mret; rewrite unpack_eta; reflexivity|]. cbv beta iota.
apply implM_from_evt.
zstep. if_cases Kw2; zify_cond Kw2.
{
apply evt_done. replace (uv b2 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
apply implM_ret. apply evt_done. split; [reflexivity|]. cbv beta iota. close_A. }

apply evt_done. replace (uv b2 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
eapply implM_bind_run; [apply nbs_skip_run|]. cbv beta.
eapply implM_bind_run; [unfold bits_unpack_unsigned_M, mret; rewrite unpack_eta; reflexivity|]. cbv beta iota.
apply implM_from_evt.
eapply (nbA_skip 0x20ca8 (ub b2 1)); [right; reflexivity | lia | unfold bits_pos in *; lia | | close_A].
clear - NH IH BSZ BOK2 Hov2 Hpos2 Hnb2 Hrem2 Hw2 Hbs2 Kw2.
intros ms' AT.
first [ sf_destruct 22%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
set (b3 := skip_bits (ub b2 1)) in *.
open_bits REP BOK.
pose proof (speex_bits_unpack_unsigned_ok b3 1 _ _ BOK ltac:(lia) (unpack_eta b3 1)) as sfP_; first [ sf_destruct 6%nat sfP_ as BOK3 Hw3 _ _ Hbs3 _ | sf_fb; destruct sfP_ as (BOK3 & Hw3 & _ & _ & Hbs3 & _) ].

zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b3 1); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b3 1) in *. cbn [fst snd] in *. after_bits REP (ub b3 1).
match goal with H : ?v = Z_to_bv 64 (uv b3 1) |- _ => subst v end.
zstep. if_cases Kw3; zify_cond Kw3.
{
apply evt_done. replace (uv b3 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
apply implM_ret. apply evt_done. split; [reflexivity|]. cbv beta iota. close_A. }

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ TG TS _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & TG & TS & _) ]. unfold NB_GOT_STDERR, NB_STDERR_VAR, NB_RSTDERR in TG, TS.
do 9 zstep.
apply evt_done. replace (uv b3 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
clear TG TS.
eapply implM_bind.
{ eapply HN with (lo := lo); try reflexivity.
- apply cstr_more_than_two; [exact MI| exact T0| exact (h_strtop _ _ _ NH)].
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
replace (ret_pc (Z_to_bv 64 0x223f0)) with (Z_to_bv 64 0x223f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply implM_from_evt. zstep. zstep. apply evt_done.
apply implM_ret. close_X.
Qed.
End Seg.
