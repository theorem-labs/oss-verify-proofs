(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn X1hp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
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

#[using="notify STR_TOP NH"] Lemma nbG_iter : forall i st b ms, at_G X i st b ms -> i < 4 ->
evt rsegs (fun ms' => if i + 1 <? 4 then at_G X (i + 1) st b ms' else at_H X st b ms') ms.
Proof.
intros i st b ms AT Hi.
first [ sf_destruct 21%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E88 E112 JEXC Hi0 | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E88 & E112 & JEXC & Hi0) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.

zstep. zstep. zstep. zstep. zstep. zstep. step. zstep.
call ((h_lspi _ _ _ NH) (ST + 2040) (usp + -256) (usp + -776) i (j_old_qlsp j) (f_ql fr) (f_iq fr));
[ exact P3 | exact Loq | exact FS | exact Lfql | exact FQ | exact Lfiq
| unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia | unfold apart; lia | lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. try clear FQ. try clear Lfiq.
match goal with H : rw_cells _ _ (usp + -776) (f32 ?ws), L : length ?ws = 10%nat |- _ => rename H into FQ; rename L into Lfiq end.

pose proof (f32_split rsegs _ _ (f_ak fr) 10 ltac:(rewrite Lfak; lia) FK) as [FK1 FK2]. clear FK.
replace (usp + -736 + 4 * Z.of_nat 10) with (usp + -696) in FK2 by lia.
assert (LFK2 : length (skipn 10 (f_ak fr)) = 30%nat) by (rewrite length_skipn; lia).
assert (LFK1 : length (firstn 10 (f_ak fr)) = 10%nat) by (rewrite length_firstn; lia).
zstep. zstep. zstep. zstep. zstep.
call ((h_l2l _ _ _ NH) (usp + -776) (usp + -736) lo _ (firstn 10 (f_ak fr)) (Z_to_bv 64 0));
[ exact FQ | exact Lfiq | exact FK1 | exact LFK1
| rewrite USP; exact STK | rewrite USP; unfold LSP2LPC_DEPTH; lia | exact T0
| rewrite USP; pose proof (h_spx _ _ _ NH); lia
| rewrite USP; unfold apart; lia | rewrite USP; unfold apart; lia | unfold apart; lia
| reflexivity | reflexivity | reflexivity | reflexivity | assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. rewrite USP in *. try clear FK1. clear LFK1.
match goal with H : rw_cells _ _ (usp + -736) (f32 ?ws), L : length ?ws = 10%nat |- _ => rename H into FK1; rename L into LFK1 end.

lazymatch type of FK1 with rw_cells _ _ _ (f32 ?ak) =>
destruct ak as [|k0 [|k1 [|k2 [|k3 [|k4 [|k5 [|k6 [|k7 [|k8 [|k9 [|kk ak']]]]]]]]]]]; try (cbn in LFK1; lia) end.
rewrite !f32_cons, f32_nil in FK1.
zstep. step.
step. step. step. zstep. step. zstep. if_true_x.
step. step. step. zstep. step. zstep. if_true_x.
step. step. step. zstep. step. zstep. if_true_x.
step. step. step. zstep. step. zstep. if_true_x.
step. step. step. zstep. step. zstep. if_false_x.

zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.

first [ pose proof (f32_split_at rsegs _ _ (j_pi_gain j) (Z.to_nat i) ltac:(rewrite Lpig; lia) P7) as sfP_; sf_destruct 6%nat sfP_ as pgx _ PG1 PG2 PG3 LPG1 | sf_fb; destruct (f32_split_at rsegs _ _ (j_pi_gain j) (Z.to_nat i) ltac:(rewrite Lpig; lia) P7) as (pgx & _ & PG1 & PG2 & PG3 & LPG1) ]. clear P7.
rewrite Z2Nat.id in PG2, PG3 by lia.
replace (ST + 2168 + i * 4) with (ST + 2168 + 4 * i) by lia.
remember (ST + 2168 + 4 * i) as PGA eqn:EPGA.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with H : rw_cells _ mm PGA [C4 ?v] |- _ =>
subst PGA;
destruct (f32_join_at rsegs mm (ST + 2168) (firstn (Z.to_nat i) (j_pi_gain j)) v (skipn (S (Z.to_nat i)) (j_pi_gain j)))
as [P7 Lpig'];
[ exact PG1 | rewrite LPG1, Z2Nat.id by lia; exact H | rewrite LPG1, Z2Nat.id by lia; exact PG3 | clear PG1 H PG3 ]
end end.
rewrite LPG1, length_skipn, Lpig in Lpig'.
replace (S (Z.to_nat i + (4 - S (Z.to_nat i))))%nat with 4%nat in Lpig' by lia.
lazymatch type of P7 with rw_cells _ _ _ (f32 ?l) => remember l as pg' eqn:Epg; clear Epg end.

zstep. zstep. zstep. zstep. zstep. zstep. rewrite E112. zstep. zstep.
first [ pose proof (f32_split3 rsegs _ OUT ows (Z.to_nat (40 * i)) 40 ltac:(rewrite Lows; lia) XO) as sfP_; sf_destruct 6%nat sfP_ as XO1 XO2 XO3 LO1 LO2 LO3 | sf_fb; destruct (f32_split3 rsegs _ OUT ows (Z.to_nat (40 * i)) 40 ltac:(rewrite Lows; lia) XO) as (XO1 & XO2 & XO3 & LO1 & LO2 & LO3) ]. clear XO.
rewrite Z2Nat.id in XO2, XO3 by lia.
replace (OUT + 4 * (40 * i)) with (OUT + 160 * i) in XO2, XO3 by lia.
replace (OUT + i * 160) with (OUT + 160 * i) by lia.
pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY) as LSO.
lazymatch type of XO2 with rw_cells _ _ _ (f32 ?xs) =>
call ((h_iir _ _ _ NH) (OUT + 160 * i) (ST + 2080) (OUT + 160 * i) (ST + 2120) 40 xs (j_interp_qlpc j) xs (j_mem_sp j) (Z_to_bv 64 0));
[ exact XO2 | exact LO2 | exact P4 | exact Liq | exact P5 | exact Lmsp
| left; split; reflexivity
| lia | unfold apart; lia | unfold apart; lia | unfold apart; lia | unfold apart; lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ]
end.
cbv beta delta [callR]. try rename MI0 into MI. try clear XO2. clear LO2. try clear P5. clear Lmsp. clear LSO.
match goal with H : rw_cells _ _ (OUT + 160 * i) (f32 ?ws), L : length ?ws = _ |- _ => rename H into XO2; rename L into LO2; cbn in LO2 end.
match goal with H : rw_cells _ _ (ST + 2120) (f32 ?ws), L : length ?ws = _ |- _ => rename H into P5; rename L into Lmsp end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of XO2 with rw_cells _ _ _ (f32 ?ys) =>
assert (XO : rw_cells rsegs mm OUT (f32 (firstn (Z.to_nat (40 * i)) ows ++ ys ++ skipn (Z.to_nat (40 * i) + 40) ows)))
by (apply f32_join; [exact XO1 | rewrite LO1, Z2Nat.id by lia; replace (OUT + 4 * (40 * i)) with (OUT + 160 * i) by lia;
apply f32_join; [exact XO2 | rewrite LO2; exact XO3]]);
assert (Lows' : length (firstn (Z.to_nat (40 * i)) ows ++ ys ++ skipn (Z.to_nat (40 * i) + 40) ows) = 160%nat)
by (rewrite !length_app, LO1, LO2, LO3, Lows; lia);
clear XO1 XO2 XO3
end end.
lazymatch type of XO with rw_cells _ _ _ (f32 ?l) => remember l as ows' eqn:Eows; clear Eows end.

zstep. zstep. zstep. zstep.
pose proof (rw_cells_bound _ _ _ _ P4) as BP4. rewrite cells_size_f32, Liq in BP4.
pose proof (rw_cells_bound _ _ _ _ FK1) as BFK. cbn [cells_size csize Nat.add] in BFK.
pose proof (f32_as_blob _ _ _ 10%nat P4 Liq) as P4B. clear P4.
call (nmemcpy_specZ (ST + 2080) (usp + -736) 40 (cells_bytes (f32 [k0; k1; k2; k3; k4; k5; k6; k7; k8; k9])) _);
[ apply f32_bytes_at; rewrite !f32_cons, f32_nil; exact FK1 | rewrite f32_bytes_length; reflexivity | exact P4B
| pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); unfold apart, NBSTATE_SIZEOF in *; lia
| assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. clear BP4 BFK.
match goal with H : rw_cells _ ?mm (ST + 2080) [CB _ _] |- _ =>
destruct (rw_cells_CB_f32 rsegs _ _ 10 _ H) as (iq' & Liq' & P4); clear H end.
match goal with H : bytes_at _ _ (usp + -736) _ |- _ => clear H end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FK : rw_cells rsegs mm (usp + -736) (f32 ([k0; k1; k2; k3; k4; k5; k6; k7; k8; k9] ++ skipn 10 (f_ak fr))))
by (apply f32_join; [rewrite !f32_cons, f32_nil; exact FK1 | cbn [length]; replace (usp + -736 + 4 * Z.of_nat 10) with (usp + -696) by lia; exact FK2]);
assert (Lfak2 : length ([k0; k1; k2; k3; k4; k5; k6; k7; k8; k9] ++ skipn 10 (f_ak fr)) = 40%nat) by (rewrite length_app, LFK2; reflexivity)
end.
clear FK1 FK2.
lazymatch type of FK with rw_cells _ _ _ (f32 ?l) => remember l as ak' eqn:Eak; clear Eak end.

zstep. zstep.
destruct (Z.ltb_spec (i + 1) 4) as [LT | GE].
- if_true_x. apply evt_done. cbv beta. close_cut 2.
- if_false_x. replace (i + 1) with 4 by lia. apply evt_done. cbv beta. close_cut 2.
Qed.

#[using="notify STR_TOP NH"] Lemma nbG : forall st b ms, at_G X 0 st b ms -> evt rsegs (at_H X st b) ms.
Proof.
intros st b ms AT.
eapply evt_cut; [exact (nbG_iter 0 st b ms AT ltac:(lia))|]. cbn [Z.add Z.ltb]. cbv iota. intros ms1 H1.
eapply evt_cut; [exact (nbG_iter 1 st b ms1 H1 ltac:(lia))|]. cbn [Z.add Z.ltb]. cbv iota. intros ms2 H2.
eapply evt_cut; [exact (nbG_iter 2 st b ms2 H2 ltac:(lia))|]. cbn [Z.add Z.ltb]. cbv iota. intros ms3 H3.
eapply evt_cut; [exact (nbG_iter 3 st b ms3 H3 ltac:(lia))|]. cbn [Z.add Z.ltb]. cbv iota. intros ms4 H4. apply evt_done. exact H4.
Qed.
End Seg.
