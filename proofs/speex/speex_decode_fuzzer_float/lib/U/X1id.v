(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1ic.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma le8_zero_split : le8 (Z_to_bv 64 0) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0).
Proof. vm_compute. reflexivity. Qed.

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

Local Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac uif b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
replace c with b; [cbv iota | symmetry; ucond_rw; solve_cond_rec] end.
Local Ltac cpy E b := zstep; uif false; zstep; step; zstep; rewrite E; zstep; zstep; step; zstep; uif b.

Ltac close_atX :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
lazymatch goal with MU : munch _ (x_m0 _) m |- _ =>
apply evt_done; unfold at_X;
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); sf_eexists 13%nat;
junk_exists; sf_eexists 3%nat; frame_exists; split; [reflexivity|];
split; [asm|]; split; [close_ctxX MU|]; split; [close_fok|]; split; [close_frame'| close_feqs]
end end.

#[using="notify STR_TOP NH"] Lemma nbH3 : forall st b ms, at_H3 X st b ms -> evt rsegs (at_X X 0 (nb_end st) b) ms.
Proof.
intros st b ms AT. unfold at_H3, at_Hpc in AT. unfold nb_end.
first [ sf_destruct 31%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E88 E104 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E88 & E104 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].
pose proof (h_sthi _ _ _ NH) as STHI. unfold NBSTATE_SIZEOF in STHI.

zstep. zstep. rewrite E104. zstep. rewrite zb_lxor_ones by lia. zstep. zstep.
remember (f_ql fr) as ql eqn:Eql.
destruct ql as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|qq ql']]]]]]]]]]]; try (cbn in Lfql; lia).
rewrite !f32_cons, f32_nil in FS.
lazymatch type of P3 with rw_cells _ _ _ (f32 ?oq) =>
destruct oq as [|o0 [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|o7 [|o8 [|o9 [|oo oq']]]]]]]]]]]; try (cbn in Loq; lia) end.
rewrite !f32_cons, f32_nil in P3.
cpy E104 true. cpy E104 true. cpy E104 true. cpy E104 true. cpy E104 true.
cpy E104 true. cpy E104 true. cpy E104 true. cpy E104 true. cpy E104 false.
rewrite <- f32_nil, <- !f32_cons in FS. rewrite Eql in FS.
clear Lfql. assert (Lfql : length (f_ql fr) = 10%nat) by (rewrite <- Eql; reflexivity).
rewrite <- f32_nil, <- !f32_cons in P3.
lazymatch type of P3 with rw_cells _ _ _ (f32 ?l) => assert (Loq' : length l = 10%nat) by reflexivity end.

zstep. rewrite sx32_small by (unfold int31; lia). zstep. step. step.
zstep. rewrite swrap32_small by lia.
step. step. zstep. rewrite E88.
lazymatch type of P0 with rw_cells _ ?mm _ [C8 ?c0; C4 ?c1; C4 ?c2; C4 ?c3; C4 ?c4; C8 ?c5] =>
assert (P0' : rw_cells rsegs mm ST [C8 c0; CB 8 (le4 c1 ++ le4 c2); C4 c3; C4 c4; C8 c5])
by (eapply rw_cells_recast; [exact P0 | cbn; repeat split; try exact I; rewrite length_app, !length_le4; reflexivity
| cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity]);
clear P0; rename P0' into P0
end.
lstep.
lazymatch type of P0 with rw_cells _ ?mm _ [C8 ?c0; C8 (Z_to_bv 64 0); C4 ?c3; C4 ?c4; C8 ?c5] =>
assert (P0' : rw_cells rsegs mm ST [C8 c0; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 c3; C4 c4; C8 c5])
by (eapply rw_cells_recast; [exact P0 | cbn; repeat split; exact I
| cbn [cells_bytes cbytes]; rewrite le8_zero_split, <- !app_assoc; reflexivity]);
clear P0; rename P0' into P0
end.
zstep. unfold bv_lts. rewrite !zb_signed_small by lia. if_false_x.
zstep. zstep. zstep. uif false.
zstep. rewrite E48. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
zstep. rewrite zb_lxor_ones by lia. zstep. uif false.
zstep. zstep.
set (idx := nb_pitch_gain_buf_idx st) in *.
first [ pose proof (f32_split_at rsegs _ _ (j_pitch_gain_buf j) (Z.to_nat idx) ltac:(rewrite Lpgb; lia) P11) as sfP_; sf_destruct 6%nat sfP_ as pgx _ PG1 PG2 PG3 LPG1 | sf_fb; destruct (f32_split_at rsegs _ _ (j_pitch_gain_buf j) (Z.to_nat idx) ltac:(rewrite Lpgb; lia) P11) as (pgx & _ & PG1 & PG2 & PG3 & LPG1) ]. clear P11.
rewrite Z2Nat.id in PG2, PG3 by lia.
remember (ST + 2212 + 4 * idx) as PGA eqn:EPGA.
replace (ST + 2212 + idx * 4) with PGA by lia.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with H : rw_cells _ mm PGA [C4 ?v] |- _ =>
subst PGA;
destruct (f32_join_at rsegs mm (ST + 2212) (firstn (Z.to_nat idx) (j_pitch_gain_buf j)) v (skipn (S (Z.to_nat idx)) (j_pitch_gain_buf j)))
as [P11 Lpgb'];
[ exact PG1 | rewrite LPG1, Z2Nat.id by lia; exact H | rewrite LPG1, Z2Nat.id by lia; exact PG3 | clear PG1 H PG3 ]
end end.
rewrite LPG1, length_skipn, Lpgb in Lpgb'.
replace (S (Z.to_nat idx + (3 - S (Z.to_nat idx))))%nat with 3%nat in Lpgb' by lia.
lazymatch type of P11 with rw_cells _ _ _ (f32 ?l) => remember l as pgb' eqn:Epg; clear Epg end.

zstep. unfold bv_lts. rewrite !zb_signed_small by lia.
destruct (Z_lt_ge_dec idx 2) as [LT2 | GE2].
- if_true_x. zstep. zstep. rewrite E88. step.
replace (2 <? idx + 1) with false by (symmetry; apply Z.ltb_ge; lia).
close_atX.
- if_false_x. lstep. zstep. zstep. rewrite E88. step.
replace (2 <? idx + 1) with true by (symmetry; apply Z.ltb_lt; lia).
close_atX.
Qed.

#[using="notify STR_TOP NH"] Lemma nbH : forall st b ms, at_H X st b ms -> evt rsegs (at_X X 0 (nb_end st) b) ms.
Proof.
intros st b ms AT.
eapply evt_cut; [exact (nbH1 notify STR_TOP X NH st b ms AT)|]. intros ms1 H1.
eapply evt_cut; [exact (nbH2 notify STR_TOP X NH st b ms1 H1)|]. intros ms2 H2.
exact (nbH3 st b ms2 H2).
Qed.
End Seg.
