(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1ic.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
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
first [ sf_destruct 20%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E88 E112 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E88 & E112 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].

zstep. zstep. zstep. zstep.
pose proof (f32_as_blob _ _ _ 10%nat P3 Loq) as DSTB. clear P3.
pose proof (rw_cells_bound _ _ _ _ DSTB) as BD. cbn [cells_size csize Nat.add Z.to_nat Z.of_nat Pos.to_nat Pos.iter_op Nat.mul] in BD.
call (nmemcpy_specZ (ST + 2040) (usp + -256) 40 (cells_bytes (f32 (f_ql fr))) _);
[ apply f32_bytes_at; exact FS | rewrite f32_bytes_length, Lfql; reflexivity | exact DSTB
| pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. try clear DSTB. clear BD.
match goal with H : rw_cells _ ?mm (ST + 2040) [CB _ _] |- _ =>
assert (P3 : rw_cells rsegs mm (ST + 2040) (f32 (f_ql fr)))
by (eapply rw_cells_recast; [exact H | apply cells_wf_f32 | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity]);
clear H end.
match goal with H : bytes_at _ _ (usp + -256) _ |- _ => clear H end.

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

zstep. rewrite sx32_small by (unfold int31; lia). zstep. step. step.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep. zstep. zstep. step. zstep.

zstep. zstep.
set (idx := nb_pitch_gain_buf_idx st) in *.
first [ pose proof (f32_split_at rsegs _ _ (j_pitch_gain_buf j) (Z.to_nat idx) ltac:(rewrite Lpgb; lia) P11) as sfP_; sf_destruct 6%nat sfP_ as pgx _ PG1 PG2 PG3 LPG1 | sf_fb; destruct (f32_split_at rsegs _ _ (j_pitch_gain_buf j) (Z.to_nat idx) ltac:(rewrite Lpgb; lia) P11) as (pgx & _ & PG1 & PG2 & PG3 & LPG1) ]. clear P11.
rewrite Z2Nat.id in PG2, PG3 by lia.
remember (ST + 2212 + 4 * idx) as PGA eqn:EPGA.
replace (ST + idx * 4 + 2047) with (PGA + -165) by lia.
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
- if_true_x. zstep. step.
replace (2 <? idx + 1) with false by (symmetry; apply Z.ltb_ge; lia).
close_atX.
- if_false_x. lstep. zstep. step.
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
