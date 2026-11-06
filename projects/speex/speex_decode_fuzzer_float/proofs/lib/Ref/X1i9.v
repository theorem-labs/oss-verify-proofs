(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3 X1i4 X1i5 X1i6 X1i7 X1i8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require X1g7.
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

#[using="notify STR_TOP NH"] Lemma nbE6 : forall r mo olp bp2 sub st b ms, at_E6 X r mo olp bp2 sub st b ms ->
evt rsegs (fun ms' => if sub + 1 <? 4 then at_E X r mo olp bp2 (sub + 1) st b ms' else at_F X r mo olp bp2 st b ms') ms.
Proof.
intros r mo olp bp2 sub st b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m kc xra xa0 xs0 xs3 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E64 E80 E88 E96 E104 E112 JEXC SAT SID BP2 OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs0 & xs3 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & JEXC & SAT & SID & BP2 & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
zstep. zstep. zstep. step. zstep. zstep.
destruct (Z_lt_ge_dec (sub + 1) 4) as [LT | GE].
- if_true_x. replace (sub + 1 <? 4) with true by (symmetry; apply Z.ltb_lt; lia).
replace (160 * sub + 160) with (160 * (sub + 1)) in * by lia.
apply evt_done. cbv beta iota. close_cut 6.
- if_false_x. replace (sub + 1 <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
replace (sub + 1) with 4 by lia.
apply evt_done. cbv beta iota. close_cut 5.
Qed.

#[using="notify STR_TOP NH"] Lemma nbE_iter : forall r mo olp bp sub st b st' b' ms,
at_E X r mo olp bp sub st b ms -> sub < 4 ->
subframe_pure (smr_sm r) olp sub st b = Some (st', b') ->
evt rsegs (fun ms' => exists bp', if sub + 1 <? 4 then at_E X r mo olp bp' (sub + 1) st' b' ms' else at_F X r mo olp bp' st' b' ms') ms.
Proof.
intros r mo olp bp sub st b st' b' ms AT Hsub HP.
assert (SAT : smrec_at mo = Some r /\ nb_submodeID st = mo).
{ first [ sf_destruct 32%nat AT as Fx fc m kc xra xa0 xs3 xs4 xs6 xs7 j ows iws sws fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ SAT SID _ | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs3 & xs4 & xs6 & xs7 & j & ows & iws & sws & fr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SAT & SID & _) ]. split; assumption. }
destruct SAT as [SAT SID].
pose proof (smrec_sub_facts mo r SAT) as sfP_; first [ sf_destruct 5%nat sfP_ as k ki HK HKI _ | sf_fb; destruct sfP_ as (k & ki & HK & HKI & _) ].
unfold subframe_pure in HP. rewrite HK, HKI, SID in HP.
eapply evt_cut; [exact (nbE1 notify STR_TOP X NH r mo olp bp sub st b k ms AT Hsub HK)|]. intros ms1 [pit H1].
eapply evt_cut; [exact (nbE2 notify STR_TOP X NH _ _ _ _ _ _ _ _ _ H1)|]. intros ms2 [bp2 H2].
eapply evt_cut; [exact (nbE3a notify STR_TOP X NH _ _ _ _ _ _ _ _ _ H2)|]. intros ms3 H3.
eapply evt_cut; [exact (nbE3b notify STR_TOP X NH _ _ _ _ _ _ _ _ _ H3)|]. intros ms4 H4. rewrite HKI in H4.
eapply evt_cut; [exact (nbE4 notify STR_TOP X NH _ _ _ _ _ _ _ _ H4)|]. intros ms5 H5.
eapply evt_cut; [exact (nbE5 notify STR_TOP X NH _ _ _ _ _ _ _ _ H5)|]. intros ms6 H6.
eapply evt_mono; [exact (nbE6 _ _ _ _ _ _ _ _ H6)|].
intros ms7 H7. exists bp2. cbv beta in H7.
unfold hsg_bits in H7.
destruct (mo =? 1).
- destruct (voc_loop VOC_FUEL (nb_voc_offset st) olp) as [v|]; [| discriminate].
injection HP as <- <-. exact H7.
- injection HP as <- <-. exact H7.
Qed.

#[using="notify STR_TOP NH"] Lemma nbE_loop : forall n r mo olp bp sub st b ms,
at_E X r mo olp bp sub st b ms -> sub + Z.of_nat n = 4 -> (1 <= n)%nat ->
match subframes_pure n sub (smr_sm r) olp st b with
| Some (st', b') => evt rsegs (fun ms' => exists bp', at_F X r mo olp bp' st' b' ms') ms
| None => True
end.
Proof.
induction n as [|n IH]; intros r mo olp bp sub st b ms AT Hn H1n; [lia|].
cbn [subframes_pure].
destruct (subframe_pure (smr_sm r) olp sub st b) as [[st1 b1]|] eqn:E1; [| exact I].
destruct (subframes_pure n (sub + 1) (smr_sm r) olp st1 b1) as [[st' b']|] eqn:E2; [| exact I].
eapply evt_cut; [exact (nbE_iter r mo olp bp sub st b st1 b1 ms AT ltac:(lia) E1)|].
intros ms1 [bp1 HI].
destruct n as [|n'].
- replace (sub + 1 <? 4) with false in HI by (symmetry; apply Z.ltb_ge; lia).
cbn [subframes_pure] in E2. injection E2 as <- <-. apply evt_done. exists bp1. exact HI.
- replace (sub + 1 <? 4) with true in HI by (symmetry; apply Z.ltb_lt; lia).
pose proof (IH r mo olp bp1 (sub + 1) st1 b1 ms1 HI ltac:(lia) ltac:(lia)) as K. rewrite E2 in K. exact K.
Qed.

#[using="notify STR_TOP NH"] Lemma nbE : forall r mo olp st b ms, at_E X r mo olp 40 0 st b ms ->
match subframes_pure 4 0 (smr_sm r) olp st b with
| Some (st', b') => evt rsegs (fun ms' => exists bp, at_F X r mo olp bp st' b' ms') ms
| None => True
end.
Proof. intros r mo olp st b ms AT. exact (nbE_loop 4 r mo olp 40 0 st b ms AT eq_refl ltac:(lia)). Qed.
End Seg.
