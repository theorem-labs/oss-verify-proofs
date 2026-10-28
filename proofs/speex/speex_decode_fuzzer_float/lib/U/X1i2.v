(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1g7 X1i0.
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

Local Notation at_D1 := (at_D1 X). Local Notation at_D2 := (at_D2 X).

Ltac nbred_all :=
cbn [nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID
nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled nb_isave_ptr
set_nb_first set_nb_count_lost set_nb_submodeID set_nb_voc_offset set_nb_dtx_enabled set_nb_pitch_gain_buf_idx] in *.

Ltac merge_at pcz :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?rom) =>
apply (evt_cut segs (fun ms => exists F' fc', ms = MS R F' (Z_to_bv 64 pcz) fc' rv m rom /\ frm0 fc') Q)
end.
Ltac merge_done := apply evt_done; sf_eexists 2%nat; split; [reflexivity | assumption].

#[using="notify STR_TOP NH"] Lemma nbD2 : forall r mo olp st b ms, at_D2 r mo olp st b ms -> evt rsegs (at_E X r mo olp 40 0 st b) ms.
Proof.
intros r mo olp st b ms AT.
first [ sf_destruct 37%nat AT as Fx fc m k xra xa0 xs0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E80 E88 E104 E112 E120 SAT JEXC SID OLP ISAVE | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E80 & E88 & E104 & E112 & E120 & SAT & JEXC & SID & OLP & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
merge_at 0x2123c; [ if_cases K1; [ merge_done | zstep; merge_done ] | ].
intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx1 fcq -> FRM1 | sf_fb; destruct sfH_ as (Fx1 & fcq & -> & FRM1) ].
lstep. zstep. zstep. zstep. zstep. zstep.
merge_at 0x21258; [ if_cases K2; [ merge_done | zstep; merge_done ] | ].
intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx2 fcq2 -> FRM2 | sf_fb; destruct sfH_ as (Fx2 & fcq2 & -> & FRM2) ].
lstep. zstep. zstep. rewrite E48. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. zstep. zstep. zstep. zstep. zstep. rewrite swrap32_small by lia. zstep. zstep. zstep. zstep.
zstep. zstep.
apply evt_done. close_cut 7.
Qed.
End Seg.
