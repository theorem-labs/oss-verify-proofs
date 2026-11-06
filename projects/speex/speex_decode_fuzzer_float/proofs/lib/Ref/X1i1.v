(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1g7 X1i0.
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

Local Notation at_D1 := (at_D1 X). Local Notation at_D2 := (at_D2 X).

Ltac nbred_all :=
cbn [nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID
nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled nb_isave_ptr
set_nb_first set_nb_count_lost set_nb_submodeID set_nb_voc_offset set_nb_dtx_enabled set_nb_pitch_gain_buf_idx] in *.

Ltac do_unpack b n :=
call (X1g7.speex_bits_unpack_unsigned_spec A D b n); [eassumption | eassumption | lia | eassumption |];
rewrite (unpack_eta b n) in *; cbn [fst snd] in *;
try rename MI0 into MI;
match goal with H : bits_rep _ _ _ _ (ub b n) |- _ => rename H into REP end;
match goal with H : ?v = Z_to_bv 64 (uv b n) |- _ => subst v end;
lazymatch goal with BOK : bits_ok b |- _ =>
let B1 := fresh "BOK" in let R1 := fresh "Huv" in let S1 := fresh "Hbs" in
pose proof (speex_bits_unpack_unsigned_ok b n _ _ BOK ltac:(lia) (unpack_eta b n)) as sfP_; sf_curry 6%nat sfP_; intros B1 R1 _ _ S1 _; sf_clear sfP_; sf_fix_order
end.

#[using="notify STR_TOP NH"] Lemma nbD1 : forall r mo b ms, at_D1 r mo b ms ->
evt rsegs (at_D2 r mo (segD_olp (smr_sm r) b) (segD_st (set_nb_submodeID st0 mo) (smr_sm r) b) (segD_bits (set_nb_submodeID st0 mo) (smr_sm r) b)) ms.
Proof.
intros r mo b ms AT.
first [ sf_destruct 25%nat AT as Fx fc m k xra xa0 xs3 xs4 xs8 j ows iws sws fr -> FRM CTX FOK FRA E56 E64 E104 E112 SAT JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs3 & xs4 & xs8 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E56 & E64 & E104 & E112 & SAT & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK. nbred_all.
pose proof (smrec_facts mo r SAT) as sfP_; first [ sf_destruct 5%nat sfP_ as CASES LORD INr SPlo SPE | sf_fb; destruct sfP_ as (CASES & LORD & INr & SPlo & SPE) ]. cbv zeta in CASES.
pose proof (smrec_at_in mo r SAT) as (_ & _ & Hmo). unfold NB_SUBMODES_PTR in P14.

zstep.
pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC.
unfold smrec_cells in SMC. cbv zeta in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR. rewrite SPE in SPR.
clear TAB TB2.
zstep. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. replace (213512 + mo * 8) with (213512 + 8 * mo) by lia.
zstep. clear SPR.
unfold segD_olp, segD_st, segD_bits, segD_b3, segD_b2, segD_b1.
destruct CASES as [(ELBR & EFPG & M18) | [(ELBR & EFPG & ->) | (ELBR & EFPG & M37)]]; rewrite ELBR, EFPG in *; cbn [Z.eqb Pos.eqb negb].
-
zstep. zstep. zstep. if_false.
zstep. zstep. zstep. do_unpack b 7.
pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR. rewrite SPE in SPR. clear TAB.
zstep. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. replace (213512 + mo * 8) with (213512 + 8 * mo) by lia. zstep. clear SPR.
zstep. rewrite swrap32_small by lia. zstep.

zstep. zstep. if_false. zstep. zstep. zstep. do_unpack (ub b 7) 4.
zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. do_unpack (ub (ub b 7) 4) 5.
zstep. zstep. zstep. zstep. zstep.
call (h_exp _ _ _ NH lo); [rewrite USP; exact STK | rewrite USP; unfold EXP_DEPTH; lia | exact MI | assumption |].
try rename MI0 into MI. cbv delta [callR]. rewrite USP in *.
zstep. rewrite sx32_small by (unfold int31; lia). zstep. zstep.
destruct M18 as [-> | ->].
+
zstep. if_false. zstep. zstep. zstep. do_unpack (ub (ub (ub b 7) 4) 5) 4.
zstep. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite seqz15 by lia.
zstep. zstep. zstep. if_true_x.
apply evt_done. cbn [nb_submodeID set_nb_submodeID Z.eqb Pos.eqb]. close_cut 5.
+
zstep. if_true_x. zstep. zstep. if_false_x. lstep.
apply evt_done. cbn [nb_submodeID set_nb_submodeID Z.eqb Pos.eqb Z.ltb]. close_cut 5.
-
zstep. zstep. zstep. if_false.
zstep. zstep. zstep. do_unpack b 7.
pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof (sub_ptr_read _ 2 TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR. rewrite SPE in SPR. clear TAB.
zstep. zstep. zstep. zstep. zstep. clear SPR.
zstep. rewrite swrap32_small by lia. zstep.
zstep. zstep. if_true. zstep.

zstep. zstep. zstep. zstep. do_unpack (ub b 7) 5.
zstep. zstep. zstep. zstep. zstep.
call (h_exp _ _ _ NH lo); [rewrite USP; exact STK | rewrite USP; unfold EXP_DEPTH; lia | exact MI | assumption |].
try rename MI0 into MI. cbv delta [callR]. rewrite USP in *.
zstep. zstep. zstep. zstep. if_true_x. zstep. zstep. if_false_x. lstep.
apply evt_done. cbn [nb_submodeID set_nb_submodeID Z.eqb Pos.eqb Z.ltb]. close_cut 5.
-
zstep. zstep. zstep. if_true. zstep.
zstep. zstep. if_true. zstep.
zstep. zstep. zstep. zstep. do_unpack b 5.
zstep. zstep. zstep. zstep. zstep.
call (h_exp _ _ _ NH lo); [rewrite USP; exact STK | rewrite USP; unfold EXP_DEPTH; lia | exact MI | assumption |].
try rename MI0 into MI. cbv delta [callR]. rewrite USP in *.
zstep. rewrite sx32_small by (unfold int31; lia). zstep. zstep. zstep.
if_cases Km; zify_cond Km; [| exfalso; lia]. zstep. zstep. if_cases Km2; zify_cond Km2; rewrite ?signed_lit_small in Km2 by lia; [exfalso; lia|]. lstep.
apply evt_done.
replace (mo =? 1) with false by (symmetry; apply Z.eqb_neq; lia).
replace (1 <? mo) with true by (symmetry; apply Z.ltb_lt; lia). cbn [nb_submodeID set_nb_submodeID].
replace (mo =? 1) with false by (symmetry; apply Z.eqb_neq; lia). replace (1 <? mo) with true by (symmetry; apply Z.ltb_lt; lia).
close_cut 5.
Qed.

End Seg.
