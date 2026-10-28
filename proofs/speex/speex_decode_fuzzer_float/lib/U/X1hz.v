(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac uif b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) => replace c with b; [cbv iota | symmetry; ucond_rw; solve_cond_rec] end.

Lemma lsp_entry_even : forall k, lsp_entry k mod 2 = 0 /\ 0 <= lsp_entry k < 2^64.
Proof. intros []; cbn -[Z.pow Z.modulo Z.lt Z.le]; unfold A_lsp_unquant_lbr, A_lsp_unquant_nb, A_lsp_unquant_high; lia. Qed.

Lemma sx32_ssmall_B : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sx32. rewrite Z_to_bv_unsigned.
replace (bv_swrap 32 (bv_wrap 64 v)) with v; [reflexivity|].
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (4294967296 / 2) with 2147483648.
symmetry. Z.to_euclidean_division_equations. lia.
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

Definition QB (mo : Z) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => match smrec_at mo with
| None => at_N X b ms
| Some r => at_C X r mo (lsp_bits (sm_lsp_unquant (smr_sm r)) b) ms
end.

#[using="notify STR_TOP NH"] Lemma nbB : forall mo b ms, at_B X mo b ms -> evt rsegs (QB mo b) ms.
Proof.
intros mo b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 Hmo JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & Hmo & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK.

pose proof (rw_cells_f32_CB rsegs _ _ _ P1) as EXB. rewrite Lexc in EXB.
set (ebs := cells_bytes (f32 (j_excbuf j))) in EXB.
assert (LEB : length ebs = 2000%nat).
{ subst ebs. rewrite cells_bytes_length by apply cells_wf_f32. rewrite cells_size_f32, Lexc. reflexivity. }
replace (4 * 500)%nat with (length ebs) in EXB by (rewrite LEB; reflexivity). clear P1.
pose proof (h_sthi _ _ _ NH) as STHI. unfold NBSTATE_SIZEOF in STHI.
zstep. zstep. uif true.
zstep. rewrite E88. zstep. zstep. zstep. zstep.
call (h_memmove _ _ _ NH (ST + 32) ebs (ST + 32) (ST + 672) 1360);
[exact EXB | lia | rewrite LEB; cbn; lia | lia | rewrite LEB; cbn; lia | lia | lia
| rewrite LEB; pose proof (h_sthi _ _ _ NH); unfold NBSTATE_SIZEOF in *; cbn; lia
| reflexivity | reflexivity | reflexivity | exact MI | ].
try rename MI0 into MI. cbv delta [callR].
match goal with H : rw_cells _ _ (ST + 32) [CB (length ebs) ?bs'] |- _ =>
rewrite LEB in H; change 2000%nat with (4 * 500)%nat in H;
destruct (rw_cells_CB_f32 rsegs _ _ 500 _ H) as (eb' & Leb' & P1); clear H end.
try clear EXB. clear LEB. try clear ebs.

pose proof (ctx_tables _ _ X NH _ MU) as TAB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR.
zstep. zstep. cbn [nb_submodeID set_nb_submodeID] in *. rewrite (sx32_ssmall_B mo) by lia. unfold NB_SUBMODES_PTR in *.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. zstep. zstep. zstep.
if_true_z.
zstep. zstep. zstep. zstep. zstep.
rewrite (lxor_sign_nn mo) by lia.
if_true_z.
zstep. if_true_z.
zstep. zstep. if_true_z.
zstep.
idtac.
destruct (smrec_cases mo Hmo) as [(Hm0 & SP0 & SAT & SMN) | (r & SAT & INr & SPE & SPlo & SMS & LORD)].
-
rewrite SP0. zstep. if_true.
apply evt_done. unfold QB. rewrite SAT. subst mo. close_cut 13.
-
pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
rewrite SPE. zstep. if_false_x.
assert (SPA : smr_ptr r mod 8 = 0) by (unfold nb_smrecs in INr; repeat (destruct INr as [<-|INr]; [reflexivity|]); destruct INr).
zstep. if_true_z. zstep. zstep. if_true_z.
zstep. zstep. zstep. zstep. zstep. rewrite E112. zstep.
set (kq := sm_lsp_unquant (smr_sm r)) in *.
pose proof (lsp_entry_even kq) as [EV ER].
replace (ret_pc (Z_to_bv 64 (lsp_entry kq))) with (Z_to_bv 64 (lsp_entry kq)) by (symmetry; apply ret_pc_even; [exact ER| exact EV]).
pose proof TAB as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ _ _ TGOT | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & TGOT) ].
clear SMC TAB TB2. pose proof (h_sp16 _ _ _ NH) as SP16.
call (h_lsp _ _ _ NH kq A D b (usp + -256) (f_ql fr) lo);
[ exact REP | exact BOK | exact TGOT | exact FS | rewrite LORD; exact Lfql
| rewrite USP; exact STK | rewrite USP; unfold LSPQ_DEPTH; lia | exact T0 | unfold NB_GLOBALS_TOP; lia | exact T3
| rewrite USP, LORD; unfold apart; lia
| rewrite USP; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP, BSZ; unfold apart; pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite LORD; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite LORD, BSZ; unfold apart; pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | rewrite LORD; reflexivity | reflexivity | exact MI | exact FRM | lia | lia | ].
after_bits REP (lsp_bits kq b). cbv delta [callR]. rewrite USP, LORD in *.
pose proof (lsp_bits_size kq b) as BSZ1.
apply evt_done. unfold QB. rewrite SAT. subst kq. close_cut 12.
Qed.
End Seg.
