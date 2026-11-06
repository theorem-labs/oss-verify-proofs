(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma lsp_entry_even : forall k, lsp_entry k mod 2 = 0 /\ 0 <= lsp_entry k < 2^64.
Proof. intros []; cbn -[Z.pow Z.modulo Z.lt Z.le]; unfold A_lsp_unquant_lbr, A_lsp_unquant_nb, A_lsp_unquant_high; lia. Qed.

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
first [ sf_destruct 27%nat AT as Fx fc m k xra xa0 xs0 xs2 xs3 xs4 xs8 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E104 E112 Hmo JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs2 & xs3 & xs4 & xs8 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E104 & E112 & Hmo & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK.

pose proof (rw_cells_f32_CB rsegs _ _ _ P1) as EXB. rewrite Lexc in EXB.
set (ebs := cells_bytes (f32 (j_excbuf j))) in EXB.
assert (LEB : length ebs = 2000%nat).
{ subst ebs. rewrite cells_bytes_length by apply cells_wf_f32. rewrite cells_size_f32, Lexc. reflexivity. }
replace (4 * 500)%nat with (length ebs) in EXB by (rewrite LEB; reflexivity). clear P1.
zstep. zstep. zstep. zstep.
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
zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. unfold NB_SUBMODES_PTR. replace (213512 + mo * 8) with (213512 + 8 * mo) by lia.
zstep. clear SPR.
destruct (smrec_cases mo Hmo) as [(Hm0 & SP0 & SAT & SMN) | (r & SAT & INr & SPE & SPlo & SMS & LORD)].
-
rewrite SP0. zstep. if_true.
apply evt_done. unfold QB. rewrite SAT. subst mo. close_cut 7.
-
pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
rewrite SPE. zstep. if_false_x.
zstep. zstep. zstep. zstep. zstep. rewrite E104. zstep. zstep.
set (kq := sm_lsp_unquant (smr_sm r)) in *.
pose proof (lsp_entry_even kq) as [EV ER].
replace (ret_pc (Z_to_bv 64 (lsp_entry kq))) with (Z_to_bv 64 (lsp_entry kq)) by (symmetry; apply ret_pc_even; [exact ER| exact EV]).
pose proof TAB as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ _ _ TGOT | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & TGOT) ].
clear SMC TAB TB2.
call (h_lsp _ _ _ NH kq A D b (usp + -256) (f_ql fr) lo);
[ exact REP | exact BOK | exact TGOT | exact FS | rewrite LORD; exact Lfql
| rewrite USP; exact STK | rewrite USP; unfold LSPQ_DEPTH; lia | exact T0 | unfold NB_GLOBALS_TOP; lia | exact T3
| rewrite USP, LORD; unfold apart; lia
| rewrite USP; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP, BSZ; unfold apart; pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite LORD; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite LORD, BSZ; unfold apart; pose proof (lay_D_stk _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | rewrite LORD; reflexivity | reflexivity | exact MI | exact FRM | ].
after_bits REP (lsp_bits kq b). cbv delta [callR]. rewrite USP, LORD in *.
pose proof (lsp_bits_size kq b) as BSZ1.
apply evt_done. unfold QB. rewrite SAT. subst kq. close_cut 5.
Qed.
End Seg.
