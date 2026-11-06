(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn.
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

#[using="Type"] Lemma exc_split_enh : forall m eb, rw_cells rsegs m (ST + 32) (f32 eb) -> length eb = 500%nat ->
rw_cells rsegs m (ST + 32) (f32 (firstn 294 eb)) /\ rw_cells rsegs m (ST + 1208) (f32 (firstn 160 (skipn 294 eb)))
/\ rw_cells rsegs m (ST + 1848) (f32 (skipn 454 eb))
/\ length (firstn 294 eb) = 294%nat /\ length (firstn 160 (skipn 294 eb)) = 160%nat /\ length (skipn 454 eb) = 46%nat.
Proof.
intros m eb H L.
destruct (f32_split rsegs m _ eb 294 ltac:(lia) H) as [H1 H2].
destruct (f32_split rsegs m _ (skipn 294 eb) 160 ltac:(rewrite length_skipn; lia) H2) as [H3 H4].
rewrite skipn_skipn in H4. cbn [Nat.add] in H4.
replace (ST + 32 + 4 * Z.of_nat 294) with (ST + 1208) in H3, H4 by lia.
replace (ST + 1208 + 4 * Z.of_nat 160) with (ST + 1848) in H4 by lia.
split; [exact H1|]. split; [exact H3|]. split; [exact H4|].
rewrite !length_firstn, !length_skipn. lia.
Qed.
#[using="Type"] Lemma exc_join_enh : forall m e1 e2 e3,
rw_cells rsegs m (ST + 32) (f32 e1) -> rw_cells rsegs m (ST + 1208) (f32 e2) -> rw_cells rsegs m (ST + 1848) (f32 e3) ->
length e1 = 294%nat -> length e2 = 160%nat -> length e3 = 46%nat ->
rw_cells rsegs m (ST + 32) (f32 (e1 ++ e2 ++ e3)) /\ length (e1 ++ e2 ++ e3) = 500%nat.
Proof.
intros m e1 e2 e3 H1 H2 H3 L1 L2 L3. split; [| rewrite !length_app; lia].
apply f32_join; [exact H1|]. rewrite L1. replace (ST + 32 + 4 * Z.of_nat 294) with (ST + 1208) by lia.
apply f32_join; [exact H2|]. rewrite L2. replace (ST + 1208 + 4 * Z.of_nat 160) with (ST + 1848) by lia. exact H3.
Qed.

Definition at_F2 (bp : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs3 xs6 xs7 xs10 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 40) xs3 (Z_to_bv 64 bp) (Z_to_bv 64 ST) xs6 xs7 (Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -576)) xs10 (Z_to_bv 64 4)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f948) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v112 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368.

Ltac f_tail := zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep; step; zstep; zstep; step; zstep.

#[using="notify STR_TOP NH"] Lemma nbF_copy : forall bp st b ms, at_F2 bp st b ms -> evt rsegs (at_G X 0 st b) ms.
Proof.
intros bp st b ms AT.
first [ sf_destruct 25%nat AT as Fx fc m k xra xa0 xs3 xs6 xs7 xs10 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E88 E112 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs3 & xs6 & xs7 & xs10 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E88 & E112 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].

zstep. rewrite JEXC. zstep. zstep. zstep. rewrite E56. zstep. zstep.
first [ pose proof (exc_split_enh _ _ P1 Lexc) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (exc_split_enh _ _ P1 Lexc) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ]. clear P1.
pose proof (rw_cells_bound _ _ _ _ XO) as BXO. rewrite cells_size_f32, Lows in BXO.
pose proof (rw_cells_bound _ _ _ _ PE2) as BPE. rewrite cells_size_f32, LE2 in BPE.
pose proof (f32_as_blob _ _ _ 160%nat XO Lows) as XOB. clear XO.
call (nmemcpy_specZ OUT (ST + 1208) 640 (cells_bytes (f32 (firstn 160 (skipn 294 (j_excbuf j))))) _);
[ apply f32_bytes_at; exact PE2 | rewrite f32_bytes_length, LE2; reflexivity | exact XOB
| pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY); unfold apart, NBSTATE_SIZEOF in *; lia
| assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI. clear BXO BPE.
match goal with H : rw_cells _ ?mm OUT [CB _ _] |- _ =>
destruct (rw_cells_CB_f32 rsegs _ _ 160 _ H) as (ows' & Lows' & XO); clear H end.
match goal with H : bytes_at _ _ (ST + 1208) _ |- _ => clear H end.
destruct (exc_join_enh _ _ _ _ PE1 PE2 PE3 LE1 LE2 LE3) as [P1 Lexc1]. clear PE1 PE2 PE3.

zstep. rewrite E112. zstep. rewrite E48. zstep. rewrite Icl. zstep. if_true.

zstep.
f_tail.
apply evt_done. close_cut 2.
Qed.

#[using="notify STR_TOP NH"] Lemma nbF : forall r mo olp bp st b ms, at_F X r mo olp bp st b ms -> evt rsegs (at_G X 0 st b) ms.
Proof.
intros r mo olp bp st b ms AT.
first [ sf_destruct 30%nat AT as Fx fc m k xra xa0 xs3 xs6 xs7 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E64 E80 E88 E104 E112 JEXC SAT SID BP | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs3 & xs6 & xs7 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E64 & E80 & E88 & E104 & E112 & JEXC & SAT & SID & BP) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].
pose proof (smrec_at_in mo r SAT) as (INr & _ & Hmo).

zstep. zstep. rewrite E88.
destruct Ien as [EN | EN]; rewrite EN; rewrite sx32_small by (unfold int31; lia).
-
zstep. if_true. apply (nbF_copy bp st b). close_cut 6.
- zstep. if_false.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC.
unfold smrec_cells in SMC. cbv zeta in SMC.
pose proof (ro_cells_bound _ _ _ _ SMC) as SMB. cbn [cells_size csize Nat.add] in SMB.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR. unfold NB_SUBMODES_PTR in SPR.
pose proof (smrec_cases mo ltac:(lia)) as [(Hm0 & _) | (r' & SAT' & _ & SPE & _)]; [lia|].
rewrite SAT in SAT'. injection SAT' as <-. rewrite SPE in SPR. clear TAB TB2.
unfold NB_SUBMODES_PTR in P14.
zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. replace (213512 + mo * 8) with (213512 + 8 * mo) by lia.
zstep. step. step. zstep.
if_cases K.
+
clear SMC SMB SPR K. apply (nbF_copy bp st b). close_cut 6.
+
zstep. rewrite Icl. zstep. if_true.
zstep. rewrite JEXC. zstep. zstep. rewrite E48. zstep. zstep. zstep. zstep. zstep. zstep. rewrite E56. zstep. zstep. zstep. zstep. rewrite E112. zstep. zstep.
pose proof (f32_split rsegs _ _ ows 80 ltac:(rewrite Lows; lia) XO) as [XO1 XO2]. clear XO.
replace (OUT + 4 * Z.of_nat 80) with (OUT + 320) in XO2 by lia.
assert (LO1 : length (firstn 80 ows) = 80%nat) by (rewrite length_firstn; lia).
assert (LO2 : length (skipn 80 ows) = 80%nat) by (rewrite length_skipn; lia).
call ((h_multicomb _ _ _ NH) (ST + 32) 294 OUT (ST + 2080) bp lo (j_excbuf j) (firstn 80 ows) (j_interp_qlpc j) (Z_to_bv 64 0));
[ exact P1 | exact Lexc | left; reflexivity | exact XO1 | exact LO1 | exact P4 | exact Liq | exact BP
| rewrite USP; exact STK | rewrite USP; unfold MULTICOMB_DEPTH; lia | exact T0
| rewrite USP; pose proof (h_spx _ _ _ NH); lia
| rewrite USP; unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP; unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY); lia
| f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. rewrite USP in *. try clear XO1. clear LO1.
match goal with H : rw_cells _ _ OUT (f32 ?ws), L : length ?ws = 80%nat |- _ => rename H into XO1; rename L into LO1 end.

pose proof (ctx_tables _ _ X NH _ MU) as TAB. pose proof TAB as (_ & TB2 & _). pose proof (TB2 r INr) as SMC2.
unfold smrec_cells in SMC2. cbv zeta in SMC2.
pose proof (sub_ptr_read _ mo TAB ltac:(lia)) as SPR2. unfold NB_SUBMODES_PTR in SPR2. rewrite SPE in SPR2. clear TAB TB2.
zstep. rewrite SID. rewrite sx32_small by (unfold int31; lia). zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
zstep. replace (213512 + mo * 8) with (213512 + 8 * mo) by lia.
zstep. zstep. rewrite JEXC. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
try clear SMC; try clear SMC2; try clear SMB; try clear SPR; try clear SPR2.
call ((h_multicomb _ _ _ NH) (ST + 32) 374 (OUT + 320) (ST + 2080) bp lo (j_excbuf j) (skipn 80 ows) (j_interp_qlpc j) (Z_to_bv 64 0));
[ exact P1 | exact Lexc | right; reflexivity | exact XO2 | exact LO2 | exact P4 | exact Liq | exact BP
| rewrite USP; match goal with H : stk _ _ lo _ |- _ => exact H end | rewrite USP; unfold MULTICOMB_DEPTH; lia | exact T0
| rewrite USP; pose proof (h_spx _ _ _ NH); lia
| rewrite USP; unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP; unfold apart; pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY); lia
| f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. rewrite ?USP in *. try clear XO2. clear LO2.
match goal with H : rw_cells _ _ (OUT + 320) (f32 ?ws), L : length ?ws = 80%nat |- _ => rename H into XO2; rename L into LO2 end.
lazymatch type of XO1 with rw_cells _ ?mm _ (f32 ?o1) => lazymatch type of XO2 with rw_cells _ _ _ (f32 ?o2) =>
assert (XO : rw_cells rsegs mm OUT (f32 (o1 ++ o2)))
by (apply f32_join; [exact XO1 | rewrite LO1; replace (OUT + 4 * Z.of_nat 80) with (OUT + 320) by lia; exact XO2]);
assert (Lows2 : length (o1 ++ o2) = 160%nat) by (rewrite length_app, LO1, LO2; reflexivity)
end end.
clear XO1 XO2.

zstep. zstep. rewrite Icl. zstep. if_true. zstep.
f_tail.
apply evt_done. close_cut 2.
Qed.
End Seg.
