(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3.
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

Definition at_E3 (r : smrec) (mo olp bp bp2 sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -896)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 2120)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 (160 * sub)) (Z_to_bv 64 (nb_isave_ptr OUT st)) (Z_to_bv 64 bp2) (Z_to_bv 64 bp) (Z_to_bv 64 (ST + 1368)) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 (usp + -256)) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 olp) (Z_to_bv 64 sub)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x1f654) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 OUT /\ f_v64 fr = Z_to_bv 64 0x1008c
/\ f_v80 fr = Z_to_bv 64 (ST + 2228) /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (160 * sub)
/\ f_v104 fr = Z_to_bv 64 A /\ f_v112 fr = Z_to_bv 64 0
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144 /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Ltac merge_at pcz :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?rom) =>
apply (evt_cut segs (fun ms => exists F' fc', ms = MS R F' (Z_to_bv 64 pcz) fc' rv m rom /\ frm0 fc') Q)
end.
Ltac merge_done := apply evt_done; sf_eexists 2%nat; split; [reflexivity | assumption].

#[using="notify STR_TOP NH"] Lemma nbE2 : forall r mo olp bp sub pit st b ms, at_E2 X r mo olp bp sub pit st b ms ->
evt rsegs (fun ms' => exists bp2, at_E3 r mo olp bp bp2 sub st b ms') ms.
Proof.
intros r mo olp bp sub pit st b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m kc xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E64 E80 E88 E96 E104 E112 EPV JEXC SAT SID BP PIT OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E64 & E80 & E88 & E96 & E104 & E112 & EPV & JEXC & SAT & SID & BP & PIT & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
box OLP.

zstep. zstep. step. step. zstep.
call ((h_san _ _ _ NH) (usp + -576) (f_e32 fr)); [exact FE | exact Lfe32 | reflexivity | reflexivity | assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. try clear FE. clear Lfe32.
match goal with H : rw_cells _ _ (usp + -576) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FE; rename L into Lfe32 end.

step. step. zstep.
merge_at 0x1f4d0; [ if_cases K1; [ merge_done | step; merge_done ] | ]. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx1 fcq1 -> FRM1 | sf_fb; destruct sfH_ as (Fx1 & fcq1 & -> & FRM1) ]. try clear K1.
step. step. step. zstep.
merge_at 0x1f4e4; [ if_cases K2; [ merge_done | step; merge_done ] | ]. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx2 fcq2 -> FRM2 | sf_fb; destruct sfH_ as (Fx2 & fcq2 & -> & FRM2) ]. try clear K2.
step. step. step. zstep.
merge_at 0x1f4f8; [ if_cases K3; [ merge_done | step; merge_done ] | ]. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx3 fcq3 -> FRM3 | sf_fb; destruct sfH_ as (Fx3 & fcq3 & -> & FRM3) ]. try clear K3.
step. step. step. step. step. zstep.

rewrite EPV in *.
set (QQ := fun ms' : machine_state => exists bp2, at_E3 r mo olp bp bp2 sub st b ms').
lazymatch goal with |- evt _ _ (MS ?R0 _ _ _ _ ?mm ?rom) =>
set (J := fun (s4v : word) (pcv : Z) (ms : machine_state) =>
exists (wa1 wa2 wa3 : word) (F' : bvmap 5 word) (fc' : bv 32), frm0 fc' /\
ms = MS (@bvmap_set 5 word (Z_to_bv 5 20) s4v (@bvmap_set 5 word (Z_to_bv 5 11) wa1
(@bvmap_set 5 word (Z_to_bv 5 12) wa2 (@bvmap_set 5 word (Z_to_bv 5 13) wa3 R0)))) F' (Z_to_bv 64 pcv) fc' None mm rom);
assert (CJ5 : forall ms v, 17 <= v <= 144 -> J (Z_to_bv 64 v) 0x1f654 ms -> evt rsegs QQ ms)
end.
{ intros ms v Hv sfH_; first [ sf_destruct 7%nat sfH_ as wa1 wa2 wa3 F' fc' FR' -> | sf_fb; destruct sfH_ as (wa1 & wa2 & wa3 & F' & fc' & FR' & ->) ]. subst J QQ. simp_regs.
apply evt_done. exists v. unfold boxed in OLP. close_cut 2. }
assert (CJ4 : forall ms w4, J w4 0x1f64c ms -> evt rsegs QQ ms).
{ intros ms w4 sfH_; first [ sf_destruct 7%nat sfH_ as wa1 wa2 wa3 F' fc' FR' -> | sf_fb; destruct sfH_ as (wa1 & wa2 & wa3 & F' & fc' & FR' & ->) ]. simp_regs.
step. zstep. apply (CJ5 _ bp); [lia | cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption]. }
assert (CJ3 : forall ms, J (Z_to_bv 64 pit) 0x1f638 ms -> evt rsegs QQ ms).
{ intros ms sfH_; first [ sf_destruct 7%nat sfH_ as wa1 wa2 wa3 F' fc' FR' -> | sf_fb; destruct sfH_ as (wa1 & wa2 & wa3 & F' & fc' & FR' & ->) ]. simp_regs.
zstep. if_cases K.
+ step. zstep. apply (CJ5 _ pit); [lia | cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption].
+ step. zstep. apply (CJ5 _ pit); [lia | cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption]. }
assert (CJ2 : forall ms w4, J w4 0x1f5d4 ms -> evt rsegs QQ ms).
{ intros ms w4 sfH_; first [ sf_destruct 7%nat sfH_ as wa1 wa2 wa3 F' fc' FR' -> | sf_fb; destruct sfH_ as (wa1 & wa2 & wa3 & F' & fc' & FR' & ->) ]. simp_regs.
zstep. step. step. step. zstep. if_cases K.
+ eapply CJ4. cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption.
+ zstep. rewrite sx32_ssmall by lia. zstep. zstep; zstep; zstep; zstep. zstep. zstep. if_cases K1; [ apply CJ3; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | ].
zstep. zstep; zstep; zstep; zstep. zstep. if_cases K2; [ apply CJ3; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | ].
zstep. zstep; zstep; zstep; zstep. zstep. if_cases K3; [ eapply CJ4; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | apply CJ3; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption ]. }
assert (CJ1 : forall ms w4, J w4 0x1f564 ms -> evt rsegs QQ ms).
{ intros ms w4 sfH_; first [ sf_destruct 7%nat sfH_ as wa1 wa2 wa3 F' fc' FR' -> | sf_fb; destruct sfH_ as (wa1 & wa2 & wa3 & F' & fc' & FR' & ->) ]. simp_regs.
zstep. rewrite E64. step. step. step. step. step. zstep. if_cases K.
+ eapply CJ2. cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption.
+ zstep. rewrite sx32_ssmall by lia. zstep. zstep; zstep; zstep; zstep. zstep. zstep. if_cases K1; [ apply CJ3; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | ].
zstep. zstep; zstep; zstep; zstep. zstep. if_cases K2; [ apply CJ3; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | ].
zstep. zstep; zstep; zstep; zstep. zstep. zstep. if_cases K3; [ apply CJ3; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | eapply CJ2; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption ]. }

if_cases K0.
- eapply CJ1. cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption.
- zstep. rewrite sx32_ssmall by lia. zstep. zstep; zstep; zstep; zstep. zstep. zstep. if_cases K1; [ eapply CJ1; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | ].
zstep. zstep; zstep; zstep; zstep. zstep. if_cases K2; [ eapply CJ1; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption | ].
zstep. zstep; zstep; zstep; zstep. step. zstep. if_cases K3; [ apply (CJ5 _ pit); [lia | cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption] | eapply CJ1; cbv beta delta [J]; sf_eexists 5%nat; split; [ | reflexivity ]; assumption ].
Qed.
End Seg.
