(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp X1i3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
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

Definition at_E3 (r : smrec) (mo olp bp bp2 sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs5 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) (Z_to_bv 64 (isv_sub X sub st)) (Z_to_bv 64 (usp + -256)) xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
(Z_to_bv 64 1) (Z_to_bv 64 (usp + -416)) (Z_to_bv 64 (ST + 1368)) xs5 (Z_to_bv 64 160) (Z_to_bv 64 (ST + 1368 + 160 * sub))
(Z_to_bv 64 sub) (Z_to_bv 64 (ST + 2184)) (Z_to_bv 64 bp2) (Z_to_bv 64 olp)
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 0x21794) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v56 fr = Z_to_bv 64 0x10e24 /\ f_v72 fr = Z_to_bv 64 (ST + 2228)
/\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST /\ f_v96 fr = Z_to_bv 64 (40 * sub)
/\ f_v104 fr = Z_to_bv 64 (ST + 2040) /\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ f_v128 fr = Z_to_bv 64 (olp + 1073741824)
/\ j_exc j = ST + 1368 /\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144 /\ 17 <= bp2 <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub < 4 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Ltac merge_at pcz :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?rom) =>
apply (evt_cut segs (fun ms => exists F' fc', ms = MS R F' (Z_to_bv 64 pcz) fc' rv m rom /\ frm0 fc') Q)
end.
Ltac merge_done := apply evt_done; sf_eexists 2%nat; split; [reflexivity | assumption].
Ltac merge_at2 pcz :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?rom) =>
apply (evt_cut segs (fun ms => exists F' fc' w0 w1, ms = MS (@bvmap_set 5 word (Z_to_bv 5 10) w0 (@bvmap_set 5 word (Z_to_bv 5 11) w1 R)) F' (Z_to_bv 64 pcz) fc' rv m rom /\ frm0 fc') Q)
end.
Ltac merge_done2 := apply evt_done; sf_eexists 4%nat; split; [reflexivity | assumption].
Ltac ubd := first [ ub_dec | (tnorm; rewrite ?bv_eqb_same_k; lit_if) | (rewrite srl30_guard by lia; lit_if) ].
Ltac bt p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then ubd else ub_step)); first [ ub_at_pc p | ub_show_pc_fail p ].
Ltac jmerge P := lazymatch goal with |- evt ?segs ?Q _ => apply (evt_cut segs P Q) end.
Ltac jfill := hnf; sf_eexists 5%nat; split; [ | reflexivity ]; assumption.
Ltac jdone := apply evt_done; jfill.
Ltac jopen := let H := fresh "HJ" in intro H; destruct H as (? & ? & ? & ? & ? & ? & ->); simp_regs.

#[using="notify STR_TOP NH"] Lemma nbE2 : forall r mo olp bp sub pit st b ms, at_E2 X r mo olp bp sub pit st b ms ->
evt rsegs (fun ms' => exists bp2, at_E3 r mo olp bp bp2 sub st b ms') ms.
Proof.
intros r mo olp bp sub pit st b ms AT.
first [ sf_destruct 36%nat AT as Fx fc m kc xra xa0 xs10 j ows iws sws fr -> FRM CTX FOK FRA E48 E56 E72 E80 E88 E96 E104 E112 E120 E128 EPV JEXC SAT SID BP PIT OLP SUB ISAVE | sf_fb; destruct AT as (Fx & fc & m & kc & xra & xa0 & xs10 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E56 & E72 & E80 & E88 & E96 & E104 & E112 & E120 & E128 & EPV & JEXC & SAT & SID & BP & PIT & OLP & SUB & ISAVE) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof (h_sp16 _ _ _ NH) as SP16.
box OLP.

zstep. zstep. step. step. zstep.
call ((h_san _ _ _ NH) (usp + -576) (f_e32 fr)); [exact FE | exact Lfe32 | lia | lia | reflexivity | reflexivity | assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. try clear FE. clear Lfe32.
match goal with H : rw_cells _ _ (usp + -576) (f32 ?ws), L : length ?ws = 40%nat |- _ => rename H into FE; rename L into Lfe32 end.

step. step. zstep.
merge_at 0x214a4; [ if_cases K1; [ merge_done | step; merge_done ] | ]. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx1 fcq1 -> FRM1 | sf_fb; destruct sfH_ as (Fx1 & fcq1 & -> & FRM1) ]. try clear K1.
step. step. step. zstep.
merge_at 0x214b8; [ if_cases K2; [ merge_done | step; merge_done ] | ]. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx2 fcq2 -> FRM2 | sf_fb; destruct sfH_ as (Fx2 & fcq2 & -> & FRM2) ]. try clear K2.
step. step. zstep.
merge_at2 0x214ec; [ if_cases K3; [ bt 0x214e4%Z; step; step; merge_done2 | bt 0x214d0%Z; step; zstep; merge_done2 ] | ]. intros ms' sfH_; first [ sf_destruct 6%nat sfH_ as Fx3 fcq3 w0 w1 -> FRM3 | sf_fb; destruct sfH_ as (Fx3 & fcq3 & w0 & w1 & -> & FRM3) ]. try clear K3. simp_regs.
step. step. step. step. step. zstep.

rewrite EPV in *.
set (QQ := fun ms' : machine_state => exists bp2, at_E3 r mo olp bp bp2 sub st b ms').
lazymatch goal with |- evt _ _ (MS ?R0 _ _ _ _ ?mm ?rom) =>
set (J := fun (s10v : word) (pcv : Z) (ms : machine_state) =>
exists (wa1 wa2 wa3 : word) (F' : bvmap 5 word) (fc' : bv 32), frm0 fc' /\
ms = MS (@bvmap_set 5 word (Z_to_bv 5 26) s10v (@bvmap_set 5 word (Z_to_bv 5 11) wa1
(@bvmap_set 5 word (Z_to_bv 5 12) wa2 (@bvmap_set 5 word (Z_to_bv 5 13) wa3 R0)))) F' (Z_to_bv 64 pcv) fc' None mm rom);
assert (CJ5 : forall ms v, 17 <= v <= 144 -> J (Z_to_bv 64 v) 0x21794 ms -> evt rsegs QQ ms)
end.
{ intros ms v Hv sfH_; first [ sf_destruct 7%nat sfH_ as wa1 wa2 wa3 F' fc' FR' -> | sf_fb; destruct sfH_ as (wa1 & wa2 & wa3 & F' & fc' & FR' & ->) ]. subst J QQ. simp_regs.
apply evt_done. exists v. unfold boxed in OLP. close_cut 3. }
assert (CJR : forall ms w, J w 0x2178c ms -> evt rsegs QQ ms).
{ intros ms w; jopen.
step. zstep. apply (CJ5 _ bp); [lia | jfill]. }
assert (CJA : forall ms, J (Z_to_bv 64 pit) 0x21778 ms -> evt rsegs QQ ms).
{ intros ms; jopen.
zstep. if_cases K.
+ step. zstep. apply (CJ5 _ pit); [lia | jfill].
+ step. zstep. apply (CJ5 _ pit); [lia | jfill]. }
assert (CJ3 : forall ms w, J w 0x216a4 ms -> evt rsegs QQ ms).
{ intros ms w; jopen.
zstep. step. step. step. zstep. if_cases K.
+ eapply CJR; jfill.
+ bt 0x216c4%Z. zstep. rewrite sx32_ssmall by lia.
bt 0x216d8%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x216ec); [ if_cases KA1; [ jdone | bt 0x216ec%Z; jdone ] | intro; jopen ].
bt 0x216f4%Z. zstep. if_cases KB1; [ apply CJA; jfill | ].
bt 0x21718%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x2172c); [ if_cases KA2; [ jdone | bt 0x2172c%Z; jdone ] | intro; jopen ].
bt 0x21734%Z. zstep. if_cases KB2; [ apply CJA; jfill | ].
bt 0x21758%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x2176c); [ if_cases KA3; [ jdone | bt 0x2176c%Z; jdone ] | intro; jopen ].
bt 0x21774%Z. zstep. if_cases KB3; [ eapply CJR; jfill | apply CJA; jfill ]. }
assert (CJ2 : forall ms w, J w 0x215c8 ms -> evt rsegs QQ ms).
{ intros ms w; jopen.
zstep. rewrite E56. step. step. step. step. step. zstep. if_cases K.
+ eapply CJ3; jfill.
+ zstep. rewrite sx32_ssmall by lia.
bt 0x21604%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x21618); [ if_cases KA1; [ jdone | bt 0x21618%Z; jdone ] | intro; jopen ].
bt 0x21620%Z. zstep. if_cases KB1; [ apply CJA; jfill | ].
bt 0x21644%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x21658); [ if_cases KA2; [ jdone | bt 0x21658%Z; jdone ] | intro; jopen ].
bt 0x21660%Z. zstep. if_cases KB2; [ apply CJA; jfill | ].
bt 0x21684%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x21698); [ if_cases KA3; [ jdone | bt 0x21698%Z; jdone ] | intro; jopen ].
bt 0x216a0%Z. zstep. if_cases KB3; [ apply CJA; jfill | eapply CJ3; jfill ]. }

if_cases K0.
- eapply CJ2; jfill.
- bt 0x21510%Z. zstep. rewrite sx32_ssmall by lia.
bt 0x21524%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x21538); [ if_cases KA1; [ jdone | bt 0x21538%Z; jdone ] | intro; jopen ].
bt 0x21540%Z. zstep. if_cases KB1; [ eapply CJ2; jfill | ].
bt 0x21564%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x21578); [ if_cases KA2; [ jdone | bt 0x21578%Z; jdone ] | intro; jopen ].
bt 0x21580%Z. zstep. if_cases KB2; [ eapply CJ2; jfill | ].
bt 0x215a4%Z. zstep.
jmerge (J (Z_to_bv 64 pit) 0x215b8); [ if_cases KA3; [ jdone | bt 0x215b8%Z; jdone ] | intro; jopen ].
bt 0x215c4%Z. zstep. if_cases KB3; [ apply (CJ5 _ pit); [ lia | jfill ] | eapply CJ2; jfill ].
Qed.
End Seg.
