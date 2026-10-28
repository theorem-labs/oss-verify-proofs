(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1hn X1hp.
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

Definition at_Hpc (pc : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : iclob) (xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 : word)
(j : nb_junk) (ows iws sws : list word) (fr : frame),
ms = MS (mkR xra (Z_to_bv 64 (usp + -912)) gp tp (c_t0 k) (c_t1 k) (c_t2 k) xs0 xs1 xa0
(c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 (ST + 2184)) xs10 xs11
(c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k))
Fx (Z_to_bv 64 pc) fc None m (seg_rom rsegs)
/\ frm0 fc /\ nbctx X m st b j ows iws sws /\ frame_ok fr /\ frame_at X m fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v88 fr = Z_to_bv 64 ST /\ f_v104 fr = Z_to_bv 64 (ST + 2040)
/\ j_exc j = ST + 1368.
Definition at_H2 := at_Hpc 0x21e34.
Definition at_H3 := at_Hpc 0x21e94.

#[using="notify STR_TOP NH"] Lemma nbH1 : forall st b ms, at_H X st b ms -> evt rsegs (at_H2 st b) ms.
Proof.
intros st b ms AT. unfold at_H2.
first [ sf_destruct 34%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E104 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E104 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].

zstep. rewrite Ihp. rewrite sx32_small by (unfold int31; lia). zstep. if_false.
zstep. zstep. rewrite E48. zstep.
pose proof (lay_ST_OUT _ _ _ _ _ _ _ _ _ LAY) as LSO.
pose proof (h_stal _ _ _ NH) as STAL. pose proof (h_out4 _ _ _ NH) as OUT4.
pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY) as LSS. pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ LAY) as LOS.
unfold NBSTATE_SIZEOF in LSS.
destruct Iwb as [EW | EW]; rewrite EW; rewrite sx32_small by (unfold int31; lia).
-
zstep. if_true. zstep. zstep. zstep. rewrite E80. zstep. zstep.
call ((h_hp _ _ _ NH) OUT (ST + 2160) 1 lo ows (j_mem_hp j));
[ exact XO | exact Lows | exact P6 | exact Lmhp | left; reflexivity | unfold apart; (clear - LSO X ptr; lia)
| lia | exact OUT4 | lia | lia
| rewrite USP; exact STK | rewrite USP; unfold HIGHPASS_DEPTH; lia | exact T0 | rewrite USP; lia
| rewrite USP; unfold apart in *; lia | rewrite USP; unfold apart in *; lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. rewrite ?USP in *. try clear XO. clear Lows. try clear P6. clear Lmhp. clear LSO.
match goal with H : rw_cells _ _ OUT (f32 ?ws), L : length ?ws = _ |- _ => rename H into XO; rename L into Lows end.
match goal with H : rw_cells _ _ (ST + 2160) (f32 ?ws), L : length ?ws = _ |- _ => rename H into P6; rename L into Lmhp end.
apply evt_done. close_cut 13.
-
zstep. if_false. zstep. zstep. zstep. zstep. rewrite E80. zstep. zstep.
call ((h_hp _ _ _ NH) OUT (ST + 2160) 3 lo ows (j_mem_hp j));
[ exact XO | exact Lows | exact P6 | exact Lmhp | right; reflexivity | unfold apart; (clear - LSO X ptr; lia)
| lia | exact OUT4 | lia | lia
| rewrite USP; exact STK | rewrite USP; unfold HIGHPASS_DEPTH; lia | exact T0 | rewrite USP; lia
| rewrite USP; unfold apart in *; lia | rewrite USP; unfold apart in *; lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | assumption | assumption | ].
cbv beta delta [callR]. try rename MI0 into MI. rewrite ?USP in *. try clear XO. clear Lows. try clear P6. clear Lmhp. clear LSO.
match goal with H : rw_cells _ _ OUT (f32 ?ws), L : length ?ws = _ |- _ => rename H into XO; rename L into Lows end.
match goal with H : rw_cells _ _ (ST + 2160) (f32 ?ws), L : length ?ws = _ |- _ => rename H into P6; rename L into Lmhp end.
apply evt_done. close_cut 13.
Qed.

Ltac merge_at pcz :=
lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?rom) =>
apply (evt_cut segs (fun ms => exists F' fc', ms = MS R F' (Z_to_bv 64 pcz) fc' rv m rom /\ frm0 fc') Q)
end.
Ltac merge_done := apply evt_done; sf_eexists 2%nat; split; [reflexivity | assumption].

#[using="notify STR_TOP NH"] Lemma nbH2 : forall st b ms, at_H2 st b ms -> evt rsegs (at_H3 st b) ms.
Proof.
intros st b ms AT. unfold at_H3.
first [ sf_destruct 31%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E88 E104 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E88 & E104 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.

lazymatch type of P9 with rw_cells _ _ _ (f32 ?lv) =>
destruct lv as [|l0 [|l1 [|l2 [|lx lrest]]]]; try (cbn in Llev; lia) end.
rewrite !f32_cons, f32_nil in P9.
step. step. step. step. step. step. step. step. step.
step.
merge_at 0x21e60; [ if_cases K1; [ merge_done | step; merge_done ] | ].
intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx1 fcq1 -> FRM1 | sf_fb; destruct sfH_ as (Fx1 & fcq1 & -> & FRM1) ].
step. step. step. step. step. step.
step.
merge_at 0x21e80; [ if_cases K2; [ merge_done | step; merge_done ] | ].
intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as Fx2 fcq2 -> FRM2 | sf_fb; destruct sfH_ as (Fx2 & fcq2 & -> & FRM2) ].
step. step. step. step.
if_cases K3.
-
rewrite <- f32_nil, <- !f32_cons in P9. apply evt_done. close_cut 13.
- step. rewrite <- f32_nil, <- !f32_cons in P9. apply evt_done. close_cut 13.
Qed.
End Seg.
