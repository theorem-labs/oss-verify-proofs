(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0p2.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz X1m1 X1ky X1lg.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rffin_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

Lemma rfree_fin0 {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x31b78) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros TP MR MI FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ]. destruct GL as (LK & NL & _).
unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
rewrite (unsigned_lit 316496) in ERR by lia. change (316496 + -164) with 316332 in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x31b8c)) with (Z_to_bv 64 0x31b8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. sf_eexists 16%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 316496) by lia. change (316496 + -164) with 316332. exact ERR.
Qed.

Definition rfmun_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x31ba8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

Lemma rfree_tomunmap {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv rsegs m -> 0 < len < 2^64 ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x31b78) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ]. destruct GL as (LK & NL & _).
unfold alloc_ceiling, RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
rewrite (unsigned_lit 316496) in ERR by lia. change (316496 + -164) with 316332 in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x31b8c)) with (Z_to_bv 64 0x31b8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }

st1. st1. st1. st1.
replace (ret_pc (Z_to_bv 64 0x31b94)) with (Z_to_bv 64 0x31b94) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
apply evt_done. unfold rfmun_post. sf_eexists 14%nat. split; [rewrite (unsigned_lit 316496) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [rewrite (unsigned_lit 316496) by lia; change (316496 + -164) with 316332; exact ERR| exact MR2].
Qed.

Lemma rerrno_avoids_repfoot {RCEIL : RunCeiling} : forall st m a, rmrep st m -> 316332 <= a < 316336 -> ~ rrepfoot st a.
Proof.
intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ].
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- first [ sf_destruct 4%nat C as ak ar Hak Hin | sf_fb; destruct C as (ak & ar & Hak & Hin) ].
first [ pose proof (rarea_conc st ak ar WF Hak) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | sf_fb; destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ].
first [ pose proof (WR _ _ Hra) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF) ]. destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
- first [ sf_destruct 4%nat C as b gh Hb Hin | sf_fb; destruct C as (b & gh & Hb & Hin) ].
first [ pose proof (rgroup_conc st b gh WF Hb) as sfP_; sf_destruct 9%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 SbA RB0 RBC | sf_fb; destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC) ].
first [ pose proof (WR _ _ Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF) ]. destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
- first [ sf_destruct 7%nat C as rid r v Hr Hk Hin HC | sf_fb; destruct C as (rid & r & v & Hr & Hk & Hin & HC) ].
first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed.

Lemma rmrep_transport_frame_errno {RCEIL : RunCeiling} : forall st m m' (sp : Z),
rmrep st m -> munch [(sp - 48, sp); (316332, 316336)]%Z m m' -> wmono rsegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof.
intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
- intros a Ha. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in HS.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ unfold RCTX in C. lia.
+ unfold RMLOCK in C. lia.
+ unfold RNEED_LOCKS in C. lia.
+ unfold RPAGE_SIZE in C. lia.
+ first [ sf_destruct 4%nat C as ak ar Hak Hin | sf_fb; destruct C as (ak & ar & Hak & Hin) ].
first [ pose proof (rarea_conc st ak ar WF Hak) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | sf_fb; destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]. unfold alloc_ceiling in RBC. lia.
+ first [ sf_destruct 4%nat C as b gh Hb Hin | sf_fb; destruct C as (b & gh & Hb & Hin) ].
first [ pose proof (rgroup_conc st b gh WF Hb) as sfP_; sf_destruct 9%nat sfP_ as rb Hrb Cb Krb Sb0 Sb1 SbA RB0 RBC | sf_fb; destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC) ]. unfold alloc_ceiling in RBC. lia.
+ first [ sf_destruct 7%nat C as rid r v Hr Hk Hin HC | sf_fb; destruct C as (rid & r & v & Hr & Hk & Hin & HC) ].
first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RBC _ | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _) ]. unfold alloc_ceiling in RBC. lia.
+ unfold RGOT_SSP in C. lia.
+ unfold RSSP_GUARD in C. lia.
- intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

Lemma rfree_fin1 {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
le4 ew = le4 errv ->
rw_cells rsegs m (errno_addr tp) [C4 e'] ->
stk rsegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt rsegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (316332, 316336)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x31ba8) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (316332, 316336)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold alloc_ceiling, RATP in *. subst tp.
rewrite (unsigned_lit 316496) in ERR by lia. change (316496 + -164) with 316332 in ERR.
rewrite (unsigned_lit 316496) by lia. change (316496 + -164) with 316332.

st1.

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. sf_eexists 16%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 316496) by lia. change (316496 + -164) with 316332.
eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
