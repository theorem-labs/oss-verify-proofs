(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1n0 X1n1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Local Ltac xport MU WM H :=
eapply rw_cells_transport in H; [| exact MU | exact WM |
cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; rewrite ?cells_size_f32, ?length_f32; cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; lia].

Local Ltac xport_mem mo MU WM :=
repeat match goal with H : rw_cells rsegs mo _ _ |- _ => first [xport MU WM H | clear H] end.

Local Ltac piece_sizes E1 E2 E3 E4 E5 E6 E7 E8 E12 :=
rewrite ?cells_size_app, ?cells_size_f32, ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E12.

Local Ltac solve_munch MU1 MU2 ELBD :=
eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]];
unfold ctlW; cbn [creq_ivs creq_size app]; intros x; rewrite !outside_cons, outside_blocks_ivs; cbn [fst snd outside creq_size]; intros (O1 & O2 & O3);
[split; [lia| exact I]|]; split; [| exact I];
first [ lia | specialize (O3 _ ltac:(rewrite ELBD; left; reflexivity)); cbn [blk_addr blk_size fst snd] in O3; lia ].

Theorem rctl_nbB {RCEIL : RunCeiling} : forall st, rctl_atP (fun r => creq_grp1 r = false) (DecNB st).
Proof.
intros st OUT STEREO S LBD r P lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
GRP REP DEPTH OK PRE PTR SPA TP BR NDI LAP AP APB ST CLO LO MI FRM -> -> ->.
cbn [ctl_depth] in LO. cbn [decst_rep] in REP. destruct REP as [ELBD NB].
pose proof (BR _ ltac:(rewrite ELBD; left; reflexivity)) as BRS. unfold blk_addr, blk_size in BRS. cbn [fst snd] in BRS.
first [ sf_destruct 5%nat BRS as S0 S16 _ SCE SIMG | sf_fb; destruct BRS as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE, CLO. unfold NBSTATE_SIZEOF in *.
pose proof (APB _ ltac:(rewrite ELBD; left; reflexivity)) as APS. unfold blk_addr, blk_size in APS. cbn [fst snd] in APS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
first [ sf_destruct 7%nat NB as AL POS INV j JOK CBS X | sf_fb; destruct NB as (AL & POS & INV & j & JOK & CBS & X) ].
pose proof JOK as sfP_; first [ sf_destruct 13%nat sfP_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 | sf_fb; destruct sfP_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13) ].
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].
apply (nb_pieces_of_cells rsegs _ _ _ m S OUT STEREO st j JOK) in X.
first [ sf_destruct 19%nat X as P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 | sf_fb; destruct X as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18) ].
unfold nb_hdr_cells in P0. unfold nb_cfg_cells in P14. unfold nb_ucb_cells, cb_cells in P16. cbn [fst snd] in P16. unfold nb_tail_cells in P18.

eapply evt_cut.
{ eapply (nbctl_entry S P (ctl_req_code r) lo _ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0);
[reflexivity| exact TP| exact ST| lia| lia| lia| lia| lia| | exact MI| exact AL].
unfold nbctl_code_ok. destruct r; cbn [ctl_req_code]; cbn in OK; clear - OK; tauto. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 13%nat sfH_ as xt1 xa0 xa1 xa2 xa4 j0 m1 -> FR MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (xt1 & xa0 & xa1 & xa2 & xa4 & j0 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1) ]. unfold nbctl_frame in FR.
xport MU1 WM1 P0. xport MU1 WM1 P1. xport MU1 WM1 P2. xport MU1 WM1 P3. xport MU1 WM1 P4. xport MU1 WM1 P5. xport MU1 WM1 P6.
xport MU1 WM1 P7. xport MU1 WM1 P8. xport MU1 WM1 P9. xport MU1 WM1 P10. xport MU1 WM1 P11. xport MU1 WM1 P12. xport MU1 WM1 P13.
xport MU1 WM1 P14. xport MU1 WM1 P15. xport MU1 WM1 P16. xport MU1 WM1 P17. xport MU1 WM1 P18.
destruct r; cbn in OK; try (exfalso; exact OK); try discriminate GRP; cbn [ctl_req_code creq_size] in *; cbn [creq_pre] in PRE; cbn [creq_ptr_ok] in PTR; try destruct PTR as [PP PA].
-
destruct PRE as (ws & ARG & LWS). xport MU1 WM1 ARG.
eapply evt_cut.
{ eapply (nbarm_get_pi_gain S P _ _ gp tp t0 xt1 t2 xa0 xa1 xa2 xa4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 MI1 ltac:(lia) AL ws (j_pi_gain j) ARG LWS P7 E6). all: first [assumption | lia]. }
cbv beta. intros ms2 sfH_; destruct sfH_ as (m2 & F2 & ys0 & ya1 & ws' & OUT2 & ARG' & LWS' & P7' & MU2 & WM2 & MI2). clear ARG P7.
xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI2| exact OUT2]. }
cbv beta. intros ms3 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F' & ->).
assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -96)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F') | exact (fc) | exact (m2) | ] | sf_fb; exists F', fc, m2 ].
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [solve_munch MU1 MU2 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; exists ws'; split; [exact ARG'| exact LWS']|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU2 WM2 EXQ. exact EXQ.
-
destruct PRE as ((ws & ARG & LWS) & EXR). cbn [dec_exc_ready] in EXR. xport MU1 WM1 ARG. xport MU1 WM1 EXR.
eapply evt_cut.
{ eapply (nbarm_get_exc S P _ _ gp tp t0 xt1 t2 xa0 xa1 xa2 xa4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 MI1 ltac:(lia) AL ws (j_excbuf j) ARG LWS EXR P1 E1 ltac:(lia) FRM PP PA). }
cbv beta. intros ms2 sfH_; destruct sfH_ as (m2 & F2 & fc2 & ys0 & ya1 & OUT2 & (MI2 & FRM2 & (ws' & ARG' & LWS') & EXR' & P1' & MU2 & WM2)). clear ARG P1 EXR.
xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI2| exact OUT2]. }
cbv beta. intros ms3 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F' & ->).
assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -96)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F') | exact (fc2) | exact (m2) | ] | sf_fb; exists F', fc2, m2 ].
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [solve_munch MU1 MU2 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; exists ws'; split; [exact ARG'| exact LWS']|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros _. exact EXR'.
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG.
pose proof (rw_cells_bound _ _ _ _ ARG) as PB. cbn [cells_size csize Nat.add] in PB.
eapply evt_cut. { apply (nbarm_get_dtx_status S P _ _ gp tp t0 xt1 t2 xa0 xa1 xa2 xa4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 ltac:(lia) AL _ _ _ _ _ P18). all: first [assumption | lia]. }
cbv beta. intros ms2 OUT2.
eapply evt_cut. { eapply (nbctl_exit_get (bv_unsigned sp) P w j0); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1| exact OUT2]. }
cbv beta. intros ms3 (m3 & (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F' & ->) & EM3 & MI3 & ARG3). replace (P + Z.of_nat 0) with P in EM3 by lia.
assert (MU3 : munch [(P, P + 4)] m1 m3) by (rewrite EM3; apply munch_write; rewrite ?length_le4; [apply munch_refl| lia| lia| cbn; lia]).
assert (WM3 : wmono rsegs m1 m3) by (rewrite EM3; apply wmono_write; apply wmono_refl).
clear ARG. xport_mem m1 MU3 WM3.
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -96)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F') | exact (fc) | exact (m3) | ] | sf_fb; exists F', fc, m3 ].
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [solve_munch MU1 MU3 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; split; [exact ARG3| exact Idt]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU3 WM3 EXQ. exact EXQ.
-
destruct OK as [EP HOFF].
eapply evt_cut.
{ apply (nbarm_set_innovation_save S P _ _ gp tp t0 xt1 t2 xa0 xa1 xa2 xa4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 MI1 ltac:(lia) AL _ P8). }
cbv beta. intros ms2 sfH_; destruct sfH_ as (m2 & F2 & ys0 & ya1 & OUT2 & P8' & MU2 & WM2 & MI2). clear P8.
xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI2| exact OUT2]. }
cbv beta. intros ms3 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F' & ->).
assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -96)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F') | exact (fc) | exact (m2) | ] | sf_fb; exists F', fc, m2 ].
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]];
unfold ctlW; cbn [creq_ivs creq_size app]; intros x; rewrite !outside_cons, outside_blocks_ivs; cbn [fst snd outside]; intros (O1 & O3);
(split; [| exact I]); [lia| specialize (O3 _ ltac:(rewrite ELBD; left; reflexivity)); cbn [blk_addr blk_size fst snd] in O3; lia]. }
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [unfold nb_inv in *; cbn; repeat split; try assumption; try lia|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
unfold nb_isave_ptr. cbn [nb_innov_save set_nb_innov_save]. rewrite <- EP.
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post]; exact I|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU2 WM2 EXQ. exact EXQ.
Qed.

Theorem rctl_nb {RCEIL : RunCeiling} : forall st, rctl_at (DecNB st).
Proof. intros st. apply rctl_at_join; [apply rctl_nbA| apply rctl_nbB]. Qed.
