(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1n0 X1n4 X1n5 X1mc.
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

Theorem rctl_isave_nb {RCEIL : RunCeiling} : forall st, rctl_isave_at (DecNB st).
Proof.
intros st OUT0 OUT STEREO S LBD off P lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP DEPTH OK TP BR NDI LAP AP APB ST CLO LO MI FRM -> -> ->.
change Ubsan.M.loaded_segments with X1ff.rsegs in *.
cbn [ctl_depth] in LO. cbn [decst_rep] in REP. destruct REP as [ELBD NB].
pose proof (BR _ ltac:(rewrite ELBD; left; reflexivity)) as BRS. unfold blk_addr, blk_size in BRS. cbn [fst snd] in BRS.
first [ sf_destruct 5%nat BRS as S0 S16 _ SCE SIMG | sf_fb; destruct BRS as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE, CLO. unfold NBSTATE_SIZEOF in *.
pose proof (APB _ ltac:(rewrite ELBD; left; reflexivity)) as APS. unfold blk_addr, blk_size in APS. cbn [fst snd] in APS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
first [ sf_destruct 7%nat NB as AL POS INV j JOK CBS X | sf_fb; destruct NB as (AL & POS & INV & j & JOK & CBS & X) ].
pose proof JOK as sfP_; first [ sf_destruct 13%nat sfP_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 | sf_fb; destruct sfP_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13) ].
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].
apply (nb_pieces_of_cells rsegs _ _ _ m S OUT0 STEREO st j JOK) in X.
first [ sf_destruct 19%nat X as P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 | sf_fb; destruct X as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18) ].
unfold nb_hdr_cells in P0. unfold nb_cfg_cells in P14. unfold nb_ucb_cells, cb_cells in P16. cbn [fst snd] in P16. unfold nb_tail_cells in P18.
cbn [ctl_req_code creq_size] in AP, APB, APS |- *. cbn in OK. destruct OK as [EP HOFF].

eapply evt_cut.
{ eapply (nbctl_entry S P 104 lo _ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0);
[reflexivity| exact TP| exact ST| lia| lia| lia| lia| lia| | exact MI| exact AL].
unfold nbctl_code_ok. lia. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 13%nat sfH_ as xt1 xa0 xa1 xa2 xa4 j0 m1 -> FR MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (xt1 & xa0 & xa1 & xa2 & xa4 & j0 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1) ]. unfold nbctl_frame in FR.
xport MU1 WM1 P0. xport MU1 WM1 P1. xport MU1 WM1 P2. xport MU1 WM1 P3. xport MU1 WM1 P4. xport MU1 WM1 P5. xport MU1 WM1 P6.
xport MU1 WM1 P7. xport MU1 WM1 P8. xport MU1 WM1 P9. xport MU1 WM1 P10. xport MU1 WM1 P11. xport MU1 WM1 P12. xport MU1 WM1 P13.
xport MU1 WM1 P14. xport MU1 WM1 P15. xport MU1 WM1 P16. xport MU1 WM1 P17. xport MU1 WM1 P18.

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

Theorem rctl_isave_sb {RCEIL : RunCeiling} : forall s low, rctl_isave_at (DecSB s low).
Proof.
intros s low OUT0 OUT STEREO S LBD off P lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
REP DEPTH OK TP BR NDI LAP AP APB ST CLO LO MI FRM -> -> ->.

change Ubsan.M.loaded_segments with X1ff.rsegs in *.
cbn [ctl_depth] in LO. fold (ctl_depth low) in LO. cbn [dec_depth] in DEPTH.
cbn [decst_rep] in REP. fold (DREP OUT0 STEREO m) in REP.
first [ sf_destruct 12%nat REP as a j LBL ELBD AL POS INV JOK X BU OUTL RL | sf_fb; destruct REP as (a & j & LBL & ELBD & AL & POS & INV & JOK & X & BU & OUTL & RL) ].
assert (INL : forall b, In b LBL -> In b LBD) by (intros b Hb; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (INS : In (sbd_blk s, S, SBSTATE_SIZEOF) LBD) by (rewrite ELBD; left; reflexivity).
pose proof (BR _ INS) as BRS. unfold blk_addr, blk_size in BRS. cbn [fst snd] in BRS. unfold SBSTATE_SIZEOF in BRS.
first [ sf_destruct 5%nat BRS as S0 S16 _ SCE SIMG | sf_fb; destruct BRS as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE, CLO.
pose proof (APB _ INS) as APS. unfold blk_addr, blk_size, SBSTATE_SIZEOF in APS. cbn [fst snd] in APS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (dec_depth_pos low) as DPOS.
assert (CDP : 64 <= ctl_depth low) by (clear; induction low; cbn; lia).
assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite ELBD in NDI; exact (NoDup_map_app_r _ _ _ NDI)).
assert (LAPL : lbd_apart LBL) by (eapply lbd_apart_sub; [exact LAP| exact INL]).
assert (SAP : forall b, In b (tl (sb_blocks s S a) ++ LBL) -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S).
{ intros b Hb. pose proof NDI as ND0. pose proof LAP as LAP0. rewrite ELBD in ND0, LAP0.
change (sb_blocks s S a ++ LBL) with ([(sbd_blk s, S, SBSTATE_SIZEOF)] ++ (tl (sb_blocks s S a) ++ LBL)) in ND0, LAP0.
destruct (apart_parts _ _ _ _ ND0 LAP0 ltac:(left; reflexivity) Hb) as [D|D]; unfold blk_addr, blk_size, SBSTATE_SIZEOF in D |- *; cbn [fst snd] in D; lia. }
assert (SAPL : forall b, In b LBL -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S) by (intros b Hb; apply SAP; apply in_app_iff; right; exact Hb).
assert (SAPB : forall b, In b (tl (sb_blocks s S a)) -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S) by (intros b Hb; apply SAP; apply in_app_iff; left; exact Hb).
assert (LCE : forall b, In b LBL -> 0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling).
{ intros b Hb. first [ pose proof (BR _ (INL _ Hb)) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC _ | sf_fb; destruct (BR _ (INL _ Hb)) as (B0 & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia. }
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Imo Ifs Iffs Isfs Inbs Ilpc Ifi Isr Ien Ies Isid Iis | sf_fb; destruct sfP_ as (Imo & Ifs & Iffs & Isfs & Inbs & Ilpc & Ifi & Isr & Ien & Ies & Isid & Iis) ].
unfold sb_cells in X.
cbn [ctl_req_code creq_size] in AP, APB, APS |- *. cbn in OK. destruct OK as [EP HOFF].

eapply evt_cut.
{ eapply (sbctl_entry (sbd_mode s) S P 104 lo _ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Imo X);
[reflexivity| exact TP| exact ST| lia| lia| lia| lia| exact AL| lia| | exact MI].
unfold sbctl_code_ok. lia. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 12%nat sfH_ as xt1 xa0 xa1 xa4 j0 m1 -> FR MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (xt1 & xa0 & xa1 & xa4 & j0 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1) ]. unfold sbctl_frame in FR.
xport MU1 WM1 X.
assert (RL1 : DREP OUTL STEREO m1 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL| exact MU1| exact WM1|]. intros b x Hb Hx. destruct (LCE _ Hb). cbn. split; [lia| exact I]. }
clear RL TP.
assert (SBLO : forall b', In b' (sb_blocks s S a) -> blk_addr b' + blk_size b' <= lo).
{ intros b' Hb'. first [ pose proof (BR b' ltac:(rewrite ELBD; apply in_app_iff; left; exact Hb')) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BR b' ltac:(rewrite ELBD; apply in_app_iff; left; exact Hb')) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia. }
assert (BU1 : sb_bufs rsegs m1 a j).
{ eapply (sb_bufs_out _ s S); [exact BU| exact JOK| exact MU1| exact WM1|]. intros b x Hb Hx.
assert (HbD : In b LBD) by (rewrite ELBD; apply in_app_iff; left; right; exact Hb).
first [ pose proof (BR _ HbD) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BR _ HbD) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. cbn. split; [lia| exact I]. }
clear BU.
cbn [sbctl_armpc Z.eqb Pos.eqb].

pose proof (conj MU1 WM1) as MW1. clear MU1 WM1.
pose proof (munch_refl [(S + 120, S + 128)] m1) as MU3. pose proof (wmono_refl rsegs m1) as WM3.
zstep. if_false_z. zstep. zstep. if_false_z. step. zstep. rewrite ?AL. destruct MW1 as [MU1 WM1].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in *; clearbody m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (SAPB _ Hb). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (SAPL _ Hb). lia. }
match goal with H : stk rsegs m3 lo _ |- _ => rename H into ST3 end.
clear BU1 RL1.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI3]. }
cbv beta. intros ms3 ->.
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F) | exact (fc) | exact (m3) | ] | sf_fb; exists F, fc, m3 ].
split; [rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU3|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3); cbn; (split; [| exact I]).
- lia.
- specialize (O3 _ INS). unfold blk_addr, blk_size, SBSTATE_SIZEOF in O3. cbn [fst snd] in O3. lia. }
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [speex_decoder_ctl fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|].
split; [unfold sb_inv in *; cbn; repeat split; try assumption; lia|]. split; [exact JOK|].
split; [| split; [exact BU3| exists OUTL; exact RL3]].
unfold sb_cells. cbn -[Z.add Z.mul Z_to_bv rsegs]. unfold sb_isave_ptr. cbn [sbd_innov_save set_sbd_innov_save]. rewrite <- EP.
rewrite ?unsigned_lit in X by lia. first [exact X | rewrite Z_to_bv_bv_unsigned in X; exact X | idtac "ISVFIX"].
+ split; [cbn [creq_post]; exact I| exc_sb].
Qed.

Theorem rctl_isave_all {RCEIL : RunCeiling} : forall d, rctl_isave_at d.
Proof. intros [st|s low]; [apply rctl_isave_nb| apply rctl_isave_sb]. Qed.
