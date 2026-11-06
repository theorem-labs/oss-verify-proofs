(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1cp X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X05m X09f X06d X069 X05y X05z.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5 X0ys X0x2 X0wr X0ws.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ws.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rctl_nbA2 : forall st, rctl_atPB (fun r => creq_grp1 r = true /\ creq_grp1a r = false) (DecNB st).
Proof.
intros st OUT STEREO S LBD r P lo usp ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
[GRP GRP2] REP OK PRE BLK OBP PAL PPOS OBM AP APB ST LOS LO SPH CC LC MI FRM.
unfold NBCTL_STACK in LO. cbn [decst_rep] in REP. destruct REP as [ELBD NB].
pose proof (BLK _ ltac:(rewrite ELBD; left; reflexivity)) as BRS. unfold ablk, blk_addr, blk_size in BRS. cbn [fst snd] in BRS.
destruct BRS as (OBS & S8 & SOFF & _ & SLO). unfold NBSTATE_SIZEOF in *.
pose proof (APB _ ltac:(rewrite ELBD; left; reflexivity)) as APS. unfold blk_addr, blk_size in APS. cbn [fst snd] in APS.
destruct NB as (AL & POS & INV & j & JOK & CBS & X).
pose proof JOK as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
pose proof INV as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis).
apply (nb_pieces_of_cells bsegs _ _ _ m S OUT STEREO st j JOK) in X.
destruct X as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
unfold nb_hdr_cells in P0. unfold nb_cfg_cells in P14. unfold nb_ucb_cells, cb_cells in P16. cbn [fst snd] in P16. unfold nb_tail_cells in P18.
pose proof OBS as (S0 & STOP & _). pose proof OBP as (PP0 & PTOP & _). pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
assert (OF1 : offsh [(usp + -112, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).

eapply evt_cut.
{ eapply (nbctl_entry S P (ctl_req_code r) lo usp _ ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0);
[reflexivity| exact OBS| exact S8| exact OBM| exact ST| lia| exact LOS| exact SPH| lia| lia| lia| | exact CC| exact LC| exact MI].
unfold nbctl_code_ok. destruct r; cbn [ctl_req_code]; cbn in OK; clear - OK GRP GRP2; try discriminate GRP; try discriminate GRP2; tauto. }
cbv beta. intros ms1 (xt1 & xa2 & xa4 & xa5 & j0 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1 & EA1). unfold nbctl_frame in FR.
pose proof (aobj_munch bsegs _ m m1 S 2968 OBS MU1 (shfree_of_aobj bsegs _ m S 2968 OF1 OBS)) as OBS1.
pose proof (aobj_munch bsegs _ m m1 P _ OBP MU1 (shfree_of_aobj bsegs _ m P _ OF1 OBP)) as OBP1.
xport MU1 WM1 P0. xport MU1 WM1 P1. xport MU1 WM1 P2. xport MU1 WM1 P3. xport MU1 WM1 P4. xport MU1 WM1 P5. xport MU1 WM1 P6.
xport MU1 WM1 P7. xport MU1 WM1 P8. xport MU1 WM1 P9. xport MU1 WM1 P10. xport MU1 WM1 P11. xport MU1 WM1 P12. xport MU1 WM1 P13.
xport MU1 WM1 P14. xport MU1 WM1 P15. xport MU1 WM1 P16. xport MU1 WM1 P17. xport MU1 WM1 P18.
destruct r; cbn in OK; try (exfalso; exact OK); try discriminate GRP; try discriminate GRP2; cbn [ctl_req_code creq_size creq_align] in *; cbn [creq_pre] in PRE.
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG.
eapply evt_cut. { eapply (nbarm_get_sampling_rate S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL| exact P0| exact Isr]. }
cbv beta. intros ms2 (ya1 & ya2 & ->).
eapply evt_cut. { eapply (nbctl_exit_get usp P w); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 (F' & m3 & -> & MU3 & WM3 & MI3 & ARG3 & FR3).
clear ARG FR. xport_mem m1 MU3 WM3.
assert (ST3 : stk bsegs m3 lo (usp + -112)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
unfold nbctl_frame in FR3. release_frame FR3 ST3 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m3.
split; [reflexivity|].
split; [solve_munch MU1 MU3 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; split; [exact ARG3| first [exact Isr | unfold NB_FRAME_SIZE, NB_SUBFRAME_SIZE; lia]]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU3 WM3 EXQ. exact EXQ.
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG.
eapply evt_cut. { eapply (nbarm_get_lookahead S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL]. }
cbv beta. intros ms2 ->.
eapply evt_cut. { eapply (nbctl_exit_get2 usp P w); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 (F' & m3 & -> & MU3 & WM3 & MI3 & ARG3 & FR3).
clear ARG FR. xport_mem m1 MU3 WM3.
assert (ST3 : stk bsegs m3 lo (usp + -112)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
unfold nbctl_frame in FR3. release_frame FR3 ST3 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m3.
split; [reflexivity|].
split; [solve_munch MU1 MU3 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; split; [exact ARG3| first [exact Isr | unfold NB_FRAME_SIZE, NB_SUBFRAME_SIZE; lia]]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU3 WM3 EXQ. exact EXQ.
-
destruct PRE as (w & ARG & EQW & RV). xport MU1 WM1 ARG.
eapply evt_cut.
{ eapply (nbarm_set_wideband S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL| exact ARG| exact P18| lia]. }
cbv beta. intros ms2 (m2 & ya0 & ya2 & -> & P18' & ARG' & MU2 & WM2 & MI2). clear P18 ARG.
xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit usp); [lia| reflexivity| exact FR| exact MI2]. }
cbv beta. intros ms3 (F' & ->).
assert (ST2 : stk bsegs m2 lo (usp + -112)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m2.
split; [reflexivity|].
split; [solve_munch MU1 MU2 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [unfold nb_inv in *; cbn; repeat split; try assumption; try lia|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
assert (P18n : rw_cells bsegs m2 (S + 2948) [C4 (Z_to_bv 64 (nb_voc_offset st)); C4 (Z_to_bv 64 (nb_dtx_enabled st)); C4 (Z_to_bv 64 v);
C4 (Z_to_bv 64 (nb_highpass_enabled st)); CB 4 (j_pad2 j)]).
{ eapply rw_cells_samebytes; [exact P18'| cbn; repeat split; try reflexivity; exact E13 | cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w v EQW); reflexivity | reflexivity]. }
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; exists w; split; [exact ARG'| exact EQW]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU2 WM2 EXQ. exact EXQ.
Qed.

Theorem rctl_nbA : forall st, rctl_atPB (fun r => creq_grp1 r = true) (DecNB st).
Proof.
intros st OUT STEREO S LBD r. intros. destruct (creq_grp1a r) eqn:G; [eapply rctl_nbA1| eapply rctl_nbA2]; try eassumption. split; assumption.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rctl_nbA2 : forall st, rctl_atP (fun r => creq_grp1 r = true /\ creq_grp1a r = false) (DecNB st).
Proof.
intros st OUT STEREO S LBD r P lo usp ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
[GRP GRP2] REP OK PRE BLK OBP PAL OBM AP APB ST LOS LO SPH CC LC MI FRM.
unfold NBCTL_STACK in LO. cbn [decst_rep] in REP. destruct REP as [ELBD NB].
pose proof (BLK _ ltac:(rewrite ELBD; left; reflexivity)) as BRS. unfold ablk, blk_addr, blk_size in BRS. cbn [fst snd] in BRS.
destruct BRS as (OBS & S8 & SOFF & _ & SLO). unfold NBSTATE_SIZEOF in *.
pose proof (APB _ ltac:(rewrite ELBD; left; reflexivity)) as APS. unfold blk_addr, blk_size in APS. cbn [fst snd] in APS.
destruct NB as (AL & POS & INV & j & JOK & CBS & X).
pose proof JOK as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
pose proof INV as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis).
apply (nb_pieces_of_cells asegs _ _ _ m S OUT STEREO st j JOK) in X.
destruct X as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
unfold nb_hdr_cells in P0. unfold nb_cfg_cells in P14. unfold nb_ucb_cells, cb_cells in P16. cbn [fst snd] in P16. unfold nb_tail_cells in P18.
pose proof OBS as (S0 & STOP & _). pose proof OBP as (PP0 & PTOP & _). pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
assert (OF1 : offsh [(usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).

eapply evt_cut.
{ eapply (nbctl_entry S P (ctl_req_code r) lo usp _ ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0);
[reflexivity| exact OBS| exact S8| exact OBM| exact ST| lia| exact LOS| exact SPH| lia| lia| lia| | exact CC| exact LC| exact MI].
unfold nbctl_code_ok. destruct r; cbn [ctl_req_code]; cbn in OK; clear - OK GRP GRP2; try discriminate GRP; try discriminate GRP2; tauto. }
cbv beta. intros ms1 (xt1 & xa0 & xa1 & xa2 & xa4 & xa5 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1 & EA1). unfold nbctl_frame in FR.
pose proof (aobj_munch asegs _ m m1 S 2968 OBS MU1 (shfree_of_aobj asegs _ m S 2968 OF1 OBS)) as OBS1.
pose proof (aobj_munch asegs _ m m1 P _ OBP MU1 (shfree_of_aobj asegs _ m P _ OF1 OBP)) as OBP1.
xport MU1 WM1 P0. xport MU1 WM1 P1. xport MU1 WM1 P2. xport MU1 WM1 P3. xport MU1 WM1 P4. xport MU1 WM1 P5. xport MU1 WM1 P6.
xport MU1 WM1 P7. xport MU1 WM1 P8. xport MU1 WM1 P9. xport MU1 WM1 P10. xport MU1 WM1 P11. xport MU1 WM1 P12. xport MU1 WM1 P13.
xport MU1 WM1 P14. xport MU1 WM1 P15. xport MU1 WM1 P16. xport MU1 WM1 P17. xport MU1 WM1 P18.
destruct r; cbn in OK; try (exfalso; exact OK); try discriminate GRP; try discriminate GRP2; cbn [ctl_req_code creq_size creq_align] in *; cbn [creq_pre] in PRE.
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG.
eapply evt_cut. { eapply (nbarm_get_sampling_rate S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL| exact P0| exact Isr]. }
cbv beta. intros ms2 (ya2 & ya4 & ya5 & ->).
eapply evt_cut. { eapply (nbctl_exit_get usp P w); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 (F' & m3 & -> & MU3 & WM3 & MI3 & ARG3 & FR3).
clear ARG FR. xport_mem m1 MU3 WM3.
assert (ST3 : stk asegs m3 lo (usp + -80)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
unfold nbctl_frame in FR3. release_frame FR3 ST3 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m3.
split; [reflexivity|].
split; [solve_munch MU1 MU3 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; split; [exact ARG3| first [exact Isr | unfold NB_FRAME_SIZE, NB_SUBFRAME_SIZE; lia]]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU3 WM3 EXQ. exact EXQ.
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG.
eapply evt_cut. { eapply (nbarm_get_lookahead S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL]. }
cbv beta. intros ms2 (ya2 & ya4 & ya5 & ->).
eapply evt_cut. { eapply (nbctl_exit_get usp P w); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 (F' & m3 & -> & MU3 & WM3 & MI3 & ARG3 & FR3).
clear ARG FR. xport_mem m1 MU3 WM3.
assert (ST3 : stk asegs m3 lo (usp + -80)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
unfold nbctl_frame in FR3. release_frame FR3 ST3 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m3.
split; [reflexivity|].
split; [solve_munch MU1 MU3 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; split; [exact ARG3| first [exact Isr | unfold NB_FRAME_SIZE, NB_SUBFRAME_SIZE; lia]]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU3 WM3 EXQ. exact EXQ.
-
destruct PRE as (w & ARG & EQW & RV). xport MU1 WM1 ARG.
eapply evt_cut.
{ eapply (nbarm_set_wideband S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL| exact ARG| exact P18| lia]. }
cbv beta. intros ms2 (m2 & ya1 & ya2 & ya4 & ya5 & -> & P18' & ARG' & MU2 & WM2 & MI2). clear P18 ARG.
xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit usp); [lia| reflexivity| exact FR| exact MI2]. }
cbv beta. intros ms3 (F' & ->).
assert (ST2 : stk asegs m2 lo (usp + -80)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m2.
split; [reflexivity|].
split; [solve_munch MU1 MU2 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [unfold nb_inv in *; cbn; repeat split; try assumption; try lia|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
assert (P18n : rw_cells asegs m2 (S + 2948) [C4 (Z_to_bv 64 (nb_voc_offset st)); C4 (Z_to_bv 64 (nb_dtx_enabled st)); C4 (Z_to_bv 64 v);
C4 (Z_to_bv 64 (nb_highpass_enabled st)); CB 4 (j_pad2 j)]).
{ eapply rw_cells_samebytes; [exact P18'| cbn; repeat split; try reflexivity; exact E13 | cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w v EQW); reflexivity | reflexivity]. }
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; exists w; split; [exact ARG'| exact EQW]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU2 WM2 EXQ. exact EXQ.
Qed.

Theorem rctl_nbA : forall st, rctl_atP (fun r => creq_grp1 r = true) (DecNB st).
Proof.
intros st OUT STEREO S LBD r. intros. destruct (creq_grp1a r) eqn:G; [eapply rctl_nbA1| eapply rctl_nbA2]; try eassumption. split; assumption.
Qed.
