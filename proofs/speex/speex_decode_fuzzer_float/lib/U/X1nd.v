(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1ne X1nf X1ng X1nh.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Theorem rinit_sb {RCEIL : RunCeiling} : forall mo, (mo = ModeWB \/ mo = ModeUWB) -> rinit_at (lower_mode mo) -> rinit_at mo.
Proof.
intros mo Hmo IH ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB AB lo errv
HEAP TP AUX SB ST CLO LO ERR MI FRM TPE HA0 SP16.
eapply (rinit_sbA mo); try eassumption.
intros blk S low LBL st1 ms1 AT40.
eapply (rinit_sbA2 mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB AB lo m Hmo SB CLO LO TPE); [| exact AT40].
intros blk' S' lr low' LBL' st2 ms2 AT78.
eapply (rinit_sbB mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s LB AB lo m Hmo SB CLO LO TPE). exact AT78.
Qed.

Theorem rinit_all {RCEIL : RunCeiling} : forall mo, rinit_at mo.
Proof.
intros [| |].
- exact rinit_nb.
- apply (rinit_sb ModeWB); [left; reflexivity| exact rinit_nb].
- apply (rinit_sb ModeUWB); [right; reflexivity|]. apply (rinit_sb ModeWB); [left; reflexivity| exact rinit_nb].
Qed.

Lemma mode_depth_le3 : forall mo, (mode_depth mo <= 3)%nat.
Proof. intros [| |]; cbn; lia. Qed.
Lemma init_depth_le : forall mo, init_depth mo <= DEC_INIT_STACK.
Proof. intros [| |]; cbn; unfold DEC_INIT_STACK; lia. Qed.

Theorem rspx_decoder_init_proof {RCEIL : RunCeiling} : rspx_decoder_init_stmt DECREP.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB mo AB lo errv
HEAP TP AUX SB ABB ST CLO LO ERR MI FRM TPE SPA HA0.
eapply implM_mono.
{ eapply (rinit_all mo); try eassumption. pose proof (init_depth_le mo). lia. }
cbv beta. intros r s' ms' sfH_; first [ sf_destruct 28%nat sfH_ as x0 x1 x2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x3 x4 x5 x6 F' fc' m' errv' -> FRM' MI' ST' ERR' AUX' PRES' PSO' RES | sf_fb; destruct sfH_ as (x0 & x1 & x2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & F' & fc' & m' & errv' & -> & FRM' & MI' & ST' & ERR' & AUX' & PRES' & PSO' & RES) ].
unfold rspx_decoder_init_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F') | exact (fc') | exact (m') | exact (errv') | ] | sf_fb; exists F', fc', m', errv' ].
split; [reflexivity|]. split; [exact FRM'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|]. split; [exact PRES'|]. split; [exact PSO'|].
destruct r as [d|]; [| exact RES].
first [ sf_destruct 13%nat RES as S LBD -> SB' HEAP' REP ND DM TIS DD _ _ NE | sf_fb; destruct RES as (S & LBD & -> & SB' & HEAP' & REP & ND & DM & TIS & DD & _ & _ & NE) ].
exists S, LBD. split; [reflexivity|]. split; [exact SB'|]. split; [exact HEAP'|]. split; [| exact DM].
intros STEREO. split; [exact TIS|]. split; [rewrite DD; apply mode_depth_le3|].
split; [rewrite map_app in ND; apply List.NoDup_app_remove_r in ND; exact ND|].
split.
{ intros b1 b2 H1 H2 NEQ. eapply (RHEAP_blocks_disjoint_proof _ _ _ b1 b2 HEAP'); [apply in_app_iff; left; exact H1| apply in_app_iff; left; exact H2| exact NEQ]. }
split; [exact NE|]. exists 0. exact (REP STEREO).
Qed.
