(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1n3 X1n6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Theorem rctl_all {RCEIL : RunCeiling} : forall d, rctl_at d.
Proof. induction d as [st|s low IH]; [apply rctl_nb| apply rctl_sb; exact IH]. Qed.

Lemma ctl_depth_le : forall d : dec_state bptr, (dec_depth d <= 3)%nat -> ctl_depth d <= 160.
Proof.
intros d Hd. destruct d as [st|s1 [st|s2 [st|s3 low]]]; cbn; try lia. exfalso. cbn in Hd. pose proof (dec_depth_pos low). lia.
Qed.

Lemma ctl_req_of_ok : forall code arg req OUT P, ctl_req_of code arg = Some req -> ctl_req_fits req -> creq_ok OUT P req /\ ctl_req_code req = code /\ creq_size req = ctl_arg_size arg.
Proof.
intros code arg req OUT P H F. unfold ctl_req_of in H. destruct arg;
repeat match type of H with context [if ?c then _ else _] => destruct c eqn:? end; inversion H; subst; cbn in *;
repeat match goal with K : (_ =? _) = true |- _ => apply Z.eqb_eq in K; subst end; cbn; auto.
Qed.

Lemma ctl_top_isave : forall (d : dec_state bptr) r, creq_grp1 r = true -> top_isave_none d -> top_isave_none (snd (speex_decoder_ctl d r)).
Proof.
intros d r OK T. destruct d as [st|s low]; destruct r; cbn in OK |- *; try discriminate OK; try exact T.
all: match goal with |- context [speex_decoder_ctl ?lw ?q] => destruct (speex_decoder_ctl lw q) as [v' l]; cbn; exact T end.
Qed.

Lemma ctl_depth_same : forall (d : dec_state bptr) r, dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof.
induction d as [st|s low IH]; intros r; [destruct r; reflexivity|].
destruct r; cbn [speex_decoder_ctl]; try reflexivity.
all: match goal with |- context [speex_decoder_ctl ?lw ?q] =>
pose proof (IH q) as E; destruct (speex_decoder_ctl lw q) as [v' l]; cbn [fst snd dec_depth] in E |- *; rewrite E; reflexivity end.
Qed.

Lemma cb_pad_word : forall m P (pad : list byte) STEREO,
rw_cells rsegs m P [C4 (wz SPEEX_INBAND_STEREO); CB 4 pad; C8 (wz A_speex_std_stereo_request_handler); C8 (wz STEREO)] ->
rw_cells rsegs m P [C4 (wz SPEEX_INBAND_STEREO); C4 (le_bytes_to_word pad); C8 (wz A_speex_std_stereo_request_handler); C8 (wz STEREO)].
Proof.
intros m P pad STEREO X. pose proof X as [[WF _] _]. cbn in WF. destruct WF as (_ & LP & _).
eapply rw_cells_samebytes; [exact X| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite dr_le4_of_bytes by exact LP; reflexivity| reflexivity].
Qed.
Lemma cb_pad_bytes : forall m P (pad : word) STEREO,
rw_cells rsegs m P [C4 (wz SPEEX_INBAND_STEREO); C4 pad; C8 (wz A_speex_std_stereo_request_handler); C8 (wz STEREO)] ->
rw_cells rsegs m P [C4 (wz SPEEX_INBAND_STEREO); CB 4 (le4 pad); C8 (wz A_speex_std_stereo_request_handler); C8 (wz STEREO)].
Proof.
intros m P pad STEREO X.
eapply rw_cells_samebytes; [exact X| cbn; pose proof (length_le4 pad); tauto| cbn [cells_bytes cbytes app]; reflexivity| reflexivity].
Qed.

Theorem rspx_decoder_ctl_proof {RCEIL : RunCeiling} : rspx_decoder_ctl_stmt DECREP.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m STEREO S d LBD code P arg req lo
REP RQ FITS APRE APOK SP16 TP BR AP APB ST CLO LO MI FRM -> -> ->.
first [ sf_destruct 7%nat REP as TOP DE ND LAP NE OUT R | sf_fb; destruct REP as (TOP & DE & ND & LAP & NE & OUT & R) ].
destruct (ctl_req_of_ok code arg req OUT P RQ FITS) as (OK & <- & SZ).
assert (G1 : creq_grp1 req = true).
{ destruct arg; cbn in RQ; repeat match type of RQ with context [if ?c then _ else _] => destruct c end; inversion RQ; subst; reflexivity. }
unfold DEC_CTL_STACK in LO.
assert (CRE : creq_pre STEREO m S d P req).
{ destruct arg; cbn in APRE, RQ |- *;
repeat match type of RQ with context [if ?c then _ else _] => destruct c end; inversion RQ; subst; cbn; unfold wz in APRE.
- exact APRE.
- exact APRE.
- destruct APRE as (bs & X). exists (le_bytes_to_word bs). apply rw_cells_C4_of_CB4. exact X.
- destruct APRE as (bs & X). exists (le_bytes_to_word bs). apply rw_cells_C4_of_CB4. exact X.
- destruct APRE as (pad & X). exists (le_bytes_to_word pad). apply cb_pad_word in X. unfold wz in X. exact X. }
assert (CPO : creq_ptr_ok P req).
{ destruct arg; cbn in APOK, RQ |- *;
repeat match type of RQ with context [if ?c then _ else _] => destruct c end; inversion RQ; subst; cbn; first [exact APOK | exact I]. }
eapply evt_mono.
{ eapply (rctl_all d OUT STEREO S LBD req P lo); try eassumption; try reflexivity.
- rewrite SZ. exact AP.
- rewrite SZ. exact APB.
- pose proof (ctl_depth_le d DE). lia. }
cbv beta. intros ms' sfH_; first [ sf_destruct 26%nat sfH_ as x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F' fc' m' -> MU WM MI' FRM' ST' R' CP _ | sf_fb; destruct sfH_ as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & R' & CP & _) ].
unfold rspx_decoder_ctl_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F') | exact (fc') | exact (m') | exact (req) | ] | sf_fb; exists F', fc', m', req ].
split; [reflexivity|]. split; [exact RQ|].
split; [rewrite (ctlW_grp1 _ _ _ _ _ G1) in MU; unfold blocks_ivs in MU; rewrite SZ in MU; exact MU|].
split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact ST'|]. split; [reflexivity|].
split.
- split; [apply ctl_top_isave; assumption|]. split; [rewrite ctl_depth_same; exact DE|]. split; [exact ND|]. split; [exact LAP|].
split; [apply ctl_nested_same; exact NE|]. exists OUT. exact R'.
- destruct arg; cbn in RQ, CP |- *;
repeat match type of RQ with context [if ?c then _ else _] => destruct c end; inversion RQ; subst; cbn in CP |- *; unfold wz.
+ exact CP.
+ exact CP.
+ exact CP.
+ exact CP.
+ destruct CP as (pad' & X). exists (le4 pad'). apply cb_pad_bytes in X. unfold wz in X. exact X.
Qed.
