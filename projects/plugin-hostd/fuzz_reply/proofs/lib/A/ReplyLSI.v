(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 648 of its 762 lines of code are new or changed and 1113 lines of the source are left out. *)
(* ONE LS instance for every LS hypothesis of top_x (W_LLVMFuzzerTestOneInput_top_x.v at the window head
   a working branch 1b86af9bd95, with W8's F8 / F9 text 7ff2278dbb61; the gone rules at gone_base's KF-COUNT
   text):
     LSI B OM nsec KMAX KC := fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP /\ fr_SEC nsec KMAX KC   (OUT_MAX4 <= OM),
   RINV := fr_RINV, MT := ReplyKfMeter.MT_sec nsec KMAX (the counting meter, KF-COUNT), TfibB := B.  proves no function
   (kind: invariant lemma).
   - One plug lsi_<row> per top_x hypothesis, stated at top_x's own text with LSx := LSI B OM nsec KMAX KC, RINV :=
     fr_RINV, MT := MT_sec nsec KMAX, TfibB := B, and top_x's XM_LIB / XN_LIB as this Section's.  LS_rm_rr_pre and
     LS_gone_rig at OM := OUT_MAX4 (their g_capout bound comes from the entry's CAPOUT clause, ReplyLS3eCap.v).
   - Post rules (they conclude LS) combine their twins: fr_LS3cp (ReplyLS3p.v), fr_OUT (ReplyLS3o.v / ReplyLS3oGn.v),
     fr_ENT (ReplyLS3e.v), fr_CAP (ReplyLScap.v), fr_SEC (ReplyLSsec.v / ReplyLSsecGn.v).  Pre rules project LSI; their
     meter conjuncts (`mo_ok MT S cost`) come from fr_SEC.
   - The gone rules take a Theorem Labs lane's RINV halves as ONE hypothesis each (forall LS, G8.GN_RI_*_ri B MT LS fr_RINV).
   - The instance (KF-COUNT #7) sets nsec := a Theorem Labs lane's nsec_cf, KMAX := cf_kmax, KC := a Theorem Labs lane's KF_KC (256) and the
     driver's XM_LIB / XN_LIB, and discharges HKC, HXM, HXN, HNSF below.
   - lsi_sat: a concrete state at which LSI holds, given the meter's count at the two states (lsi_sat_count: at
     nsec := 0 every premise holds). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c RelayCap SlotReads SlotInv SlotDrain3Aux SlotPass2Aux
  relay_remove_b_aux send_line_b_c RelayRunT RelayRunF ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak ReplyTrPeakC.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3p ReplyLS3oRf ReplyLS3oGn ReplyLS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3cTopxGoneF ReplyLS3cTopxGoneH ReplyLS3cTopx ReplyLS3cTopxPost ReplyLS3cTopxPro
  ReplyLS3cTopxGone8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Peak ReplyLS3pGn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLScap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyKfMeter ReplyLSsec ReplyLSsecGn.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== g_capout never falls below 0 over a drain *)
(* ds_ocap changes only through lines_run's send_line calls (Prog/drain_b_c.v:126-161), and send_line never lowers a
   capacity that is >= 0 (ReplyTrPeak.v tp_send_line) *)
Lemma lsi_lines_run_cap_ge : forall ls live mx no cap H ka j o ha ks, 0 <= cap ->
  cap <= fst (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks Hc; cbn [drain_b_c.lines_run fst snd]; [lia|].
  pose proof (proj2 (tp_send_line live mx no cap (Z.of_nat (length l) + 1) j o Hc)) as H1.
  match goal with |- context [drain_b_c.lines_run live mx ?no' ?cap' ?H' ?ka' r ?j' ?o' ?ha' ?ks'] =>
    pose proof (IH live mx no' cap' H' ka' j' o' ha' ks' ltac:(lia)) as H2 end.
  lia.
Qed.
Lemma lsi_drain_run_ocap_ge : forall f live mx s j a, 0 <= drain_b_c.ds_ocap s ->
  drain_b_c.ds_ocap s <= drain_b_c.ds_ocap (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
  induction f as [|f IH]; intros live mx s j a Hs; [cbn; lia|].
  cbn [drain_b_c.drain_run].
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst snd]. etransitivity; [|apply IH]; cbn [drain_b_c.ds_ocap]; lia.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs]; [cbn [fst snd drain_b_c.ds_ocap]; lia|].
    match goal with |- context [if ?b then _ else _] => destruct b end; [cbn [fst snd drain_b_c.ds_ocap]; lia|].
    match goal with |- context [RelayModel.chunk ?u ?k ?d] => destruct (RelayModel.chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [drain_b_c.lines_run live mx ?no ?cap ?H ?ka rl ?j3 ?o ?ha ?ks] =>
      pose proof (lsi_lines_run_cap_ge rl live mx no cap H ka j3 o ha ks Hs) as Hl;
      destruct (drain_b_c.lines_run live mx no cap H ka rl j3 o ha ks) as [[tr [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [fst snd] in Hl |- *.
    etransitivity; [|apply IH]; cbn [drain_b_c.ds_ocap]; lia.
Qed.
Lemma lsi_drain_fin_ocap : forall live mx NO CAP e h, 0 <= CAP ->
  CAP <= drain_b_c.ds_ocap (drain_b_c.drain_fin live mx NO CAP e h).
Proof.
  intros live mx NO CAP e h Hc. unfold drain_b_c.drain_fin, drain_b_c.drain_go.
  exact (lsi_drain_run_ocap_ge _ live mx (drain_b_c.drain_init NO CAP e h) 0 drain_b_c.dadr0 Hc).
Qed.


(* LSI := fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B /\ fr_CAP /\ fr_SEC (fr_CAP is ReplyLScap.v's, fr_SEC ReplyLSsec.v's) *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition LSI (B : asyms) (OM : Z) (nsec : astate -> Z) (KMAX KC : Z) (cx : lfcx) (t : Z) (m : lmod) (ly : alayout)
    (S : astate) : Prop :=
  fr_LS3cp B cx t m ly S /\ fr_OUT OM cx t m ly S /\ fr_ENT B cx m ly S /\ fr_CAP cx t m ly S /\
  fr_SEC nsec KMAX KC cx t m ly S.
Lemma lsi_txp : forall B OM nsec KMAX KC cx t m ly S, LSI B OM nsec KMAX KC cx t m ly S -> txp_LSx B OM cx t m ly S.
Proof. intros B OM nsec KMAX KC cx t m ly S (HP & HO & HE & _). exact (conj HP (conj HO HE)). Qed.
End inst.

(* ================================================================== the plugs *)
Section lsi.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.
(* the counting meter: the count of secondary entries, the run bound and the per-operation constant *)
Variable nsec : astate -> Z.
Variables KMAX KC : Z.
Hypothesis HKC : 240 <= KC.
(* top_x's per-call meter budgets at the entry (lf_base_x's mo_ok) and the exit (POST's mo_le) *)
Variables XM_LIB XN_LIB : Z -> Z.
Hypothesis HXM : forall n, SEC_CALL KC <= XM_LIB n.
Hypothesis HXN : forall n, SEC_CALL KC <= XN_LIB n.
(* the meter does not see a frame-state change (ReplyKfMeter.MT_sec_set_fs's premise: set_fs keeps st_secs) *)
Hypothesis HNSF : forall f s, nsec (set_fs f s) = nsec s.

Local Notation MT := (MT_sec nsec KMAX).
Local Notation LSx := (LSI B OM nsec KMAX KC).
Local Notation RINV := fr_RINV.
Local Notation TfibB := B.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).

(* the parts of LSI the twins read *)
Lemma lsi_parts : forall cx t m ly S, LSx cx t m ly S ->
  fr_LS3cp B cx t m ly S /\ fr_LS3c B cx t m ly S /\ fr_LS3 B cx t m ly S /\ fr_OUT OM cx t m ly S /\
  fr_ENT B cx m ly S /\ fr_CAP cx t m ly S /\ fr_SEC nsec KMAX KC cx t m ly S.
Proof.
  intros cx t m ly S (HP & HO & HE & HC & HS). pose proof HP as (H3c & _). pose proof H3c as (H3 & _).
  exact (conj HP (conj H3c (conj H3 (conj HO (conj HE (conj HC HS)))))).
Qed.
Ltac lsi_open H := destruct (lsi_parts _ _ _ _ _ H) as (?HP & ?H3c & ?H3 & ?HO & ?HE & ?HC & ?HS); clear H.
Ltac lsi_goal := unfold LSI; refine (conj _ (conj _ (conj _ (conj _ _)))).
(* the call's entry budget, from lf_base_x's mo_ok at the entry (conjunct 19 of fr_lib_pre_cf_x) *)
Lemma lsi_entry : forall RLO RHI LIBROOM NP G ARX cx Hp,
  lf_base_x TfibB MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  nsec (c_S cx) + SEC_CALL KC <= KMAX.
Proof.
  intros RLO RHI LIBROOM NP G ARX cx Hp (_ & Hpre).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMO & _).
  change (nsec (c_S cx) + XM_LIB (c_n cx) <= KMAX) in HMO. pose proof (HXM (c_n cx)). lia.
Qed.

(* ---------------------------------------------------------------- the keep rules *)
(* top_x :184 *)
Lemma lsi_LS_close : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S H Hpk. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_close; eassumption.
  - eapply fr_OUT_close; eassumption.
  - eapply fr_ENT_close; eassumption.
  - eapply fr_CAP_close; eassumption.
  - eapply fr_SEC_close; eassumption.
Qed.
(* top_x :187 *)
Lemma lsi_LS_eintr : forall cx t m i ly S, LSx cx t m ly S ->
  pick (lm_hs m) (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) = Some i ->
  LSx cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S H Hpk. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_eintr; eassumption.
  - eapply fr_OUT_eintr; eassumption.
  - eapply fr_ENT_eintr; eassumption.
  - eapply fr_CAP_eintr; eassumption.
  - eapply fr_SEC_eintr; eassumption.
Qed.
(* top_x :190 *)
Lemma lsi_LS_sendmax : forall cx t m ly S, LSx cx t m ly S ->
  LSx cx (t + 1) (sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof.
  intros cx t m ly S H. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_sendmax; eassumption.
  - eapply fr_OUT_sendmax; eassumption.
  - eapply fr_ENT_sendmax; eassumption.
  - eapply fr_CAP_sendmax; eassumption.
  - eapply fr_SEC_sendmax; eassumption.
Qed.
(* top_x :192 *)
Lemma lsi_LS_default : forall cx t m ly S, LSx cx t m ly S -> LSx cx (t + 1) (sm_default cx m (sm_dg cx m)) ly S.
Proof.
  intros cx t m ly S H. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_default; eassumption.
  - eapply fr_OUT_default; eassumption.
  - eapply fr_ENT_default; eassumption.
  - eapply fr_CAP_default; eassumption.
  - eapply fr_SEC_default; eassumption.
Qed.
(* top_x :225 *)
Lemma lsi_LS_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (oa_cost MT) -> Permutation (ablocks TfibB ly' S') ((q, APARTIAL) :: ablocks TfibB ly S) ->
  LSx cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' H _ _ Hf Hmo HPm. lsi_open H.
  pose proof H3 as (rest & e0 & _ & _ & _ & _ & Hl4 & _). lsi_goal.
  - eapply fr_LS3cp_add_open; eassumption.
  - eapply fr_OUT_add_open; eassumption.
  - eapply fr_ENT_add_open; eassumption.
  - eapply fr_CAP_add_open; eassumption.
  - eapply fr_SEC_add_open; eassumption.
Qed.
(* top_x :229 *)
Lemma lsi_LS_add_none : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m -> oa_first (ad_os (lm_hs m)) = None ->
  LSx cx (t + 1) (ad_none m) ly S.
Proof.
  intros cx t m ly S H _ _ _. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_add_none; eassumption.
  - eapply fr_OUT_add_none; eassumption.
  - eapply fr_ENT_add_none; eassumption.
  - eapply fr_CAP_add_none; eassumption.
  - eapply fr_SEC_add_none; eassumption.
Qed.
(* top_x :236 *)
Lemma lsi_LS_write_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof.
  intros cx t m ly S H. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_write_skip; eassumption.
  - eapply fr_OUT_write_skip; eassumption.
  - eapply fr_ENT_write_skip; eassumption.
  - eapply fr_CAP_write_skip; eassumption.
  - eapply fr_SEC_write_skip; eassumption.
Qed.
(* top_x :252 *)
Lemma lsi_LS_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks TfibB ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks TfibB ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ev ly S ly' S' H Hp Hn Hr Hc Hv HPm Hmo Ht. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_write_push; eassumption.
  - eapply fr_OUT_write_push; eassumption.
  - eapply fr_ENT_write_push; eassumption.
  - eapply fr_CAP_write_push; eassumption.
  - eapply fr_SEC_write_push; eassumption.
Qed.
(* top_x :314 *)
Lemma lsi_LS_head_nout : forall cx t m ly S, LSx cx t m ly S -> LSx cx t (lm_clear_O m) ly S.
Proof.
  intros cx t m ly S H. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_head_nout; eassumption.
  - eapply fr_OUT_head_nout; eassumption.
  - eapply fr_ENT_head_nout; eassumption.
  - eapply fr_CAP_head_nout; eassumption.
  - eapply fr_SEC_head_nout; eassumption.
Qed.
(* top_x :318 *)
Lemma lsi_LS_head_skip : forall cx t m ly S, 0 <= t < OPS_MAX -> 0 <= lm_k m < c_n cx -> lm_O m = [] ->
  picks (in_byte cx (lm_k m) mod 10) = true -> in_byte cx (lm_k m) mod 10 <> 1 ->
  pick (lm_hs m) (hd_kb cx m) = None -> LSx cx t m ly S -> LSx cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S Ht Hk HO0 Hpk H1 Hn H. lsi_open H. lsi_goal.
  - eapply fr_LS3cp_head_skip; eassumption.
  - eapply fr_OUT_head_skip; eassumption.
  - eapply fr_ENT_head_skip; eassumption.
  - eapply fr_CAP_head_skip; eassumption.
  - eapply fr_SEC_head_skip; eassumption.
Qed.
(* top_x :431: dr_skip moves only the cursor (fr_POT_same, fr_OUT_k_only, fr_ENT_keep) *)
Lemma lsi_LS_drain_skip : forall cx t m ly S,
  LSx cx t m ly S -> LSx cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros cx t m ly S H. lsi_open H. lsi_goal.
  - split; [exact (topx3c_LS_drain_skip B cx t m ly S H3c)|].
    apply (fr_POT_same cx t (t + 1) m); [reflexivity | reflexivity | lia | exact (proj2 HP)].
  - eapply fr_OUT_k_only with (m := m) (t := t); try reflexivity; try lia; exact HO.
  - eapply fr_ENT_keep; [reflexivity | exact HE].
  - eapply fr_CAP_drain_skip; eassumption.
  - eapply fr_SEC_drain_skip; eassumption.
Qed.

(* ---------------------------------------------------------------- the step rules with block relations *)
(* top_x LS_event_step *)
Lemma lsi_LS_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  LSx cx t m ly S -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks TfibB ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks TfibB ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks TfibB ly3 S3 = l1 ++ l2) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q H HE' M1 M2 M3 Hk HO0 Hc0 Hm HRR Hf Ht.
  lsi_open H. lsi_goal.
  - exact (fr_LS3cp_event_step_p B cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HP HE' M1 M2 M3 Hk HO0 Hc0 Hm HRR Hf).
  - eapply fr_OUT_event_step_p; eassumption.
  - eapply fr_ENT_event_step_p; eassumption.
  - eapply fr_CAP_event_step; eassumption.
  - eapply fr_SEC_event_step; eassumption.
Qed.
(* top_x LS_drain_step: fr_OUT's twin also takes 0 <= cap' (lsi_drain_fin_ocap) *)
Lemma lsi_LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  LSx cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks TfibB ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks TfibB ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) ->
  dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 ->
  ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HL Hpick Hj M1 M2 HF1 Hp1 EE EH HF2 Eh
    Hat HRI Hfd Heof Hep Hkh Hhp Hhn Hc0 Hcap' Hepo Hhpo Hdp Hcp Ht.
  assert (Hc' : 0 <= cap').
  { rewrite Hcap'. destruct (dr_live (lm_c m) h); [|exact Hc0].
    unfold dr_fin. pose proof (lsi_drain_fin_ocap (dr_live (lm_c m) h) (lm_mx m) (Z.of_nat (length (lm_O m)))
      (lm_cap m) (nth j (lm_es m) dr_e0) h Hc0). lia. }
  lsi_open HL. lsi_goal.
  - exact (fr_LS3cp_drain_step_p B cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HP Hpick Hj
      M1 M2 HF1 Hp1 EE EH HF2 Eh Hat HRI Hfd Heof Hep Hkh Hhp Hhn Hc0 Hcap' Hepo Hhpo Hdp Hcp).
  - eapply fr_OUT_drain_step_p; eassumption.
  - eapply fr_ENT_drain_step_p; eassumption.
  - eapply fr_CAP_drain_step; eassumption.
  - eapply fr_SEC_drain_step; eassumption.
Qed.
(* top_x LS_rm_step: fr_OUT's twin also takes 0 <= cap2 (send_line and the drain never lower g_capout) *)
Lemma lsi_LS_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  LSx cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S)
       (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= t < OPS_MAX ->
  LSx cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HL HU Hmo HRI Hat Hrr Hcnl Hcshe
    HF Hpos Hkeys Hpend Ht.
  lsi_open HL.
  assert (Hc0 : 0 <= lm_cap m) by exact (proj1 HO).
  assert (Hc2 : 0 <= cap2).
  { pose proof Hrr as Hrr'. unfold rm_rr_ok in Hrr'. cbv zeta in Hrr'. destruct Hrr' as (_ & Hs).
    match type of Hs with sl_sends ?mx ?c1 ?O1 ?cap1 ?Bs = _ =>
      assert (H1 : 0 <= cap1);
      [| pose proof (ou_sends_ge mx Bs c1 O1 cap1 H1) as H2; rewrite Hs in H2; cbn [snd] in H2; lia] end.
    match goal with |- 0 <= (if ?b then _ else _) => destruct b; [|exact Hc0] end.
    unfold dr_fin. pose proof (lsi_drain_fin_ocap (dr_live (lm_c m) h) (lm_mx m) (Z.of_nat (length (lm_O m)))
      (lm_cap m) (rm_ent m j0) h Hc0). lia. }
  lsi_goal.
  - exact (fr_LS3cp_rm_step_p B cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HP Hmo HRI
      Hat Hrr Hcnl Hcshe HF Hpos Hkeys Hpend).
  - eapply fr_OUT_rm_step_p; eassumption.
  - eapply fr_ENT_rm_step_p; eassumption.
  - eapply fr_CAP_rm_step; eassumption.
  - eapply fr_SEC_rm_step; eassumption.
Qed.
(* top_x LS_pro: its first three conjuncts by ReplyLS3cTopxPro.v topx_LS_pro_xok_px, fr_CAP by ReplyLScap.v fr_CAP_pro,
   fr_SEC by ReplyLSsec.v fr_SEC_pro (the entry budget from lf_base_x, the seat's count from the window text's
   mo_le MT (c_S cx) S2 0) *)
Lemma lsi_LS_pro : forall RLO RHI LIBROOM NP G ARX,
  forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x TfibB MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at TfibB fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT (c_S cx) S2 0 ->
  mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks TfibB (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok TfibB (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks TfibB ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks TfibB ly S) ((q, APARTIAL) :: ablocks TfibB (c_ly cx) (c_S cx))))) ->
  LSx cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout Hc1 Hc2 Hc3 Hc4 Hb2 Hf2 Hn2
    Hbb2 Hmo0 Hmo HX.
  destruct (topx_LS_pro_xok_px B OM HOM XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hout
              Hc1 Hc2 Hc3 Hc4 Hb2 Hf2 Hn2 Hbb2 Hmo HX) as (HP & HO & HE).
  refine (conj HP (conj HO (conj HE (conj (fr_CAP_pro B MT XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out
    S2 pos ly S HB Hout Hc1 Hc2 Hc3 Hc4 Hb2 Hf2 Hn2 Hbb2 Hmo HX) _)))).
  exact (fr_SEC_pro nsec KMAX KC cx S2 S _ ly (lsi_entry RLO RHI LIBROOM NP G ARX cx Hp HB) Hmo0 Hmo
           (sec_ub_pro q T' pj c O cap out)).
Qed.

(* ---------------------------------------------------------------- the pre rules: projections and fr_SEC *)
(* top_x :222 *)
Lemma lsi_LS_add_room : forall cx t m ly S,
  LSx cx t m ly S -> RINV cx t m -> ad_at_op cx m ->
  blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S (oa_cost MT).
Proof.
  intros cx t m ly S H HRI Hat. lsi_open H. split; [exact (topx3c_LS_add_room B cx t m ly S H3c HRI Hat)|].
  rewrite (sec_oa nsec KMAX). pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S S 0 0 HS); lia.
Qed.
(* top_x :245 *)
Lemma lsi_LS_write_room : forall cx t m si h ly S,
  LSx cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  (lp_grow (hs_pending h) = true -> lp_vbytes (hs_pending h) < WR_MMAX) /\
  blocks_bytes S + (if lp_grow (hs_pending h) then lp_vbytes (hs_pending h) else 0) + (wr_n cx m + 1) <= LIVE_MAX /\
  mo_ok MT S (lp_cost MT (hs_pending h) (wr_n cx m)).
Proof.
  intros cx t m si h ly S H Hp Hn. lsi_open H.
  destruct (topx3c_LS_write_room B cx t m si h ly S H3c Hp Hn) as (R1 & R2).
  refine (conj R1 (conj R2 _)).
  pose proof (ReplyKfTrSm.kf_lp_cost MT (sec_HMs nsec KMAX) (sec_HFs nsec KMAX) (hs_pending h) (wr_n cx m)) as K.
  assert (K2 : ReplyKfTrSm.KC_lp = 2) by reflexivity. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S S 0 _ HS); lia.
Qed.
(* top_x :289 *)
Lemma lsi_LS_event_malloc : forall cx t m ly S e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  re_len e < CfParamsReply.fr_MMAX /\ blocks_bytes S + re_len e <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT (re_len e)).
Proof.
  intros cx t m ly S e H HRI He. lsi_open H.
  destruct (topx3c_LS_event_malloc B cx t m ly S e H3c HRI He) as (R1 & R2).
  exact (conj R1 (conj R2 (fr_SEC_event_malloc nsec KMAX KC HKC cx t m ly S e HS))).
Qed.
(* top_x :292 *)
Lemma lsi_LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) q,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  ablocks TfibB ly1 S1 = ablocks TfibB ly S ++ [(q, re_len e)] ->
  sl_maxr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) < CfParamsReply.fr_MMAX /\
  blocks_bytes S1 + sl_alloc (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= LIVE_MAX /\
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros cx t m ly S S1 e ly1 q H HRI He M1 HO Hb. lsi_open H.
  destruct (topx3c_LS_event_relay B cx t m ly S S1 e ly1 q H3c HRI He M1 HO Hb) as (R1 & R2).
  exact (conj R1 (conj R2 (fr_SEC_event_relay nsec KMAX KC HKC cx t m ly S S1 e He HO M1 HS))).
Qed.
(* top_x :300, at the window text (F7: lm_O m = [] after ev_evt) *)
Lemma lsi_LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  LSx cx t m ly S -> RINV cx t m -> ev_evt cx m e ->
  lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
Proof.
  intros cx t m ly S S1 S2 e H _ He HO M1 M2. lsi_open H.
  exact (fr_SEC_event_free nsec KMAX KC HKC cx t m ly S S1 S2 e He HO M1 M2 HS).
Qed.
(* top_x :338 (it names no LS), at the window text (F2: mo_le MT (c_S cx) S2 0) *)
Lemma lsi_LS_pro_oa : forall RLO RHI LIBROOM NP G ARX cx Hp (S2 : astate) pos,
  lf_base_x TfibB MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  ablocks TfibB (c_ly cx) S2 = ablocks TfibB (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 (oa_cost MT).
Proof.
  intros RLO RHI LIBROOM NP G ARX cx Hp S2 pos HB Hb2 Hf2 Hn2 Hbb2 Hmo0.
  split; [exact (topx_LS_pro_oa B XM_LIB RLO RHI LIBROOM NP G ARX cx Hp S2 pos HB Hb2 Hf2 Hn2 Hbb2)|].
  exact (fr_SEC_pro_oa nsec KMAX KC HKC cx S2 (lsi_entry RLO RHI LIBROOM NP G ARX cx Hp HB) Hmo0).
Qed.
(* top_x LS_cnl_pre: ReplyLS3Arms.v fr_LS3_cnl_pre_p and ReplyLSsec.v fr_SEC_cnl_pre *)
Lemma lsi_LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' e' cap' out',
  LSx cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  dr3_epre (nth j (lm_es m) dr_e0) -> dr3_hpre h -> 0 <= lm_cap m ->
  (exists rest,
     Permutation (ablocks TfibB ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks TfibB ly' S') (aentry_blks e' ++ asrc_blks h'' ++ aout_blks cap' out' ++ rest)) ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h'' ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
Proof.
  intros cx t m ly S ly' S' si h j h'' e' cap' out' H HRI Hpick Hj Hfd Heof Hmo Hcap Hmap Hheld Ht HO Hep Hhp Hc0
    HPm Hcap' Hepo Hhpo. lsi_open H.
  destruct (fr_LS3_cnl_pre_p B cx t m ly S ly' S' si h j h'' e' cap' out' H3 HRI Hpick Hj Hfd Heof Hmo Hcap Hmap Hheld
              Ht HO Hep Hhp Hc0 HPm Hcap' Hepo Hhpo) as (N1 & N2 & N3 & N4 & N5).
  refine (conj N1 (conj N2 (conj N3 (conj N4 (conj _ N5))))).
  exact (fr_SEC_cnl_pre nsec KMAX KC HKC cx t m ly S S' si h j h'' HRI Hpick Hj Hfd Heof Hmo Hmap Hheld Ht HO Hep HS).
Qed.
(* top_x LS_rf_room: ReplyLS3oRf.v LS_rf_room_p *)
Lemma lsi_LS_rf_room : forall cx t m ly S,
  LSx cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_LLVMFuzzerTestOneInput_exit.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m)
    (lm_es m).
Proof.
  intros cx t m ly S H Ht. lsi_open H.
  exact (LS_rf_room_p B OM cx t m ly S H3c HO Ht).
Qed.
(* top_x LS_exit_budget (relay_finish's count: its room at the row's t, the keys by the row's last premise) *)
Lemma lsi_LS_exit_budget : forall cx t m ly S, LSx cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m).
Proof.
  intros cx t m ly S H Ht Hk.
  lsi_open H.
  exact (fr_SEC_exit_budget nsec KMAX KC HKC cx t m ly S (LS_rf_room_p B OM cx t m ly S H3c HO Ht) Hk HS).
Qed.
(* top_x LS_rm_cnl_pre: ReplyLS3Arms.v fr_LS3_rm_cnl_pre_p; the meter by fr_SEC (the row's t and partial-line bounds) *)
Lemma lsi_LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) out2,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall rest, Permutation (ablocks TfibB ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks TfibB ly S) (input_blks cx ++ model_blks (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si (Some h1) j0 c2 O2 cap2 out2) ++ rest)) ->
  cnl_room CfParamsReply.fr_MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 H HRI Hat Hrr Ht HU Hmo Hpos HPm. lsi_open H.
  split; [exact (fr_LS3_rm_cnl_pre_p B cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 H3 HRI Hat Hrr Hmo Hpos
                   HPm)|].
  change (nsec S <= nsec S0 + W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost in Hmo. rewrite (sec_tr nsec KMAX) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost.
  apply (fr_SEC_rm_after nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 0 _ HRI Hat Hrr Ht HU);
    [lia | lia | exact HS].
Qed.
(* top_x LS_rm_cshe_pre *)
Lemma lsi_LS_rm_cshe_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H',
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)) ->
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H').
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H HRI Hat Hrr Ht HU _ Hmo. lsi_open H.
  change (nsec S <= nsec S0 + (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
    W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1))) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost, W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost in Hmo.
  rewrite (sec_tr nsec KMAX) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost. rewrite (sec_cshe nsec KMAX).
  apply (fr_SEC_rm_after nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2
           (cnl_cost MT (hs_expected h1) (hs_held h1)) 0 HRI Hat Hrr Ht HU); [lia | lia | exact HS].
Qed.
(* top_x LS_rm_sr_pre *)
Lemma lsi_LS_rm_sr_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc,
  LSx cx t m ly0 S0 -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  W_LLVMFuzzerTestOneInput_remove.rm_cnl_ok h1 E' H' -> W_LLVMFuzzerTestOneInput_remove.rm_cshe_ok m (set_exp_held h1 E' H') O2 (W_LLVMFuzzerTestOneInput_remove.rm_A1 m h1) H'' ds cc ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H') ->
  mo_ok MT S (sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))).
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc H HRI Hat Hrr Ht HU _ _ Hmo. lsi_open H.
  change (nsec S <= nsec S0 + (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
    W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H')) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost, W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost,
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost in Hmo.
  rewrite (sec_tr nsec KMAX), (sec_cshe nsec KMAX) in Hmo. rewrite (sec_sr nsec KMAX).
  apply (fr_SEC_rm_after nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2
           (cnl_cost MT (hs_expected h1) (hs_held h1)) 0 HRI Hat Hrr Ht HU); [lia | lia | exact HS].
Qed.
(* top_x LS_exit_end, fr_live_post := fr_live_post3 OM, fr_surv := ACfn_cf.fr_surv B (ReplyLS3e.v LS_exit_end3e), the
   meter conjunct by fr_SEC (the call's count within SEC_CALL <= XN_LIB).  ROUTE R (a Theorem Labs lane, 2026-10-31): stated at
   any world relation R, its journal premise at ajournal_gx_xR .. R, for lib/A/W_LLVMFuzzerTestOneInput_exit_x.v's LS_exit_end_R (Section exitR),
   through ReplyLS3e.v LS_exit_end3e_xR; the strict lsi_LS_exit_end below is its instance at R := wle *)
Lemma lsi_LS_exit_end_xR : forall fr_FP ARX G (R : world segs -> world segs -> Prop),
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  ajournal_gx_xR segs TfibB [] ARX R G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post3 OM (c_S cx) (stack_free_state 1 fpos S') k' /\
  ACfn_cf.fr_surv B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof.
  intros fr_FP ARX G R cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H HP3 HP' Hfr Hmo HC0 HJ Hcap Ht
    HFH HND Hk.
  lsi_open H.
  assert (HM : mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx))).
  { pose proof (fr_SEC_exit_end nsec KMAX KC HKC cx t m ly3 S3 S' C fpos HNSF Hmo HC0
                  (LS_rf_room_p B OM cx t m ly3 S3 H3c HO Ht) Hk HS) as X.
    pose proof (HXN (c_n cx)). change (nsec (stack_free_state 1 fpos S') <= nsec (c_S cx) + XN_LIB (c_n cx)). lia. }
  enough (E : fr_live_post3 OM (c_S cx) (stack_free_state 1 fpos S') k' /\
              ACfn_cf.fr_surv B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem')
    by exact (conj (proj1 E) (conj (proj2 E) HM)).
  eapply LS_exit_end3e_xR; eassumption.
Qed.

(* top_x LS_exit_end (lib/A/W_LLVMFuzzerTestOneInput_exit_x.v:183, the strict rule): lsi_LS_exit_end_xR at R := wle *)
Lemma lsi_LS_exit_end : forall fr_FP ARX G,
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  LSx cx t m ly3 S3 ->
  Permutation (ablocks TfibB ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks TfibB ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_LLVMFuzzerTestOneInput_exit.lx_exit_cost MT m ->
  ajournal_gx_x segs TfibB [] ARX G 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks TfibB ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_live_post3 OM (c_S cx) (stack_free_state 1 fpos S') k' /\
  ACfn_cf.fr_surv B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) ly' (stack_free_state 1 fpos S') W' mem' /\
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof. intros fr_FP ARX G. exact (lsi_LS_exit_end_xR fr_FP ARX G (@wle segs)). Qed.

(* ---------------------------------------------------------------- the sum-form rows at their peak forms *)
(* ReplyLS3Peak.v (the sum form `blocks_bytes S + tr_alloc ..` is false at reachable states), the meter conjuncts by
   fr_SEC.  LS_rm_rr_pre and LS_gone_rig read g_capout's bound through the entry's CAPOUT clause (their last premise;
   ReplyLS3eCap.v ls3e_cap_lt_MMAX), so they hold at OM := OUT_MAX4; LS_drain_pre at any OM *)
(* top_x LS_drain_pre: ReplyLS3Peak.v pk_drain_pre *)
Lemma lsi_LS_drain_pre : forall cx t m ly S si h j,
  LSx cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j H HRI Hat Hpick Hj Hfd Heof Ht HU Hpos. lsi_open H.
  destruct (pk_drain_pre B cx t m ly S si h j H3 HRI Hat Hpick Hj Hfd Heof Ht HU Hpos) as (C1 & C2 & C3 & C4 & C5).
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5
    (fr_SEC_drain_pre nsec KMAX KC HKC B cx t m ly S si h j H3 HRI Hat Hpick Hj Hfd Heof Ht HU HS)))))).
Qed.
(* top_x LS_rm_rr_pre, OM := OUT_MAX4: ReplyLS3Peak.v pk_rm_rr_pre *)
Lemma lsi_LS_rm_rr_pre : forall cx t m ly S si h j0,
  LSI B OUT_MAX4 nsec KMAX KC cx t m ly S -> RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) /\ lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + 4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 H HRI Hat Ht HU Hpos HSRC HCAP0.
  destruct H as ((H3c & HPOT) & HOU & HE & _ & HS).
  destruct (pk_rm_rr_pre B cx t m ly S si h j0 (conj H3c (conj HOU HE)) HRI Hat Ht HU Hpos HSRC HCAP0)
    as (C1 & C2 & C3 & C5 & C6).
  exact (conj C1 (conj C2 (conj C3 (conj (fr_SEC_rm_rr_pre nsec KMAX KC HKC cx t m ly S si h j0 HRI Hat Ht HU HS)
    (conj C5 C6))))).
Qed.
(* top_x LS_gone_rig at gone_base's GN_LS_rig, OM := OUT_MAX4: ReplyLS3Peak.v pk_gone_rig, the meter by
   ReplyLSsecGn.v fr_SEC_gone_rig *)
Lemma lsi_GN_LS_rig :
  W_LLVMFuzzerTestOneInput_gone_base.GN_LS_rig MT (LSI B OUT_MAX4 nsec KMAX KC) RINV CfParamsReply.fr_MMAX.
Proof.
  unfold W_LLVMFuzzerTestOneInput_gone_base.GN_LS_rig.
  intros cx t m ly S hs H HRI Hp Hop HU Hpos HSRC HCAP0.
  destruct H as ((H3c & HPOT) & HOU & HE & _ & HS).
  destruct (pk_gone_rig B cx t m ly S hs (conj H3c (conj HOU HE)) HRI Hp Hop HU Hpos HSRC HCAP0) as (R1 & R2 & R4 & R5).
  exact (conj R1 (conj R2 (conj (fr_SEC_gone_rig nsec KMAX KC HKC B cx t m ly S hs H3c HRI Hp Hop HU HSRC HS)
    (conj R4 R5)))).
Qed.

(* ---------------------------------------------------------------- the gone rules *)
(* RI_gone_step at gone_base's text (the KF-COUNT text: q, gn_runc, gn_cst): the RINV half is a Theorem Labs lane's (any LS);
   the room half at LSI's fr_LS3c, the two meter halves by ReplyLSsecGn.v from fr_SEC *)
Lemma lsi_GN_RI_step : (forall LS, G8.GN_RI_step_ri B MT LS RINV) ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step B MT LSx RINV CfParamsReply.fr_MMAX.
Proof.
  intros HRI. apply G8.GN_RI_step_split; [exact (HRI _) | | |].
  - unfold G8.GN_RI_step_room.
    intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
      P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
    lsi_open P7.
    exact (gx8_step_room_c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q P1 P2 P3 P4 P5 P6 H3c
      P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20).
  - unfold G8.GN_RI_step_cnl_meter.
    intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
      P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
    lsi_open P7.
    exact (fr_SEC_gone_cnl nsec KMAX KC HKC B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx cst q H3c P1 P2 P3 P4
      P5 P6 P8 P9 P10 P12 P13 P14 P17 P18 HS).
  - unfold G8.GN_RI_step_cshe_meter.
    intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
      P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 h' E' H' Sy Hc Hm.
    lsi_open P7.
    exact (fr_SEC_gone_cshe nsec KMAX KC HKC B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx Sy cst q h' H3c P1 P2
      P3 P4 P5 P6 P8 P9 P10 P12 P13 P14 P17 P18 Hm HS).
Qed.
(* RI_gone_end at gone_base's text: the RINV half is a Theorem Labs lane's (any LS); the LS half at LSI from its six twins:
   fr_LS3c (ReplyLS3cTopxGone8.v gx8_end_LS3c), fr_POT (ReplyLS3pGn.v fr_POT_gone_end), fr_OUT (ReplyLS3oGn.v
   fr_OUT_gone_end), fr_ENT (ReplyLS3e.v fr_ENT_gone_end, its REQ5 from ReplyLS3cTopxGoneH.v gxh_req5), fr_CAP
   (ReplyLScap.v fr_CAP_gone_end), fr_SEC (ReplyLSsecGn.v fr_SEC_gone_end) *)
Lemma lsi_GN_RI_end : (forall LS, G8.GN_RI_end_ri B MT LS RINV) ->
  W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end B MT LSx RINV.
Proof.
  intros HRI. apply G8.GN_RI_end_split; [exact (HRI _) |].
  unfold G8.GN_RI_end_ls.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
  lsi_open P8.
  pose proof (proj2 HP) as HPOT.
  pose proof (gxh_req5 cx t m hs qs c2 O2 cap2 out2 m1 mc A _ _ P1 P9 P10 P11 P12) as HR5.
  lsi_goal.
  - split.
    + exact (gx8_end_LS3c B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q P1 P2 P3 P4 P5 P6 P7 H3c
        P9 P10 P11 P12 P13 P14 P15 P16).
    + exact (fr_POT_gone_end cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx P1 P2 P3 P5 P6 P7 HPOT P9 P10 P11 P12).
  - eapply fr_OUT_gone_end; eassumption.
  - eapply fr_ENT_gone_end; eassumption.
  - eapply fr_CAP_gone_end; eassumption.
  - exact (fr_SEC_gone_end nsec KMAX KC HKC B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q H3c P1 P2 P3 P5 P6
      P7 P9 P10 P11 P12 P13 P14 P15 HS).
Qed.
End lsi.

(* ================================================================== LSI is satisfiable *)
(* ReplyLS3.v sat3's allocator state (the 1-byte input block, the relay's table, one open source's partial buffer) and
   model ls3_m (the first head's), with the call's ENTRY state holding only the input block (so the entry's harness
   blocks are none: fr_hblks reads nothing at ls3_W / an empty memory), at t = 0.  fr_CAP holds there because
   lm_cap (ls3_m B) = 0 (ReplyLScap.v fr_CAP_sat_at); fr_SEC because the model holds no bytes, given the meter's count
   at the two states (the meter is a Variable here: lsi_sat_count gives it at nsec := 0) *)
Section sat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition lsi_S0 : astate := YG00.set_chunks [ls3_k0] YG00.init_state.
Definition lsi_cx : lfcx (rc := rc) :=
  LFCX ls3_ly lsi_S0 ls3_W bvmap_empty (fun _ => None) ls3_md (ls3_p B) 1 [Z_to_bv 8 7] 0.
Lemma lsi_sat : forall OM nsec KMAX KC, OUT_MAX4 <= OM ->
  nsec ls3_S <= nsec lsi_S0 -> nsec lsi_S0 + SEC_CALL KC <= KMAX ->
  LSI B OM nsec KMAX KC lsi_cx 0 (ls3_m B) ls3_ly ls3_S.
Proof.
  intros OM nsec KMAX KC HOM HN1 HN2.
  assert (EA : ablocks B ls3_ly ls3_S = input_blks lsi_cx ++ model_blks (ls3_m B) ++ []) by reflexivity.
  assert (E0 : ablocks B ls3_ly lsi_S0 = input_blks lsi_cx ++ [] ++ []) by reflexivity.
  assert (Hbb : blocks_bytes ls3_S = 1 + ATABLE + APARTIAL) by (vm_compute; reflexivity).
  assert (Hb0 : blocks_bytes lsi_S0 = 1) by (vm_compute; reflexivity).
  assert (Hin : bsum (input_blks lsi_cx) = 1) by reflexivity.
  assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
  assert (HS : c_S lsi_cx = lsi_S0) by reflexivity.
  assert (Hn : c_n lsi_cx = 1) by reflexivity.
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (En : npend (ls3_m B) = 0) by reflexivity.
  assert (Ek : kk lsi_cx (ls3_m B) = 0) by reflexivity.
  assert (Eo : nopen (lm_hs (ls3_m B)) = 1) by reflexivity.
  assert (Ep : PHI3 (ls3_m B) = ATABLE + APARTIAL + E_ENT + K0) by reflexivity.
  assert (EH : fr_hblks (c_W lsi_cx) (c_mem lsi_cx) = []) by (vm_compute; reflexivity).
  unfold LSI, fr_LS3cp.
  refine (conj (conj (conj _ _) _) (conj _ (conj _ (conj (fr_CAP_sat_at B lsi_cx ls3_ly ls3_S) _)))).
  - exists [], 0. rewrite EA, HS, Hb0, Hn, Hin, Hrest, HC, HL, En, Ek, Eo, Ep.
    split; [apply Permutation_refl|].
    unfold W_OPEN, MB_K, MB_C, ATABLE, APARTIAL, E_ENT, K0.
    refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
  - unfold fr_CNT. rewrite EA, !cnt_sec_app, cnt_sec_nil.
    split; [unfold ReplyCnt.SEC0; lia | split; [| rewrite En; lia]].
    intros c. rewrite !cnt_cls_app, cnt_cls_nil. unfold ReplyCnt.CLS0. lia.
  - intros c. assert (E1 : pt_kc c (ls3_m B) = 0) by reflexivity. assert (E2 : pt_mass (ls3_m B) = 0) by reflexivity.
    rewrite E1, E2. lia.
  - assert (EM : bsum (model_blks (ls3_m B)) = ATABLE + APARTIAL) by (vm_compute; reflexivity).
    assert (EC : lm_cap (ls3_m B) = 0) by reflexivity.
    assert (EMass : MASS (ls3_m B) = 0) by reflexivity.
    unfold fr_OUT, XB. rewrite HS, Hb0, Hbb, EM, EC, EMass. unfold OUT_MAX4 in HOM. unfold ATABLE, APARTIAL.
    repeat split; lia.
  - intros rest Hr. rewrite EA in Hr.
    pose proof (ent_rest_eq _ _ _ _ _ (Permutation_refl (input_blks lsi_cx ++ model_blks (ls3_m B) ++ [])) Hr) as Hrr.
    change (ablocks B (c_ly lsi_cx) (c_S lsi_cx)) with (ablocks B ls3_ly lsi_S0). rewrite E0, EH.
    apply Permutation_app_head, Permutation_app_head. exact Hrr.
  - assert (EU : sec_ub (ls3_m B) = 0) by reflexivity.
    exact (fr_SEC_init nsec KMAX KC lsi_cx (ls3_m B) ls3_ly ls3_S HN2 HN1 EU).
Qed.
(* the meter's count at nsec := 0 with KMAX := SEC_CALL KC: LSI is not empty at any KC *)
Lemma lsi_sat_count : forall OM KC, OUT_MAX4 <= OM ->
  LSI B OM (fun _ => 0) (SEC_CALL KC) KC lsi_cx 0 (ls3_m B) ls3_ly ls3_S.
Proof. intros OM KC HOM. apply lsi_sat; [exact HOM | lia | lia]. Qed.
End sat.
