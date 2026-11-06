(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyLSBDrainPre.v, with its module paths and module names changed; 631 of its 771 lines of code are new or changed and 546 lines of the source are left out. *)
(* The PEAK-form rows of the three top_x rules whose sum-form room conjunct is false at reachable states, and their
   proofs at LS v3.  proves no function (kind: invariant lemma).
   top_x (W_LLVMFuzzerTestOneInput_top_x.v at the TOP head 3d17f490d56) states LS_drain_pre and LS_rm_rr_pre at this
   file's former TX_ texts, and gone_base's GN_LS_rig is its former TX_GN_LS_rig: each is the old sum-form row with
   every `blocks_bytes S + tr_alloc X` as `blocks_bytes S + tr_peak X` (ReplyTrPeak.v:120) and the premises the
   proof needs added LAST.  ReplyLSI.v states all three at top_x's text (lsi_LS_drain_pre / lsi_LS_rm_rr_pre /
   lsi_GN_LS_rig) from pk_drain_pre / pk_rm_rr_pre / pk_gone_rig below, which state the rows' room conjuncts; the rows'
   meter conjuncts are ReplyLSI.v's (from its fr_SEC).  The cap conjuncts need OM := OUT_MAX4
   (ReplyLS3eCap.ls3e_cap_lt_MMAX).

   THE ADDED PREMISES, each with the arm site that holds it where the rule is applied (integ = riplug 5dfdaedea77;
   gone = 6a2e02357a4; W_rep.v is the same text in both):
   (1) LS_drain_pre (lib/A/W_LLVMFuzzerTestOneInput_drain_x.v dc_stB :2618, the rule applied at :2741):
       `0 <= t < OPS_MAX`              - Ht, dc_regs' clause (drain_x.v:1740), destructed from HR at :2629;
       `|re_U (nth j ..)| <= APARTIAL` - HEOK :2683 (aentry_ok of entry j from HREL's Forall, :2675), W_rep.v:125;
       the blocks' sizes `0 < snd b`   - HXP :2731-2735 (the premise of v2's fr_LS_drain_pre_c5p, word for word).
   (2) LS_rm_rr_pre (lib/A/W_LLVMFuzzerTestOneInput_remove_x.v rm_rr_x :1624, the rule applied at :1681):
       `0 <= t < OPS_MAX`              - Rt :1636, lregs_rr's rm_regs_base clause (_remove.v:358, :371);
       `|re_U (rm_ent m j0)| <= APARTIAL` - HREL :1639 (arelay_at's Forall aentry_ok, W_rep.v:162), entry j0 (Hj0
                                         :1634), aentry_ok W_rep.v:125;
       `forall b, In b (model_blks m) -> 0 <= snd b` - HMOD :1635 through (rr_blks_pos B) (_remove.v:2257), as the
                                         arm itself uses it at :1745;
       the source's read offset (HSRC)  - HSRC :1640 (asrc_at of slot si), its clause W_rep.v:104-105; the same text
                                         is top_x's LS_rm_step premise :551-552;
       HCAP0 `exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX`
                                       - the cut pre's last conjunct (fr_lib_pre_cf, _cut.v:213, word for word),
                                         reached through the arm's lf_base (HB :1633).
   (3) gone_base's GN_LS_rig (this file's former TX_GN_LS_rig, which W8 adopted; lib/A/W_LLVMFuzzerTestOneInput_gone_p3.v gp3_rig_c1 :908, the rule
       applied at :995):
       `gn_op cx t m`                   - HOP :914 (GRG's clause, lib/A/W_LLVMFuzzerTestOneInput_gone_base.v:676; its parts lm_O m = [] and
                                         0 <= t < OPS_MAX are what R1 reads);
       `Forall (|re_U| <= APARTIAL) (lm_es m)` - HREL :924, arelay_at W_rep.v:162 -> aentry_ok :125 (lib/A/W_LLVMFuzzerTestOneInput_gone_p3.v
                                         :1345-1347 already reads this clause);
       `forall b, In b (model_blks m) -> 0 <= snd b` - HMOD :914 (amodel_at), by the proof of _remove.v:2257
                                         rr_blks_pos;
       every slot's read offset (HSRC)  - HSLOT :924 (amodel_at's aslot for i < 4, _cut.v:378), clause W_rep.v:104-105;
       HCAP0                            - as in (2), through gp3_rig_c1's lf_base (:909).

   WHY EACH IS NEEDED.  t and |re_U| are the two facts of ReplyLSDrainPre.v / ReplyLSRrPre.v (pending 2^25 + 2 bytes
   and drain's first growth unbounded without them).  The blocks' sizes: ReplyTrPeak.v's header (a negative size
   makes a realloc's net growth unbounded in the model).  HCAP0: neither fr_LS3 nor fr_RINV bounds lm_cap
   (ReplyLS3eCap.v's header).  HSRC: only for the `+ 4 * Z.max (lm_cap m) (tr_max ..)` conjunct (conj. 6 / R5), whose
   proof reads the PENDING CREDIT 64 * pend_bytes m that fr_LS3's potential already holds (pk_room_pend below); HSRC
   makes |pending_stream h| = slot_pend (Some h) (ReplyLS3Arms.ls3_ps_sp).

   THE ARITHMETIC (LIVE_MAX = 2^34; fr_LS3_room_x: blocks_bytes S + 4,160,659,073 <= LIVE_MAX; P = |pending_stream|,
   K = keys_total, |keys| <= K, K + P < 2^26, P <= 65535 * 511 = 33,488,385 at t < OPS_MAX):
   - drain, conj. 5: tr_peak <= tr_pos + tr_max <= (44 P + 8 |keys| + 92320) + (WR_MMAX - 1).  The slack form
     (+ tr_max) needs 44 P + 8 |keys| + 92320 + 2 (WR_MMAX - 1) <= 1,742,452,764 + 92,320 + 2,145,386,494
     = 3,887,931,578: 272,727,495 under v3's 4,160,659,073 (v2: 272,794,055 under 4,160,725,633; the 66,560
     difference is covered).
   - remove, conj. 3: (48 P + 10 K + 116320) + 2 tr_max; with v2's tr_max < WR_MMAX this is <= 4,089,150,074
     (71,508,999 to spare); the proof uses pk_rr_tr_max (<= 3,017,601,404).
   - conj. 6 / R5 need a tr_max bound far under WR_MMAX: 4 * (WR_MMAX - 1) = 4,290,772,988 alone exceeds the room.
     The bound: reference_feed's expected array grows at n = cap to 32 cap, and its capacity stays 0 or 8 * 2^k
     (ecap_ok, SlotInv.v:98, and push_cap doubles it), so with n < P + 1 <= 2^25 the growth is at most
     32 * 2^24 = 2^29 (pk_pushes_run8); every other request of a drain, of relay_remove's key run and of
     relay_instance_gone's run is at most 8 (2^26 + 6000).  So tr_max <= pk_TXM = 536,918,912 (pk_rr_tr_max; the
     gone run's pk_run_rq8).  With the flat room this still fails (remove: 48 P + 10 K + 116320 + 5 pk_TXM can reach
     4,628,358,140), so the proofs read the pending credit: blocks_bytes S + 4,160,659,073 + 64 pend_bytes m <=
     LIVE_MAX (pk_room_pend) and P <= pend_bytes m (HSRC):
       remove: 48 P + 10 K + 116320 + 5 pk_TXM - 64 P <= 671,088,630 + 116,320 + 2,684,594,560 = 3,355,799,510;
       gone:   12 Zk + 46 Zp + 417280 + 5 pk_TXM - 64 Zp <= 805,306,356 + 417,280 + 2,684,594,560 = 3,490,318,196,
     both under 4,160,659,073 (Zk, Zp: the run's keys_total and pending bytes; Zk <= c_n < 2^26; lm_cap <= 2^29 <=
     pk_TXM by HCAP0). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3 ReplyTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLS3Arms ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o ReplyLS3e ReplyLS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3cTopxRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
  ReplyLS3cTopxGoneF ReplyLS3cTopxPro ReplyLS3cTopxPost ReplyLS3cTopxGone8.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).
(* _cut.v's segs (the entry clause's image, as top_x and gone_base state the clause) *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).

(* ================================================================== the instance's MMAX *)
Lemma pk_fr_MMAX : CfParamsReply.fr_MMAX = WR_MMAX.
Proof. reflexivity. Qed.
Lemma pk_WR_MMAX : WR_MMAX = 1072693248.
Proof. reflexivity. Qed.
(* every request bound below: 8 (2^26 + 6000) *)
Definition pk_TXM : Z := 536918912.

(* ================================================================== the expected array's capacity *)
(* 0 or 8 * 2^k: SlotInv.ecap_ok without its upper end, kept by push_cap *)
Definition pk_pw8 (c : Z) : Prop := c = 0 \/ exists k, 0 <= k /\ c = 8 * 2 ^ k.
Lemma pk_pw8_ecap : forall c, SlotInv.ecap_ok c -> pk_pw8 c.
Proof. intros c [H|(k & Hk & H)]; [left; exact H | right; exists k; split; [lia | exact H]]. Qed.
Lemma pk_pw8_push : forall n c, pk_pw8 c -> pk_pw8 (drain_b_c.push_cap n c).
Proof.
  intros n c Hc. unfold drain_b_c.push_cap.
  destruct (Z.eqb_spec n c); [|exact Hc].
  destruct (Z.eqb_spec c 0) as [E|E].
  - right. exists 0. split; [lia | reflexivity].
  - destruct Hc as [Hc|(k & Hk & Hc)]; [contradiction|].
    right. exists (k + 1). split; [lia|]. rewrite Hc, Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
Qed.
(* below 2^25 such a capacity is at most 2^24 *)
Lemma pk_pw8_le : forall c E, pk_pw8 c -> c < E -> E <= 2 ^ 25 -> c <= 2 ^ 24.
Proof.
  intros c E [->|(k & Hk & ->)] H1 H2; [lia|].
  assert (E21 : 2 ^ 21 = 2097152) by reflexivity. assert (E22 : 2 ^ 22 = 4194304) by reflexivity.
  assert (E24 : 2 ^ 24 = 16777216) by reflexivity. assert (E25 : 2 ^ 25 = 33554432) by reflexivity.
  destruct (Z_le_gt_dec k 21) as [Hle|Hgt].
  - pose proof (Z.pow_le_mono_r 2 k 21 ltac:(lia) Hle). lia.
  - pose proof (Z.pow_le_mono_r 2 22 k ltac:(lia) ltac:(lia)). lia.
Qed.

(* reference_feed's pushes (ReplyLSDrainPre.v dpre_pushes_run, the array's growth at most 2^29) *)
Lemma pk_pushes_run8 : forall ls n cap j v rs M En,
  Forall (fun l => Z.of_nat (length l) <= 6000) ls -> n + Z.of_nat (length ls) <= En -> En <= 2 ^ 25 ->
  pk_pw8 cap -> 2 ^ 29 <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.pushes_run n cap ls j v rs))) /\
  pk_pw8 (snd (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  assert (E24 : 2 ^ 24 = 16777216) by reflexivity. assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  induction ls as [|l r IH]; intros n cap j v rs M En HF Hn HE Hc H29 H6; cbn [drain_b_c.pushes_run].
  - cbn [fst snd]. split; [constructor | exact Hc].
  - apply Forall_cons_iff in HF as [Hl HF]. cbn [length] in Hn.
    match goal with |- context [drain_b_c.pushes_run (n + 1) ?c2 r ?j2 ?v2 ?rs2] =>
      destruct (IH (n + 1) c2 j2 v2 rs2 M En HF ltac:(lia) HE (pk_pw8_push n cap Hc) H29 H6) as [I1 I2] end.
    cbn [fst snd]. split; [|exact I2].
    apply Forall_app. split; [|exact I1].
    unfold ListTr.list_push_tra. apply Forall_app. split.
    + destruct (Z.eqb_spec n cap) as [E|E]; [|constructor].
      pose proof (pk_pw8_le cap En Hc ltac:(lia) HE) as Hle.
      destruct (cap =? 0); (apply Forall_cons; [cbn [dpre_rq]; lia | constructor]).
    + apply Forall_cons; [cbn [dpre_rq]; lia | constructor].
Qed.

(* drain's rounds (ReplyLSDrainPre.v dpre_drain_run with the capacity's form kept) *)
Definition pk_inv8 (Hk A En : Z) (s : drain_b_c.dstate) : Prop :=
  dpre_inv Hk A En s /\ pk_pw8 (drain_b_c.ds_ecap s).
Lemma pk_drain_run8 : forall f live mx s j a M Hk A En, pk_inv8 Hk A En s ->
  20192 <= M -> 2 * A <= M -> 8 * (Hk + A) <= M -> En <= 2 ^ 25 -> 2 ^ 29 <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx s j a M Hk A En (HI & Hpw) Hg H2 H8 HE H29 H6; [constructor|].
  pose proof HI as (Iu & Io & Ir & Ia & Ih & Ie).
  cbn [drain_b_c.drain_run].
  pose proof (dpre_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) M
                ltac:(lia) Hg) as G1.
  destruct (drain_b_c.ds_eintr s).
  - (* EINTR: the growth only, then the same state *)
    cbn [fst]. apply Forall_app. split; [exact G1|].
    apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
    unfold pk_inv8. split; [|cbn [drain_b_c.ds_ecap]; exact Hpw].
    unfold dpre_inv, dpre_rem in HI |- *.
    cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
         drain_b_c.ds_pend].
    exact HI.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP; [exact G1|].
    assert (Hrem : dpre_rem s = Z.of_nat (length r0) + Z.of_nat (length (concat rs)) - drain_b_c.ds_off s).
    { unfold dpre_rem. rewrite EP. cbn [concat]. rewrite length_app. lia. }
    match goal with |- context [Z.leb ?x 0] => destruct (Z.leb_spec x 0) as [Hn0|Hn0] end; [exact G1|].
    match type of Hn0 with 0 < ?x =>
      assert (Hn1 : x <= Z.of_nat (length r0) - drain_b_c.ds_off s) by lia;
      set (n := x) in * end.
    assert (Hd : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0))) = n)
      by (rewrite length_firstn, length_skipn; lia).
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
    destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
    destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & C2 & C3).
    cbv beta iota.
    destruct (dpre_ref_lines d (drain_b_c.ds_ref s) Ir) as (R1 & R2 & R3).
    match goal with |- context [drain_b_c.pushes_run ?n0 ?c ?ls ?jj ?v ?rs0] =>
      destruct (pk_pushes_run8 ls n0 c jj v rs0 M En R1 ltac:(lia) HE Hpw H29 H6) as [P1 P2] end.
    match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
      pose proof (dpre_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 M Hk A C1 ltac:(lia) ltac:(lia) H2 H8 H6)
        as [L1 L2];
      revert L1 L2;
      destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
      intros L1 L2 end.
    cbn [fst snd] in L1, L2 |- *.
    apply Forall_app. split; [exact G1|].
    apply Forall_app. split; [exact P1|].
    destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [Ew|Ew].
    + (* the head text is read to its end: list_drop frees it *)
      apply Forall_app. split; [unfold ListTr.list_drop_tra; apply Forall_cons; [exact I | constructor]|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold pk_inv8. split; [|cbn [drain_b_c.ds_ecap]; exact P2].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend].
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
    + apply Forall_app. split; [constructor|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold pk_inv8. split; [|cbn [drain_b_c.ds_ecap]; exact P2].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend concat].
      rewrite length_app.
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
Qed.

(* one drain from g_nout = 0 (ReplyLSDrainPre.v dpre_dr_tr_max at any M of the four sizes) *)
Lemma pk_dr_tr_max8 : forall c mx cap e h M,
  Z.of_nat (length (re_U e)) <= APARTIAL ->
  hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h) ->
  0 <= hs_off h -> hl_recs (hs_expected h) = [] -> SlotInv.ecap_ok (hl_cap (hs_expected h)) ->
  Z.of_nat (length (pending_stream h)) <= 65535 * 511 ->
  20192 <= M -> 2 * (6000 + Z.of_nat (length (pending_stream h))) <= M ->
  8 * (Z.of_nat (length (re_keys e)) + (6000 + Z.of_nat (length (pending_stream h)))) <= M -> 2 ^ 29 <= M ->
  tr_max (dr_tr c mx 0 cap e h) <= M.
Proof.
  intros c mx cap e h M HU HJ Ho He Hec Hp Hg H2 H8 H29.
  assert (E25 : 2 ^ 25 = 33554432) by reflexivity. assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  unfold APARTIAL in HU.
  unfold dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go.
  apply dpre_tr_max; [lia|].
  apply (pk_drain_run8 _ _ _ _ _ _ M (Z.of_nat (length (re_keys e)))
           (6000 + Z.of_nat (length (pending_stream h))) (Z.of_nat (length (pending_stream h))));
    [|lia ..].
  unfold pk_inv8. split; [|cbn [drain_b_c.drain_init drain_b_c.ds_ecap]; exact (pk_pw8_ecap _ Hec)].
  pose proof (dpre_rem_init 0 cap e h Ho) as Hr.
  unfold dpre_inv.
  cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H
       drain_b_c.ds_en] in Hr |- *.
  assert (Hu : length (bzs (re_U e)) = length (re_U e)) by (unfold bzs; apply length_map).
  split; [lia|]. split; [exact Ho|]. split.
  { unfold dpre_jref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
    destruct HJ as [E|E]; [left; rewrite E; reflexivity | right; rewrite <- E; lia]. }
  split; [lia|]. split.
  { unfold drain_b_c.keys_texts. rewrite length_map. lia. }
  unfold hl_n. rewrite He. cbn [length]. lia.
Qed.

Section req.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* relay_remove's requests (ReplyLSRrPre.v fr_LS_rm_rr_pre_c2's proof at pk_TXM; it reads RINV only) *)
Lemma pk_rr_tr_max : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= pk_TXM.
Proof.
  intros cx t m si h j0 HRI Hat Ht HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff).
  cbn [fst snd] in Hre, Hexp, Hec, Hpe, Hoff.
  destruct HE as (_ & _ & _ & _ & Hsk).
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (fr_keys_total_nonneg (re_keys (rm_ent m j0))) as HKT0.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  assert (HX0 : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr, rr_tr. cbv beta zeta.
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  destruct (hs_fd h <? 0); cbv iota; [unfold tr_max, pk_TXM; cbn [fold_right]; lia|].
  rewrite Hfind. cbv beta iota zeta.
  destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo; cbv iota.
  - (* open: drain's own trace, then the gesture ends of the keys it leaves, then two frees *)
    apply Z.eqb_eq in Eo.
    assert (HA : tr_max (dr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (rm_ent m j0) h) <= pk_TXM).
    { destruct (Hre Eo) as (S1 & W1). unfold pk_TXM. apply pk_dr_tr_max8.
      - exact HU.
      - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia.
      - exact Hoff.
      - exact Hexp.
      - exact Hec.
      - unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
      - lia.
      - lia.
      - lia.
      - lia. }
    rewrite rrp_tr_max_app.
    match goal with |- Z.max _ (tr_max ?KF) <= _ => assert (HB : tr_max KF <= pk_TXM) end.
    { unfold pk_TXM. apply dpre_tr_max; [lia|]. apply Forall_app. split.
      - apply rrp_ker_lens. unfold dr_fin.
        pose proof (rm3_no_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h Hoff) as NF.
        pose proof (rrp_fin_kw (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h) as KW.
        rewrite (rm3_skip_if (re_skip (rm_ent m j0)) (Z.of_nat (length (re_U (rm_ent m j0)))) Hsk) in NF.
        lia.
      - apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil. }
    lia.
  - (* at eof: no drain; the gesture ends of the entry's own keys from g_nout = 0, then two frees *)
    rewrite app_nil_l. unfold pk_TXM.
    apply dpre_tr_max; [lia|]. apply Forall_app. split.
    + apply rrp_ker_lens. cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_H].
      rewrite <- rm3_kt_kw. lia.
    + apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
Qed.

(* ================================================================== relay_instance_gone's requests *)
(* ReplyLS3cTopxRig.v grg_ok with the expected array's capacity of an open pair *)
Definition pk_ok8 (p : rentry * (hsrc * nat)) : Prop :=
  grg_ok p /\ (re_eof (fst p) = 0 -> SlotInv.ecap_ok (hl_cap (hs_expected (fst (snd p))))).

(* grg_entry_tr at pk_inv8 *)
Lemma pk_entry_tr8 : forall lv mx no cap (e : rentry) (hj : hsrc * nat) j (a0 : drain_b_c.dadr) M K,
  pk_ok8 (e, hj) -> grg_cost (e, hj) <= K ->
  2 * (no + 2 * grg_cost (e, hj) + 6000) <= M -> 8 * (K + 6000) <= M -> 2 ^ 29 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else []).
Proof.
  intros lv mx no cap e hj j a0 M K ((Hsk & Hop) & Hec8) HK HM H8 H29 Hg.
  unfold grg_cost in HK, HM. cbn [fst snd] in Hsk, Hop, Hec8, HK, HM.
  assert (E25 : 2 ^ 25 = 33554432) by reflexivity. assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  pose proof (fr_keys_total_nonneg (re_keys e)) as HKT.
  pose proof (dpre_keys_le (re_keys e)) as Hkl.
  revert HK HM. destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; intros HK HM; cbv iota in HK, HM |- *;
    [|constructor].
  destruct (Hop Eo) as (HU & HJ & Ho & He & Hp & _).
  pose proof (Hec8 Eo) as Hec.
  assert (Hu : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  unfold drain_b_c.drain_tr, drain_b_c.drain_go.
  apply (pk_drain_run8 _ _ _ _ _ _ M (Z.of_nat (length (re_keys e)) - no)
           (no + 6000 + Z.of_nat (length (pending_stream (fst hj)))) (Z.of_nat (length (pending_stream (fst hj)))));
    [| lia ..].
  unfold pk_inv8. split; [|cbn [drain_b_c.drain_init drain_b_c.ds_ecap]; exact (pk_pw8_ecap _ Hec)].
  pose proof (dpre_rem_init no cap e (fst hj) Ho) as Hr.
  unfold dpre_inv.
  cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H
       drain_b_c.ds_en] in Hr |- *.
  assert (Hu' : length (bzs (re_U e)) = length (re_U e)) by (unfold bzs; apply length_map).
  unfold APARTIAL in HU.
  split; [lia|]. split; [exact Ho|]. split.
  { unfold dpre_jref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
    destruct HJ as [E|E]; [left; rewrite E; reflexivity | right; rewrite <- E; lia]. }
  split; [lia|]. split.
  { unfold drain_b_c.keys_texts. rewrite length_map. lia. }
  unfold hl_n. rewrite He. cbn [length]. lia.
Qed.

(* grg_run_rq at pk_ok8 *)
Lemma pk_run_rq8 : forall ps lv mx pre nm no cap j o M K,
  Forall pk_ok8 ps -> zsum (map grg_cost ps) <= K ->
  2 * (no + 2 * zsum (map grg_cost ps) + 6000) <= M -> 8 * (K + 6000) <= M -> 2 ^ 29 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx pre nm no cap j o M K HF HK HM H8 H29 Hg.
  { cbn [relay_instance_gone_b_c.gone_run fst]. constructor. }
  apply Forall_cons_iff in HF as [Hok HF].
  cbn [map fold_right] in HK, HM.
  pose proof (grg_cost_nonneg (e, hj)) as Hc0.
  pose proof (zsum_map_nonneg grg_cost r grg_cost_nonneg) as Hr0.
  pose proof (grg_entry_no lv mx no cap e hj (proj1 Hok)) as HN.
  pose proof (grg_run_cons lv mx no cap pre e hj r nm j o) as EC. cbv zeta in EC. rewrite EC. clear EC.
  apply Forall_app. split.
  { apply (pk_entry_tr8 _ _ _ _ _ _ _ _ M K Hok); lia. }
  match goal with |- Forall _ (fst (gestures_end_b_c.keys_end_run ?lv' ?mx' (drain_b_c.ds_no ?S0) ?c1 ?X ?j1 ?o1)
                               ++ _) =>
    assert (HXF : Forall (fun x => 0 <= fst x) X)
      by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
    assert (HX : fold_right (fun x acc => fst x + 5 + acc) 0 X <= rm3_kw (drain_b_c.ds_H S0))
      by apply grg_xks_le;
    pose proof (grg_fold_fst _ X) as EF
  end.
  apply Forall_app. split.
  { apply rrp_ker; [exact HXF | lia]. }
  apply (IH lv mx pre nm _ _ _ _ M K HF); lia.
Qed.

(* the open pairs' expected arrays are fr_relay's rows' (grg_pair_pt's argument) *)
Lemma pk_pair_ecap : forall cx t m e p q,
  fr_RINV cx t m -> fr_pair_ok m t e q -> gn_pair_ok m e p -> SlotInv.ecap_ok (hl_cap (hs_expected (fst p))).
Proof.
  intros cx t m e p q HRI Hq Hp.
  destruct Hq as (Hq4 & Hqn & Hqf & _ & _ & _ & _ & Hec & _).
  destruct Hp as (Hp4 & Hpn & Hpf & _).
  assert (Es : fst p = fst q).
  { destruct (Nat.eq_dec (snd p) (snd q)) as [E|E].
    - rewrite E, Hqn in Hpn. injection Hpn as Hpq. exact (eq_sym Hpq).
    - exfalso. apply (RI_fds_holds cx t m (snd p) (snd q) (fst p) (fst q) HRI Hp4 Hq4 E Hpn Hqn).
      rewrite Hpf, Hqf. reflexivity. }
  rewrite Es. exact Hec.
Qed.
Lemma pk_pairs8 : forall cx t m hs,
  fr_RINV cx t m -> gn_pairs m hs -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  Forall pk_ok8 (combine (lm_es m) hs).
Proof.
  intros cx t m hs HRI HP Ht HUs.
  destruct (grg_pairs cx t m hs HRI HP Ht HUs) as (HF & _).
  pose proof HRI as (_ & HR & _).
  destruct HR as (_ & _ & _ & _ & hj & HF2 & _).
  pose proof HP as (HLhs & HFa & _).
  pose proof (Forall2_length HF2) as Lhj.
  apply Forall_forall. intros x Hx.
  split; [exact (proj1 (Forall_forall _ _) HF x Hx)|].
  intros Eo.
  pose proof (proj1 (Forall_forall _ _) HFa x Hx Eo) as Hp.
  apply (In_nth _ _ (gn_e0, gn_hj0)) in Hx as (i & Hi & Ex).
  rewrite length_combine in Hi.
  rewrite combine_nth in Ex by lia.
  subst x. cbn [fst snd] in Hp |- *.
  exact (pk_pair_ecap cx t m _ _ _ HRI (fr_F2_nth _ _ _ _ _ HF2 i gn_e0 gn_hj0 ltac:(lia)) Hp).
Qed.

(* ================================================================== the run's input, summed *)
Definition pk_gk (p : rentry * (hsrc * nat)) : Z := gestures_end_b_c.keys_total (re_keys (fst p)).
Definition pk_gp (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then Z.of_nat (length (pending_stream (fst (snd p)))) else 0.
Lemma pk_gk_nonneg : forall p, 0 <= pk_gk p.
Proof. intros p. unfold pk_gk. apply fr_keys_total_nonneg. Qed.
Lemma pk_gp_nonneg : forall p, 0 <= pk_gp p.
Proof. intros p. unfold pk_gp. destruct (re_eof (fst p) =? 0); lia. Qed.
Lemma pk_sum_cost : forall ps, Forall grg_ok ps ->
  zsum (map grg_cost ps) <= zsum (map pk_gk ps) + zsum (map pk_gp ps) + 6000 * Z.of_nat (length ps).
Proof.
  induction ps as [|p ps IH]; intros HF; cbn [map fold_right length]; [lia|].
  apply Forall_cons_iff in HF as [(Hsk & Hop) HF]. specialize (IH HF).
  assert (Hp : grg_cost p <= pk_gk p + pk_gp p + 6000).
  { unfold grg_cost, pk_gk, pk_gp.
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Eo|Eo]; cbv iota.
    - destruct (Hop Eo) as (HU & _). unfold APARTIAL in HU. destruct (re_skip (fst p) =? 0); lia.
    - lia. }
  lia.
Qed.
Lemma pk_sum_pc : forall ps,
  zsum (map grg_pc ps) <= 42 * zsum (map pk_gp ps) + 8 * zsum (map pk_gk ps) + 80320 * Z.of_nat (length ps).
Proof.
  induction ps as [|p ps IH]; cbn [map fold_right length]; [lia|].
  assert (Hp : grg_pc p <= 42 * pk_gp p + 8 * pk_gk p + 80320).
  { unfold grg_pc, pk_gk, pk_gp.
    pose proof (dpre_keys_le (re_keys (fst p))). pose proof (fr_keys_total_nonneg (re_keys (fst p))).
    destruct (re_eof (fst p) =? 0); lia. }
  lia.
Qed.
Lemma pk_sum_k : forall ps, zsum (map pk_gk ps) <= zsum (map grg_cost ps).
Proof.
  induction ps as [|p ps IH]; cbn [map fold_right]; [lia|].
  assert (Hp : pk_gk p <= grg_cost p).
  { unfold grg_cost, pk_gk. destruct (re_eof (fst p) =? 0); [destruct (re_skip (fst p) =? 0)|]; lia. }
  lia.
Qed.

(* ---------------------------------------------------------------- the open pairs' pending bytes *)
Lemma pk_zsum_perm : forall (g : nat -> Z) l l', Permutation l l' -> zsum (map g l) = zsum (map g l').
Proof. intros g l l' HP. induction HP; cbn [map fold_right]; lia. Qed.
(* distinct indices sum to at most all of them (ReplyLS3Arms.v ls3_sum_incl, any nonnegative weight) *)
Lemma pk_zsum_nodup_le : forall (g : nat -> Z) A Bl, (forall i, 0 <= g i) -> List.NoDup A -> incl A Bl ->
  zsum (map g A) <= zsum (map g Bl).
Proof.
  intros g. induction A as [|a A IH]; intros Bl Hg Hnd Hinc.
  - cbn [map fold_right]. apply zsum_map_nonneg. exact Hg.
  - apply NoDup_cons_iff in Hnd as [Ha Hnd].
    assert (Hin : In a Bl) by (apply Hinc; left; reflexivity).
    destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hi : incl A (l1 ++ l2)).
    { intros x Hx. assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hinc; right; exact Hx).
      apply in_app_iff in Hx' as [H1 | [H2 | H3]]; apply in_app_iff;
        [left; exact H1 | subst x; contradiction | right; exact H3]. }
    specialize (IH (l1 ++ l2) Hg Hnd Hi).
    rewrite (pk_zsum_perm g (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
    cbn [map fold_right]. lia.
Qed.
Lemma pk_zsum_seq : forall (f : option hsrc -> Z) l,
  zsum (map (fun i => f (nth i l None)) (seq 0 (length l))) = zsum (map f l).
Proof.
  intros f l. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map fold_right nth]. rewrite <- seq_shift, map_map. cbn [nth]. rewrite IH. reflexivity.
Qed.
Lemma pk_slots_cons : forall e (hj : hsrc * nat) ps,
  rig_slots ((e, hj) :: ps) = (if re_eof e =? 0 then [snd hj] else []) ++ rig_slots ps.
Proof. intros e hj ps. unfold rig_slots. cbn [map concat]. reflexivity. Qed.
Lemma pk_gp_slots : forall m ps,
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  zsum (map pk_gp ps) = zsum (map (fun i => slot_pend (nth i (lm_hs m) None)) (rig_slots ps)).
Proof.
  intros m. induction ps as [|[e hj] ps IH]; intros HF HS; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF].
  rewrite pk_slots_cons, map_app, zsum_app. cbn [map fold_right]. cbn [fst snd] in H1.
  change (pk_gp (e, hj)) with (if re_eof e =? 0 then Z.of_nat (length (pending_stream (fst hj))) else 0).
  rewrite <- (IH HF HS).
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; cbn [map fold_right].
  - destruct (H1 Eo) as (_ & Hn & _).
    rewrite Hn, (ls3_ps_sp (fst hj) (HS _ _ Hn)). lia.
  - lia.
Qed.
Lemma pk_gp_le_pend : forall m ps,
  length (lm_hs m) = 4%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
  List.NoDup (rig_slots ps) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  zsum (map pk_gp ps) <= pend_bytes m.
Proof.
  intros m ps Hl HF HND HS.
  rewrite (pk_gp_slots m ps HF HS).
  unfold pend_bytes. rewrite <- (pk_zsum_seq slot_pend (lm_hs m)).
  apply pk_zsum_nodup_le; [intros i; apply slot_pend_nonneg | exact HND |].
  intros i Hi. unfold rig_slots in Hi. apply in_concat in Hi as (l & Hl' & Hil).
  apply in_map_iff in Hl' as (p & <- & Hp).
  destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Eo|Eo]; [|destruct Hil].
  destruct Hil as [<- | []].
  destruct (proj1 (Forall_forall _ _) HF p Hp Eo) as (H4 & _).
  apply in_seq. rewrite Hl. lia.
Qed.

End req.

(* ================================================================== the instance *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* what LS v3 gives at any cut point with the pending credit kept: fr_LS3_room_x's proof without dropping
   W_P * pend_bytes from PHI3 *)
Lemma pk_room_pend : forall cx t m ly S, fr_LS3 B cx t m ly S ->
  blocks_bytes S + 4160659073 + W_P * pend_bytes m <= LIVE_MAX.
Proof.
  intros cx t m ly S (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP), !bsum_app.
  unfold PHI3, PHI, held_bytes, vslack in HM.
  pose proof (ECRED_nonneg m).
  pose proof (zsum_map_nonneg slot_held (lm_hs m) slot_held_nonneg).
  pose proof (zsum_map_nonneg entry_held (lm_es m) entry_held_nonneg).
  pose proof (zsum_map_nonneg slot_vsl (lm_hs m) slot_vsl_nonneg).
  pose proof (nopen_le4 _ Hl). pose proof (npend_nonneg m).
  assert (Hk : kk cx m <= c_n cx) by (unfold kk; lia).
  assert (HC : ACfn_cf.CALL_ROOM = 8589934592) by reflexivity.
  unfold MB_K, MB_C, W_OPEN, E_ENT, K0, APARTIAL, W_H, W_P in *. lia.
Qed.

(* ---------------------------------------------------------------- (1) LS_drain_pre *)
(* conjunct 5 in its slack form: ReplyTrPeak.v fr_LS_drain_pre_c5p_slack at fr_LS3 (fr_LS3_drain_pre_c4,
   fr_LS3_room_x) *)
Lemma pk_drain_c5_slack : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) +
    tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  pose proof (fr_LS3_drain_pre_c4 B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU) as HM.
  pose proof (fr_LS3_room_x B cx t m ly S HLS) as Hroom.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & Hcost).
  destruct Hp as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (S1 & W1).
  destruct Hat as (_ & HO & _).
  set (e := nth j (lm_es m) dr_e0) in *.
  destruct (tp_pos_entry e (fun b Hb => Z.lt_le_incl _ _ (HXP b (in_or_app _ _ _ (or_introl Hb))))) as [Hrc Hka].
  assert (Hcap : 0 <= lm_cap m).
  { apply (tp_pos_out (lm_cap m) (lm_out m)). intros b Hb. apply Z.lt_le_incl, HXP, in_or_app. right.
    apply in_or_app. right. exact Hb. }
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HJ : hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h)).
  { destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia. }
  replace (Z.of_nat (length (lm_O m))) with 0 in HM by (rewrite HO; reflexivity).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  destruct (tp_dr (lm_c m) (lm_mx m) (lm_cap m) e h Hcap Hrc Hka (proj1 Hec') Hoff Hexp HU HJ) as (D1 & _).
  pose proof (tr_peak_le_pos (dr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) e h)) as PK.
  unfold fr_pair_cost in Hcost. cbn [fst] in Hcost.
  pose proof (dpre_keys_le (re_keys e)) as Hkl.
  assert (HX : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0)) by (destruct (re_skip e =? 0); lia).
  assert (EM : WR_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
Qed.
Lemma pk_drain_c5 : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  pose proof (pk_drain_c5_slack cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP) as H.
  pose proof (tr_max_nonneg'
    (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)). lia.
Qed.
(* the five room conjuncts at LS := fr_LS3 (the row's meter conjunct is ReplyLSI.v's, from its fr_SEC) *)
Lemma pk_drain_pre : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    < CfParamsReply.fr_MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP.
  destruct (fr_LS3_drain_pre_c1236 B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof) as (C1 & C2 & C3 & _).
  pose proof (fr_LS3_drain_pre_c4 B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU) as C4.
  pose proof (pk_drain_c5 cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU HXP) as C5.
  rewrite pk_fr_MMAX.
  exact (conj C1 (conj C2 (conj C3 (conj C4 C5)))).
Qed.

(* ---------------------------------------------------------------- (2) LS_rm_rr_pre *)
(* conjunct 3 in its slack form: ReplyTrPeak.v fr_LS_rm_rr_pre_c3p_slack at fr_LS3 (pk_rr_tr_max in place of
   fr_LS_rm_rr_pre_c2, fr_LS3_room_x in place of dr3_room_S) *)
Lemma pk_rr_c3_slack : forall cx t m ly S si h j0,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) +
    tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Ht HU Hpos.
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as HM.
  pose proof (fr_LS3_room_x B cx t m ly S HLS) as Hroom.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct HE as (_ & _ & _ & _ & Hsk).
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  destruct (tp_pos_entry (rm_ent m j0) (fun b Hb => Hpos b (rm3_in_model_entry m j0 b Hj0 Hb))) as [Hrc Hka].
  assert (Hcap : 0 <= lm_cap m).
  { apply (tp_pos_out (lm_cap m) (lm_out m)). intros b Hb. exact (Hpos b (rm3_in_model_out m b Hb)). }
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HJ : re_eof (rm_ent m j0) = 0 -> hs_overlong h = 1 \/ bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
  { intros Eo. destruct (Hre Eo) as (S1 & W1).
    destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia. }
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr in *.
  replace (Z.of_nat (length (lm_O m))) with 0 in HM by (rewrite HO; reflexivity).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  pose proof (tp_rr (lm_c m) (lm_mx m) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hfind Hcap Hrc Hka
                (proj1 Hec') Hoff Hexp HU HJ) as TR.
  pose proof (tr_peak_le_pos (rr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (hs_fd h) (lm_es m) h)) as PK.
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  pose proof (RelayCap.keys_total_nonneg (re_keys (rm_ent m j0))) as HKT.
  assert (HX : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold SlotInv.WRITE_MAX, OPS_MAX, pk_TXM in *. lia.
Qed.
Lemma pk_rr_c3 : forall cx t m ly S si h j0,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 HLS HRI Hat Ht HU Hpos.
  pose proof (pk_rr_c3_slack cx t m ly S si h j0 HLS HRI Hat Ht HU Hpos) as H.
  pose proof (tr_max_nonneg' (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)). lia.
Qed.
(* conjunct 6: the pending credit (pk_room_pend, P <= pend_bytes by HSRC), pk_rr_tr_max, and lm_cap <= 2^29 from
   HCAP0 (ReplyLS3eCap.ls3e_cap_lt_MMAX) *)
Lemma pk_rr_c6 : forall cx t m ly S si h j0,
  fr_LS3c B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> fr_ENT B cx m ly S ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) +
    4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 HLS HOU HE HRI Hat Ht HU Hpos Hsrc HCAP0.
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as HM.
  pose proof (pk_room_pend cx t m ly S (proj1 HLS)) as Hroom.
  destruct (ls3e_cap_lt_MMAX B cx t m ly S HLS HOU HE HCAP0) as (_ & Hcap29 & _).
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE' & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & Hsi & Hh & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff). cbn [fst snd] in Hre, Hexp, Hec, Hpe, Hoff.
  destruct HE' as (_ & _ & _ & _ & Hsk).
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  destruct (tp_pos_entry (rm_ent m j0) (fun b Hb => Hpos b (rm3_in_model_entry m j0 b Hj0 Hb))) as [Hrc Hka].
  assert (Hcap : 0 <= lm_cap m).
  { apply (tp_pos_out (lm_cap m) (lm_out m)). intros b Hb. exact (Hpos b (rm3_in_model_out m b Hb)). }
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HJ : re_eof (rm_ent m j0) = 0 -> hs_overlong h = 1 \/ bzs (re_U (rm_ent m j0)) = bzs (hs_W h)).
  { intros Eo. destruct (Hre Eo) as (S1 & W1).
    destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia. }
  assert (HPS : Z.of_nat (length (pending_stream h)) <= pend_bytes m).
  { rewrite (ls3_ps_sp h Hsrc). apply pend_bytes_in. rewrite <- Hh. apply nth_In.
    pose proof HRI as (_ & (Hl4 & _) & _). lia. }
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr in *.
  replace (Z.of_nat (length (lm_O m))) with 0 in HM by (rewrite HO; reflexivity).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  pose proof (tp_rr (lm_c m) (lm_mx m) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hfind Hcap Hrc Hka
                (proj1 Hec') Hoff Hexp HU HJ) as TR.
  pose proof (tr_peak_le_pos (rr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (hs_fd h) (lm_es m) h)) as PK.
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  pose proof (RelayCap.keys_total_nonneg (re_keys (rm_ent m j0))) as HKT.
  assert (HX : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  unfold pk_TXM, W_P in *. lia.
Qed.
(* the five room conjuncts at LS := fr_LS3c /\ fr_OUT OUT_MAX4 /\ fr_ENT (the meter conjunct is ReplyLSI.v's) *)
Lemma pk_rm_rr_pre : forall cx t m ly S si h j0,
  (fr_LS3c B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ fr_ENT B cx m ly S) ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  (re_eof (rm_ent m j0) = 0 ->
     Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\
     re_nheld (rm_ent m j0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26) /\
  tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) +
    4 * Z.max (lm_cap m) (tr_max (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h)) <= LIVE_MAX.
Proof.
  intros cx t m ly S si h j0 (HLS & HOU & HE) HRI Hat Ht HU Hpos Hsrc HCAP0.
  destruct (fr_LS3_rm_rr_pre_sizes B cx t m ly S si h j0 (proj1 HLS) HRI Hat) as (C1 & _).
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as C2.
  pose proof (pk_rr_c3 cx t m ly S si h j0 (proj1 HLS) HRI Hat Ht HU Hpos) as C3.
  destruct (ls3e_cap_lt_MMAX B cx t m ly S HLS HOU HE HCAP0) as (_ & _ & C5).
  pose proof (pk_rr_c6 cx t m ly S si h j0 HLS HOU HE HRI Hat Ht HU Hpos Hsrc HCAP0) as C6.
  rewrite pk_fr_MMAX.
  refine (conj C1 (conj _ (conj C3 (conj C5 C6)))).
  rewrite pk_WR_MMAX. unfold pk_TXM in C2. lia.
Qed.

(* ---------------------------------------------------------------- (3) GN_LS_rig *)
(* R5: the pending credit over the open pairs (every slot's HSRC; the pairs' slots are distinct), pk_rig's request
   bound, and lm_cap <= 2^29 from HCAP0 *)
Lemma pk_rig_r5 : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> fr_ENT B cx m ly S ->
  fr_RINV cx t m -> gn_pairs m hs ->
  gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) +
    4 * Z.max (lm_cap m)
          (tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs))
    <= LIVE_MAX.
Proof.
  intros cx t m ly S hs HLS HOU HE HRI HP Hop HUs Hpos Hsrc HCAP0.
  destruct Hop as (_ & HO & Ht & _).
  pose proof (pk_room_pend cx t m ly S (proj1 HLS)) as Hroom.
  destruct (ls3e_cap_lt_MMAX B cx t m ly S HLS HOU HE HCAP0) as (_ & Hcap29 & _).
  destruct (grg_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & H4).
  pose proof (pk_pairs8 cx t m hs HRI HP Ht HUs) as HF8.
  pose proof HP as (HLhs & HFa & HND).
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (HFp : Forall grg_okp (combine (lm_es m) hs)).
  { apply Forall_forall. intros p Hp. split; [exact (proj1 (Forall_forall _ _) HF p Hp)|].
    apply (grg_pos_entry m (fst p)); [|exact Hpos].
    destruct p as [e q]. cbn [fst]. exact (in_combine_l _ _ _ _ Hp). }
  assert (Hcap : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    apply (Hpos (lm_out m, lm_cap m)). unfold model_blks. right. apply in_or_app. right. apply in_or_app. right.
    unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity. }
  assert (HND' : List.NoDup (rig_slots (combine (lm_es m) hs))).
  { first [exact (proj1 (NoDup_ListNoDup _) HND) | exact HND]. }
  pose proof (pk_gp_le_pend m (combine (lm_es m) hs) Hl4 HFa HND' Hsrc) as HZp.
  pose proof (pk_sum_cost (combine (lm_es m) hs) HF) as HZc.
  pose proof (pk_sum_pc (combine (lm_es m) hs)) as HZpc.
  pose proof (pk_sum_k (combine (lm_es m) hs)) as HZk.
  pose proof (zsum_map_nonneg pk_gp (combine (lm_es m) hs) pk_gp_nonneg) as HZp0.
  pose proof (zsum_map_nonneg pk_gk (combine (lm_es m) hs) pk_gk_nonneg) as HZk0.
  rewrite length_combine, HLhs, Nat.min_id in HZc, HZpc.
  assert (HL : Z.of_nat (length (lm_es m)) <= 4) by lia.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  rewrite HO. cbn [length Z.of_nat].
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr. cbv zeta.
  match goal with |- context [tr_peak (fst (fst (fst (relay_instance_gone_b_c.gone_run
                                ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9))))] =>
    pose proof (grg_run_pos a6 a1 a2 a5 a7 a3 a4 a8 a9 HFp Hcap) as POS;
    pose proof (tr_peak_le_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))))
      as PK;
    pose proof (dpre_tr_max (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) pk_TXM
                  ltac:(unfold pk_TXM; lia)
                  (pk_run_rq8 a6 a1 a2 a5 a7 a3 a4 a8 a9 pk_TXM (c_n cx) HF8 HC
                     ltac:(unfold pk_TXM; lia) ltac:(unfold pk_TXM; lia)
                     ltac:(unfold pk_TXM; lia) ltac:(unfold pk_TXM; lia))) as TM;
    set (T := fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) in *
  end.
  set (Zc := zsum (map grg_cost (combine (lm_es m) hs))) in *.
  set (Zpc := zsum (map grg_pc (combine (lm_es m) hs))) in *.
  set (Zp := zsum (map pk_gp (combine (lm_es m) hs))) in *.
  set (Zk := zsum (map pk_gk (combine (lm_es m) hs))) in *.
  clearbody T Zc Zpc Zp Zk.
  clear - Hroom Hcap29 HC Hn Hcap HZp HZc HZpc HZk HZp0 HZk0 HL POS PK TM.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (E29 : 2 ^ 29 = 536870912) by reflexivity.
  unfold pk_TXM, W_P in *. lia.
Qed.
(* the four room conjuncts at LS := fr_LS3c /\ fr_OUT OUT_MAX4 /\ fr_ENT, MMAX := fr_MMAX (GN_LS_rig's meter conjunct
   is ReplyLSI.v's, from its fr_SEC) *)
Lemma pk_gone_rig : forall cx t m ly S hs,
  (fr_LS3c B cx t m ly S /\ fr_OUT OUT_MAX4 cx t m ly S /\ fr_ENT B cx m ly S) ->
  fr_RINV cx t m -> gn_pairs m hs ->
  gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (gn_id cx m) (lm_es m) hs in
  tr_max tr < CfParamsReply.fr_MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\
  lm_cap m < CfParamsReply.fr_MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
Proof.
  intros cx t m ly S hs (HLS & HOU & HE) HRI HP Hop HUs Hpos Hsrc HCAP0 tr.
  pose proof Hop as (_ & HO & Ht & _).
  pose proof (fr_LS3c_gone_rig_c1 B cx t m ly S hs HLS HRI HP HO Ht HUs) as R1.
  pose proof (fr_LS3c_gone_rig_c2p B cx t m ly S hs HLS HRI HP HO Ht HUs Hpos) as R2.
  destruct (ls3e_cap_lt_MMAX B cx t m ly S HLS HOU HE HCAP0) as (_ & _ & R4).
  pose proof (pk_rig_r5 cx t m ly S hs HLS HOU HE HRI HP Hop HUs Hpos Hsrc HCAP0) as R5.
  rewrite pk_fr_MMAX. unfold tr.
  refine (conj R1 (conj _ (conj R4 R5))). lia.
Qed.
End inst.
