(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: group RI-gone of the image-A top (W_LLVMFuzzerTestOneInput_top_x.v, the rows
   RI_gone_pairs / RI_gone_read / RI_gone_step / RI_gone_end) at RINV := fr_RINV (ReplyRINV.v).  Proves no function
   walk (model-rule obligations only).
   Part 1 (over ReplyRINV.v's copies of the gone model, verbatim the same text as gone_base.v's):
   - RI_gone_pairs_holds: fr_RINV's pairing hj of the table with the open sources is a gn_pairs witness.  The size
     bounds gn_pair_ok asks come from fr_RINV's cost bound (fr_cost <= c_n < 2 ^ 26: a pending stream and a key count
     are parts of one entry's cost) and from fr_pair_ok's ecap_ok.
   - RI_gone_read_holds: a slot k that reads (gn_reads m k = 1) holds the source of an open entry j; that entry's
     gn_pair_ok source is at slot k (fr_RINV's distinct fds, RI_fds_holds), so after relay_instance_gone slot k holds
     rig_post's source for entry j, which rig_rel's dr_rel leaves drained (pending list empty, offset 0).
   - RI_gone_read_sat: one state meets all of RI_gone_read's premises (and RI_gone_pairs's).
   - Section collapse / collapse2: the records of rounds 1 and 2 of the gone rules' texts (bb9dae5d905, a1a3591c77c),
     which were false at the instance; machine-checked counter-instances, not proofs of the rows.
   Part 2 (over W_LLVMFuzzerTestOneInput_gone_base.v's own model): RI_gone_pairs_plug / RI_gone_read_plug restate
   part 1 at gone_base's GN_RI_pairs / GN_RI_read; then the step and end rows.
   - The table-order loop (gn_run) as an invariant (rg_inv): every entry's slot, once processed, holds what
     check_no_loss and check_shape_ends left of what relay_instance_gone left there; when gone = 0, `at` is the
     entry's position in the stream relay_instance_gone sent (rg_acc_pos), which is the entries' drained lines and
     then their ended keys' end lines (rg_rel_dec, rg_strm).
   - RI_gone_step_holds(_c): GN_RI_step of a working branch a39b599f92e (copied verbatim as
     GN_RI_step_d) at MT := ameter_triv, RINV := fr_RINV, MMAX := WR_MMAX, LS := fr_LS3 B / fr_LS3c B.  The LS-side
     conjunct cnl_room is a Theorem Labs lane's gx6_step_room(_c) (ReplyLS3cTopxGoneF.v at b25d82fcf04); mo_ok is True at
     ameter_triv; the rest is RINV-side (rg_step_rinv_side).
   - RI_gone_end_holds_q5(_c): GN_RI_end of a39b599f92e (copied as GN_RI_end_q5) with REQ5 (no held list's capacity
     shrinks from m to mc) as one more, last, premise: s5-r1d's gx6_end_LS3(_c) needs it, and a39b599f92e's gn_cnl_ok
     does not carry `hl_cap (hs_held h) <= hl_cap H'` from which ReplyLS3cTopxGoneH.v's gxh_req5 derives it.
   - GN_RI_step_r3 (Section rg3): the record of round 3 (aa34c06e82c): without re_U NUL-free the step row is false.
   Local helpers rg_lines_nz / rg_upds_in / rg_W_read_lines_nz state what a Theorem Labs lane's ReplyRINV_a12.v
   (lines_nul_free / upds_nul_free) states; they stay local. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths changed; 472 of its 575 lines of code are new or changed and 2820 lines of the source are left out. *)
(* fr_CAP: g_capout's model value stays within the entry contract's CAPOUT_MAX at every cut, and the exit's two LS
   rules at the top's instance.  proves no function (kind: invariant lemma).

   WHY fr_CAP (a Theorem Labs lane's ruling (A), 2026-10-30 05:40Z).  RiRestate's LS_exit_cap (a working branch
   5a9b16eac9e, W_LLVMFuzzerTestOneInput_exit_x.v:196-198 and _exit.v:7785-7787) needs lm_cap m <= CAPOUT_MAX
   (ou_rf_cap: relay_finish never lowers g_capout).  Over fr_LS3cp B /\ fr_OUT OM /\ fr_ENT B nothing bounds lm_cap m
   by a constant: fr_OUT gives lm_cap m <= XB + OM, and under fr_ENT XB is the ENTRY's harness bytes, which hold the
   entry's g_capout (ReplyLS3eCap.v ent_XB), bounded only by fr_LS3's blocks_bytes (c_S cx) + CALL_ROOM <= LIVE_MAX.
   ReplyLScapCex.v's LS_exit_cap_false_at_LSI is the counterexample (t = 0, entry g_capout = 2^32).  So the top's
   LS instance takes one more conjunct, LAST (agreed with a Theorem Labs lane, whose lib/A/ReplyLSI.v Requires this file):
     LSI cx t m ly S := fr_LS3cp B cx t m ly S /\ fr_OUT OM cx t m ly S /\ fr_ENT B cx m ly S /\ fr_CAP cx t m ly S.

   WHY IT IS KEPT.  The first head takes it from the entry contract's signed CAPOUT clause (_cut.v:213 / _cut_x.v:109,
   the pre's last conjunct `exists c, val_mem segs (arm W mem) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX`): the
   entry's g_out block (out, cap) is one of its harness blocks fr_hblks, whose sizes are ATABLE or the rdword read of
   g_capout, which that clause bounds (fr_CAP_pro: ReplyLSI.v's slot states top_x's LS_pro text at LSx := fr_CAP, whose
   lf_base_x is cut_x's, the pre ending with that clause).  A rule that does not send
   keeps lm_cap (fr_CAP_keep).  A rule that sends grows g_capout to at most twice what one operation sends
   (send_line's growth), which s5-r1d's fr_OUT proofs bound by the model's mass (drain 2 * MASS m, remove and gone
   4 * MASS m, event 2 * 65,536), and fr_OUT's MASS m <= WMAX * t with the rule's own t < OPS_MAX (rm_step's
   premise, gone's gn_op) makes 4 * WMAX * t <= 4 * 65,535 * 511 = CAPOUT_MAX (tight); drain needs only t <= OPS_MAX.  Each keep lemma fr_CAP_<rule> takes fr_OUT's twin's premises in the same order
   (ReplyLS3o.v, ReplyLS3oGn.v) with fr_CAP at the rule's pre inserted right after fr_OUT, and replays the twin's
   proof up to its capacity bound (marked "replayed from"). *)
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
  ReplyLS3cTopxGone ReplyLS3cTopxGoneF ReplyLS3cTopxGoneH ReplyLS3cTopx ReplyLS3cTopxPost ReplyLS3cTopxPro
  ReplyLS3cTopxGone8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLS3eCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3w ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation MT := ameter_triv.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== the conjunct *)
Section cap.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition fr_CAP (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop := 0 <= lm_cap m <= CAPOUT_MAX.

Lemma CAPOUT_MAX_eq : CAPOUT_MAX = OUT_MAX4.
Proof. reflexivity. Qed.
Lemma CAPOUT_MAX_4WMAX : forall t, 0 <= t < OPS_MAX -> 4 * (WMAX * t) <= CAPOUT_MAX.
Proof. intros t Ht. unfold CAPOUT_MAX, WMAX, OPS_MAX in *. lia. Qed.
Lemma CAPOUT_MAX_2WMAX : forall t, 0 <= t <= OPS_MAX -> 2 * (WMAX * t) <= CAPOUT_MAX.
Proof. intros t Ht. unfold CAPOUT_MAX, WMAX, OPS_MAX in *. lia. Qed.

(* a rule that does not touch g_capout *)
Lemma fr_CAP_keep : forall cx t t' m m' ly S ly' S',
  lm_cap m' = lm_cap m -> fr_CAP cx t m ly S -> fr_CAP cx t' m' ly' S'.
Proof. intros cx t t' m m' ly S ly' S' E H. unfold fr_CAP in *. rewrite E. exact H. Qed.

(* a rule that grows g_capout to at most k * MASS m, with k * WMAX * t <= CAPOUT_MAX *)
Lemma fr_CAP_of_mass : forall k cx t t' m m' ly S ly' S',
  0 <= k -> 0 <= MASS m -> MASS m <= WMAX * t -> k * (WMAX * t) <= CAPOUT_MAX ->
  0 <= lm_cap m' -> lm_cap m' <= Z.max (lm_cap m) (k * MASS m) ->
  fr_CAP cx t m ly S -> fr_CAP cx t' m' ly' S'.
Proof.
  intros k cx t t' m m' ly S ly' S' Hk Hm0 Hm Hkt H0 Hle (C1 & C2). unfold fr_CAP.
  assert (k * MASS m <= k * (WMAX * t)) by (apply Z.mul_le_mono_nonneg_l; lia).
  split; [exact H0|]. apply (Z.le_trans _ _ _ Hle). apply Z.max_lub; lia.
Qed.

(* ReplyLSI.v's slot fr_CAP_sat (`fr_CAP lsi_cx 0 (ls3_m B) ls3_ly ls3_S`, ReplyLSI.v:783 at ce7d0d0bf8c): fr_CAP reads
   only the model's capacity, and ls3_m's (ReplyLS3.v:485, the first head's) is 0; plug it as
   `fr_CAP_sat_at B lsi_cx ls3_ly ls3_S` (lsi_cx is ReplyLSI.v's, which Requires this file) *)
Lemma fr_CAP_sat_at : forall B cx ly S, fr_CAP cx 0 (ls3_m B) ly S.
Proof.
  intros B cx ly S. unfold fr_CAP.
  assert (EC : lm_cap (ls3_m B) = 0) by reflexivity. rewrite EC. unfold CAPOUT_MAX, OPS_MAX. lia.
Qed.
End cap.

(* ================================================================== the keep rules *)
Section keep.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable OM : Z.
Hypothesis HOM : OUT_MAX4 <= OM.

(* ---- the rules of ReplyLS3c.v that keep the model's capacity (fr_OUT_head_nout .. fr_OUT_add_none) ---- *)
Lemma fr_CAP_head_nout_r : forall cx t m ly S, fr_CAP cx t m ly S -> fr_CAP cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_head_skip_r : forall cx t m ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof. intros cx t m ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_close_r : forall cx t m i ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_close cx m i) ly S.
Proof. intros cx t m i ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_eintr_r : forall cx t m i ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_eintr cx m i) ly S.
Proof. intros cx t m i ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_sendmax_r : forall cx t m u ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_sendmax cx m u) ly S.
Proof. intros cx t m u ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_default_r : forall cx t m g ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_default cx m g) ly S.
Proof. intros cx t m g ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_write_skip_r : forall cx t m ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof. intros cx t m ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_add_none_r : forall cx t m ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_drain_skip_r : forall cx t m ly S, fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof. intros cx t m ly S. apply fr_CAP_keep. reflexivity. Qed.

(* ---- op_add's open and the write arm's push keep g_capout (fr_OUT_add_open's / fr_OUT_write_push's EC) ---- *)
Lemma fr_CAP_add_open_r : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 B cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof. intros cx t m i q pj ev ly S ly' S' _ _ _ _. apply fr_CAP_keep. reflexivity. Qed.
Lemma fr_CAP_write_push_r : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3 B cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S ->
  fr_CAP cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof. intros cx t m si h l' d ly S ly' S' ev _ _ _ _ _ _ _ _. apply fr_CAP_keep. reflexivity. Qed.

(* ---- the drain arm's step (fr_OUT_drain_step_p, ReplyLS3o.v:519): g_capout <= max (lm_cap m) (2 * MASS m) ---- *)
Lemma fr_CAP_drain_step_r : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> fr_RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= cap' -> 0 <= t < OPS_MAX ->
  fr_CAP cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' HLS (U1 & U2 & U3 & U4) HCAP Hpick Hj
    (rest_d & HPd1 & HPd2) Hpend HEq HHq Hcnl Hh'' Hat HRI Hfd Heof Hepre Hkh Hhpre Hhn Hcap0 Hcap'
    Hepost Hhpost Hdpost Hcpost Hcapn Ht.
  subst E H h''.
  pose proof Hpick as (_ & Hsi & Hh).
  destruct Hat as (Hk & HO & _).
  set (e := nth j (lm_es m) dr_e0) in *.
  set (m' := dr_step m (dr_k' cx m) si (set_exp_held h1 E' H') j e' c' O' cap' out') in *.
  destruct Hdpost as (HU' & Hka' & Hoff1 & Hmap & Hheld & HnE1).
  replace (Z.of_nat (length (lm_O m))) with 0 in Hcap', HU', Hka' by (rewrite HO; reflexivity).
  unfold dr_fin in HU', Hka'. fold e in HU', Hka'.
  (* replayed from fr_OUT_drain_step_p: what the drain sends is within the pair's mass *)
  destruct (dr3_rinv cx t m si h j HRI Hpick Hj Hfd Heof)
    as ((Hsk & HskU) & Hsk01 & _ & _ & Hexp & _ & _ & _ & Hoff & _).
  destruct Hepre as (Hce & HU & HUz & Hkh8 & H14).
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))) in *.
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live (lm_c m) h) (lm_mx m) 0 (lm_cap m) e h HJ
                (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Hno.
  change (lines (hs_state h) (bzs (pending_stream h))) with Ls in Hno. fold TOT in Hno.
  destruct (ls3_drain_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) e h (proj1 Hhpre) Hkh168) as (RM & RK).
  rewrite <- HU' in RM. rewrite SlotReads.bzs_length in RM.
  assert (HMASS : TOT + Z.of_nat (length (re_U e')) <=
                  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h))) by lia.
  assert (He_in : In e (lm_es m)) by (unfold e; apply nth_In; exact Hj).
  assert (Hh_in : In (Some h) (lm_hs m)) by (rewrite <- Hh; apply nth_In; exact (rm3_nth_lt _ _ _ Hh)).
  pose proof (MASSe_in (lm_es m) e He_in) as Hem.
  pose proof (pend_bytes_in m (Some h) Hh_in) as Hpm.
  assert (HPS : Z.of_nat (length (pending_stream h)) = slot_pend (Some h)) by exact (ls3_ps_sp h (proj1 Hhpre)).
  pose proof (kw7s_nonneg (drain_b_c.keys_texts (re_keys e))) as Hkw0.
  assert (HUm : Z.of_nat (length (re_U e)) <= ent_mass e) by (unfold ent_mass; lia).
  assert (HTOTm : 2 * TOT <= 2 * MASS m).
  { unfold MASS. pose proof (MASSe_nonneg (lm_es m)). lia. }
  assert (Hcapb : cap' <= Z.max (lm_cap m) (2 * MASS m)).
  { pose proof (dr3_ocap (lm_c m) (lm_mx m) (lm_cap m) e h HJ (dr3_pok 0 (lm_cap m) e h Hoff Hhpre) Hce0) as Ho.
    fold Ls in Ho. fold TOT in Ho.
    rewrite Hcap'. destruct (dr_live (lm_c m) h); lia. }
  (* the conjunct *)
  assert (ECap : lm_cap m' = cap') by reflexivity.
  apply (fr_CAP_of_mass 2 cx t (t + 1) m m' ly S ly' S'); try lia.
  all: first [exact HCAP | apply MASS_nonneg | (apply CAPOUT_MAX_2WMAX; lia) | (apply CAPOUT_MAX_4WMAX; lia) | lia].
Qed.

(* ---- the remove arm's step (fr_OUT_rm_step_p, ReplyLS3o.v:728): g_capout <= max (lm_cap m) (4 * MASS m) ---- *)
Lemma fr_CAP_rm_step_r : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS3 B cx t m ly0 S0 -> fr_OUT OM cx t m ly0 S0 -> fr_CAP cx t m ly0 S0 ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= cap2 -> 0 <= t < OPS_MAX ->
  fr_CAP cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 H1 (U1 & U2 & U3 & U4) HCAP
    HRI Hat Hrr Hcn Hcs Hfr Hpos H14 Hoffc Hcapn Ht.
  pose proof Hat as (_ & _ & _ & _ & Hsi & Hh & Hj0 & _).
  (* replayed from fr_OUT_rm_step_p *)
  pose proof (ou_rm_cap2 cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr) as Hc2.
  assert (He_in : In (rm_ent m j0) (lm_es m)) by (unfold rm_ent; apply nth_In; exact Hj0).
  assert (Hh_in : In (Some h) (lm_hs m)) by (rewrite <- Hh; apply nth_In; exact (rm3_nth_lt _ _ _ Hh)).
  pose proof (MASSe_in (lm_es m) _ He_in) as Hem.
  pose proof (pend_bytes_in m (Some h) Hh_in) as Hpm.
  assert (HPS : Z.of_nat (length (pending_stream h)) = slot_pend (Some h)) by exact (ls3_ps_sp h Hoffc).
  assert (Hmass_nn : 0 <= MASS m) by (apply MASS_nonneg).
  assert (Hc2' : cap2 <= Z.max (lm_cap m) (4 * MASS m)) by (unfold MASS in *; lia).
  assert (ECap : lm_cap (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) = cap2) by reflexivity.
  apply (fr_CAP_of_mass 4 cx t (t + 1) m _ ly0 S0 ly S); try lia.
  all: first [exact HCAP | apply MASS_nonneg | (apply CAPOUT_MAX_2WMAX; lia) | (apply CAPOUT_MAX_4WMAX; lia) | lia].
Qed.

(* ---- the event arm's step (fr_OUT_event_step_p, ReplyLS3o.v:781): g_capout <= max (lm_cap m) (2 * 65,536) ---- *)
Lemma fr_CAP_event_step_r : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3 B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> ev_evt cx m e ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_CAP cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HLS _ (C1 & C2) HE Hk HO Hc0 Hm HRR Hf.
  set (cap' := sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in *.
  assert (ECap : lm_cap (ev_step cx m e v out') = cap') by reflexivity.
  (* replayed from fr_OUT_event_step_p *)
  assert (Hcge : lm_cap m <= cap').
  { unfold cap', sl_cap.
    exact (proj2 (tp_send_line (sl_live (lm_c m) (re_len e)) (lm_mx m) (Z.of_nat (length (lm_O m)))
                   (lm_cap m) (re_len e) 0 RelayRunF.adr0 Hc0)). }
  assert (HO0 : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  assert (Hcle : cap' <= Z.max (lm_cap m) (2 * 65536)).
  { pose proof (ev3_cap_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as Hle.
    pose proof (ou_ev_len cx m e HE) as Hlen. unfold cap'. lia. }
  unfold fr_CAP. rewrite ECap. split; [lia|].
  apply (Z.le_trans _ _ _ Hcle). apply Z.max_lub; [lia | unfold CAPOUT_MAX, OPS_MAX; lia].
Qed.

(* ---- the gone arm (fr_OUT_gone_end, ReplyLS3oGn.v:265): g_capout <= max (lm_cap m) (2 * |O2|), |O2| <= 2 * MASS m ---- *)
Lemma fr_CAP_gone_end_r : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate),
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (* REQ1 *) 0 <= lm_cap m ->
  (* REQ2 *)
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  (* REQ3 *)
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3 B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  fr_CAP cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx HRI Hop HE Hcap HE6 HS6 HLS (U1 & U2 & U3 & U4) HCAP
    Hpairs Hafter Hrok Hrun Hfr.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hpairs) as HX.
  pose proof (gx_pf_all cx t m hs HRI Hpairs HX) as HPF.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof HX as (HO & _ & _).
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & Hfds).
  pose proof HRI as (_ & (Hl4 & _) & _).
  pose proof Hop as (_ & _ & Ht & _).
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  (* the run: what it sends, the mass it leaves, and g_capout *)
  destruct (ou_rig _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 Hrr HPF U1) as (R1 & R2 & R3).
  destruct (gx_rig _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 (lm_cap m) Hrr (gx_pre_len _) HPF
              ltac:(lia)) as (_ & R4).
  rewrite HO in R1. cbn [length Z.of_nat] in R1.
  (* the loop keeps the table, g_capout and every slot's pending bytes *)
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R5 & R6 & _ & _ & _ & R7 & Hhist & _).
  assert (Hpm1 : pend_bytes mc = pend_bytes m1).
  { unfold pend_bytes. rewrite (gx_sum4 slot_pend (lm_hs mc) ltac:(lia)), (gx_sum4 slot_pend (lm_hs m1) A11).
    assert (Hk : forall k', slot_pend (nth k' (lm_hs mc) None) = slot_pend (nth k' (lm_hs m1) None)).
    { intros k'. destruct (Hhist k') as [L | (h0 & h2 & i0 & X1 & X2 & X3 & _)]; [rewrite L; reflexivity|].
      rewrite X1, X2.
      destruct X3 as (h' & E' & H' & P & g & A0 & ob & ds & c & (E1 & _) & (H'' & E2 & _)).
      subst. reflexivity. }
    rewrite !Hk. reflexivity. }
  (* relay_instance_gone empties the pending lists of the slots it drains and keeps the others *)
  assert (HALL : Forall (fun pq => re_eof (fst (fst pq)) = 0 ->
            nth (snd (snd (fst pq))) (lm_hs m) None = Some (fst (snd (fst pq))) /\
            nth (snd (snd (fst pq))) (lm_hs m1) None = Some (snd (snd pq)) /\
            slot_pend (Some (fst (snd (fst pq)))) = Z.of_nat (length (pending_stream (fst (snd (fst pq))))) /\
            slot_pend (Some (snd (snd pq))) = 0) (combine ps qs)).
  { rewrite Forall_forall in HPQ, HRP, HPF |- *. intros [p q] Hin Heof. cbn [fst snd] in Heof |- *.
    destruct (HPQ (p, q) Hin Heof) as (_ & Q2 & Q3). cbn [fst snd] in Q2, Q3.
    destruct (HRP (p, q) Hin) as (_ & Hdr). cbn [fst snd] in Hdr.
    destruct (Hdr Heof) as (c' & mx' & no & cap' & e1 & LB & D).
    destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ D) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Dp & Do & _).
    pose proof (HPF p (in_combine_l _ _ _ _ Hin) Heof) as Hpf.
    destruct Hpf as (_ & _ & _ & _ & _ & _ & _ & _ & Hhpre & _).
    split; [exact Q2|]. split; [exact Q3|]. split.
    - symmetry. exact (ls3_ps_sp _ (proj1 Hhpre)).
    - cbn [slot_pend]. unfold hl_bytes. rewrite Dp, Do. reflexivity. }
  set (F := fun j => slot_pend (nth j (lm_hs m1) None) - slot_pend (nth j (lm_hs m) None)).
  assert (S1 : pend_bytes m1 - pend_bytes m = F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { unfold pend_bytes, F. rewrite (gx_sum4 slot_pend (lm_hs m1) A11), (gx_sum4 slot_pend (lm_hs m) Hl4). lia. }
  assert (S2 : F 0%nat + F 1%nat + F 2%nat + F 3%nat = zsum (map F (rig_slots ps))).
  { apply gx_sum_RS.
    - apply NoDup_ListNoDup. exact HRS.
    - intros j Hj. destruct (gx_rs_in j ps Hj) as (p & Hp & Heof & <-).
      rewrite Forall_forall in HPok. destruct (HPok p Hp Heof) as (Hj4 & _). exact Hj4.
    - intros j Hj Hn. unfold F. rewrite (A12 j Hj Hn). lia. }
  rewrite gx_rs_sum in S2.
  rewrite (gx_sum_cfst (fun p => if re_eof (fst p) =? 0 then F (snd (snd p)) else 0) ps qs Hlps) in S2.
  cbv beta in S2.
  assert (S3 : zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then F (snd (snd (fst pq))) else 0)
                     (combine ps qs)) =
               zsum (map (fun pq => - ou_ps (fst pq)) (combine ps qs))).
  { apply (gx_sum_ext _ _ _ _ HALL). intros [p q] Hpq. cbn [fst snd] in Hpq |- *. unfold ou_ps.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (Hm & Hm1 & P1 & P2).
    unfold F. rewrite Hm, Hm1, P1, P2. lia. }
  rewrite ou_zsum_opp, <- (gx_sum_cfst ou_ps ps qs Hlps) in S3.
  (* the mass: the old entries' and the drained sources', against the new entries' *)
  assert (EPM : zsum (map ou_pm ps) = MASSe (lm_es m) + zsum (map ou_ps ps)).
  { unfold ou_pm, MASSe. rewrite (gx_zsum_add (fun p => ent_mass (fst p)) ou_ps ps).
    rewrite (gx_sum_cfst ent_mass (lm_es m) hs ltac:(lia)). reflexivity. }
  assert (EMq : MASSe (lm_es mc) = zsum (map (fun q => ent_mass (fst q)) qs))
    by (unfold MASSe; rewrite R5, A3, map_map; reflexivity).
  assert (Hp1 : 0 <= pend_bytes m1) by (apply zsum_map_nonneg; exact slot_pend_nonneg).
  assert (HMm : MASS m = MASSe (lm_es m) + pend_bytes m) by reflexivity.
  assert (HMc : MASS mc = MASSe (lm_es mc) + pend_bytes mc) by reflexivity.
  assert (HMASS : MASS mc <= MASS m) by lia.
  assert (HOUT : Z.of_nat (length O2) <= 2 * MASS m) by lia.
  (* the conjunct (replayed from fr_OUT_gone_end above this line) *)
  assert (ECap : lm_cap mc = cap2) by (rewrite R6; exact A7).
  apply (fr_CAP_of_mass 4 cx t (t + 1) m mc ly S lyx Sx); try lia.
  all: first [exact HCAP | apply MASS_nonneg | (apply CAPOUT_MAX_2WMAX; lia) | (apply CAPOUT_MAX_4WMAX; lia) | lia].
Qed.

(* ================================================================== the slots of a Theorem Labs lane's ReplyLSI.v
   Each statement below is ReplyLSI.v's `Hypothesis fr_CAP_<rule>` (a working branch 1318828167d,
   lib/A/ReplyLSI.v:248-350) word for word, at this file's fr_CAP, so ReplyLSI.v swaps its slots for these lemmas. *)
Lemma fr_CAP_head_nout : forall cx t m ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx t (lm_clear_O m) ly S.
Proof.
  intros cx t m ly S _. exact (fr_CAP_head_nout_r cx t m ly S).
Qed.
Lemma fr_CAP_head_skip : forall cx t m ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (lm_set_k m (hd_k' cx m)) ly S.
Proof.
  intros cx t m ly S _. exact (fr_CAP_head_skip_r cx t m ly S).
Qed.
Lemma fr_CAP_close : forall cx t m i ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S _. exact (fr_CAP_close_r cx t m i ly S).
Qed.
Lemma fr_CAP_eintr : forall cx t m i ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S _. exact (fr_CAP_eintr_r cx t m i ly S).
Qed.
Lemma fr_CAP_sendmax : forall cx t m u ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_sendmax cx m u) ly S.
Proof.
  intros cx t m u ly S _. exact (fr_CAP_sendmax_r cx t m u ly S).
Qed.
Lemma fr_CAP_default : forall cx t m g ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (sm_default cx m g) ly S.
Proof.
  intros cx t m g ly S _. exact (fr_CAP_default_r cx t m g ly S).
Qed.
Lemma fr_CAP_write_skip : forall cx t m ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (wr_skip m (wr_k2 cx m)) ly S.
Proof.
  intros cx t m ly S _. exact (fr_CAP_write_skip_r cx t m ly S).
Qed.
Lemma fr_CAP_add_none : forall cx t m ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (ad_none m) ly S.
Proof.
  intros cx t m ly S _. exact (fr_CAP_add_none_r cx t m ly S).
Qed.
Lemma fr_CAP_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_LS3 B cx t m ly S -> oa_first (ad_os (lm_hs m)) = Some i ->
  Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S) ->
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  exact fr_CAP_add_open_r.
Qed.
Lemma fr_CAP_write_push : forall cx t m si h (l' : hlist) d ly S ly' S' ev,
  fr_LS3 B cx t m ly S -> wr_pick cx m si h -> 0 < wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  hl_cap l' = grow_cap (hl_n (hs_pending h)) (hl_cap (hs_pending h)) ->
  (lp_grow (hs_pending h) = false -> hl_v l' = hl_v (hs_pending h)) ->
  (forall rest, Permutation (ablocks B ly S)
       ((if lp_grow (hs_pending h) && negb (hl_cap (hs_pending h) =? 0)
         then [(hl_v (hs_pending h), AREC * hl_cap (hs_pending h))] else []) ++ rest) ->
     Permutation (ablocks B ly' S')
       ((d, Z.of_nat (length (wr_x cx m)) + 1) ::
        (if lp_grow (hs_pending h) then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) ->
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  exact fr_CAP_write_push_r.
Qed.
Lemma fr_CAP_drain_skip : forall cx t m ly S,
  fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> fr_CAP cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof.
  intros cx t m ly S _. exact (fr_CAP_drain_skip_r cx t m ly S).
Qed.
Lemma fr_CAP_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) q,
  fr_LS3 B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> ev_evt cx m e ->
  0 <= lm_k m < c_n cx -> lm_O m = [] -> 0 <= lm_cap m ->
  ablocks B ly1 S1 = ablocks B ly S ++ [(q, re_len e)] ->
  (exists rest, Permutation (ablocks B ly1 S1) (aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly2 S2)
       (aout_blks (sl_cap (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) out' ++ rest)) ->
  (exists l1 l2, ablocks B ly2 S2 = l1 ++ (q, re_len e) :: l2 /\ ablocks B ly3 S3 = l1 ++ l2) ->
  fr_CAP cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  exact fr_CAP_event_step_r.
Qed.
Lemma fr_CAP_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat ->
  (exists rest,
     Permutation (ablocks B ly S)
       (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m) ++ rest) /\
     Permutation (ablocks B ly1 S1) (aentry_blks e' ++ asrc_blks h1 ++ aout_blks cap' out' ++ rest)) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  (forall rest, Permutation (ablocks B ly1 S1) (list_blks E ++ list_blks H ++ rest) ->
     Permutation (ablocks B ly' S') (list_blks E' ++ list_blks H' ++ rest)) ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> fr_RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) -> ls3_kh (nth j (lm_es m) dr_e0) -> dr3_hpre h -> ls3_hn h -> 0 <= lm_cap m ->
  cap' = (if dr_live (lm_c m) h
          then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                                   (nth j (lm_es m) dr_e0) h)
          else lm_cap m) ->
  dr3_epost (nth j (lm_es m) dr_e0) e' h -> dr3_hpost h h1 -> ls3_dpost m j h e' h1 -> ls3_cpost h1 E' H' ->
  0 <= cap' -> 0 <= t < OPS_MAX ->
  fr_CAP cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  exact fr_CAP_drain_step_r.
Qed.
Lemma fr_CAP_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5,
  fr_LS3 B cx t m ly0 S0 -> fr_OUT OM cx t m ly0 S0 -> fr_CAP cx t m ly0 S0 ->
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> rm_cnl_ok h1 E' H' ->
  rm_cshe_ok m (set_exp_held h1 E' H') O2 (rm_A1 m h1) H'' ds cc ->
  (forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B ly S)
       (input_blks cx ++ model_blks (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ++ rest)) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  Forall (fun k => 14 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (re_keys (rm_ent m j0)) ->
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  0 <= cap2 -> 0 <= t < OPS_MAX ->
  fr_CAP cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  exact fr_CAP_rm_step_r.
Qed.
(* fr_CAP_pro at any meter (a Theorem Labs lane 09:45Z, KF-COUNT #6: top_x's meter becomes MT_sec): the proof reads only
   lf_base_x's last conjunct and not the mo_le premise *)
Variable MT : ameter_ops.
Lemma fr_CAP_pro : forall XM_LIB RLO RHI LIBROOM NP G ARX,
  forall cx Hp q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base_x B MT XM_LIB RLO RHI ACfn_cf.fr_live_pre LIBROOM NP G ARX cx Hp ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ReplyCnt.xcnt_ok B (c_S cx) (c_ly cx) (input_blks cx) T0 cap out /\
     fr_hblks (c_W cx) (c_mem cx) = (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  fr_CAP cx 0 (pro_m q T' pj c O cap out) ly S.
Proof.
  intros XM_LIB RLO RHI LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S (_ & Hpre) (c0 & mx0 & HA)
    _ _ _ _ _ _ _ _ _ (T0 & rest0 & _ & _ & Hhb & _).
  (* the entry contract's last conjunct, the signed CAPOUT clause (_cut_x.v:109), as fr_hblks' rdword read *)
  unfold W_LLVMFuzzerTestOneInput_cut_x.fr_lib_pre_cf_x in Hpre.
  repeat match type of Hpre with _ /\ _ => destruct Hpre as [_ Hpre] end.
  destruct Hpre as (cv & Hv & Hcv).
  assert (Hc : rdword (aview tfibsegs (@w_H tfibsegs (c_W cx)) (c_mem cx)) (rg_capout fr_RG) = Some cv).
  { apply (rdword_of_val_mem tfibsegs (w_H (c_W cx)) (c_mem cx)); [exact Hv | unfold CAPOUT_MAX, OPS_MAX in *; lia]. }
  (* aout_at's last conjunct: g_out is empty (cap = 0) or a live block of cap > 0 bytes *)
  unfold aout_at in HA.
  repeat match type of HA with _ /\ _ => destruct HA as [_ HA] end.
  unfold fr_CAP. change (lm_cap (pro_m q T' pj c O cap out)) with cap.
  destruct HA as [(Ec & _ & _) | (Hpos & _ & _ & _)]; [subst cap; unfold CAPOUT_MAX, OPS_MAX; lia|].
  (* the g_out block (out, cap) is one of the entry's harness blocks fr_hblks, whose sizes are ATABLE or the
     rdword read of g_capout, cv *)
  assert (Hin : In (out, cap) (W_LLVMFuzzerTestOneInput_cut.fr_hblks (c_W cx) (c_mem cx))).
  { rewrite Hhb. apply in_or_app. right. unfold aout_blks. destruct (Z.eqb_spec cap 0); [lia | left; reflexivity]. }
  revert Hin. match goal with |- In _ (?f _ _) -> _ => unfold f end. cbv zeta.
  rewrite Hc. cbv beta iota.
  destruct (rdword (aview tfibsegs (@w_H tfibsegs (c_W cx)) (c_mem cx)) (rg_src fr_RG)) as [g|];
    [destruct (g =? 0)|];
    (destruct (rdword (aview tfibsegs (@w_H tfibsegs (c_W cx)) (c_mem cx)) (rg_out fr_RG)) as [o|];
     [destruct (cv =? 0)|]);
    cbn [app In]; intros Hin;
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end;
    try contradiction;
    match type of Hin with (_, _) = (_, _) => injection Hin as <- <- end;
    unfold ATABLE, CAPOUT_MAX, OPS_MAX in *; lia.
Qed.
Lemma fr_CAP_gone_end : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate),
  fr_RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  fr_LS3 B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_CAP cx t m ly S ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  fr_CAP cx (t + 1) mc lyx Sx.
Proof.
  exact fr_CAP_gone_end_r.
Qed.

(* ================================================================== the exit's two LS rules at the top's instance *)
(* LSI's four conjuncts, as a Theorem Labs lane's ReplyLSI.v states them (fr_CAP last) *)
Local Notation LSI4 cx t m ly S :=
  (fr_LS3cp B cx t m ly S /\ fr_OUT OM cx t m ly S /\ fr_ENT B cx m ly S /\ fr_CAP cx t m ly S).

(* the cut's XCNT name (ReplyCnt.xcnt_ok) is ReplyLS3w.xcnt_post with the class bound restricted to 1 <= c <= 30:
   both count over xcnt_kept's list, with ReplyCnt's cnt_sec / cnt_cls / SEC0 / CLS0 *)
Lemma xcnt_ok_of_post : forall cx (ly : alayout) (S : astate) T0 cap out,
  ReplyLS3w.xcnt_post B cx ly S T0 cap out -> ReplyCnt.xcnt_ok B S ly (input_blks cx) T0 cap out.
Proof.
  intros cx ly S T0 cap out (H1 & H2). unfold ReplyCnt.xcnt_ok, ReplyCnt.xcnt_kept. split.
  - exact H1.
  - intros c _. exact (H2 c).
Qed.

(* LS_exit_cnt (exit_x.v:190-195 / lib/A/W_LLVMFuzzerTestOneInput_exit.v:7779-7784 at rmexit 5a9b16eac9e; a Theorem Labs lane 06:03Z): ReplyLS3w.v:89
   fr_LS3c_exit_cnt through xcnt_ok_of_post *)
Lemma LS_exit_cnt_I : forall cx t m ly3 S3 rest (ly' : alayout) (S' : astate) cap out,
  LSI4 cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  (forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p) ->
  ReplyCnt.xcnt_ok B S' ly' (input_blks cx) (lm_G m) cap out.
Proof.
  intros cx t m ly3 S3 rest ly' S' cap out ((HLS & _) & _ & _ & _) HP3 HP' HA.
  apply xcnt_ok_of_post.
  exact (fr_LS3c_exit_cnt B cx t m ly3 S3 rest ly' S' cap out HLS HP3 HP' HA).
Qed.

(* LS_exit_cap (exit_x.v:196-198 / lib/A/W_LLVMFuzzerTestOneInput_exit.v:7785-7787 at rmexit 5a9b16eac9e): relay_finish's capacity is at most
   max (lm_cap m) (2 * rf_sum (lm_es m)) (ReplyLS3o.v ou_rf_cap); fr_CAP bounds the first, fr_OUT's mass the second *)
Lemma LS_exit_cap_I : forall (RINV : lfcx -> Z -> lmod -> Prop) cx t m ly S,
  LSI4 cx t m ly S -> RINV cx t m -> 0 <= t <= OPS_MAX ->
  gse_cap (W_LLVMFuzzerTestOneInput_exit.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) <= CAPOUT_MAX.
Proof.
  intros RINV cx t m ly S (_ & (U1 & U2 & U3 & U4) & _ & (C1 & C2)) _ Ht.
  destruct (ou_rf_cap (lm_es m) (lm_c m) [] (lm_mx m) 0 (lm_cap m) U1) as (_ & R2 & _).
  pose proof (rf_sum_mass (lm_es m)) as Hrf.
  assert (Hmass : MASSe (lm_es m) <= MASS m).
  { unfold MASS. assert (0 <= pend_bytes m) by (apply zsum_map_nonneg; exact slot_pend_nonneg). lia. }
  pose proof (CAPOUT_MAX_2WMAX t Ht) as H2.
  apply (Z.le_trans _ _ _ R2). apply Z.max_lub; lia.
Qed.
End keep.
