(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_top_x.v, with its module paths and module names changed; 1646 of its 1749 lines of code are new or changed and 1124 lines of the source are left out. *)
(* Image B's fr_SEC: the secondary-allocation count clause of the B top's LS instance (KF-COUNT B #6), its keep lemmas,
   the meter conjuncts of the B top's rows and of gone_base's GN_RI_step at the counting meter MT_sec.  The B twin of
   image A's lib/A/ReplyLSsec.v and lib/A/ReplyLSsecGn.v (s5-r1d 121b964360a): the same texts and proofs over lib/B's
   names.  proves no function (kind: invariant lemma).

   THE CLAUSE.  At MT := ReplyKfMeterB.MT_sec nsec KMAX (mo_le s s' c := nsec s' <= nsec s + c, mo_ok s c :=
   nsec s + c <= KMAX, mo_malloc n := (if 64512 <? n then 1 else 0), mo_free := 0):
     fr_SEC nsec KMAX KC cx t m ly S := nsec (c_S cx) + SEC_CALL KC <= KMAX /\
                                        21 * (nsec S - nsec (c_S cx)) + sec_ub m <= SEC_RATE KC * Z.min t OPS_MAX,
   SEC_RATE KC := WMAX + 21 * KC, SEC_CALL KC := SEC_RATE KC * (OPS_MAX + 1) / 21, and sec_ub m the bytes not yet
   consumed into lines: every source's pending stream plus every entry's partial line re_U.  A write adds at most WMAX
   bytes (paid by t + 1); a drain, remove or gone consumes bytes that pay its begin-key reallocations at 21 bytes per
   begin line (lane B's B twins lib/B/ReplyKfTrB.v, ReplyKfTrRrB.v, ReplyKfTrRigB.v); every other secondary request of
   one operation is in KC.  The first conjunct is the call's entry budget (lf_base_x's mo_ok at the entry, given
   SEC_CALL KC <= XM_LIB n).  The clause bounds every row's `mo_ok MT S cost` by SEC_CALL KC over the entry
   (fr_SEC_bound), with no bound on t (Z.min).
   - KC: B's counts are A's.  A drain is 45 (sec_drain45: ReplyKfTrB's three capacity chains, 15 each, without the
     relay buffer's re_cap premise LS_drain_pre / LS_rm_rr_pre / GN_LS_rig do not carry), relay_remove 60 (45 and
     ReplyKfChainB.KC_ke = 15), relay_instance_gone 4 * 60 = 240 at GN_LS_rig (no re_cap there) and
     ReplyKfTrRigB.KC_rig = 180 inside GN_RI_step / GN_RI_end (whose premises give re_cap), plus the loop's
     check_no_loss calls 4 * 15.  So the largest operation is 240 and KC is a Variable with 240 <= KC (lane C's
     lib/B/ReplyKfCB.v KF_KC = 256 satisfies it).
   - check_no_loss's charge cnl_cost is at most 15: lib/B/ReplyKfCnlB.kf_cnl_cost_le, cited by name (sec_cnl_le), its
     premises from the drained pair's row of fr_RINV and the reference splitter's 6000-byte lines.
   - fr_SEC reads no block, so the keep lemmas take only the rule's meter premises and the facts that bound its counts.
   A -> B NAMES: lib/A ReplyKfMeter / ReplyKfNsec / ReplyKfChain / ReplyKfTr / ReplyKfTrRr / ReplyKfTrRig / ReplyKfTrSm
   -> the lib/B files of those names with suffix B; A's v3 facts (the dr3_, rm3_, ls3_ and gx_ lemmas) ->
   lib/B/ReplyB3LS3Arms.v,
   ReplyLSBDrainPre.v, ReplyB3LS3cTopxGone.v / GoneF.v (the same names); ReplyLS.wr_facts -> ReplyB3Base.wr_facts_B;
   ReplyLSEvent3.ev3_maxr_le -> ReplyLSBArms.bt_maxr_le; ReplyLS3o.ou_ev_len -> ReplyLSBo.bo_ev_len;
   ReplyRINV_a12.fr_a12_held_keys -> sec_held_keys below (lib/B/ReplyRINVB_exit.v bx_held_keys's proof); fr_rm_pair -> ReplyLSBDrainPre.rm3_pair;
   fr_rm_facts -> sec_rm_cnl's own reading of rm_rr_ok's dr_rel; ReplyLS3Peak.pk_rr_tr_max -> sec_rm_tr_max below
   (the proof of the deleted lib/B/ReplyLSBRrPre.v brr_rm_rr_pre_c2); ReplyLS3cTopxRig.grg_pairs ->
   ReplyLSBRig.brig_pairs; ReplyLS3Peak's pk_gp / pk_slots_cons /
   pk_zsum_seq / pk_zsum_nodup_le -> sec_gp / sec_slots_cons / sec_zsum_seq / sec_zsum_nodup_le below (their B twins
   are in lib/B/ReplyB3LS3Peak.v, which Requires lib/B/ReplyLS3B_inst.v, so this file must not Require it); A's
   WR_MMAX bounds (pk_WR_MMAX) -> fr_MMAX (ReplyLSBArms.fr_MMAX_val); the exit's lx_* -> lib/B/W_bx_defs.v's; the
   rows' arm names are the B top's (lib/B/W_LLVMFuzzerTestOneInput_top_x.v): _arm_event.v's ev_evt / ev_step,
   _drain_defs_x.v's dr3_epre / ls3_dpost, _remove.v's rm_*.  fr_LS3 / fr_LS3c at the instance's call room
   YCfn_cf.CALL_ROOM_B.
   - The gone step's two meter conjuncts are also stated at lib/B/ReplyRINVB_gone.v's RG.GN_RI_step_cnl_meter /
     RG.GN_RI_step_cshe_meter (fr_SEC_GN_RI_step_cnl_meter / _cshe_meter), for any LS whose states give fr_LS3c and
     fr_SEC. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
  W_LLVMFuzzerTestOneInput_head W_LLVMFuzzerTestOneInput_small W_LLVMFuzzerTestOneInput_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c RelayCap
  SlotReads SlotInv SlotDrain3Aux SlotPass2Aux relay_remove_b_aux send_line_b_c ListTr SlotParse.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre ReplyLSBTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
ReplyB3Base ReplyB3LS3 ReplyB3LS3Arms ReplyB3LSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxDefs ReplyB3LS3cTopxGone.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo ReplyLSBoRf ReplyB3LS3o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxGoneF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3oGn ReplyB3LS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3cTopxRig ReplyLSBRig ReplyB3LS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  W_LLVMFuzzerTestOneInput_remove W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_pro
  W_LLVMFuzzerTestOneInput_arm_event W_LLVMFuzzerTestOneInput_drain_defs_x W_bx_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt ReplyRINVB_gone.
(* the exit row's journal (ajournal_gx_x, the B top's LS_exit_end text) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyKfMeterB ReplyKfNsecB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  ReplyKfChainB ReplyKfTrB ReplyKfTrRrB ReplyKfTrRigB ReplyKfTrSmB ReplyKfCB ReplyKfCnlB.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).
(* the B top's arm names (lib/B/W_LLVMFuzzerTestOneInput_top_x.v) *)
Local Notation rm_ent := W_LLVMFuzzerTestOneInput_remove.rm_ent.
Local Notation rm_at := W_LLVMFuzzerTestOneInput_remove.rm_at.
Local Notation rm_rr_tr := W_LLVMFuzzerTestOneInput_remove.rm_rr_tr.
Local Notation rm_rr_ok := W_LLVMFuzzerTestOneInput_remove.rm_rr_ok.
Local Notation rm_mk := W_LLVMFuzzerTestOneInput_remove.rm_mk.
Local Notation rm_cev := W_LLVMFuzzerTestOneInput_remove.rm_cev.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Local Notation gn_pair_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_pair_ok.
Local Notation gn_op := W_LLVMFuzzerTestOneInput_gone_base.gn_op.
Local Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Local Notation osum := ReplyKfTrRigB.osum.
Local Notation kf_in := ReplyKfTrRigB.kf_in.
Local Notation kf_tail := ReplyKfTrRigB.kf_tail.
Local Notation CR := YCfn_cf.CALL_ROOM_B.

(* ================================================================== the per-trace counts without re_cap *)
(* one drain, at any liveness, base and addresses: lane B's potential (kf_drain_pot) with each of its three chains
   gaining at most 15 (kf_drain_caps, kd_gain), instead of kf_drain_tr's relay-buffer bound (which needs re_cap) *)
Lemma sec_drain45 : forall live mx no cap e h j a,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  tr_max (drain_b_c.drain_tr live mx no cap e h j a) < 2 ^ 30 ->
  21 * nsec_tr (drain_b_c.drain_tr live mx no cap e h j a) +
    Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin live mx no cap e h))) <=
  21 * 45 + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
Proof.
  intros live mx no cap e h j a Ho HW HM.
  pose proof (ReplyKfTrB.kf_drain_pot live mx no cap e h j a Ho HW) as P.
  destruct (ReplyKfTrB.kf_drain_caps live mx no cap e h j a Ho HW) as (C1 & C2 & C3).
  pose proof (ReplyKfTrB.kd_gain _ _ _ C1 HM) as G1.
  pose proof (ReplyKfTrB.kd_gain _ _ _ C2 HM) as G2.
  pose proof (ReplyKfTrB.kd_gain _ _ _ C3 HM) as G3.
  lia.
Qed.

(* W_contract.dr_tr is drain_tr at live := dr_live c h, j := 0, a := dadr0 (as ReplyKfTrB.kf_dr) *)
Lemma sec_dr45 : forall c mx no cap e h,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  tr_max (dr_tr c mx no cap e h) < 2 ^ 30 ->
  21 * nsec_tr (dr_tr c mx no cap e h) + Z.of_nat (length (drain_b_c.ds_u (dr_fin c mx no cap e h))) <=
  21 * 45 + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
Proof. intros c mx no cap e h. exact (sec_drain45 (dr_live c h) mx no cap e h 0 drain_b_c.dadr0). Qed.

(* relay_remove: ReplyKfTrRrB.kf_rr_g at the drain bound sec_dr45 (45 + KC_ke = 60) *)
Lemma sec_rr60 : forall c mx no cap FD es h e,
  0 <= FD -> find (fun e => re_fd e =? FD) es = Some e ->
  (re_eof e = 0 -> 0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000)) ->
  tr_max (rr_tr c mx no cap FD es h) < 2 ^ 30 ->
  21 * nsec_tr (rr_tr c mx no cap FD es h) <=
  21 * 60 + (if re_eof e =? 0 then Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) else 0).
Proof.
  intros c mx no cap FD es h e HFD Hf HP HM.
  assert (HD : re_eof e = 0 -> 0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
                 tr_max (dr_tr c mx no cap e h) < 2 ^ 30).
  { intros Ho. destruct (HP Ho) as (H1 & H2).
    pose proof (ReplyKfTrRrB.kf_rr_tm_dr c mx no cap FD es h e HFD Hf Ho). repeat split; try assumption. lia. }
  pose proof (ReplyKfTrRrB.kf_rr_g 45 ltac:(lia)
    (fun c mx no cap e h => 0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
       tr_max (dr_tr c mx no cap e h) < 2 ^ 30)
    (fun c' mx' no' cap' e' h' H => sec_dr45 c' mx' no' cap' e' h' (proj1 H) (proj1 (proj2 H)) (proj2 (proj2 H)))
    c mx no cap FD es h e HFD Hf HD HM) as K.
  assert (KK : ReplyKfChainB.KC_ke = 15) by reflexivity. rewrite KK in K.
  destruct (re_eof e =? 0); lia.
Qed.

(* relay_instance_gone at the drain bound sec_drain45: ReplyKfTrRigB.kf_gone_run / kf_rig's induction, KC 4 * 60 *)
Definition sec_dr_pre (e : rentry) (h : hsrc) : Prop :=
  0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000).

Lemma sec_gone_run : forall c0 mx0 no0 cap0 lv mx pre nm ps no cap j o,
  Forall (fun p => re_eof (fst p) = 0 -> sec_dr_pre (fst p) (fst (snd p))) ps ->
  tr_max (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) < 2 ^ 30 ->
  21 * nsec_tr (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) +
    osum (kf_tail c0 mx0 no0 cap0) ps <=
  21 * 60 * Z.of_nat (length ps) + osum kf_in ps.
Proof.
  intros c0 mx0 no0 cap0 lv mx pre nm ps.
  induction ps as [|[e hj] r IH]; intros no cap j o HF HM.
  - cbn [relay_instance_gone_b_c.gone_run fst length ReplyKfTrRigB.osum map fold_right Z.of_nat].
    rewrite nsec_tr_nil. lia.
  - apply Forall_cons_iff in HF as [HF0 HFr]. cbn [fst snd] in HF0.
    rewrite !ReplyKfTrRigB.osum_cons. cbn [length]. rewrite Nat2Z.inj_succ.
    cbn [relay_instance_gone_b_c.gone_run] in HM |- *. cbv zeta in HM |- *.
    match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
      pose proof (IH n c j1 o1 HFr) as IHr;
      destruct (relay_instance_gone_b_c.gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
    cbn [fst snd] in IHr, HM |- *.
    rewrite !ReplyKfChainB.kf_tm_app in HM. rewrite !nsec_tr_app.
    specialize (IHr ltac:(lia)).
    match goal with |- context [nsec_tr (fst (gestures_end_b_c.keys_end_run ?l ?m ?n ?cp ?x ?jj ?oo))] =>
      assert (HK : nsec_tr (fst (gestures_end_b_c.keys_end_run l m n cp x jj oo)) <= ReplyKfChainB.KC_ke)
        by (apply ReplyKfChainB.kf_keys; lia) end.
    unfold ReplyKfChainB.KC_ke in *.
    destruct (Z.eqb_spec (re_eof e) 0) as [E|E]; cbv beta iota in HM |- *.
    + destruct (HF0 E) as (P1 & P2).
      match goal with |- context [drain_b_c.drain_tr ?l ?m ?n ?cp ?ee ?h ?jj ?a] =>
        assert (HD : 21 * nsec_tr (drain_b_c.drain_tr l m n cp ee h jj a) +
                       Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin l m n cp ee h))) <=
                     21 * 45 + Z.of_nat (length (re_U ee)) + Z.of_nat (length (pending_stream h)))
          by (apply sec_drain45; first [assumption | lia]);
        rewrite (ReplyKfTrRigB.kf_tail_fin c0 mx0 no0 cap0 l m n cp ee h) in HD end.
      assert (KI : ReplyKfTrRigB.kf_in e (fst hj) =
                   Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream (fst hj)))) by reflexivity.
      lia.
    + rewrite nsec_tr_nil. lia.
Qed.

Lemma sec_rig45 : forall c mx no cap ID es hs,
  (length es <= 4)%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> sec_dr_pre (fst p) (fst (snd p))) (combine es hs) ->
  tr_max (rig_tr c mx no cap ID es hs) < 2 ^ 30 ->
  21 * nsec_tr (rig_tr c mx no cap ID es hs) + osum (kf_tail c mx no cap) (combine es hs) <=
  21 * 240 + osum kf_in (combine es hs).
Proof.
  intros c mx no cap ID es hs Hn HF HM.
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr in HM |- *. cbv zeta in HM |- *.
  pose proof (sec_gone_run c mx no cap _ _ _ _ _ _ _ _ _ HF HM) as H.
  pose proof (ReplyKfTrRigB.kf_combine_len _ _ es hs) as HL.
  assert (HN : 0 <= Z.of_nat (length (combine es hs)) <= 4) by lia.
  lia.
Qed.

(* ================================================================== the reference splitter's lines *)
(* an open entry's relay partial line is the harness's kept partial line unless the line is overlong (fr_pair_ok's
   clause), so the kept partial line is at most 6000 bytes when not overlong *)
Lemma sec_hsW : forall (e : rentry) h, re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  (re_skip e = 0 \/ re_skip e = 1) -> Z.of_nat (length (re_U e)) <= APARTIAL ->
  hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000.
Proof.
  intros e h Hsk HskU H01 HU Ho.
  assert (E0 : re_skip e = 0) by lia.
  pose proof (f_equal (@length Z) (HskU E0)) as L. rewrite !SlotReads.bzs_length in L.
  unfold APARTIAL in HU. lia.
Qed.

(* then every line the splitter gives is at most 6000 bytes (SlotDrain3Aux.lines_len6) *)
Lemma sec_lines6 : forall h, (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  Forall (fun l => Z.of_nat (length l) <= 6000) (dr_lines h).
Proof.
  intros h HW. unfold dr_lines.
  assert (HR : ls_k (hs_state h) = false -> SlotParse.zlen (ls_w (hs_state h)) <= 6000).
  { cbn [hs_state ls_k ls_w]. intros Hk. apply Z.eqb_neq in Hk. unfold SlotParse.zlen.
    rewrite SlotReads.bzs_length. exact (HW Hk). }
  pose proof (SlotDrain3Aux.lines_len6 (bzs (pending_stream h)) (hs_state h) HR) as L.
  eapply Forall_impl; [|exact L]. intros l Hl. unfold SlotParse.zlen in Hl. exact Hl.
Qed.

(* the records of an expected list holding the lines Ls (as bytes) are at most APARTIAL bytes each *)
Lemma sec_recs_short : forall (E : hlist) (Ls : list (list Z)),
  map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall (fun l => Z.of_nat (length l) <= 6000) Ls ->
  Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs E).
Proof.
  intros E Ls Hm HL. apply Forall_forall. intros r Hr.
  assert (Hin : In (snd r) (map (map (Z_to_bv 8)) Ls)) by (rewrite <- Hm; apply in_map; exact Hr).
  apply in_map_iff in Hin as (l & El & Hl). rewrite <- El, length_map.
  rewrite Forall_forall in HL. specialize (HL l Hl). unfold APARTIAL. lia.
Qed.

(* the held list is no longer than the keys: its texts are distinct and each is a key's (A's ReplyRINV_a12.v
   fr_a12_held_keys; lib/B/ReplyRINVB_exit.v bx_held_keys, the same proof) *)
Lemma sec_held_keys : forall ks (H : hlist), NoDup (texts H) -> same_set (drain_b_c.keys_texts ks) (texts H) ->
  hl_n H <= Z.of_nat (length ks).
Proof.
  intros ks H Hnd Hss. first [apply NoDup_ListNoDup in Hnd | idtac].
  assert (Hinc : incl (texts H) (drain_b_c.keys_texts ks)) by (intros y Hy; exact (proj2 (Hss y) Hy)).
  pose proof (NoDup_incl_length Hnd Hinc) as Hle.
  unfold texts, drain_b_c.keys_texts in Hle. rewrite !length_map in Hle. unfold hl_n. lia.
Qed.

(* check_no_loss's count premise: the held keys are the entry's keys (at most keys_total / 5 of them) and the lines'
   begin keys cost 21 bytes each of the drained bytes, all within the pair's cost (fr_pair_cost < 2 ^ 26) *)
Lemma sec_cnl_count : forall (e : rentry) (p : hsrc * nat) (H : hlist) Ls,
  NoDup (texts H) -> same_set (drain_b_c.keys_texts (re_keys e)) (texts H) ->
  Z.of_nat (length (with_nul Ls)) <=
    (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0) + Z.of_nat (length (pending_stream (fst p))) ->
  fr_pair_cost e p < 2 ^ 26 ->
  hl_n H + Z.of_nat (count_begin Ls) < 2 ^ 25.
Proof.
  intros e p H Ls Hnd Hss HW Hc.
  pose proof (sec_held_keys (re_keys e) H Hnd Hss) as A.
  pose proof (rm3_kt_len (re_keys e)) as K.
  pose proof (SlotReads.count_begin_bytes Ls) as C.
  unfold fr_pair_cost in Hc. destruct (re_skip e =? 0); lia.
Qed.

(* ================================================================== the clause *)
Section sec.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a Theorem Labs lane's count of granted non-errbuf secondary entries (nsec_cf), the run bound (cf_kmax) and the per-operation
   constant (lane C's ReplyKfCB.KF_KC): the instance file sets them *)
Variable nsec : astate -> Z.
Variable KMAX : Z.
Variable KC : Z.
Local Notation MT := (MT_sec nsec KMAX).

(* Three bounds of the same family, with different roles; do not merge them.
   - KMAX: the run total of secondary entries, a Variable here. The instance sets it to reply's cf_kmax, whose value
     (2 ^ 23 or 2 ^ 24) is a Theorem Labs lane's ruling (AbudgetRestate), pending on 2026-10-30. Nothing in this file depends on it;
     this file proves only per-call facts within SEC_CALL.
   - 2 ^ 25: the premise of check_no_loss's count, ReplyKfCnlB.kf_cnl_cost_le (hl_n H + count_begin (texts E) < 2 ^ 25),
     derived here from fr_RINV by sec_cnl_count.
   - 2 ^ 22: a conjunct of B top_x's LS_cnl_pre / LS_rm_cnl_pre and of the gone rows (hl_n + count_begin < 2 ^ 22). It is
     cnl_spec's own bound, proved in ReplyB3LS3cTopxPost.v, not here; it implies the 2 ^ 25 premise. *)
Definition sec_str (o : option hsrc) : Z :=
  match o with Some h => Z.of_nat (length (pending_stream h)) | None => 0 end.
Definition sec_ub (m : lmod) : Z := zsum (map sec_str (lm_hs m)) + zsum (map pt_eu (lm_es m)).
Definition SEC_RATE : Z := WMAX + 21 * KC.
Definition SEC_CALL : Z := SEC_RATE * (OPS_MAX + 1) / 21.
Definition fr_SEC (cx : lfcx) (t : Z) (m : lmod) (ly : alayout) (S : astate) : Prop :=
  nsec (c_S cx) + SEC_CALL <= KMAX /\
  21 * (nsec S - nsec (c_S cx)) + sec_ub m <= SEC_RATE * Z.min t OPS_MAX.

Lemma sec_str_nonneg : forall o, 0 <= sec_str o.
Proof. intros [h|]; cbn [sec_str]; lia. Qed.
Lemma sec_ub_nonneg : forall m, 0 <= sec_ub m.
Proof.
  intros m. unfold sec_ub.
  pose proof (zsum_map_nonneg sec_str (lm_hs m) sec_str_nonneg).
  pose proof (zsum_map_nonneg pt_eu (lm_es m) pt_eu_nonneg). lia.
Qed.
(* one source and one entry are within sec_ub *)
Lemma sec_ub_pair : forall m si h j e,
  nth si (lm_hs m) None = Some h -> nth_error (lm_es m) j = Some e ->
  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) <= sec_ub m.
Proof.
  intros m si h j e Hh He. unfold sec_ub.
  pose proof (zsum_map_elem sec_str (lm_hs m) si (Some h) sec_str_nonneg (nth_some_error _ _ _ Hh)) as A.
  pose proof (zsum_map_elem pt_eu (lm_es m) j e pt_eu_nonneg He) as E.
  assert (E1 : sec_str (Some h) = Z.of_nat (length (pending_stream h))) by reflexivity.
  assert (E2 : pt_eu e = Z.of_nat (length (re_U e))) by reflexivity.
  lia.
Qed.

(* ---- the meter's facts at MT_sec ---- *)
Lemma sec_HMs : forall n, mo_malloc MT n = if 64512 <? n then 1 else 0.
Proof. reflexivity. Qed.
Lemma sec_HFs : mo_free MT = 0.
Proof. reflexivity. Qed.
Lemma sec_tr : forall (P : Type) (tr : list (RelayRunT.rev P)), tr_cost MT tr = nsec_tr tr.
Proof. intros P tr. exact (tr_cost_sec MT P tr sec_HMs sec_HFs). Qed.
Lemma sec_oa : oa_cost MT = 0.
Proof. reflexivity. Qed.
Lemma sec_sr : forall o, sr_cost MT o = 0.
Proof. intros [h|]; unfold sr_cost, lf_cost; rewrite !sec_HFs; lia. Qed.
Lemma sec_cshe : forall H, cshe_cost MT H = 0.
Proof. intros H. unfold cshe_cost. rewrite sec_HFs. lia. Qed.
(* the kit's malloc law is PresetRoom's class rule (ReplyKfMeterB.sec_lit) *)
Lemma sec_KF_MAL : forall n, mo_malloc MT n = if ReplyCnt.Psec n then 1 else 0.
Proof. intros n. unfold ReplyCnt.Psec. rewrite sec_lit. reflexivity. Qed.

(* ---- check_no_loss's charge: ReplyKfCnlB.v's kf_gmc_nonneg / kf_cnl_cost_le at MT := MT_sec, cited, not re-proved ---- *)
Lemma sec_cnl_nonneg : forall E H, 0 <= cnl_cost MT E H.
Proof.
  intros E H. unfold cnl_cost. generalize (texts H) (hl_cap H). induction (hl_recs E) as [|r rs IH]; intros T cap.
  - cbn [cnl_go]. lia.
  - cbn [cnl_go]. pose proof (ReplyKfCnlB.kf_gmc_nonneg MT sec_KF_MAL sec_HFs T cap (snd r)).
    specialize (IH (RelayModel.upd T (bzs (snd r))) (capstep T (bzs (snd r)) cap)). rewrite sec_HFs. lia.
Qed.
Lemma sec_ends : forall hs, W_bx_defs.lx_ends_cost MT hs = 0.
Proof. induction hs as [|[h|] hs IH]; cbn [W_bx_defs.lx_ends_cost]; rewrite ?sec_HFs; lia. Qed.
Lemma sec_srt : forall hs, W_bx_defs.lx_sr_total MT hs = 0.
Proof. intros hs. unfold W_bx_defs.lx_sr_total. rewrite !sec_sr. lia. Qed.

(* ---- the arithmetic ---- *)
Section rate.
Hypothesis HKC : 240 <= KC.

Lemma SEC_RATE_ge : 21 * KC <= SEC_RATE /\ 0 <= SEC_RATE.
Proof. unfold SEC_RATE, WMAX. lia. Qed.

(* a rule with no secondary request and no new bytes: t may grow without bound *)
Lemma fr_SEC_keep : forall cx t t' m m' ly S ly' S',
  t <= t' -> nsec S' <= nsec S -> sec_ub m' <= sec_ub m -> fr_SEC cx t m ly S -> fr_SEC cx t' m' ly' S'.
Proof.
  intros cx t t' m m' ly S ly' S' Ht HS Hu (H1 & H2). split; [exact H1|].
  destruct SEC_RATE_ge as (_ & R0).
  assert (Hm : SEC_RATE * Z.min t OPS_MAX <= SEC_RATE * Z.min t' OPS_MAX) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

(* one operation (t < OPS_MAX): its requests D and its new bytes within SEC_RATE *)
Lemma fr_SEC_step : forall cx t m m' ly S ly' S' D,
  0 <= t < OPS_MAX -> nsec S' <= nsec S + D -> 21 * D + sec_ub m' <= sec_ub m + SEC_RATE ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) m' ly' S'.
Proof.
  intros cx t m m' ly S ly' S' D Ht HS Hu (H1 & H2). split; [exact H1|].
  assert (E1 : Z.min t OPS_MAX = t) by lia.
  assert (E2 : Z.min (t + 1) OPS_MAX = t + 1) by (unfold OPS_MAX in *; lia).
  rewrite E1 in H2. rewrite E2, Z.mul_add_distr_l, Z.mul_1_r. lia.
Qed.

(* every count of the call so far, plus one operation's (paid from sec_ub), stays within SEC_CALL of the entry *)
Lemma fr_SEC_bound : forall cx t m ly S X,
  fr_SEC cx t m ly S -> 21 * (X - nsec S) <= 21 * KC + sec_ub m -> X <= nsec (c_S cx) + SEC_CALL.
Proof.
  intros cx t m ly S X (H1 & H2) HX.
  destruct SEC_RATE_ge as (R1 & R0).
  assert (Hm : SEC_RATE * Z.min t OPS_MAX <= SEC_RATE * OPS_MAX) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (H3 : 21 * (X - nsec (c_S cx)) <= SEC_RATE * (OPS_MAX + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. lia. }
  assert (H4 : X - nsec (c_S cx) <= SEC_RATE * (OPS_MAX + 1) / 21) by (apply Z.div_le_lower_bound; lia).
  unfold SEC_CALL. lia.
Qed.

(* the rows' mo_ok: the state S1 is at most D requests past S, and D plus the row's cost is paid *)
Lemma fr_SEC_ok : forall cx t m ly S S1 D c,
  fr_SEC cx t m ly S -> nsec S1 <= nsec S + D -> 21 * (D + c) <= 21 * KC + sec_ub m -> mo_ok MT S1 c.
Proof.
  intros cx t m ly S S1 D c H HS Hc. change (nsec S1 + c <= KMAX).
  pose proof (fr_SEC_bound cx t m ly S (nsec S1 + c) H ltac:(lia)) as X.
  destruct H as (H1 & _). lia.
Qed.

(* the call's start: no request since the entry and no bytes *)
Lemma fr_SEC_init : forall cx m ly S,
  nsec (c_S cx) + SEC_CALL <= KMAX -> nsec S <= nsec (c_S cx) -> sec_ub m = 0 -> fr_SEC cx 0 m ly S.
Proof.
  intros cx m ly S H1 HS Hu. split; [exact H1|]. rewrite Hu.
  change (Z.min 0 OPS_MAX) with 0. rewrite Z.mul_0_r. lia.
Qed.
End rate.

(* ================================================================== the keep lemmas *)
Section keep.
Hypothesis HKC : 240 <= KC.
Variable B : asyms.
Lemma sec_cnl_le : forall E H : hlist,
  hl_n H + Z.of_nat (count_begin (texts E)) < 2 ^ 25 ->
  Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs E) ->
  cnl_cost MT E H <= 15.
Proof. exact (ReplyKfCnlB.kf_cnl_cost_le MT sec_KF_MAL sec_HFs). Qed.

(* ---- the rules that keep the sources' pending lists and the entries ---- *)
Lemma fr_SEC_close_a : forall cx t m i ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S. apply fr_SEC_keep; [exact HKC | lia | lia |].
  unfold sec_ub. cbn [sm_close lm_hs lm_es].
  rewrite (upd_hs_map sec_str i upd_closed (lm_hs m)) by (intros h; reflexivity). lia.
Qed.
Lemma fr_SEC_eintr_a : forall cx t m i ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S. apply fr_SEC_keep; [exact HKC | lia | lia |].
  unfold sec_ub. cbn [sm_eintr lm_hs lm_es].
  rewrite (upd_hs_map sec_str i upd_eintr (lm_hs m)) by (intros h; reflexivity). lia.
Qed.
Lemma fr_SEC_sendmax_a : forall cx t m u ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_sendmax cx m u) ly S.
Proof. intros cx t m u ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [sm_sendmax lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_default_a : forall cx t m g ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_default cx m g) ly S.
Proof. intros cx t m g ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [sm_default lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_add_none_a : forall cx t m ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [ad_none lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_write_skip_a : forall cx t m k ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (wr_skip m k) ly S.
Proof. intros cx t m k ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [wr_skip lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_head_nout_a : forall cx t m ly S, fr_SEC cx t m ly S -> fr_SEC cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [lm_clear_O lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_head_skip_a : forall cx t m k ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (lm_set_k m k) ly S.
Proof. intros cx t m k ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [lm_set_k lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_drain_skip_a : forall cx t m k ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (dr_skip m k) ly S.
Proof. intros cx t m k ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [dr_skip lm_hs lm_es]. lia. Qed.

(* ---- op_add: relay_add's requests are primary (oa_cost = 0); the new source and entry hold no bytes ---- *)
Lemma fr_SEC_add_open_a : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  length (lm_hs m) = 4%nat -> oa_first (ad_os (lm_hs m)) = Some i -> mo_le MT S S' (oa_cost MT) ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (ad_open m i q pj ev) ly' S'.
Proof.
  intros cx t m i q pj ev ly S ly' S' Hl Hf Hmo H.
  change (nsec S' <= nsec S + oa_cost MT) in Hmo. rewrite sec_oa in Hmo.
  apply (fr_SEC_keep HKC cx t (t + 1) m (ad_open m i q pj ev) ly S ly' S'); [lia | lia | | exact H].
  destruct (oa_first_free (lm_hs m) i Hl Hf) as (_ & Hi).
  unfold sec_ub. rewrite ad_open_hs, ad_open_es, map_app, zsum_app.
  match goal with |- context [map sec_str (?f i ?x (lm_hs m))] =>
    pose proof (set_nth_zsum sec_str i x None (lm_hs m) Hi) as Zs;
    assert (P0 : sec_str x = 0) by reflexivity end.
  assert (N0 : sec_str None = 0) by reflexivity.
  match goal with |- context [map pt_eu [?y]] => assert (U0 : zsum (map pt_eu [y]) = 0) by reflexivity end.
  lia.
Qed.

(* ---- write: list_push's requests (kf_lp_cost, 2) and the pushed bytes (at most WMAX) ---- *)
Lemma sec_stream_push : forall h (l' : hlist) d (x : list byte), hl_recs l' = hl_recs (hs_pending h) ++ [(d, x)] ->
  Z.of_nat (length (pending_stream (set_pending h l'))) <=
  Z.of_nat (length (pending_stream h)) + Z.of_nat (length x).
Proof.
  intros h l' d x Hr. unfold pending_stream. cbn [set_pending hs_pending hs_off]. rewrite Hr.
  destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [app].
  - cbn [map concat snd]. rewrite app_nil_r, length_skipn. cbn [length]. lia.
  - rewrite map_app, concat_app. cbn [map concat snd]. rewrite app_nil_r, !length_app. lia.
Qed.
Lemma fr_SEC_write_push_a : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  wr_pick cx m si h -> 0 < wr_n cx m -> hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) -> 0 <= t < OPS_MAX ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ev ly S ly' S' (_ & _ & Hh) Hn Hr Hmo Ht H.
  change (nsec S' <= nsec S + lp_cost MT (hs_pending h) (wr_n cx m)) in Hmo.
  pose proof (ReplyKfTrSmB.kf_lp_cost MT sec_HMs sec_HFs (hs_pending h) (wr_n cx m)) as Klp.
  assert (Klp2 : ReplyKfTrSmB.KC_lp = 2) by reflexivity.
  apply (fr_SEC_step cx t m _ ly S ly' S' (lp_cost MT (hs_pending h) (wr_n cx m)) Ht Hmo); [|exact H].
  unfold sec_ub. cbn [wr_push lm_hs lm_es].
  pose proof (set_nth_zsum sec_str si (Some (set_pending h l')) (Some h) (lm_hs m) (nth_some_error _ _ _ Hh)) as Zs.
  pose proof (sec_stream_push h l' d (wr_x cx m) Hr) as Hp.
  assert (E1 : sec_str (Some h) = Z.of_nat (length (pending_stream h))) by reflexivity.
  assert (E2 : sec_str (Some (set_pending h l')) = Z.of_nat (length (pending_stream (set_pending h l'))))
    by reflexivity.
  destruct (wr_facts_B cx m Hn) as (_ & Hx). pose proof (ou_wr_n_le cx m) as Hw.
  destruct (SEC_RATE_ge HKC) as (R1 & _). unfold SEC_RATE in *. lia.
Qed.

(* ---- event: its own copy (one request at most, kf_ev_cost) and relay_event's send (kf_re_cost, 15) ---- *)
Lemma sec_ev_sl : forall cx m e, W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> lm_O m = [] ->
  sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= 15.
Proof.
  intros cx m e HE HO.
  pose proof (bt_maxr_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as M.
  pose proof (bo_ev_len cx m e HE) as L.
  assert (E0 : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  rewrite E0 in M |- *.
  pose proof (ReplyKfTrSmB.kf_re_cost MT sec_HMs sec_HFs (lm_c m) (lm_mx m) 0 (lm_cap m) e ltac:(lia)) as K.
  assert (K2 : ReplyKfTrSmB.KC_re = 15) by reflexivity. lia.
Qed.
Lemma fr_SEC_event_step_a : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out',
  W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) -> lm_O m = [] -> 0 <= t < OPS_MAX ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' HE M1 M2 M3 HO Ht H.
  change (nsec S1 <= nsec S + mo_malloc MT (re_len e)) in M1.
  change (nsec S2 <= nsec S1 + sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in M2.
  change (nsec S3 <= nsec S2 + mo_free MT) in M3.
  pose proof (sec_ev_sl cx m e HE HO) as K1.
  pose proof (ReplyKfTrSmB.kf_ev_cost MT sec_HMs (re_len e)) as K2.
  assert (K3 : ReplyKfTrSmB.KC_ev = 1) by reflexivity. rewrite sec_HFs in M3.
  apply (fr_SEC_step cx t m _ ly S ly3 S3 16 Ht ltac:(lia)); [|exact H].
  unfold sec_ub. cbn [W_LLVMFuzzerTestOneInput_arm_event.ev_step lm_hs lm_es].
  destruct (SEC_RATE_ge HKC) as (R1 & _). lia.
Qed.
Lemma fr_SEC_event_malloc_a : forall cx t m ly S e,
  fr_SEC cx t m ly S -> mo_ok MT S (mo_malloc MT (re_len e)).
Proof.
  intros cx t m ly S e H.
  pose proof (ReplyKfTrSmB.kf_ev_cost MT sec_HMs (re_len e)) as K.
  assert (K2 : ReplyKfTrSmB.KC_ev = 1) by reflexivity. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.
Lemma fr_SEC_event_relay_a : forall cx t m ly S (S1 : astate) e,
  W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> lm_O m = [] -> mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  fr_SEC cx t m ly S ->
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros cx t m ly S S1 e HE HO M1 H. change (nsec S1 <= nsec S + mo_malloc MT (re_len e)) in M1.
  pose proof (sec_ev_sl cx m e HE HO) as K1.
  pose proof (ReplyKfTrSmB.kf_ev_cost MT sec_HMs (re_len e)) as K2.
  assert (K3 : ReplyKfTrSmB.KC_ev = 1) by reflexivity. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok HKC cx t m ly S S1 (mo_malloc MT (re_len e))); [exact H | lia | lia].
Qed.
Lemma fr_SEC_event_free_a : forall cx t m ly S (S1 S2 : astate) e,
  W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  fr_SEC cx t m ly S -> mo_ok MT S2 (mo_free MT).
Proof.
  intros cx t m ly S S1 S2 e HE HO M1 M2 H.
  change (nsec S1 <= nsec S + mo_malloc MT (re_len e)) in M1.
  change (nsec S2 <= nsec S1 + sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in M2.
  pose proof (sec_ev_sl cx m e HE HO) as K1.
  pose proof (ReplyKfTrSmB.kf_ev_cost MT sec_HMs (re_len e)) as K2.
  assert (K3 : ReplyKfTrSmB.KC_ev = 1) by reflexivity. pose proof (sec_ub_nonneg m).
  rewrite sec_HFs. apply (fr_SEC_ok HKC cx t m ly S S2 16); [exact H | lia | lia].
Qed.

(* ---- op_add's prologue rows and the call's start ---- *)
Lemma fr_SEC_pro_oa_a : forall cx (S2 : astate),
  nsec (c_S cx) + SEC_CALL <= KMAX -> mo_le MT (c_S cx) S2 0 -> mo_ok MT S2 (oa_cost MT).
Proof.
  intros cx S2 H1 Hmo. change (nsec S2 <= nsec (c_S cx) + 0) in Hmo. rewrite sec_oa. change (nsec S2 + 0 <= KMAX).
  unfold SEC_CALL, SEC_RATE, WMAX, OPS_MAX in H1.
  assert (0 <= (65535 + 21 * KC) * (512 + 1) / 21) by (apply Z.div_pos; lia). lia.
Qed.
Lemma sec_ub_pro : forall q T' pj c O cap out, sec_ub (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) = 0.
Proof. reflexivity. Qed.
Lemma fr_SEC_pro_a : forall cx (S2 S : astate) m ly,
  nsec (c_S cx) + SEC_CALL <= KMAX -> mo_le MT (c_S cx) S2 0 -> mo_le MT S2 S (oa_cost MT) -> sec_ub m = 0 ->
  fr_SEC cx 0 m ly S.
Proof.
  intros cx S2 S m ly H1 M1 M2 Hu. change (nsec S2 <= nsec (c_S cx) + 0) in M1.
  change (nsec S <= nsec S2 + oa_cost MT) in M2. rewrite sec_oa in M2.
  apply fr_SEC_init; [exact H1 | lia | exact Hu].
Qed.

(* ---- drain: drain's requests (sec_dr45, paid by the drained bytes) and check_no_loss's (15) ---- *)
(* the drained pair's facts the counts read (ReplyB3LS3Arms.v dr3_rinv) *)
Lemma sec_dr_pair : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
  Forall (fun l => Z.of_nat (length l) <= 6000) (dr_lines h) /\
  hl_n (hs_held h) + Z.of_nat (count_begin (dr_lines h)) < 2 ^ 25 /\ hl_recs (hs_expected h) = [] /\
  Forall SlotReads.zrange (dr_lines h) /\
  Z.of_nat (length (pending_stream h)) <= SlotInv.WRITE_MAX * t /\
  Z.of_nat (length (re_keys (nth j (lm_es m) dr_e0))) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  (hs_overlong h = 1 \/ bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)).
Proof.
  intros cx t m si h j HRI Hpick Hj Hfd Heof HU.
  destruct (dr3_rinv cx t m si h j HRI Hpick Hj Hfd Heof)
    as ((Hsk & HskU) & Hsk01 & Hss & Hnd & Hexp & _ & _ & Hpw & Hoff & Hcost).
  set (e := nth j (lm_es m) dr_e0) in *.
  pose proof (sec_hsW e h Hsk HskU Hsk01 HU) as HW.
  pose proof (dr3_lines h) as (_ & HLw & HZr & _).
  pose proof (dr3_wcost e h Hsk HskU Hsk01) as Hwc.
  refine (conj Hoff (conj HW (conj (sec_lines6 h HW) (conj _ (conj Hexp (conj HZr (conj Hpw (conj _ _)))))))).
  - apply (sec_cnl_count e (h, si) (hs_held h) (dr_lines h) Hnd Hss); [|exact Hcost].
    cbn [fst]. rewrite Hwc in HLw. exact HLw.
  - unfold fr_pair_cost in Hcost. cbn [fst] in Hcost. pose proof (dpre_keys_le (re_keys e)).
    destruct (re_skip e =? 0); lia.
  - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply HskU. lia.
Qed.

(* the expected list after the drain holds the lines (ls3_dpost), and check_no_loss over it costs at most 15 *)
Lemma sec_cnl_lines : forall h (h1 : hsrc),
  hl_n (hs_held h) + Z.of_nat (count_begin (dr_lines h)) < 2 ^ 25 -> hl_recs (hs_expected h) = [] ->
  Forall SlotReads.zrange (dr_lines h) -> Forall (fun l => Z.of_nat (length l) <= 6000) (dr_lines h) ->
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h1 = hs_held h ->
  cnl_cost MT (hs_expected h1) (hs_held h1) <= 15.
Proof.
  intros h h1 Hc Hexp HZr HL Hmap Hheld. rewrite Hexp in Hmap. cbn [map app] in Hmap.
  apply sec_cnl_le.
  - assert (HT : texts (hs_expected h1) = dr_lines h).
    { unfold texts. rewrite <- (map_map snd bzs). rewrite Hmap. exact (fr_bzs_lines _ HZr). }
    rewrite HT, Hheld. exact Hc.
  - exact (sec_recs_short (hs_expected h1) (dr_lines h) Hmap HL).
Qed.

(* top_x LS_drain_pre's meter conjunct *)
Lemma fr_SEC_drain_pre_a : forall cx t m ly S si h j,
  fr_LS3 B CR cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  fr_SEC cx t m ly S ->
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfd Heof Ht HU H.
  destruct (sec_dr_pair cx t m si h j HRI Hpick Hj Hfd Heof HU) as (Hoff & HW & _).
  pose proof (fr_LS3_drain_pre_c4 B CR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfd Heof Ht HU) as HM.
  rewrite fr_MMAX_val in HM.
  pose proof (sec_dr45 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h
                Hoff HW ltac:(lia)) as K.
  pose proof Hpick as (_ & _ & Hh).
  assert (Hej : nth_error (lm_es m) j = Some (nth j (lm_es m) dr_e0)) by (apply nth_error_nth'; exact Hj).
  pose proof (sec_ub_pair m si h j (nth j (lm_es m) dr_e0) Hh Hej) as P.
  unfold dr_cost. rewrite sec_tr.
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.

(* top_x LS_cnl_pre's meter conjunct *)
Lemma fr_SEC_cnl_pre_a : forall cx t m ly S (S' : astate) si h j h'',
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] -> W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) ->
  fr_SEC cx t m ly S -> mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')).
Proof.
  intros cx t m ly S S' si h j h'' HRI Hpick Hj Hfd Heof Hmo Hmap Hheld Ht HO Hep H.
  destruct Hep as (_ & HU & _).
  destruct (sec_dr_pair cx t m si h j HRI Hpick Hj Hfd Heof HU)
    as (Hoff & HW & HL & Hc & Hexp & HZr & Hpw & Hkp & HUW).
  assert (HM : tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
               < 2 ^ 30).
  { rewrite HO. cbn [length Z.of_nat].
    pose proof (dpre_dr_tr_max (lm_c m) (lm_mx m) (lm_cap m) (nth j (lm_es m) dr_e0) h HU HUW Hoff Hexp Hkp
                  ltac:(unfold SlotInv.WRITE_MAX, OPS_MAX in *; lia)) as X.
    rewrite fr_MMAX_val in X. lia. }
  pose proof (sec_dr45 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h
                Hoff HW HM) as K.
  pose proof (sec_cnl_lines h h'' Hc Hexp HZr HL Hmap Hheld) as Kc.
  pose proof Hpick as (_ & _ & Hh).
  assert (Hej : nth_error (lm_es m) j = Some (nth j (lm_es m) dr_e0)) by (apply nth_error_nth'; exact Hj).
  pose proof (sec_ub_pair m si h j (nth j (lm_es m) dr_e0) Hh Hej) as P.
  change (nsec S' <= nsec S + dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                     (nth j (lm_es m) dr_e0) h) in Hmo.
  unfold dr_cost in Hmo. rewrite sec_tr in Hmo.
  pose proof (sec_cnl_nonneg (hs_expected h'') (hs_held h'')).
  apply (fr_SEC_ok HKC cx t m ly S S' _ _ H Hmo). lia.
Qed.

(* top_x LS_drain_step *)
Lemma fr_SEC_drain_step_a : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B CR cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  hl_recs (hs_pending h1) = [] -> E = hs_expected h1 -> H = hs_held h1 -> h'' = set_exp_held h1 E' H' ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 -> 0 <= t < OPS_MAX ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H h1 E' H' HLS HRI Hat Hpick Hj Hfd Heof Hep M1 M2
    Hpend EE EH Hh'' Hdp Ht HS.
  subst E H.
  destruct Hep as (_ & HU & _).
  destruct (sec_dr_pair cx t m si h j HRI Hpick Hj Hfd Heof HU) as (Hoff & HW & HL & Hc & Hexp & HZr & _).
  pose proof (fr_LS3_drain_pre_c4 B CR cx t m ly S si h j HLS HRI Hat Hpick Hj Hfd Heof Ht HU) as HM.
  rewrite fr_MMAX_val in HM.
  set (e := nth j (lm_es m) dr_e0) in *.
  pose proof (sec_dr45 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) e h Hoff HW ltac:(lia)) as K.
  destruct Hdp as (HU' & _ & Hoff1 & Hmap & Hheld & _).
  pose proof (sec_cnl_lines h h1 Hc Hexp HZr HL Hmap Hheld) as Kc.
  change (nsec S1 <= nsec S + dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) e h) in M1.
  change (nsec S' <= nsec S1 + cnl_cost MT (hs_expected h1) (hs_held h1)) in M2.
  unfold dr_cost in M1. rewrite sec_tr in M1.
  apply (fr_SEC_step cx t m _ ly S ly' S'
           (nsec_tr (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) e h) +
            cnl_cost MT (hs_expected h1) (hs_held h1)) Ht ltac:(lia)); [|exact HS].
  pose proof Hpick as (_ & _ & Hh).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  assert (Hej : nth_error (lm_es m) j = Some e) by (unfold e; apply nth_error_nth'; exact Hj).
  unfold sec_ub. cbn [dr_step lm_hs lm_es].
  pose proof (dr3_dset_zsum sec_str si (Some h'') (Some h) (lm_hs m) Hhi) as Zp.
  pose proof (dr3_dset_zsum pt_eu j e' e (lm_es m) Hej) as Zu.
  assert (P0 : sec_str (Some h'') = 0).
  { subst h''. cbn [sec_str]. unfold pending_stream. cbn [set_exp_held hs_pending]. rewrite Hpend. reflexivity. }
  assert (EU' : pt_eu e' = Z.of_nat (length (drain_b_c.ds_u
                  (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) e h)))).
  { unfold pt_eu. rewrite <- (SlotReads.bzs_length (re_U e')). fold e in HU'. rewrite HU'. reflexivity. }
  assert (E1 : sec_str (Some h) = Z.of_nat (length (pending_stream h))) by reflexivity.
  assert (Eu : pt_eu e = Z.of_nat (length (re_U e))) by reflexivity.
  destruct (SEC_RATE_ge HKC) as (R1 & _). lia.
Qed.

(* ---- remove: relay_remove's requests (sec_rr60, paid by the entry's and the source's bytes), check_no_loss's (15),
   check_shape_ends' and source_reset's (frees only).  The count needs the arm's 0 <= t < OPS_MAX (the requests'
   largest, sec_rm_tr_max) and |re_U e| <= APARTIAL (the kept partial line, the lines' lengths):
   premises here ---- *)
(* the remove arm's model update of a slot (lib/B/W_LLVMFuzzerTestOneInput_remove.v rm_set_nth; ReplyB3LS3Arms.v
   rm3_set_zsum's statement and proof over it) *)
Lemma sec_rm_set_zsum : forall (X : Type) (g : X -> Z) i x y l, nth_error l i = Some y ->
  zsum (map g (W_LLVMFuzzerTestOneInput_remove.rm_set_nth i x l)) + g y = zsum (map g l) + g x.
Proof.
  intros X g i. induction i as [|i IH]; intros x y [|z l] H; cbn in H; try discriminate.
  - injection H as ->. cbn. lia.
  - cbn [W_LLVMFuzzerTestOneInput_remove.rm_set_nth map fold_right]. specialize (IH x y l H). lia.
Qed.
Lemma sec_rm_pair : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  0 <= hs_off h /\
  (re_eof (rm_ent m j0) = 0 -> hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
  NoDup (texts (hs_held h)) /\
  same_set (drain_b_c.keys_texts (re_keys (rm_ent m j0))) (texts (hs_held h)) /\
  fr_pair_cost (rm_ent m j0) (h, si) < 2 ^ 26 /\ hl_recs (hs_expected h) = [] /\
  (re_eof (rm_ent m j0) = 0 -> re_skip (rm_ent m j0) = hs_overlong h /\
     (re_skip (rm_ent m j0) = 0 -> bzs (re_U (rm_ent m j0)) = bzs (hs_W h))) /\
  (re_skip (rm_ent m j0) = 0 \/ re_skip (rm_ent m j0) = 1).
Proof.
  intros cx t m si h j0 HRI Hat HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  destruct HP as (_ & _ & _ & Hre & Hss & Hnd & Hexp & _ & _ & _ & Hoff). cbn [fst snd] in *.
  destruct HE as (_ & _ & _ & _ & Hsk01).
  assert (Hc' : fr_pair_cost (rm_ent m j0) (h, si) < 2 ^ 26) by lia.
  refine (conj Hoff (conj _ (conj Hnd (conj Hss (conj Hc' (conj Hexp (conj Hre Hsk01))))))).
  intros Ho. destruct (Hre Ho) as (Hsk & HskU). exact (sec_hsW _ h Hsk HskU Hsk01 HU).
Qed.

(* relay_remove's largest request: drain's (dpre_dr_tr_max), the gesture ends of the keys it leaves (rrp_ker_lens,
   from g_nout <= the pair's cost), two frees (the proof of brr_rm_rr_pre_c2, kf-b6's lib/B/ReplyLSBRrPre.v, which the
   window deleted) *)
Lemma sec_rm_tr_max : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  tr_max (rm_rr_tr m h) < fr_MMAX.
Proof.
  intros cx t m si h j0 HRI Hat Ht HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & Hc & Hn).
  pose proof Hat as (_ & HO & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & Hexp & _ & _ & Hpe & Hoff). cbn [fst snd] in Hre, Hexp, Hpe, Hoff.
  destruct HE as (_ & _ & _ & _ & Hsk).
  unfold fr_pair_cost in Hc. cbn [fst] in Hc.
  pose proof (fr_keys_total_nonneg (re_keys (rm_ent m j0))) as HKT0.
  pose proof (dpre_keys_le (re_keys (rm_ent m j0))) as Hkl.
  assert (HX0 : 0 <= (if re_skip (rm_ent m j0) =? 0 then Z.of_nat (length (re_U (rm_ent m j0))) else 0))
    by (destruct (re_skip (rm_ent m j0) =? 0); lia).
  pose proof fr_MMAX_val as EM.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr, rr_tr. cbv beta zeta.
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  destruct (hs_fd h <? 0); cbv iota; [unfold tr_max; cbn [fold_right]; lia|].
  rewrite Hfind. cbv beta iota zeta.
  destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo; cbv iota.
  - (* open: drain's own trace, then the gesture ends of the keys it leaves, then two frees *)
    apply Z.eqb_eq in Eo.
    assert (HA : tr_max (dr_tr (lm_c m) (lm_mx m) 0 (lm_cap m) (rm_ent m j0) h) < fr_MMAX).
    { destruct (Hre Eo) as (S1 & W1). apply dpre_dr_tr_max.
      - exact HU.
      - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia.
      - exact Hoff.
      - exact Hexp.
      - lia.
      - unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia. }
    rewrite tr_max_app'.
    match goal with |- Z.max _ (tr_max ?KF) < _ => assert (HB : tr_max KF <= fr_MMAX - 1) end.
    { apply dpre_tr_max; [lia|]. apply Forall_app. split.
      - apply rrp_ker_lens. unfold dr_fin.
        pose proof (rm3_no_fin (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h Hoff) as NF.
        pose proof (rrp_fin_kw (dr_live (lm_c m) h) (lm_mx m) (lm_cap m) (rm_ent m j0) h) as KW.
        rewrite (rm3_skip_if (re_skip (rm_ent m j0)) (Z.of_nat (length (re_U (rm_ent m j0)))) Hsk) in NF.
        lia.
      - apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil. }
    lia.
  - (* at eof: no drain; the gesture ends of the entry's own keys from g_nout = 0, then two frees *)
    rewrite app_nil_l.
    apply (Z.le_lt_trans _ (fr_MMAX - 1)); [|lia].
    apply dpre_tr_max; [lia|]. apply Forall_app. split.
    + apply rrp_ker_lens. cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_H].
      rewrite <- rm3_kt_kw. lia.
    + apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
Qed.

Lemma sec_rm_rr : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  21 * nsec_tr (rm_rr_tr m h) <=
  21 * 60 + Z.of_nat (length (re_U (rm_ent m j0))) + Z.of_nat (length (pending_stream h)).
Proof.
  intros cx t m si h j0 HRI Hat Ht HU.
  pose proof Hat as (_ & _ & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  destruct (sec_rm_pair cx t m si h j0 HRI Hat HU) as (Hoff & HW & _).
  assert (HFD : 0 <= hs_fd h).
  { destruct HRI as (_ & (_ & _ & Hrng & _) & _). rewrite Forall_forall in Hrng.
    assert (Hin : In (rm_ent m j0) (lm_es m))
      by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply nth_In; exact Hj0).
    specialize (Hrng _ Hin). lia. }
  pose proof (sec_rm_tr_max cx t m si h j0 HRI Hat Ht HU) as HM. rewrite fr_MMAX_val in HM.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr in HM |- *.
  pose proof (sec_rr60 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (hs_fd h) (lm_es m) h
                (rm_ent m j0) HFD Hfind (fun Ho => conj Hoff (HW Ho)) ltac:(lia)) as K.
  destruct (re_eof (rm_ent m j0) =? 0); lia.
Qed.

(* what relay_remove leaves of the source h1 (rm_rr_ok: drain's dr_rel when the entry is open, h1 = h at eof):
   check_no_loss over it costs at most 15 *)
Lemma sec_rm_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> rm_at cx m si h j0 -> rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  cnl_cost MT (hs_expected h1) (hs_held h1) <= 15.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU.
  destruct (sec_rm_pair cx t m si h j0 HRI Hat HU) as (_ & HW & Hnd & Hss & Hcost & Hexp & Hre & Hsk01).
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_ok in Hrr. cbv zeta in Hrr. destruct Hrr as (Hd & _).
  destruct (Z.eqb_spec (re_eof (rm_ent m j0)) 0) as [E0|E1]; cbv iota in Hd.
  - destruct Hd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmap & _ &
      Hheld & _).
    destruct (Hre E0) as (Hsk & HskU).
    pose proof (HW E0) as HW0.
    pose proof (dr3_lines h) as (_ & HLw & HZr & _).
    pose proof (dr3_wcost (rm_ent m j0) h Hsk HskU Hsk01) as Hwc.
    assert (Hc : hl_n (hs_held h) + Z.of_nat (count_begin (dr_lines h)) < 2 ^ 25).
    { apply (sec_cnl_count (rm_ent m j0) (h, si) (hs_held h) (dr_lines h) Hnd Hss); [|exact Hcost].
      cbn [fst]. rewrite Hwc in HLw. exact HLw. }
    exact (sec_cnl_lines h h1 Hc Hexp HZr (sec_lines6 h HW0) Hmap Hheld).
  - destruct Hd as (_ & ->). unfold cnl_cost. rewrite Hexp. cbn [cnl_go]. lia.
Qed.

(* top_x LS_rm_rr_pre's meter conjunct *)
Lemma fr_SEC_rm_rr_pre_a : forall cx t m ly S si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  fr_SEC cx t m ly S -> mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h).
Proof.
  intros cx t m ly S si h j0 HRI Hat Ht HU H.
  pose proof (sec_rm_rr cx t m si h j0 HRI Hat Ht HU) as K.
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  assert (Hej : nth_error (lm_es m) j0 = Some (rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply nth_error_nth'; exact Hj0).
  pose proof (sec_ub_pair m si h j0 _ Hh Hej) as P.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost. rewrite sec_tr.
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia |].
  lia.
Qed.

(* the remove's rows after relay_remove: S is at most rr + (cnl) + (cshe = 0) past S0 *)
Lemma fr_SEC_rm_after : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 X c,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  nsec S <= nsec S0 + nsec_tr (rm_rr_tr m h) + X ->
  X + c <= cnl_cost MT (hs_expected h1) (hs_held h1) ->
  fr_SEC cx t m ly0 S0 -> mo_ok MT S c.
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 X c HRI Hat Hrr Ht HU HS HX H.
  pose proof (sec_rm_rr cx t m si h j0 HRI Hat Ht HU) as K.
  pose proof (sec_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU) as Kc.
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  assert (Hej : nth_error (lm_es m) j0 = Some (rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply nth_error_nth'; exact Hj0).
  pose proof (sec_ub_pair m si h j0 _ Hh Hej) as P.
  apply (fr_SEC_ok HKC cx t m ly0 S0 S (nsec_tr (rm_rr_tr m h) + X) c H); [lia | lia].
Qed.

(* top_x LS_rm_step *)
Lemma fr_SEC_rm_step_a : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ev5,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h +
                 (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) +
                 (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  fr_SEC cx t m ly0 S0 ->
  fr_SEC cx (t + 1) (rm_mk cx m si None j0 (rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ev5 HRI Hat Hrr Hmo Ht HU HS.
  pose proof (sec_rm_rr cx t m si h j0 HRI Hat Ht HU) as K.
  pose proof (sec_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU) as Kc.
  change (nsec S <= nsec S0 + (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
            W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
            W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H' +
            sr_cost MT (Some (set_held (set_exp_held h1 E' H') H'')))) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost, W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost,
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost in Hmo.
  rewrite sec_tr, sec_cshe, sec_sr in Hmo.
  apply (fr_SEC_step cx t m _ ly0 S0 ly S
           (nsec_tr (rm_rr_tr m h) + cnl_cost MT (hs_expected h1) (hs_held h1))
           Ht ltac:(lia)); [|exact HS].
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  unfold sec_ub. cbn [W_LLVMFuzzerTestOneInput_remove.rm_mk lm_hs lm_es].
  pose proof (sec_rm_set_zsum _ sec_str si None (Some h) (lm_hs m) Hhi) as Zp.
  pose proof (fr_sum_perm _ pt_eu _ _ (fr_remove_perm _ (lm_es m) j0 relay_remove_b_c.no_entry Hj0)) as Pe.
  cbn [map fold_right] in Pe.
  assert (E1 : sec_str (Some h) = Z.of_nat (length (pending_stream h))) by reflexivity.
  assert (N1 : sec_str None = 0) by reflexivity.
  assert (Eu : pt_eu (nth j0 (lm_es m) relay_remove_b_c.no_entry) =
               Z.of_nat (length (re_U (nth j0 (lm_es m) relay_remove_b_c.no_entry)))) by reflexivity.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_ent in K.
  destruct (SEC_RATE_ge HKC) as (R1 & _). lia.
Qed.

(* ---- exit: relay_finish's requests (kf_rf_cost, 15); check_shape_ends' and source_reset's are frees.  The count
   reads relay_finish's room (the B top's LS_rf_room, at 0 <= t <= OPS_MAX) and the entries' keys not empty:
   premises here ---- *)
(* W_bx_defs' lx_rf_* are W_contract's rf_* (lib/B/W_bx_rf.v xrf_cost_eq / xrf_room_eq, the same inductions) *)
Lemma sec_xrf_cost : forall es c O mx no cap,
  W_bx_defs.lx_rf_cost MT c O mx no cap es = rf_cost MT c O mx no cap es.
Proof.
  induction es as [|e es IH]; intros c O mx no cap; [reflexivity|].
  cbn [W_bx_defs.lx_rf_cost rf_cost]. rewrite IH. reflexivity.
Qed.
Lemma sec_xrf_room : forall MMAX es bb c O mx no cap,
  W_bx_defs.lx_rf_room MMAX bb c O mx no cap es -> rf_room MMAX bb c O mx no cap es.
Proof.
  intros MMAX. induction es as [|e es IH]; intros bb c O mx no cap H; [exact I|].
  cbn [W_bx_defs.lx_rf_room rf_room] in *. destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
Lemma sec_exit_cost : forall m bb,
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX bb (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  W_bx_defs.lx_exit_cost MT m <= 15.
Proof.
  intros m bb Hroom Hk. unfold W_bx_defs.lx_exit_cost. rewrite sec_ends, sec_srt, sec_xrf_cost.
  pose proof (sec_xrf_room _ _ _ _ _ _ _ _ Hroom) as R.
  pose proof (ReplyKfTrSmB.kf_rf_cost MT sec_HMs sec_HFs CfParamsReply.fr_MMAX bb (lm_c m) [] (lm_mx m) 0 (lm_cap m)
                (lm_es m) CfParamsReply.reply_HMMAX Hk R) as K.
  assert (K2 : ReplyKfTrSmB.KC_rf = 15) by reflexivity. lia.
Qed.
(* top_x LS_exit_budget *)
Lemma fr_SEC_exit_budget_a : forall cx t m ly S,
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_SEC cx t m ly S -> mo_ok MT S (W_bx_defs.lx_exit_cost MT m).
Proof.
  intros cx t m ly S Hroom Hk H. pose proof (sec_exit_cost m _ Hroom Hk) as K. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.
(* top_x LS_exit_end's meter conjunct: the call's count at its end, freeing the frame (set_fs) does not change nsec *)
Lemma fr_SEC_exit_end_a : forall cx t m ly3 S3 (S' : astate) C fpos,
  (forall f s, nsec (set_fs f s) = nsec s) ->
  mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S3) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_SEC cx t m ly3 S3 -> nsec (stack_free_state 1 fpos S') <= nsec (c_S cx) + SEC_CALL.
Proof.
  intros cx t m ly3 S3 S' C fpos HNS Hmo HC Hroom Hk H. change (nsec S' <= nsec S3 + C) in Hmo.
  pose proof (sec_exit_cost m _ Hroom Hk) as K. pose proof (sec_ub_nonneg m).
  unfold stack_free_state. rewrite HNS.
  apply (fr_SEC_bound HKC cx t m ly3 S3 (nsec S') H). lia.
Qed.
End keep.
End sec.

(* ================================================================== fr_SEC over the gone operation *)
(* A's lib/A/ReplyLSsecGn.v: GN_LS_rig's meter conjunct, GN_RI_step's two meter conjuncts and GN_RI_end's fr_SEC, at
   gone_base's KF-COUNT text (the binder q, gn_runc, gn_cst).
   - relay_instance_gone's requests: lane B's ReplyKfTrRigB.kf_rig (KC_rig = 180) at gn_rigc's own pairs, its premises
     from gone's REQ2 / REQ3 (gx_pf_all), paid by the open pairs' bytes (sec_osum_in); GN_LS_rig has no re_cap, so
     there sec_rig45 (240).  gn_rigc's pairs and the rule's give the same open sources (sec_osum_same: the slots'
     fds are distinct, RI_fds_holds).
   - the loop's requests q: one check_no_loss per call, at most 15 at a drained slot and 0 at an untouched one (its
     expected list is empty), so q plus every slot's remaining charge is the slots' charge after the rig (sec_runc),
     at most 4 * 15 (sec_F_m1).
   - the bytes: the rig consumes every open pair's pending stream and partial line and leaves dr_fin's partial line
     (sec_ub_gone). *)

(* ---- lib/B/ReplyB3LS3Peak.v's pk_zsum_perm / pk_zsum_nodup_le / pk_zsum_seq / pk_slots_cons / pk_gp, their texts
   and proofs (that file Requires ReplyLS3B_inst.v) ---- *)
Definition sec_gp (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then Z.of_nat (length (pending_stream (fst (snd p)))) else 0.
Lemma sec_zsum_perm : forall (g : nat -> Z) l l', Permutation l l' -> zsum (map g l) = zsum (map g l').
Proof. intros g l l' HP. induction HP; cbn [map fold_right]; lia. Qed.
Lemma sec_zsum_nodup_le : forall (g : nat -> Z) A Bl, (forall i, 0 <= g i) -> List.NoDup A -> incl A Bl ->
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
    rewrite (sec_zsum_perm g (l1 ++ a :: l2) (a :: l1 ++ l2) (Permutation_sym (Permutation_middle l1 l2 a))).
    cbn [map fold_right]. lia.
Qed.
Lemma sec_zsum_seq : forall (f : option hsrc -> Z) l,
  zsum (map (fun i => f (nth i l None)) (seq 0 (length l))) = zsum (map f l).
Proof.
  intros f l. induction l as [|x l IH]; [reflexivity|].
  cbn [length seq map fold_right nth]. rewrite <- seq_shift, map_map. cbn [nth]. rewrite IH. reflexivity.
Qed.
Lemma sec_slots_cons : forall e (hj : hsrc * nat) ps,
  rig_slots ((e, hj) :: ps) = (if re_eof e =? 0 then [snd hj] else []) ++ rig_slots ps.
Proof. intros e hj ps. unfold rig_slots. cbn [map concat]. reflexivity. Qed.

(* ================================================================== the open pairs' bytes *)
Lemma sec_osum_nonneg : forall (f : rentry -> hsrc -> Z) ps, (forall e h, 0 <= f e h) -> 0 <= osum f ps.
Proof.
  intros f ps Hf. induction ps as [|[e hj] ps IH].
  - unfold ReplyKfTrRigB.osum. cbn [map fold_right]. lia.
  - rewrite ReplyKfTrRigB.osum_cons. pose proof (Hf e (fst hj)). destruct (re_eof e =? 0); lia.
Qed.
Lemma sec_osum_split : forall ps, osum kf_in ps = osum (fun e _ => pt_eu e) ps + zsum (map sec_gp ps).
Proof.
  induction ps as [|[e hj] ps IH]; [reflexivity|].
  rewrite !ReplyKfTrRigB.osum_cons. cbn [map fold_right]. rewrite IH.
  change (sec_gp (e, hj)) with (if re_eof e =? 0 then Z.of_nat (length (pending_stream (fst hj))) else 0).
  unfold ReplyKfTrRigB.kf_in, pt_eu. destruct (re_eof e =? 0); lia.
Qed.
Lemma sec_osum_U : forall es (hs : list (hsrc * nat)), osum (fun e _ => pt_eu e) (combine es hs) <= zsum (map pt_eu es).
Proof.
  induction es as [|e es IH]; intros [|hj hs]; cbn [combine map fold_right].
  - unfold ReplyKfTrRigB.osum. cbn [map fold_right]. lia.
  - unfold ReplyKfTrRigB.osum. cbn [map fold_right]. lia.
  - unfold ReplyKfTrRigB.osum. cbn [map fold_right]. pose proof (pt_eu_nonneg e).
    pose proof (zsum_map_nonneg pt_eu es pt_eu_nonneg). lia.
  - rewrite ReplyKfTrRigB.osum_cons. pose proof (pt_eu_nonneg e). specialize (IH hs). destruct (re_eof e =? 0); lia.
Qed.
Section gpsl.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sec_gp_slots : forall m ps,
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps ->
  zsum (map sec_gp ps) = zsum (map (fun i => sec_str (nth i (lm_hs m) None)) (rig_slots ps)).
Proof.
  intros m. induction ps as [|[e hj] ps IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF].
  rewrite sec_slots_cons, map_app, zsum_app. cbn [map fold_right]. cbn [fst snd] in H1.
  change (sec_gp (e, hj)) with (if re_eof e =? 0 then Z.of_nat (length (pending_stream (fst hj))) else 0).
  rewrite <- (IH HF).
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; cbn [map fold_right].
  - destruct (H1 Eo) as (_ & Hn & _). rewrite Hn.
    change (sec_str (Some (fst hj))) with (Z.of_nat (length (pending_stream (fst hj)))). lia.
  - lia.
Qed.
Lemma sec_gp_le : forall m ps, length (lm_hs m) = 4%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) ps -> List.NoDup (rig_slots ps) ->
  zsum (map sec_gp ps) <= zsum (map sec_str (lm_hs m)).
Proof.
  intros m ps Hl HF HND. rewrite (sec_gp_slots m ps HF).
  rewrite <- (sec_zsum_seq sec_str (lm_hs m)).
  apply sec_zsum_nodup_le; [intros i; apply sec_str_nonneg | exact HND |].
  intros i Hi. unfold rig_slots in Hi. apply in_concat in Hi as (l & Hl' & Hil).
  apply in_map_iff in Hl' as (p & <- & Hp).
  destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Eo|Eo]; [|destruct Hil].
  destruct Hil as [<- | []].
  destruct (proj1 (Forall_forall _ _) HF p Hp Eo) as (H4 & _).
  apply in_seq. rewrite Hl. lia.
Qed.
(* the open pairs' bytes are within sec_ub *)
Lemma sec_osum_in : forall m hs, length (lm_hs m) = 4%nat -> gn_pairs m hs ->
  osum kf_in (combine (lm_es m) hs) <= sec_ub m.
Proof.
  intros m hs Hl (_ & HF & HND). rewrite sec_osum_split.
  pose proof (sec_osum_U (lm_es m) hs). pose proof (sec_gp_le m _ Hl HF (proj1 (NoDup_ListNoDup _) HND)).
  unfold sec_ub. lia.
Qed.
(* the open entries' sources are the same at any two pairings (the open slots' fds are distinct) *)
Lemma sec_osum_same : forall cx t m (f : rentry -> hsrc -> Z) hs hs',
  fr_RINV cx t m -> gn_pairs m hs -> gn_pairs m hs' ->
  osum f (combine (lm_es m) hs) = osum f (combine (lm_es m) hs').
Proof.
  intros cx t m f hs hs' HRI (Hl & HF & _) (Hl' & HF' & _).
  assert (G : forall es (hs1 hs1' : list (hsrc * nat)), length hs1 = length es -> length hs1' = length es ->
    Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) (combine es hs1) ->
    Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) (combine es hs1') ->
    osum f (combine es hs1) = osum f (combine es hs1')).
  { induction es as [|e es IH]; intros [|hj hs1] [|hj' hs1'] L L' F F'; cbn [length] in L, L'; try lia.
    cbn [combine] in F, F' |- *. apply Forall_cons_iff in F as [F0 F]. apply Forall_cons_iff in F' as [F0' F'].
    rewrite !ReplyKfTrRigB.osum_cons. rewrite (IH hs1 hs1' ltac:(lia) ltac:(lia) F F').
    destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; [|reflexivity].
    cbn [fst snd] in F0, F0'. destruct (F0 Eo) as (Hj & Hn & Hfd & _). destruct (F0' Eo) as (Hj' & Hn' & Hfd' & _).
    assert (Ej : snd hj = snd hj').
    { destruct (Nat.eq_dec (snd hj) (snd hj')) as [E|E]; [exact E|].
      exfalso. exact (RI_fds_holds cx t m (snd hj) (snd hj') (fst hj) (fst hj') HRI Hj Hj' E Hn Hn'
                        ltac:(congruence)). }
    rewrite Ej in Hn. rewrite Hn in Hn'. injection Hn' as E. rewrite E. reflexivity. }
  exact (G (lm_es m) hs hs' Hl Hl' HF HF').
Qed.
End gpsl.

(* the open pairs' facts give lane B's drain premises *)
Lemma sec_pf_pre : forall p, gx_pf p -> ReplyKfTrRigB.kf_dr_pre (fst p) (fst (snd p)).
Proof.
  intros [e [h j]] (_ & _ & Hoff & Hsk & HskU & Hsk01 & (Hce & HU & _) & _). cbn [fst snd] in *.
  refine (conj Hoff (conj (sec_hsW e h Hsk HskU Hsk01 HU) (conj Hce _))). unfold APARTIAL in HU. lia.
Qed.

(* ================================================================== the loop's check_no_loss charges *)
Section gn.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable nsec : astate -> Z.
Variable KMAX : Z.
Variable KC : Z.
Local Notation MT := (MT_sec nsec KMAX).

Definition sec_c (o : option hsrc) : Z :=
  match o with Some h => cnl_cost MT (hs_expected h) (hs_held h) | None => 0 end.
Definition sec_F (hs : list (option hsrc)) : Z :=
  sec_c (nth 0 hs None) + sec_c (nth 1 hs None) + sec_c (nth 2 hs None) + sec_c (nth 3 hs None).

Lemma sec_c_nonneg : forall o, 0 <= sec_c o.
Proof. intros [h|]; cbn [sec_c]; [apply sec_cnl_nonneg | lia]. Qed.
Lemma sec_F_nonneg : forall hs, 0 <= sec_F hs.
Proof.
  intros hs. unfold sec_F. pose proof (sec_c_nonneg (nth 0 hs None)). pose proof (sec_c_nonneg (nth 1 hs None)).
  pose proof (sec_c_nonneg (nth 2 hs None)). pose proof (sec_c_nonneg (nth 3 hs None)). lia.
Qed.
Lemma sec_c_empty : forall h, hl_recs (hs_expected h) = [] -> sec_c (Some h) = 0.
Proof. intros h E. cbn [sec_c]. unfold cnl_cost. rewrite E. reflexivity. Qed.
Lemma sec_F_ge : forall hs k h, (k < 4)%nat -> nth k hs None = Some h -> sec_c (Some h) <= sec_F hs.
Proof.
  intros hs k h Hk Hh. unfold sec_F. pose proof (sec_c_nonneg (nth 0 hs None)).
  pose proof (sec_c_nonneg (nth 1 hs None)). pose proof (sec_c_nonneg (nth 2 hs None)).
  pose proof (sec_c_nonneg (nth 3 hs None)).
  destruct k as [|[|[|[|k]]]]; [| | | | lia]; rewrite <- Hh; lia.
Qed.
Lemma sec_nth_lt : forall (l : list (option hsrc)) k h, nth k l None = Some h -> (k < length l)%nat.
Proof.
  intros l k h E. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [exact L|].
  rewrite nth_overflow in E by exact L. discriminate.
Qed.
Lemma sec_F_set : forall hs k x, (k < 4)%nat -> (k < length hs)%nat ->
  sec_F (W_LLVMFuzzerTestOneInput_gone_base.gn_setn k x hs) = sec_F hs - sec_c (nth k hs None) + sec_c x.
Proof.
  intros hs k x Hk Hl. unfold sec_F.
  destruct k as [|[|[|[|k]]]]; [| | | | lia];
    rewrite ?(gx_setn_same _ x hs Hl); rewrite ?gx_setn_other by discriminate; lia.
Qed.

(* q plus the slots' remaining charges is their charge after the rig *)
Lemma sec_runc : forall P m1 mc A i k q, W_LLVMFuzzerTestOneInput_gone_base.gn_runc MT P m1 mc A i k q ->
  q + sec_F (lm_hs mc) = sec_F (lm_hs m1).
Proof.
  intros P m1 mc A i k q H.
  induction H as [|mc A i k q Hr IH Hk Hs|mc A i k q h h' h'' E' H' ds c Hr IH Hk Hi Hh Hfd Hcnl Hcshe
                  |mc A i q Hr IH].
  - lia.
  - exact IH.
  - cbn [W_LLVMFuzzerTestOneInput_gone_base.gn_set lm_hs].
    rewrite (sec_F_set (lm_hs mc) k (Some h'') Hk (sec_nth_lt _ _ _ Hh)), Hh.
    destruct Hcnl as (Eh' & HrE & _). destruct Hcshe as (H'' & Eh'' & _).
    assert (Z0 : sec_c (Some h'') = 0).
    { apply sec_c_empty. rewrite Eh'', Eh'. cbn [set_held set_exp_held hs_expected]. exact HrE. }
    assert (Z1 : sec_c (Some h) = cnl_cost MT (hs_expected h) (hs_held h)) by reflexivity.
    rewrite (sec_cshe nsec KMAX). lia.
  - exact IH.
Qed.

(* a slot the rig drained: its check_no_loss charge is at most 15 (sec_cnl_le) *)
Lemma sec_c_drained : forall cx t m k (e : rentry) h0 h1 c mx no cap e1 LB,
  fr_RINV cx t m -> (k < 4)%nat -> nth k (lm_hs m) None = Some h0 -> gx_pf (e, (h0, k)) ->
  dr_rel c mx no cap e h0 e1 h1 LB -> sec_c (Some h1) <= 15.
Proof.
  intros cx t m k e h0 h1 c mx no cap e1 LB HRI Hk Hh Hpf Hdr.
  destruct Hpf as (Hexp & _ & _ & Hsk & HskU & Hsk01 & Hepre & _ & _ & Hps). cbn [fst snd] in *.
  destruct Hepre as (_ & HU & _).
  destruct (gx_rinv_slot cx t m k h0 HRI Hk Hh) as (_ & _ & _ & _ & Hnd & e2 & Hss & Hkt).
  destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hdr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmap & Hheld & _).
  destruct (gx_exp_lines _ _ _ _ _ _ _ _ _ Hdr Hexp) as (HT & _).
  pose proof (sec_hsW e h0 Hsk HskU Hsk01 HU) as HW.
  pose proof (dr3_lines h0) as (_ & HLw & _ & _).
  pose proof (dr3_wcost e h0 Hsk HskU Hsk01) as Hwc.
  cbn [sec_c]. apply (sec_cnl_le nsec KMAX).
  - rewrite HT, Hheld.
    pose proof (sec_held_keys (re_keys e2) (hs_held h0) Hnd Hss) as A.
    pose proof (rm3_kt_len (re_keys e2)) as K.
    pose proof (SlotReads.count_begin_bytes (dr_lines h0)) as C.
    rewrite Hwc in HLw. unfold APARTIAL in HU. destruct (re_skip e =? 0); lia.
  - rewrite Hexp in Hmap. cbn [map app] in Hmap.
    exact (sec_recs_short (hs_expected h1) (dr_lines h0) Hmap (sec_lines6 h0 HW)).
Qed.

(* the slots' charges after the rig: at most 4 * 15 *)
Lemma sec_F_m1 : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 -> gx_xpre m hs -> sec_F (lm_hs m1) <= 60.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hr HX.
  assert (Hk : forall k, (k < 4)%nat -> sec_c (nth k (lm_hs m1) None) <= 15).
  { intros k Hk. destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hr HX k Hk) as
      [E | (e & h0 & h1 & c & mx & no & cap & e1 & LB & i & H0 & H1 & Hpf & Hdr & _)].
    - rewrite E. destruct (nth k (lm_hs m) None) as [h|] eqn:Eh; [|cbn [sec_c]; lia].
      destruct (gx_rinv_slot cx t m k h HRI Hk Eh) as (Hexp & _). rewrite (sec_c_empty h Hexp). lia.
    - rewrite H1. exact (sec_c_drained cx t m k e h0 h1 c mx no cap e1 LB HRI Hk H0 Hpf Hdr). }
  unfold sec_F. pose proof (Hk 0%nat ltac:(lia)). pose proof (Hk 1%nat ltac:(lia)).
  pose proof (Hk 2%nat ltac:(lia)). pose proof (Hk 3%nat ltac:(lia)). lia.
Qed.

(* ================================================================== the bytes over the gone operation *)
Lemma sec_rig_U : forall pre mx ps qs c O cap c2 O2 cap2 c0 mx0 no0 cap0,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  zsum (map (fun q => pt_eu (fst q)) qs) =
  zsum (map (fun p => if re_eof (fst p) =? 0 then kf_tail c0 mx0 no0 cap0 (fst p) (fst (snd p))
                      else pt_eu (fst p)) ps).
Proof.
  intros pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs c O cap c2 O2 cap2 c0 mx0 no0 cap0 HR.
  - destruct qs as [|q qs]; cbn [rig_rel] in HR; [reflexivity | contradiction].
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] eqn:ES end.
    cbn [map fold_right fst snd]. rewrite (IH q c3 O3 cap3 c2 O2 cap2 c0 mx0 no0 cap0 Hrest).
    subst e'. assert (EU : pt_eu (entry_keys e1 (snd (geik pre (re_keys e1)))) = pt_eu e1) by reflexivity.
    rewrite EU. revert Hd. destruct (re_eof e =? 0) eqn:Eo; intros Hd.
    + destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hd) as (_ & _ & HU' & _).
      assert (ET : pt_eu e1 = kf_tail c0 mx0 no0 cap0 e h).
      { unfold pt_eu. rewrite <- (SlotReads.bzs_length (re_U e1)), HU'. unfold dr_fin.
        exact (ReplyKfTrRigB.kf_tail_fin c0 mx0 no0 cap0 _ _ _ _ e h). }
      lia.
    + destruct Hd as [-> ->]. lia.
Qed.
Lemma sec_tail_split : forall (g : rentry -> hsrc -> Z) ps,
  zsum (map (fun p => if re_eof (fst p) =? 0 then g (fst p) (fst (snd p)) else pt_eu (fst p)) ps) =
  zsum (map (fun p => pt_eu (fst p)) ps) - osum (fun e _ => pt_eu e) ps + osum g ps.
Proof.
  intros g. induction ps as [|[e hj] ps IH]; [reflexivity|].
  cbn [map fold_right fst snd]. rewrite !ReplyKfTrRigB.osum_cons, IH. destruct (re_eof e =? 0); lia.
Qed.

(* the rig consumes the open pairs' bytes and leaves the drains' partial lines; the loop keeps every pending stream *)
Lemma sec_ub_gone : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gx_xpre m hs -> gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_run (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A
    (length (lm_es m1)) 0%nat ->
  sec_ub mc + osum kf_in (combine (lm_es m) hs) =
  sec_ub m + osum (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)) (combine (lm_es m) hs).
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI HX Hpairs Hafter Hrok Hrun.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & Hfds).
  pose proof HRI as (_ & (Hl4 & _) & _).
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  pose proof (sec_rig_U _ _ _ _ _ _ _ _ _ _ (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) Hrr) as HU.
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R5 & R6 & _ & _ & _ & R7 & Hhist & _).
  (* the loop keeps every slot's pending stream *)
  assert (Hs1 : zsum (map sec_str (lm_hs mc)) = zsum (map sec_str (lm_hs m1))).
  { rewrite (gx_sum4 sec_str (lm_hs mc) ltac:(lia)), (gx_sum4 sec_str (lm_hs m1) A11).
    assert (Hk : forall k', sec_str (nth k' (lm_hs mc) None) = sec_str (nth k' (lm_hs m1) None)).
    { intros k'. destruct (Hhist k') as [L | (h0 & h2 & i0 & X1 & X2 & X3 & _)]; [rewrite L; reflexivity|].
      rewrite X1, X2.
      destruct X3 as (h' & E' & H' & P & g & A0 & ob & ds & c & (E1 & _) & (H'' & E2 & _)).
      subst. reflexivity. }
    rewrite !Hk. reflexivity. }
  (* relay_instance_gone empties the drained slots' pending lists and keeps the others *)
  assert (HALL : Forall (fun pq => re_eof (fst (fst pq)) = 0 ->
            nth (snd (snd (fst pq))) (lm_hs m) None = Some (fst (snd (fst pq))) /\
            nth (snd (snd (fst pq))) (lm_hs m1) None = Some (snd (snd pq)) /\
            sec_str (Some (snd (snd pq))) = 0) (combine ps qs)).
  { rewrite Forall_forall in HPQ, HRP |- *. intros [p q] Hin Heof. cbn [fst snd] in Heof |- *.
    destruct (HPQ (p, q) Hin Heof) as (_ & Q2 & Q3). cbn [fst snd] in Q2, Q3.
    destruct (HRP (p, q) Hin) as (_ & Hdr). cbn [fst snd] in Hdr.
    destruct (Hdr Heof) as (c' & mx' & no & cap' & e1 & LB & D).
    destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ D) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Dp & _).
    split; [exact Q2|]. split; [exact Q3|].
    change (sec_str (Some (snd q))) with (Z.of_nat (length (pending_stream (snd q)))).
    unfold pending_stream. rewrite Dp. reflexivity. }
  set (F := fun j => sec_str (nth j (lm_hs m1) None) - sec_str (nth j (lm_hs m) None)).
  assert (S1 : zsum (map sec_str (lm_hs m1)) - zsum (map sec_str (lm_hs m)) = F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { unfold F. rewrite (gx_sum4 sec_str (lm_hs m1) A11), (gx_sum4 sec_str (lm_hs m) Hl4). lia. }
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
               zsum (map (fun pq => - sec_gp (fst pq)) (combine ps qs))).
  { apply (gx_sum_ext _ _ _ _ HALL). intros [p q] Hpq. cbn [fst snd] in Hpq |- *. unfold sec_gp.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (Hm & Hm1 & P2).
    unfold F. rewrite Hm, Hm1, P2.
    change (sec_str (Some (fst (snd p)))) with (Z.of_nat (length (pending_stream (fst (snd p))))). lia. }
  rewrite ou_zsum_opp, <- (gx_sum_cfst sec_gp ps qs Hlps) in S3.
  (* the entries: the drained ones' partial lines are dr_fin's *)
  assert (EU : zsum (map pt_eu (lm_es mc)) = zsum (map (fun q => pt_eu (fst q)) qs))
    by (rewrite R5, A3, map_map; reflexivity).
  assert (EE : zsum (map pt_eu (lm_es m)) = zsum (map (fun p => pt_eu (fst p)) ps))
    by (exact (gx_sum_cfst pt_eu (lm_es m) hs ltac:(lia))).
  rewrite sec_tail_split in HU.
  pose proof (sec_osum_split ps) as SP.
  unfold sec_ub. lia.
Qed.

(* ================================================================== the rows and the rules *)
Section rules.
Hypothesis HKC : 240 <= KC.
Variable B : asyms.
Local Notation fr_SEC := (fr_SEC nsec KMAX KC).

(* lane B's rig count at gn_rigc's (or any) pairing, with gone's premises *)
Lemma sec_rig_at : forall cx t m ly S hs',
  fr_LS3c B CR cx t m ly S -> fr_RINV cx t m -> gn_op cx t m -> gx_xpre m hs' -> gn_pairs m hs' ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  21 * nsec_tr (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs') +
    osum (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)) (combine (lm_es m) hs') <=
  21 * 180 + osum kf_in (combine (lm_es m) hs').
Proof.
  intros cx t m ly S hs' HLS HRI Hop HX Hp HU.
  pose proof Hop as (_ & HO & Ht & _).
  destruct (ReplyLSBRig.brig_pairs cx t m hs' HRI Hp Ht HU) as (_ & _ & _ & Hlen).
  pose proof (ReplyB3LS3cTopxRig.fr_LS3c_gone_rig_c1 B CR cx t m ly S hs' HLS HRI Hp HO Ht HU) as HM.
  rewrite fr_MMAX_val in HM.
  pose proof (gx_pf_all cx t m hs' HRI Hp HX) as HPF.
  assert (HF : Forall (fun p => re_eof (fst p) = 0 -> ReplyKfTrRigB.kf_dr_pre (fst p) (fst (snd p)))
                 (combine (lm_es m) hs')).
  { eapply Forall_impl; [|exact HPF]. intros p Hp' Heof. exact (sec_pf_pre p (Hp' Heof)). }
  pose proof (ReplyKfTrRigB.kf_rig (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m)
                hs' Hlen HF ltac:(lia)) as K.
  assert (KK : ReplyKfTrRigB.KC_rig = 180) by reflexivity. lia.
Qed.

(* top_x GN_LS_rig_x's meter conjunct: no re_cap there, so sec_rig45 *)
Lemma fr_SEC_gone_rig_a : forall cx t m ly S hs,
  fr_LS3c B CR cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs -> gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  fr_SEC cx t m ly S ->
  mo_ok MT S (tr_cost MT (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Proof.
  intros cx t m ly S hs HLS HRI Hp Hop HU HS H.
  pose proof Hop as (_ & HO & Ht & _). pose proof HRI as (_ & (Hl4 & _ & _ & Hent & _) & _).
  destruct (ReplyLSBRig.brig_pairs cx t m hs HRI Hp Ht HU) as (_ & _ & _ & Hlen).
  pose proof (ReplyB3LS3cTopxRig.fr_LS3c_gone_rig_c1 B CR cx t m ly S hs HLS HRI Hp HO Ht HU) as HM.
  rewrite fr_MMAX_val in HM.
  assert (HF : Forall (fun p => re_eof (fst p) = 0 -> sec_dr_pre (fst p) (fst (snd p))) (combine (lm_es m) hs)).
  { pose proof Hp as (_ & HPok & _). rewrite Forall_forall in HPok |- *. intros [e hj] Hin Heof. cbn [fst snd] in *.
    destruct (HPok (e, hj) Hin Heof) as (Hj & Hn & _ & Hsk & HskU & _). cbn [fst snd] in *.
    assert (He : In e (lm_es m)) by exact (in_combine_l _ _ _ _ Hin).
    rewrite Forall_forall in Hent, HU. destruct (Hent e He) as (_ & _ & _ & _ & Hsk01).
    split.
    - destruct (HS _ _ Hn) as [(_ & E) | (r & rs & _ & E & _)]; lia.
    - exact (sec_hsW e (fst hj) Hsk HskU Hsk01 (HU e He)). }
  pose proof (sec_rig45 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs Hlen HF
                ltac:(lia)) as K.
  pose proof (sec_osum_in m hs Hl4 Hp) as Hin.
  pose proof (sec_osum_nonneg (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m))
                (combine (lm_es m) hs) ltac:(intros; unfold ReplyKfTrRigB.kf_tail; lia)) as T0.
  rewrite (sec_tr nsec KMAX).
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.

(* the gone operation's count so far at a call of the loop: the rig's (at gn_rigc's pairing) and the earlier calls' *)
Lemma sec_gone_so_far : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k (Sx : astate) cst q,
  fr_LS3c B CR cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_runc MT (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT cx m m1 q cst ->
  exists r, nsec Sx <= nsec S + r + q /\ 21 * r <= 21 * 180 + sec_ub m /\ q + sec_F (lm_hs mc) <= 60.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrunc Hmo
    Hcst.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hp) as HX.
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (HU : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m))
    by (eapply Forall_impl; [|exact HE6]; intros e He; exact (proj1 He)).
  destruct Hcst as (r & (hs' & qs' & c2' & O2' & cap2' & out2' & Hp' & _ & Er) & Hc).
  pose proof (gx_xpre_of6 cx t m hs' Hop HE Hcap HE6 HS6 Hp') as HX'.
  pose proof (sec_rig_at cx t m ly S hs' HLS HRI Hop HX' Hp' HU) as Kr.
  pose proof (sec_osum_in m hs' Hl4 Hp') as Hin.
  pose proof (sec_osum_nonneg (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m))
                (combine (lm_es m) hs') ltac:(intros; unfold ReplyKfTrRigB.kf_tail; lia)) as T0.
  pose proof (sec_F_m1 cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hrok HX) as HF1.
  pose proof (sec_runc _ m1 mc A _ _ q Hrunc) as HR.
  change (nsec Sx <= nsec S + cst) in Hmo. rewrite (sec_tr nsec KMAX) in Er.
  exists r. subst r. split; [lia|]. split; lia.
Qed.

(* GN_RI_step's cnl meter conjunct *)
Lemma fr_SEC_gone_cnl_a : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (Sx : astate) cst q,
  fr_LS3c B CR cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_runc MT (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT cx m m1 q cst ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some h ->
  fr_SEC cx t m ly S -> mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)).
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrunc Hmo
    Hcst Hk Hh H.
  destruct (sec_gone_so_far cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp
              Ha Hrok Hrunc Hmo Hcst) as (r & R1 & R2 & R3).
  pose proof (sec_F_ge (lm_hs mc) k h Hk Hh) as Hge.
  assert (Ec : sec_c (Some h) = cnl_cost MT (hs_expected h) (hs_held h)) by reflexivity.
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S Sx (r + q)); [exact H | lia | lia].
Qed.
(* GN_RI_step's cshe meter conjunct (check_shape_ends frees only) *)
Lemma fr_SEC_gone_cshe_a : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (Sx Sy : astate) cst q (h' : hsrc),
  fr_LS3c B CR cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_runc MT (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT cx m m1 q cst ->
  (k < 4)%nat -> nth k (lm_hs mc) None = Some h ->
  mo_le MT Sx Sy (cnl_cost MT (hs_expected h) (hs_held h)) ->
  fr_SEC cx t m ly S -> mo_ok MT Sy (hl_n (hs_held h') * mo_free MT).
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx Sy cst q h' HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok
    Hrunc Hmo Hcst Hk Hh Hmo2 H.
  destruct (sec_gone_so_far cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp
              Ha Hrok Hrunc Hmo Hcst) as (r & R1 & R2 & R3).
  pose proof (sec_F_ge (lm_hs mc) k h Hk Hh) as Hge.
  assert (Ec : sec_c (Some h) = cnl_cost MT (hs_expected h) (hs_held h)) by reflexivity.
  change (nsec Sy <= nsec Sx + cnl_cost MT (hs_expected h) (hs_held h)) in Hmo2.
  rewrite (sec_HFs nsec KMAX), Z.mul_0_r.
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S Sy (r + q + cnl_cost MT (hs_expected h) (hs_held h))); [exact H | lia |].
  lia.
Qed.

(* GN_RI_end's fr_SEC *)
Lemma fr_SEC_gone_end_a : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst q,
  fr_LS3c B CR cx t m ly S -> fr_RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_run (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A
    (length (lm_es m1)) 0%nat ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_runc MT (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A
    (length (lm_es m1)) 0%nat q ->
  mo_le MT S Sx cst -> W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT cx m m1 q cst ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q HLS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrun Hrunc
    Hmo Hcst H.
  pose proof (gx_xpre_of6 cx t m hs Hop HE Hcap HE6 HS6 Hp) as HX.
  pose proof Hop as (_ & _ & Ht & _).
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (HU : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m))
    by (eapply Forall_impl; [|exact HE6]; intros e He; exact (proj1 He)).
  destruct Hcst as (r & (hs' & qs' & c2' & O2' & cap2' & out2' & Hp' & _ & Er) & Hc).
  pose proof (gx_xpre_of6 cx t m hs' Hop HE Hcap HE6 HS6 Hp') as HX'.
  pose proof (sec_rig_at cx t m ly S hs' HLS HRI Hop HX' Hp' HU) as Kr.
  rewrite (sec_osum_same cx t m kf_in hs' hs HRI Hp' Hp),
    (sec_osum_same cx t m (kf_tail (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)) hs' hs HRI Hp' Hp)
    in Kr.
  pose proof (sec_ub_gone cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI HX Hp Ha Hrok Hrun) as Hub.
  pose proof (sec_F_m1 cx t m hs qs c2 O2 cap2 out2 m1 HRI Hp Ha Hrok HX) as HF1.
  pose proof (sec_runc _ m1 mc A _ _ q Hrunc) as HR. pose proof (sec_F_nonneg (lm_hs mc)) as HF0.
  change (nsec Sx <= nsec S + cst) in Hmo. rewrite (sec_tr nsec KMAX) in Er. subst r.
  apply (fr_SEC_step nsec KMAX KC cx t m mc ly S lyx Sx
           (nsec_tr (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs') + q)
           Ht ltac:(lia)); [|exact H].
  destruct (SEC_RATE_ge KC HKC) as (R1 & _). lia.
Qed.

(* ---- the gone step's two meter conjuncts at lib/B/ReplyRINVB_gone.v's texts (Module RG, Section ri:
   RG.GN_RI_step_cnl_meter / RG.GN_RI_step_cshe_meter, the premise lists of gone_base's GN_RI_step), for any LS whose
   states carry fr_LS3c and fr_SEC (the B instance's LSI with fr_SEC, through sec_lsi_parts below) ---- *)
Lemma fr_SEC_GN_RI_step_cnl_meter : forall (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  (forall cx t m ly S, LS cx t m ly S -> fr_LS3c B CR cx t m ly S /\ fr_SEC cx t m ly S) ->
  ReplyRINVB_gone.RG.GN_RI_step_cnl_meter B MT LS fr_RINV.
Proof.
  intros LS HLS. unfold ReplyRINVB_gone.RG.GN_RI_step_cnl_meter.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20.
  destruct (HLS cx t m ly S P7) as (H3c & HS).
  exact (fr_SEC_gone_cnl_a cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx cst q H3c P1 P2 P3 P4 P5 P6 P8 P9 P10
           P12 P13 P14 P17 P18 HS).
Qed.
Lemma fr_SEC_GN_RI_step_cshe_meter : forall (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  (forall cx t m ly S, LS cx t m ly S -> fr_LS3c B CR cx t m ly S /\ fr_SEC cx t m ly S) ->
  ReplyRINVB_gone.RG.GN_RI_step_cshe_meter B MT LS fr_RINV.
Proof.
  intros LS HLS. unfold ReplyRINVB_gone.RG.GN_RI_step_cshe_meter.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst q
    P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 h' E' H' Sy Hc Hm.
  destruct (HLS cx t m ly S P7) as (H3c & HS).
  exact (fr_SEC_gone_cshe_a cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h Sx Sy cst q h' H3c P1 P2 P3 P4 P5 P6 P8
           P9 P10 P12 P13 P14 P17 P18 Hm HS).
Qed.
End rules.
End gn.

(* ================================================================== the B instance's parts these lemmas read *)
(* LSI with fr_SEC (lib/B/ReplyLS3B_inst.v LSI B OM C at C := fun cx t m ly S => ReplyB3LScap.fr_CAP cx t m ly S /\
   fr_SEC nsec KMAX KC cx t m ly S, written out: fr_LS3cp /\ fr_OUT /\ fr_ENT /\ (fr_CAP /\ fr_SEC)) gives fr_LS3c and
   fr_SEC; an LSI hypothesis is this premise up to unfolding, so `sec_lsi_parts B OM ReplyB3LScap.fr_CAP nsec KMAX KC`
   is the HLSx of Section rows below at LSx := that LSI *)
Section lsip.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma sec_lsi_parts : forall B OM (CAP : lfcx -> Z -> lmod -> alayout -> astate -> Prop) nsec KMAX KC cx t m ly S,
  ReplyB3LS3p.fr_LS3cp B CR cx t m ly S /\ ReplyLSBo.fr_OUT OM cx t m ly S /\ ReplyB3LS3e.fr_ENT B cx m ly S /\
  (CAP cx t m ly S /\ fr_SEC nsec KMAX KC cx t m ly S) ->
  fr_LS3c B CR cx t m ly S /\ fr_SEC nsec KMAX KC cx t m ly S.
Proof.
  intros B OM CAP nsec KMAX KC cx t m ly S ((H3c & _) & _ & _ & _ & HS). exact (conj H3c HS).
Qed.
End lsip.

(* ================================================================== the slot lemmas: one per B top_x rule *)
(* The shape of lib/B/ReplyB3LScap.v's fr_CAP_<rule> (a Theorem Labs lane's slot order), at MT := MT_sec nsec KMAX:
   the binders in the B top's order (lib/B/W_LLVMFuzzerTestOneInput_top_x.v, the line cited); first the LSI parts the
   lemma reads, in LSI's order (fr_LS3 / fr_LS3c at the instance's call room YCfn_cf.CALL_ROOM_B); then
   `fr_SEC nsec KMAX KC cx t m ly S` at the rule's pre-state; then the rule's own premises in the top's order (a
   subset).
   - fr_SEC_<rule>, one per B top_x rule that concludes LS: fr_SEC at the rule's post-state.
   - sec_<row>, one per B top_x meter binder: exactly that row's meter conjunct (`mo_ok MT S (cost ..)`, LS_exit_end's
     `mo_le MT (c_S cx) .. (XN_LIB (c_n cx))`), the top's cost arguments verbatim.
   After the Section closes every lemma takes B nsec KMAX KC HKC first (then XM_LIB HXM for sec_entry, fr_SEC_pro and
   sec_LS_pro_oa; OM for sec_exit_room and sec_LS_exit_budget; XN_LIB HXN HNSF OM for sec_LS_exit_end).
   F8 / F9 (KF-COUNT; W8's A texts, window aacecd50fedd, which a Theorem Labs lane's B top_x restate takes at the same
   positions): the facts the counts need that the rows did not carry are now the rows' own premises, so no lemma here
   has a named hypothesis for them:
     LS_exit_budget: `0 <= t <= OPS_MAX` and every entry's keys not empty, after LSx (relay_finish's room comes from
       fr_LS3's room and fr_OUT, as the top's LS_rf_room; the keys from amodel_at's aentry_ok);
     LS_exit_end: the keys not empty, last;
     LS_rm_cnl_pre / LS_rm_cshe_pre / LS_rm_sr_pre: `0 <= t < OPS_MAX` and |re_U (rm_ent m j0)| <= APARTIAL, after
       rm_rr_ok (relay_remove's count, sec_rm_tr_max); LS_rm_step: the |re_U| bound, after LSx. *)
Section slots.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable nsec : astate -> Z.
Variables KMAX KC : Z.
Hypothesis HKC : 240 <= KC.
Local Notation MT := (MT_sec nsec KMAX).
Local Notation RINV := fr_RINV.
Local Notation fr_SEC := (fr_SEC nsec KMAX KC).
(* the B top's per-call meter budgets at the entry (lf_base_x's mo_ok, fr_lib_pre_cf_x's conjunct 19) and the exit
   (POST's mo_le), and the meter's blindness to a frame-state change (ReplyKfMeterB.MT_sec_set_fs's premise) *)
Variables XM_LIB XN_LIB : Z -> Z.
Hypothesis HXM : forall n, SEC_CALL KC <= XM_LIB n.
Hypothesis HXN : forall n, SEC_CALL KC <= XN_LIB n.
Hypothesis HNSF : forall f s, nsec (set_fs f s) = nsec s.
(* LSI's fr_OUT bound (the exit's relay_finish room, ReplyLSBoRf.LS_rf_room_p_room) *)
Variable OM : Z.

(* the call's entry budget, from lf_base_x's mo_ok at the entry *)
Lemma sec_entry : forall RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  nsec (c_S cx) + SEC_CALL KC <= KMAX.
Proof using B HKC XM_LIB HXM.
  intros RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp (_ & Hpre).
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMO & _).
  change (nsec (c_S cx) + XM_LIB (c_n cx) <= KMAX) in HMO. pose proof (HXM (c_n cx)). lia.
Qed.

(* ---------------------------------------------------------------- fr_SEC_<rule>: the LS rules *)
(* top_x :221 LS_head_nout *)
Lemma fr_SEC_head_nout : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx t (W_LLVMFuzzerTestOneInput_head.lm_clear_O m) ly S.
Proof using B HKC. exact (fr_SEC_head_nout_a nsec KMAX KC HKC). Qed.
(* top_x :225-227 LS_head_skip *)
Lemma fr_SEC_head_skip : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_head.lm_set_k m (W_LLVMFuzzerTestOneInput_head.hd_k' cx m)) ly S.
Proof using B HKC. intros cx t m ly S. exact (fr_SEC_head_skip_a nsec KMAX KC HKC cx t m _ ly S). Qed.
(* top_x :309-322 LS_pro: the entry budget (lf_base_x), the seat's count (mo_le MT (c_S cx) S2 0), relay_add's
   primary requests (oa_cost = 0) and the first head's model, which holds no bytes *)
Lemma fr_SEC_pro : forall RLO RHI fr_live_pre LIBROOM NP G ARX,
  forall cx Hp q T' pj c O cap out (S2 : astate) (pos : Z) ly S,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  mo_le MT (c_S cx) S2 0 -> mo_le MT S2 S (W_op_add.oa_cost MT) ->
  fr_SEC cx 0 (W_LLVMFuzzerTestOneInput_pro.pro_m q T' pj c O cap out) ly S.
Proof using B HKC XM_LIB HXM.
  intros RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp q T' pj c O cap out S2 pos ly S HB Hmo0 Hmo.
  exact (fr_SEC_pro_a nsec KMAX KC cx S2 S _ ly (sec_entry RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp HB) Hmo0 Hmo
           (sec_ub_pro q T' pj c O cap out)).
Qed.
(* top_x :507-508 LS_drain_skip *)
Lemma fr_SEC_drain_skip : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
Proof using B HKC. intros cx t m ly S. exact (fr_SEC_drain_skip_a nsec KMAX KC HKC cx t m _ ly S). Qed.
(* top_x :511-537 LS_drain_step *)
Lemma fr_SEC_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (ly1 : alayout) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B CR cx t m ly S -> fr_SEC cx t m ly S ->
  dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  hl_recs (hs_pending h1) = [] ->
  E = hs_expected h1 -> H = hs_held h1 ->
  h'' = set_exp_held h1 E' H' ->
  dr_at_op cx m -> RINV cx t m -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.ls3_dpost m j h e' h1 ->
  0 <= t < OPS_MAX ->
  fr_SEC cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof using B HKC.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H ly1 h1 E' H' H3 HS Hpick Hj M1 M2 Hpend EE EH Hh''
    Hat HRI Hfd Heof Hep Hdp Ht.
  exact (fr_SEC_drain_step_a nsec KMAX KC HKC B cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H h1 E' H' H3
           HRI Hat Hpick Hj Hfd Heof Hep M1 M2 Hpend EE EH Hh'' Hdp Ht HS).
Qed.
(* top_x :572-574 LS_close *)
Lemma fr_SEC_close : forall cx t m i ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_close cx m i) ly S.
Proof using B HKC. exact (fr_SEC_close_a nsec KMAX KC HKC). Qed.
(* top_x :575-577 LS_eintr *)
Lemma fr_SEC_eintr : forall cx t m i ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_eintr cx m i) ly S.
Proof using B HKC. exact (fr_SEC_eintr_a nsec KMAX KC HKC). Qed.
(* top_x :578-579 LS_sendmax *)
Lemma fr_SEC_sendmax : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_sendmax cx m (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0)) ly S.
Proof using B HKC. intros cx t m ly S. exact (fr_SEC_sendmax_a nsec KMAX KC HKC cx t m _ ly S). Qed.
(* top_x :580 LS_default *)
Lemma fr_SEC_default : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_small.sm_default cx m (W_LLVMFuzzerTestOneInput_small.sm_dg cx m)) ly S.
Proof using B HKC. intros cx t m ly S. exact (fr_SEC_default_a nsec KMAX KC HKC cx t m _ ly S). Qed.
(* top_x :596-599 LS_add_open (the four slots: fr_RINV's fr_relay) *)
Lemma fr_SEC_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
  fr_SEC cx t m ly S -> RINV cx t m ->
  W_op_add.oa_first (W_LLVMFuzzerTestOneInput_add.ad_os (lm_hs m)) = Some i ->
  mo_le MT S S' (W_op_add.oa_cost MT) ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_open m i q pj ev) ly' S'.
Proof using B HKC.
  intros cx t m i q pj ev ly S ly' S' HS HRI Hf Hmo. pose proof HRI as (_ & (Hl4 & _) & _).
  exact (fr_SEC_add_open_a nsec KMAX KC HKC cx t m i q pj ev ly S ly' S' Hl4 Hf Hmo HS).
Qed.
(* top_x :600-602 LS_add_none *)
Lemma fr_SEC_add_none : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_add.ad_none m) ly S.
Proof using B HKC. exact (fr_SEC_add_none_a nsec KMAX KC HKC). Qed.
(* top_x :613-614 LS_write_skip *)
Lemma fr_SEC_write_skip : forall cx t m ly S, fr_SEC cx t m ly S ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_skip m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m)) ly S.
Proof using B HKC. intros cx t m ly S. exact (fr_SEC_write_skip_a nsec KMAX KC HKC cx t m _ ly S). Qed.
(* top_x :628-641 LS_write_push *)
Lemma fr_SEC_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  fr_SEC cx t m ly S ->
  W_LLVMFuzzerTestOneInput_write.wr_pick cx m si h -> 0 < W_LLVMFuzzerTestOneInput_write.wr_n cx m ->
  hl_recs l' = hl_recs (hs_pending h) ++ [(d, W_LLVMFuzzerTestOneInput_write.wr_x cx m)] ->
  mo_le MT S S' (W_contract.lp_cost MT (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) ->
  0 <= t < OPS_MAX ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_write.wr_push m (W_LLVMFuzzerTestOneInput_write.wr_k2 cx m) si (W_LLVMFuzzerTestOneInput_write.set_pending h l') ev) ly' S'.
Proof using B HKC.
  intros cx t m si h l' d ev ly S ly' S' HS Hp Hn Hr Hmo Ht.
  exact (fr_SEC_write_push_a nsec KMAX KC HKC cx t m si h l' d ev ly S ly' S' Hp Hn Hr Hmo Ht HS).
Qed.
(* top_x :742-758 LS_rm_step (F9: the removed entry's |re_U| <= APARTIAL after LSx) *)
Lemma fr_SEC_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' (ds : list (Z * list byte)) (cc : Z) ev5,
  fr_SEC cx t m ly0 S0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0 (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
Proof using B HKC.
  intros cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ds cc ev5 HS HU Hmo HRI Hat Hrr Ht.
  exact (fr_SEC_rm_step_a nsec KMAX KC HKC cx t m ly0 S0 ly S si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ev5 HRI
           Hat Hrr Hmo Ht HU HS).
Qed.
(* top_x :822-834 LS_event_step *)
Lemma fr_SEC_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out' (ly1 ly2 : alayout) (q : Z),
  fr_SEC cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) ->
  lm_O m = [] ->
  0 <= t < OPS_MAX ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_arm_event.ev_step cx m e v out') ly3 S3.
Proof using B HKC.
  intros cx t m ly S S1 S2 S3 ly3 e v out' ly1 ly2 q HS HE M1 M2 M3 HO Ht.
  exact (fr_SEC_event_step_a nsec KMAX KC HKC cx t m ly S S1 S2 S3 ly3 e v out' HE M1 M2 M3 HO Ht HS).
Qed.
(* top_x :865 GN_RI_end_x's LS half (lib/B/ReplyRINVB_gone.v RG.GN_RI_end_ls's text) *)
Lemma fr_SEC_gone_end : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst q,
  fr_LS3c B CR cx t m ly S -> fr_SEC cx t m ly S ->
  RINV cx t m -> gn_op cx t m ->
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
  gn_pairs m hs -> W_LLVMFuzzerTestOneInput_gone_base.gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_rig_ok cx m hs qs c2 O2 cap2 ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_run (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A
    (length (lm_es m1)) 0%nat ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_runc MT (W_LLVMFuzzerTestOneInput_gone_base.gn_pre cx m) m1 mc A
    (length (lm_es m1)) 0%nat q ->
  mo_le MT S Sx cst -> W_LLVMFuzzerTestOneInput_gone_base.gn_cst MT cx m m1 q cst ->
  fr_SEC cx (t + 1) mc lyx Sx.
Proof using B HKC.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q H3c HS HRI Hop HE Hcap HE6 HS6 Hp Ha Hrok Hrun Hrunc
    Hmo Hcst.
  exact (fr_SEC_gone_end_a nsec KMAX KC HKC B cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst q H3c HRI Hop HE
           Hcap HE6 HS6 Hp Ha Hrok Hrun Hrunc Hmo Hcst HS).
Qed.

(* ---------------------------------------------------------------- sec_<row>: the meter binders *)
(* top_x :295-300 LS_pro_oa *)
Lemma sec_LS_pro_oa : forall RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp (S2 : astate) pos,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  mo_le MT (c_S cx) S2 0 ->
  mo_ok MT S2 (W_op_add.oa_cost MT).
Proof using B HKC XM_LIB HXM.
  intros RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp S2 pos HB _ _ _ _ Hmo0.
  exact (fr_SEC_pro_oa_a nsec KMAX KC HKC cx S2 (sec_entry RLO RHI fr_live_pre LIBROOM NP G ARX cx Hp HB) Hmo0).
Qed.
(* relay_finish's room at the exit, as the top's LS_rf_room (:335-338) holds it: LS v3's room (fr_LS3_room_rel) and
   fr_OUT give s5-r1d's peak form (ReplyLSBoRf.LS_rf_room_p_room); its copies ReplyLSBArms.ge_room_c3 /
   gse_room_c3 have the bodies of lib/B/W_contract.v's ge_room / gse_room *)
Lemma sec_R_rf_fits : LS3_OVER + R_rf <= CR.
Proof using. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sec_gse_room_px : forall MX xs bb c mx no cap,
  gse_room_c3 MX bb c mx no cap xs -> W_contract.gse_room MX bb c mx no cap xs.
Proof using.
  intros MX. induction xs as [|x xs IH]; intros bb c mx no cap H; [exact I|].
  cbn [gse_room_c3 W_contract.gse_room] in *. destruct H as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
Lemma sec_rf_room_px : forall MX es bb c O mx no cap,
  lx_rf_room_p MX bb c O mx no cap es -> W_bx_defs.lx_rf_room MX bb c O mx no cap es.
Proof using.
  intros MX. induction es as [|e es IH]; intros bb c O mx no cap H; [exact I|].
  cbn [lx_rf_room_p W_bx_defs.lx_rf_room] in *. destruct H as [H1 H2].
  split; [exact (sec_gse_room_px _ _ _ _ _ _ _ H1) | apply IH; exact H2].
Qed.
Lemma sec_exit_room : forall cx t m ly S,
  fr_LS3 B CR cx t m ly S -> ReplyLSBo.fr_OUT OM cx t m ly S -> 0 <= t <= OPS_MAX ->
  W_bx_defs.lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m).
Proof using B OM.
  intros cx t m ly S H3 HO Ht. apply sec_rf_room_px.
  exact (LS_rf_room_p_room LS3_OVER CR OM sec_R_rf_fits cx t m ly S (fr_LS3_room_rel B CR cx t m ly S H3) HO Ht).
Qed.
(* top_x :339-340 LS_exit_budget (F8: `0 <= t <= OPS_MAX` and the keys not empty, after LSx) *)
Lemma sec_LS_exit_budget : forall cx t m ly S,
  fr_LS3 B CR cx t m ly S -> ReplyLSBo.fr_OUT OM cx t m ly S -> fr_SEC cx t m ly S ->
  0 <= t <= OPS_MAX ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_ok MT S (W_bx_defs.lx_exit_cost MT m).
Proof using B HKC OM.
  intros cx t m ly S H3 HO HS Ht Hk.
  exact (fr_SEC_exit_budget_a nsec KMAX KC HKC cx t m ly S (sec_exit_room cx t m ly S H3 HO Ht) Hk HS).
Qed.
(* top_x :354-367 LS_exit_end's meter conjunct (the call's count within SEC_CALL KC <= XN_LIB; F8: the keys not empty,
   last) *)
Lemma sec_LS_exit_end : forall fr_FP ARX G,
  forall cx t m ly3 S3 rest ly' S' (W' : world segs) mem' md' fpos k' C cap out,
  fr_LS3 B CR cx t m ly3 S3 -> ReplyLSBo.fr_OUT OM cx t m ly3 S3 -> fr_SEC cx t m ly3 S3 ->
  Permutation (ablocks B ly3 S3) (input_blks cx ++ model_blks m ++ rest) ->
  Permutation (ablocks B ly' S') (input_blks cx ++ (lm_G m, ATABLE) :: aout_blks cap out ++ rest) ->
  frames S' = [(1, fpos)] -> mo_le MT S3 S' C -> C <= W_bx_defs.lx_exit_cost MT m ->
  ajournal_gx_x segs B [] ARX G 0 [] YCfn.LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [] ly' (stack_free_state 1 fpos S') [] W' mem' md' k' ->
  cap = gse_cap (W_bx_defs.lx_rf_run (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m)) ->
  0 <= t <= OPS_MAX ->
  fr_hblks W' mem' = (lm_G m, ATABLE) :: aout_blks cap out ->
  List.NoDup (ablocks B ly' S') ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  mo_le MT (c_S cx) (stack_free_state 1 fpos S') (XN_LIB (c_n cx)).
Proof using B HKC XN_LIB HXN HNSF OM.
  intros fr_FP ARX G cx t m ly3 S3 rest ly' S' W' mem' md' fpos k' C cap out H3 HO HS _ _ _ Hmo HC0 _ _ Ht _ _ Hk.
  pose proof (sec_exit_room cx t m ly3 S3 H3 HO Ht) as Hroom.
  pose proof (fr_SEC_exit_end_a nsec KMAX KC HKC cx t m ly3 S3 S' C fpos HNSF Hmo HC0 Hroom Hk HS) as X.
  pose proof (HXN (c_n cx)). change (nsec (stack_free_state 1 fpos S') <= nsec (c_S cx) + XN_LIB (c_n cx)). lia.
Qed.
(* top_x :462-477 LS_drain_pre *)
Lemma sec_LS_drain_pre : forall cx t m ly S si h j,
  fr_LS3 B CR cx t m ly S -> fr_SEC cx t m ly S ->
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof using B HKC.
  intros cx t m ly S si h j H3 HS HRI Hat Hpick Hj Hfd Heof Ht HU.
  exact (fr_SEC_drain_pre_a nsec KMAX KC HKC B cx t m ly S si h j H3 HRI Hat Hpick Hj Hfd Heof Ht HU HS).
Qed.
(* top_x :480-506 LS_cnl_pre (check_no_loss's count premise, hl_n held + count_begin < 2 ^ 25, from the drained pair's
   row of fr_RINV: sec_dr_pair / sec_cnl_count) *)
Lemma sec_LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'' (e' : rentry) (cap' out' : Z),
  fr_SEC cx t m ly S ->
  RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] ->
  W_LLVMFuzzerTestOneInput_drain_defs_x.dr3_epre (nth j (lm_es m) dr_e0) ->
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')).
Proof using B HKC.
  intros cx t m ly S ly' S' si h j h'' e' cap' out' HS HRI Hpick Hj Hfd Heof Hmo Hmap Hheld Ht HO Hep.
  exact (fr_SEC_cnl_pre_a nsec KMAX KC HKC cx t m ly S S' si h j h'' HRI Hpick Hj Hfd Heof Hmo Hmap Hheld Ht HO Hep
           HS).
Qed.
(* top_x :593-595 LS_add_room *)
Lemma sec_LS_add_room : forall cx t m ly S, fr_SEC cx t m ly S -> mo_ok MT S (W_op_add.oa_cost MT).
Proof using B HKC.
  intros cx t m ly S HS. rewrite (sec_oa nsec KMAX). pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S S 0 0 HS); lia.
Qed.
(* top_x :622-626 LS_write_room *)
Lemma sec_LS_write_room : forall cx t m (si : nat) h ly S, fr_SEC cx t m ly S ->
  mo_ok MT S (W_contract.lp_cost MT (hs_pending h) (W_LLVMFuzzerTestOneInput_write.wr_n cx m)).
Proof using B HKC.
  intros cx t m si h ly S HS.
  pose proof (ReplyKfTrSmB.kf_lp_cost MT (sec_HMs nsec KMAX) (sec_HFs nsec KMAX) (hs_pending h)
                (W_LLVMFuzzerTestOneInput_write.wr_n cx m)) as K.
  assert (K2 : ReplyKfTrSmB.KC_lp = 2) by reflexivity. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok nsec KMAX KC HKC cx t m ly S S 0 _ HS); lia.
Qed.
(* top_x :679-692 LS_rm_rr_pre *)
Lemma sec_LS_rm_rr_pre : forall cx t m ly S si h j0,
  fr_SEC cx t m ly S ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h).
Proof using B HKC.
  intros cx t m ly S si h j0 HS HRI Hat Ht HU.
  exact (fr_SEC_rm_rr_pre_a nsec KMAX KC HKC cx t m ly S si h j0 HRI Hat Ht HU HS).
Qed.
(* top_x :704-711 LS_rm_cnl_pre (check_no_loss's count premise from the removed pair's row of fr_RINV and
   relay_remove's dr_rel: sec_rm_cnl / sec_cnl_count; F9: t and |re_U| after rm_rr_ok) *)
Lemma sec_LS_rm_cnl_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (ly : alayout) (out2 : Z),
  fr_SEC cx t m ly0 S0 ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h) ->
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)).
Proof using B HKC.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 ly out2 HS HRI Hat Hrr Ht HU Hmo.
  change (nsec S <= nsec S0 + W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost in Hmo. rewrite (sec_tr nsec KMAX) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost.
  apply (fr_SEC_rm_after nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 0 _ HRI Hat Hrr Ht HU);
    [lia | lia | exact HS].
Qed.
(* top_x :719-723 LS_rm_cshe_pre (F9: t and |re_U| after rm_rr_ok) *)
Lemma sec_LS_rm_cshe_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 (E' H' : hlist),
  fr_SEC cx t m ly0 S0 ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1)) ->
  mo_ok MT S ((W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H').
Proof using B HKC.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' HS HRI Hat Hrr Ht HU Hmo.
  change (nsec S <= nsec S0 + (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
    W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1))) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost, W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost in Hmo.
  rewrite (sec_tr nsec KMAX) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost. rewrite (sec_cshe nsec KMAX).
  apply (fr_SEC_rm_after nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2
           (cnl_cost MT (hs_expected h1) (hs_held h1)) 0 HRI Hat Hrr Ht HU); [lia | lia | exact HS].
Qed.
(* top_x :730-734 LS_rm_sr_pre (F9: t and |re_U| after rm_rr_ok) *)
Lemma sec_LS_rm_sr_pre : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H''
    (ds : list (Z * list byte)) (cc : Z),
  fr_SEC cx t m ly0 S0 ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h + (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) + (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H') ->
  mo_ok MT S (sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))).
Proof using B HKC.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 E' H' H'' ds cc HS HRI Hat Hrr Ht HU Hmo.
  change (nsec S <= nsec S0 + (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h +
    W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT (hs_expected h1) (hs_held h1) +
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT H')) in Hmo.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost, W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost,
    W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost in Hmo.
  rewrite (sec_tr nsec KMAX), (sec_cshe nsec KMAX) in Hmo. rewrite (sec_sr nsec KMAX).
  apply (fr_SEC_rm_after nsec KMAX KC HKC cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2
           (cnl_cost MT (hs_expected h1) (hs_held h1)) 0 HRI Hat Hrr Ht HU); [lia | lia | exact HS].
Qed.
(* top_x :801-803 LS_event_malloc *)
Lemma sec_LS_event_malloc : forall cx t m ly S e, fr_SEC cx t m ly S -> mo_ok MT S (mo_malloc MT (re_len e)).
Proof using B HKC. exact (fr_SEC_event_malloc_a nsec KMAX KC HKC). Qed.
(* top_x :805-812 LS_event_relay *)
Lemma sec_LS_event_relay : forall cx t m ly S (S1 : astate) e (ly1 : alayout) (q : Z),
  fr_SEC cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  lm_O m = [] ->
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof using B HKC.
  intros cx t m ly S S1 e ly1 q HS HE M1 HO.
  exact (fr_SEC_event_relay_a nsec KMAX KC HKC cx t m ly S S1 e HE HO M1 HS).
Qed.
(* top_x :815-819 LS_event_free *)
Lemma sec_LS_event_free : forall cx t m ly S (S1 S2 : astate) e,
  fr_SEC cx t m ly S -> W_LLVMFuzzerTestOneInput_arm_event.ev_evt cx m e -> lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_ok MT S2 (mo_free MT).
Proof using B HKC.
  intros cx t m ly S S1 S2 e HS HE HO M1 M2.
  exact (fr_SEC_event_free_a nsec KMAX KC HKC cx t m ly S S1 S2 e HE HO M1 M2 HS).
Qed.
(* top_x :876-889 GN_LS_rig_x (no re_cap there: sec_rig45, 240) *)
Lemma sec_GN_LS_rig_x : forall cx t m ly S hs,
  fr_LS3c B CR cx t m ly S -> fr_SEC cx t m ly S ->
  RINV cx t m -> W_LLVMFuzzerTestOneInput_gone_base.gn_pairs m hs ->
  W_LLVMFuzzerTestOneInput_gone_base.gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (W_LLVMFuzzerTestOneInput_gone_base.gn_id cx m) (lm_es m) hs in
  mo_ok MT S (tr_cost MT tr).
Proof using B HKC.
  intros cx t m ly S hs H3c HS HRI Hp Hop HU HSRC. cbv zeta.
  exact (fr_SEC_gone_rig_a nsec KMAX KC HKC B cx t m ly S hs H3c HRI Hp Hop HU HSRC HS).
Qed.
(* top_x :864 GN_RI_step_x's two meter conjuncts: fr_SEC_GN_RI_step_cnl_meter / fr_SEC_GN_RI_step_cshe_meter above
   (lib/B/ReplyRINVB_gone.v's RG texts, any LS with sec_lsi_parts' projection) *)
End slots.
