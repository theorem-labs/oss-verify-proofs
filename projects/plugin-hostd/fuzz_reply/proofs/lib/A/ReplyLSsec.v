(* fr_SEC: the secondary-allocation count clause of the top's LS instance (KF-COUNT #6), its keep lemmas and the meter
   conjuncts of top_x's rows at the counting meter MT_sec.  proves no function (kind: invariant lemma).

   THE CLAUSE.  At MT := ReplyKfMeter.MT_sec nsec KMAX (mo_le s s' c := nsec s' <= nsec s + c, mo_ok s c :=
   nsec s + c <= KMAX, mo_malloc n := (if 64512 <? n then 1 else 0), mo_free := 0):
     fr_SEC cx t m ly S := nsec (c_S cx) + SEC_CALL <= KMAX /\
                           21 * (nsec S - nsec (c_S cx)) + sec_ub m <= SEC_RATE * Z.min t OPS_MAX,
   SEC_RATE := WMAX + 21 * KC, SEC_CALL := SEC_RATE * (OPS_MAX + 1) / 21, and sec_ub m the bytes not yet consumed into
   lines: every source's pending stream plus every entry's partial line re_U (the lane B counts' own terms,
   ReplyKfTrRig.v kf_in).  A write adds at most WMAX bytes (paid by t + 1); a drain, remove or gone consumes bytes that
   pay its begin-key reallocations at 21 bytes per begin line (KF lane B: ReplyKfTr.v, ReplyKfTrRr.v, ReplyKfTrRig.v);
   every other secondary request of one operation is in KC.  The first conjunct is the call's entry budget (from
   lf_base_x's mo_ok at the entry, given SEC_CALL <= XM_LIB n, ReplyLSI.v).  The clause bounds every row's
   `mo_ok MT S cost` by SEC_CALL over the entry (fr_SEC_bound), with no bound on t (Z.min).
   - The per-trace counts at 45 per drain and 60 per relay_remove (sec_drain45 / sec_rr60, and sec_rig45 at 4 * 60)
     are lane B's own chains (kf_drain_pot, kf_drain_caps, kd_gain; kf_rr_g; kf_gone_run's induction) without the
     relay buffer's re_cap premise, which LS_drain_pre / LS_rm_rr_pre / LS_gone_rig do not carry.  The gone rules
     (ReplyLSsecGn.v) charge relay_instance_gone with lane B's kf_rig (180), whose re_cap their own premises give, and
     the loop's check_no_loss calls with 4 * 15.  KC >= 240 covers the largest operation (gone: 180 + 60).
   - check_no_loss's charge cnl_cost (the kit's fixed text) is bounded by k4's ReplyKfCnl.kf_cnl_cost_le (15), its
     premises from the drained pair's row of fr_RINV and the reference splitter's 6000-byte lines.
   - fr_SEC reads no block, so the keep lemmas take only the rule's meter premises and the facts that bound its
     counts. *)
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
  relay_remove_b_aux send_line_b_c RelayRunT RelayRunF ListTr relay_instance_gone_b_c SlotParse.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Arms ReplyLSCntL ReplyLS3c ReplyLS3cArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o ReplyLS3p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3Peak ReplyLSRrPre ReplyRINV_a12.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyKfMeter ReplyKfNsec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
  ReplyKfChain ReplyKfTr ReplyKfTrRr ReplyKfTrRig ReplyKfTrSm ReplyCnt ReplyKfCnl.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation zsum l := (fold_right Z.add 0 l).

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
  pose proof (ReplyKfTr.kf_drain_pot live mx no cap e h j a Ho HW) as P.
  destruct (ReplyKfTr.kf_drain_caps live mx no cap e h j a Ho HW) as (C1 & C2 & C3).
  pose proof (ReplyKfTr.kd_gain _ _ _ C1 HM) as G1.
  pose proof (ReplyKfTr.kd_gain _ _ _ C2 HM) as G2.
  pose proof (ReplyKfTr.kd_gain _ _ _ C3 HM) as G3.
  lia.
Qed.

(* W_contract.dr_tr is drain_tr at live := dr_live c h, j := 0, a := dadr0 (as ReplyKfTr.kf_dr) *)
Lemma sec_dr45 : forall c mx no cap e h,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  tr_max (dr_tr c mx no cap e h) < 2 ^ 30 ->
  21 * nsec_tr (dr_tr c mx no cap e h) + Z.of_nat (length (drain_b_c.ds_u (dr_fin c mx no cap e h))) <=
  21 * 45 + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
Proof. intros c mx no cap e h. exact (sec_drain45 (dr_live c h) mx no cap e h 0 drain_b_c.dadr0). Qed.

(* relay_remove: ReplyKfTrRr.kf_rr_g at the drain bound sec_dr45 (45 + KC_ke = 60) *)
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
    pose proof (ReplyKfTrRr.kf_rr_tm_dr c mx no cap FD es h e HFD Hf Ho). repeat split; try assumption. lia. }
  pose proof (ReplyKfTrRr.kf_rr_g 45 ltac:(lia)
    (fun c mx no cap e h => 0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
       tr_max (dr_tr c mx no cap e h) < 2 ^ 30)
    (fun c' mx' no' cap' e' h' H => sec_dr45 c' mx' no' cap' e' h' (proj1 H) (proj1 (proj2 H)) (proj2 (proj2 H)))
    c mx no cap FD es h e HFD Hf HD HM) as K.
  assert (KK : ReplyKfChain.KC_ke = 15) by reflexivity. rewrite KK in K.
  destruct (re_eof e =? 0); lia.
Qed.

(* relay_instance_gone at the drain bound sec_drain45: ReplyKfTrRig.kf_gone_run / kf_rig's induction, KC 4 * 60 *)
Definition sec_dr_pre (e : rentry) (h : hsrc) : Prop :=
  0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000).

Lemma sec_gone_run : forall c0 mx0 no0 cap0 lv mx pre nm ps no cap j o,
  Forall (fun p => re_eof (fst p) = 0 -> sec_dr_pre (fst p) (fst (snd p))) ps ->
  tr_max (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) < 2 ^ 30 ->
  21 * nsec_tr (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) +
    ReplyKfTrRig.osum (ReplyKfTrRig.kf_tail c0 mx0 no0 cap0) ps <=
  21 * 60 * Z.of_nat (length ps) + ReplyKfTrRig.osum ReplyKfTrRig.kf_in ps.
Proof.
  intros c0 mx0 no0 cap0 lv mx pre nm ps.
  induction ps as [|[e hj] r IH]; intros no cap j o HF HM.
  - cbn [relay_instance_gone_b_c.gone_run fst length ReplyKfTrRig.osum map fold_right Z.of_nat].
    rewrite nsec_tr_nil. lia.
  - apply Forall_cons_iff in HF as [HF0 HFr]. cbn [fst snd] in HF0.
    rewrite !ReplyKfTrRig.osum_cons. cbn [length]. rewrite Nat2Z.inj_succ.
    cbn [relay_instance_gone_b_c.gone_run] in HM |- *. cbv zeta in HM |- *.
    match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
      pose proof (IH n c j1 o1 HFr) as IHr;
      destruct (relay_instance_gone_b_c.gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
    cbn [fst snd] in IHr, HM |- *.
    rewrite !ReplyKfChain.kf_tm_app in HM. rewrite !nsec_tr_app.
    specialize (IHr ltac:(lia)).
    match goal with |- context [nsec_tr (fst (gestures_end_b_c.keys_end_run ?l ?m ?n ?cp ?x ?jj ?oo))] =>
      assert (HK : nsec_tr (fst (gestures_end_b_c.keys_end_run l m n cp x jj oo)) <= ReplyKfChain.KC_ke)
        by (apply ReplyKfChain.kf_keys; lia) end.
    unfold ReplyKfChain.KC_ke in *.
    destruct (Z.eqb_spec (re_eof e) 0) as [E|E]; cbv beta iota in HM |- *.
    + destruct (HF0 E) as (P1 & P2).
      match goal with |- context [drain_b_c.drain_tr ?l ?m ?n ?cp ?ee ?h ?jj ?a] =>
        assert (HD : 21 * nsec_tr (drain_b_c.drain_tr l m n cp ee h jj a) +
                       Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin l m n cp ee h))) <=
                     21 * 45 + Z.of_nat (length (re_U ee)) + Z.of_nat (length (pending_stream h)))
          by (apply sec_drain45; first [assumption | lia]);
        rewrite (ReplyKfTrRig.kf_tail_fin c0 mx0 no0 cap0 l m n cp ee h) in HD end.
      assert (KI : ReplyKfTrRig.kf_in e (fst hj) =
                   Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream (fst hj)))) by reflexivity.
      lia.
    + rewrite nsec_tr_nil. lia.
Qed.

Lemma sec_rig45 : forall c mx no cap ID es hs,
  (length es <= 4)%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> sec_dr_pre (fst p) (fst (snd p))) (combine es hs) ->
  tr_max (rig_tr c mx no cap ID es hs) < 2 ^ 30 ->
  21 * nsec_tr (rig_tr c mx no cap ID es hs) + ReplyKfTrRig.osum (ReplyKfTrRig.kf_tail c mx no cap) (combine es hs) <=
  21 * 240 + ReplyKfTrRig.osum ReplyKfTrRig.kf_in (combine es hs).
Proof.
  intros c mx no cap ID es hs Hn HF HM.
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr in HM |- *. cbv zeta in HM |- *.
  pose proof (sec_gone_run c mx no cap _ _ _ _ _ _ _ _ _ HF HM) as H.
  pose proof (ReplyKfTrRig.kf_combine_len _ _ es hs) as HL.
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
  pose proof (fr_a12_held_keys (re_keys e) H Hnd Hss) as A.
  pose proof (rm3_kt_len (re_keys e)) as K.
  pose proof (SlotReads.count_begin_bytes Ls) as C.
  unfold fr_pair_cost in Hc. destruct (re_skip e =? 0); lia.
Qed.

(* ================================================================== the clause *)
Section sec.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a Theorem Labs lane's count of granted non-errbuf secondary entries (nsec_cf), the run bound (cf_kmax) and the per-operation
   constant (a Theorem Labs lane's ReplyKfC.KF_KC): the instance file sets them *)
Variable nsec : astate -> Z.
Variable KMAX : Z.
Variable KC : Z.
Local Notation MT := (MT_sec nsec KMAX).

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
(* the window kit's malloc law is PresetRoom's class rule (ReplyKfMeter.sec_lit) *)
Lemma sec_KF_MAL : forall n, mo_malloc MT n = if ReplyCnt.Psec n then 1 else 0.
Proof. intros n. unfold ReplyCnt.Psec. rewrite sec_lit. reflexivity. Qed.
Lemma sec_cnl_nonneg : forall E H, 0 <= cnl_cost MT E H.
Proof.
  intros E H. unfold cnl_cost. generalize (texts H) (hl_cap H). induction (hl_recs E) as [|r rs IH]; intros T cap.
  - cbn [cnl_go]. lia.
  - cbn [cnl_go]. pose proof (ReplyKfCnl.kf_gmc_nonneg MT sec_KF_MAL sec_HFs T cap (snd r)).
    specialize (IH (RelayModel.upd T (bzs (snd r))) (capstep T (bzs (snd r)) cap)). rewrite sec_HFs. lia.
Qed.
Lemma sec_ends : forall hs, lx_ends_cost MT hs = 0.
Proof. induction hs as [|[h|] hs IH]; cbn [lx_ends_cost]; rewrite ?sec_HFs; lia. Qed.
Lemma sec_srt : forall hs, lx_sr_total MT hs = 0.
Proof. intros hs. unfold lx_sr_total. rewrite !sec_sr. lia. Qed.

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
(* check_no_loss's charge at the kit's fixed cnl_cost: k4's ReplyKfCnl.kf_cnl_cost_le at MT_sec *)
Lemma sec_cnl_le : forall E H : hlist,
  hl_n H + Z.of_nat (count_begin (texts E)) < 2 ^ 25 ->
  Forall (fun r => Z.of_nat (length (snd r)) <= APARTIAL) (hl_recs E) ->
  cnl_cost MT E H <= 15.
Proof. exact (ReplyKfCnl.kf_cnl_cost_le MT sec_KF_MAL sec_HFs). Qed.

(* ---- the rules that keep the sources' pending lists and the entries ---- *)
Lemma fr_SEC_close : forall cx t m i ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_close cx m i) ly S.
Proof.
  intros cx t m i ly S. apply fr_SEC_keep; [exact HKC | lia | lia |].
  unfold sec_ub. cbn [sm_close lm_hs lm_es].
  rewrite (upd_hs_map sec_str i upd_closed (lm_hs m)) by (intros h; reflexivity). lia.
Qed.
Lemma fr_SEC_eintr : forall cx t m i ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_eintr cx m i) ly S.
Proof.
  intros cx t m i ly S. apply fr_SEC_keep; [exact HKC | lia | lia |].
  unfold sec_ub. cbn [sm_eintr lm_hs lm_es].
  rewrite (upd_hs_map sec_str i upd_eintr (lm_hs m)) by (intros h; reflexivity). lia.
Qed.
Lemma fr_SEC_sendmax : forall cx t m u ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_sendmax cx m u) ly S.
Proof. intros cx t m u ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [sm_sendmax lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_default : forall cx t m g ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (sm_default cx m g) ly S.
Proof. intros cx t m g ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [sm_default lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_add_none : forall cx t m ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (ad_none m) ly S.
Proof. intros cx t m ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [ad_none lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_write_skip : forall cx t m k ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (wr_skip m k) ly S.
Proof. intros cx t m k ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [wr_skip lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_head_nout : forall cx t m ly S, fr_SEC cx t m ly S -> fr_SEC cx t (lm_clear_O m) ly S.
Proof. intros cx t m ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [lm_clear_O lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_head_skip : forall cx t m k ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (lm_set_k m k) ly S.
Proof. intros cx t m k ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [lm_set_k lm_hs lm_es]. lia. Qed.
Lemma fr_SEC_drain_skip : forall cx t m k ly S, fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (dr_skip m k) ly S.
Proof. intros cx t m k ly S. apply fr_SEC_keep; [exact HKC | lia | lia |]. unfold sec_ub. cbn [dr_skip lm_hs lm_es]. lia. Qed.

(* ---- op_add: relay_add's requests are primary (oa_cost = 0); the new source and entry hold no bytes ---- *)
Lemma fr_SEC_add_open : forall cx t m i q pj ev ly S (ly' : alayout) (S' : astate),
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
Lemma fr_SEC_write_push : forall cx t m si h (l' : hlist) d ev ly S ly' S',
  wr_pick cx m si h -> 0 < wr_n cx m -> hl_recs l' = hl_recs (hs_pending h) ++ [(d, wr_x cx m)] ->
  mo_le MT S S' (lp_cost MT (hs_pending h) (wr_n cx m)) -> 0 <= t < OPS_MAX ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (wr_push m (wr_k2 cx m) si (set_pending h l') ev) ly' S'.
Proof.
  intros cx t m si h l' d ev ly S ly' S' (_ & _ & Hh) Hn Hr Hmo Ht H.
  change (nsec S' <= nsec S + lp_cost MT (hs_pending h) (wr_n cx m)) in Hmo.
  pose proof (ReplyKfTrSm.kf_lp_cost MT sec_HMs sec_HFs (hs_pending h) (wr_n cx m)) as Klp.
  assert (Klp2 : ReplyKfTrSm.KC_lp = 2) by reflexivity.
  apply (fr_SEC_step cx t m _ ly S ly' S' (lp_cost MT (hs_pending h) (wr_n cx m)) Ht Hmo); [|exact H].
  unfold sec_ub. cbn [wr_push lm_hs lm_es].
  pose proof (set_nth_zsum sec_str si (Some (set_pending h l')) (Some h) (lm_hs m) (nth_some_error _ _ _ Hh)) as Zs.
  pose proof (sec_stream_push h l' d (wr_x cx m) Hr) as Hp.
  assert (E1 : sec_str (Some h) = Z.of_nat (length (pending_stream h))) by reflexivity.
  assert (E2 : sec_str (Some (set_pending h l')) = Z.of_nat (length (pending_stream (set_pending h l'))))
    by reflexivity.
  destruct (ReplyLS.wr_facts cx m Hn) as (_ & Hx). pose proof (ou_wr_n_le cx m) as Hw.
  destruct (SEC_RATE_ge HKC) as (R1 & _). unfold SEC_RATE in *. lia.
Qed.

(* ---- event: its own copy (one request at most, kf_ev_cost) and relay_event's send (kf_re_cost, 15) ---- *)
Lemma sec_ev_sl : forall cx m e, ev_evt cx m e -> lm_O m = [] ->
  sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e) <= 15.
Proof.
  intros cx m e HE HO.
  pose proof (ev3_maxr_le (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) as M.
  pose proof (ou_ev_len cx m e HE) as L.
  assert (E0 : Z.of_nat (length (lm_O m)) = 0) by (rewrite HO; reflexivity).
  rewrite E0 in M |- *.
  pose proof (ReplyKfTrSm.kf_re_cost MT sec_HMs sec_HFs (lm_c m) (lm_mx m) 0 (lm_cap m) e ltac:(lia)) as K.
  assert (K2 : ReplyKfTrSm.KC_re = 15) by reflexivity. lia.
Qed.
Lemma fr_SEC_event_step : forall cx t m ly S (S1 S2 S3 : astate) (ly3 : alayout) e v out',
  ev_evt cx m e ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  mo_le MT S2 S3 (mo_free MT) -> lm_O m = [] -> 0 <= t < OPS_MAX ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (ev_step cx m e v out') ly3 S3.
Proof.
  intros cx t m ly S S1 S2 S3 ly3 e v out' HE M1 M2 M3 HO Ht H.
  change (nsec S1 <= nsec S + mo_malloc MT (re_len e)) in M1.
  change (nsec S2 <= nsec S1 + sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in M2.
  change (nsec S3 <= nsec S2 + mo_free MT) in M3.
  pose proof (sec_ev_sl cx m e HE HO) as K1.
  pose proof (ReplyKfTrSm.kf_ev_cost MT sec_HMs (re_len e)) as K2.
  assert (K3 : ReplyKfTrSm.KC_ev = 1) by reflexivity. rewrite sec_HFs in M3.
  apply (fr_SEC_step cx t m _ ly S ly3 S3 16 Ht ltac:(lia)); [|exact H].
  unfold sec_ub. cbn [ev_step lm_hs lm_es]. destruct (SEC_RATE_ge HKC) as (R1 & _). lia.
Qed.
Lemma fr_SEC_event_malloc : forall cx t m ly S e,
  fr_SEC cx t m ly S -> mo_ok MT S (mo_malloc MT (re_len e)).
Proof.
  intros cx t m ly S e H.
  pose proof (ReplyKfTrSm.kf_ev_cost MT sec_HMs (re_len e)) as K.
  assert (K2 : ReplyKfTrSm.KC_ev = 1) by reflexivity. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.
Lemma fr_SEC_event_relay : forall cx t m ly S (S1 : astate) e,
  ev_evt cx m e -> lm_O m = [] -> mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  fr_SEC cx t m ly S ->
  mo_ok MT S1 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)).
Proof.
  intros cx t m ly S S1 e HE HO M1 H. change (nsec S1 <= nsec S + mo_malloc MT (re_len e)) in M1.
  pose proof (sec_ev_sl cx m e HE HO) as K1.
  pose proof (ReplyKfTrSm.kf_ev_cost MT sec_HMs (re_len e)) as K2.
  assert (K3 : ReplyKfTrSm.KC_ev = 1) by reflexivity. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok HKC cx t m ly S S1 (mo_malloc MT (re_len e))); [exact H | lia | lia].
Qed.
Lemma fr_SEC_event_free : forall cx t m ly S (S1 S2 : astate) e,
  ev_evt cx m e -> lm_O m = [] ->
  mo_le MT S S1 (mo_malloc MT (re_len e)) ->
  mo_le MT S1 S2 (sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) ->
  fr_SEC cx t m ly S -> mo_ok MT S2 (mo_free MT).
Proof.
  intros cx t m ly S S1 S2 e HE HO M1 M2 H.
  change (nsec S1 <= nsec S + mo_malloc MT (re_len e)) in M1.
  change (nsec S2 <= nsec S1 + sl_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (re_len e)) in M2.
  pose proof (sec_ev_sl cx m e HE HO) as K1.
  pose proof (ReplyKfTrSm.kf_ev_cost MT sec_HMs (re_len e)) as K2.
  assert (K3 : ReplyKfTrSm.KC_ev = 1) by reflexivity. pose proof (sec_ub_nonneg m).
  rewrite sec_HFs. apply (fr_SEC_ok HKC cx t m ly S S2 16); [exact H | lia | lia].
Qed.

(* ---- op_add's prologue rows and the call's start ---- *)
Lemma fr_SEC_pro_oa : forall cx (S2 : astate),
  nsec (c_S cx) + SEC_CALL <= KMAX -> mo_le MT (c_S cx) S2 0 -> mo_ok MT S2 (oa_cost MT).
Proof.
  intros cx S2 H1 Hmo. change (nsec S2 <= nsec (c_S cx) + 0) in Hmo. rewrite sec_oa. change (nsec S2 + 0 <= KMAX).
  unfold SEC_CALL, SEC_RATE, WMAX, OPS_MAX in H1.
  assert (0 <= (65535 + 21 * KC) * (512 + 1) / 21) by (apply Z.div_pos; lia). lia.
Qed.
Lemma sec_ub_pro : forall q T' pj c O cap out, sec_ub (pro_m q T' pj c O cap out) = 0.
Proof. reflexivity. Qed.
Lemma fr_SEC_pro : forall cx (S2 S : astate) m ly,
  nsec (c_S cx) + SEC_CALL <= KMAX -> mo_le MT (c_S cx) S2 0 -> mo_le MT S2 S (oa_cost MT) -> sec_ub m = 0 ->
  fr_SEC cx 0 m ly S.
Proof.
  intros cx S2 S m ly H1 M1 M2 Hu. change (nsec S2 <= nsec (c_S cx) + 0) in M1.
  change (nsec S <= nsec S2 + oa_cost MT) in M2. rewrite sec_oa in M2.
  apply fr_SEC_init; [exact H1 | lia | exact Hu].
Qed.

(* ---- drain: drain's requests (sec_dr45, paid by the drained bytes) and check_no_loss's (15) ---- *)
(* the drained pair's facts the counts read (ReplyLSDrain3.v dr3_rinv) *)
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
Lemma fr_SEC_drain_pre : forall cx t m ly S si h j,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  fr_SEC cx t m ly S ->
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfd Heof Ht HU H.
  destruct (sec_dr_pair cx t m si h j HRI Hpick Hj Hfd Heof HU) as (Hoff & HW & _).
  pose proof (fr_LS3_drain_pre_c4 B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfd Heof Ht HU) as HM.
  rewrite pk_WR_MMAX in HM.
  pose proof (sec_dr45 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h
                Hoff HW ltac:(lia)) as K.
  pose proof Hpick as (_ & _ & Hh).
  assert (Hej : nth_error (lm_es m) j = Some (nth j (lm_es m) dr_e0)) by (apply nth_error_nth'; exact Hj).
  pose proof (sec_ub_pair m si h j (nth j (lm_es m) dr_e0) Hh Hej) as P.
  unfold dr_cost. rewrite sec_tr.
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.

(* top_x LS_cnl_pre's meter conjunct: the row's own conjunct 3 (fr_LS3_cnl_pre_p) gives check_no_loss's count *)
Lemma fr_SEC_cnl_pre : forall cx t m ly S (S' : astate) si h j h'',
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  0 <= t < OPS_MAX -> lm_O m = [] -> dr3_epre (nth j (lm_es m) dr_e0) ->
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
    rewrite pk_WR_MMAX in X. lia. }
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
Lemma fr_SEC_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist) (h1 : hsrc) (E' H' : hlist),
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr3_epre (nth j (lm_es m) dr_e0) ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  hl_recs (hs_pending h1) = [] -> E = hs_expected h1 -> H = hs_held h1 -> h'' = set_exp_held h1 E' H' ->
  ls3_dpost m j h e' h1 -> 0 <= t < OPS_MAX ->
  fr_SEC cx t m ly S -> fr_SEC cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.
Proof.
  intros cx t m ly S S1 ly' S' si h j h'' e' c' O' cap' out' E H h1 E' H' HLS HRI Hat Hpick Hj Hfd Heof Hep M1 M2
    Hpend EE EH Hh'' Hdp Ht HS.
  subst E H.
  destruct Hep as (_ & HU & _).
  destruct (sec_dr_pair cx t m si h j HRI Hpick Hj Hfd Heof HU) as (Hoff & HW & HL & Hc & Hexp & HZr & _).
  pose proof (fr_LS3_drain_pre_c4 B cx t m ly S si h j HLS HRI Hat Hpick Hj Hfd Heof Ht HU) as HM.
  rewrite pk_WR_MMAX in HM.
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
   largest, pk_rr_tr_max) and |re_U e| <= APARTIAL (the kept partial line, the lines' lengths): premises here ---- *)
Lemma sec_rm_pair : forall cx t m si h j0,
  fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  0 <= hs_off h /\
  (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) = 0 ->
     hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
  NoDup (texts (hs_held h)) /\
  same_set (drain_b_c.keys_texts (re_keys (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) (texts (hs_held h)) /\
  fr_pair_cost (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) (h, si) < 2 ^ 26.
Proof.
  intros cx t m si h j0 HRI Hat HU.
  destruct (fr_rm_pair cx t m si h j0 HRI Hat) as (HP & Hcost & HE).
  destruct HP as (_ & _ & _ & Hre & Hss & Hnd & _ & _ & _ & _ & Hoff).
  destruct HE as (_ & _ & _ & _ & Hsk01).
  refine (conj Hoff (conj _ (conj Hnd (conj Hss Hcost)))).
  intros Ho. destruct (Hre Ho) as (Hsk & HskU). exact (sec_hsW _ h Hsk HskU Hsk01 HU).
Qed.

Lemma sec_rm_rr : forall cx t m si h j0,
  fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  21 * nsec_tr (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <=
  21 * 60 + Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) +
    Z.of_nat (length (pending_stream h)).
Proof.
  intros cx t m si h j0 HRI Hat Ht HU.
  pose proof Hat as (_ & _ & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  assert (Hfind : find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]).
  destruct (sec_rm_pair cx t m si h j0 HRI Hat HU) as (Hoff & HW & _).
  assert (HFD : 0 <= hs_fd h).
  { destruct HRI as (_ & (_ & _ & Hrng & _) & _). rewrite Forall_forall in Hrng.
    assert (Hin : In (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) (lm_es m))
      by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply nth_In; exact Hj0).
    specialize (Hrng _ Hin). lia. }
  pose proof (pk_rr_tr_max cx t m si h j0 HRI Hat Ht HU) as HM. unfold pk_TXM in HM.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr in HM |- *.
  pose proof (sec_rr60 (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (hs_fd h) (lm_es m) h
                (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) HFD Hfind
                (fun Ho => conj Hoff (HW Ho)) ltac:(lia)) as K.
  destruct (re_eof (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0) =? 0); lia.
Qed.

Lemma sec_rm_cnl : forall cx t m si h j0 e1 h1 ev LB c2 O2 cap2,
  fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  cnl_cost MT (hs_expected h1) (hs_held h1) <= 15.
Proof.
  intros cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU.
  destruct (fr_rm_facts cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr)
    as (Ls & Hheld & _ & _ & HtE & Hmap & HZr & HWl & _ & _ & _ & _ & HLs).
  destruct (sec_rm_pair cx t m si h j0 HRI Hat HU) as (_ & HW & Hnd & Hss & Hcost).
  apply sec_cnl_le.
  - rewrite HtE, Hheld. exact (sec_cnl_count _ (h, si) (hs_held h) Ls Hnd Hss HWl Hcost).
  - apply (sec_recs_short (hs_expected h1) Ls Hmap).
    destruct HLs as [-> | (Heof & ->)]; [constructor | exact (sec_lines6 h (HW Heof))].
Qed.

(* top_x LS_rm_rr_pre's meter conjunct *)
Lemma fr_SEC_rm_rr_pre : forall cx t m ly S si h j0,
  fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  fr_SEC cx t m ly S -> mo_ok MT S (W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT m h).
Proof.
  intros cx t m ly S si h j0 HRI Hat Ht HU H.
  pose proof (sec_rm_rr cx t m si h j0 HRI Hat Ht HU) as K.
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  assert (Hej : nth_error (lm_es m) j0 = Some (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply nth_error_nth'; exact Hj0).
  pose proof (sec_ub_pair m si h j0 _ Hh Hej) as P.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_cost. rewrite sec_tr.
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia |].
  lia.
Qed.

(* the remove's rows after relay_remove: S is at most rr + (cnl) + (cshe = 0) past S0 *)
Lemma fr_SEC_rm_after : forall cx t m ly0 S0 (S : astate) si h j0 e1 h1 ev LB c2 O2 cap2 X c,
  fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  nsec S <= nsec S0 + nsec_tr (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + X ->
  X + c <= cnl_cost MT (hs_expected h1) (hs_held h1) ->
  fr_SEC cx t m ly0 S0 -> mo_ok MT S c.
Proof.
  intros cx t m ly0 S0 S si h j0 e1 h1 ev LB c2 O2 cap2 X c HRI Hat Hrr Ht HU HS HX H.
  pose proof (sec_rm_rr cx t m si h j0 HRI Hat Ht HU) as K.
  pose proof (sec_rm_cnl cx t m si h j0 e1 h1 ev LB c2 O2 cap2 HRI Hat Hrr HU) as Kc.
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  assert (Hej : nth_error (lm_es m) j0 = Some (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))
    by (unfold W_LLVMFuzzerTestOneInput_remove.rm_ent; apply nth_error_nth'; exact Hj0).
  pose proof (sec_ub_pair m si h j0 _ Hh Hej) as P.
  apply (fr_SEC_ok HKC cx t m ly0 S0 S (nsec_tr (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + X) c H);
    [lia | lia].
Qed.

(* top_x LS_rm_step *)
Lemma fr_SEC_rm_step : forall cx t m ly0 S0 (ly : alayout) (S : astate)
    si h j0 e1 h1 ev LB c2 O2 cap2 out2 E' H' H'' ev5,
  fr_RINV cx t m -> W_LLVMFuzzerTestOneInput_remove.rm_at cx m si h j0 ->
  W_LLVMFuzzerTestOneInput_remove.rm_rr_ok m h j0 e1 h1 ev LB c2 O2 cap2 ->
  mo_le MT S0 S ((W_LLVMFuzzerTestOneInput_remove.rm_rr_cost MT) m h +
                 (W_LLVMFuzzerTestOneInput_remove.rm_cnl_cost MT) (hs_expected h1) (hs_held h1) +
                 (W_LLVMFuzzerTestOneInput_remove.rm_cshe_cost MT) H' +
                 sr_cost MT (Some (set_held (set_exp_held h1 E' H') H''))) ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (W_LLVMFuzzerTestOneInput_remove.rm_ent m j0))) <= APARTIAL ->
  fr_SEC cx t m ly0 S0 ->
  fr_SEC cx (t + 1) (W_LLVMFuzzerTestOneInput_remove.rm_mk cx m si None j0
                       (W_LLVMFuzzerTestOneInput_remove.rm_cev c2 ev5) O2 cap2 out2) ly S.
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
           (nsec_tr (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) + cnl_cost MT (hs_expected h1) (hs_held h1))
           Ht ltac:(lia)); [|exact HS].
  pose proof Hat as (_ & _ & _ & _ & _ & Hh & Hj0 & _).
  pose proof (nth_some_error _ _ _ Hh) as Hhi.
  unfold sec_ub. cbn [W_LLVMFuzzerTestOneInput_remove.rm_mk lm_hs lm_es].
  pose proof (rm3_set_zsum _ sec_str si None (Some h) (lm_hs m) Hhi) as Zp.
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
   reads relay_finish's room (LS_rf_room, at 0 <= t <= OPS_MAX) and the entries' keys not empty: premises here ---- *)
Lemma sec_exit_cost : forall m bb,
  lx_rf_room CfParamsReply.fr_MMAX bb (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  lx_exit_cost MT m <= 15.
Proof.
  intros m bb Hroom Hk. unfold lx_exit_cost. rewrite sec_ends, sec_srt, xrf_cost_eq.
  assert (R : rf_room CfParamsReply.fr_MMAX bb (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m))
    by (eapply xrf_room_eq; exact Hroom).
  pose proof (ReplyKfTrSm.kf_rf_cost MT sec_HMs sec_HFs CfParamsReply.fr_MMAX bb (lm_c m) [] (lm_mx m) 0 (lm_cap m)
                (lm_es m) CfParamsReply.reply_HMMAX Hk R) as K.
  assert (K2 : ReplyKfTrSm.KC_rf = 15) by reflexivity. lia.
Qed.
(* top_x LS_exit_budget *)
Lemma fr_SEC_exit_budget : forall cx t m ly S,
  lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) ->
  Forall (fun e => Forall (fun x : list byte => x <> []) (gse_keys e)) (lm_es m) ->
  fr_SEC cx t m ly S -> mo_ok MT S (lx_exit_cost MT m).
Proof.
  intros cx t m ly S Hroom Hk H. pose proof (sec_exit_cost m _ Hroom Hk) as K. pose proof (sec_ub_nonneg m).
  apply (fr_SEC_ok HKC cx t m ly S S 0); [exact H | lia | lia].
Qed.
(* top_x LS_exit_end's meter conjunct: the call's count at its end, freeing the frame (set_fs) does not change nsec *)
Lemma fr_SEC_exit_end : forall cx t m ly3 S3 (S' : astate) C fpos,
  (forall f s, nsec (set_fs f s) = nsec s) ->
  mo_le MT S3 S' C -> C <= lx_exit_cost MT m ->
  lx_rf_room CfParamsReply.fr_MMAX (blocks_bytes S3) (lm_c m) [] (lm_mx m) 0 (lm_cap m) (lm_es m) ->
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
