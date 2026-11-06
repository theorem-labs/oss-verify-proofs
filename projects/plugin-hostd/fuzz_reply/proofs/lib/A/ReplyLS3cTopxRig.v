(* The conjuncts of the gone arm's LS_gone_rig at its former sum-form text (W8's GN_LS_rig at 1fcc03569d3; gone_base's
   GN_LS_rig is now the peak text, ReplyLS3Peak.v's former TX_GN_LS_rig, proved there by pk_gone_rig from the pieces
   below) at the instance LS := fr_LS3 B (and fr_LS3c B, by
   its first projection), RINV := fr_RINV, MT := ameter_triv, MMAX := WR_MMAX.  proves no function (kind: invariant
   lemma).  tr := rig_tr (lm_c m) (lm_mx m) |lm_O m| (lm_cap m) (gn_id cx m) (lm_es m) hs (W_contract.v rig_tr;
   lib/Prog/relay_instance_gone_b_c.v relay_instance_gone_tr :79, gone_run :60): for each relay entry in table order,
   drain (s) when it is open, then the gesture ends of the held keys with the instance prefix.  Its five conjuncts:
   (R1) tr_max tr < MMAX: PROVED at a PROPOSED text (fr_LS3_gone_rig_c1) with three premises the gone arm holds where
        it applies LS_gone_rig (gone_p3.v:995, in gp3_rig_c1 from the cut point GRG, _gone_base.v:656-664):
          `lm_O m = []` and `0 <= t < OPS_MAX` - gn_op (_gone_base.v:355-356), GRG's clause :659, destructed as HOP at
            gone_p3.v:914;
          `Forall (fun e => |re_U e| <= APARTIAL) (lm_es m)` - aentry_ok (W_rep.v:125 on integ, `|re_U e| = re_used e /\
            re_used e <= APARTIAL`) of every entry: arelay_at's clause W_rep.v:162 `Forall (aentry_ok ..) es`, in
            amodel_at (_cut.v:379), which GRG carries through gst (_gone_base.v:630, :658); gone_p3.v:924 destructs
            it as HREL.
        fr_LS3 and fr_RINV give none of the three: fr_RINV says nothing of lm_O (ReplyRINV.v:219-226), so the run's
        starting g_nout and every send growth 2 * (g_nout + len) are free; the two drain facts are the reasons
        ReplyLSDrainPre.v's header gives (pending 2^25 + 2 NULs and 32 * 2^25 for t >= 513; re_U unbounded at
        re_skip = 1 and 2 re_cap >= 2^30).  The bound: one induction over the table (grg_run_rq) with the drain
        requests from dpre_drain_run at g_nout = no (Hk = |keys| - no), the key run by rrp_ker, and g_nout growing by
        at most 2 * cost per entry (grg_entry_no: drain adds the pending bytes and the kept line, rrp_drain_kw / rm3_dm_run,
        the key run at most the held keys' bytes, grg_xks_le), against fr_relay's fr_cost <= c_n < 2^26 (the pair of
        each open entry is fr_relay's row: grg_pair_pt).  Every request is at most
        max (2 (2 c_n + 6000), 8 (c_n + 6000), 32 (65535 * 511 - 1), 20192) < WR_MMAX.
   (R2) blocks_bytes S + tr_alloc tr <= LIVE_MAX: NOT PROVABLE (false at reachable states).  tr_alloc sums every request
        size, and the drain inside relay_instance_gone of ONE open source regrows the relay's held-key array by one
        slot per new begin line (drain_b_c.seen_tr, RRealloc ka ((|H| + 1) * 8)), so N new begins ask >= 4 N (N + 1)
        bytes: for N = 65,536 (about 1.6 MB of pending input, which fr_RINV allows with t < OPS_MAX and c_n < 2^26)
        that is 17,180,131,328 > LIVE_MAX = 2^34, whatever blocks_bytes S is.  Measured: grg_probe_300 below (one open
        source of 300 new begins through rig_tr itself: its tr_alloc is one drain's, ReplyTrPeak.v pr_probe_300,
        423,948 bytes, with peak 42,341), ReplyTrPeak.v pr_probe_999 (999 begins: tr_alloc 4,131,438, peak 108,959),
        and W8Add's 65,520 begins at 17,184,602,328 requested bytes (ReplyLSDrainPre.v:22-28).  Even LS v3's exact
        spare (fr_LS3_room_x: blocks_bytes S + 4,160,659,073 <= LIVE_MAX) is passed at N >= 32,252, and up to four
        drains and four key runs add to the same sum.
   (R3) mo_ok MT S (tr_cost MT tr): vacuous at ameter_triv (mo_ok is True; fr_LS3_gone_rig_c3).
   (R4) lm_cap m < MMAX: PROVED with ONE named hypothesis Hcap : lm_cap m <= 2 ^ 29 (fr_LS3_gone_rig_c4), as
        ReplyLS3Arms.v fr_LS3_rm_rr_pre_cap :1004: fr_RINV says nothing of lm_cap (ReplyRINV.v:219-226) and fr_LS3
        bounds it only through PHI3 (aout_blks (lm_cap m) (lm_out m) is a model block), about 2^33.  The program keeps
        it [INFERENCE]: g_capout only grows, by send_line to 2 (g_nout + len), and every operation starts at g_nout = 0
        (gn_op, the head's lm_clear_O); for gone this file bounds every send growth (g_capout's new size) by
        2 (2 c_n + 6000) < 2^28 + 2^14.
   (R5) blocks_bytes S + tr_alloc tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX: NOT PROVABLE, for R2's reason:
        4 * Z.max (lm_cap m) (tr_max tr) >= 0 (tr_max >= 0), so R5 implies R2.
   The peak form of R2 (cause C3, ReplyTrPeak.v tr_peak) IS provable: fr_LS3_gone_rig_c2p, `blocks_bytes S + tr_peak tr
   + 636848 <= LIVE_MAX`, at R1's premises and the model blocks' sizes not negative (ReplyTrPeak.v
   fr_LS_rm_rr_pre_c3p's premise; the gone arm has amodel_at at GRG, from which the remove arm's rr_blks_pos
   (_remove.v:2257 on integ) proves it).  tr_peak <= tr_pos + tr_max (tr_peak_le_pos), tr_pos of the run <= 4 c_n
   (g_capout from cap to at most max cap (2 g_nout)) + per open entry 42 P + 8 K + 80320 (grg_entry_pos, tp_dr's
   accounting at any g_nout), at most four entries (fr_relay's slots), so tr_peak <= 46 c_n + 321280 + (WR_MMAX - 1)
   = 4,160,022,225 at most, 636,848 under LS v3's 4,160,659,073.  The form with `+ tr_max tr` (ReplyTrPeak.v's variant
   (b)) is NOT proved here: it would need 1,072,693,247 more bytes than these bounds leave. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3 ReplyTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the instance (ReplyATop.v:93 MT := ameter_triv; W_LLVMFuzzerTestOneInput_write.v:132 WR_MMAX) *)
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).

(* ================================================================== each pair's facts and cost *)
(* the input cost the run reads off one (entry, source) pair: the gesture ends of its keys and, when the entry is open,
   the pending bytes and the kept line (fr_pair_cost's terms; the source's terms only when drain reads it) *)
Definition grg_cost (p : rentry * (hsrc * nat)) : Z :=
  gestures_end_b_c.keys_total (re_keys (fst p)) +
  (if re_eof (fst p) =? 0 then
     Z.of_nat (length (pending_stream (fst (snd p)))) +
     (if re_skip (fst p) =? 0 then Z.of_nat (length (re_U (fst p))) else 0)
   else 0).
(* what drain's request bound reads of an open pair (ReplyLSDrainPre.v dpre_dr_tr_max's premises) *)
Definition grg_ok (p : rentry * (hsrc * nat)) : Prop :=
  (re_skip (fst p) = 0 \/ re_skip (fst p) = 1) /\
  (re_eof (fst p) = 0 ->
     Z.of_nat (length (re_U (fst p))) <= APARTIAL /\
     (hs_overlong (fst (snd p)) = 1 \/ bzs (re_U (fst p)) = bzs (hs_W (fst (snd p)))) /\
     0 <= hs_off (fst (snd p)) /\ hl_recs (hs_expected (fst (snd p))) = [] /\
     Z.of_nat (length (pending_stream (fst (snd p)))) <= 65535 * 511 /\
     0 <= hl_cap (hs_expected (fst (snd p)))).

Lemma grg_cost_nonneg : forall p, 0 <= grg_cost p.
Proof.
  intros p. unfold grg_cost. pose proof (fr_keys_total_nonneg (re_keys (fst p))).
  destruct (re_eof (fst p) =? 0); [destruct (re_skip (fst p) =? 0)|]; lia.
Qed.

(* ================================================================== the keys gestures_end_instance ends *)
Lemma grg_geia_loop_perm : forall fuel pre n H,
  Permutation (fst (relay_instance_gone_b_c.geia_loop fuel pre n H) ++
               snd (relay_instance_gone_b_c.geia_loop fuel pre n H)) H.
Proof.
  induction fuel as [|f IH]; intros pre n H; cbn [relay_instance_gone_b_c.geia_loop].
  - cbn [fst snd app]. apply Permutation_refl.
  - destruct (Nat.ltb_spec n (length H)) as [Hn|Hn].
    + match goal with |- context [if ?b then _ else _] => destruct b end.
      * match goal with |- context [relay_instance_gone_b_c.geia_loop f pre n ?H2] =>
          pose proof (IH pre n H2) as IHn; destruct (relay_instance_gone_b_c.geia_loop f pre n H2) as [E H'] end.
        cbn [fst snd app] in IHn |- *.
        eapply perm_trans; [apply perm_skip; exact IHn|].
        match goal with |- Permutation (nth n H ?d :: _) _ =>
          destruct (nth_split H d Hn) as (l1 & l2 & EH & EL); set (x := nth n H d) in *; clearbody x end.
        rewrite EH, <- EL. apply Permutation_sym, swap_remove_perm.
      * apply IH.
    + cbn [fst snd app]. apply Permutation_refl.
Qed.

Lemma grg_combine_kw : forall (A : Type) (H : list (list Z)) (ks : list A),
  zsum (map (fun x => Z.of_nat (length (fst x)) + 5) (combine H ks)) <= rm3_kw H.
Proof.
  intros A H. unfold rm3_kw. induction H as [|x H IH]; intros [|k ks]; cbn [combine map fold_right fst]; try lia.
  - pose proof (zsum_map_nonneg (fun y : list Z => Z.of_nat (length y) + 5) H ltac:(intros; cbv beta; lia)). lia.
  - specialize (IH ks). lia.
Qed.

(* the ended keys' bytes with their 5 end bytes are at most the held keys' (geia keeps the rest) *)
Lemma grg_xks_le : forall pre (H : list (list Z)) (ks : list (RelayRunT.addr YO0i.sptr)),
  fold_right (fun x acc => fst x + 5 + acc) 0
    (map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (relay_instance_gone_b_c.geia pre (combine H ks))))
  <= rm3_kw H.
Proof.
  intros pre H ks.
  pose proof (grg_geia_loop_perm (length (combine H ks)) pre 0 (combine H ks)) as HP.
  pose proof (fr_sum_perm _ (fun x : list Z * RelayRunT.addr YO0i.sptr => Z.of_nat (length (fst x)) + 5) _ _ HP)
    as ES.
  rewrite map_app, zsum_app in ES.
  pose proof (zsum_map_nonneg (fun x : list Z * RelayRunT.addr YO0i.sptr => Z.of_nat (length (fst x)) + 5)
                (snd (relay_instance_gone_b_c.geia_loop (length (combine H ks)) pre 0 (combine H ks)))
                ltac:(intros; cbv beta; lia)) as N.
  pose proof (grg_combine_kw _ H ks) as C.
  assert (E1 : forall E : list (list Z * RelayRunT.addr YO0i.sptr),
    fold_right (fun x acc => fst x + 5 + acc) 0 (map (fun x => (Z.of_nat (length (fst x)), snd x)) E) =
    zsum (map (fun x => Z.of_nat (length (fst x)) + 5) E)).
  { induction E as [|y E IHE]; cbn [map fold_right fst]; lia. }
  rewrite E1. unfold relay_instance_gone_b_c.geia. lia.
Qed.

Lemma grg_fold_fst : forall (A : Type) (l : list (Z * A)),
  fold_right (fun xl acc => xl + 5 + acc) 0 (map fst l) = fold_right (fun x acc => fst x + 5 + acc) 0 l.
Proof. intros A l. induction l as [|x l IH]; cbn [map fold_right]; lia. Qed.

Lemma grg_fold_nonneg : forall (A : Type) (l : list (Z * A)), Forall (fun x => 0 <= fst x) l ->
  0 <= fold_right (fun x acc => fst x + 5 + acc) 0 l.
Proof. intros A l H. induction H as [|x l Hx _ IH]; cbn [fold_right]; lia. Qed.

(* ================================================================== one step of relay_instance_gone's run *)
Lemma grg_run_cons : forall lv mx no cap pre e (hj : hsrc * nat) r nm j o,
  let s := relay_remove_b_c.after_drain lv mx no cap e (fst hj) in
  let a0 := drain_b_c.drain_start nm o e (fst hj) in
  let td := if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else [] in
  let a := relay_remove_b_c.after_drain_adr lv mx no cap e (fst hj) j a0 in
  let xks := map (fun x => (Z.of_nat (length (fst x)), snd x))
               (fst (relay_instance_gone_b_c.geia pre (combine (drain_b_c.ds_H s) (drain_b_c.da_keys a)))) in
  let k := gestures_end_b_c.keys_end_run lv mx (drain_b_c.ds_no s) (drain_b_c.ds_ocap s) xks
             (j + RelayRunT.nret _ td)%nat (drain_b_c.da_out a) in
  fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ((e, hj) :: r) nm j o))) =
    td ++ fst k ++ fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx
      (drain_b_c.ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst xks)) (fst (snd k)) pre r nm
      (j + RelayRunT.nret _ td + RelayRunT.nret _ (fst k))%nat (snd (snd k))))).
Proof.
  intros lv mx no cap pre e hj r nm j o. cbv zeta. cbn [relay_instance_gone_b_c.gone_run].
  match goal with |- context [relay_instance_gone_b_c.gone_run ?a1 ?a2 ?a3 ?a4 ?a5 r ?a6 ?a7 ?a8] =>
    destruct (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 r a6 a7 a8) as [[[x1 x2] x3] [x4 x5]] end.
  reflexivity.
Qed.

(* ================================================================== one entry *)
(* drain's g_nout and the keys it leaves, from g_nout = no: at most no + 2 * the pair's cost *)
Lemma grg_entry_no : forall lv mx no cap (e : rentry) (hj : hsrc * nat),
  grg_ok (e, hj) ->
  drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) +
    rm3_kw (drain_b_c.ds_H (relay_remove_b_c.after_drain lv mx no cap e (fst hj))) <= no + 2 * grg_cost (e, hj).
Proof.
  intros lv mx no cap e hj (Hsk & Hop).
  unfold grg_cost. cbn [fst snd] in Hsk, Hop |- *.
  pose proof (fr_keys_total_nonneg (re_keys e)) as HKT.
  unfold relay_remove_b_c.after_drain.
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; cbv iota.
  - destruct (Hop Eo) as (HU & HJ & Hoff & Hexp & Hp & _).
    unfold drain_b_c.drain_fin, drain_b_c.drain_go.
    pose proof (rm3_dm_run (S (S (length (pending_stream (fst hj))))) lv mx (drain_b_c.drain_init no cap e (fst hj))
                  0%nat drain_b_c.dadr0 Hoff) as D.
    pose proof (rrp_drain_kw (S (S (length (pending_stream (fst hj))))) lv mx (drain_b_c.drain_init no cap e (fst hj))
                  0%nat drain_b_c.dadr0) as W.
    unfold rm3_dm at 2 in D. rewrite rm3_dstr_init in D.
    cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_skip drain_b_c.ds_u drain_b_c.ds_H] in D, W.
    rewrite !RelayCap.rc_length_bzs in D.
    rewrite <- rm3_kt_kw in W.
    rewrite (rm3_skip_if (re_skip e) (Z.of_nat (length (re_U e))) Hsk) in D.
    assert (HX : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
      by (destruct (re_skip e =? 0); lia).
    revert D W.
    generalize (fst (snd (drain_b_c.drain_run (S (S (length (pending_stream (fst hj))))) lv mx
                  (drain_b_c.drain_init no cap e (fst hj)) 0%nat drain_b_c.dadr0))).
    intros s D W. unfold rm3_dm in D.
    destruct (drain_b_c.ds_skip s); lia.
  - cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_H]. rewrite <- rm3_kt_kw. lia.
Qed.

(* the drain's requests when the entry is open (dpre_drain_run from g_nout = no: Hk = |keys| - no) *)
Lemma grg_entry_tr : forall lv mx no cap (e : rentry) (hj : hsrc * nat) j (a0 : drain_b_c.dadr) M K,
  grg_ok (e, hj) -> grg_cost (e, hj) <= K ->
  2 * (no + 2 * grg_cost (e, hj) + 6000) <= M -> 8 * (K + 6000) <= M -> 1071628288 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else []).
Proof.
  intros lv mx no cap e hj j a0 M K (Hsk & Hop) HK HM H8 H32 Hg.
  unfold grg_cost in HK, HM. cbn [fst snd] in Hsk, Hop, HK, HM.
  pose proof (fr_keys_total_nonneg (re_keys e)) as HKT.
  pose proof (dpre_keys_le (re_keys e)) as Hkl.
  revert HK HM. destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; intros HK HM; cbv iota in HK, HM |- *;
    [|constructor].
  destruct (Hop Eo) as (HU & HJ & Ho & He & Hp & _).
  assert (Hu : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  unfold drain_b_c.drain_tr, drain_b_c.drain_go.
  apply (dpre_drain_run _ _ _ _ _ _ M (Z.of_nat (length (re_keys e)) - no)
           (no + 6000 + Z.of_nat (length (pending_stream (fst hj)))) (Z.of_nat (length (pending_stream (fst hj)))));
    [| lia ..].
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

(* ================================================================== the run's requests *)
Lemma grg_run_rq : forall ps lv mx pre nm no cap j o M K,
  Forall grg_ok ps -> zsum (map grg_cost ps) <= K ->
  2 * (no + 2 * zsum (map grg_cost ps) + 6000) <= M -> 8 * (K + 6000) <= M -> 1071628288 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx pre nm no cap j o M K HF HK HM H8 H32 Hg.
  { cbn [relay_instance_gone_b_c.gone_run fst]. constructor. }
  apply Forall_cons_iff in HF as [Hok HF].
  cbn [map fold_right] in HK, HM.
  pose proof (grg_cost_nonneg (e, hj)) as Hc0.
  pose proof (zsum_map_nonneg grg_cost r grg_cost_nonneg) as Hr0.
  pose proof (grg_entry_no lv mx no cap e hj Hok) as HN.
  pose proof (grg_run_cons lv mx no cap pre e hj r nm j o) as EC. cbv zeta in EC. rewrite EC. clear EC.
  apply Forall_app. split.
  { apply (grg_entry_tr _ _ _ _ _ _ _ _ M K Hok); lia. }
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

(* ================================================================== the pairs, from fr_RINV *)
Lemma grg_zsum_le : forall (X Y : Type) (f : X -> Z) (g : Y -> Z) (l1 : list X) (l2 : list Y) dx dy,
  length l1 = length l2 -> (forall i, (i < length l1)%nat -> f (nth i l1 dx) <= g (nth i l2 dy)) ->
  zsum (map f l1) <= zsum (map g l2).
Proof.
  intros X Y f g l1. induction l1 as [|x l1 IH]; intros [|y l2] dx dy HL HI; cbn [length] in HL; try lia.
  - cbn. lia.
  - cbn [map fold_right]. pose proof (HI 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0.
    assert (HI' : forall i, (i < length l1)%nat -> f (nth i l1 dx) <= g (nth i l2 dy)).
    { intros i Hi. exact (HI (S i) ltac:(cbn [length]; lia)). }
    pose proof (IH l2 dx dy ltac:(lia) HI') as IHr. lia.
Qed.

Section grig.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* an open entry's pair in gn_pairs is the entry's row of fr_relay (one source per fd among the open slots) *)
Lemma grg_pair_pt : forall cx t m e p q,
  fr_RINV cx t m -> 0 <= t < OPS_MAX -> fr_pair_ok m t e q -> fr_entry_ok e ->
  Z.of_nat (length (re_U e)) <= APARTIAL -> (re_eof e = 0 -> gn_pair_ok m e p) ->
  grg_ok (e, p) /\ grg_cost (e, p) <= fr_pair_cost e q.
Proof.
  intros cx t m e p q HRI Ht Hq Hent HUe Hp.
  destruct Hq as (Hq4 & Hqn & Hqf & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff).
  destruct Hent as (_ & _ & _ & _ & Hsk).
  pose proof (fr_keys_total_nonneg (re_keys e)) as HKT.
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HX : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  unfold grg_ok, grg_cost, fr_pair_cost. cbn [fst snd].
  destruct (Z.eq_dec (re_eof e) 0) as [Eo|Eo].
  - destruct (Hp Eo) as (Hp4 & Hpn & Hpf & _).
    assert (Es : fst p = fst q).
    { destruct (Nat.eq_dec (snd p) (snd q)) as [E|E].
      - rewrite E, Hqn in Hpn. injection Hpn as Hpq. exact (eq_sym Hpq).
      - exfalso. apply (RI_fds_holds cx t m (snd p) (snd q) (fst p) (fst q) HRI Hp4 Hq4 E Hpn Hqn).
        rewrite Hpf, Hqf. reflexivity. }
    rewrite Es. destruct (Hre Eo) as (Eov & HW).
    rewrite (proj2 (Z.eqb_eq _ _) Eo). cbv iota.
    split; [split; [exact Hsk|] | lia].
    intros _. split; [exact HUe|]. split.
    + destruct (Z.eq_dec (hs_overlong (fst q)) 1) as [E1|E1]; [left; exact E1 | right]. apply HW. lia.
    + split; [exact Hoff|]. split; [exact Hexp|]. split; [|lia].
      unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
  - rewrite (proj2 (Z.eqb_neq _ _) Eo). cbv iota.
    split; [split; [exact Hsk | intros E; contradiction] |].
    pose proof (Nat2Z.is_nonneg (length (pending_stream (fst q)))). lia.
Qed.

(* the run's pairs: each grg_ok, their cost within the input (fr_relay's fr_cost <= c_n), at most four entries *)
Lemma grg_pairs : forall cx t m hs,
  fr_RINV cx t m -> gn_pairs m hs -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  Forall grg_ok (combine (lm_es m) hs) /\ zsum (map grg_cost (combine (lm_es m) hs)) <= c_n cx /\
  c_n cx < 2 ^ 26 /\ (length (lm_es m) <= 4)%nat.
Proof.
  intros cx t m hs HRI HP Ht HUs.
  pose proof HRI as (_ & HR & Hn & _).
  destruct HR as (Hlen & Hnd & _ & Hent & hj & HF & HNDs & _ & _ & Hcn).
  destruct HP as (HLhs & HFa & _).
  pose proof (Forall2_length HF) as Lhj.
  assert (HI : forall i, (i < length (lm_es m))%nat ->
    grg_ok (nth i (lm_es m) gn_e0, nth i hs gn_hj0) /\
    grg_cost (nth i (lm_es m) gn_e0, nth i hs gn_hj0) <= fr_pair_cost (nth i (lm_es m) gn_e0) (nth i hj gn_hj0)).
  { intros i Hi.
    assert (He : In (nth i (lm_es m) gn_e0) (lm_es m)) by (apply nth_In; exact Hi).
    apply (grg_pair_pt cx t m _ _ _ HRI Ht (fr_F2_nth _ _ _ _ _ HF i gn_e0 gn_hj0 Hi)).
    - rewrite Forall_forall in Hent. exact (Hent _ He).
    - rewrite Forall_forall in HUs. exact (HUs _ He).
    - intros Eo.
      assert (Hin : In (nth i (lm_es m) gn_e0, nth i hs gn_hj0) (combine (lm_es m) hs)).
      { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
      exact (proj1 (Forall_forall _ _) HFa _ Hin Eo). }
  split; [|split; [|split]].
  - apply Forall_forall. intros x Hx.
    apply (In_nth _ _ (gn_e0, gn_hj0)) in Hx as (i & Hi & <-).
    rewrite length_combine in Hi.
    rewrite combine_nth by lia. apply (HI i). lia.
  - eapply Z.le_trans; [|exact Hcn]. unfold fr_cost.
    apply (grg_zsum_le _ _ grg_cost (fun q => fr_pair_cost (fst q) (snd q)) (combine (lm_es m) hs)
             (combine (lm_es m) hj) (gn_e0, gn_hj0) (gn_e0, gn_hj0)).
    + rewrite !length_combine. lia.
    + intros i Hi. rewrite length_combine in Hi. rewrite !combine_nth by lia. cbn [fst snd]. apply HI. lia.
  - exact Hn.
  - assert (H4 : forall x, In x (map snd hj) -> In x (seq 0 4)).
    { intros x Hx. apply in_map_iff in Hx as (q & <- & Hq).
      apply (In_nth _ _ gn_hj0) in Hq as (i & Hi & <-).
      destruct (fr_F2_nth _ _ _ _ _ HF i gn_e0 gn_hj0 ltac:(lia)) as (Hs4 & _).
      apply in_seq. lia. }
    pose proof (List.NoDup_incl_length (proj1 (NoDup_ListNoDup _) HNDs) H4) as HL.
    rewrite length_map, length_seq in HL. lia.
Qed.

(* ================================================================== the rules *)
(* (R1) GN_LS_rig's first conjunct, at the PROPOSED text: the published premises and the three gn_op / aentry_ok
   facts the gone arm holds at gone_p3.v:995 (HOP from GRG :659, HREL from GRG's amodel_at) *)
Lemma fr_LS3_gone_rig_c1 : forall cx t m ly S hs,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) < MMAX.
Proof.
  intros cx t m ly S hs _ HRI HP HO Ht HUs.
  destruct (grg_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & _).
  rewrite HO. cbn [length Z.of_nat].
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr. cbv zeta.
  assert (EM : WR_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  pose proof (zsum_map_nonneg grg_cost (combine (lm_es m) hs) grg_cost_nonneg) as H0.
  apply (Z.le_lt_trans _ (WR_MMAX - 1)); [|lia].
  apply dpre_tr_max; [lia|].
  apply (grg_run_rq _ _ _ _ _ 0 _ _ _ (WR_MMAX - 1) (c_n cx) HF HC); lia.
Qed.

(* (R3) GN_LS_rig's third conjunct: mo_ok is True at ameter_triv *)
Lemma fr_LS3_gone_rig_c3 : forall cx t m ly S hs,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  mo_ok MT S (tr_cost MT (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m)
                            (lm_es m) hs)).
Proof. intros. exact I. Qed.

(* (R4) GN_LS_rig's fourth conjunct, with the named extra fact Hcap (neither fr_LS3 nor fr_RINV bounds lm_cap) *)
Lemma fr_LS3_gone_rig_c4 : forall cx t m ly S hs,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  lm_cap m < MMAX.
Proof. intros cx t m ly S hs _ _ _ Hcap. assert (EM : WR_MMAX = 1072693248) by reflexivity. lia. Qed.

(* R1, R3 and R4 together, at R1's PROPOSED text and with Hcap *)
Lemma fr_LS3_gone_rig_134 : forall cx t m ly S hs,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ mo_ok MT S (tr_cost MT tr) /\ lm_cap m < MMAX.
Proof.
  intros cx t m ly S hs HLS HRI HP HO Ht HUs Hcap tr.
  split; [exact (fr_LS3_gone_rig_c1 cx t m ly S hs HLS HRI HP HO Ht HUs)|].
  split; [exact I | exact (fr_LS3_gone_rig_c4 cx t m ly S hs HLS HRI HP Hcap)].
Qed.

(* the same at fr_LS3c (its first projection is fr_LS3) *)
Lemma fr_LS3c_gone_rig_c1 : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) < MMAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_c1 cx t m ly S hs (proj1 H)). Qed.
Lemma fr_LS3c_gone_rig_c3 : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  mo_ok MT S (tr_cost MT (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m)
                            (lm_es m) hs)).
Proof. intros. exact I. Qed.
Lemma fr_LS3c_gone_rig_c4 : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  lm_cap m < MMAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_c4 cx t m ly S hs (proj1 H)). Qed.
Lemma fr_LS3c_gone_rig_134 : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  forall (Hcap : lm_cap m <= 2 ^ 29),
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ mo_ok MT S (tr_cost MT tr) /\ lm_cap m < MMAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_134 cx t m ly S hs (proj1 H)). Qed.
End grig.

(* ================================================================== the peak form of R2 (cause C3) *)
(* the per-entry facts the summed positive growth reads: the entry's buffer and held-array sizes not negative *)
Definition grg_okp (p : rentry * (hsrc * nat)) : Prop :=
  grg_ok p /\ 0 <= re_cap (fst p) /\ 0 <= drain_b_c.ent_ka (fst p).
(* an open entry's drain: at most 42 per pending byte, 8 per held key and 80320 beyond its g_capout growth *)
Definition grg_pc (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then
    42 * Z.of_nat (length (pending_stream (fst (snd p)))) + 8 * Z.of_nat (length (re_keys (fst p))) + 80320
  else 0.

Lemma grg_pc_nonneg : forall p, 0 <= grg_pc p.
Proof. intros p. unfold grg_pc. destruct (re_eof (fst p) =? 0); lia. Qed.
Lemma grg_pc_le : forall p, grg_pc p <= 42 * grg_cost p + 80320.
Proof.
  intros p. unfold grg_pc, grg_cost. pose proof (fr_keys_total_nonneg (re_keys (fst p))).
  pose proof (dpre_keys_le (re_keys (fst p))).
  destruct (re_eof (fst p) =? 0); [destruct (re_skip (fst p) =? 0)|]; lia.
Qed.
Lemma grg_zsum_pc : forall l, zsum (map grg_pc l) <= 42 * zsum (map grg_cost l) + 80320 * Z.of_nat (length l).
Proof. induction l as [|p l IH]; cbn [map fold_right length]; [lia|]. pose proof (grg_pc_le p). lia. Qed.

(* one entry: its drain's summed positive growth (tp_dr's accounting, ReplyTrPeak.v, at any g_nout) and its g_capout *)
Lemma grg_entry_pos : forall lv mx no cap (e : rentry) (hj : hsrc * nat) j (a0 : drain_b_c.dadr),
  grg_okp (e, hj) -> 0 <= cap ->
  tr_pos (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else []) + cap <=
    drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) + grg_pc (e, hj) /\
  0 <= drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) /\
  drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) <=
    Z.max cap (2 * drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e (fst hj))).
Proof.
  intros lv mx no cap e hj j a0 ((Hsk & Hop) & Hrc & Hka) Hcap.
  unfold grg_pc. cbn [fst snd] in Hsk, Hop, Hrc, Hka |- *.
  unfold relay_remove_b_c.after_drain.
  destruct (Z.eqb_spec (re_eof e) 0) as [Eo|Eo]; cbv iota.
  - destruct (Hop Eo) as (HU & HJ & Hoff & Hexp & Hp & Hec).
    unfold APARTIAL in HU.
    assert (HI : tp_inv (Z.max (re_cap e) 20192)
                   (Z.max (hl_cap (hs_expected (fst hj))) (Z.max 8 (2 * Z.of_nat (length (pending_stream (fst hj))))))
                   (Z.of_nat (length (pending_stream (fst hj)))) (drain_b_c.drain_init no cap e (fst hj))).
    { unfold tp_inv, tp_R. rewrite rm3_dstr_init, RelayCap.rc_length_bzs.
      unfold drain_b_c.drain_init. tp_projg. unfold hl_n. rewrite Hexp, RelayCap.rc_length_bzs. cbn [length]. lia. }
    assert (PS0 : tp_psi (drain_b_c.drain_init no cap e (fst hj)) =
      re_cap e + 16 * hl_cap (hs_expected (fst hj)) + cap -
      tp_kdef (drain_b_c.keys_texts (re_keys e)) (drain_b_c.ent_ka e) -
      SlotReads.wcost (hs_state (fst hj)) - 10 * Z.of_nat (length (pending_stream (fst hj))) -
      9 * (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e)))).
    { unfold tp_psi, tp_R, tp_U. rewrite rm3_dstr_init, RelayCap.rc_length_bzs.
      unfold drain_b_c.drain_init. tp_projg. rewrite RelayCap.rc_length_bzs. reflexivity. }
    destruct (tp_drain_run (S (S (length (pending_stream (fst hj))))) lv mx (drain_b_c.drain_init no cap e (fst hj))
                j a0 (Z.max (re_cap e) 20192)
                (Z.max (hl_cap (hs_expected (fst hj))) (Z.max 8 (2 * Z.of_nat (length (pending_stream (fst hj))))))
                (Z.of_nat (length (pending_stream (fst hj)))) ltac:(lia) ltac:(lia) HI) as [T1 T2].
    pose proof (RelayCap.drain_ocap_le lv mx no cap e (fst hj)) as [N1 OC].
    pose proof (RelayCap.rc_drain_state (S (S (length (pending_stream (fst hj))))) lv mx
                  (drain_b_c.drain_init no cap e (fst hj)) j a0 0%nat drain_b_c.dadr0) as ES.
    rewrite ES in T1, T2.
    unfold drain_b_c.drain_tr, drain_b_c.drain_fin, drain_b_c.drain_go in *.
    assert (KD : tp_kdef (drain_b_c.keys_texts (re_keys e)) (drain_b_c.ent_ka e) <=
                 8 * Z.of_nat (length (re_keys e))).
    { unfold tp_kdef, drain_b_c.keys_texts. rewrite length_map. lia. }
    assert (WC : SlotReads.wcost (hs_state (fst hj)) <= 6000).
    { unfold SlotReads.wcost, hs_state. cbn [ls_k ls_w].
      destruct HJ as [E|E]; [rewrite E; cbn; lia|].
      destruct (hs_overlong (fst hj) =? 1); [lia|]. rewrite <- E, RelayCap.rc_length_bzs. lia. }
    assert (HX : 0 <= (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e))) <= 6000)
      by (destruct (re_skip e =? 1); lia).
    revert T1 T2 OC N1.
    generalize (fst (snd (drain_b_c.drain_run (S (S (length (pending_stream (fst hj))))) lv mx
                  (drain_b_c.drain_init no cap e (fst hj)) 0%nat drain_b_c.dadr0))) as fin.
    generalize (fst (drain_b_c.drain_run (S (S (length (pending_stream (fst hj))))) lv mx
                  (drain_b_c.drain_init no cap e (fst hj)) j a0)) as tr.
    intros tr fin T1 T2 OC N1.
    assert (PSF : tp_psi fin <= drain_b_c.ds_cap fin + 16 * drain_b_c.ds_ecap fin + drain_b_c.ds_ocap fin).
    { unfold tp_psi, tp_kdef, tp_R, tp_U. pose proof (SlotReads.wcost_nonneg (drain_b_c.ds_ref fin)).
      destruct (drain_b_c.ds_skip fin); lia. }
    destruct T2 as (F1 & F2 & F3 & _).
    split; [lia | split; lia].
  - cbn [drain_b_c.drain_init drain_b_c.ds_ocap drain_b_c.ds_no]. rewrite tr_pos_nil. lia.
Qed.

(* the run: its summed positive growth with the start's g_capout is at most g_capout's final bound and the drains' *)
Lemma grg_run_pos : forall ps lv mx pre nm no cap j o,
  Forall grg_okp ps -> 0 <= cap ->
  tr_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) + cap <=
    Z.max cap (2 * (no + 2 * zsum (map grg_cost ps))) + zsum (map grg_pc ps).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx pre nm no cap j o HF Hcap.
  { cbn [relay_instance_gone_b_c.gone_run fst map fold_right]. rewrite tr_pos_nil. lia. }
  apply Forall_cons_iff in HF as [Hok HF].
  cbn [map fold_right].
  pose proof (grg_cost_nonneg (e, hj)) as Hc0.
  pose proof (zsum_map_nonneg grg_cost r grg_cost_nonneg) as Hr0.
  pose proof (zsum_map_nonneg grg_pc r grg_pc_nonneg) as Hp0.
  pose proof (grg_entry_no lv mx no cap e hj (proj1 Hok)) as HN.
  destruct (grg_entry_pos lv mx no cap e hj j (drain_b_c.drain_start nm o e (fst hj)) Hok Hcap) as (P1 & P2 & P3).
  pose proof (grg_run_cons lv mx no cap pre e hj r nm j o) as EC. cbv zeta in EC. rewrite EC. clear EC.
  rewrite !tr_pos_app.
  match goal with |- context [fst (gestures_end_b_c.keys_end_run ?lv' ?mx' (drain_b_c.ds_no ?S0) ?c1 ?X ?j1 ?o1)] =>
    assert (HXF : Forall (fun x => 0 <= fst x) X)
      by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
    assert (HX : fold_right (fun x acc => fst x + 5 + acc) 0 X <= rm3_kw (drain_b_c.ds_H S0))
      by apply grg_xks_le;
    pose proof (grg_fold_fst _ X) as EF;
    pose proof (grg_fold_nonneg _ X HXF) as F0;
    destruct (tp_ker lv' mx' X (drain_b_c.ds_no S0) c1 j1 o1 P2 HXF) as [K1 K2];
    pose proof (RelayCap.keys_end_run_cap_le lv' mx' X (drain_b_c.ds_no S0) c1 j1 o1 HXF) as K3
  end.
  match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n2 ?c2 pre r nm ?j2 ?o2] =>
    pose proof (IH lv mx pre nm n2 c2 j2 o2 HF ltac:(lia)) as IHr end.
  lia.
Qed.

Section gpeak.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma grg_pos_entry : forall m e, In e (lm_es m) -> (forall b, In b (model_blks m) -> 0 <= snd b) ->
  0 <= re_cap e /\ 0 <= drain_b_c.ent_ka e.
Proof.
  intros m e He Hpos.
  assert (HA : forall b, In b (aentry_blks e) -> 0 <= snd b).
  { intros b Hb. apply Hpos. unfold model_blks. right. apply in_or_app. left. apply in_concat.
    exists (aentry_blks e). split; [apply in_map; exact He | exact Hb]. }
  unfold drain_b_c.ent_ka. split.
  - destruct (Z.eqb_spec (re_cap e) 0) as [E|E]; [lia|].
    apply (HA (re_buf e, re_cap e)). unfold aentry_blks. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
  - destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; [lia|].
    apply (HA (re_hp e, re_kh e)). unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
Qed.

(* (R2), peak form: rig_spec's room at cause C3's measure (ReplyTrPeak.v tr_peak), at R1's PROPOSED premises and the
   model blocks' sizes not negative (fr_LS_rm_rr_pre_c3p's premise; amodel_at at GRG gives it as the remove arm's
   rr_blks_pos does), with 636848 bytes to spare *)
Lemma fr_LS3_gone_rig_c2p : forall cx t m ly S hs,
  fr_LS3 B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) + 636848
    <= LIVE_MAX.
Proof.
  intros cx t m ly S hs HLS HRI HP HO Ht HUs Hpos.
  pose proof (fr_LS3_gone_rig_c1 B cx t m ly S hs HLS HRI HP HO Ht HUs) as HM.
  pose proof (fr_LS3_room_x B cx t m ly S HLS) as Hroom.
  destruct (grg_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & H4).
  pose proof HP as (HLhs & _ & _).
  assert (HFp : Forall grg_okp (combine (lm_es m) hs)).
  { apply Forall_forall. intros p Hp. split; [exact (proj1 (Forall_forall _ _) HF p Hp)|].
    apply (grg_pos_entry m (fst p)); [|exact Hpos].
    destruct p as [e q]. cbn [fst]. exact (in_combine_l _ _ _ _ Hp). }
  assert (Hcap : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    apply (Hpos (lm_out m, lm_cap m)). unfold model_blks. right. apply in_or_app. right. apply in_or_app. right.
    unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity. }
  pose proof (grg_zsum_pc (combine (lm_es m) hs)) as HPC.
  rewrite length_combine, HLhs, Nat.min_id in HPC.
  pose proof (zsum_map_nonneg grg_cost (combine (lm_es m) hs) grg_cost_nonneg) as H0.
  revert HM. rewrite HO. cbn [length Z.of_nat]. intros HM.
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr in *. cbv zeta in *.
  match goal with |- context [tr_peak (fst (fst (fst (relay_instance_gone_b_c.gone_run
                                ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9))))] =>
    pose proof (grg_run_pos a6 a1 a2 a5 a7 a3 a4 a8 a9 HFp Hcap) as POS;
    pose proof (tr_peak_le_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))))
      as PK;
    set (T := fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) in *
  end.
  assert (HL : Z.of_nat (length (lm_es m)) <= 4) by lia.
  set (Zc := zsum (map grg_cost (combine (lm_es m) hs))) in *.
  set (Zp := zsum (map grg_pc (combine (lm_es m) hs))) in *.
  clearbody T Zc Zp.
  clear - Hroom HM POS PK HPC HL HC Hn H0 Hcap.
  assert (EM : WR_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  lia.
Qed.
Lemma fr_LS3c_gone_rig_c2p : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) + 636848
    <= LIVE_MAX.
Proof. intros cx t m ly S hs H. exact (fr_LS3_gone_rig_c2p cx t m ly S hs (proj1 H)). Qed.
End gpeak.

(* ================================================================== R2's probe *)
(* relay_instance_gone's trace (rig_tr itself, id 0) with one open source holding ReplyTrPeak.v's 300 new begin lines
   (keys "param_gesture kDDD", none with the instance prefix, so no gesture end): its requested sum is that drain's
   (pr_probe_300: 423948, of which the held array's regrowths 4 * 300 * 301 = 361200), its peak 42341.  The sum
   grows with N^2 (pr_probe_999: 4131438), the peak with N; at N = 65,536 the sum alone passes LIVE_MAX = 2^34. *)
Lemma grg_probe_300 :
  tr_alloc (rig_tr pr_c 0 0 0 0 [pr_e] [(pr_h 300, 0%nat)]) = 423948 /\
  tr_peak (rig_tr pr_c 0 0 0 0 [pr_e] [(pr_h 300, 0%nat)]) = 42341 /\
  tr_max (rig_tr pr_c 0 0 0 0 [pr_e] [(pr_h 300, 0%nat)]) = 12750.
Proof. split; [|split]; vm_compute; reflexivity. Qed.
