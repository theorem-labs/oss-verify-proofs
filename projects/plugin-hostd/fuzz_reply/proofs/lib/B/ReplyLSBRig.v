(* proves no function (kind: invariant lemma): the image-B HLSRIG premise of the entry walk of fuzz_reply's
   LLVMFuzzerTestOneInput, GN_LS_rig in C3's peak form with its four proposed premises (lib/B/ReplyLSBArms.v
   GN_LS_rig_p_T, whose meter conjunct is the LS instance's since KF-COUNT #6), at LS := ReplyLSB.fr_LS B CR,
   RINV := ReplyRINVB.fr_RINV, MMAX := fr_MMAX *)
(* THE PORT.  A's proof is B1cTopxLS's lib/A/ReplyLS3cTopxRig.v (a working branch 9f4cbd12a19, the file
   at 2db71055935): fr_LS3_gone_rig_c1 :402 (tr_max tr < MMAX), fr_LS3_gone_rig_c2p :610 (blocks_bytes S + tr_peak tr
   + 636848 <= LIVE_MAX) and fr_LS3_gone_rig_c3 :421 (mo_ok, True at ameter_triv), with that file's helpers grg_*
   (:106-397, :475-605).  Each helper here is A's renamed grg_ -> brig_, its proof A's but for the swaps below; the
   rules: c1 -> brig_rig_c1 (without A's unused fr_LS3 premise), c3 -> brig_rig_c3 (at any S and trace),
   c2p -> brig_rig_c2p (at fr_LS B CR with HCR, the conclusion without A's 636848 slack).  tr is
   rig_tr (lm_c m) (lm_mx m) |lm_O m| (lm_cap m) (gn_id cx m) (lm_es m) hs (lib/B/W_contract.v :1421, A's text): for
   each relay entry in table order, drain it when it is open, then end its held keys with the instance prefix.
   WHAT A's PROOF READS OF LS.  Only fr_LS3_room_x (lib/A/ReplyLS3.v :133, `blocks_bytes S + 4160659073 <= LIVE_MAX`),
   in c2p; c1 and c3 do not read LS at all (A :408, :425).  No other v3 conjunct (PHI3, E_ENT, W_OPEN) is read.  Here
   that room is lib/B/ReplyLSBArms.v bt_LS_room at fr_LS v2 (`blocks_bytes S + CR <= LIVE_MAX + LS_OVER`) with the
   rule's HCR : LS_OVER + R_rig <= CR, so no extra hypothesis is carried.
   THE ROOM R_rig.  c2p bounds tr_peak tr <= tr_pos tr + tr_max tr (tr_peak_le_pos) with tr_pos tr <= 4 c_n (g_capout
   from lm_cap to at most max lm_cap (2 g_nout), g_nout <= 2 * the pairs' cost <= 2 c_n) + per open entry
   42 P + 8 K + 80320 (brig_entry_pos, at most four entries) and tr_max tr <= fr_MMAX - 1 (c1), with c_n < 2 ^ 26 from
   fr_RINV: tr_peak tr <= 46 (2 ^ 26 - 1) + 4 * 80320 + (fr_MMAX - 1) = 4,160,022,225 = R_rig, which fits the B
   driver's room 2 ^ 33 (LS_OVER + R_rig = 8,589,231,184, 703,408 under it).
   THE FOUR PROPOSED PREMISES (GN_LS_rig_p_T over GN_LS_rig_T), each read by A's proof for the reason A's header gives
   (A :9-25, :45-48), unchanged at B (fr_RINV and fr_LS v2 read nothing more of them than A's fr_RINV and fr_LS3).
   GN_LS_rig_T, without them, is not provable from fr_LS B CR and fr_RINV:
     `lm_O m = []` (c1): fr_LS reads lm_O nowhere (model_blks: lm_G, lm_es, lm_hs, lm_cap, lm_out; kk: lm_k) and
       fr_RINV neither (ReplyRINVB.v :204-208), so g_nout = |lm_O m| is free (brig_O_free below) and a drain's send
       may ask 2 (g_nout + len) > fr_MMAX (brig_probe_O below); the gone arm holds it (gn_op, the cut's cleared O);
     `0 <= t < OPS_MAX` (c1): fr_RINV bounds the pending stream by WRITE_MAX * t and by c_n < 2 ^ 26 only; for
       t >= 513 a stream of 2 ^ 25 + 2 NULs makes reference_feed's list_push grow the expected array to 32 * 2 ^ 25 =
       2 ^ 30 > fr_MMAX (lib/A/ReplyLSDrainPre.v :18-20);
     `Forall (|re_U e| <= APARTIAL) (lm_es m)` (c1): fr_RINV says nothing of re_U at re_skip = 1, and fr_LS bounds
       re_cap only through PHI (about 2 ^ 33), so drain's first growth may ask 2 re_cap >= 2 ^ 30 (ReplyLSDrainPre.v
       :21-23); the arm has it from amodel_at's aentry_ok;
     `forall b, In b (model_blks m) -> 0 <= snd b` (c2p): the peak's accounting needs re_cap, the held-key array's
       size and lm_cap not negative (brig_pos_entry; a negative old size k makes a realloc's rise n - k exceed n).  fr_LS
       ties model_blks to ablocks by a Permutation, but ablocks' sizes are the chunks' ck_req (lib/Reusable/YG01.v
       :212-213), not negative only under the allocator's chunk_ok (YG01.v :387-388), which fr_LS does not carry; and
       a negative block can cancel a positive one in fr_LS's sums (brig_probe_cap below).  The arm has it from
       amodel_at (the remove arm's rr_blks_pos).
   A -> B SWAPS (A at a working branch 9f4cbd12a19):
     imports: A's list (A :53-96) with lib/A AB1v -> lib/B YB1v; Reusable YE01 + lib/A AE2k -> lib/B YE01 YE2k;
       lib/A ACfn -> lib/B YCfn (Required only); lib/A W_syms .. W_journal, W_rep W_contract W_sites W_frame,
       W_LLVMFuzzerTestOneInput_cut -> lib/B's files of the same names, then lib/B ReplyGuardB (Required);
       lib/A ReplyLS, ReplyRINV -> lib/B ReplyLSB, ReplyRINVB (+ ReplyLSBArms for tr_peak and the bt_ helpers);
       lib/A ReplyTrPeak -> lib/B ReplyLSBTrPeak; lib/A ReplyLSDrainPre, ReplyLSRemove3, ReplyLSRrPre -> lib/B
       ReplyLSBDrainPre (their B ports, with ReplyRINV.v's list facts); lib/A W_op_add, _drain, _write, _event,
       ReplyLSArms, ReplyLSDrain3, ReplyLS3, ReplyLS3c, ReplyLS3cTopxDefs -> not loaded (nothing here reads them; the
       Defs names are lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's); lib/A CfParamsReply (fr_MMAX) and lib/B YCfn_cf
       (CALL_ROOM_B) as ReplyLSBArms.v loads them;
     names: lfcx, lmod, model_blks, OPS_MAX, in_byte (lib/B/W_LLVMFuzzerTestOneInput_cut.v); rig_tr, rig_slots,
       tr_max, tr_cost (lib/B/W_contract.v :1419-1424, :946-966, A's text); gn_id, gn_pair_ok, gn_pairs
       (lib/B/W_LLVMFuzzerTestOneInput_gone_base.v, pinned by Local Notations); tr_peak (lib/B/ReplyLSBArms.v, a copy
       of A's); fr_RINV, fr_relay, fr_pair_ok, fr_entry_ok, fr_pair_cost, fr_cost
       (lib/B/ReplyRINVB.v, A's text); WR_MMAX -> fr_MMAX (lib/A/CfParamsReply.v, the same value 1072693248);
       zsum_map_nonneg -> bt_zsum_map_nonneg (ReplyLSBArms.v); gn_e0 / gn_hj0 -> their bodies relay_remove_b_c.no_entry
       / relay_instance_gone_b_c.no_hj; fr_LS3_room_x -> bt_LS_room with HCR.
     The model types rentry / hsrc / hlist and every program model this proof runs (drain_b_c, gestures_end_b_c,
       relay_instance_gone_b_c, RelayCap, SlotReads, SlotInv) are lib/Prog's, shared by both images. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBArms ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation MMAX := fr_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).
(* the gone arm's notions are lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's (:362, :429-439) *)
Local Notation gn_id := W_LLVMFuzzerTestOneInput_gone_base.gn_id.
Local Notation gn_pair_ok := W_LLVMFuzzerTestOneInput_gone_base.gn_pair_ok.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.

(* ================================================================== each pair's facts and cost (A :106-129) *)
(* the input cost the run reads off one (entry, source) pair: the gesture ends of its keys and, when the entry is open,
   the pending bytes and the kept line (fr_pair_cost's terms; the source's terms only when drain reads it) *)
Definition brig_cost (p : rentry * (hsrc * nat)) : Z :=
  gestures_end_b_c.keys_total (re_keys (fst p)) +
  (if re_eof (fst p) =? 0 then
     Z.of_nat (length (pending_stream (fst (snd p)))) +
     (if re_skip (fst p) =? 0 then Z.of_nat (length (re_U (fst p))) else 0)
   else 0).
(* what drain's request bound reads of an open pair (ReplyLSDrainPre.v dpre_drain_run's invariant) *)
Definition brig_ok (p : rentry * (hsrc * nat)) : Prop :=
  (re_skip (fst p) = 0 \/ re_skip (fst p) = 1) /\
  (re_eof (fst p) = 0 ->
     Z.of_nat (length (re_U (fst p))) <= APARTIAL /\
     (hs_overlong (fst (snd p)) = 1 \/ bzs (re_U (fst p)) = bzs (hs_W (fst (snd p)))) /\
     0 <= hs_off (fst (snd p)) /\ hl_recs (hs_expected (fst (snd p))) = [] /\
     Z.of_nat (length (pending_stream (fst (snd p)))) <= 65535 * 511 /\
     0 <= hl_cap (hs_expected (fst (snd p)))).

Lemma brig_cost_nonneg : forall p, 0 <= brig_cost p.
Proof.
  intros p. unfold brig_cost. pose proof (fr_keys_total_nonneg (re_keys (fst p))).
  destruct (re_eof (fst p) =? 0); [destruct (re_skip (fst p) =? 0)|]; lia.
Qed.

(* ================================================================== the keys gestures_end_instance ends (A :131-187) *)
Lemma brig_geia_loop_perm : forall fuel pre n H,
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

Lemma brig_combine_kw : forall (A : Type) (H : list (list Z)) (ks : list A),
  zsum (map (fun x => Z.of_nat (length (fst x)) + 5) (combine H ks)) <= rm3_kw H.
Proof.
  intros A H. unfold rm3_kw. induction H as [|x H IH]; intros [|k ks]; cbn [combine map fold_right fst]; try lia.
  - pose proof (bt_zsum_map_nonneg (fun y : list Z => Z.of_nat (length y) + 5) H ltac:(intros; cbv beta; lia)). lia.
  - specialize (IH ks). lia.
Qed.

(* the ended keys' bytes with their 5 end bytes are at most the held keys' (geia keeps the rest) *)
Lemma brig_xks_le : forall pre (H : list (list Z)) (ks : list (RelayRunT.addr YO0i.sptr)),
  fold_right (fun x acc => fst x + 5 + acc) 0
    (map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (relay_instance_gone_b_c.geia pre (combine H ks))))
  <= rm3_kw H.
Proof.
  intros pre H ks.
  pose proof (brig_geia_loop_perm (length (combine H ks)) pre 0 (combine H ks)) as HP.
  pose proof (fr_sum_perm _ (fun x : list Z * RelayRunT.addr YO0i.sptr => Z.of_nat (length (fst x)) + 5) _ _ HP)
    as ES.
  rewrite map_app, zsum_app in ES.
  pose proof (bt_zsum_map_nonneg (fun x : list Z * RelayRunT.addr YO0i.sptr => Z.of_nat (length (fst x)) + 5)
                (snd (relay_instance_gone_b_c.geia_loop (length (combine H ks)) pre 0 (combine H ks)))
                ltac:(intros; cbv beta; lia)) as N.
  pose proof (brig_combine_kw _ H ks) as C.
  assert (E1 : forall E : list (list Z * RelayRunT.addr YO0i.sptr),
    fold_right (fun x acc => fst x + 5 + acc) 0 (map (fun x => (Z.of_nat (length (fst x)), snd x)) E) =
    zsum (map (fun x => Z.of_nat (length (fst x)) + 5) E)).
  { induction E as [|y E IHE]; cbn [map fold_right fst]; lia. }
  rewrite E1. unfold relay_instance_gone_b_c.geia. lia.
Qed.

Lemma brig_fold_fst : forall (A : Type) (l : list (Z * A)),
  fold_right (fun xl acc => xl + 5 + acc) 0 (map fst l) = fold_right (fun x acc => fst x + 5 + acc) 0 l.
Proof. intros A l. induction l as [|x l IH]; cbn [map fold_right]; lia. Qed.

Lemma brig_fold_nonneg : forall (A : Type) (l : list (Z * A)), Forall (fun x => 0 <= fst x) l ->
  0 <= fold_right (fun x acc => fst x + 5 + acc) 0 l.
Proof. intros A l H. induction H as [|x l Hx _ IH]; cbn [fold_right]; lia. Qed.

(* ================================================================== one step of relay_instance_gone's run (A :189-208) *)
Lemma brig_run_cons : forall lv mx no cap pre e (hj : hsrc * nat) r nm j o,
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

(* ================================================================== one entry (A :210-274) *)
(* drain's g_nout and the keys it leaves, from g_nout = no: at most no + 2 * the pair's cost *)
Lemma brig_entry_no : forall lv mx no cap (e : rentry) (hj : hsrc * nat),
  brig_ok (e, hj) ->
  drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) +
    rm3_kw (drain_b_c.ds_H (relay_remove_b_c.after_drain lv mx no cap e (fst hj))) <= no + 2 * brig_cost (e, hj).
Proof.
  intros lv mx no cap e hj (Hsk & Hop).
  unfold brig_cost. cbn [fst snd] in Hsk, Hop |- *.
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
Lemma brig_entry_tr : forall lv mx no cap (e : rentry) (hj : hsrc * nat) j (a0 : drain_b_c.dadr) M K,
  brig_ok (e, hj) -> brig_cost (e, hj) <= K ->
  2 * (no + 2 * brig_cost (e, hj) + 6000) <= M -> 8 * (K + 6000) <= M -> 1071628288 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else []).
Proof.
  intros lv mx no cap e hj j a0 M K (Hsk & Hop) HK HM H8 H32 Hg.
  unfold brig_cost in HK, HM. cbn [fst snd] in Hsk, Hop, HK, HM.
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

(* ================================================================== the run's requests (A :276-303) *)
Lemma brig_run_rq : forall ps lv mx pre nm no cap j o M K,
  Forall brig_ok ps -> zsum (map brig_cost ps) <= K ->
  2 * (no + 2 * zsum (map brig_cost ps) + 6000) <= M -> 8 * (K + 6000) <= M -> 1071628288 <= M -> 20192 <= M ->
  Forall (dpre_rq M) (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx pre nm no cap j o M K HF HK HM H8 H32 Hg.
  { cbn [relay_instance_gone_b_c.gone_run fst]. constructor. }
  apply Forall_cons_iff in HF as [Hok HF].
  cbn [map fold_right] in HK, HM.
  pose proof (brig_cost_nonneg (e, hj)) as Hc0.
  pose proof (bt_zsum_map_nonneg brig_cost r brig_cost_nonneg) as Hr0.
  pose proof (brig_entry_no lv mx no cap e hj Hok) as HN.
  pose proof (brig_run_cons lv mx no cap pre e hj r nm j o) as EC. cbv zeta in EC. rewrite EC. clear EC.
  apply Forall_app. split.
  { apply (brig_entry_tr _ _ _ _ _ _ _ _ M K Hok); lia. }
  match goal with |- Forall _ (fst (gestures_end_b_c.keys_end_run ?lv' ?mx' (drain_b_c.ds_no ?S0) ?c1 ?X ?j1 ?o1)
                               ++ _) =>
    assert (HXF : Forall (fun x => 0 <= fst x) X)
      by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
    assert (HX : fold_right (fun x acc => fst x + 5 + acc) 0 X <= rm3_kw (drain_b_c.ds_H S0))
      by apply brig_xks_le;
    pose proof (brig_fold_fst _ X) as EF
  end.
  apply Forall_app. split.
  { apply rrp_ker; [exact HXF | lia]. }
  apply (IH lv mx pre nm _ _ _ _ M K HF); lia.
Qed.

(* ================================================================== the pairs, from fr_RINV (A :305-397) *)
Lemma brig_zsum_le : forall (X Y : Type) (f : X -> Z) (g : Y -> Z) (l1 : list X) (l2 : list Y) dx dy,
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

(* an open entry's pair in gn_pairs is the entry's row of fr_relay (one source per fd among the open slots) *)
Lemma brig_pair_pt : forall cx t m e p q,
  fr_RINV cx t m -> 0 <= t < OPS_MAX -> fr_pair_ok m t e q -> fr_entry_ok e ->
  Z.of_nat (length (re_U e)) <= APARTIAL -> (re_eof e = 0 -> gn_pair_ok m e p) ->
  brig_ok (e, p) /\ brig_cost (e, p) <= fr_pair_cost e q.
Proof.
  intros cx t m e p q HRI Ht Hq Hent HUe Hp.
  destruct Hq as (Hq4 & Hqn & Hqf & Hre & _ & _ & Hexp & Hec & _ & Hpe & Hoff).
  destruct Hent as (_ & _ & _ & _ & Hsk).
  pose proof (fr_keys_total_nonneg (re_keys e)) as HKT.
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec'.
  assert (HX : 0 <= (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0))
    by (destruct (re_skip e =? 0); lia).
  unfold brig_ok, brig_cost, fr_pair_cost. cbn [fst snd].
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

(* the run's pairs: each brig_ok, their cost within the input (fr_relay's fr_cost <= c_n), at most four entries *)
Lemma brig_pairs : forall cx t m hs,
  fr_RINV cx t m -> gn_pairs m hs -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  Forall brig_ok (combine (lm_es m) hs) /\ zsum (map brig_cost (combine (lm_es m) hs)) <= c_n cx /\
  c_n cx < 2 ^ 26 /\ (length (lm_es m) <= 4)%nat.
Proof.
  intros cx t m hs HRI HP Ht HUs.
  pose proof HRI as (_ & HR & Hn & _).
  destruct HR as (Hlen & Hnd & _ & Hent & hj & HF & HNDs & _ & _ & Hcn).
  destruct HP as (HLhs & HFa & _).
  pose proof (Forall2_length HF) as Lhj.
  set (e0 := relay_remove_b_c.no_entry). set (hj0 := relay_instance_gone_b_c.no_hj).
  assert (HI : forall i, (i < length (lm_es m))%nat ->
    brig_ok (nth i (lm_es m) e0, nth i hs hj0) /\
    brig_cost (nth i (lm_es m) e0, nth i hs hj0) <= fr_pair_cost (nth i (lm_es m) e0) (nth i hj hj0)).
  { intros i Hi.
    assert (He : In (nth i (lm_es m) e0) (lm_es m)) by (apply nth_In; exact Hi).
    apply (brig_pair_pt cx t m _ _ _ HRI Ht (fr_F2_nth _ _ _ _ _ HF i e0 hj0 Hi)).
    - rewrite Forall_forall in Hent. exact (Hent _ He).
    - rewrite Forall_forall in HUs. exact (HUs _ He).
    - intros Eo.
      assert (Hin : In (nth i (lm_es m) e0, nth i hs hj0) (combine (lm_es m) hs)).
      { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
      exact (proj1 (Forall_forall _ _) HFa _ Hin Eo). }
  split; [|split; [|split]].
  - apply Forall_forall. intros x Hx.
    apply (In_nth _ _ (e0, hj0)) in Hx as (i & Hi & <-).
    rewrite length_combine in Hi.
    rewrite combine_nth by lia. apply (HI i). lia.
  - eapply Z.le_trans; [|exact Hcn]. unfold fr_cost.
    apply (brig_zsum_le _ _ brig_cost (fun q => fr_pair_cost (fst q) (snd q)) (combine (lm_es m) hs)
             (combine (lm_es m) hj) (e0, hj0) (e0, hj0)).
    + rewrite !length_combine. lia.
    + intros i Hi. rewrite length_combine in Hi. rewrite !combine_nth by lia. cbn [fst snd]. apply HI. lia.
  - exact Hn.
  - assert (H4 : forall x, In x (map snd hj) -> In x (seq 0 4)).
    { intros x Hx. apply in_map_iff in Hx as (q & <- & Hq).
      apply (In_nth _ _ hj0) in Hq as (i & Hi & <-).
      destruct (fr_F2_nth _ _ _ _ _ HF i e0 hj0 ltac:(lia)) as (Hs4 & _).
      apply in_seq. lia. }
    pose proof (List.NoDup_incl_length (proj1 (NoDup_ListNoDup _) HNDs) H4) as HL.
    rewrite length_map, length_seq in HL. lia.
Qed.

(* ================================================================== (R1), (R3) (A :399-425) *)
(* GN_LS_rig's first conjunct at the proposed premises; no LS fact is read *)
Lemma brig_rig_c1 : forall cx t m hs,
  fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  tr_max (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs) < MMAX.
Proof.
  intros cx t m hs HRI HP HO Ht HUs.
  destruct (brig_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & _).
  rewrite HO. cbn [length Z.of_nat].
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr. cbv zeta.
  pose proof fr_MMAX_val as EM.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  pose proof (bt_zsum_map_nonneg brig_cost (combine (lm_es m) hs) brig_cost_nonneg) as H0.
  apply (Z.le_lt_trans _ (fr_MMAX - 1)); [|lia].
  apply dpre_tr_max; [lia|].
  apply (brig_run_rq _ _ _ _ _ 0 _ _ _ (fr_MMAX - 1) (c_n cx) HF HC); lia.
Qed.

(* GN_LS_rig's old third conjunct (meter-only): True at ameter_triv, for B's v2 top (ReplyBTop.v) *)
Lemma brig_rig_c3 : forall (S : astate) (tr : list (RelayRunT.rev YO0i.sptr)),
  mo_ok ameter_triv S (tr_cost ameter_triv tr).
Proof. intros. exact I. Qed.
End grig.

(* ================================================================== the peak form of R2 (A :475-585) *)
(* the per-entry facts the summed positive growth reads: the entry's buffer and held-array sizes not negative *)
Definition brig_okp (p : rentry * (hsrc * nat)) : Prop :=
  brig_ok p /\ 0 <= re_cap (fst p) /\ 0 <= drain_b_c.ent_ka (fst p).
(* an open entry's drain: at most 42 per pending byte, 8 per held key and 80320 beyond its g_capout growth *)
Definition brig_pc (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then
    42 * Z.of_nat (length (pending_stream (fst (snd p)))) + 8 * Z.of_nat (length (re_keys (fst p))) + 80320
  else 0.

Lemma brig_pc_nonneg : forall p, 0 <= brig_pc p.
Proof. intros p. unfold brig_pc. destruct (re_eof (fst p) =? 0); lia. Qed.
Lemma brig_pc_le : forall p, brig_pc p <= 42 * brig_cost p + 80320.
Proof.
  intros p. unfold brig_pc, brig_cost. pose proof (fr_keys_total_nonneg (re_keys (fst p))).
  pose proof (dpre_keys_le (re_keys (fst p))).
  destruct (re_eof (fst p) =? 0); [destruct (re_skip (fst p) =? 0)|]; lia.
Qed.
Lemma brig_zsum_pc : forall l, zsum (map brig_pc l) <= 42 * zsum (map brig_cost l) + 80320 * Z.of_nat (length l).
Proof. induction l as [|p l IH]; cbn [map fold_right length]; [lia|]. pose proof (brig_pc_le p). lia. Qed.

(* one entry: its drain's summed positive growth (tp_drain_run's accounting at any g_nout) and its g_capout *)
Lemma brig_entry_pos : forall lv mx no cap (e : rentry) (hj : hsrc * nat) j (a0 : drain_b_c.dadr),
  brig_okp (e, hj) -> 0 <= cap ->
  tr_pos (if re_eof e =? 0 then drain_b_c.drain_tr lv mx no cap e (fst hj) j a0 else []) + cap <=
    drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) + brig_pc (e, hj) /\
  0 <= drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) /\
  drain_b_c.ds_ocap (relay_remove_b_c.after_drain lv mx no cap e (fst hj)) <=
    Z.max cap (2 * drain_b_c.ds_no (relay_remove_b_c.after_drain lv mx no cap e (fst hj))).
Proof.
  intros lv mx no cap e hj j a0 ((Hsk & Hop) & Hrc & Hka) Hcap.
  unfold brig_pc. cbn [fst snd] in Hsk, Hop, Hrc, Hka |- *.
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
    { unfold SlotReads.wcost, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
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
Lemma brig_run_pos : forall ps lv mx pre nm no cap j o,
  Forall brig_okp ps -> 0 <= cap ->
  tr_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) + cap <=
    Z.max cap (2 * (no + 2 * zsum (map brig_cost ps))) + zsum (map brig_pc ps).
Proof.
  induction ps as [|[e hj] r IH]; intros lv mx pre nm no cap j o HF Hcap.
  { cbn [relay_instance_gone_b_c.gone_run fst map fold_right]. rewrite tr_pos_nil. lia. }
  apply Forall_cons_iff in HF as [Hok HF].
  cbn [map fold_right].
  pose proof (brig_cost_nonneg (e, hj)) as Hc0.
  pose proof (bt_zsum_map_nonneg brig_cost r brig_cost_nonneg) as Hr0.
  pose proof (bt_zsum_map_nonneg brig_pc r brig_pc_nonneg) as Hp0.
  pose proof (brig_entry_no lv mx no cap e hj (proj1 Hok)) as HN.
  destruct (brig_entry_pos lv mx no cap e hj j (drain_b_c.drain_start nm o e (fst hj)) Hok Hcap) as (P1 & P2 & P3).
  pose proof (brig_run_cons lv mx no cap pre e hj r nm j o) as EC. cbv zeta in EC. rewrite EC. clear EC.
  rewrite !tr_pos_app.
  match goal with |- context [fst (gestures_end_b_c.keys_end_run ?lv' ?mx' (drain_b_c.ds_no ?S0) ?c1 ?X ?j1 ?o1)] =>
    assert (HXF : Forall (fun x => 0 <= fst x) X)
      by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
    assert (HX : fold_right (fun x acc => fst x + 5 + acc) 0 X <= rm3_kw (drain_b_c.ds_H S0))
      by apply brig_xks_le;
    pose proof (brig_fold_fst _ X) as EF;
    pose proof (brig_fold_nonneg _ X HXF) as F0;
    destruct (tp_ker lv' mx' X (drain_b_c.ds_no S0) c1 j1 o1 P2 HXF) as [K1 K2];
    pose proof (RelayCap.keys_end_run_cap_le lv' mx' X (drain_b_c.ds_no S0) c1 j1 o1 HXF) as K3
  end.
  match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n2 ?c2 pre r nm ?j2 ?o2] =>
    pose proof (IH lv mx pre nm n2 c2 j2 o2 HF ltac:(lia)) as IHr end.
  lia.
Qed.

(* ================================================================== the room (A :587-652, at fr_LS v2) *)
(* the room the peak needs above the live bytes: 46 per input byte (c_n <= 2 ^ 26 - 1), 80320 per entry (at most
   four), and the largest request (fr_MMAX - 1) *)
Definition R_rig : Z := 4160022225.
Lemma R_rig_val : R_rig = 46 * (2 ^ 26 - 1) + 4 * 80320 + (fr_MMAX - 1).
Proof. reflexivity. Qed.

Section gpeak.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma brig_pos_entry : forall m e, In e (lm_es m) -> (forall b, In b (model_blks m) -> 0 <= snd b) ->
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

(* (R2), peak form: rig_spec's room at C3's measure, at the proposed premises, from fr_LS v2's room *)
Lemma brig_rig_c2p : forall CR, LS_OVER + R_rig <= CR -> forall cx t m ly S hs,
  fr_LS B CR cx t m ly S -> fr_RINV cx t m -> gn_pairs m hs ->
  lm_O m = [] -> 0 <= t < OPS_MAX ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  blocks_bytes S +
    tr_peak (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)
    <= LIVE_MAX.
Proof.
  intros CR HCR cx t m ly S hs HLS HRI HP HO Ht HUs Hpos.
  pose proof (brig_rig_c1 cx t m hs HRI HP HO Ht HUs) as HM.
  pose proof (bt_LS_room B CR cx t m ly S HLS) as Hroom.
  destruct (brig_pairs cx t m hs HRI HP Ht HUs) as (HF & HC & Hn & H4).
  pose proof HP as (HLhs & _ & _).
  assert (HFp : Forall brig_okp (combine (lm_es m) hs)).
  { apply Forall_forall. intros p Hp. split; [exact (proj1 (Forall_forall _ _) HF p Hp)|].
    apply (brig_pos_entry m (fst p)); [|exact Hpos].
    destruct p as [e q]. cbn [fst]. exact (in_combine_l _ _ _ _ Hp). }
  assert (Hcap : 0 <= lm_cap m).
  { destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
    apply (Hpos (lm_out m, lm_cap m)). unfold model_blks. right. apply in_or_app. right. apply in_or_app. right.
    unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity. }
  pose proof (brig_zsum_pc (combine (lm_es m) hs)) as HPC.
  rewrite length_combine, HLhs, Nat.min_id in HPC.
  pose proof (bt_zsum_map_nonneg brig_cost (combine (lm_es m) hs) brig_cost_nonneg) as H0.
  revert HM. rewrite HO. cbn [length Z.of_nat]. intros HM.
  unfold rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr in *. cbv zeta in *.
  match goal with |- context [tr_peak (fst (fst (fst (relay_instance_gone_b_c.gone_run
                                ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9))))] =>
    pose proof (brig_run_pos a6 a1 a2 a5 a7 a3 a4 a8 a9 HFp Hcap) as POS;
    pose proof (tr_peak_le_pos (fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))))
      as PK;
    set (T := fst (fst (fst (relay_instance_gone_b_c.gone_run a1 a2 a3 a4 a5 a6 a7 a8 a9)))) in *
  end.
  assert (HL : Z.of_nat (length (lm_es m)) <= 4) by lia.
  set (Zc := zsum (map brig_cost (combine (lm_es m) hs))) in *.
  set (Zp := zsum (map brig_pc (combine (lm_es m) hs))) in *.
  clearbody T Zc Zp.
  clear - HCR Hroom HM POS PK HPC HL HC Hn H0 Hcap.
  pose proof fr_MMAX_val as EM. pose proof LS_OVER_val as EO.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold R_rig in HCR. lia.
Qed.

(* ================================================================== GN_LS_rig, C3 peak form, proposed premises *)
Lemma brig_gone_rig : forall CR, LS_OVER + R_rig <= CR ->
  GN_LS_rig_p_T fr_MMAX (fr_LS B CR) fr_RINV.
Proof.
  intros CR HCR cx t m ly S hs HLS HRI HP HO Ht HUs Hpos. cbv zeta.
  split; [exact (brig_rig_c1 cx t m hs HRI HP HO Ht HUs)|].
  exact (brig_rig_c2p CR HCR cx t m ly S hs HLS HRI HP HO Ht HUs Hpos).
Qed.
End gpeak.

(* ================================================================== the instance at the B driver's room *)
Lemma R_rig_fits : LS_OVER + R_rig <= YCfn_cf.CALL_ROOM_B.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma GN_LS_rig_B : GN_LS_rig_p_T fr_MMAX (fr_LS B YCfn_cf.CALL_ROOM_B) fr_RINV.
Proof. exact (brig_gone_rig B _ R_rig_fits). Qed.
End inst.

(* ================================================================== why GN_LS_rig_T needs the proposed premises *)
(* Two of the four, measured on rig_tr itself (one open entry of fd 100 whose source has one pending line "a"; the
   controller connected).  (1) `lm_O m = []`: fr_LS, fr_RINV, gn_pairs and gn_id read no lm_O (brig_O_free), so a
   state that meets them with any g_nout meets them with every other, and at g_nout = g_capout = 2 ^ 29 the line's
   send asks 2 ^ 30 + 4 > fr_MMAX (brig_probe_O).  (2) the model blocks' sizes not negative: an entry buffer of
   2 ^ 40 bytes with g_capout = - 2 ^ 40 adds 0 to bsum (model_blks m), so fr_LS's sums cannot tell it from an empty
   model, yet the send's regrowth from the negative size rises 2 ^ 40 > LIVE_MAX above the start (brig_probe_cap).
   The other two (t < OPS_MAX, |re_U| <= APARTIAL) need streams of 2 ^ 25 and 2 ^ 29 bytes; the header gives why. *)
Section why.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition brig_setO (m : lmod) (O : list byte) : lmod :=
  LM (lm_k m) (lm_hs m) (lm_G m) (lm_es m) (lm_c m) O (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
Lemma brig_O_free : forall CR cx t m ly S hs O,
  (fr_LS B CR cx t m ly S -> fr_LS B CR cx t (brig_setO m O) ly S) /\
  (fr_RINV cx t m -> fr_RINV cx t (brig_setO m O)) /\
  (gn_pairs m hs -> gn_pairs (brig_setO m O) hs) /\ gn_id cx (brig_setO m O) = gn_id cx m.
Proof. intros. split; [|split; [|split]]; [intros H; exact H .. | reflexivity]. Qed.
End why.

Definition brig_ph : hsrc :=
  HS 100 1 0 0 (HL 4096 8 [(8192, map (Z_to_bv 8) [97; 0])] []) 0 12288 [] 0 0 [] (HL 0 0 [] []) (HL 0 0 [] []).
Definition brig_pe (cap : Z) : rentry := RE 100 0 0 [] 4096 0 cap 0 0 [] [] [] [].
Definition brig_pctl : ctl := CTL 3 0 0 0 0.
Lemma brig_probe_O :
  fr_MMAX < tr_max (rig_tr brig_pctl 0 (2 ^ 29) (2 ^ 29) 0 [brig_pe 0] [(brig_ph, 0%nat)]).
Proof. apply Z.ltb_lt. vm_compute. reflexivity. Qed.
Lemma brig_probe_cap :
  bsum (concat (map aentry_blks [brig_pe (2 ^ 40)]) ++ aout_blks (- 2 ^ 40) 0) = 0 /\
  LIVE_MAX < tr_peak (rig_tr brig_pctl 0 0 (- 2 ^ 40) 0 [brig_pe (2 ^ 40)] [(brig_ph, 0%nat)]).
Proof. split; [vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity]. Qed.
