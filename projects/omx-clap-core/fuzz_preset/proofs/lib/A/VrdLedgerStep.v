(* fuzz_preset, slice S5b, the Ival walk's lane (a Theorem Labs lane): THE LEDGER STEP across a call of parse_items' loop (shared:
   the Ival walk's parse_value call, the S3 walk's parse_string call and REFUSE-B fuzz_free cite it; written once, a Theorem Labs lane's
   ruling on shared lemmas). Pure composition lemmas over PRH_FnParse.v's rd_ledger_move / rd_blocks_move / rd_room:
   - vl_ledger_move_app: a granted prefix's rd_ledger_move (ok = repeat true (calls tr1)) composed with the next call's
     move at any ok2 (the lszR-append fact for the second trace is the caller's: it depends on the callee's grammar);
   - vl_blocks_move_app: rd_blocks_move composed with a call's new blocks;
   - vl_room_tail: rd_room for the continuation after a granted prefix;
   - vl_agrees_some / vl_oks_granted: a granted run's oracle prefix (the run's ok list may be SHORTER than its calls,
     nth's default being true, so ok = repeat true .. ++ okr is false in general);
   - vl_lsum_app / vl_lsum_perm / vl_hpeak_bound / vl_hpeak_le_pos / vl_nlive_app and the repeat-true helpers.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). No walk, no machine state.
   Proofs from two sub-lanes, Qed in uncommitted files, gathered here unchanged but for the vl_
   prefix. SET: a working branch on a working branch da5334ad793; texts a working branch
   49745a1a153 (PRH_FnParse.v blob e21b8b02d69e), texts on walkkit-next 0afb3f76c28. A-only. No numeral is an
   address.
   A'LEDGER (a Theorem Labs lane, 2026-10-29), against the kit text PRH_FnParse.v blob 94232293d483 / PRH_Base.v blob
   ee2f5cd7ed35 (a working branch 3ac20a5c9e30): rd_ledger_move takes g_most (most) and the call's
   ALL-GRANTED trace gt, keys g_ran_out on prh_oks's per-call requests (prh_ev_reqs tr) against most, and adds the
   refusal peak prh_refused_peak over prh_ev_helds gt. vl_ledger_move_app composes a granted prefix tr1 (any gt1:
   with no refusal the refusal peak is 0) with the next call's move at its gt2 into the move at gt = tr1 ++ gt2;
   vl_oks_granted takes prh_oks's ns and most. The six pure trace helpers this file took from VrdIStep.v are proved
   here (Local), so the file no longer Requires VrdFrame / VrdIElem / VrdIStep and builds before them. *)
(* The kit's CUT (lane RBase, a working branch 7cdbb61b5fa0, PRH_FnParse.v blob f0d92dcec7e9, PRH_Base.v blob
   ef7c8ca98529): rd_room's live conjunct is PER EVENT, PRH_Base.prh_live_evs S (rd_hevs gt) (FnParse:251; LIVE_rd is
   retired, a Theorem Labs lane's entry-sum ruling). vl_room_tail's statement moves for that reason only: the live room of the
   continuation is the tail of the per-event list from the state after the prefix, so its premises are the prefix's
   LIVE-REQUEST MOVE (the reader posts' hlive_from conjunct) and room_live_cf, in place of the blocks_bytes bound and
   the held sign the entry-sum form used. New: the per-event toolkit vl_zsum_perm / vl_live_at_prefix /
   vl_live_evs_prefix (a callee's own room is a prefix of the caller's events) / vl_live_evs_tail. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80xf YGcallMx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

(* ---- THE PURE TRACE HELPERS, ONE HOME (A'Ledger, to cut this file's Require of VrdIStep, a Theorem Labs lane's approval
   2026-10-29): these were VrdIStep.v's vi_hpeak_nonneg / vi_hpeak_app / vi_maxreq_nonneg / vi_maxreq_app /
   vi_lsum_app / vi_lsum_perm (and vi_calls_app, which is PjGrammar.calls_app). The proofs live HERE now; VrdIStep.v,
   which Requires this file, keeps its vi_ names as one-line forwarders to these, so no proof is duplicated ---- *)
Lemma vl_hpeak_nonneg : forall t, 0 <= hpeakR t.
Proof. induction t as [|e t IH]; cbn [hpeakR]; lia. Qed.

Lemma vl_hpeak_app : forall a b, hpeakR (a ++ b) = Z.max (hpeakR a) (PjGrammar.held a + hpeakR b).
Proof.
  induction a as [|e a IH]; intros b; cbn [app hpeakR PjGrammar.held].
  - pose proof (vl_hpeak_nonneg b). lia.
  - rewrite IH. lia.
Qed.

Lemma vl_maxreq_nonneg : forall t, 0 <= prh_maxreq t.
Proof. unfold prh_maxreq. induction t as [|e t IH]; cbn [map fold_right]; lia. Qed.

Lemma vl_maxreq_app : forall a b, prh_maxreq (a ++ b) = Z.max (prh_maxreq a) (prh_maxreq b).
Proof.
  unfold prh_maxreq. induction a as [|e a IH]; intros b; cbn [app map fold_right].
  - pose proof (vl_maxreq_nonneg b) as Hb. unfold prh_maxreq in Hb. lia.
  - rewrite IH. lia.
Qed.

Lemma vl_lsum_app : forall a b, Ledger.lsum (a ++ b) = Ledger.lsum a + Ledger.lsum b.
Proof. induction a as [|[x k] a IH]; intros b; cbn [app Ledger.lsum]; [reflexivity | rewrite IH; lia]. Qed.

Lemma vl_lsum_perm : forall a b, Permutation a b -> Ledger.lsum a = Ledger.lsum b.
Proof.
  intros a b H. induction H as [|[x k] a b _ IH|[x k] [y j] a|a b c _ IH1 _ IH2];
    cbn [Ledger.lsum]; [reflexivity | rewrite IH; reflexivity | lia | rewrite IH1; exact IH2].
Qed.

(* hpeakR is the largest prefix sum (and 0) *)
Lemma vl_hpeak_bound : forall t Bd, 0 <= Bd ->
  (forall p r, t = p ++ r -> PjGrammar.held p <= Bd) -> hpeakR t <= Bd.
Proof.
  induction t as [|e t IH]; intros Bd HB HP; cbn [hpeakR]; [lia|].
  assert (H1 : PjGrammar.held_ev e <= Bd).
  { specialize (HP [e] t eq_refl). cbn [PjGrammar.held] in HP. lia. }
  assert (H2 : hpeakR t <= Bd - PjGrammar.held_ev e).
  { apply IH; [lia|]. intros p r Ht. specialize (HP (e :: p) r).
    rewrite Ht in HP. specialize (HP eq_refl). cbn [PjGrammar.held] in HP. lia. }
  lia.
Qed.

Lemma vl_nlive_app : forall a b, nliveR (a ++ b) = nliveR a + nliveR b.
Proof. induction a as [|e a IH]; intros b; cbn [app nliveR]; [lia | rewrite IH; lia]. Qed.

Lemma vl_nth_repeat_true : forall n i, nth i (repeat true n) true = true.
Proof. induction n as [|n IH]; intros [|i]; cbn; auto. Qed.

Lemma vl_nth_rep_app1 : forall k (ok : list bool) i, (i < k)%nat -> nth i (repeat true k ++ ok) true = true.
Proof. intros k ok i Hi. rewrite app_nth1 by (rewrite repeat_length; lia). apply vl_nth_repeat_true. Qed.

Lemma vl_nth_rep_app2 : forall k (ok : list bool) i, (k <= i)%nat ->
  nth i (repeat true k ++ ok) true = nth (i - k) ok true.
Proof. intros k ok i Hi. rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length. reflexivity. Qed.

(* ---- the per-call lists of a trace (PRH_Base.v prh_ev_reqs / prh_ev_helds) and the refusal peak prh_refused_peak,
   split along a granted prefix of k1 calls (A'Ledger) ---- *)
(* prh_ev_reqs filters with stdpp's base.filter (decide over Is_true): one cons step, by computation per event *)
Lemma vl_ev_reqs_cons : forall e t,
  prh_ev_reqs (e :: t) = (if PjGrammar.is_call e then [PjReqBound.ev_req e] else []) ++ prh_ev_reqs t.
Proof. intros e t. destruct e; reflexivity. Qed.

Lemma vl_ev_reqs_app : forall a b, prh_ev_reqs (a ++ b) = prh_ev_reqs a ++ prh_ev_reqs b.
Proof.
  induction a as [|e a IH]; intros b; [reflexivity|].
  cbn [app]. rewrite !vl_ev_reqs_cons, IH, app_assoc. reflexivity.
Qed.

Lemma vl_ev_reqs_length : forall t, length (prh_ev_reqs t) = PjGrammar.calls t.
Proof.
  induction t as [|e t IH]; [reflexivity|].
  rewrite vl_ev_reqs_cons, length_app, IH. cbn [PjGrammar.calls]. destruct (PjGrammar.is_call e); reflexivity.
Qed.

Lemma vl_ev_helds_length : forall t, length (prh_ev_helds t) = PjGrammar.calls t.
Proof.
  induction t as [|e t IH]; cbn [prh_ev_helds PjGrammar.calls]; [reflexivity|].
  rewrite length_app, length_map, IH. destruct (PjGrammar.is_call e); reflexivity.
Qed.

Lemma vl_ev_helds_app : forall a b,
  prh_ev_helds (a ++ b) = prh_ev_helds a ++ map (Z.add (PjGrammar.held a)) (prh_ev_helds b).
Proof.
  induction a as [|e a IH]; intros b; cbn [app prh_ev_helds PjGrammar.held].
  - rewrite (map_ext (Z.add 0) (fun x => x)) by (intros x; lia). rewrite map_id. reflexivity.
  - rewrite IH, map_app, map_map, <- app_assoc. f_equal. f_equal. apply map_ext. intros x. lia.
Qed.

Local Lemma vl_fold_max_nonneg : forall l, 0 <= fold_right Z.max 0 l.
Proof. induction l as [|x l IH]; cbn [fold_right]; lia. Qed.

Lemma vl_refused_peak_nonneg : forall ok cnt fail k hs, 0 <= prh_refused_peak ok cnt fail k hs.
Proof. intros ok cnt fail k hs. unfold prh_refused_peak. apply vl_fold_max_nonneg. Qed.

Lemma vl_refused_rep : forall k1 (ok2 : list bool) cnt fail i, (i < k1)%nat ->
  prh_refused (repeat true k1 ++ ok2) cnt fail i = false.
Proof. intros k1 ok2 cnt fail i Hi. unfold prh_refused. rewrite vl_nth_rep_app1 by exact Hi. reflexivity. Qed.

Lemma vl_refused_app : forall k1 (ok2 : list bool) cnt fail i,
  prh_refused (repeat true k1 ++ ok2) cnt fail (k1 + i) = prh_refused ok2 (cnt + Z.of_nat k1) fail i.
Proof.
  intros k1 ok2 cnt fail i. unfold prh_refused. rewrite vl_nth_rep_app2 by lia.
  replace (k1 + i - k1)%nat with i by lia.
  replace (cnt + Z.of_nat (k1 + i)) with (cnt + Z.of_nat k1 + Z.of_nat i) by lia. reflexivity.
Qed.

Local Lemma vl_nth_skipn : forall k (l : list Z) j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction k as [|k IH]; intros l j; [reflexivity|].
  destruct l as [|x l]; [destruct j; reflexivity | exact (IH l j)].
Qed.

Local Lemma vl_skipn_app_len : forall (A : Type) (l1 l2 : list A), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros A. induction l1 as [|x l1 IH]; intros l2; [reflexivity | exact (IH l2)]. Qed.

Local Lemma vl_map_seq_shift : forall (f g : nat -> Z) k1 len s,
  (forall j, f (j + k1)%nat = g j) -> map f (List.seq (s + k1) len) = map g (List.seq s len).
Proof.
  intros f g k1 len. induction len as [|len IH]; intros s H; [reflexivity|].
  cbn [List.seq map]. rewrite H. f_equal. exact (IH (S s) H).
Qed.

Local Lemma vl_fold_max_zero : forall (f : nat -> Z) l R, (forall i, In i l -> f i = 0) -> 0 <= R ->
  fold_right Z.max R (map f l) = R.
Proof.
  intros f l R H HR. induction l as [|i l IH]; cbn [map fold_right]; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros j Hj; apply H; right; exact Hj). lia.
Qed.

(* the refusal peak of a granted prefix of k1 calls followed by k2 more: the prefix refuses nothing *)
Lemma vl_refused_peak_app : forall k1 k2 (ok2 : list bool) cnt fail hs,
  prh_refused_peak (repeat true k1 ++ ok2) cnt fail (k1 + k2) hs =
  prh_refused_peak ok2 (cnt + Z.of_nat k1) fail k2 (skipn k1 hs).
Proof.
  intros k1 k2 ok2 cnt fail hs. unfold prh_refused_peak.
  rewrite List.seq_app, map_app, fold_right_app.
  rewrite (vl_map_seq_shift _ (fun i => if prh_refused ok2 (cnt + Z.of_nat k1) fail i
                                        then Z.min SIZE_MAXZ (nth i (skipn k1 hs) 0) else 0) k1 k2 0).
  2:{ intros j. cbv beta. replace (j + k1)%nat with (k1 + j)%nat by lia.
      rewrite vl_refused_app, vl_nth_skipn. reflexivity. }
  apply vl_fold_max_zero; [|apply vl_fold_max_nonneg].
  intros i Hi. apply List.in_seq in Hi. cbv beta. rewrite vl_refused_rep by lia. reflexivity.
Qed.

(* the refusal peak reads only its first k entries *)
Lemma vl_refused_peak_app_r : forall ok cnt fail k (l X : list Z), (k <= length l)%nat ->
  prh_refused_peak ok cnt fail k (l ++ X) = prh_refused_peak ok cnt fail k l.
Proof.
  intros ok cnt fail k l X Hk. unfold prh_refused_peak. f_equal. apply map_ext_in.
  intros i Hi. apply List.in_seq in Hi. rewrite app_nth1 by lia. reflexivity.
Qed.

Local Lemma vl_skipn_len_app : forall (A : Type) (l1 l2 : list A) k, length l1 = k -> skipn k (l1 ++ l2) = l2.
Proof. intros A l1 l2 k <-. apply vl_skipn_app_len. Qed.

(* THE WHOLE CALL'S GRANTED TRACE AT A STEP: the call so far granted tr1's calls, the step makes k2 calls, and the
   call's all-granted trace is tr1, then the step's all-granted trace gt2, then the rest. The call's refusal peak
   over those k1 + k2 calls is the step's own over gt2, at the live bytes after tr1 *)
Lemma vl_refused_peak_gsplit : forall tr1 (ok2 : list bool) cnt fail k2 L gt2 rest,
  (k2 <= PjGrammar.calls gt2)%nat ->
  prh_refused_peak (repeat true (PjGrammar.calls tr1) ++ ok2) cnt fail (PjGrammar.calls tr1 + k2)
    (map (Z.add L) (prh_ev_helds (tr1 ++ gt2 ++ rest))) =
  prh_refused_peak ok2 (cnt + Z.of_nat (PjGrammar.calls tr1)) fail k2
    (map (Z.add (L + PjGrammar.held tr1)) (prh_ev_helds gt2)).
Proof.
  intros tr1 ok2 cnt fail k2 L gt2 rest Hk.
  rewrite vl_refused_peak_app, vl_ev_helds_app, map_app.
  rewrite (vl_skipn_len_app _ (map (Z.add L) (prh_ev_helds tr1)) _ (PjGrammar.calls tr1))
    by (rewrite length_map; apply vl_ev_helds_length).
  rewrite map_map, vl_ev_helds_app, map_app.
  rewrite vl_refused_peak_app_r by (rewrite length_map, vl_ev_helds_length; exact Hk).
  f_equal. apply map_ext. intros x. lia.
Qed.

(* the ledger move of a granted prefix followed by one more call's move. The composed move's granted trace is the
   prefix followed by the call's (tr1 ++ gt2); the prefix's own gt1 is free, since a granted prefix refuses nothing *)
Lemma vl_ledger_move_app : forall Lam peak cnt fail ran most gt1 tr1 D1 Lam1 peak1 cnt1 fail1 ran1 ok2 gt2 tr2 D2
    Lam2 peak2 cnt2 fail2 ran2,
  0 <= cnt -> cnt + Z.of_nat (PjGrammar.calls tr1) < 2 ^ 64 ->
  rd_ledger_move Lam peak cnt fail ran most (repeat true (PjGrammar.calls tr1)) gt1 tr1 D1 Lam1 peak1 cnt1 fail1
    ran1 ->
  rd_ledger_move Lam1 peak1 cnt1 fail1 ran1 most ok2 gt2 tr2 D2 Lam2 peak2 cnt2 fail2 ran2 ->
  Ledger.lsum D1 = PjGrammar.held tr1 ->
  Permutation (lszR (tr1 ++ tr2)) (lszR tr1 ++ lszR tr2) ->
  rd_ledger_move Lam peak cnt fail ran most (repeat true (PjGrammar.calls tr1) ++ ok2) (tr1 ++ gt2) (tr1 ++ tr2)
    (D1 ++ D2) Lam2 peak2 cnt2 fail2 ran2.
Proof.
  intros Lam peak cnt fail ran most gt1 tr1 D1 Lam1 peak1 cnt1 fail1 ran1 ok2 gt2 tr2 D2 Lam2 peak2 cnt2 fail2 ran2
    Hc0 Hcb H1 H2 HD1 HL.
  destruct H1 as (O1 & C1 & F1 & P1 & Q1 & N1 & K1).
  destruct H2 as (O2 & C2 & F2 & P2 & Q2 & N2 & K2).
  unfold rd_ledger_move. rewrite PjGrammar.calls_app, vl_ev_reqs_app.
  pose proof (vl_ev_reqs_length tr1) as Hrl.
  set (k1 := PjGrammar.calls tr1) in *. set (k2 := PjGrammar.calls tr2) in *.
  assert (RP1 : prh_refused_peak (repeat true k1) cnt fail k1 (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds gt1)) = 0).
  { apply prh_refused_peak_granted. intros i Hi Hn. rewrite vl_nth_repeat_true in Hn. discriminate. }
  destruct O1 as (O1a & O1b & _).
  assert (Hnf : forall i, (i < k1)%nat -> cnt + Z.of_nat i <> fail).
  { intros i Hi E. specialize (O1a i Hi E). rewrite vl_nth_repeat_true in O1a. discriminate. }
  assert (Hlo : ~ (cnt <= fail < cnt + Z.of_nat k1)).
  { intros [Ha Hb]. apply (Hnf (Z.to_nat (fail - cnt))); [lia | rewrite Z2Nat.id by lia; lia]. }
  assert (Hf1 : fail1 = fail) by exact (proj2 F1 Hlo).
  assert (Hr1 : ran1 = ran).
  { destruct O1b as [E | (_ & i & _ & Hn & _)]; [exact E|].
    unfold prh_refused in Hn. rewrite vl_nth_repeat_true in Hn. cbn in Hn. discriminate Hn. }
  assert (Hc1 : cnt1 = cnt + Z.of_nat k1) by (rewrite C1; apply Z.mod_small; lia).
  clear C1 F1 O1a O1b. subst fail1 ran1 cnt1.
  destruct O2 as (O2a & O2b & O2c).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - unfold prh_oks. split; [|split].
    + intros i Hi E. destruct (Nat.lt_ge_cases i k1) as [Hlt|Hge].
      * exfalso. exact (Hnf i Hlt E).
      * rewrite vl_nth_rep_app2 by lia. apply O2a; lia.
    + destruct O2b as [E | (E & i & Hi & Hn & Hm)]; [left; exact E | right; split; [exact E|]].
      exists (k1 + i)%nat. split; [lia|]. split.
      * rewrite vl_refused_app. exact Hn.
      * rewrite app_nth2 by lia. replace (k1 + i - length (prh_ev_reqs tr1))%nat with i by lia. exact Hm.
    + intros i Hi Hn Hm. destruct (Nat.lt_ge_cases i k1) as [Hlt|Hge].
      * rewrite (vl_refused_rep k1 ok2 cnt fail i Hlt) in Hn. discriminate Hn.
      * replace i with (k1 + (i - k1))%nat in Hn, Hm by lia. rewrite vl_refused_app in Hn.
        rewrite app_nth2 in Hm by lia.
        replace (k1 + (i - k1) - length (prh_ev_reqs tr1))%nat with (i - k1)%nat in Hm by lia.
        apply (O2c (i - k1)%nat); [lia | exact Hn | exact Hm].
  - rewrite C2, Nat2Z.inj_add, Z.add_assoc. reflexivity.
  - unfold fail_afterR in *. destruct F2 as (F2a & F2b). rewrite Nat2Z.inj_add. split; intros Hx.
    + assert (cnt + Z.of_nat k1 <= fail).
      { destruct (Z_lt_le_dec fail (cnt + Z.of_nat k1)) as [Hy|Hy]; [|exact Hy].
        exfalso. apply Hlo. lia. }
      apply F2a. lia.
    + apply F2b. intros Hy. apply Hx. lia.
  - eapply perm_trans; [exact P2|]. eapply perm_trans; [apply Permutation_app_head; exact P1|].
    rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - rewrite map_app. eapply perm_trans; [apply Permutation_app; [exact Q1 | exact Q2]|].
    rewrite <- map_app. apply Permutation_map. apply Permutation_sym. exact HL.
  - rewrite length_app, Nat2Z.inj_add, vl_nlive_app. lia.
  - assert (HL1 : Ledger.lsum Lam1 = Ledger.lsum Lam + PjGrammar.held tr1)
      by (rewrite (vl_lsum_perm _ _ P1), vl_lsum_app, HD1; lia).
    assert (Hsk : skipn k1 (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds (tr1 ++ gt2))) =
                  map (Z.add (Ledger.lsum Lam1)) (prh_ev_helds gt2)).
    { rewrite vl_ev_helds_app, map_app.
      replace k1 with (length (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds tr1)))
        by (rewrite length_map, vl_ev_helds_length; reflexivity).
      rewrite vl_skipn_app_len, map_map, HL1. apply map_ext. intros x. lia. }
    rewrite vl_refused_peak_app, Hsk, K2, K1, RP1, HL1, vl_hpeak_app.
    pose proof (vl_hpeak_nonneg tr1). pose proof (vl_hpeak_nonneg tr2).
    pose proof (vl_refused_peak_nonneg ok2 (cnt + Z.of_nat k1) fail k2
      (map (Z.add (Ledger.lsum Lam + PjGrammar.held tr1)) (prh_ev_helds gt2))).
    lia.
Qed.

Lemma vl_skipn_rep : forall (k : nat) (okr : list bool), skipn k (repeat true k ++ okr) = okr.
Proof. induction k as [|k IH]; intros okr; cbn [repeat app skipn]; [reflexivity | apply IH]. Qed.

Lemma vl_ok_upto_rep : forall (k : nat) (okr : list bool), PjGrammar.ok_upto (repeat true k ++ okr) k.
Proof. intros k okr i Hi. exact (vl_nth_rep_app1 k okr i Hi). Qed.

Lemma vl_agrees_some : forall (A : Type) (m : PjGrammar.M A) ok v tr okr,
  PjGrammar.agrees m -> m ok = (Some v, tr, okr) ->
  fst (fst (m [])) = Some v /\ snd (fst (m [])) = tr /\ PjGrammar.ok_upto ok (PjGrammar.calls tr) /\
  (forall okr', m (repeat true (PjGrammar.calls tr) ++ okr') = (Some v, tr, okr')).
Proof.
  intros A m ok v tr okr HA HE.
  destruct (PjGrammar.agrees_some _ _ _ _ _ _ HA HE) as (H0 & _).
  assert (HU : PjGrammar.ok_upto ok (PjGrammar.calls tr)).
  { destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls tr)) as [Hu | (j & Hj & Hf & Hu)]; [exact Hu|].
    exfalso.
    assert (Hj' : (j < PjGrammar.calls (snd (fst (m []))))%nat) by (rewrite H0; exact Hj).
    destruct (proj2 (HA ok) j Hj' Hf Hu) as (P & e & rest & Em & _).
    rewrite HE in Em. discriminate Em. }
  rewrite H0. cbn [fst snd].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HU|].
  intros okr'. pose proof (proj1 (HA (repeat true (PjGrammar.calls tr) ++ okr'))) as H1.
  rewrite H0 in H1. cbn [fst snd] in H1.
  rewrite (H1 (vl_ok_upto_rep _ _)). rewrite vl_skipn_rep. reflexivity.
Qed.

Lemma vl_oks_granted : forall ok cnt fail (k : nat) ns most ran ran',
  PjGrammar.ok_upto ok k -> prh_oks ok cnt fail k ns most ran ran' ->
  prh_oks (repeat true k) cnt fail k ns most ran ran'.
Proof.
  intros ok cnt fail k ns most ran ran' HU (O1 & O2 & O3).
  unfold prh_oks. split; [|split].
  - intros i Hi Hc. exfalso. pose proof (O1 i Hi Hc) as Hf. rewrite (HU i Hi) in Hf. discriminate Hf.
  - left. destruct O2 as [E | (_ & i & Hi & Hn & _)]; [exact E|].
    unfold prh_refused in Hn. rewrite (HU i Hi) in Hn. cbn in Hn. discriminate Hn.
  - intros i Hi Hn. unfold prh_refused in Hn. rewrite vl_nth_repeat_true in Hn. cbn in Hn. discriminate Hn.
Qed.

Lemma vl_hpeak_le_pos : forall t, hpeakR t <= Z.of_nat (PjGrammar.pos t).
Proof.
  induction t as [|e t IH]; cbn [hpeakR PjGrammar.pos]; [lia|].
  assert (He : PjGrammar.held_ev e <= Z.of_nat (PjGrammar.pos_ev e))
    by (destruct e; cbn [PjGrammar.held_ev PjGrammar.pos_ev]; lia).
  rewrite Nat2Z.inj_add. lia.
Qed.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}
        {HL : Z}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation PLA := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
#[local] Notation VAL := (@pa_val _ A_prog_listing PAI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* the subtree moves of a granted prefix followed by one more call's moves *)
Lemma vl_blocks_move_app : forall ly0 S0 ly1 S1 ly2 S2 D1 D2 tr1 tr2 x d,
  rd_blocks_move B ly0 S0 ly1 S1 D1 tr1 x d ->
  (forall a k, In (a, k) D2 -> ~ In (a - cf_head, k + cf_head) (ablocks B ly1 S1)) ->
  Permutation (ablocks B ly2 S2) (prhReader_ab D2 ++ ablocks B ly1 S1) ->
  Permutation (frames S2) (frames S1) ->
  hpeakR (tr1 ++ tr2) <= 224 * Z.of_nat (length x) + 512 * Z.of_nat (PjGrammar.MAXD - d) ->
  rd_blocks_move B ly0 S0 ly2 S2 (D1 ++ D2) (tr1 ++ tr2) x d.
Proof.
  intros ly0 S0 ly1 S1 ly2 S2 D1 D2 tr1 tr2 x d (B1 & B2 & B3 & _) HN HP HF HH.
  refine (conj _ (conj _ (conj _ HH))).
  - intros a k Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (B1 a k Hin)|].
    intros Hab. apply (HN a k Hin). eapply Permutation_in; [apply Permutation_sym; exact B2|].
    apply in_or_app. right. exact Hab.
  - eapply perm_trans; [exact HP|]. eapply perm_trans; [apply Permutation_app_head; exact B2|].
    unfold prhReader_ab. rewrite map_app, app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply perm_trans; [exact HF | exact B3].
Qed.

(* ---- THE PER-EVENT LIVE ROOM (the kit's cut, PRH_Base.prh_live_evs): a prefix of the events, and the tail from the state
   the prefix leads to ---- *)
Lemma vl_zsum_perm : forall l l' : list Z, Permutation l l' -> fold_right Z.add 0 l = fold_right Z.add 0 l'.
Proof.
  intros l l' H. induction H as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; cbn [fold_right]; lia.
Qed.

Lemma vl_live_at_prefix : forall S E1 E2 j, (j <= length E1)%nat -> prh_live_at S (E1 ++ E2) j = prh_live_at S E1 j.
Proof.
  intros S E1 E2 j Hj. unfold prh_live_at. rewrite firstn_app.
  replace (j - length E1)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

(* a callee's events are a prefix of the caller's: its per-event room is the caller's at those events *)
Lemma vl_live_evs_prefix : forall S E1 E2, prh_live_evs S (E1 ++ E2) -> prh_live_evs S E1.
Proof.
  intros S E1 E2 H j e Hj.
  assert (Hlt : (j < length E1)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  rewrite <- (vl_live_at_prefix S E1 E2 j) by lia. apply H. rewrite nth_error_app1 by exact Hlt. exact Hj.
Qed.

(* the events after a prefix, from the state the prefix leads to (its live requests moved by the prefix's events) *)
Lemma vl_live_evs_tail : forall S S' E1 E2,
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E1) ->
  prh_live_evs S (E1 ++ E2) -> prh_live_evs S' E2.
Proof.
  intros S S' E1 E2 HP H j e Hj.
  specialize (H (length E1 + j)%nat e).
  rewrite nth_error_app2 in H by lia. replace (length E1 + j - length E1)%nat with j in H by lia.
  specialize (H Hj).
  assert (Heq : prh_live_at S' E2 j = prh_live_at S (E1 ++ E2) (length E1 + j)).
  { unfold prh_live_at. rewrite firstn_app. replace (length E1 + j - length E1)%nat with j by lia.
    rewrite (firstn_all2 E1) by lia. rewrite PresetReqAt.hlive_from_app.
    apply vl_zsum_perm. apply PresetReqAtNoMiss.hlive_from_perm. exact HP. }
  rewrite Heq. exact H.
Qed.

(* the room of the continuation after one call of the granted run (the kit's cut: the per-event live room moves by the
   call's live-request move; the request bound is the tail's largest request) *)
Lemma vl_room_tail : forall (S S' : astate) tv t',
  rd_room S (tv ++ t') -> room_live_cf S' ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.rd_hevs tv)) ->
  rd_room S' t'.
Proof.
  intros S S' tv t' (R1 & R2 & R3) HR HP.
  rewrite vl_maxreq_app in R2.
  unfold rd_room. refine (conj HR (conj _ _)); [lia|].
  assert (Ha : PresetReqAt.rd_hevs (tv ++ t') = PresetReqAt.rd_hevs tv ++ PresetReqAt.rd_hevs t')
    by (unfold PresetReqAt.rd_hevs; apply flat_map_app).
  rewrite Ha in R3. exact (vl_live_evs_tail S S' _ _ HP R3).
Qed.

End V.

Print Assumptions vl_room_tail.
Print Assumptions vl_live_evs_prefix.
Print Assumptions vl_live_evs_tail.
