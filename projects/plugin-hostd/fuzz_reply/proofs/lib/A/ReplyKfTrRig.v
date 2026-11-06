(* The secondary-request count nsec_tr (ReplyKfNsec.v) of relay_instance_gone's request trace rig_tr (W_contract.v), in
   the drain form of ReplyKfTr.v (the bytes a drain consumes pay for its begins), summed over the table's open entries.
   proves no function (kind: segment lemma).
   - kf_rig: 21 * (count of rig_tr) + (the partial lines the open entries' drains leave) <= 21 * KC_rig + (the open
     entries' |re_U e| + |pending_stream h|), with KC_rig = 4 * (KC_dr + KC_ke) = 4 * (30 + 15) = 180.
   - rig_tr is relay_instance_gone_b_c.gone_run's trace: per entry, drain (s) when s->eof = 0, at the liveness of a
     one-byte send (sl_live c 1), from the g_nout / g_capout the earlier entries leave, at addresses named from base
     j > 0; then the key run of gestures_end_instance.  kf_gone_run takes each drain by the drain bound at ANY
     liveness, g_nout, g_capout, base and addresses (kf_drain_tr: its premises are kf_dr_pre on (e, h) and the drain's
     requests below 2 ^ 30, a segment of rig_tr), and each key run by ReplyKfChain.kf_keys (at most
     KC_ke = 15 when its requests are below 2 ^ 30; rig_spec's pre: tr_max tr < MMAX, and at top_x MMAX is
     CfParamsReply.fr_MMAX = 1,072,693,248).  The table holds at most 4 entries (rig_spec's g_nsrc <= 4).
   - kf_tail: the partial line is stated at rig's own (c, mx, no, cap); ReplyCntAcc.acc_fin_canon rewrites it to the
     dr_fin of any other liveness, g_nout and g_capout (kf_tail_fin), for example rig_rel's chained ones.
   The drain's own bound is ReplyKfTr.kf_drain_tr (KC_dr = 30); kf_dr_pre collects its premises on
   (e, h), which ReplyKfTr.kf_dr_src / kf_dr_ent derive from asrc_at / aentry_ok. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT RelayRunF send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rep W_contract ReplyCntAcc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyKfNsec ReplyKfChain ReplyKfTr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ the sums over the open entries *)
(* f summed over the entries (e, (h, j)) with s->eof = 0 *)
Definition osum (f : rentry -> hsrc -> Z) (ps : list (rentry * (hsrc * nat))) : Z :=
  fold_right Z.add 0 (map (fun p => if re_eof (fst p) =? 0 then f (fst p) (fst (snd p)) else 0) ps).
Lemma osum_cons : forall f e hj ps, osum f ((e, hj) :: ps) = (if re_eof e =? 0 then f e (fst hj) else 0) + osum f ps.
Proof. reflexivity. Qed.

(* an open entry's input: the relay's partial line and the harness's pending bytes *)
Definition kf_in (e : rentry) (h : hsrc) : Z := Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
(* an open entry's partial line after its drain, at rig's own liveness, g_nout and g_capout *)
Definition kf_tail (c : W_rep.ctl) (mx no cap : Z) (e : rentry) (h : hsrc) : Z :=
  Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))).

(* the partial line does not depend on the drain's sends *)
Lemma kf_tail_fin : forall c mx no cap live mx' no' cap' e h,
  Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin live mx' no' cap' e h))) = kf_tail c mx no cap e h.
Proof.
  intros c mx no cap live mx' no' cap' e h. unfold kf_tail, W_contract.dr_fin.
  pose proof (ReplyCntAcc.acc_fin_canon live (W_contract.dr_live c h) mx' mx no' no cap' cap e h) as X.
  apply (f_equal drain_b_c.ds_u) in X. unfold ReplyCntAcc.acc_canon in X. cbn [drain_b_c.ds_u] in X.
  rewrite X. reflexivity.
Qed.

Lemma kf_combine_len : forall (A B : Type) (l : list A) (l' : list B), (length (combine l l') <= length l)%nat.
Proof. intros A B l. induction l as [|x l IH]; intros [|y l']; cbn [combine length]; try lia. specialize (IH l'). lia. Qed.

(* the drain bound's premises on the entry and its harness source (ReplyKfTr.kf_drain_tr; kf_dr_src / kf_dr_ent derive
   them from asrc_at and aentry_ok) *)
Definition kf_dr_pre (e : rentry) (h : hsrc) : Prop :=
  0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
  Z.of_nat (length (re_U e)) <= 6000.

(* ------------------------------------------------------------------ relay_instance_gone *)

Definition KC_rig : Z := 4 * (KC_dr + KC_ke).

(* gone_run over the entries ps: each open entry's drain by kf_drain_tr, each key run by kf_keys *)
Lemma kf_gone_run : forall c0 mx0 no0 cap0 lv mx pre nm ps no cap j o,
  Forall (fun p => re_eof (fst p) = 0 -> kf_dr_pre (fst p) (fst (snd p))) ps ->
  W_contract.tr_max (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) < 2 ^ 30 ->
  21 * nsec_tr (fst (fst (fst (relay_instance_gone_b_c.gone_run lv mx no cap pre ps nm j o)))) +
    osum (kf_tail c0 mx0 no0 cap0) ps <=
  21 * (KC_dr + KC_ke) * Z.of_nat (length ps) + osum kf_in ps.
Proof.
  intros c0 mx0 no0 cap0 lv mx pre nm ps. pose proof KC_dr_nonneg as K0.
  induction ps as [|[e hj] r IH]; intros no cap j o HF HM.
  - cbn [relay_instance_gone_b_c.gone_run fst length osum map fold_right Z.of_nat]. rewrite nsec_tr_nil. lia.
  - apply Forall_cons_iff in HF as [HF0 HFr]. cbn [fst snd] in HF0.
    rewrite !osum_cons. cbn [length]. rewrite Nat2Z.inj_succ.
    cbn [relay_instance_gone_b_c.gone_run] in HM |- *. cbv zeta in HM |- *.
    match goal with |- context [relay_instance_gone_b_c.gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
      pose proof (IH n c j1 o1 HFr) as IHr;
      destruct (relay_instance_gone_b_c.gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
    cbn [fst snd] in IHr, HM |- *.
    rewrite !kf_tm_app in HM. rewrite !nsec_tr_app.
    specialize (IHr ltac:(lia)).
    match goal with |- context [nsec_tr (fst (gestures_end_b_c.keys_end_run ?l ?m ?n ?cp ?x ?jj ?oo))] =>
      assert (HK : nsec_tr (fst (gestures_end_b_c.keys_end_run l m n cp x jj oo)) <= KC_ke)
        by (apply kf_keys; lia) end.
    unfold KC_ke in *.
    destruct (Z.eqb_spec (re_eof e) 0) as [E|E]; cbv beta iota in HM |- *.
    + destruct (HF0 E) as (P1 & P2 & P3 & P4).
      match goal with |- context [drain_b_c.drain_tr ?l ?m ?n ?cp ?ee ?h ?jj ?a] =>
        assert (HD : 21 * nsec_tr (drain_b_c.drain_tr l m n cp ee h jj a) +
                       Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin l m n cp ee h))) <=
                     21 * KC_dr + Z.of_nat (length (re_U ee)) + Z.of_nat (length (pending_stream h)))
          by (apply kf_drain_tr; first [assumption | lia]);
        rewrite (kf_tail_fin c0 mx0 no0 cap0 l m n cp ee h) in HD end.
      assert (KI : kf_in e (fst hj) = Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream (fst hj))))
        by reflexivity.
      lia.
    + rewrite nsec_tr_nil. lia.
Qed.

(* THE COUNT: relay_instance_gone's trace *)
Theorem kf_rig : forall c mx no cap ID es hs,
  (length es <= 4)%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> kf_dr_pre (fst p) (fst (snd p))) (combine es hs) ->
  W_contract.tr_max (W_contract.rig_tr c mx no cap ID es hs) < 2 ^ 30 ->
  21 * nsec_tr (W_contract.rig_tr c mx no cap ID es hs) + osum (kf_tail c mx no cap) (combine es hs) <=
  21 * KC_rig + osum kf_in (combine es hs).
Proof.
  intros c mx no cap ID es hs Hn HF HM.
  unfold W_contract.rig_tr, relay_instance_gone_b_c.relay_instance_gone_tr in HM |- *. cbv zeta in HM |- *.
  pose proof (kf_gone_run c mx no cap _ _ _ _ _ _ _ _ _ HF HM) as H.
  pose proof (kf_combine_len _ _ es hs) as HL.
  assert (HN : 0 <= Z.of_nat (length (combine es hs)) <= 4) by lia.
  unfold KC_rig, KC_ke, KC_dr in *. lia.
Qed.
