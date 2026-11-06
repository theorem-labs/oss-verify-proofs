(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the secondary-request count of relay_remove's request trace (W_contract.rr_tr). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfTrRr.v, with its module paths changed; 60 of its 102 lines of code are new or changed and 124 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfTrRr.v, with its module paths and module names changed. *)
(* KF-COUNT row #5, relay_remove: the count nsec_tr (ReplyKfNsecB.v) of the requests rr_tr makes, in the form agreed for
   the drains (per drained entry, the bytes the drain consumes pay for its begins).  proves no function (kind: segment
   lemma).  The image-B (asan-ubsan) twin of lib/A/ReplyKfTrRr.v at 6f39e9474dd (F6): the same text over
   lib/B/W_contract.v and lib/B/W_rep.v.
   - kf_rr: for fd >= 0 and the first entry e of fd: 21 * (count of rr_tr) + (when e is open, the partial line the
     drain leaves) <= 21 * KC_rr + (when e is open, |re_U e| + |pending_stream h|), KC_rr = KC_dr + KC_ke = 30 + 15.
     The drain is ReplyKfTrB.v's kf_dr (its four premises on e and h, asked when e is open); the key run of
     gestures_end over the keys the drain leaves counts at most KC_ke = 15 (ReplyKfChainB.v kf_keys); the two frees
     count 0.  Both need rr_tr's requests below 2 ^ 30 (rr_spec's pre: tr_max tr < MMAX, and fr_MMAX <= 2 ^ 30,
     CfParamsReplyB.reply_HMMAX, lib/B/CfParamsReplyB.v:129).
   - kf_rr_at: kf_rr from rr_spec's own premises at the entry: asrc_at and aentry_ok (ReplyKfTrB.v kf_dr_src /
     kf_dr_ent), tr_max tr < MMAX, MMAX <= 2 ^ 30.
   - kf_rr_none: no entry of fd (or fd < 0): rr_tr is empty, its count is 0.
   - kf_rr_g: the same bound for ANY drain bound of kf_dr's form (premise DRP, constant KCd >= 0); kf_rr is it at
     kf_dr. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT gestures_end_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_kit W_listing W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyKfNsecB ReplyKfChainB ReplyKfTrB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ relay_remove *)
(* rr_tr is empty for fd < 0 or no entry of fd *)
Lemma kf_rr_none : forall c mx no cap FD es h,
  (FD < 0 \/ find (fun e => re_fd e =? FD) es = None) -> nsec_tr (W_contract.rr_tr c mx no cap FD es h) = 0.
Proof.
  intros c mx no cap FD es h [H|H]; unfold W_contract.rr_tr.
  - rewrite (proj2 (Z.ltb_lt FD 0) H). reflexivity.
  - destruct (FD <? 0); [reflexivity|]. rewrite H. reflexivity.
Qed.

(* the drain's requests are among rr_tr's: its largest request is at most rr_tr's *)
Lemma kf_rr_tm_dr : forall c mx no cap FD es h e,
  0 <= FD -> find (fun e => re_fd e =? FD) es = Some e -> re_eof e = 0 ->
  W_contract.tr_max (W_contract.dr_tr c mx no cap e h) <= W_contract.tr_max (W_contract.rr_tr c mx no cap FD es h).
Proof.
  intros c mx no cap FD es h e HFD Hf Ho. unfold W_contract.rr_tr.
  rewrite (proj2 (Z.ltb_ge FD 0) HFD), Hf. cbv beta iota zeta.
  rewrite (proj2 (Z.eqb_eq (re_eof e) 0) Ho). cbv beta iota. rewrite !kf_tm_app. lia.
Qed.

Section rr.
(* a drain bound of kf_dr's form, over its premise DRP and its constant KCd *)
Variable KCd : Z.
Hypothesis KCd_nonneg : 0 <= KCd.
Variable DRP : W_rep.ctl -> Z -> Z -> Z -> rentry -> hsrc -> Prop.
Hypothesis kf_dr_h : forall c mx no cap e h, DRP c mx no cap e h ->
  21 * nsec_tr (W_contract.dr_tr c mx no cap e h) +
    Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))) <=
  21 * KCd + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).

Lemma kf_rr_g : forall c mx no cap FD es h e,
  0 <= FD -> find (fun e => re_fd e =? FD) es = Some e ->
  (re_eof e = 0 -> DRP c mx no cap e h) ->
  W_contract.tr_max (W_contract.rr_tr c mx no cap FD es h) < 2 ^ 30 ->
  21 * nsec_tr (W_contract.rr_tr c mx no cap FD es h) +
    (if re_eof e =? 0 then Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))) else 0) <=
  21 * (KCd + KC_ke) + (if re_eof e =? 0 then Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) else 0).
Proof.
  intros c mx no cap FD es h e HFD Hf HD HM.
  assert (F0 : forall (P : Type) (k1 k2 : Z) (a b : RelayRunT.addr P),
    nsec_tr [RelayRunT.RFree k1 a; RelayRunT.RFree k2 b] = 0) by reflexivity.
  unfold W_contract.rr_tr in HM |- *. rewrite (proj2 (Z.ltb_ge FD 0) HFD), Hf in HM |- *.
  cbv beta iota zeta in HM |- *.
  destruct (re_eof e =? 0) eqn:Ho; cbv beta iota in HM |- *.
  - apply Z.eqb_eq in Ho. pose proof (kf_dr_h c mx no cap e h (HD Ho)) as D.
    rewrite !kf_tm_app in HM. rewrite !nsec_tr_app, F0.
    match goal with |- context [nsec_tr (fst (gestures_end_b_c.keys_end_run ?lv ?m ?n ?cp ?x ?jj ?oo))] =>
      assert (K : nsec_tr (fst (gestures_end_b_c.keys_end_run lv m n cp x jj oo)) <= KC_ke)
        by (apply kf_keys; lia) end.
    lia.
  - rewrite !kf_tm_app in HM. rewrite !nsec_tr_app, F0.
    match goal with |- context [nsec_tr (fst (gestures_end_b_c.keys_end_run ?lv ?m ?n ?cp ?x ?jj ?oo))] =>
      assert (K : nsec_tr (fst (gestures_end_b_c.keys_end_run lv m n cp x jj oo)) <= KC_ke)
        by (apply kf_keys; lia) end.
    rewrite nsec_tr_nil. lia.
Qed.
End rr.

(* ------------------------------------------------------------------ at the drain lane's kf_dr *)
Definition KC_rr : Z := KC_dr + KC_ke.

Lemma kf_rr : forall c mx no cap FD es h e,
  0 <= FD -> find (fun e => re_fd e =? FD) es = Some e ->
  (re_eof e = 0 ->
   0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
   (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\ Z.of_nat (length (re_U e)) <= 6000) ->
  W_contract.tr_max (W_contract.rr_tr c mx no cap FD es h) < 2 ^ 30 ->
  21 * nsec_tr (W_contract.rr_tr c mx no cap FD es h) +
    (if re_eof e =? 0 then Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))) else 0) <=
  21 * KC_rr + (if re_eof e =? 0 then Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) else 0).
Proof.
  intros c mx no cap FD es h e HFD Hf HP HM. unfold KC_rr.
  apply (kf_rr_g KC_dr KC_dr_nonneg
    (fun c mx no cap e h =>
       0 <= hs_off h /\ (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) /\
       (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\ Z.of_nat (length (re_U e)) <= 6000 /\
       W_contract.tr_max (W_contract.dr_tr c mx no cap e h) < 2 ^ 30)); [| exact HFD | exact Hf | | exact HM].
  - intros c' mx' no' cap' e' h' (H1 & H2 & H3 & H4 & H5). exact (kf_dr c' mx' no' cap' e' h' H1 H2 H3 H4 H5).
  - intros Ho. destruct (HP Ho) as (H1 & H2 & H3 & H4). pose proof (kf_rr_tm_dr c mx no cap FD es h e HFD Hf Ho).
    repeat split; try assumption. lia.
Qed.

Lemma KC_rr_val : KC_rr = 45.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ the call site supplies the premises *)
Section pre.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : W_kit.PAImg W_listing.fr_prog_listing}.
Variable B : YG0f.asyms.

(* rr_spec_x's premises at the entry of fd when it is open (its dr_src_ok's asrc_at, lib/B/W_contract.v:1274-1276;
   arelay_at's aentry_ok, lib/B/W_rep.v:157,165), its tr_max tr < MMAX (lib/B/W_contract_x.v:938), and MMAX <= 2 ^ 30
   (CfParamsReplyB.reply_HMMAX at fr_MMAX, lib/B/CfParamsReplyB.v:129) *)
Lemma kf_rr_at : forall ly S W mem HA c mx no cap FD es h e MMAX,
  0 <= FD -> find (fun e => re_fd e =? FD) es = Some e ->
  (re_eof e = 0 -> W_rep.asrc_at B ly S W mem HA h /\ W_rep.aentry_ok B ly S W mem e) ->
  W_contract.tr_max (W_contract.rr_tr c mx no cap FD es h) < MMAX -> MMAX <= 2 ^ 30 ->
  21 * nsec_tr (W_contract.rr_tr c mx no cap FD es h) +
    (if re_eof e =? 0 then Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))) else 0) <=
  21 * KC_rr + (if re_eof e =? 0 then Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) else 0).
Proof.
  intros ly S W mem HA c mx no cap FD es h e MMAX HFD Hf HP HM HX.
  apply kf_rr; [exact HFD | exact Hf | | lia].
  intros Ho. destruct (HP Ho) as [Hs He].
  destruct (kf_dr_src B ly S W mem HA h Hs) as [H1 H2]. destruct (kf_dr_ent B ly S W mem e He) as [H3 H4].
  repeat split; try assumption. intros _. exact H2.
Qed.
End pre.
