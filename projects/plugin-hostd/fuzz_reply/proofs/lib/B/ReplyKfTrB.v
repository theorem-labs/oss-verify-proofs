(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the secondary-request count of drain's request trace (drain_b_c.drain_tr, W_contract.dr_tr). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfTr.v, with its module paths changed; 10 of its 324 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfTr.v, with its module paths and module names changed. *)
(* KF-COUNT row #5, drain: the count nsec_tr (ReplyKfNsecB.v) of the requests one drain makes, in the form agreed for
   the drains: the bytes the drain consumes pay for its begins.  proves no function (kind: segment lemma).
   The image-B (asan-ubsan) twin of lib/A/ReplyKfTr.v at 88de4270740 (F6): the same text over lib/B/W_contract.v and
   lib/B/W_rep.v (the drain model, Prog/drain_b_c.v, is shared).
   - A drain's secondary requests are of three kinds (Prog/drain_b_c.v):
     (a) gesture_seen's held-array realloc to (|H| + 1) * 8 and the key's strndup, on a begin line not held
         (seen_tr :45-46).  A begin line has at least 20 bytes (SlotParse.begin_line_len, the fact
         ReKhMax.ekl_begin_cost sums), so 21 * (its count) <= |line| + 1 (kd_seen); the relayed lines' bytes with
         their NULs plus the partial line left are at most the partial line before plus the bytes read (kd_chunk), and
         the bytes read are the pending stream's (SlotDrain3.round_str).
     (b) three growth chains, each step from a block of s bytes to one of c >= 2 s bytes (ReplyKfChainB.kf_lg_grow):
         the relay buffer (grow_tr :28-31), g_out (send_line, kf_send) and the expected list's vector (16 cap ->
         32 cap, pushes_run :109-117).  The texts list_push copies are reference lines (at most 6,000 bytes,
         SlotDrain3Aux.lines_len6), so primary.
   - kf_drain_pot: for any liveness, base j and addresses a, 21 * (count) + |the partial line left| plus 21 times the
     three chains' potential kf_lg at the start is at most |re_U e| + |pending_stream h| plus 21 times their potential
     at the end (drain_fin).  kf_drain_caps: each chain's end size is its start size or at most the trace's largest
     request.  Premises: 0 <= hs_off h and, while the reference splitter keeps its line (hs_overlong h <> 1),
     |hs_W h| <= 6,000 (asrc_at gives both: kf_dr_src).
   - kf_drain_tr / kf_dr (dr_tr is drain_tr at live := dr_live c h, j := 0, a := dadr0): with the trace's largest
     request below 2 ^ 30 (dr_spec's pre: tr_max < MMAX, fr_MMAX <= 2 ^ 30) and the relay buffer in its three sizes
     with at most 6,000 bytes kept (aentry_ok gives both: kf_dr_ent), 21 * (count) + |the partial line left| <=
     21 * KC_dr + |re_U e| + |pending_stream h|, KC_dr = 30: g_out at most 15 growths above 32,256 bytes, the
     expected vector at most 15 doublings above 2,016 entries (kf_lg_le15), the relay buffer none (it stays at most
     16,384 bytes, ReKhMax.rkm_drain_cap_set).
   - kf_dr_at: kf_dr from dr_spec_x's own premises (asrc_at, aentry_ok, tr_max < MMAX, MMAX <= 2 ^ 30). *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
  RelayRunT RelayRunF RelayModel RelayKeys HarnessRep RelayRep ListTr send_line_b_c drain_b_c SlotParse SlotDrain3Aux
  SlotDrain3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayCap ReKhMax.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_kit W_listing W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyKfNsecB ReplyKfChainB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ one event's count and largest request *)
Lemma kd_ns_malloc : forall (P : Type) (n : Z) (r : list (RelayRunT.rev P)),
  nsec_tr (RelayRunT.RMalloc n :: r) = (if 64512 <? n then 1 else 0) + nsec_tr r.
Proof. reflexivity. Qed.

Lemma kd_ns_realloc : forall (P : Type) (k n : Z) (x : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  nsec_tr (RelayRunT.RRealloc k n x :: r) = (if 64512 <? n then 1 else 0) + nsec_tr r.
Proof. reflexivity. Qed.

Lemma kd_ns_free : forall (P : Type) (k : Z) (x : RelayRunT.addr P) (r : list (RelayRunT.rev P)),
  nsec_tr (RelayRunT.RFree k x :: r) = nsec_tr r.
Proof. reflexivity. Qed.

Lemma kd_tm_nil : forall (P : Type), W_contract.tr_max (@nil (RelayRunT.rev P)) = 0.
Proof. reflexivity. Qed.

Lemma kd_sec : forall c, ((if 64512 <? c then 1 else 0) = 1 /\ 64512 < c) \/ ((if 64512 <? c then 1 else 0) = 0 /\ c <= 64512).
Proof. intros c. destruct (Z.ltb_spec 64512 c) as [H|H]; [left|right]; split; (reflexivity || exact H). Qed.

Ltac kd_ns := repeat first [ rewrite nsec_tr_app | rewrite kd_ns_malloc | rewrite kd_ns_realloc | rewrite kd_ns_free
                           | rewrite nsec_tr_nil ].

(* a primary allocation keeps a chain *)
Lemma kd_ch_prim : forall (P : Type) c c' n (r : list (RelayRunT.rev P)),
  n <= 64512 -> kf_ch c r c' -> kf_ch c (RelayRunT.RMalloc n :: r) c'.
Proof.
  intros P c c' n r Hn [H1 H2]. unfold kf_ch. rewrite kd_ns_malloc. unfold W_contract.tr_max in *.
  cbn [fold_right]. pose proof (kd_sec n) as K. lia.
Qed.

(* list_drop's free, or nothing *)
Lemma kd_td_ns : forall (w : bool) x m, nsec_tr (if w then list_drop_tra x m else []) = 0.
Proof. intros [|] x m; reflexivity. Qed.

Lemma kd_td_tm : forall (w : bool) x m, W_contract.tr_max (if w then list_drop_tra x m else []) = 0.
Proof. intros [|] x m; reflexivity. Qed.

(* ------------------------------------------------------------------ the three growth chains *)
(* the relay buffer: 0 -> 8192, cap -> 2 cap *)
Lemma kd_grow : forall cap used j b,
  kf_ch cap (fst (grow_tr cap used j b)) (fst (snd (grow_tr cap used j b))).
Proof.
  intros cap used j b. unfold grow_tr.
  destruct (cap - used <? 4096); cbn [fst snd]; [|apply kf_ch_nil].
  destruct (Z.eqb_spec cap 0) as [E|E]; cbn [fst snd].
  - apply kf_ch_malloc; [lia | apply kf_ch_nil].
  - apply kf_ch_realloc; [lia | apply kf_ch_nil].
Qed.

(* the expected list's vector, in bytes (16 * cap): 0 -> 128, 16 cap -> 32 cap; the texts are primary *)
Lemma kd_pushes : forall ls n cap j v rs, Forall (fun l => zlen l <= 6000) ls ->
  kf_ch (16 * cap) (fst (fst (pushes_run n cap ls j v rs))) (16 * snd (fst (pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs HF.
  - cbn [pushes_run fst snd]. apply kf_ch_nil.
  - apply Forall_cons_iff in HF as [Hl HF]. unfold zlen in Hl.
    cbn [pushes_run fst snd].
    match goal with |- context [pushes_run (n + 1) (push_cap n cap) r ?a1 ?a2 ?a3] =>
      pose proof (IH (n + 1) (push_cap n cap) a1 a2 a3 HF) as I end.
    eapply kf_ch_app; [|exact I].
    unfold list_push_tra, push_cap.
    destruct (Z.eqb_spec n cap) as [En|En]; [destruct (Z.eqb_spec cap 0) as [Ec|Ec]|]; cbv beta iota.
    + eapply kf_ch_app; [apply kf_ch_malloc; [lia | apply kf_ch_nil]|].
      apply kd_ch_prim; [lia | apply kf_ch_nil].
    + replace (16 * (cap * 2)) with (32 * cap) by lia.
      eapply kf_ch_app; [apply kf_ch_realloc; [lia | apply kf_ch_nil]|].
      apply kd_ch_prim; [lia | apply kf_ch_nil].
    + cbn [app]. apply kd_ch_prim; [lia | apply kf_ch_nil].
Qed.

(* ------------------------------------------------------------------ the begins: paid by the line *)
Lemma kd_seen : forall H ka l j ha ks,
  21 * nsec_tr (fst (fst (seen_tr H ka l j ha ks))) <= Z.of_nat (length l) + 1.
Proof.
  intros H ka l j ha ks. unfold seen_tr.
  destruct (gesture l) as [[[|] x]|] eqn:Eg.
  - destruct (index_of x H); cbn [fst].
    + rewrite nsec_tr_nil. lia.
    + destruct (gesture_begin l x Eg) as [Ex Eb]. pose proof (begin_line_len l Eb) as L20.
      unfold zlen in Ex, L20.
      pose proof (kd_sec ((Z.of_nat (length H) + 1) * 8)) as S1.
      pose proof (kd_sec (Z.of_nat (length x) + 1)) as S2.
      destruct (ka =? 0); cbv beta iota; kd_ns; lia.
  - destruct (index_of x H); cbn [fst]; kd_ns; lia.
  - cbn [fst]. rewrite nsec_tr_nil. lia.
Qed.

(* the relayed lines of one round: g_out's chain, and the begins paid by the lines' bytes with their NULs *)
Lemma kd_lines : forall ls live mx no cap H ka j o ha ks,
  21 * nsec_tr (fst (fst (lines_run live mx no cap H ka ls j o ha ks))) + 21 * kf_lg cap <=
    21 * kf_lg (fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks))))) +
    Z.of_nat (length (with_nul ls)) /\
  fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))) <=
    Z.max cap (W_contract.tr_max (fst (fst (lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks.
  - cbn [lines_run fst snd]. rewrite nsec_tr_nil, kd_tm_nil. change (with_nul []) with (@nil Z).
    cbn [length]. lia.
  - cbn [lines_run fst snd]. rewrite !nsec_tr_app, !kf_tm_app.
    match goal with |- context [send_line_tr live mx no cap ?len ?jj ?oo] =>
      destruct (kf_send live mx no cap len jj oo) as [S1 S2] end.
    match goal with |- context [seen_tr H ka l ?jj ?hh ?kk] =>
      pose proof (kd_seen H ka l jj hh kk) as SN end.
    match goal with |- context [lines_run live mx ?a1 ?a2 ?a3 ?a4 r ?a5 ?a6 ?a7 ?a8] =>
      destruct (IH live mx a1 a2 a3 a4 a5 a6 a7 a8) as [I1 I2] end.
    rewrite RelayCap.with_nul_cons_len. split; lia.
Qed.

(* ------------------------------------------------------------------ bytes: chunk and the reference splitter *)
Lemma kd_scan : forall d skip acc,
  Z.of_nat (length (with_nul (snd (scan skip acc d)))) + Z.of_nat (length (snd (fst (scan skip acc d)))) <=
  Z.of_nat (length acc) + Z.of_nat (length d).
Proof.
  induction d as [|b d IH]; intros skip acc.
  - cbn [scan fst snd]. change (with_nul []) with (@nil Z). cbn [length]. lia.
  - cbn [scan]. destruct (Z.eqb b 0).
    + pose proof (IH false []) as I. revert I. destruct (scan false [] d) as [[sk r] ls]. intros I.
      cbn [fst snd length] in I |- *.
      destruct (skip || Nat.ltb LINE_LIMIT (length acc)); [lia|].
      rewrite RelayCap.with_nul_cons_len. lia.
    + pose proof (IH skip (acc ++ [b])) as I. rewrite length_app in I. cbn [length] in I |- *. lia.
Qed.

Lemma kd_chunk : forall u skip d,
  Z.of_nat (length (with_nul (snd (chunk u skip d)))) + Z.of_nat (length (fst (fst (chunk u skip d)))) <=
  Z.of_nat (length u) + Z.of_nat (length d).
Proof.
  intros u skip d. unfold chunk. pose proof (kd_scan d skip u) as I.
  revert I. destruct (scan skip u d) as [[sk r] ls]. intros I. cbn [fst snd] in I |- *.
  destruct (Nat.ltb LINE_LIMIT (length r)); cbn [fst snd length]; lia.
Qed.

(* the reference splitter's partial line stays at most LINE_LIMIT while it is kept *)
Definition kd_rok (st : lstate) : Prop := ls_k st = false -> zlen (ls_w st) <= 6000.

Lemma kd_feed_rok : forall d st, kd_rok st -> kd_rok (feed st d).
Proof.
  induction d as [|b d IH]; intros st H; [exact H|]. rewrite feed_cons. apply IH. unfold kd_rok in *.
  destruct (Z.eqb_spec b 0) as [->|Hb].
  - rewrite step_zero. cbn [fst ls_w]. intros _. unfold zlen. cbn [length]. lia.
  - destruct (ls_k st) eqn:Ek.
    + rewrite (step_nz_k st b Hb Ek). cbn [fst]. rewrite Ek. intros E. discriminate E.
    + destruct (Nat.eq_dec (length (ls_w st)) LINE_LIMIT) as [He|He].
      * rewrite (step_nz_full st b Hb Ek He). cbn [fst ls_k]. intros E. discriminate E.
      * rewrite (step_nz_add st b Hb Ek He). cbn [fst ls_w]. intros _. unfold zlen in *. rewrite length_app.
        cbn [length]. specialize (H eq_refl). pose proof (LL_ne _ He) as N. lia.
Qed.

(* ------------------------------------------------------------------ drain_run *)
(* the three chains' potential: the relay buffer, g_out, the expected vector in bytes *)
Definition kd_pot (s : dstate) : Z := kf_lg (ds_cap s) + kf_lg (ds_ocap s) + kf_lg (16 * ds_ecap s).

Lemma kd_run : forall f lv mx s j a, 0 <= ds_off s -> kd_rok (ds_ref s) ->
  21 * nsec_tr (fst (drain_run f lv mx s j a)) + zlen (ds_u (fst (snd (drain_run f lv mx s j a)))) +
    zlen (d3str (fst (snd (drain_run f lv mx s j a)))) + 21 * kd_pot s <=
  zlen (ds_u s) + zlen (d3str s) + 21 * kd_pot (fst (snd (drain_run f lv mx s j a))) /\
  ds_cap (fst (snd (drain_run f lv mx s j a))) <= Z.max (ds_cap s) (W_contract.tr_max (fst (drain_run f lv mx s j a))) /\
  ds_ocap (fst (snd (drain_run f lv mx s j a))) <=
    Z.max (ds_ocap s) (W_contract.tr_max (fst (drain_run f lv mx s j a))) /\
  16 * ds_ecap (fst (snd (drain_run f lv mx s j a))) <=
    Z.max (16 * ds_ecap s) (W_contract.tr_max (fst (drain_run f lv mx s j a))).
Proof.
  induction f as [|f IH]; intros lv mx s j a Ho Hr.
  { cbn [drain_run fst snd]. rewrite nsec_tr_nil, kd_tm_nil. lia. }
  assert (KP : kd_pot s = kf_lg (ds_cap s) + kf_lg (ds_ocap s) + kf_lg (16 * ds_ecap s)) by reflexivity.
  cbn [drain_run]. cbv zeta.
  pose proof (kd_grow (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)) as G.
  destruct (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)) as [tg [cap1 b1]] eqn:Eg.
  try rewrite Eg in G. cbn [fst snd] in G |- *. destruct G as [G1 G2].
  destruct (ds_eintr s).
  - cbn [fst snd].
    match goal with |- context [drain_run f lv mx ?s1 ?j1 ?a1] =>
      destruct (IH lv mx s1 j1 a1 Ho Hr) as (I1 & I2 & I3 & I4);
      change (kd_pot s1) with (kf_lg cap1 + kf_lg (ds_ocap s) + kf_lg (16 * ds_ecap s)) in I1;
      change (zlen (ds_u s1)) with (zlen (ds_u s)) in I1;
      change (d3str s1) with (d3str s) in I1;
      change (ds_cap s1) with cap1 in I2;
      change (ds_ocap s1) with (ds_ocap s) in I3;
      change (ds_ecap s1) with (ds_ecap s) in I4
    end.
    rewrite nsec_tr_app, kf_tm_app, KP.
    split; [clear G2 I2 I3 I4; lia|].
    split; [clear I3 I4; lia|]. split; [clear G2 I2 I4; lia | clear G2 I2 I3; lia].
  - destruct (ds_pend s) as [|r0 rs] eqn:Ep.
    + cbn [fst snd]. unfold kd_pot, d3str. rewrite Ep. cbn [ds_pend ds_off ds_u ds_cap ds_ocap ds_ecap]. lia.
    + match goal with |- context [if Z.min ?x ?y <=? 0 then _ else _] => set (n := Z.min x y) in * end.
      destruct (Z.leb_spec n 0) as [En|En].
      * cbn [fst snd]. unfold kd_pot, d3str. rewrite Ep. cbn [ds_pend ds_off ds_u ds_cap ds_ocap ds_ecap]. lia.
      * assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) in *.
        pose proof (kd_chunk (ds_u s) (ds_skip s) d) as CH.
        destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:Ech.
        try rewrite Ech in CH. cbn [fst snd] in CH. cbv beta iota.
        match goal with |- context [pushes_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6] =>
          pose proof (kd_pushes a3 a1 a2 a4 a5 a6 (lines_len6 d (ds_ref s) Hr)) as PU;
          destruct (pushes_run a1 a2 a3 a4 a5 a6) as [[tp cp] ap] eqn:Epu
        end.
        try rewrite Epu in PU. cbn [fst snd] in PU |- *. destruct PU as [P1 P2].
        match goal with |- context [lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o3 ?h3 ?k3] =>
          pose proof (kd_lines rl lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o3 h3 k3) as [L1 L2];
          destruct (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o3 h3 k3)
            as [[tl [[oc' H'] ka']] [[o' ha'] ks']] eqn:Elr
        end.
        try rewrite Elr in L1. try rewrite Elr in L2. cbn [fst snd] in L1, L2. cbv beta iota. cbn [fst snd].
        match goal with |- context [drain_run f lv mx ?s2 ?j4 ?a2] =>
          assert (HO2 : 0 <= ds_off s2)
            by (cbn [ds_off]; destruct (ds_off s + n =? Z.of_nat (length r0)); lia);
          assert (HR2 : kd_rok (ds_ref s2)) by (cbn [ds_ref]; apply kd_feed_rok; exact Hr);
          destruct (IH lv mx s2 j4 a2 HO2 HR2) as (I1 & I2 & I3 & I4);
          assert (SE : d3str s = d ++ d3str s2)
            by (unfold d; apply (round_str s s2 r0 rs n Ep Ho En Hn1); reflexivity);
          assert (LSE : zlen (d3str s) = zlen d + zlen (d3str s2))
            by (rewrite SE; unfold zlen; rewrite length_app; lia);
          change (kd_pot s2) with (kf_lg cap1 + kf_lg oc' + kf_lg (16 * cp)) in I1;
          change (ds_u s2) with u' in I1;
          change (ds_cap s2) with cap1 in I2;
          change (ds_ocap s2) with oc' in I3;
          change (ds_ecap s2) with cp in I4
        end.
        clear SE. rewrite !nsec_tr_app, !kf_tm_app, kd_td_ns, kd_td_tm, KP. unfold zlen in *.
        split; [clear G2 P2 L2 I2 I3 I4; lia|].
        split; [clear P2 L2 I3 I4; lia|].
        split; [clear G2 P2 I2 I4; lia | clear G2 L2 I2 I3; lia].
Qed.

(* ------------------------------------------------------------------ one drain *)
Lemma kd_init_rok : forall NO CAP e h, (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  kd_rok (ds_ref (drain_init NO CAP e h)).
Proof.
  intros NO CAP e h H Hk. change ((hs_overlong h =? 1) = false) in Hk.
  cbn [ds_ref drain_init hs_state ls_w]. unfold zlen, bzs. rewrite length_map. apply H. apply Z.eqb_neq. exact Hk.
Qed.

Lemma kd_drain : forall live mx no cap e h j a,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  21 * nsec_tr (drain_tr live mx no cap e h j a) + Z.of_nat (length (ds_u (drain_fin live mx no cap e h))) +
    21 * (kf_lg (re_cap e) + kf_lg cap + kf_lg (16 * hl_cap (hs_expected h))) <=
  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) +
    21 * (kf_lg (ds_cap (drain_fin live mx no cap e h)) + kf_lg (ds_ocap (drain_fin live mx no cap e h)) +
          kf_lg (16 * ds_ecap (drain_fin live mx no cap e h))) /\
  ds_cap (drain_fin live mx no cap e h) <= Z.max (re_cap e) (W_contract.tr_max (drain_tr live mx no cap e h j a)) /\
  ds_ocap (drain_fin live mx no cap e h) <= Z.max cap (W_contract.tr_max (drain_tr live mx no cap e h j a)) /\
  16 * ds_ecap (drain_fin live mx no cap e h) <=
    Z.max (16 * hl_cap (hs_expected h)) (W_contract.tr_max (drain_tr live mx no cap e h j a)).
Proof.
  intros live mx no cap e h j a Ho HW. unfold drain_tr, drain_fin, drain_go.
  rewrite (drain_st live mx (S (S (length (pending_stream h)))) (drain_init no cap e h) 0 dadr0 j a).
  destruct (kd_run (S (S (length (pending_stream h)))) live mx (drain_init no cap e h) j a Ho
              (kd_init_rok no cap e h HW)) as (I1 & I2 & I3 & I4).
  rewrite d3str_init in I1.
  change (ds_u (drain_init no cap e h)) with (bzs (re_U e)) in I1.
  change (kd_pot (drain_init no cap e h)) with (kf_lg (re_cap e) + kf_lg cap + kf_lg (16 * hl_cap (hs_expected h))) in I1.
  unfold kd_pot in I1. unfold zlen, bzs in I1. rewrite !length_map in I1.
  split; [lia|]. split; [exact I2|]. split; [exact I3 | exact I4].
Qed.

(* the telescoping form: for any liveness, base j and addresses a *)
Lemma kf_drain_pot : forall live mx no cap e h j a,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  21 * nsec_tr (drain_tr live mx no cap e h j a) + Z.of_nat (length (ds_u (drain_fin live mx no cap e h))) +
    21 * (kf_lg (re_cap e) + kf_lg cap + kf_lg (16 * hl_cap (hs_expected h))) <=
  Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) +
    21 * (kf_lg (ds_cap (drain_fin live mx no cap e h)) + kf_lg (ds_ocap (drain_fin live mx no cap e h)) +
          kf_lg (16 * ds_ecap (drain_fin live mx no cap e h))).
Proof. intros live mx no cap e h j a Ho HW. exact (proj1 (kd_drain live mx no cap e h j a Ho HW)). Qed.

(* each chain ends at its start size or at most the trace's largest request *)
Lemma kf_drain_caps : forall live mx no cap e h j a,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  ds_cap (drain_fin live mx no cap e h) <= Z.max (re_cap e) (W_contract.tr_max (drain_tr live mx no cap e h j a)) /\
  ds_ocap (drain_fin live mx no cap e h) <= Z.max cap (W_contract.tr_max (drain_tr live mx no cap e h j a)) /\
  16 * ds_ecap (drain_fin live mx no cap e h) <=
    Z.max (16 * hl_cap (hs_expected h)) (W_contract.tr_max (drain_tr live mx no cap e h j a)).
Proof. intros live mx no cap e h j a Ho HW. exact (proj2 (kd_drain live mx no cap e h j a Ho HW)). Qed.

(* ------------------------------------------------------------------ the per-drain constant *)
Definition KC_dr : Z := 30.

Lemma KC_dr_nonneg : 0 <= KC_dr.
Proof. unfold KC_dr. lia. Qed.

Lemma kd_lg_small : forall x, x <= 16384 -> kf_lg x = 0.
Proof.
  intros x H. pose proof (kf_lg_nonneg x). pose proof (kf_lg_mono x 16384 H).
  assert (E : kf_lg 16384 = 0) by (vm_compute; reflexivity). lia.
Qed.

Lemma kd_gain : forall x0 x1 T, x1 <= Z.max x0 T -> T < 2 ^ 30 -> kf_lg x1 <= kf_lg x0 + 15.
Proof.
  intros x0 x1 T H HT. pose proof (kf_lg_nonneg x0) as N.
  destruct (Z.max_spec x0 T) as [[_ E]|[_ E]]; rewrite E in H.
  - assert (H30 : x1 <= 2 ^ 30) by lia. pose proof (kf_lg_le15 x1 H30). lia.
  - pose proof (kf_lg_mono x1 x0 H). lia.
Qed.

Lemma kf_drain_tr : forall live mx no cap e h j a,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) -> Z.of_nat (length (re_U e)) <= 6000 ->
  W_contract.tr_max (drain_tr live mx no cap e h j a) < 2 ^ 30 ->
  21 * nsec_tr (drain_tr live mx no cap e h j a) + Z.of_nat (length (ds_u (drain_fin live mx no cap e h))) <=
  21 * KC_dr + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
Proof.
  intros live mx no cap e h j a Ho HW HC HU HM.
  destruct (kd_drain live mx no cap e h j a Ho HW) as (P & _ & C2 & C3).
  pose proof (kd_gain _ _ _ C2 HM) as D2. pose proof (kd_gain _ _ _ C3 HM) as D3.
  assert (HU' : zlen (ds_u (drain_init no cap e h)) <= 6000)
    by (cbn [ds_u drain_init]; unfold zlen, bzs; rewrite length_map; exact HU).
  pose proof (ReKhMax.rkm_drain_cap_set (S (S (length (pending_stream h)))) live mx (drain_init no cap e h) 0 dadr0
                HC HU') as CS.
  change (fst (snd (drain_run (S (S (length (pending_stream h)))) live mx (drain_init no cap e h) 0 dadr0)))
    with (drain_fin live mx no cap e h) in CS.
  assert (B1 : kf_lg (ds_cap (drain_fin live mx no cap e h)) = 0) by (apply kd_lg_small; lia).
  assert (B0 : kf_lg (re_cap e) = 0) by (apply kd_lg_small; lia).
  unfold KC_dr. clear C2 C3. lia.
Qed.

(* W_contract.dr_tr is drain_tr at live := dr_live c h, j := 0, a := dadr0 *)
Lemma kf_dr : forall c mx no cap e h,
  0 <= hs_off h -> (hs_overlong h <> 1 -> Z.of_nat (length (hs_W h)) <= 6000) ->
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) -> Z.of_nat (length (re_U e)) <= 6000 ->
  W_contract.tr_max (W_contract.dr_tr c mx no cap e h) < 2 ^ 30 ->
  21 * nsec_tr (W_contract.dr_tr c mx no cap e h) +
    Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))) <=
  21 * KC_dr + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
Proof. intros c mx no cap e h. exact (kf_drain_tr (W_contract.dr_live c h) mx no cap e h 0 dadr0). Qed.

(* ------------------------------------------------------------------ the call site supplies the premises *)
Section pre.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : W_kit.PAImg W_listing.fr_prog_listing}.
Variable B : YG0f.asyms.

(* dr_spec_x's asrc_at (lib/B/W_rep.v:107-111; APARTIAL = 6000 at :61): the offset clause and the partial buffer's
   6,000 bytes *)
Lemma kf_dr_src : forall ly S W mem HA h, W_rep.asrc_at B ly S W mem HA h ->
  0 <= hs_off h /\ Z.of_nat (length (hs_W h)) <= 6000.
Proof.
  intros ly S W mem HA h Hs.
  destruct Hs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HO & _ & _ & _ & HJ & _).
  unfold W_rep.APARTIAL in HJ. split.
  - destruct HO as [[_ E]|(r & rs & _ & E & _)]; lia.
  - unfold hs_W. rewrite length_firstn. lia.
Qed.

(* dr_spec_x's aentry_ok (lib/B/W_rep.v:127-128): the buffer's three sizes and the kept bytes *)
Lemma kf_dr_ent : forall ly S W mem e, W_rep.aentry_ok B ly S W mem e ->
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\ Z.of_nat (length (re_U e)) <= 6000.
Proof.
  intros ly S W mem e He.
  destruct He as (_ & _ & _ & _ & _ & HC & HU & HU6 & _).
  unfold W_rep.APARTIAL in HU6. split; [exact HC | lia].
Qed.

(* kf_dr from dr_spec_x's own premises (lib/B/W_contract_x.v:756-778: aentry_ok :764, asrc_at :765, tr_max (dr_tr ..)
   < MMAX :772), and MMAX <= 2 ^ 30 (CfParamsReplyB.reply_HMMAX at fr_MMAX, lib/B/CfParamsReplyB.v:129) *)
Lemma kf_dr_at : forall ly S W mem HA c mx no cap e h MMAX,
  W_rep.asrc_at B ly S W mem HA h -> W_rep.aentry_ok B ly S W mem e ->
  W_contract.tr_max (W_contract.dr_tr c mx no cap e h) < MMAX -> MMAX <= 2 ^ 30 ->
  21 * nsec_tr (W_contract.dr_tr c mx no cap e h) +
    Z.of_nat (length (drain_b_c.ds_u (W_contract.dr_fin c mx no cap e h))) <=
  21 * KC_dr + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)).
Proof.
  intros ly S W mem HA c mx no cap e h MMAX Hs He HM HX.
  destruct (kf_dr_src ly S W mem HA h Hs) as [Ho HW]. destruct (kf_dr_ent ly S W mem e He) as [HC HU].
  apply kf_dr; [exact Ho | intros _; exact HW | exact HC | exact HU | lia].
Qed.
End pre.
