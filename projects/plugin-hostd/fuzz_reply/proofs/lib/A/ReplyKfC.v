(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyKfC.v, with its module paths changed; 1 of its 341 lines of code is new or changed and 1 line of the source is left out. *)
(* The secondary-request counts of the harness's growing arrays, over the plain model's request traces, at a meter
   that charges 1 for a secondary request (a malloc or realloc to at least 64,513 bytes, Psec) and 0 for everything
   else.  rule 24: no function proved (kind: segment lemma).

   POTENTIALS, NOT COUNTERS.  A count of the secondary growths so far does not compose across calls; a potential
   of the CURRENT capacity does.  kf_psi_v c = max 10 (log2 c) for a list vector (list_push grows 16 * CAP bytes to
   32 * CAP, secondary iff CAP >= 2,017, and then log2 CAP >= 10) and kf_psi_o c = max 14 (log2 c) for g_out
   (send_line grows it to 2 * (no + n) > 2 * cap, secondary iff that is >= 64,513, and then its log2 is >= 15).
   Each secondary growth raises the potential by at least 1 and a primary growth never lowers it, so the count of a
   trace is at most the potential's rise over it; the potential of a capacity under the bound is at most a constant
   above its floor, so the count per trace is a constant: 15 for a vector whose cap stays under 2 ^ 26, 12 for g_out
   (whose cap persists across ops and calls, so the 12 holds for a whole run).  The run sum checks the constant
   KF_C = 60 (and the per-op constant KF_KC = 256) against the 2 ^ 23 budget over 4 calls of at most OPS_MAX ops.

   The meter is the Section variable MT with the two equations KF_MAL / KF_FREE.

   Sources:
     lib/A/W_contract.v:944-950 tr_cost; :366-367 lp_cost; :786 sl_cap; :789-799 sl_cost_run / sl_cost;
       :1514-1516 ge_cap / ge_cost;
     lib/A/ReplyCnt.v:30 Psec; lib/A/ReplyLSCntL.v:74 is_sec_iff;
     lib/Prog/ListTr.v:50-52 list_push_tra; lib/Prog/drain_b_c.v:58 push_cap, :109-118 pushes_run;
     lib/Prog/send_line_b_c.v:27-38 sl_run, :42-47 send_line_tr / send_line_cap;
     lib/A/W_LLVMFuzzerTestOneInput_cut.v:104 OPS_MAX, :181 CAPOUT_MAX;
     lib/Reusable/YC5d.v:17-21 ameter_ops. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT ListTr drain_b_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt ReplyLSCntL.
Import ListNotations.
Local Open Scope Z_scope.

Section kf.
Variable MT : ameter_ops.
Hypothesis KF_MAL : forall n, mo_malloc MT n = if Psec n then 1 else 0.
Hypothesis KF_FREE : mo_free MT = 0.

(* ================================================================== the potentials *)
Definition kf_psi_v (c : Z) : Z := Z.max 10 (Z.log2 c).
Definition kf_psi_o (c : Z) : Z := Z.max 14 (Z.log2 c).

(* ================================================================== helpers: log2, Psec, the meter on traces *)
Lemma kf_log2_ge : forall k c, 0 <= k -> 2 ^ k <= c -> k <= Z.log2 c.
Proof.
  intros k c Hk H. pose proof (Z.log2_le_mono _ _ H) as H1. rewrite Z.log2_pow2 in H1 by exact Hk. exact H1.
Qed.

Lemma kf_log2_lt : forall k c, 0 < c -> c < 2 ^ k -> Z.log2 c < k.
Proof. intros k c Hc H. destruct (Z.log2_lt_pow2 c k Hc) as [H1 _]. exact (H1 H). Qed.

Lemma kf_log2_mul2 : forall c, 0 < c -> Z.log2 (c * 2) = Z.log2 c + 1.
Proof. intros c Hc. rewrite Z.mul_comm, Z.log2_double by exact Hc. lia. Qed.

Lemma kf_b01 : forall b : bool, 0 <= (if b then 1 else 0) <= 1.
Proof. intros [|]; cbv beta iota; lia. Qed.

Lemma kf_psec_small : forall n, 0 <= n < 64513 -> Psec n = false.
Proof. intros n Hn. rewrite (is_sec_iff n) by lia. apply Z.leb_gt. lia. Qed.

Lemma kf_cost_nil : forall {P : Type}, tr_cost MT (@nil (RelayRunT.rev P)) = 0.
Proof. reflexivity. Qed.

Lemma kf_cost_app : forall {P : Type} (a b : list (RelayRunT.rev P)),
  tr_cost MT (a ++ b) = tr_cost MT a + tr_cost MT b.
Proof.
  intros P a b. induction a as [|e a IH].
  - reflexivity.
  - unfold tr_cost in *. cbn [app fold_right]. rewrite IH. lia.
Qed.

Lemma kf_cost_cons : forall {P : Type} (e : RelayRunT.rev P) tr, tr_cost MT (e :: tr) = tr_cost MT [e] + tr_cost MT tr.
Proof. intros P e tr. exact (kf_cost_app [e] tr). Qed.

Lemma kf_cost_malloc : forall {P : Type} n, tr_cost MT [@RelayRunT.RMalloc P n] = if Psec n then 1 else 0.
Proof.
  intros P n. unfold tr_cost. cbn [fold_right]. rewrite KF_MAL, KF_FREE. destruct (Psec n); reflexivity.
Qed.

Lemma kf_cost_realloc : forall {P : Type} k n (a : RelayRunT.addr P),
  tr_cost MT [RelayRunT.RRealloc k n a] = if Psec n then 1 else 0.
Proof.
  intros P k n a. unfold tr_cost. cbn [fold_right]. rewrite KF_MAL, KF_FREE. destruct (Psec n); reflexivity.
Qed.

Lemma kf_cost_grow : forall {P : Type} (cap c : Z) (o : RelayRunT.addr P),
  tr_cost MT [if cap =? 0 then RelayRunT.RMalloc c else RelayRunT.RRealloc cap c o] = if Psec c then 1 else 0.
Proof.
  intros P cap c o. destruct (cap =? 0); cbv beta iota; [apply kf_cost_malloc | apply kf_cost_realloc].
Qed.

(* ================================================================== (1) the list vector *)
(* the vector's doubling: the potential never falls, and rises by 1 when the growth (32 * c bytes) is secondary *)
Lemma kf_psi_v_double : forall c, 0 < c ->
  kf_psi_v c <= kf_psi_v (c * 2) /\ (if Psec (32 * c) then 1 else 0) <= kf_psi_v (c * 2) - kf_psi_v c.
Proof.
  intros c Hc. assert (Hm2 : Z.log2 (c * 2) = Z.log2 c + 1) by (apply kf_log2_mul2; lia).
  rewrite (is_sec_iff (32 * c)) by lia. unfold kf_psi_v.
  destruct (Z.leb_spec 64513 (32 * c)) as [H|H]; cbv beta iota.
  - assert (H10 : 10 <= Z.log2 c) by (apply kf_log2_ge; [lia | change (2 ^ 10) with 1024; lia]). lia.
  - lia.
Qed.

Lemma kf_psi_v_08 : kf_psi_v 8 - kf_psi_v 0 = 0.
Proof. unfold kf_psi_v. change (Z.log2 8) with 3. change (Z.log2 0) with 0. lia. Qed.

Lemma kf_push_cap_nonneg : forall N CAP, 0 <= CAP -> 0 <= drain_b_c.push_cap N CAP.
Proof.
  intros N CAP HC. unfold drain_b_c.push_cap.
  destruct (N =? CAP); destruct (CAP =? 0); cbv beta iota; lia.
Qed.

(* one push: the vector growth (32 * CAP secondary iff CAP >= 2017, so log2 CAP >= 10) plus the text block *)
Lemma kf_list_push : forall v N CAP n, 0 <= CAP -> 0 <= n ->
  tr_cost MT (ListTr.list_push_tra v N CAP n)
    <= kf_psi_v (drain_b_c.push_cap N CAP) - kf_psi_v CAP + (if Psec (n + 1) then 1 else 0).
Proof.
  intros v N CAP n HC Hn. unfold ListTr.list_push_tra, drain_b_c.push_cap.
  rewrite kf_cost_app, kf_cost_malloc.
  destruct (N =? CAP); cbv beta iota.
  - destruct (Z.eqb_spec CAP 0) as [E0|E0]; cbv beta iota.
    + subst CAP. rewrite kf_cost_malloc, (kf_psec_small 128) by lia. cbv beta iota.
      pose proof kf_psi_v_08. lia.
    + rewrite kf_cost_realloc. destruct (kf_psi_v_double CAP ltac:(lia)) as [_ H]. lia.
  - rewrite kf_cost_nil. lia.
Qed.

Lemma kf_psi_v_push : forall N CAP, 0 <= CAP -> kf_psi_v CAP <= kf_psi_v (drain_b_c.push_cap N CAP).
Proof.
  intros N CAP HC. unfold drain_b_c.push_cap.
  destruct (N =? CAP); cbv beta iota; [|lia].
  destruct (Z.eqb_spec CAP 0) as [E0|E0]; cbv beta iota.
  - subst CAP. pose proof kf_psi_v_08. lia.
  - exact (proj1 (kf_psi_v_double CAP ltac:(lia))).
Qed.

(* reference_feed's pushes (drain): the texts' term counts lines of at least 64,512 bytes *)
Lemma kf_pushes_run : forall n cap ls j v rs, 0 <= cap ->
  tr_cost MT (fst (fst (drain_b_c.pushes_run n cap ls j v rs)))
    <= kf_psi_v (snd (fst (drain_b_c.pushes_run n cap ls j v rs))) - kf_psi_v cap
       + Z.of_nat (length (List.filter (fun l => Psec (Z.of_nat (length l) + 1)) ls)).
Proof.
  intros n cap ls. revert n cap. induction ls as [|l ls IH]; intros n cap j v rs Hc;
    cbn [drain_b_c.pushes_run fst snd].
  - rewrite kf_cost_nil. cbn [List.filter length]. lia.
  - rewrite kf_cost_app.
    match goal with |- context [drain_b_c.pushes_run (n + 1) ?c ls ?j' ?v' ?rs'] =>
      pose proof (IH (n + 1) c j' v' rs' (kf_push_cap_nonneg n cap Hc)) as H2 end.
    pose proof (kf_list_push v n cap (Z.of_nat (length l)) Hc (Nat2Z.is_nonneg _)) as H1.
    revert H1. cbn [List.filter]. destruct (Psec (Z.of_nat (length l) + 1)); cbn [length]; intros H1; lia.
Qed.

(* the range: any cap below 2^26 *)
Lemma kf_vec_range : forall c c', 0 <= c -> c' < 2 ^ 26 -> kf_psi_v c' - kf_psi_v c <= 15.
Proof.
  intros c c' Hc Hc'. unfold kf_psi_v.
  destruct (Z.leb_spec c' 0) as [H|H].
  - rewrite (Z.log2_nonpos c' H). lia.
  - assert (Z.log2 c' < 26) by (apply kf_log2_lt; [lia | exact Hc']). lia.
Qed.

(* ================================================================== (2) g_out *)
(* a growth to m * 2 from cap < m: the potential never falls, and rises by 1 when the growth is secondary *)
Lemma kf_psi_o_grow : forall cap m, 0 <= cap -> cap < m ->
  (if Psec (m * 2) then 1 else 0) <= kf_psi_o (m * 2) - kf_psi_o cap.
Proof.
  intros cap m Hc Hm.
  assert (Hm2 : Z.log2 (m * 2) = Z.log2 m + 1) by (apply kf_log2_mul2; lia).
  assert (Hmono : Z.log2 cap <= Z.log2 m) by (apply Z.log2_le_mono; lia).
  rewrite (is_sec_iff (m * 2)) by lia. unfold kf_psi_o.
  destruct (Z.leb_spec 64513 (m * 2)) as [H|H]; cbv beta iota.
  - assert (H15 : 15 <= Z.log2 (m * 2)) by (apply kf_log2_ge; [lia | change (2 ^ 15) with 32768; lia]). lia.
  - lia.
Qed.

(* sl_run's final capacity does not depend on the addresses *)
Lemma kf_sl_run_cap_addr : forall f mx no cap rem j o j' o',
  fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [send_line_b_c.sl_run]; [reflexivity|].
  destruct (rem <=? 0); cbn [fst snd]; [reflexivity|].
  match goal with |- context [if cap <? ?m then _ else _] => destruct (cap <? m) end; cbn [fst snd]; apply IH.
Qed.

(* the invariant is 0 <= cap only: n may be mx, which may be negative *)
Lemma kf_sl_run_cost : forall f mx no cap rem j o, 0 <= cap ->
  tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o))
    <= kf_psi_o (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))) - kf_psi_o cap.
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. rewrite kf_cost_nil. lia.
  - destruct (rem <=? 0); cbn [fst snd].
    + rewrite kf_cost_nil. lia.
    + match goal with |- context [rem - ?x] => remember x as n eqn:En end.
      destruct (Z.ltb_spec cap (no + n)) as [Hg|Hg]; cbn [fst snd].
      * rewrite kf_cost_cons, kf_cost_grow.
        pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as H1.
        pose proof (kf_psi_o_grow cap (no + n) Hc Hg) as H2. lia.
      * apply IH. exact Hc.
Qed.

Lemma kf_sl_run_cap_mono : forall f mx no cap rem j o, 0 <= cap ->
  cap <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. lia.
  - destruct (rem <=? 0); cbn [fst snd]; [lia|].
    match goal with |- context [rem - ?x] => remember x as n eqn:En end.
    destruct (Z.ltb_spec cap (no + n)) as [Hg|Hg]; cbn [fst snd].
    + pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as H1. lia.
    + apply IH. exact Hc.
Qed.

Lemma kf_sl_run : forall f mx no cap rem j o, 0 <= cap -> 0 <= no ->
  tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o))
    <= kf_psi_o (fst (snd (send_line_b_c.sl_run f mx no cap rem j o))) - kf_psi_o cap.
Proof. intros f mx no cap rem j o Hc _. exact (kf_sl_run_cost f mx no cap rem j o Hc). Qed.

(* kf_send_line without its 0 <= NO premise *)
Lemma kf_send_line_gen : forall live mx NO CAP LEN j o, 0 <= CAP ->
  tr_cost MT (send_line_b_c.send_line_tr live mx NO CAP LEN j o)
    <= kf_psi_o (send_line_b_c.send_line_cap live mx NO CAP LEN) - kf_psi_o CAP.
Proof.
  intros live mx NO CAP LEN j o HC. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live.
  - rewrite (kf_sl_run_cap_addr _ _ _ _ _ _ _ j o). apply kf_sl_run_cost. exact HC.
  - rewrite kf_cost_nil. lia.
Qed.

Lemma kf_send_line : forall live mx NO CAP LEN j o, 0 <= CAP -> 0 <= NO ->
  tr_cost MT (send_line_b_c.send_line_tr live mx NO CAP LEN j o)
    <= kf_psi_o (send_line_b_c.send_line_cap live mx NO CAP LEN) - kf_psi_o CAP.
Proof. intros live mx NO CAP LEN j o HC _. exact (kf_send_line_gen live mx NO CAP LEN j o HC). Qed.

(* send_line_cap is monotone from a capacity 0 <= CAP.  The premise 0 <= CAP is needed: below,
   send_line_cap true (-10) 0 (-11) 1 = -20 < -11 (n = mx = -10, cap -11 < no + n = -10, growth to (no + n) * 2). *)
Lemma kf_send_line_cap_mono : forall live mx NO CAP LEN, 0 <= CAP -> CAP <= send_line_b_c.send_line_cap live mx NO CAP LEN.
Proof.
  intros live mx NO CAP LEN HC. unfold send_line_b_c.send_line_cap.
  destruct live; [apply kf_sl_run_cap_mono; exact HC | lia].
Qed.

Lemma kf_send_line_cap_mono_cex : send_line_b_c.send_line_cap true (-10) 0 (-11) 1 = -20.
Proof. reflexivity. Qed.

Lemma kf_send_line_cap_mono_false :
  ~ (forall live mx NO CAP LEN, CAP <= send_line_b_c.send_line_cap live mx NO CAP LEN).
Proof.
  intros H. pose proof (H true (-10) 0 (-11) 1) as H1. rewrite kf_send_line_cap_mono_cex in H1. lia.
Qed.

(* the range: g_capout <= CAPOUT_MAX = 133,953,540 < 2^27 *)
Lemma kf_out_range : forall c c', 0 <= c -> c' <= CAPOUT_MAX -> kf_psi_o c' - kf_psi_o c <= 12.
Proof.
  intros c c' Hc Hc'. unfold CAPOUT_MAX, OPS_MAX in Hc'. unfold kf_psi_o.
  destruct (Z.leb_spec c' 0) as [H|H].
  - rewrite (Z.log2_nonpos c' H). lia.
  - assert (Z.log2 c' < 27) by (apply kf_log2_lt; [lia | change (2 ^ 27) with 134217728; lia]). lia.
Qed.

(* ================================================================== (3) the constant and the run sum *)
Definition KF_C : Z := 60.
(* 3 lists x 15 doublings + 12 g_out growths + 1 write text block + 1 event copy *)
Lemma kf_C_le : 3 * 15 + 12 + 1 + 1 <= KF_C.
Proof. unfold KF_C. lia. Qed.

(* one run = 4 calls; per call D_i <= (OPS_MAX - 1) * 65,535 drained bytes and t_i <= OPS_MAX ops *)
Lemma kf_run_sum : forall D t, 0 <= D <= 4 * ((OPS_MAX - 1) * 65535) -> 0 <= t <= 4 * OPS_MAX ->
  D / 21 + KF_C * t <= 2 ^ 23.
Proof.
  intros D t HD Ht. unfold KF_C. unfold OPS_MAX in HD, Ht.
  assert (D / 21 <= 6378740) by (apply Z.div_le_upper_bound; lia).
  change (2 ^ 23) with 8388608. lia.
Qed.

Lemma kf_run_sum4 : forall D1 D2 D3 D4 t1 t2 t3 t4,
  0 <= D1 <= (OPS_MAX - 1) * 65535 -> 0 <= D2 <= (OPS_MAX - 1) * 65535 ->
  0 <= D3 <= (OPS_MAX - 1) * 65535 -> 0 <= D4 <= (OPS_MAX - 1) * 65535 ->
  0 <= t1 <= OPS_MAX -> 0 <= t2 <= OPS_MAX -> 0 <= t3 <= OPS_MAX -> 0 <= t4 <= OPS_MAX ->
  (D1 / 21 + KF_C * t1) + (D2 / 21 + KF_C * t2) + (D3 / 21 + KF_C * t3) + (D4 / 21 + KF_C * t4) <= 2 ^ 23.
Proof.
  intros D1 D2 D3 D4 t1 t2 t3 t4 HD1 HD2 HD3 HD4 Ht1 Ht2 Ht3 Ht4. unfold KF_C.
  unfold OPS_MAX in HD1, HD2, HD3, HD4, Ht1, Ht2, Ht3, Ht4.
  assert (D1 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  assert (D2 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  assert (D3 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  assert (D4 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  change (2 ^ 23) with 8388608. lia.
Qed.

(* ================================================================== the vector's final cap, and per-trace constants *)
Lemma kf_push_cap_step : forall n cap, 0 <= n <= cap ->
  n + 1 <= drain_b_c.push_cap n cap /\ drain_b_c.push_cap n cap <= Z.max cap (Z.max 8 (2 * (n + 1))).
Proof.
  intros n cap H. unfold drain_b_c.push_cap.
  destruct (Z.eqb_spec n cap); destruct (Z.eqb_spec cap 0); cbv beta iota; lia.
Qed.

Lemma kf_pushes_cap_le : forall n cap ls j v rs, 0 <= n <= cap ->
  snd (fst (drain_b_c.pushes_run n cap ls j v rs)) <= Z.max cap (Z.max 8 (2 * (n + Z.of_nat (length ls)))).
Proof.
  intros n cap ls. revert n cap. induction ls as [|l ls IH]; intros n cap j v rs Hn;
    cbn [drain_b_c.pushes_run fst snd].
  - lia.
  - destruct (kf_push_cap_step n cap Hn) as [H1 H2].
    match goal with |- context [drain_b_c.pushes_run (n + 1) ?c ls ?j' ?v' ?rs'] =>
      pose proof (IH (n + 1) c j' v' rs' ltac:(lia)) as H3 end.
    cbn [length]. lia.
Qed.

Lemma kf_pushes_run_le : forall n cap ls j v rs, 0 <= cap ->
  snd (fst (drain_b_c.pushes_run n cap ls j v rs)) < 2 ^ 26 ->
  tr_cost MT (fst (fst (drain_b_c.pushes_run n cap ls j v rs)))
    <= 15 + Z.of_nat (length (List.filter (fun l => Psec (Z.of_nat (length l) + 1)) ls)).
Proof.
  intros n cap ls j v rs Hc Hlt.
  pose proof (kf_pushes_run n cap ls j v rs Hc) as H1.
  pose proof (kf_vec_range cap _ Hc Hlt) as H2. lia.
Qed.

Lemma kf_pushes_run_le_start : forall n cap ls j v rs, 0 <= n <= cap -> cap < 2 ^ 26 ->
  n + Z.of_nat (length ls) < 2 ^ 25 ->
  tr_cost MT (fst (fst (drain_b_c.pushes_run n cap ls j v rs)))
    <= 15 + Z.of_nat (length (List.filter (fun l => Psec (Z.of_nat (length l) + 1)) ls)).
Proof.
  intros n cap ls j v rs Hn Hc Hl.
  pose proof (kf_pushes_cap_le n cap ls j v rs Hn) as H.
  apply kf_pushes_run_le; [lia|].
  change (2 ^ 26) with 67108864 in Hc |- *. change (2 ^ 25) with 33554432 in Hl. lia.
Qed.

(* one push has at most one vector event: no premise is needed *)
Lemma kf_list_push_le : forall v N CAP n,
  tr_cost MT (ListTr.list_push_tra v N CAP n) <= 1 + (if Psec (n + 1) then 1 else 0).
Proof.
  intros v N CAP n. unfold ListTr.list_push_tra. rewrite kf_cost_app, kf_cost_malloc.
  pose proof (kf_b01 (Psec (n + 1))).
  destruct (N =? CAP); cbv beta iota.
  - destruct (CAP =? 0); cbv beta iota.
    + rewrite kf_cost_malloc. pose proof (kf_b01 (Psec 128)). lia.
    + rewrite kf_cost_realloc. pose proof (kf_b01 (Psec (32 * CAP))). lia.
  - rewrite kf_cost_nil. lia.
Qed.

Lemma kf_send_line_le : forall live mx NO CAP LEN j o, 0 <= CAP ->
  send_line_b_c.send_line_cap live mx NO CAP LEN <= CAPOUT_MAX ->
  tr_cost MT (send_line_b_c.send_line_tr live mx NO CAP LEN j o) <= 12.
Proof.
  intros live mx NO CAP LEN j o HC Hle.
  pose proof (kf_send_line_gen live mx NO CAP LEN j o HC) as H1.
  pose proof (kf_out_range CAP _ HC Hle) as H2. lia.
Qed.

(* ================================================================== the owner's per-op constant *)
Definition KF_KC : Z := 256.

Lemma kf_C_le_KC : KF_C <= KF_KC.
Proof. unfold KF_C, KF_KC. lia. Qed.

Lemma kf_run_sum_KC : forall D t, 0 <= D <= 4 * ((OPS_MAX - 1) * 65535) -> 0 <= t <= 4 * OPS_MAX ->
  D / 21 + KF_KC * t <= 2 ^ 23.
Proof.
  intros D t HD Ht. unfold KF_KC. unfold OPS_MAX in HD, Ht.
  assert (D / 21 <= 6378740) by (apply Z.div_le_upper_bound; lia).
  change (2 ^ 23) with 8388608. lia.
Qed.

Lemma kf_run_sum4_KC : forall D1 D2 D3 D4 t1 t2 t3 t4,
  0 <= D1 <= (OPS_MAX - 1) * 65535 -> 0 <= D2 <= (OPS_MAX - 1) * 65535 ->
  0 <= D3 <= (OPS_MAX - 1) * 65535 -> 0 <= D4 <= (OPS_MAX - 1) * 65535 ->
  0 <= t1 <= OPS_MAX -> 0 <= t2 <= OPS_MAX -> 0 <= t3 <= OPS_MAX -> 0 <= t4 <= OPS_MAX ->
  (D1 / 21 + KF_KC * t1) + (D2 / 21 + KF_KC * t2) + (D3 / 21 + KF_KC * t3) + (D4 / 21 + KF_KC * t4) <= 2 ^ 23.
Proof.
  intros D1 D2 D3 D4 t1 t2 t3 t4 HD1 HD2 HD3 HD4 Ht1 Ht2 Ht3 Ht4. unfold KF_KC.
  unfold OPS_MAX in HD1, HD2, HD3, HD4, Ht1, Ht2, Ht3, Ht4.
  assert (D1 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  assert (D2 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  assert (D3 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  assert (D4 / 21 <= 1594685) by (apply Z.div_le_upper_bound; lia).
  change (2 ^ 23) with 8388608. lia.
Qed.

(* ================================================================== the spec costs of W_contract.v *)
(* sl_cost_run charges exactly what sl_run's trace costs at this meter *)
Lemma kf_sl_cost_run_tr : forall f mx no cap rem j o,
  tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run MT f mx no cap rem.
Proof.
  intros f. induction f as [|f IH]; intros mx no cap rem j o; cbn [sl_cost_run send_line_b_c.sl_run].
  - cbn [fst]. reflexivity.
  - destruct (rem <=? 0); cbn [fst snd].
    + reflexivity.
    + match goal with |- context [rem - ?x] => remember x as n eqn:En end.
      destruct (cap <? no + n); cbn [fst snd].
      * rewrite kf_cost_cons, kf_cost_grow, KF_MAL, KF_FREE.
        rewrite (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j)). lia.
      * apply IH.
Qed.

Lemma kf_sl_cost_tr : forall c mx no cap len j o,
  tr_cost MT (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o) = sl_cost MT c mx no cap len.
Proof.
  intros c mx no cap len j o. unfold sl_cost, send_line_b_c.send_line_tr.
  destruct (sl_live c len); [apply kf_sl_cost_run_tr | reflexivity].
Qed.

Lemma kf_sl_cost_psi : forall c mx no cap len, 0 <= cap ->
  sl_cost MT c mx no cap len <= kf_psi_o (sl_cap c mx no cap len) - kf_psi_o cap.
Proof.
  intros c mx no cap len Hc. rewrite <- (kf_sl_cost_tr c mx no cap len 0%nat (RelayRunT.Ret 0%nat)).
  unfold sl_cap. apply kf_send_line_gen. exact Hc.
Qed.

Lemma kf_sl_cost_le : forall c mx no cap len, 0 <= cap -> sl_cap c mx no cap len <= CAPOUT_MAX ->
  sl_cost MT c mx no cap len <= 12.
Proof.
  intros c mx no cap len Hc Hle.
  pose proof (kf_sl_cost_psi c mx no cap len Hc) as H1.
  pose proof (kf_out_range cap _ Hc Hle) as H2. lia.
Qed.

Lemma kf_sl_cap_mono : forall c mx no cap len, 0 <= cap -> cap <= sl_cap c mx no cap len.
Proof. intros c mx no cap len Hc. unfold sl_cap. apply kf_send_line_cap_mono. exact Hc. Qed.

(* gesture_end's two sends: their caps chain, so the potential differences telescope *)
Lemma kf_ge_cost_le : forall c mx no cap XL, 0 <= cap -> ge_cap c mx no cap XL <= CAPOUT_MAX ->
  ge_cost MT c mx no cap XL <= 12.
Proof.
  intros c mx no cap XL Hc Hle. unfold ge_cost. unfold ge_cap in Hle.
  pose proof (kf_sl_cap_mono c mx no cap XL Hc) as H1.
  pose proof (kf_sl_cost_psi c mx no cap XL Hc) as H2.
  pose proof (kf_sl_cost_psi (sl_ctl c XL) mx (sl_no c no XL) (sl_cap c mx no cap XL) 5 ltac:(lia)) as H3.
  pose proof (kf_out_range cap _ Hc Hle) as H4. lia.
Qed.

Lemma kf_lp_cost_le : forall l n, lp_cost MT l n <= 1 + (if Psec (n + 1) then 1 else 0).
Proof.
  intros l n. unfold lp_cost. rewrite !KF_MAL, KF_FREE.
  pose proof (kf_b01 (Psec (n + 1))). pose proof (kf_b01 (Psec (lp_vbytes l))).
  destruct (lp_grow l); cbv beta iota; lia.
Qed.
End kf.
