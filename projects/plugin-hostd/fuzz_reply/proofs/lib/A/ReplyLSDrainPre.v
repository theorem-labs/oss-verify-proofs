(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: fr_RINV, a concrete definition of the loop's relational invariant RINV of the
   entry walk of fuzz_reply's LLVMFuzzerTestOneInput (lib/A/W_LLVMFuzzerTestOneInput_cut.v:534, the Section variable
   `RINV : lfcx -> Z -> lmod -> Prop` that lcut carries at every cut point), and, below it, each model rule over RINV
   that a W8 segment takes as a Section hypothesis, restated with RINV := fr_RINV (the `_obl` definitions).  The last
   section proves the obligations that read fr_RINV alone or step only the cursor and the flags; the rest are open.
   The shape is the plain proof's (lib/Prog/SlotInv.v:253-314): relay_at's pairing of the relay's entries with the
   open harness sources (Forall2 pair_ok es hj, NoDup (map snd hj), every slot outside hj closed, the entries' fds
   distinct and in [FIRST_FD, FIRST_FD + nfd)), pair_ok's model clauses, LI's input-cost bound
   (slot_cost es hj <= k, k <= n < INPUT_MAX) and globals_at's link between g_gone and the controller's flags.
   What differs from the plain LI, and why:
   - The COUNTING invariant `2 * nfd <= t + 1 + nopen` replaces the plain `0 <= nfd <= t + 1` (SlotInv.v:309).  The
     plain bound allows nfd = 512 at t = 511, so it does not give op_add's `nfd < OPS_MAX` (a Theorem Labs lane's ruling on
     a Theorem Labs lane's finding).  Every operation keeps the counting invariant (fuzz_reply.c:577-593: op_add raises g_nfd
     only when it opens a slot; :619-631: op_remove closes the slot it removes; no other operation opens or closes a
     slot), and with t < OPS_MAX and a free slot it gives nfd <= 257.  The plain bound follows from it and the
     fd clauses (nopen <= nfd, since the open slots' fds are distinct and in [100, 100 + nfd)).
   - No upper bound on t and no `k <= n`.  Most RI_* rules step `RINV cx t m -> RINV cx (t + 1) m'` with no
     `t < OPS_MAX` premise and, for the small arms, no `lm_k m < c_n cx` premise, so a t- or k-bound in RINV would
     make those rules false.  The input-cost bound is therefore split into `cost <= k` (k only grows) and
     `cost <= n` (the rules that raise the cost all carry `lm_k m < c_n cx`).
   - pair_ok's src_at (memory) is amodel_at's slot here; pair_ok keeps the model slot `nth (snd p) (lm_hs m) None =
     Some (fst p)`.  pair_ok's t-bounds on the pending list (SlotInv.v:261-262) are allocator room, which the
     A-proof keeps in LS (LS_write_room, LS_drain_pre); they are not here.
   - The cost counts the relay's unfinished line by its bytes, `length (re_U e)`, where SlotInv.v:56 counts
     `re_used e`: the two are equal under aentry_ok (W_rep.v:125), but the arms' rules see only the model, and W7's
     drain fixes re_U, not re_used (dr_step_ok, W_LLVMFuzzerTestOneInput_drain.v:559).
   - The entries' model facts that aentry_ok (W_rep.v:120-135) states in memory and that RINV-only rules read
     (RI_pads, RI_pair, RI_rm_cnlr_eof, the exit's end matching) are fr_entry_ok.
   The `_obl` definitions are grouped by segment file, each with the rule's file:line.  Rules on atop's head (head,
   drain, small, write, exit, add) are read off the segment files (Required below); rules that exist only on a hand
   branch are stated over verbatim copies of that branch's model notions (each block names the branch, file and line
   it copies; replace the block by a Require when the branch merges).  A rule that is false against fr_RINV has an
   `_obl` (verbatim) and a `_fix_obl` (the amended text, with the premise the arm already holds).  The last section
   proves every rule of W_LLVMFuzzerTestOneInput_top.v (SEG_HEAD's, ARM_add's, the small arms') in the form that
   holds. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV.v, with its module names changed; 353 of its 443 lines of code are new or changed and 1101 lines of the source are left out. *)
(* a Theorem Labs lane's FREE-PIECES row B1c (a Theorem Labs lane): the drain arm's LS_drain_pre at the instance LS := fr_LS B,
   RINV := fr_RINV, MT := ameter_triv, MMAX := WR_MMAX.  The text is a working branch 129f255c729
   lib/A/W_LLVMFuzzerTestOneInput_drain.v:730-742 (the same in integ 6fb612fb746 :658); every definition it names
   (dr_at_op, dr_pick, dr_e0 in that file; dr_tr, dr_cost, tr_max, tr_alloc in W_contract.v; drain_b_c.v,
   send_line_b_c.v, ListTr.v, RelayModel.v, RelayKeys.v, RelayRep.v, HarnessRep.v, YG01.v) has the same text in this
   tree.  Its six conjuncts, by status:
   (1) |pending_stream h| < 2^26, (2) hl_cap (hs_expected h) < 2^26, (3) re_nheld e + |pending_stream h| < 2^26,
       (6) mo_ok MT S (dr_cost ..): PROVED at the arm's exact premises (fr_LS_drain_pre_c1236).  Entry j and the picked
       source are one row of fr_relay's Forall2 (the fds are distinct), so fr_cost <= c_n < 2^26 bounds (1) and (3)
       and fr_pair_ok's ecap_ok bounds (2); mo_ok is True at ameter_triv.
   (4) tr_max (dr_tr ..) < MMAX: PROVED at a PROPOSED text (fr_LS_drain_pre_c4) with two more premises, both of which
       the arm holds where it applies LS_drain_pre (dc_stB, _drain.v:3801, the application at :3917):
         `0 <= t < OPS_MAX` - dc_regs' clause (_drain.v:2627), named Ht in dc_stB (:3812);
         `Z.of_nat (length (re_U e)) <= APARTIAL` - aentry_ok of entry j (W_rep.v:125, `length (re_U e) = re_used e
           /\ re_used e <= APARTIAL`), which dc_stB already has as HEOK (:3859-3860, from amodel_ne's arelay_at).
       fr_LS and fr_RINV do not give the first: fr_RINV bounds the pending stream by WRITE_MAX * t and by
       fr_cost < 2^26 only, so for t >= 513 a stream of 2^25 + 2 NUL bytes is at least 2^25 + 1 lines, and
       reference_feed's list_push grows the expected array at n = cap = 2^25 to 32 * 2^25 = 2^30 > WR_MMAX
       (ListTr.list_push_tra).  Nor the second: fr_RINV says nothing of re_U when re_skip = 1 (fr_cost counts it
       only at re_skip = 0) and fr_LS bounds re_cap only through PHI (about 2^33), so drain's first growth
       (drain_b_c.grow_tr, `cap - used < 4096`) may ask 2 re_cap >= 2^30, e.g. for re_cap = 2^29 and a longer re_U.
   (5) blocks_bytes S + tr_alloc (dr_tr ..) <= LIVE_MAX: NOT PROVABLE.  tr_alloc (W_contract.v:951-957) sums the size
       of every request, and gesture_seen regrows the relay's held array by one slot per new begin
       (drain_b_c.seen_tr: RRealloc ka ((|H| + 1) * 8), relay.c:106), so a drain of N new begin keys has
       tr_alloc >= 4 N (N + 1), above LIVE_MAX = 2^34 for N >= 65,536 - about 1.7 MB of input in some 26 operations
       (t < OPS_MAX), a reachable state where fr_LS and fr_RINV hold (W8Add measured such a drain, 65,520 begins
       from 1,572,578 input bytes, at 17,184,602,328 requested bytes: METER-FINDING.txt (sha256 e56f281c60fb; internal record)).  So no LS true
       of reachable states gives it; the bound must change in the callee contract (dr_spec's premise), not in LS.
       fr_LS_drain_pre below states the arm's full conclusion with this conjunct carried as the named hypothesis
       Halloc.
   The request bound (4) is a fuel induction over drain_b_c.drain_run (dpre_drain_run) with the invariant dpre_inv:
   the relay's unfinished line stays <= 6000 bytes (chunk's LINE_LIMIT reset), the reference splitter's line stays
   <= 6000 bytes, g_nout + |u| + (bytes still pending) does not grow, the held keys grow by at most one per byte
   sent, and the expected list's length + (bytes still pending) does not grow.  Every request is then at most
   max (2 * 10095, 2 * (6000 + P), 8 * (keys + 6000 + P), 32 * (P - 1), 6001) for P = |pending_stream h|. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
RelayRunT ListTr drain_b_c send_line_b_c gestures_end_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the instance (ReplyATop.v:93 MT := ameter_triv; W_LLVMFuzzerTestOneInput_write.v:132 WR_MMAX) *)
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

(* ================================================================== the request trace's sizes *)
(* a request asks at most M bytes (a free asks none) *)
Definition dpre_rq {P : Type} (M : Z) (ev : RelayRunT.rev P) : Prop :=
  match ev with
  | RelayRunT.RMalloc n => n <= M
  | RelayRunT.RFree _ _ => True
  | RelayRunT.RRealloc _ n _ => n <= M
  end.

Lemma dpre_tr_max : forall {P : Type} (tr : list (RelayRunT.rev P)) M, 0 <= M -> Forall (dpre_rq M) tr ->
  tr_max tr <= M.
Proof.
  intros P tr M HM HF. induction HF as [|ev tr Hev _ IH]; [unfold tr_max; cbn [fold_right]; lia|].
  unfold tr_max in *. cbn [fold_right]. destruct ev; cbn [dpre_rq] in Hev |- *; lia.
Qed.

(* drain's buffer growth: 8192, or 2 cap with cap < used + 4096 *)
Lemma dpre_grow : forall cap used j b M, used <= 6000 -> 20192 <= M ->
  Forall (dpre_rq M) (fst (drain_b_c.grow_tr cap used j b)).
Proof.
  intros cap used j b M Hu HM. unfold drain_b_c.grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096) as [Hlt|Hge]; cbn [fst]; [|constructor].
  destruct (Z.eqb_spec cap 0) as [E|E]; cbn [fst]; (apply Forall_cons; [cbn [dpre_rq]; lia | constructor]).
Qed.

(* send_line's rounds: a growth asks (no + n) * 2 with n <= rem, and no + rem is kept *)
Lemma dpre_sl_run : forall f mx no cap rem j o M, 2 * (no + rem) <= M ->
  Forall (dpre_rq M) (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o M HM; cbn [send_line_b_c.sl_run]; [constructor|].
  destruct (Z.leb_spec rem 0) as [Hr|Hr]; [constructor|].
  match goal with |- context [if ?b then mx else rem] =>
    assert (Hn : (if b then mx else rem) <= rem)
      by (destruct b eqn:E; [apply andb_true_iff in E as [_ E]; apply Z.ltb_lt in E; lia | lia]);
    revert Hn; generalize (if b then mx else rem); intros n Hn end.
  destruct (Z.ltb_spec cap (no + n)) as [Hc|Hc].
  - cbn [fst]. apply Forall_cons; [destruct (cap =? 0); cbn [dpre_rq]; lia | apply IH; lia].
  - apply IH. lia.
Qed.

Lemma dpre_send_line : forall live mx no cap len j o M, 2 * (no + len) <= M ->
  Forall (dpre_rq M) (send_line_b_c.send_line_tr live mx no cap len j o).
Proof.
  intros live mx no cap len j o M HM. unfold send_line_b_c.send_line_tr.
  destruct live; [apply dpre_sl_run; exact HM | constructor].
Qed.

(* a gesture's key is a prefix of its line *)
Lemma dpre_gesture_len : forall l k x, RelayModel.gesture l = Some (k, x) -> (length x <= length l)%nat.
Proof.
  intros l k x H. unfold RelayModel.gesture in H. cbv zeta in H.
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b
  | context [match ?o with Some _ => _ | None => _ end] => destruct o
  end; try discriminate H.
  all: injection H as _ Hx; subst x; rewrite length_firstn; lia.
Qed.

(* gesture_seen: (|H| + 1) * 8 and |key| + 1, or a free *)
Lemma dpre_seen : forall H ka l j ha ks M, Z.of_nat (length l) <= 6000 ->
  8 * (Z.of_nat (length H) + 1) <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.seen_tr H ka l j ha ks))).
Proof.
  intros H ka l j ha ks M Hl HH HM. unfold drain_b_c.seen_tr.
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|constructor].
  pose proof (dpre_gesture_len l kd x G) as Hx.
  destruct kd; destruct (RelayKeys.index_of x H); cbn [fst].
  - constructor.
  - apply Forall_cons; [destruct (ka =? 0); cbn [dpre_rq]; lia|].
    apply Forall_cons; [cbn [dpre_rq]; lia | constructor].
  - apply Forall_cons; [exact I | constructor].
  - constructor.
Qed.

Lemma dpre_seen_arr_len : forall H l, (length (RelayKeys.seen_arr H l) <= S (length H))%nat.
Proof.
  intros H l. unfold RelayKeys.seen_arr.
  destruct (RelayModel.gesture l) as [[[|] x]|]; [destruct (RelayKeys.index_of x H) .. | lia].
  - lia.
  - rewrite length_app. cbn [length]. lia.
  - unfold RelayKeys.swap_remove. rewrite length_firstn. lia.
  - lia.
Qed.

Lemma dpre_with_nul_cons : forall l ls,
  length (RelayModel.with_nul (l :: ls)) = (length l + 1 + length (RelayModel.with_nul ls))%nat.
Proof.
  intros l ls. unfold RelayModel.with_nul. cbn [map concat]. rewrite !length_app. cbn [length]. lia.
Qed.

(* the relayed lines (each <= 6000 bytes): the sends ask at most 2 * A, the held array at most 8 * (Hk + A), where
   g_nout plus the lines' bytes is at most A and the held keys at most Hk plus g_nout *)
Lemma dpre_lines_run : forall ls live mx no cap H ka j o ha ks M Hk A,
  Forall (fun l => Z.of_nat (length l) <= 6000) ls ->
  Z.of_nat (length H) <= Hk + no -> no + Z.of_nat (length (RelayModel.with_nul ls)) <= A ->
  2 * A <= M -> 8 * (Hk + A) <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) /\
  Z.of_nat (length (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))))) <=
    Hk + no + Z.of_nat (length (RelayModel.with_nul ls)).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks M Hk A HF HH HA H2 H8 H6;
    cbn [drain_b_c.lines_run].
  - cbn [fst snd]. split; [constructor|]. lia.
  - apply Forall_cons_iff in HF as [Hl HF].
    rewrite dpre_with_nul_cons in HA |- *.
    pose proof (dpre_seen_arr_len H l) as HS.
    match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 r ?a5 ?a6 ?a7 ?a8] =>
      destruct (IH live mx a1 a2 a3 a4 a5 a6 a7 a8 M Hk A HF ltac:(lia) ltac:(lia) H2 H8 H6) as [I1 I2] end.
    cbn [fst snd]. split; [|lia].
    apply Forall_app. split; [apply dpre_send_line; lia|].
    apply Forall_app. split; [apply dpre_seen; [exact Hl | lia | exact H6] | exact I1].
Qed.

(* reference_feed's pushes: the grown array (128, or 32 cap at n = cap < En) and the text (|l| + 1) *)
Lemma dpre_pushes_run : forall ls n cap j v rs M En,
  Forall (fun l => Z.of_nat (length l) <= 6000) ls -> n + Z.of_nat (length ls) <= En ->
  32 * (En - 1) <= M -> 128 <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (fst (drain_b_c.pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs M En HF Hn H32 H128 H6; cbn [drain_b_c.pushes_run];
    [constructor|].
  apply Forall_cons_iff in HF as [Hl HF]. cbn [length] in Hn.
  cbn [fst]. apply Forall_app. split.
  - unfold ListTr.list_push_tra. apply Forall_app. split.
    + destruct (Z.eqb_spec n cap) as [E|E]; [|constructor].
      destruct (cap =? 0); (apply Forall_cons; [cbn [dpre_rq]; lia | constructor]).
    + apply Forall_cons; [cbn [dpre_rq]; lia | constructor].
  - apply (IH _ _ _ _ _ M En HF); lia.
Qed.

(* LINE_LIMIT, a nat numeral above the abstraction threshold, read as a Z *)
Lemma dpre_LL : Z.of_nat RelayModel.LINE_LIMIT = 6000.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== the two line splitters *)
(* the reference splitter (RelayModel.step): while it is not skipping, its line is at most LINE_LIMIT bytes *)
Definition dpre_jref (st : RelayModel.lstate) : Prop :=
  RelayModel.ls_k st = true \/ Z.of_nat (length (RelayModel.ls_w st)) <= 6000.

Lemma dpre_step : forall st b, dpre_jref st ->
  dpre_jref (fst (RelayModel.step st b)) /\
  (forall l, snd (RelayModel.step st b) = Some l -> Z.of_nat (length l) <= 6000).
Proof.
  intros st b Hj. pose proof dpre_LL as LL. unfold RelayModel.step.
  destruct (Z.eqb b 0).
  - cbn [fst snd]. split; [right; cbn [RelayModel.ls_w length]; lia|].
    intros l Hl. destruct (RelayModel.ls_k st) eqn:Ek; [discriminate Hl|]. injection Hl as <-.
    destruct Hj as [Hj|Hj]; [congruence | exact Hj].
  - destruct (RelayModel.ls_k st) eqn:Ek; cbn [fst snd].
    + split; [left; exact Ek | intros l Hl; discriminate Hl].
    + destruct (Nat.eqb_spec (length (RelayModel.ls_w st)) RelayModel.LINE_LIMIT) as [El|El]; cbn [fst snd].
      * split; [left; reflexivity | intros l Hl; discriminate Hl].
      * split; [|intros l Hl; discriminate Hl]. right. cbn [RelayModel.ls_w]. rewrite length_app. cbn [length].
        destruct Hj as [Hj|Hj]; [congruence|]. lia.
Qed.

Lemma dpre_ref_lines : forall d st, dpre_jref st ->
  Forall (fun l => Z.of_nat (length l) <= 6000) (RelayModel.lines st d) /\
  (length (RelayModel.lines st d) <= length d)%nat /\ dpre_jref (RelayModel.feed st d).
Proof.
  induction d as [|b d IH]; intros st Hj.
  - rewrite RelayModel.lines_nil, RelayModel.feed_nil. split; [constructor|]. split; [cbn [length]; lia | exact Hj].
  - rewrite RelayModel.lines_cons, RelayModel.feed_cons.
    destruct (dpre_step st b Hj) as [S1 S2].
    destruct (IH (fst (RelayModel.step st b)) S1) as (I1 & I2 & I3).
    destruct (snd (RelayModel.step st b)) as [l|] eqn:Eo.
    + split; [apply Forall_cons; [exact (S2 l eq_refl) | exact I1]|]. split; [cbn [length]; lia | exact I3].
    + split; [exact I1|]. split; [cbn [length]; lia | exact I3].
Qed.

(* the relay's splitter (RelayModel.scan / chunk): a line it relays is at most LINE_LIMIT bytes, the lines' bytes with
   their NULs and the unfinished line are at most the old unfinished line and the new bytes *)
Lemma dpre_scan : forall d sk0 acc sk r ls, RelayModel.scan sk0 acc d = (sk, r, ls) ->
  Forall (fun l => Z.of_nat (length l) <= 6000) ls /\
  (length (RelayModel.with_nul ls) + length r <= length acc + length d)%nat.
Proof.
  pose proof dpre_LL as LL. induction d as [|b d IH]; intros sk0 acc sk r ls E.
  - cbn [RelayModel.scan] in E. injection E as E1 E2 E3. subst. split; [constructor|].
    unfold RelayModel.with_nul. cbn [map concat length]. lia.
  - destruct (Z.eq_dec b 0) as [Eb|Eb].
    + subst b. rewrite RelayModel.scan_zero in E.
      destruct (RelayModel.scan false [] d) as [[sk1 r1] ls1] eqn:E1. cbv beta iota in E.
      destruct (IH false [] sk1 r1 ls1 E1) as [I1 I2]. cbn [length] in I2.
      destruct (sk0 || Nat.ltb RelayModel.LINE_LIMIT (length acc)) eqn:Es; cbv beta iota in E;
        injection E as E2 E3 E4; subst.
      * split; [exact I1|]. cbn [length]. lia.
      * apply orb_false_iff in Es as [_ Es]. apply Nat.ltb_ge in Es.
        split; [apply Forall_cons; [lia | exact I1]|]. rewrite dpre_with_nul_cons. cbn [length]. lia.
    + rewrite (RelayModel.scan_nz sk0 acc b d Eb) in E. destruct (IH sk0 (acc ++ [b]) sk r ls E) as [I1 I2].
      rewrite length_app in I2. cbn [length] in I2 |- *. split; [exact I1 | lia].
Qed.

Lemma dpre_chunk : forall u sk0 d u' sk' rl, RelayModel.chunk u sk0 d = (u', sk', rl) ->
  Forall (fun l => Z.of_nat (length l) <= 6000) rl /\
  (length (RelayModel.with_nul rl) + length u' <= length u + length d)%nat /\ Z.of_nat (length u') <= 6000.
Proof.
  intros u sk0 d u' sk' rl E. pose proof dpre_LL as LL. unfold RelayModel.chunk in E.
  destruct (RelayModel.scan sk0 u d) as [[sk r] ls] eqn:E1. cbv beta iota in E.
  destruct (dpre_scan d sk0 u sk r ls E1) as [I1 I2].
  destruct (Nat.ltb_spec RelayModel.LINE_LIMIT (length r)) as [Hl|Hl]; cbv beta iota in E;
    injection E as E2 E3 E4; subst.
  - split; [exact I1|]. cbn [length]. lia.
  - split; [exact I1|]. lia.
Qed.

(* ================================================================== drain's rounds *)
(* the bytes still pending in a round state *)
Definition dpre_rem (s : drain_b_c.dstate) : Z :=
  Z.of_nat (length (concat (drain_b_c.ds_pend s))) - drain_b_c.ds_off s.

(* the round invariant: Hk bounds the held keys against g_nout, A bounds g_nout + the unfinished line + the pending
   bytes, En bounds the expected list's length + the pending bytes *)
Definition dpre_inv (Hk A En : Z) (s : drain_b_c.dstate) : Prop :=
  Z.of_nat (length (drain_b_c.ds_u s)) <= 6000 /\ 0 <= drain_b_c.ds_off s /\ dpre_jref (drain_b_c.ds_ref s) /\
  drain_b_c.ds_no s + Z.of_nat (length (drain_b_c.ds_u s)) + dpre_rem s <= A /\
  Z.of_nat (length (drain_b_c.ds_H s)) <= Hk + drain_b_c.ds_no s /\
  drain_b_c.ds_en s + dpre_rem s <= En.

Lemma dpre_drain_run : forall f live mx s j a M Hk A En, dpre_inv Hk A En s ->
  20192 <= M -> 2 * A <= M -> 8 * (Hk + A) <= M -> 32 * (En - 1) <= M -> 6001 <= M ->
  Forall (dpre_rq M) (fst (drain_b_c.drain_run f live mx s j a)).
Proof.
  induction f as [|f IH]; intros live mx s j a M Hk A En HI Hg H2 H8 H32 H6; [constructor|].
  pose proof HI as (Iu & Io & Ir & Ia & Ih & Ie).
  cbn [drain_b_c.drain_run].
  pose proof (dpre_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) M
                ltac:(lia) Hg) as G1.
  destruct (drain_b_c.ds_eintr s).
  - (* EINTR: the growth only, then the same state *)
    cbn [fst]. apply Forall_app. split; [exact G1|].
    apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
    unfold dpre_inv, dpre_rem in HI |- *.
    cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
         drain_b_c.ds_pend].
    exact HI.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP; [exact G1|].
    assert (Hrem : dpre_rem s = Z.of_nat (length r0) + Z.of_nat (length (concat rs)) - drain_b_c.ds_off s).
    { unfold dpre_rem. rewrite EP. cbn [concat]. rewrite length_app. lia. }
    match goal with |- context [Z.leb ?x 0] => destruct (Z.leb_spec x 0) as [Hn0|Hn0] end; [exact G1|].
    match type of Hn0 with 0 < ?x =>
      assert (Hn1 : x <= Z.of_nat (length r0) - drain_b_c.ds_off s) by lia;
      set (n := x) in * end.
    assert (Hd : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0))) = n)
      by (rewrite length_firstn, length_skipn; lia).
    set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
    destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
    destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & C2 & C3).
    cbv beta iota.
    destruct (dpre_ref_lines d (drain_b_c.ds_ref s) Ir) as (R1 & R2 & R3).
    match goal with |- context [drain_b_c.pushes_run ?n0 ?c ?ls ?jj ?v ?rs0] =>
      assert (P1 : Forall (dpre_rq M) (fst (fst (drain_b_c.pushes_run n0 c ls jj v rs0))))
        by (apply (dpre_pushes_run ls n0 c jj v rs0 M En R1); lia) end.
    match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
      pose proof (dpre_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 M Hk A C1 ltac:(lia) ltac:(lia) H2 H8 H6)
        as [L1 L2];
      revert L1 L2;
      destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
      intros L1 L2 end.
    cbn [fst snd] in L1, L2 |- *.
    apply Forall_app. split; [exact G1|].
    apply Forall_app. split; [exact P1|].
    destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [Ew|Ew].
    + (* the head text is read to its end: list_drop frees it *)
      apply Forall_app. split; [unfold ListTr.list_drop_tra; apply Forall_cons; [exact I | constructor]|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend].
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
    + apply Forall_app. split; [constructor|].
      apply Forall_app. split; [exact L1|].
      apply (IH live mx _ _ _ M Hk A En); [|assumption ..].
      unfold dpre_inv, dpre_rem.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_en
           drain_b_c.ds_pend concat].
      rewrite length_app.
      split; [exact C3|]. split; [lia|]. split; [exact R3|]. split; [lia|]. split; lia.
Qed.

(* the pending texts' bytes from the read offset are the pending stream *)
Lemma dpre_concat_bzs : forall rs : list (Z * list byte),
  length (concat (map (fun r => bzs (snd r)) rs)) = length (concat (map snd rs)).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite !length_app, IH.
  unfold bzs. rewrite length_map. reflexivity.
Qed.

Lemma dpre_rem_init : forall NO CAP e h, 0 <= hs_off h ->
  dpre_rem (drain_b_c.drain_init NO CAP e h) <= Z.of_nat (length (pending_stream h)).
Proof.
  intros NO CAP e h Ho. unfold dpre_rem, pending_stream.
  cbn [drain_b_c.drain_init drain_b_c.ds_pend drain_b_c.ds_off].
  destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [map concat length]; [lia|].
  rewrite !length_app, length_skipn, dpre_concat_bzs. unfold bzs. rewrite length_map. lia.
Qed.

(* drain's requests from g_nout = 0, for an entry whose unfinished line is at most APARTIAL bytes and the source the
   relay reads it from (pair_ok's clauses), with at most 65535 * 511 bytes pending (t < OPS_MAX) *)
Lemma dpre_dr_tr_max : forall c mx cap e h,
  Z.of_nat (length (re_U e)) <= APARTIAL ->
  hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h) ->
  0 <= hs_off h -> hl_recs (hs_expected h) = [] ->
  Z.of_nat (length (re_keys e)) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
  Z.of_nat (length (pending_stream h)) <= 65535 * 511 ->
  tr_max (dr_tr c mx 0 cap e h) < WR_MMAX.
Proof.
  intros c mx cap e h HU HJ Ho He Hk Hp.
  assert (EM : WR_MMAX = 1072693248) by reflexivity.
  assert (E26 : 2 ^ 26 = 67108864) by reflexivity.
  unfold APARTIAL in HU.
  assert (HM : tr_max (dr_tr c mx 0 cap e h) <= WR_MMAX - 1).
  { unfold dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go.
    apply dpre_tr_max; [lia|].
    apply (dpre_drain_run _ _ _ _ _ _ (WR_MMAX - 1) (Z.of_nat (length (re_keys e)))
             (6000 + Z.of_nat (length (pending_stream h))) (Z.of_nat (length (pending_stream h))));
      [|lia ..].
    pose proof (dpre_rem_init 0 cap e h Ho) as Hr.
    unfold dpre_inv.
    cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_no drain_b_c.ds_H
         drain_b_c.ds_en] in Hr |- *.
    assert (Hu : length (bzs (re_U e)) = length (re_U e)) by (unfold bzs; apply length_map).
    split; [lia|]. split; [exact Ho|]. split.
    { unfold dpre_jref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
      destruct HJ as [E|E]; [left; rewrite E; reflexivity | right; rewrite <- E; lia]. }
    split; [lia|]. split.
    { unfold drain_b_c.keys_texts. rewrite length_map. lia. }
    unfold hl_n. rewrite He. cbn [length]. lia. }
  lia.
Qed.

(* ================================================================== the model facts, from fr_RINV *)
Lemma dpre_sum_in : forall (T : Type) (g : T -> Z) l x, (forall y, 0 <= g y) -> In x l ->
  g x <= fold_right Z.add 0 (map g l).
Proof.
  intros T g l x Hg. induction l as [|y l IH]; intros Hx; [destruct Hx|].
  cbn [map fold_right]. destruct Hx as [E|Hx].
  - subst y. assert (0 <= fold_right Z.add 0 (map g l)).
    { clear IH. induction l as [|z l IHl]; cbn [map fold_right]; [lia|]. specialize (Hg z). lia. }
    lia.
  - specialize (Hg y). specialize (IH Hx). lia.
Qed.

Lemma dpre_keys_le : forall ks, Z.of_nat (length ks) <= gestures_end_b_c.keys_total ks.
Proof.
  induction ks as [|k ks IH]; [cbn; lia|].
  unfold gestures_end_b_c.keys_total in *. cbn [fold_right length]. lia.
Qed.

Section dpre.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the entry the arm drains and the source it picked are one row of fr_relay (their fds are equal and distinct
   among the open slots): the row's pair_ok, the entry's entry_ok, and the row's cost under 2^26 *)
Lemma dpre_pair : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  fr_pair_ok m t (nth j (lm_es m) dr_e0) (h, si) /\ fr_entry_ok (nth j (lm_es m) dr_e0) /\
  fr_pair_cost (nth j (lm_es m) dr_e0) (h, si) < 2 ^ 26.
Proof.
  intros cx t m si h j HRI Hpick Hj Hfdj.
  pose proof HRI as (_ & HR & Hn & _).
  destruct HR as (Hlen & Hnd & Hrng & Hent & hj & HF & HNDs & Hcl & Hc & Hcn).
  destruct Hpick as (_ & Hsi & Hh).
  pose proof (Forall2_length HF) as Hlh.
  pose proof (fr_F2_nth _ _ _ _ _ HF j dr_e0 (h, si) Hj) as Hp0.
  assert (Hs0 : snd (nth j hj (h, si)) = si).
  { destruct Hp0 as (H4 & Hn0 & Hf0 & _).
    destruct (Nat.eq_dec (snd (nth j hj (h, si))) si) as [E | Ne]; [exact E | exfalso].
    apply (RI_fds_holds cx t m _ si _ h HRI H4 Hsi Ne Hn0 Hh). rewrite Hf0. exact Hfdj. }
  assert (Ep0 : nth j hj (h, si) = (h, si)).
  { destruct Hp0 as (_ & Hn0 & _). rewrite Hs0, Hh in Hn0. injection Hn0 as Ef.
    apply injective_projections; [exact (eq_sym Ef) | exact Hs0]. }
  assert (Hin : In (nth j (lm_es m) dr_e0, nth j hj (h, si)) (combine (lm_es m) hj)).
  { rewrite <- combine_nth by exact Hlh. apply nth_In. rewrite length_combine. lia. }
  rewrite Ep0 in Hp0, Hin.
  split; [exact Hp0|]. split.
  - rewrite Forall_forall in Hent. apply Hent, nth_In. exact Hj.
  - pose proof (dpre_sum_in _ (fun q => fr_pair_cost (fst q) (snd q)) (combine (lm_es m) hj) _
                  (fun q => fr_pair_cost_nonneg (fst q) (snd q)) Hin) as Hle.
    unfold fr_cost in Hcn. cbn [fst snd] in Hle. lia.
Qed.

(* ================================================================== the rule *)
(* conjuncts 1, 2, 3 and 6 of _drain.v:730 LS_drain_pre, at its exact premises *)
Lemma fr_LS_drain_pre_c1236 : forall cx t m ly S si h j,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j _ HRI _ Hpick Hj Hfdj _.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & _ & Hcost).
  destruct Hp as (_ & _ & _ & _ & _ & _ & _ & Hec & _ & _ & _). cbn [fst snd] in Hec.
  unfold fr_pair_cost in Hcost. cbn [fst] in Hcost.
  pose proof (dpre_keys_le (re_keys (nth j (lm_es m) dr_e0))) as Hkl.
  assert (HU : 0 <= (if re_skip (nth j (lm_es m) dr_e0) =? 0
                     then Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) else 0))
    by (destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia).
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hc.
  unfold re_nheld. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* conjunct 4 of _drain.v:730 LS_drain_pre, at the PROPOSED text: the arm's premises and two dc_stB holds where it
   applies the rule (_drain.v:3917) - dc_regs' `0 <= t < OPS_MAX` (:2627, Ht) and entry j's aentry_ok (W_rep.v:125,
   HEOK at :3859) *)
Lemma fr_LS_drain_pre_c4 : forall cx t m ly S si h j,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX.
Proof.
  intros cx t m ly S si h j _ HRI Hat Hpick Hj Hfdj Heof Ht HU.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & Hcost).
  destruct Hp as (_ & _ & _ & Hre & _ & _ & Hexp & _ & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (S1 & W1).
  destruct Hat as (_ & HO & _).
  replace (Z.of_nat (length (lm_O m))) with 0 by (rewrite HO; reflexivity).
  apply dpre_dr_tr_max.
  - exact HU.
  - destruct (Z.eq_dec (hs_overlong h) 1) as [E|E]; [left; exact E | right]. apply W1. lia.
  - exact Hoff.
  - exact Hexp.
  - unfold fr_pair_cost in Hcost. cbn [fst] in Hcost.
    pose proof (dpre_keys_le (re_keys (nth j (lm_es m) dr_e0))) as Hkl.
    destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia.
  - unfold SlotInv.WRITE_MAX, OPS_MAX in *. lia.
Qed.

(* _drain.v:730 LS_drain_pre, its six conjuncts, at the PROPOSED premises of conjunct 4 and with conjunct 5 carried
   as Halloc: conjunct 5 is NOT PROVABLE (the header: tr_alloc of one drain exceeds LIVE_MAX at reachable states) *)
Lemma fr_LS_drain_pre : forall cx t m ly S si h j,
  fr_LS B cx t m ly S -> fr_RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  forall Halloc : blocks_bytes S +
    tr_alloc (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX,
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
  blocks_bytes S +
    tr_alloc (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
Proof.
  intros cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU Halloc.
  destruct (fr_LS_drain_pre_c1236 cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof) as (C1 & C2 & C3 & C6).
  pose proof (fr_LS_drain_pre_c4 cx t m ly S si h j HLS HRI Hat Hpick Hj Hfdj Heof Ht HU) as C4.
  exact (conj C1 (conj C2 (conj C3 (conj C4 (conj Halloc C6))))).
Qed.
End dpre.
