(* The count half of LS v3, part 6: the per-call count premise inside drain (dr_tr) and relay_remove (rr_tr).
   Proves no function (kind: invariant lemma).

   WHAT IS BOUNDED.  room_live_call_keep (a Theorem Labs lane) needs, at the PRE of every allocator call, sec_cnt <= 1,024,
   ccnt24 <= 2^15 and ccnt_c c <= RL_PRIM c := 2^31 / class_size c.  Inside a callee the count at its k-th call is the
   start count plus the first k events, so the callee premise is `cnt (ablocks B ly S) + tr_peak_w w tr <= LIM`
   (ReplyTrPeakW.v, tr_peak_w_room).  This file bounds tr_peak_w for w := w_sec and w := w_cls c over dr_tr / rr_tr.

   THE WALK (one proof for any 0/1 weight w).  A drain's requests (Prog/drain_b_c.v drain_run) are of three kinds:
   (1) the growth of four blocks that are each ONE live block at a time, a realloc counting its new block before it
       frees the old one: the relay's buffer s->buf (grow_tr), the expected list's vector (list_push_tra's first
       request), g_out (send_line's sl_run) and the held-key array s->held (seen_tr's first request);
   (2) the kept mallocs: one expected text per reference line (list_push_tra's last request, |line| + 1 bytes) and one
       key per new begin line (seen_tr's strndup, |key| + 1 <= |line| + 1 bytes); every line is at most 6,000 bytes
       (the reference splitter: tc_lines_short; the relay's chunk: ReplyLSDrainPre.dpre_chunk);
   (3) frees (the pending text list_drop frees, a held key an end line frees; gestures_end's keys and relay_remove's
       two frees): they never raise a count.
   The potential tc_phi s := the four blocks' weights (0 for a NULL block, tc_wz) is in [0, 4], so the transient of
   one regrowth is at most 5 - tc_phi above the start (tc_pc's first conjunct).  A kept malloc of size x <= 6,001
   weighs at most Bw * x / Lw (hypothesis Hs): for w_sec nothing (Lw = 1, Bw = 0: x < 64,513 is primary,
   ReplyLSCntL.is_sec_iff), for w_cls c at most x / lo c (Lw = lo c, Bw = 1: PresetRoom.lo_le).  Their sizes are paid
   by the stream bytes the drain still has to read, tc_bytes s := 2 * pending + the reference splitter's partial line
   (SlotReads.wcost) + the relay's unfinished line (tp_U): the texts' bytes by SlotReads.lines_bytes, the keys' by
   ReplyLSRemove3.rm3_chunk_mass.  So Lw * tr_peak_w w (dr_tr ..) <= 5 Lw + Bw * tc_bytes (start) (tc_dr), and the
   same for rr_tr (tc_rr: gestures_end's key run grows only g_out).  At a drain of the model, tc_bytes (start) =
   2 * pair_bytes e h, pair_bytes := pending bytes + the relay's unfinished line (fr_pair_cost without keys_total).

   THE BOUNDS.  Secondary: tr_peak_w w_sec <= 5 (fr_LS_drain_sec_peak, fr_LS_rm_sec_peak).  Class c:
   lo c * tr_peak_w (w_cls c) <= 5 lo c + 2 pair_bytes, i.e. <= 5 + 2 pair_bytes / lo c, and pair_bytes <=
   WRITE_MAX * t + APARTIAL (tc_pair_bytes_le).  Class 24 (lo 24 = 5,889): <= 11,380 at t < OPS_MAX.
   THE PER-CALL PREMISE (part 2): with fr_LS3c and msz_ok, ReplyLSCntM.fr_LS3c_sec_cut gives cnt_sec <= t + |es| +
   3 |hs| + 2 + SEC0 <= 593 (|hs| = 4 and |es| <= 4 from fr_RINV), so cnt_sec + peak <= 598 <= 1,024.  The class
   versions carry the state's class count as the one named hypothesis Hcls (the model's class count is part 2's
   potentials' job). *)
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
  SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3 ReplyLSCntL ReplyLS3c ReplyTrPeakW ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyLSCntM.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_LLVMFuzzerTestOneInput_remove.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation rv := (RelayRunT.rev YO0i.sptr).

(* ================================================================== the reference splitter's lines are short *)
(* the splitter keeps at most LINE_LIMIT = 6000 bytes of a line, or skips it (RelayModel.step) *)
Definition tc_ref (st : RelayModel.lstate) : Prop :=
  RelayModel.ls_k st = true \/ Z.of_nat (length (RelayModel.ls_w st)) <= 6000.

Lemma tc_ref_step : forall st b, tc_ref st ->
  tc_ref (fst (RelayModel.step st b)) /\
  (forall l, snd (RelayModel.step st b) = Some l -> Z.of_nat (length l) <= 6000).
Proof.
  intros [ww k] b H. unfold tc_ref in *. cbn [RelayModel.ls_k RelayModel.ls_w] in H.
  unfold RelayModel.step. cbn [RelayModel.ls_k RelayModel.ls_w].
  destruct (Z.eqb b 0).
  - cbn [fst snd RelayModel.ls_k RelayModel.ls_w length]. split; [right; lia|].
    intros l E. destruct k; [discriminate E|]. injection E as <-.
    destruct H as [H|H]; [discriminate H | exact H].
  - destruct k.
    + cbn [fst snd]. split; [left; reflexivity | intros l E; discriminate E].
    + destruct (Nat.eqb_spec (length ww) RelayModel.LINE_LIMIT) as [E|E].
      * cbn [fst snd RelayModel.ls_k]. split; [left; reflexivity | intros l E'; discriminate E'].
      * cbn [fst snd RelayModel.ls_k RelayModel.ls_w]. split; [|intros l E'; discriminate E'].
        (* LINE_LIMIT = 6000 *)
        assert (E6 : Z.of_nat (length ww) <> 6000).
        { intros C. apply E. apply Nat2Z.inj. rewrite C. vm_compute. reflexivity. }
        right. rewrite length_app. cbn [length].
        destruct H as [H|H]; [discriminate H | lia].
Qed.

Lemma tc_lines_short : forall d st, tc_ref st ->
  Forall (fun l => Z.of_nat (length l) <= 6000) (RelayModel.lines st d) /\ tc_ref (RelayModel.feed st d).
Proof.
  induction d as [|b d IH]; intros st H.
  - rewrite RelayModel.lines_nil, RelayModel.feed_nil. split; [constructor | exact H].
  - rewrite RelayModel.lines_cons, RelayModel.feed_cons.
    destruct (tc_ref_step st b H) as [H1 H2].
    destruct (IH _ H1) as [I1 I2]. split; [|exact I2].
    destruct (snd (RelayModel.step st b)) as [l|] eqn:E; [constructor; [exact (H2 l eq_refl) | exact I1] | exact I1].
Qed.

(* ================================================================== the bytes a drain still reads *)
Definition tc_bytes (s : drain_b_c.dstate) : Z := 2 * tp_R s + SlotReads.wcost (drain_b_c.ds_ref s) + tp_U s.
Definition tc_inv (s : drain_b_c.dstate) : Prop :=
  0 <= drain_b_c.ds_ocap s /\ 0 <= drain_b_c.ds_off s /\ tc_ref (drain_b_c.ds_ref s).

Ltac tc_projg := cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
  drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
  drain_b_c.ds_no drain_b_c.ds_ocap].

Lemma tc_bytes_nonneg : forall s, 0 <= tc_bytes s.
Proof.
  intros s. unfold tc_bytes, tp_R, tp_U. pose proof (SlotReads.wcost_nonneg (drain_b_c.ds_ref s)).
  destruct (drain_b_c.ds_skip s); lia.
Qed.

(* ================================================================== the walk, for any 0/1 weight *)
Section piece.
Variable w : Z -> Z.
Variables Lw Bw : Z.
Hypothesis Hw : forall x, 0 <= w x <= 1.
Hypothesis HL : 0 <= Lw.
Hypothesis Ha : 0 <= Bw.
Hypothesis Hs : forall x, 1 <= x <= 6001 -> Lw * w x <= Bw * x.

(* a one-block chain's weight: 0 while NULL *)
Definition tc_wz (n : Z) : Z := if n =? 0 then 0 else w n.
(* a piece of a trace from potential f0 to f1 that spends b: its transient within 5 - f0 above its start, its net
   within f1 - f0 (scaled by Lw, b paid in stream bytes at Bw each) *)
Definition tc_pc (tr : list rv) (f0 f1 b : Z) : Prop :=
  Lw * tr_peak_w w tr <= Lw * (5 - f0) + b /\ Lw * tr_net_w w tr <= Lw * (f1 - f0) + b.

Lemma tc_wz_range : forall n, 0 <= tc_wz n <= 1.
Proof. intros n. unfold tc_wz. destruct (n =? 0); [lia | apply Hw]. Qed.
Lemma tc_wz_nz : forall n, n <> 0 -> tc_wz n = w n.
Proof. intros n H. unfold tc_wz. rewrite (proj2 (Z.eqb_neq n 0) H). reflexivity. Qed.
Lemma tc_wz_0 : tc_wz 0 = 0.
Proof. reflexivity. Qed.

Lemma tc_nil : forall f, f <= 5 -> tc_pc [] f f 0.
Proof.
  intros f Hf. unfold tc_pc. change (tr_peak_w w (@nil rv)) with 0. change (tr_net_w w (@nil rv)) with 0.
  split; nia.
Qed.
Lemma tc_app : forall t1 t2 f0 f1 f2 b1 b2, tc_pc t1 f0 f1 b1 -> tc_pc t2 f1 f2 b2 -> 0 <= b2 ->
  tc_pc (t1 ++ t2) f0 f2 (b1 + b2).
Proof.
  intros t1 t2 f0 f1 f2 b1 b2 (P1 & N1) (P2 & N2) Hb. unfold tc_pc.
  rewrite tr_peak_w_app, tr_net_w_app. split.
  - destruct (Z.max_spec (tr_peak_w w t1) (tr_net_w w t1 + tr_peak_w w t2)) as [[_ E]|[_ E]]; rewrite E; nia.
  - nia.
Qed.
Lemma tc_le : forall tr f0 f1 b b', tc_pc tr f0 f1 b -> b <= b' -> tc_pc tr f0 f1 b'.
Proof. intros tr f0 f1 b b' (P1 & N1) H. unfold tc_pc. split; lia. Qed.
Lemma tc_eq : forall tr f0 f1 f0' f1' b, tc_pc tr f0 f1 b -> f0 = f0' -> f1 = f1' -> tc_pc tr f0' f1' b.
Proof. intros; subst; assumption. Qed.

(* one regrowth of a chain block, malloc when it is NULL *)
Lemma tc_mc : forall c f, c <> 0 -> f <= 4 -> tc_pc [RelayRunT.RMalloc c] f (f + tc_wz c) 0.
Proof.
  intros c f Hc Hf. rewrite (tc_wz_nz c Hc). pose proof (Hw c) as Wc.
  unfold tc_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r, (Z.max_r 0 (w c)) by lia.
  split; nia.
Qed.
Lemma tc_rc : forall o c (x : RelayRunT.addr YO0i.sptr) f, o <> 0 -> c <> 0 -> f <= 4 ->
  tc_pc [RelayRunT.RRealloc o c x] f (f - tc_wz o + tc_wz c) 0.
Proof.
  intros o c x f Ho Hc Hf. rewrite (tc_wz_nz c Hc), (tc_wz_nz o Ho). pose proof (Hw c) as Wc. pose proof (Hw o) as Wo.
  unfold tc_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r.
  rewrite (Z.max_l (w c) (w c - w o)) by lia. rewrite (Z.max_r 0 (w c)) by lia.
  split; nia.
Qed.
Lemma tc_grow : forall o c (x : RelayRunT.addr YO0i.sptr) f, c <> 0 -> f <= 4 ->
  tc_pc [if o =? 0 then RelayRunT.RMalloc c else RelayRunT.RRealloc o c x] f (f - tc_wz o + tc_wz c) 0.
Proof.
  intros o c x f Hc Hf. destruct (Z.eqb_spec o 0) as [E|E].
  - subst o. rewrite tc_wz_0, Z.sub_0_r. apply tc_mc; assumption.
  - apply tc_rc; assumption.
Qed.
(* a kept malloc of a line's bytes *)
Lemma tc_text : forall x f, 1 <= x <= 6001 -> f <= 5 -> tc_pc [RelayRunT.RMalloc x] f f (Bw * x).
Proof.
  intros x f Hx Hf. pose proof (Hw x) as Wx. pose proof (Hs x Hx) as Sx.
  unfold tc_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r, (Z.max_r 0 (w x)) by lia.
  split; nia.
Qed.
(* a free *)
Lemma tc_free : forall k (x : RelayRunT.addr YO0i.sptr) f, f <= 5 -> tc_pc [RelayRunT.RFree k x] f f 0.
Proof.
  intros k x f Hf. pose proof (Hw k) as Wk.
  unfold tc_pc, tr_peak_w, tr_net_w. cbn [fold_right]. rewrite !Z.add_0_r, (Z.max_l 0 (0 - w k)) by lia.
  split; nia.
Qed.
Lemma tc_cons_free : forall k (x : RelayRunT.addr YO0i.sptr) l f0 f1 b, f0 <= 5 -> tc_pc l f0 f1 b -> 0 <= b ->
  tc_pc (RelayRunT.RFree k x :: l) f0 f1 b.
Proof.
  intros k x l f0 f1 b Hf H Hb. change (RelayRunT.RFree k x :: l) with ([RelayRunT.RFree k x] ++ l).
  replace b with (0 + b) by lia. apply (tc_app _ _ _ f0); [apply tc_free; exact Hf | exact H | exact Hb].
Qed.

(* ---- send_line: g_out's regrowths *)
Lemma tc_sl_run : forall fu mx no cap rem j o A, 0 <= cap -> 0 <= A <= 3 ->
  tc_pc (fst (send_line_b_c.sl_run fu mx no cap rem j o)) (A + tc_wz cap)
     (A + tc_wz (fst (snd (send_line_b_c.sl_run fu mx no cap rem j o)))) 0 /\
  0 <= fst (snd (send_line_b_c.sl_run fu mx no cap rem j o)).
Proof.
  induction fu as [|fu IH]; intros mx no cap rem j o A Hc HA; pose proof (tc_wz_range cap) as Wc;
    cbn [send_line_b_c.sl_run].
  - cbn [fst snd]. split; [apply tc_nil; lia | exact Hc].
  - destruct (rem <=? 0); [cbn [fst snd]; split; [apply tc_nil; lia | exact Hc]|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; [|cbv beta iota; apply IH; assumption].
    cbn [fst snd].
    destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) A ltac:(lia) HA) as [I1 I2].
    split; [|exact I2].
    match goal with |- tc_pc (?e :: ?l) _ _ _ => change (e :: l) with ([e] ++ l) end.
    eapply tc_le.
    { eapply (tc_app _ _ _ (A + tc_wz ((no + n) * 2))); [| exact I1 | lia].
      eapply tc_eq; [apply (tc_grow cap ((no + n) * 2) o (A + tc_wz cap)); lia | reflexivity | lia]. }
    lia.
Qed.
Lemma tc_send_line : forall live mx no cap len j o A, 0 <= cap -> 0 <= A <= 3 ->
  tc_pc (send_line_b_c.send_line_tr live mx no cap len j o) (A + tc_wz cap)
     (A + tc_wz (send_line_b_c.send_line_cap live mx no cap len)) 0 /\
  0 <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros live mx no cap len j o A Hc HA. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live.
  - destruct (tc_sl_run (Z.to_nat len) mx no cap len j o A Hc HA) as [P1 P2].
    rewrite sl_run_fin in P1, P2 |- *. split; assumption.
  - split; [apply tc_nil; pose proof (tc_wz_range cap); lia | exact Hc].
Qed.

(* ---- gesture_seen: the held array's regrowth and the key's strndup, or a key's free *)
Lemma tc_seen : forall H ka l j ha ks A, Z.of_nat (length l) <= 6000 -> 0 <= A <= 3 ->
  tc_pc (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) (A + tc_wz ka)
     (A + tc_wz (snd (fst (drain_b_c.seen_tr H ka l j ha ks)))) (Bw * (Z.of_nat (length l) + 1)).
Proof.
  intros H ka l j ha ks A Hl HA. pose proof (tc_wz_range ka) as Wk. unfold drain_b_c.seen_tr.
  assert (B0 : 0 <= Bw * (Z.of_nat (length l) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|cbn [fst snd]; eapply tc_le; [apply tc_nil; lia | exact B0]].
  pose proof (dpre_gesture_len l kd x G) as Hx.
  destruct kd; destruct (index_of x H) as [nn|] eqn:EI; cbn [fst snd].
  - eapply tc_le; [apply tc_nil; lia | exact B0].
  - set (c := (Z.of_nat (length H) + 1) * 8).
    pose proof (tc_wz_range c) as Wc.
    match goal with |- tc_pc [?e1; ?e2] _ _ _ => change [e1; e2] with ([e1] ++ [e2]) end.
    eapply tc_le.
    { eapply tc_app; [| apply (tc_text (Z.of_nat (length x) + 1) (A + tc_wz c)); lia | ].
      - eapply tc_eq; [apply (tc_grow ka c ha (A + tc_wz ka)); unfold c; lia | reflexivity | lia].
      - apply Z.mul_nonneg_nonneg; lia. }
    nia.
  - apply tc_cons_free; [lia | eapply tc_le; [apply tc_nil; lia | exact B0] | exact B0].
  - eapply tc_le; [apply tc_nil; lia | exact B0].
Qed.

(* ---- the relayed lines: each send_line, then gesture_seen *)
Lemma tc_lines : forall ls live mx no cap H ka j o ha ks tr oc H' ka' ad A, 0 <= cap -> 0 <= A <= 2 ->
  Forall (fun l => Z.of_nat (length l) <= 6000) ls ->
  drain_b_c.lines_run live mx no cap H ka ls j o ha ks = (tr, (oc, H', ka'), ad) ->
  tc_pc tr (A + tc_wz cap + tc_wz ka) (A + tc_wz oc + tc_wz ka')
    (Bw * Z.of_nat (length (RelayModel.with_nul ls))) /\ 0 <= oc.
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks tr oc H' ka' ad A Hc HA HF E.
  - cbn [drain_b_c.lines_run] in E. injection E as <- <- <- <- <-.
    rewrite RelayCap.with_nul_nil_len, Z.mul_0_r. pose proof (tc_wz_range cap). pose proof (tc_wz_range ka).
    split; [apply tc_nil; lia | exact Hc].
  - inversion HF as [|? ? Hl HF']; subst.
    cbn [drain_b_c.lines_run] in E. cbv zeta in E.
    match type of E with context [drain_b_c.lines_run live mx ?n2 ?c2 ?H2 ?k2 ls ?j2 ?o2 ?h2 ?s2] =>
      destruct (drain_b_c.lines_run live mx n2 c2 H2 k2 ls j2 o2 h2 s2) as [[tr2 [[oc2 H2'] ka2]] ad2] eqn:E2 end.
    cbn [fst snd] in E. injection E as <- <- <- <- <-.
    rewrite RelayCap.with_nul_cons_len.
    pose proof (tc_wz_range ka) as Wk. pose proof (tc_wz_range cap) as Wc.
    destruct (tc_send_line live mx no cap (Z.of_nat (length l) + 1) j o (A + tc_wz ka) Hc ltac:(lia)) as [S1 S2].
    set (c1 := send_line_b_c.send_line_cap live mx no cap (Z.of_nat (length l) + 1)) in *.
    pose proof (tc_wz_range c1) as Wc1.
    match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
      pose proof (tc_seen H ka l jj ha ks (A + tc_wz c1) Hl ltac:(lia)) as T1 end.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A S2 HA HF' E2) as [I1 I2].
    split; [|exact I2].
    assert (B1 : 0 <= Bw * (Z.of_nat (length l) + 1)) by (apply Z.mul_nonneg_nonneg; lia).
    assert (B2 : 0 <= Bw * Z.of_nat (length (RelayModel.with_nul ls))) by (apply Z.mul_nonneg_nonneg; lia).
    eapply tc_le.
    { eapply tc_app; [eapply tc_eq; [exact S1 | lia | reflexivity] | | ].
      - eapply tc_app; [eapply tc_eq; [exact T1 | lia | reflexivity] | eapply tc_eq; [exact I1 | lia | reflexivity] | ].
        exact B2.
      - lia. }
    lia.
Qed.

(* ---- reference_feed's pushes: the vector's regrowth, then the text *)
Lemma tc_push : forall v n cap x A, 0 <= x <= 6000 -> 0 <= A <= 3 ->
  tc_pc (ListTr.list_push_tra v n cap x) (A + tc_wz (16 * cap)) (A + tc_wz (16 * drain_b_c.push_cap n cap))
    (Bw * (x + 1)).
Proof.
  intros v n cap x A Hx HA. unfold ListTr.list_push_tra, drain_b_c.push_cap.
  pose proof (tc_wz_range (16 * cap)) as W0.
  assert (B1 : 0 <= Bw * (x + 1)) by (apply Z.mul_nonneg_nonneg; lia).
  destruct (Z.eqb_spec n cap) as [En|En]; [destruct (Z.eqb_spec cap 0) as [E0|E0]|]; cbv beta iota.
  - rewrite E0. change (16 * 0) with 0. change (16 * 8) with 128. rewrite tc_wz_0.
    pose proof (tc_wz_range 128) as W1.
    replace (Bw * (x + 1)) with (0 + Bw * (x + 1)) by lia.
    eapply tc_app; [| apply tc_text; lia | exact B1].
    eapply tc_eq; [apply (tc_mc 128 (A + 0)); lia | reflexivity | lia].
  - replace (16 * (cap * 2)) with (32 * cap) by lia.
    pose proof (tc_wz_range (32 * cap)) as W1.
    replace (Bw * (x + 1)) with (0 + Bw * (x + 1)) by lia.
    eapply tc_app; [| apply tc_text; lia | exact B1].
    eapply tc_eq; [apply (tc_rc (16 * cap) (32 * cap) v (A + tc_wz (16 * cap))); lia | reflexivity | lia].
  - rewrite app_nil_l. apply tc_text; lia.
Qed.
Lemma tc_pushes : forall ls n cap j v rs tr cap' ad A, 0 <= A <= 3 ->
  Forall (fun l => Z.of_nat (length l) <= 6000) ls ->
  drain_b_c.pushes_run n cap ls j v rs = (tr, cap', ad) ->
  tc_pc tr (A + tc_wz (16 * cap)) (A + tc_wz (16 * cap')) (Bw * Z.of_nat (length (RelayModel.with_nul ls))).
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs tr cap' ad A HA HF E.
  - cbn [drain_b_c.pushes_run] in E. injection E as <- <- <-.
    rewrite RelayCap.with_nul_nil_len, Z.mul_0_r. pose proof (tc_wz_range (16 * cap)). apply tc_nil. lia.
  - inversion HF as [|? ? Hl HF']; subst.
    cbn [drain_b_c.pushes_run] in E. cbv zeta in E.
    match type of E with context [drain_b_c.pushes_run (n + 1) ?c2 ls ?j2 ?v2 ?r2] =>
      destruct (drain_b_c.pushes_run (n + 1) c2 ls j2 v2 r2) as [[tr2 cap2] ad2] eqn:E2 end.
    cbn [fst snd] in E. injection E as <- <- <-.
    pose proof (IH _ _ _ _ _ _ _ _ A HA HF' E2) as I.
    rewrite RelayCap.with_nul_cons_len.
    assert (B2 : 0 <= Bw * Z.of_nat (length (RelayModel.with_nul ls))) by (apply Z.mul_nonneg_nonneg; lia).
    eapply tc_le.
    { eapply tc_app; [apply (tc_push v n cap (Z.of_nat (length l)) A); lia | exact I | exact B2]. }
    lia.
Qed.

(* ---- the drain buffer's growth *)
Lemma tc_grow_tr : forall cap used j b A, 0 <= A <= 3 ->
  tc_pc (fst (drain_b_c.grow_tr cap used j b)) (A + tc_wz cap)
    (A + tc_wz (fst (snd (drain_b_c.grow_tr cap used j b)))) 0.
Proof.
  intros cap used j b A HA. pose proof (tc_wz_range cap). unfold drain_b_c.grow_tr.
  destruct (cap - used <? 4096); cbv beta iota zeta; cbn [fst snd].
  - eapply tc_eq; [apply (tc_grow cap _ b (A + tc_wz cap)); [destruct (Z.eqb_spec cap 0); cbv beta iota; lia | lia]
                  | reflexivity | lia].
  - apply tc_nil. lia.
Qed.

(* ---- drain's rounds *)
Definition tc_phi (s : drain_b_c.dstate) : Z :=
  tc_wz (drain_b_c.ds_cap s) + tc_wz (16 * drain_b_c.ds_ecap s) + tc_wz (drain_b_c.ds_ocap s) +
  tc_wz (drain_b_c.ds_ka s).
Lemma tc_phi_range : forall s, 0 <= tc_phi s <= 4.
Proof.
  intros s. unfold tc_phi. pose proof (tc_wz_range (drain_b_c.ds_cap s)).
  pose proof (tc_wz_range (16 * drain_b_c.ds_ecap s)). pose proof (tc_wz_range (drain_b_c.ds_ocap s)).
  pose proof (tc_wz_range (drain_b_c.ds_ka s)). lia.
Qed.

Lemma tc_drain_run : forall f live mx s j ad, tc_inv s ->
  tc_pc (fst (drain_b_c.drain_run f live mx s j ad)) (tc_phi s)
    (tc_phi (fst (snd (drain_b_c.drain_run f live mx s j ad))))
    (Bw * (tc_bytes s - tc_bytes (fst (snd (drain_b_c.drain_run f live mx s j ad))))) /\
  tc_bytes (fst (snd (drain_b_c.drain_run f live mx s j ad))) <= tc_bytes s /\
  tc_inv (fst (snd (drain_b_c.drain_run f live mx s j ad))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j ad HI.
  { cbn [drain_b_c.drain_run fst snd]. rewrite Z.sub_diag, Z.mul_0_r. pose proof (tc_phi_range s).
    split; [apply tc_nil; lia | split; [lia | exact HI]]. }
  pose proof HI as (Io & Iof & Iref).
  pose proof (tc_wz_range (16 * drain_b_c.ds_ecap s)) as We. pose proof (tc_wz_range (drain_b_c.ds_ocap s)) as Wo.
  pose proof (tc_wz_range (drain_b_c.ds_ka s)) as Wk.
  cbn [drain_b_c.drain_run]. cbv zeta.
  pose proof (tc_grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf ad)
    (tc_wz (16 * drain_b_c.ds_ecap s) + tc_wz (drain_b_c.ds_ocap s) + tc_wz (drain_b_c.ds_ka s)) ltac:(lia)) as G.
  revert G.
  generalize (drain_b_c.grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf ad)).
  intros [tg [cap1 b1]] G. cbn [fst snd] in G |- *.
  pose proof (tc_wz_range cap1) as W1.
  set (s1 := drain_b_c.DS cap1 (drain_b_c.ds_u s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s) false
               (drain_b_c.ds_pend s) (drain_b_c.ds_off s) (drain_b_c.ds_ref s) (drain_b_c.ds_en s)
               (drain_b_c.ds_ecap s) (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)).
  assert (P1 : tc_phi s1 = tc_wz cap1 + tc_wz (16 * drain_b_c.ds_ecap s) + tc_wz (drain_b_c.ds_ocap s) +
                           tc_wz (drain_b_c.ds_ka s)) by (unfold s1, tc_phi; tc_projg; reflexivity).
  assert (B1 : tc_bytes s1 = tc_bytes s) by (unfold s1, tc_bytes, tp_R, tp_U, rm3_dstr; tc_projg; reflexivity).
  assert (J1 : tc_inv s1) by (unfold s1, tc_inv; tc_projg; tauto).
  assert (G1 : tc_pc tg (tc_phi s) (tc_phi s1) 0) by (eapply tc_eq; [exact G | unfold tc_phi; lia | rewrite P1; lia]).
  clearbody s1.
  destruct (drain_b_c.ds_eintr s).
  - (* an EINTR round: the growth only, then the same state *)
    cbn [fst snd].
    match goal with |- context [drain_b_c.drain_run f live mx s1 ?j1 ?a1] =>
      destruct (IH s1 j1 a1 J1) as (I1 & I2 & I3) end.
    split; [|split; [lia | exact I3]].
    eapply tc_le; [eapply tc_app; [exact G1 | exact I1 | apply Z.mul_nonneg_nonneg; lia] | rewrite B1; lia].
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP.
    + cbn [fst snd]. rewrite B1, Z.sub_diag, Z.mul_0_r. split; [exact G1 | split; [lia | exact J1]].
    + match goal with |- context [Z.min ?x ?y <=? 0] => set (n := Z.min x y) in * end.
      assert (Hnr : n <= Z.of_nat (length r0) - drain_b_c.ds_off s) by (unfold n; apply Z.le_min_l).
      destruct (Z.leb_spec n 0) as [Hn|Hn].
      * cbn [fst snd]. rewrite B1, Z.sub_diag, Z.mul_0_r. split; [exact G1 | split; [lia | exact J1]].
      * (* a data round *)
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
        assert (Ld : Z.of_nat (length d) = n) by (unfold d; rewrite length_firstn, length_skipn; lia).
        destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
        pose proof (rm3_chunk_mass _ _ _ _ _ _ EC) as CM.
        destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & _ & _).
        pose proof (SlotReads.lines_bytes d (drain_b_c.ds_ref s)) as LB.
        destruct (tc_lines_short d (drain_b_c.ds_ref s) Iref) as [LS1 LS2].
        cbv beta iota.
        match goal with |- context [drain_b_c.pushes_run ?n0 ?c0 ?ls0 ?jj ?vv ?rr] =>
          destruct (drain_b_c.pushes_run n0 c0 ls0 jj vv rr) as [[tpu ecap'] [v' rs']] eqn:EPU end.
        pose proof (tc_pushes _ _ _ _ _ _ _ _ _
          (tc_wz cap1 + tc_wz (drain_b_c.ds_ocap s) + tc_wz (drain_b_c.ds_ka s)) ltac:(lia) LS1 EPU) as PU.
        pose proof (tc_wz_range (16 * ecap')) as We'.
        match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 rl ?a5 ?a6 ?a7 ?a8] =>
          destruct (drain_b_c.lines_run live mx a1 a2 a3 a4 rl a5 a6 a7 a8)
            as [[tl [[oc' H'] ka']] [[o' ha'] ks']] eqn:EL end.
        destruct (tc_lines _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (tc_wz cap1 + tc_wz (16 * ecap')) Io ltac:(lia) C1 EL)
          as [PL1 PL2].
        pose proof (tc_wz_range oc') as Wo'. pose proof (tc_wz_range ka') as Wk'.
        cbn [fst snd].
        assert (R0 : tp_R s = Z.of_nat (length r0) - drain_b_c.ds_off s + Z.of_nat (length (concat rs))).
        { unfold tp_R, rm3_dstr. rewrite EP, length_app, length_skipn. lia. }
        assert (Hdb : tc_bytes s = 2 * tp_R s + SlotReads.wcost (drain_b_c.ds_ref s) +
                 (if drain_b_c.ds_skip s then 0 else Z.of_nat (length (drain_b_c.ds_u s)))) by reflexivity.
        assert (BL : 0 <= Bw * Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))))
          by (apply Z.mul_nonneg_nonneg; lia).
        assert (BR : 0 <= Bw * Z.of_nat (length (RelayModel.with_nul rl))) by (apply Z.mul_nonneg_nonneg; lia).
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [W|W].
        -- (* the head text is read to its end: list_drop frees it *)
           match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] =>
             set (S2 := s2); set (J4 := j4); set (A2 := a2) end.
           assert (R2 : tp_R S2 = Z.of_nat (length (concat rs))).
           { unfold S2, tp_R, rm3_dstr. tc_projg. rewrite rm3_dstr0. reflexivity. }
           assert (D2 : tc_bytes S2 = 2 * Z.of_nat (length (concat rs)) +
                          SlotReads.wcost (RelayModel.feed (drain_b_c.ds_ref s) d) +
                          (if sk' then 0 else Z.of_nat (length u'))).
           { unfold tc_bytes. rewrite R2. unfold tp_U, S2. tc_projg. reflexivity. }
           assert (F2 : tc_phi S2 = tc_wz cap1 + tc_wz (16 * ecap') + tc_wz oc' + tc_wz ka')
             by (unfold S2, tc_phi; tc_projg; reflexivity).
           assert (J2 : tc_inv S2) by (unfold S2, tc_inv; tc_projg; split; [exact PL2 | split; [lia | exact LS2]]).
           destruct (IH S2 J4 A2 J2) as (I1 & I2 & I3).
           assert (BB : Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))) +
                        Z.of_nat (length (RelayModel.with_nul rl)) <= tc_bytes s - tc_bytes S2) by lia.
           assert (BBm : Bw * (Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))) +
                        Z.of_nat (length (RelayModel.with_nul rl))) <= Bw * (tc_bytes s - tc_bytes S2))
             by (apply Z.mul_le_mono_nonneg_l; lia).
           assert (BP : 0 <= Bw * (tc_bytes S2 - tc_bytes (fst (snd (drain_b_c.drain_run f live mx S2 J4 A2)))))
             by (apply Z.mul_nonneg_nonneg; lia).
           cbv beta iota. unfold ListTr.list_drop_tra. cbn [app].
           split; [|split; [lia | exact I3]].
           eapply tc_le.
           { eapply tc_app; [exact G1 | | ].
             - eapply tc_app; [eapply tc_eq; [exact PU | rewrite P1; lia | reflexivity] | | ].
               + apply tc_cons_free; [lia | | ].
                 * eapply (tc_app _ _ _ (tc_phi S2)); [eapply tc_eq; [exact PL1 | lia | rewrite F2; lia] | exact I1 |].
                   exact BP.
                 * lia.
               + lia.
             - lia. }
           lia.
        -- (* part of the head text read *)
           match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] =>
             set (S2 := s2); set (J4 := j4); set (A2 := a2) end.
           assert (R2 : tp_R S2 = Z.of_nat (length r0) - (drain_b_c.ds_off s + n) + Z.of_nat (length (concat rs))).
           { unfold S2, tp_R, rm3_dstr. tc_projg. rewrite length_app, length_skipn. lia. }
           assert (D2 : tc_bytes S2 = 2 * (Z.of_nat (length r0) - (drain_b_c.ds_off s + n) +
                                           Z.of_nat (length (concat rs))) +
                          SlotReads.wcost (RelayModel.feed (drain_b_c.ds_ref s) d) +
                          (if sk' then 0 else Z.of_nat (length u'))).
           { unfold tc_bytes. rewrite R2. unfold tp_U, S2. tc_projg. reflexivity. }
           assert (F2 : tc_phi S2 = tc_wz cap1 + tc_wz (16 * ecap') + tc_wz oc' + tc_wz ka')
             by (unfold S2, tc_phi; tc_projg; reflexivity).
           assert (J2 : tc_inv S2) by (unfold S2, tc_inv; tc_projg; split; [exact PL2 | split; [lia | exact LS2]]).
           destruct (IH S2 J4 A2 J2) as (I1 & I2 & I3).
           assert (BB : Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))) +
                        Z.of_nat (length (RelayModel.with_nul rl)) <= tc_bytes s - tc_bytes S2) by lia.
           assert (BBm : Bw * (Z.of_nat (length (RelayModel.with_nul (RelayModel.lines (drain_b_c.ds_ref s) d))) +
                        Z.of_nat (length (RelayModel.with_nul rl))) <= Bw * (tc_bytes s - tc_bytes S2))
             by (apply Z.mul_le_mono_nonneg_l; lia).
           assert (BP : 0 <= Bw * (tc_bytes S2 - tc_bytes (fst (snd (drain_b_c.drain_run f live mx S2 J4 A2)))))
             by (apply Z.mul_nonneg_nonneg; lia).
           cbv beta iota. cbn [app].
           split; [|split; [lia | exact I3]].
           eapply tc_le.
           { eapply tc_app; [exact G1 | | ].
             - eapply tc_app; [eapply tc_eq; [exact PU | rewrite P1; lia | reflexivity] | | ].
               + eapply (tc_app _ _ _ (tc_phi S2)); [eapply tc_eq; [exact PL1 | lia | rewrite F2; lia] | exact I1 |].
                 exact BP.
               + lia.
             - lia. }
           lia.
Qed.

(* one drain: Lw * peak <= 5 Lw + Bw * (the bytes it may read) *)
Lemma tc_dr : forall c mx no cap e h, 0 <= cap -> 0 <= hs_off h -> tc_ref (hs_state h) ->
  Lw * tr_peak_w w (dr_tr c mx no cap e h) <= 5 * Lw + Bw * tc_bytes (drain_b_c.drain_init no cap e h).
Proof using Hw HL Ha Hs.
  intros c mx no cap e h Hcap Hoff Href.
  assert (HI : tc_inv (drain_b_c.drain_init no cap e h)) by (unfold tc_inv, drain_b_c.drain_init; tc_projg; tauto).
  destruct (tc_drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx _ 0%nat drain_b_c.dadr0 HI)
    as ((P1 & _) & D2 & _).
  unfold dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go.
  pose proof (tc_phi_range (drain_b_c.drain_init no cap e h)) as F.
  assert (M1 : 0 <= Lw * tc_phi (drain_b_c.drain_init no cap e h)) by (apply Z.mul_nonneg_nonneg; lia).
  match type of D2 with tc_bytes ?sf <= _ =>
    assert (M2 : 0 <= Bw * tc_bytes sf) by (apply Z.mul_nonneg_nonneg; [lia | apply tc_bytes_nonneg]) end.
  lia.
Qed.

(* ---- gestures_end's key run: each key's two sends (g_out's regrowths), then the key's free *)
Lemma tc_keys_end_run : forall xks live mx no cap j o A, 0 <= cap -> 0 <= A <= 3 ->
  tc_pc (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)) (A + tc_wz cap)
     (A + tc_wz (fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)))) 0 /\
  0 <= fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)).
Proof.
  induction xks as [|[xl ka] r IH]; intros live mx no cap j o A Hc HA.
  - cbn [gestures_end_b_c.keys_end_run fst snd]. split; [apply tc_nil; pose proof (tc_wz_range cap); lia | exact Hc].
  - cbn [gestures_end_b_c.keys_end_run]. unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap.
    cbv zeta. cbn [fst snd].
    destruct (tc_send_line live mx no cap xl j o A Hc HA) as [S1 S2].
    match goal with |- context [send_line_b_c.send_line_tr live mx (no + xl) ?c1 5 ?j1 ?o1] =>
      destruct (tc_send_line live mx (no + xl) c1 5 j1 o1 A S2 HA) as [S3 S4] end.
    match goal with |- context [gestures_end_b_c.keys_end_run live mx (no + xl + 5) ?c2 r ?j2 ?o2] =>
      destruct (IH live mx (no + xl + 5) c2 j2 o2 A S4 HA) as [I1 I2];
      pose proof (tc_wz_range c2) as W2 end.
    split; [|exact I2].
    rewrite <- app_assoc.
    eapply tc_le.
    { eapply tc_app; [exact S1 | | ].
      - eapply tc_app; [exact S3 | apply tc_cons_free; [lia | exact I1 | lia] | lia].
      - lia. }
    lia.
Qed.

(* a whole trace's piece gives the callee's peak bound *)
Lemma tc_peak_of : forall tr f0 f1 b B', tc_pc tr f0 f1 b -> 0 <= f0 -> b <= B' -> Lw * tr_peak_w w tr <= 5 * Lw + B'.
Proof. intros tr f0 f1 b B' (P & _) H0 Hb. nia. Qed.

(* relay_remove's requests: drain's when the entry is open, the key run, two frees *)
Lemma tc_rr : forall c mx no cap FD es h e,
  find (fun e => re_fd e =? FD) es = Some e -> 0 <= cap ->
  (re_eof e = 0 -> 0 <= hs_off h /\ tc_ref (hs_state h)) ->
  Lw * tr_peak_w w (rr_tr c mx no cap FD es h) <=
    5 * Lw + (if re_eof e =? 0 then Bw * tc_bytes (drain_b_c.drain_init no cap e h) else 0).
Proof using Hw HL Ha Hs.
  intros c mx no cap FD es h e Hf Hcap HJ.
  assert (M0 : 0 <= Bw * tc_bytes (drain_b_c.drain_init no cap e h))
    by (apply Z.mul_nonneg_nonneg; [lia | apply tc_bytes_nonneg]).
  unfold rr_tr. cbv zeta.
  destruct (FD <? 0).
  { change (tr_peak_w w (@nil rv)) with 0. destruct (re_eof e =? 0); lia. }
  rewrite Hf. cbv beta iota zeta.
  destruct (re_eof e =? 0) eqn:Eo; cbv beta iota.
  - apply Z.eqb_eq in Eo. destruct (HJ Eo) as [Hoff Href].
    assert (HI : tc_inv (drain_b_c.drain_init no cap e h)) by (unfold tc_inv, drain_b_c.drain_init; tc_projg; tauto).
    pose proof (tc_drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx _ 0%nat drain_b_c.dadr0 HI) as D.
    pose proof (tc_phi_range (drain_b_c.drain_init no cap e h)) as F.
    unfold dr_tr, dr_fin, drain_b_c.drain_tr, drain_b_c.drain_fin, drain_b_c.drain_go.
    revert D.
    generalize (drain_b_c.drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx
                  (drain_b_c.drain_init no cap e h) 0%nat drain_b_c.dadr0).
    intros [tr [fin adf]] (D1 & D2 & D3). cbn [fst snd] in D1, D2, D3 |- *.
    destruct D3 as (Do & _ & _).
    pose proof (tc_wz_range (drain_b_c.ds_cap fin)). pose proof (tc_wz_range (16 * drain_b_c.ds_ecap fin)).
    pose proof (tc_wz_range (drain_b_c.ds_ka fin)).
    match goal with |- context [gestures_end_b_c.keys_end_run ?lv ?mm ?nn (drain_b_c.ds_ocap fin) ?xks ?jj ?oo] =>
      destruct (tc_keys_end_run xks lv mm nn (drain_b_c.ds_ocap fin) jj oo
        (tc_wz (drain_b_c.ds_cap fin) + tc_wz (16 * drain_b_c.ds_ecap fin) + tc_wz (drain_b_c.ds_ka fin)) Do
        ltac:(lia)) as [K1 _];
      pose proof (tc_wz_range (fst (snd (gestures_end_b_c.keys_end_run lv mm nn (drain_b_c.ds_ocap fin) xks jj oo))))
    end.
    assert (M3 : 0 <= Bw * tc_bytes fin) by (apply Z.mul_nonneg_nonneg; [lia | apply tc_bytes_nonneg]).
    eapply tc_peak_of.
    + eapply (tc_app _ _ _ (tc_phi fin)); [exact D1 | | ].
      * eapply tc_app; [eapply tc_eq; [exact K1 | unfold tc_phi; lia | reflexivity] | | ].
        -- apply tc_cons_free; [lia | apply tc_cons_free; [lia | apply tc_nil; lia | lia] | lia].
        -- lia.
      * lia.
    + exact (proj1 F).
    + lia.
  - rewrite app_nil_l.
    match goal with |- context [gestures_end_b_c.keys_end_run ?lv ?mm ?nn ?cc ?xks ?jj ?oo] =>
      assert (Hc0 : 0 <= cc) by (unfold drain_b_c.drain_init; tc_projg; exact Hcap);
      destruct (tc_keys_end_run xks lv mm nn cc jj oo 0 Hc0 ltac:(lia)) as [K1 _];
      pose proof (tc_wz_range cc);
      pose proof (tc_wz_range (fst (snd (gestures_end_b_c.keys_end_run lv mm nn cc xks jj oo))))
    end.
    eapply tc_peak_of.
    + eapply tc_app; [exact K1 | | ].
      * apply tc_cons_free; [lia | apply tc_cons_free; [lia | apply tc_nil; lia | lia] | lia].
      * lia.
    + lia.
    + lia.
Qed.
End piece.

(* ================================================================== the two weights *)
Lemma w_sec_range : forall x, 0 <= w_sec x <= 1.
Proof. intros x. unfold w_sec. destruct (Psec x); lia. Qed.
(* a line's bytes (<= 6001) are a primary request *)
Lemma w_sec_small : forall x, 1 <= x <= 6001 -> 1 * w_sec x <= 0 * x.
Proof. intros x Hx. unfold w_sec. rewrite is_sec_iff by lia. destruct (Z.leb_spec 64513 x); lia. Qed.
Lemma w_cls_range : forall c x, 0 <= w_cls c x <= 1.
Proof. intros c x. unfold w_cls. destruct (PresetRoom.in_cls c x); lia. Qed.
(* a request of class c is at least lo c bytes *)
Lemma w_cls_small : forall c x, 1 <= x <= 6001 -> PresetRoom.lo c * w_cls c x <= 1 * x.
Proof.
  intros c x Hx. unfold w_cls. pose proof (PresetRoom.lo_pos c).
  destruct (PresetRoom.in_cls c x) eqn:E; [pose proof (PresetRoom.lo_le c x ltac:(lia) E); lia | lia].
Qed.
(* the least request of the batch class (needed size in (6144, 8192]) *)
Lemma lo_24 : PresetRoom.lo PresetRoom.K_BATCH_CLASS = 5889.
Proof. vm_compute. reflexivity. Qed.
(* a Theorem Labs lane's per-class limit (rl_prim_ok, 00:28Z): RL_PRIM c := 2^31 / class_size c *)
Definition RL_PRIM (c : Z) : Z := 2 ^ 31 / PresetRoom.size_of_class c.

(* the stream bytes a drain of entry e reading source h still reads: the pending bytes and the relay's unfinished
   line when it keeps it (fr_pair_cost without keys_total) *)
Definition pair_bytes (e : rentry) (h : hsrc) : Z :=
  Z.of_nat (length (pending_stream h)) + (if re_skip e =? 0 then Z.of_nat (length (re_U e)) else 0).

Lemma pair_bytes_nonneg : forall e h, 0 <= pair_bytes e h.
Proof. intros e h. unfold pair_bytes. destruct (re_skip e =? 0); lia. Qed.

(* fr_pair_ok's relay / splitter clause (re_eof = 0): the splitter's partial line is the relay's, so a drain reads
   2 * pair_bytes, and the splitter's lines are short *)
Lemma tc_bytes_init : forall NO CAP e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  tc_bytes (drain_b_c.drain_init NO CAP e h) = 2 * pair_bytes e h.
Proof.
  intros NO CAP e h Hsk Ho Hu. unfold tc_bytes, tp_R, tp_U, pair_bytes. rewrite rm3_dstr_init, RelayCap.rc_length_bzs.
  unfold drain_b_c.drain_init. tc_projg. unfold SlotReads.wcost, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  rewrite <- Ho. destruct Hsk as [E|E].
  - pose proof (Hu E) as Eu. rewrite E. cbn [Z.eqb]. rewrite <- Eu, RelayCap.rc_length_bzs. lia.
  - rewrite E. cbn [Z.eqb Pos.eqb]. lia.
Qed.
Lemma tc_ref_state : forall e h, (re_skip e = 0 \/ re_skip e = 1) -> re_skip e = hs_overlong h ->
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) -> Z.of_nat (length (re_U e)) <= APARTIAL ->
  tc_ref (hs_state h).
Proof.
  intros e h Hsk Ho Hu HU. unfold tc_ref, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  rewrite <- Ho. destruct Hsk as [E|E].
  - right. rewrite <- (Hu E), RelayCap.rc_length_bzs. unfold APARTIAL in HU. lia.
  - left. rewrite E. reflexivity.
Qed.

(* ================================================================== at the instance *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the relay's table has at most 4 entries: fr_relay pairs each with a distinct slot < 4 *)
Lemma fr_RINV_es_le : forall cx t m, fr_RINV cx t m -> (length (lm_es m) <= 4)%nat.
Proof.
  intros cx t m (_ & HR & _). destruct HR as (_ & _ & _ & _ & hj & HF & HNDs & _).
  rewrite (Forall2_length HF), <- (length_map snd hj).
  assert (I : incl (map snd hj) (seq 0 4)).
  { intros x Hx. apply in_map_iff in Hx as (p & <- & Hp).
    destruct (fr_Forall2_r _ _ _ _ _ HF p Hp) as (e & _ & (H4 & _)). apply in_seq. lia. }
  apply NoDup_ListNoDup in HNDs.
  pose proof (NoDup_incl_length HNDs I) as L. rewrite length_seq in L. exact L.
Qed.

(* the facts of the drained pair the walk needs, from fr_RINV and the pick (fr_pair_ok, ReplyRINV.v:153-172) *)
Lemma tc_dr_facts : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  0 <= hs_off h /\ tc_ref (hs_state h) /\
  (forall NO CAP, tc_bytes (drain_b_c.drain_init NO CAP (nth j (lm_es m) dr_e0) h) =
                  2 * pair_bytes (nth j (lm_es m) dr_e0) h) /\
  pair_bytes (nth j (lm_es m) dr_e0) h <= SlotInv.WRITE_MAX * t + APARTIAL.
Proof.
  intros cx t m si h j HRI Hpick Hj Hfdj Heof HU.
  destruct (dpre_pair cx t m si h j HRI Hpick Hj Hfdj) as (Hp & Hent & _).
  destruct Hp as (_ & _ & _ & Hre & _ & _ & _ & _ & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct Hent as (_ & _ & _ & _ & Hsk).
  destruct (Hre Heof) as (S1 & W1).
  split; [exact Hoff|]. split; [exact (tc_ref_state _ h Hsk S1 W1 HU)|]. split.
  - intros NO CAP. exact (tc_bytes_init NO CAP _ h Hsk S1 W1).
  - unfold pair_bytes. destruct (re_skip (nth j (lm_es m) dr_e0) =? 0); lia.
Qed.
Lemma tc_out_pos : forall m, (forall b, In b (aout_blks (lm_cap m) (lm_out m)) -> 0 <= snd b) -> 0 <= lm_cap m.
Proof.
  intros m H. destruct (Z.eqb_spec (lm_cap m) 0) as [E|E]; [lia|].
  apply (H (lm_out m, lm_cap m)). unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
Qed.

(* ---- part 1, drain: the premises of ReplyTrPeak.fr_LS_drain_pre_c5p that the counts need (fr_LS, dr_at_op and
   0 <= t < OPS_MAX are not needed) *)
Lemma fr_LS_drain_sec_peak : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  tr_peak_w w_sec
    (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <= 5.
Proof.
  intros cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP.
  destruct (tc_dr_facts cx t m si h j HRI Hpick Hj Hfdj Heof HU) as (Hoff & Href & _ & _).
  assert (Hcap : 0 <= lm_cap m).
  { apply tc_out_pos. intros b Hb. apply Z.lt_le_incl, HXP, in_or_app. right. apply in_or_app. right. exact Hb. }
  pose proof (tc_dr w_sec 1 0 w_sec_range ltac:(lia) ltac:(lia) w_sec_small (lm_c m) (lm_mx m)
                (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h Hcap Hoff Href) as H.
  lia.
Qed.
Lemma fr_LS_drain_cls_peak : forall c cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  PresetRoom.lo c *
    tr_peak_w (w_cls c)
      (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <=
    5 * PresetRoom.lo c + 2 * pair_bytes (nth j (lm_es m) dr_e0) h.
Proof.
  intros c cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP.
  destruct (tc_dr_facts cx t m si h j HRI Hpick Hj Hfdj Heof HU) as (Hoff & Href & Hdb & _).
  assert (Hcap : 0 <= lm_cap m).
  { apply tc_out_pos. intros b Hb. apply Z.lt_le_incl, HXP, in_or_app. right. apply in_or_app. right. exact Hb. }
  pose proof (PresetRoom.lo_pos c) as Hlo.
  pose proof (tc_dr (w_cls c) (PresetRoom.lo c) 1 (w_cls_range c) ltac:(lia) ltac:(lia) (w_cls_small c) (lm_c m)
                (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h Hcap Hoff Href) as H.
  rewrite Hdb in H. lia.
Qed.
(* the same, divided out: at most 5 + 2 pair_bytes / lo c, and pair_bytes <= WRITE_MAX * t + APARTIAL *)
Lemma tc_div : forall lo p X, 1 <= lo -> lo * p <= 5 * lo + X -> p <= 5 + X / lo.
Proof.
  intros lo p X Hlo H. rewrite <- (Z.div_add_l 5 lo X) by lia. apply Z.div_le_lower_bound; lia.
Qed.
Lemma fr_LS_drain_cls_peak_div : forall c cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  tr_peak_w (w_cls c)
      (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <=
    5 + 2 * pair_bytes (nth j (lm_es m) dr_e0) h / PresetRoom.lo c /\
  pair_bytes (nth j (lm_es m) dr_e0) h <= SlotInv.WRITE_MAX * t + APARTIAL.
Proof.
  intros c cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP.
  pose proof (fr_LS_drain_cls_peak c cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP) as H.
  destruct (tc_dr_facts cx t m si h j HRI Hpick Hj Hfdj Heof HU) as (_ & _ & _ & Hpb).
  split; [apply (tc_div _ _ _ (PresetRoom.lo_pos c) H) | exact Hpb].
Qed.
(* the batch class at t < OPS_MAX: at most 11,380 *)
Lemma fr_LS_drain_cls24_peak : forall cx t m si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  tr_peak_w (w_cls PresetRoom.K_BATCH_CLASS)
      (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <= 11380.
Proof.
  intros cx t m si h j HRI Hpick Hj Hfdj Heof Ht HU HXP.
  destruct (fr_LS_drain_cls_peak_div PresetRoom.K_BATCH_CLASS cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP)
    as (H & Hpb).
  rewrite lo_24 in H. unfold SlotInv.WRITE_MAX, APARTIAL, OPS_MAX in *.
  assert (D : 2 * pair_bytes (nth j (lm_es m) dr_e0) h / 5889 <= 2 * (65535 * 511 + 6000) / 5889)
    by (apply Z.div_le_mono; lia).
  change (2 * (65535 * 511 + 6000) / 5889) with 11375 in D. lia.
Qed.

(* ---- part 1, remove: the premises of ReplyTrPeak.fr_LS_rm_rr_pre_c3p that the counts need *)
Lemma tc_rm_facts : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  find (fun e => re_fd e =? hs_fd h) (lm_es m) = Some (rm_ent m j0) /\
  0 <= hs_off h /\ pair_bytes (rm_ent m j0) h <= SlotInv.WRITE_MAX * t + APARTIAL /\
  (re_eof (rm_ent m j0) = 0 -> tc_ref (hs_state h) /\
     forall NO CAP, tc_bytes (drain_b_c.drain_init NO CAP (rm_ent m j0) h) = 2 * pair_bytes (rm_ent m j0) h).
Proof.
  intros cx t m si h j0 HRI Hat HU.
  destruct (rm3_pair cx t m si h j0 HRI Hat) as (HP & HE & _ & _).
  pose proof Hat as (_ & _ & _ & _ & _ & _ & Hj0 & Hfd & Hfirst).
  destruct HP as (_ & _ & _ & Hre & _ & _ & _ & _ & _ & Hpe & Hoff). cbn [fst snd] in *.
  destruct HE as (_ & _ & _ & _ & Hsk).
  split; [unfold rm_ent; apply rrp_find; [exact Hj0 | exact Hfd | exact Hfirst]|].
  split; [exact Hoff|]. split; [unfold pair_bytes; destruct (re_skip (rm_ent m j0) =? 0); lia|].
  intros Eo. destruct (Hre Eo) as (S1 & W1).
  split; [exact (tc_ref_state _ h Hsk S1 W1 HU)|].
  intros NO CAP. exact (tc_bytes_init NO CAP _ h Hsk S1 W1).
Qed.
Lemma tc_rm_cap : forall m, (forall b, In b (model_blks m) -> 0 <= snd b) -> 0 <= lm_cap m.
Proof. intros m Hpos. apply tc_out_pos. intros b Hb. exact (Hpos b (rm3_in_model_out m b Hb)). Qed.

Lemma fr_LS_rm_sec_peak : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  tr_peak_w w_sec (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= 5.
Proof.
  intros cx t m si h j0 HRI Hat HU Hpos.
  destruct (tc_rm_facts cx t m si h j0 HRI Hat HU) as (Hf & Hoff & _ & HJ).
  pose proof (tc_rr w_sec 1 0 w_sec_range ltac:(lia) ltac:(lia) w_sec_small (lm_c m) (lm_mx m)
                (Z.of_nat (length (lm_O m))) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hf (tc_rm_cap m Hpos)
                (fun Eo => conj Hoff (proj1 (HJ Eo)))) as H.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr. revert H. destruct (re_eof (rm_ent m j0) =? 0); intros H; lia.
Qed.
Lemma fr_LS_rm_cls_peak : forall c cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  PresetRoom.lo c * tr_peak_w (w_cls c) (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <=
    5 * PresetRoom.lo c + 2 * pair_bytes (rm_ent m j0) h.
Proof.
  intros c cx t m si h j0 HRI Hat HU Hpos.
  destruct (tc_rm_facts cx t m si h j0 HRI Hat HU) as (Hf & Hoff & _ & HJ).
  pose proof (PresetRoom.lo_pos c) as Hlo. pose proof (pair_bytes_nonneg (rm_ent m j0) h) as Hpb0.
  pose proof (tc_rr (w_cls c) (PresetRoom.lo c) 1 (w_cls_range c) ltac:(lia) ltac:(lia) (w_cls_small c) (lm_c m)
                (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (hs_fd h) (lm_es m) h (rm_ent m j0) Hf
                (tc_rm_cap m Hpos) (fun Eo => conj Hoff (proj1 (HJ Eo)))) as H.
  unfold W_LLVMFuzzerTestOneInput_remove.rm_rr_tr. revert H. destruct (re_eof (rm_ent m j0) =? 0) eqn:Eo; intros H.
  - apply Z.eqb_eq in Eo. rewrite (proj2 (HJ Eo)) in H. lia.
  - lia.
Qed.
Lemma fr_LS_rm_cls_peak_div : forall c cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  tr_peak_w (w_cls c) (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <=
    5 + 2 * pair_bytes (rm_ent m j0) h / PresetRoom.lo c /\
  pair_bytes (rm_ent m j0) h <= SlotInv.WRITE_MAX * t + APARTIAL.
Proof.
  intros c cx t m si h j0 HRI Hat HU Hpos.
  pose proof (fr_LS_rm_cls_peak c cx t m si h j0 HRI Hat HU Hpos) as H.
  destruct (tc_rm_facts cx t m si h j0 HRI Hat HU) as (_ & _ & Hpb & _).
  split; [apply (tc_div _ _ _ (PresetRoom.lo_pos c) H) | exact Hpb].
Qed.
Lemma fr_LS_rm_cls24_peak : forall cx t m si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  tr_peak_w (w_cls PresetRoom.K_BATCH_CLASS) (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= 11380.
Proof.
  intros cx t m si h j0 HRI Hat Ht HU Hpos.
  destruct (fr_LS_rm_cls_peak_div PresetRoom.K_BATCH_CLASS cx t m si h j0 HRI Hat HU Hpos) as (H & Hpb).
  rewrite lo_24 in H. unfold SlotInv.WRITE_MAX, APARTIAL, OPS_MAX in *.
  assert (D : 2 * pair_bytes (rm_ent m j0) h / 5889 <= 2 * (65535 * 511 + 6000) / 5889)
    by (apply Z.div_le_mono; lia).
  change (2 * (65535 * 511 + 6000) / 5889) with 11375 in D. lia.
Qed.

(* ---- part 2: the per-call premise at drain's and relay_remove's calls *)
(* the secondary count at the cut is at most 593 (fr_LS3c_sec_cut, |hs| = 4, |es| <= 4, t <= 511) *)
Lemma tc_sec_cut : forall cx t m ly S, fr_LS3c B cx t m ly S -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> fr_RINV cx t m ->
  0 <= t < OPS_MAX -> cnt_sec (ablocks B ly S) <= 593.
Proof.
  intros cx t m ly S HLS Hm HRI Ht.
  pose proof (ReplyLSCntM.fr_LS3c_sec_cut B cx t m ly S HLS Hm) as C.
  pose proof (fr_RINV_es_le cx t m HRI) as E4.
  pose proof HRI as (_ & (Hhs & _) & _).
  assert (Z.of_nat (length (lm_hs m)) = 4) by (rewrite Hhs; reflexivity).
  unfold SEC0, OPS_MAX in *. lia.
Qed.
Lemma fr_LS3c_drain_sec_call : forall cx t m ly S si h j,
  fr_LS3c B cx t m ly S -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  cnt_sec (ablocks B ly S) +
    tr_peak_w w_sec (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= 1024.
Proof.
  intros cx t m ly S si h j HLS Hm HRI Hpick Hj Hfdj Heof Ht HU HXP.
  pose proof (tc_sec_cut cx t m ly S HLS Hm HRI Ht).
  pose proof (fr_LS_drain_sec_peak cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP). lia.
Qed.
Lemma fr_LS3c_rm_sec_call : forall cx t m ly S si h j0,
  fr_LS3c B cx t m ly S -> ReplyCnt.msz_ok (lm_es m) (lm_hs m) -> fr_RINV cx t m -> rm_at cx m si h j0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  cnt_sec (ablocks B ly S) + tr_peak_w w_sec (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= 1024.
Proof.
  intros cx t m ly S si h j0 HLS Hm HRI Hat Ht HU Hpos.
  pose proof (tc_sec_cut cx t m ly S HLS Hm HRI Ht).
  pose proof (fr_LS_rm_sec_peak cx t m si h j0 HRI Hat HU Hpos). lia.
Qed.

(* the class counts: the state's class count is the one named hypothesis Hcls (its model part is part 2's
   potentials' job); LIM := RL_PRIM c for a primary class, 2^15 for ccnt24 *)
Lemma fr_LS3c_drain_cls_call : forall c LIM cx t m ly S si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  forall Hcls : cnt_cls c (ablocks B ly S) <= LIM - 5 - 2 * pair_bytes (nth j (lm_es m) dr_e0) h / PresetRoom.lo c,
  cnt_cls c (ablocks B ly S) +
    tr_peak_w (w_cls c)
      (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <= LIM.
Proof.
  intros c LIM cx t m ly S si h j HRI Hpick Hj Hfdj Heof HU HXP Hcls.
  destruct (fr_LS_drain_cls_peak_div c cx t m si h j HRI Hpick Hj Hfdj Heof HU HXP) as (H & _). lia.
Qed.
Lemma fr_LS3c_rm_cls_call : forall c LIM cx t m ly S si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  forall Hcls : cnt_cls c (ablocks B ly S) <= LIM - 5 - 2 * pair_bytes (rm_ent m j0) h / PresetRoom.lo c,
  cnt_cls c (ablocks B ly S) + tr_peak_w (w_cls c) (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= LIM.
Proof.
  intros c LIM cx t m ly S si h j0 HRI Hat HU Hpos Hcls.
  destruct (fr_LS_rm_cls_peak_div c cx t m si h j0 HRI Hat HU Hpos) as (H & _). lia.
Qed.
(* rl_prim_ok's limit at the calls *)
Lemma fr_LS3c_drain_prim_call : forall c cx t m ly S si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  forall Hcls : cnt_cls c (ablocks B ly S) <=
                RL_PRIM c - 5 - 2 * pair_bytes (nth j (lm_es m) dr_e0) h / PresetRoom.lo c,
  cnt_cls c (ablocks B ly S) +
    tr_peak_w (w_cls c)
      (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <= RL_PRIM c.
Proof.
  intros c cx t m ly S si h j HRI Hpick Hj Hfdj Heof HU HXP Hcls.
  exact (fr_LS3c_drain_cls_call c (RL_PRIM c) cx t m ly S si h j HRI Hpick Hj Hfdj Heof HU HXP Hcls).
Qed.
Lemma fr_LS3c_rm_prim_call : forall c cx t m ly S si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  forall Hcls : cnt_cls c (ablocks B ly S) <= RL_PRIM c - 5 - 2 * pair_bytes (rm_ent m j0) h / PresetRoom.lo c,
  cnt_cls c (ablocks B ly S) + tr_peak_w (w_cls c) (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <= RL_PRIM c.
Proof.
  intros c cx t m ly S si h j0 HRI Hat HU Hpos Hcls.
  exact (fr_LS3c_rm_cls_call c (RL_PRIM c) cx t m ly S si h j0 HRI Hat HU Hpos Hcls).
Qed.
(* ccnt24 <= 2^15 at the calls, from the state's batch-class count *)
Lemma fr_LS3c_drain_cnt24_call : forall cx t m ly S si h j,
  fr_RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  forall Hcls : cnt24 (ablocks B ly S) <= 2 ^ 15 - 11380,
  cnt24 (ablocks B ly S) +
    tr_peak_w (w_cls PresetRoom.K_BATCH_CLASS)
      (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) <= 2 ^ 15.
Proof.
  intros cx t m ly S si h j HRI Hpick Hj Hfdj Heof Ht HU HXP Hcls.
  pose proof (fr_LS_drain_cls24_peak cx t m si h j HRI Hpick Hj Hfdj Heof Ht HU HXP). lia.
Qed.
Lemma fr_LS3c_rm_cnt24_call : forall cx t m ly S si h j0,
  fr_RINV cx t m -> rm_at cx m si h j0 -> 0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (rm_ent m j0))) <= APARTIAL ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  forall Hcls : cnt24 (ablocks B ly S) <= 2 ^ 15 - 11380,
  cnt24 (ablocks B ly S) + tr_peak_w (w_cls PresetRoom.K_BATCH_CLASS) (W_LLVMFuzzerTestOneInput_remove.rm_rr_tr m h) <=
    2 ^ 15.
Proof.
  intros cx t m ly S si h j0 HRI Hat Ht HU Hpos Hcls.
  pose proof (fr_LS_rm_cls24_peak cx t m si h j0 HRI Hat Ht HU Hpos). lia.
Qed.
(* the model form: fr_LS3c's fr_CNT bounds the rest by CLS0 and the input is one block, so Hcls follows from the
   model's class count *)
Lemma tc_cnt_cls_input : forall c (cx : lfcx), cnt_cls c (input_blks cx) <= 1.
Proof.
  intros c cx. unfold input_blks. destruct (c_n cx =? 0); [rewrite cnt_cls_nil; lia|].
  rewrite cnt_cls_cons, cnt_cls_nil. destruct (PresetRoom.in_cls c (c_n cx)); lia.
Qed.
Lemma fr_LS3c_cls_of_model : forall c LIM X cx t m ly S, fr_LS3c B cx t m ly S ->
  cnt_cls c (model_blks m) + 1 + CLS0 <= LIM - X -> cnt_cls c (ablocks B ly S) <= LIM - X.
Proof.
  intros c LIM X cx t m ly S (_ & (_ & C2 & _)) H. pose proof (C2 c). pose proof (tc_cnt_cls_input c cx). lia.
Qed.
End inst.
