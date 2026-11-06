(* proves no function (kind: invariant lemma): the image-B port of C3's trace-peak lemma kit: the peak measure's
   algebra and the bounds on the summed positive growth of drain's and relay_remove's request traces *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Ported from A at a working branch 9f4cbd12a19 lib/A/ReplyTrPeak.v (A below), names and statements
   kept, over lib/B's records and request traces (lib/B/W_contract.v of a working branch
   61e610e6176: tr_max, tr_alloc, sl_alloc, sl_cap, sl_run_fin, dr_tr, dr_fin, dr_live, rr_tr have A's text) and the
   plain model files of lib/Prog (byte-identical in both trees).  For what the measure is and why C3 uses it, read
   A's header (A :3-67).
     A :136-165 tr_pos, tr_room, tr_olds_ok, tr_sizes_ok; A :167-342 the Section peak (the measure's algebra, the
       per-event invariant, soundness and exactness, tr_peak_le_alloc, tr_peak_le_pos, tr_window);
     A :345-402 the allocator rules' posts keep the invariant (tr_peak_after_malloc .. tr_peak_after_realloc);
     A :462-548 the callees' sum-form rooms (tp_sl_alloc .. tr_peak_sl_2cap);
     A :552-874 a drain's and relay_remove's summed positive growth (tp_kdef .. tp_rr);
     A :881-896 tp_pos_entry, tp_pos_out.
   tr_peak and tr_net are lib/B/ReplyLSBArms.v's copies (A :120-134, the same text).
   Not ported: the probe (A :404-459, a vm-checked sanity example on A's instance, no lemma here reads it) and the
   drain arm's instance lemmas fr_LS_drain_pre_c5p / _slack (A :898-958: they read A's drain arm, which lib/B does
   not have).  The model facts A reads from lib/A/ReplyLSDrainPre.v, ReplyLSRemove3.v, ReplyLSRrPre.v (dpre_chunk,
   dpre_gesture_len, rm3_chunk_mass, rm3_dstr, rm3_dstr0, rm3_dstr_init, rm3_no_fin, rm3_kw, rm3_kt_kw, rrp_fin_kw)
   are lib/B/ReplyLSBDrainPre.v's ports.
   A -> B SWAPS: the imports as lib/B/ReplyLSBDrainPre.v, which this file Imports; A's ReplyLS.v zsum_map_nonneg is
   lib/B/ReplyLSBArms.v bt_zsum_map_nonneg; RelayKeys names are qualified. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the measure (A :136-165) *)
(* the positive parts of the requests' net changes, summed (a bound on the live bytes' rise, for the proofs) *)
Definition tr_pos {P : Type} (tr : list (RelayRunT.rev P)) : Z :=
fold_right (fun ev acc =>
  match ev with
  | RelayRunT.RMalloc n => Z.max 0 n
  | RelayRunT.RFree k _ => Z.max 0 (- k)
  | RelayRunT.RRealloc k n _ => Z.max 0 (n - k)
  end + acc) 0 tr.
(* every request finds room on top of the live bytes bb at its point: the allocator rules' live-bytes premises in
   order, the live bytes moving as the rules' posts move them *)
Fixpoint tr_room {P : Type} (bb : Z) (tr : list (RelayRunT.rev P)) : Prop :=
  match tr with
  | [] => True
  | RelayRunT.RMalloc n :: r => bb + n <= LIVE_MAX /\ tr_room (bb + n) r
  | RelayRunT.RFree k _ :: r => tr_room (bb - k) r
  | RelayRunT.RRealloc k n _ :: r => bb + n <= LIVE_MAX /\ tr_room (bb - k + n) r
  end.
(* the sizes a trace frees (a free's size, a realloc's old size) are not negative *)
Definition tr_olds_ok {P : Type} (tr : list (RelayRunT.rev P)) : Prop :=
  Forall (fun ev => match ev with
    | RelayRunT.RMalloc _ => True
    | RelayRunT.RFree k _ => 0 <= k
    | RelayRunT.RRealloc k _ _ => 0 <= k
    end) tr.
(* every size in a trace is not negative *)
Definition tr_sizes_ok {P : Type} (tr : list (RelayRunT.rev P)) : Prop :=
  Forall (fun ev => match ev with
    | RelayRunT.RMalloc n => 0 <= n
    | RelayRunT.RFree k _ => 0 <= k
    | RelayRunT.RRealloc k n _ => 0 <= k /\ 0 <= n
    end) tr.

Section peak.
Context {P : Type}.
Local Notation rv := (RelayRunT.rev P).

Lemma tr_peak_nil : tr_peak (@nil rv) = 0.
Proof. reflexivity. Qed.
Lemma tr_peak_malloc : forall n (r : list rv), tr_peak (RelayRunT.RMalloc n :: r) = Z.max 0 (n + tr_peak r).
Proof. reflexivity. Qed.
Lemma tr_peak_free : forall k x (r : list rv), tr_peak (RelayRunT.RFree k x :: r) = Z.max 0 (tr_peak r - k).
Proof. reflexivity. Qed.
Lemma tr_peak_realloc : forall k n x (r : list rv),
  tr_peak (RelayRunT.RRealloc k n x :: r) = Z.max 0 (Z.max n (n - k + tr_peak r)).
Proof. reflexivity. Qed.
Lemma tr_net_cons : forall (ev : rv) r, tr_net (ev :: r) =
  match ev with RelayRunT.RMalloc n => n | RelayRunT.RFree k _ => - k | RelayRunT.RRealloc k n _ => n - k end +
  tr_net r.
Proof. reflexivity. Qed.
Lemma tr_pos_cons : forall (ev : rv) r, tr_pos (ev :: r) =
  match ev with
  | RelayRunT.RMalloc n => Z.max 0 n | RelayRunT.RFree k _ => Z.max 0 (- k) | RelayRunT.RRealloc k n _ => Z.max 0 (n - k)
  end + tr_pos r.
Proof. reflexivity. Qed.
Lemma tr_alloc_cons' : forall (ev : rv) r, tr_alloc (ev :: r) =
  match ev with RelayRunT.RMalloc n => n | RelayRunT.RFree _ _ => 0 | RelayRunT.RRealloc _ n _ => n end + tr_alloc r.
Proof. reflexivity. Qed.
Lemma tr_max_cons' : forall (ev : rv) r, tr_max (ev :: r) =
  match ev with
  | RelayRunT.RMalloc n => Z.max n (tr_max r) | RelayRunT.RFree _ _ => tr_max r
  | RelayRunT.RRealloc _ n _ => Z.max n (tr_max r)
  end.
Proof. reflexivity. Qed.
Lemma tr_pos_nil : tr_pos (@nil rv) = 0.
Proof. reflexivity. Qed.
Lemma tr_pos_malloc : forall n (r : list rv), tr_pos (RelayRunT.RMalloc n :: r) = Z.max 0 n + tr_pos r.
Proof. reflexivity. Qed.
Lemma tr_pos_free : forall k x (r : list rv), tr_pos (RelayRunT.RFree k x :: r) = Z.max 0 (- k) + tr_pos r.
Proof. reflexivity. Qed.
Lemma tr_pos_realloc : forall k n x (r : list rv), tr_pos (RelayRunT.RRealloc k n x :: r) = Z.max 0 (n - k) + tr_pos r.
Proof. reflexivity. Qed.
Lemma tr_max_nil : tr_max (@nil rv) = 0.
Proof. reflexivity. Qed.
Lemma tr_max_malloc : forall n (r : list rv), tr_max (RelayRunT.RMalloc n :: r) = Z.max n (tr_max r).
Proof. reflexivity. Qed.
Lemma tr_max_realloc : forall k n x (r : list rv), tr_max (RelayRunT.RRealloc k n x :: r) = Z.max n (tr_max r).
Proof. reflexivity. Qed.
Lemma tr_alloc_nil : tr_alloc (@nil rv) = 0.
Proof. reflexivity. Qed.
Lemma tr_alloc_malloc : forall n (r : list rv), tr_alloc (RelayRunT.RMalloc n :: r) = n + tr_alloc r.
Proof. reflexivity. Qed.
Lemma tr_alloc_realloc : forall k n x (r : list rv), tr_alloc (RelayRunT.RRealloc k n x :: r) = n + tr_alloc r.
Proof. reflexivity. Qed.

Lemma tr_peak_nonneg : forall (tr : list rv), 0 <= tr_peak tr.
Proof.
  intros tr. destruct tr as [|ev r]; [rewrite tr_peak_nil; lia|].
  destruct ev; [rewrite tr_peak_malloc | rewrite tr_peak_free | rewrite tr_peak_realloc]; lia.
Qed.
Lemma tr_pos_nonneg : forall (tr : list rv), 0 <= tr_pos tr.
Proof. induction tr as [|ev r IH]; [cbn; lia|]. rewrite tr_pos_cons. destruct ev; lia. Qed.
Lemma tr_max_nonneg' : forall (tr : list rv), 0 <= tr_max tr.
Proof. induction tr as [|ev r IH]; [cbn; lia|]. rewrite tr_max_cons'. destruct ev; lia. Qed.

Lemma tr_net_app : forall (a b : list rv), tr_net (a ++ b) = tr_net a + tr_net b.
Proof.
  induction a as [|ev a IH]; intros b; [cbn [app]; change (tr_net (@nil rv)) with 0; lia|].
  rewrite <- app_comm_cons, !tr_net_cons, IH. lia.
Qed.
Lemma tr_pos_app : forall (a b : list rv), tr_pos (a ++ b) = tr_pos a + tr_pos b.
Proof.
  induction a as [|ev a IH]; intros b; [cbn [app]; change (tr_pos (@nil rv)) with 0; lia|].
  rewrite <- app_comm_cons, !tr_pos_cons, IH. lia.
Qed.
Lemma tr_alloc_app' : forall (a b : list rv), tr_alloc (a ++ b) = tr_alloc a + tr_alloc b.
Proof.
  induction a as [|ev a IH]; intros b; [cbn [app]; change (tr_alloc (@nil rv)) with 0; lia|].
  rewrite <- app_comm_cons, !tr_alloc_cons', IH. lia.
Qed.
Lemma tr_max_app' : forall (a b : list rv), tr_max (a ++ b) = Z.max (tr_max a) (tr_max b).
Proof.
  intros a b. pose proof (tr_max_nonneg' b) as Hb.
  induction a as [|ev a IH]; [cbn [app]; change (tr_max (@nil rv)) with 0; lia|].
  rewrite <- app_comm_cons, !tr_max_cons'. destruct ev; lia.
Qed.

(* composition: the peak of a then b is a's, or a's net change and b's peak *)
Lemma tr_peak_app : forall (a b : list rv), tr_peak (a ++ b) = Z.max (tr_peak a) (tr_net a + tr_peak b).
Proof.
  intros a b. pose proof (tr_peak_nonneg b) as Hb.
  induction a as [|ev a IH]; [cbn [app]; rewrite tr_peak_nil; change (tr_net (@nil rv)) with 0; lia|].
  pose proof (tr_peak_nonneg a) as Ha. pose proof (tr_peak_nonneg (a ++ b)) as Hab.
  rewrite <- app_comm_cons, tr_net_cons.
  destruct ev; [rewrite !tr_peak_malloc | rewrite !tr_peak_free | rewrite !tr_peak_realloc]; rewrite IH; lia.
Qed.
(* a caller's split: a callee's window w after the requests a, before the requests b *)
Lemma tr_peak_mid : forall (a w b : list rv), tr_net a + tr_peak w <= tr_peak (a ++ w ++ b).
Proof.
  intros a w b. rewrite (tr_peak_app a (w ++ b)), (tr_peak_app w b). lia.
Qed.
Lemma tr_peak_prefix : forall (a b : list rv), tr_peak a <= tr_peak (a ++ b).
Proof. intros a b. rewrite tr_peak_app. lia. Qed.
Lemma tr_net_le_peak : forall (a b : list rv), tr_net a <= tr_peak (a ++ b).
Proof. intros a b. rewrite tr_peak_app. pose proof (tr_peak_nonneg b). lia. Qed.

(* ---- the per-event invariant bb + tr_peak (rest) <= L, one request at a time *)
Lemma tr_peak_step_malloc : forall bb L n (r : list rv), bb + tr_peak (RelayRunT.RMalloc n :: r) <= L ->
  bb + n <= L /\ (bb + n) + tr_peak r <= L.
Proof. intros bb L n r H. rewrite tr_peak_malloc in H. pose proof (tr_peak_nonneg r). lia. Qed.
Lemma tr_peak_step_free : forall bb L k x (r : list rv), bb + tr_peak (RelayRunT.RFree k x :: r) <= L ->
  (bb - k) + tr_peak r <= L.
Proof. intros bb L k x r H. rewrite tr_peak_free in H. lia. Qed.
Lemma tr_peak_step_realloc : forall bb L k n x (r : list rv), bb + tr_peak (RelayRunT.RRealloc k n x :: r) <= L ->
  bb + n <= L /\ (bb - k + n) + tr_peak r <= L.
Proof. intros bb L k n x r H. rewrite tr_peak_realloc in H. lia. Qed.

(* soundness: the peak premise gives every request's premise, in order *)
Lemma tr_peak_room : forall (tr : list rv) bb, bb + tr_peak tr <= LIVE_MAX -> tr_room bb tr.
Proof.
  induction tr as [|ev r IH]; intros bb H; [exact I|].
  destruct ev as [n|k x|k n x]; cbn [tr_room].
  - destruct (tr_peak_step_malloc bb LIVE_MAX n r H) as [H1 H2]. split; [exact H1 | apply IH; exact H2].
  - apply IH. exact (tr_peak_step_free bb LIVE_MAX k x r H).
  - destruct (tr_peak_step_realloc bb LIVE_MAX k n x r H) as [H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
(* exactness: it asks nothing more than the requests' premises *)
Lemma tr_room_peak : forall (tr : list rv) bb, tr_olds_ok tr -> bb <= LIVE_MAX -> tr_room bb tr ->
  bb + tr_peak tr <= LIVE_MAX.
Proof.
  induction tr as [|ev r IH]; intros bb HO Hb HR; [rewrite tr_peak_nil; lia|].
  inversion HO as [|? ? Hev HO']; subst.
  destruct ev as [n|k x|k n x]; cbn [tr_room] in HR.
  - destruct HR as [H1 H2]. specialize (IH (bb + n) HO' H1 H2). rewrite tr_peak_malloc. lia.
  - cbn in Hev. specialize (IH (bb - k) HO' ltac:(lia) HR). rewrite tr_peak_free. lia.
  - cbn in Hev. destruct HR as [H1 H2]. specialize (IH (bb - k + n) HO' ltac:(lia) H2). rewrite tr_peak_realloc. lia.
Qed.
Lemma tr_peak_iff_room : forall (tr : list rv) bb, tr_olds_ok tr -> bb <= LIVE_MAX ->
  (bb + tr_peak tr <= LIVE_MAX <-> tr_room bb tr).
Proof. intros tr bb HO Hb. split; [apply tr_peak_room | apply tr_room_peak; assumption]. Qed.
(* tr_room is RelayRunT.room_from at the live-bytes instance (malloc +n, free -k, realloc -k +n, room bb + n <= LIVE_MAX) *)
Lemma tr_room_from : forall (pdef : P) (qs : list P) (tr : list rv) bb j,
  RelayRunT.room_from Z P pdef (fun b n => b + n) (fun b k _ => b - k) (fun b k n _ _ => b - k + n)
    (fun b n => b + n <= LIVE_MAX) qs bb j tr <-> tr_room bb tr.
Proof.
  intros pdef qs tr. induction tr as [|ev r IH]; intros bb j; [cbn; tauto|].
  destruct ev; cbn [RelayRunT.room_from tr_room]; rewrite IH; tauto.
Qed.

(* sanity: the peak is never above the sum (traces with nonnegative sizes), so the new premise is weaker *)
Lemma tr_alloc_nonneg_ok : forall (tr : list rv), tr_sizes_ok tr -> 0 <= tr_alloc tr.
Proof.
  induction tr as [|ev r IH]; intros HS; [cbn; lia|]. inversion HS as [|? ? Hev HS']; subst.
  rewrite tr_alloc_cons'. specialize (IH HS'). destruct ev; cbn in Hev; lia.
Qed.
Lemma tr_peak_le_alloc : forall (tr : list rv), tr_sizes_ok tr -> tr_peak tr <= tr_alloc tr.
Proof.
  induction tr as [|ev r IH]; intros HS; [cbn; lia|]. inversion HS as [|? ? Hev HS']; subst.
  specialize (IH HS'). pose proof (tr_alloc_nonneg_ok r HS'). rewrite tr_alloc_cons'.
  destruct ev; cbn in Hev; [rewrite tr_peak_malloc | rewrite tr_peak_free | rewrite tr_peak_realloc]; lia.
Qed.
(* the bound the instance proofs use: the peak is at most the summed positive growth and the largest request *)
Lemma tr_peak_le_pos : forall (tr : list rv), tr_peak tr <= tr_pos tr + tr_max tr.
Proof.
  induction tr as [|ev r IH]; [cbn; lia|].
  pose proof (tr_pos_nonneg r). pose proof (tr_max_nonneg' r). rewrite tr_pos_cons, tr_max_cons'.
  destruct ev; [rewrite tr_peak_malloc | rewrite tr_peak_free | rewrite tr_peak_realloc]; lia.
Qed.

(* (b): a callee's window w whose own sum is within its peak and largest request gets its sum-form room from the
   caller's `B + tr_peak tr + tr_max tr <= L`, at live bytes bb <= B + (net of the requests before it) *)
Lemma tr_window : forall (a w b : list rv) B0 bb L, bb <= B0 + tr_net a ->
  B0 + tr_peak (a ++ w ++ b) + tr_max (a ++ w ++ b) <= L -> tr_alloc w <= tr_peak w + tr_max w ->
  bb + tr_alloc w <= L.
Proof.
  intros a w b B0 bb L Hb HL Hw. pose proof (tr_peak_mid a w b) as M.
  rewrite !tr_max_app' in HL. pose proof (tr_max_nonneg' a). pose proof (tr_max_nonneg' b). lia.
Qed.
End peak.

(* ================================================================== the rules' posts keep the invariant (A :345-402) *)
Section rules.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Context {P : Type}.
Local Notation rv := (RelayRunT.rev P).

Lemma tp_bb_app : forall ly S ly2 S2 l, ablocks B ly2 S2 = ablocks B ly S ++ l -> blocks_bytes S2 = blocks_bytes S + bsum l.
Proof. intros ly S ly2 S2 l E. rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), E, bsum_app. lia. Qed.

(* malloc: amalloc_cf_rule's premise and post *)
Lemma tr_peak_after_malloc : forall ly S ly2 S2 res n (r : list rv),
  blocks_bytes S + tr_peak (RelayRunT.RMalloc n :: r) <= LIVE_MAX ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n)] ->
  blocks_bytes S + n <= LIVE_MAX /\ blocks_bytes S2 + tr_peak r <= LIVE_MAX.
Proof.
  intros ly S ly2 S2 res n r H E. rewrite (tp_bb_app ly S ly2 S2 _ E), bsum_cons, bsum_nil. cbn [snd].
  destruct (tr_peak_step_malloc _ _ n r H). split; lia.
Qed.
(* strndup: astrndup_cf_rule's premise and post, the request RMalloc (n + 1) *)
Lemma tr_peak_after_strndup : forall ly S ly2 S2 res n (r : list rv),
  blocks_bytes S + tr_peak (RelayRunT.RMalloc (n + 1) :: r) <= LIVE_MAX ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n + 1)] ->
  blocks_bytes S + (n + 1) <= LIVE_MAX /\ blocks_bytes S2 + tr_peak r <= LIVE_MAX.
Proof. intros ly S ly2 S2 res n r. apply tr_peak_after_malloc. Qed.
(* free: afree_cf_rule's post (no premise on the live bytes) *)
Lemma tr_peak_after_free : forall ly S ly2 S2 pa n x (r : list rv),
  blocks_bytes S + tr_peak (RelayRunT.RFree n x :: r) <= LIVE_MAX ->
  (exists l1 l2, ablocks B ly S = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
  blocks_bytes S2 + tr_peak r <= LIVE_MAX.
Proof.
  intros ly S ly2 S2 pa n x r H (l1 & l2 & E1 & E2).
  pose proof (tr_peak_step_free _ _ n x r H) as H1.
  rewrite (blocks_bytes_bsum B ly S), E1, bsum_app, bsum_cons in H1. cbn [snd] in H1.
  rewrite (blocks_bytes_bsum B ly2 S2), E2, bsum_app. lia.
Qed.
(* realloc (NULL, n): arealloc_cf_rule's premise and post, the request RMalloc n *)
Lemma tr_peak_after_realloc0 : forall ly S ly2 S2 res n (r : list rv),
  blocks_bytes S + tr_peak (RelayRunT.RMalloc n :: r) <= LIVE_MAX ->
  Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B ly S) ->
  blocks_bytes S + n <= LIVE_MAX /\ blocks_bytes S2 + tr_peak r <= LIVE_MAX.
Proof.
  intros ly S ly2 S2 res n r H HP. destruct (tr_peak_step_malloc _ _ n r H) as [H1 H2]. split; [exact H1|].
  rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP), bsum_cons. cbn [snd].
  rewrite (blocks_bytes_bsum B ly S) in H2. lia.
Qed.
(* realloc (p, n) of the live block (p, n0): arealloc_cf_rule's premise (n on top, the old block still live) and
   post *)
Lemma tr_peak_after_realloc : forall ly S ly2 S2 p n0 res n x (r : list rv),
  blocks_bytes S + tr_peak (RelayRunT.RRealloc n0 n x :: r) <= LIVE_MAX ->
  (exists l1 l2, ablocks B ly S = l1 ++ (p, n0) :: l2 /\ Permutation (ablocks B ly2 S2) ((res, n) :: l1 ++ l2)) ->
  blocks_bytes S + n <= LIVE_MAX /\ blocks_bytes S2 + tr_peak r <= LIVE_MAX.
Proof.
  intros ly S ly2 S2 p n0 res n x r H (l1 & l2 & E1 & HP).
  destruct (tr_peak_step_realloc _ _ n0 n x r H) as [H1 H2]. split; [exact H1|].
  rewrite (blocks_bytes_bsum B ly S), E1, bsum_app, bsum_cons in H2. cbn [snd] in H2.
  rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP), bsum_cons, bsum_app. cbn [snd]. lia.
Qed.
End rules.

(* ================================================================== (a) and (b): the callees' sum-form rooms (A :462-548) *)
Lemma tp_sl_alloc : forall f mx no cap rem j o,
  tr_alloc (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_alloc_run f mx no cap rem.
Proof.
  induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_alloc_run]; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  destruct (cap <? no + _); [|apply IH].
  cbn [fst]. rewrite tr_alloc_cons', IH. destruct (cap =? 0); reflexivity.
Qed.
(* one send's growth chain from cap: the sum is at most its peak and largest request, less cap *)
Lemma tp_sl_win_run : forall f mx no cap rem j o, 0 <= cap ->
  fst (send_line_b_c.sl_run f mx no cap rem j o) = [] \/
  tr_alloc (fst (send_line_b_c.sl_run f mx no cap rem j o)) + cap <=
    tr_peak (fst (send_line_b_c.sl_run f mx no cap rem j o)) + tr_max (fst (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run]; [left; reflexivity|].
  destruct (rem <=? 0); [left; reflexivity|].
  match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
  destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; [|cbv beta iota; apply IH; exact Hc].
  right. cbn [fst].
  destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as [E|I];
  set (T := fst (send_line_b_c.sl_run f mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j))) in *.
  - rewrite E. destruct (Z.eqb_spec cap 0) as [Ec|Ec]; cbv beta iota;
      cbn [tr_alloc tr_peak tr_max fold_right]; lia.
  - pose proof (tr_peak_nonneg T). pose proof (tr_max_nonneg' T).
    destruct (Z.eqb_spec cap 0) as [Ec|Ec]; cbv beta iota;
      [rewrite tr_alloc_malloc, tr_peak_malloc, tr_max_malloc | rewrite tr_alloc_realloc, tr_peak_realloc, tr_max_realloc];
      lia.
Qed.
(* (b): send_line's sum premise (sl_spec) is within the peak and largest request of its trace *)
Lemma tr_sl_window : forall c mx no cap len j o, 0 <= cap ->
  sl_alloc c mx no cap len <=
  tr_peak (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o) +
  tr_max (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o).
Proof.
  intros c mx no cap len j o Hc. unfold sl_alloc, send_line_b_c.send_line_tr.
  destruct (sl_live c len); cbv beta iota; [|cbn [tr_peak tr_max fold_right]; lia].
  rewrite <- (tp_sl_alloc (Z.to_nat len) mx no cap len j o).
  destruct (tp_sl_win_run (Z.to_nat len) mx no cap len j o Hc) as [E|I]; [rewrite E; cbn; lia | lia].
Qed.
(* (b): list_push's sum premise (lp_spec) is within the peak and largest request of its trace ListTr.list_push_tra *)
Lemma tr_lp_window : forall v (l : hlist) n, 0 <= hl_cap l -> 0 <= n ->
  (if lp_grow l then lp_vbytes l else 0) + (n + 1) <=
  tr_peak (ListTr.list_push_tra v (hl_n l) (hl_cap l) n) + tr_max (ListTr.list_push_tra v (hl_n l) (hl_cap l) n).
Proof.
  intros v l n Hc Hn. unfold lp_grow, lp_vbytes, ListTr.list_push_tra, grow_cap, AREC.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; [destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]|];
    cbv beta iota; cbn [app tr_peak tr_max fold_right]; lia.
Qed.
(* (a): a send's peak is within twice the capacity it leaves *)
Lemma tp_sl_run : forall f mx no cap rem j o, 0 <= cap ->
  tr_pos (fst (send_line_b_c.sl_run f mx no cap rem j o)) = fst (snd (send_line_b_c.sl_run f mx no cap rem j o)) - cap /\
  cap <= fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd tr_pos fold_right]. lia.
  - destruct (rem <=? 0); [cbn [fst snd tr_pos fold_right]; lia|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; [|cbv beta iota; apply IH; exact Hc].
    cbn [fst snd].
    destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as [I1 I2].
    destruct (Z.eqb_spec cap 0); cbv beta iota; [rewrite tr_pos_malloc | rewrite tr_pos_realloc]; lia.
Qed.
Lemma tp_sl_peak_cap_run : forall f mx no cap rem j o, 0 <= cap ->
  tr_peak (fst (send_line_b_c.sl_run f mx no cap rem j o)) + cap <= 2 * fst (snd (send_line_b_c.sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; cbn [send_line_b_c.sl_run].
  - cbn [fst snd tr_peak fold_right]. lia.
  - destruct (rem <=? 0); [cbn [fst snd tr_peak fold_right]; lia|].
    match goal with |- context [if ?b then mx else rem] => generalize (if b then mx else rem); intros n end.
    destruct (Z.ltb_spec cap (no + n)) as [Hl|Hl]; [|cbv beta iota; apply IH; exact Hc].
    cbn [fst snd].
    pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia)) as I.
    pose proof (proj2 (tp_sl_run f mx (no + n) ((no + n) * 2) (rem - n) (S j) (RelayRunT.Ret j) ltac:(lia))) as G.
    destruct (Z.eqb_spec cap 0); cbv beta iota; [rewrite tr_peak_malloc | rewrite tr_peak_realloc]; lia.
Qed.
Lemma tr_peak_sl_2cap : forall c mx no cap len j o, 0 <= cap ->
  tr_peak (send_line_b_c.send_line_tr (sl_live c len) mx no cap len j o) <= 2 * sl_cap c mx no cap len - cap.
Proof.
  intros c mx no cap len j o Hc. unfold sl_cap, send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct (sl_live c len); cbv beta iota; [|cbn [tr_peak fold_right]; lia].
  pose proof (tp_sl_peak_cap_run (Z.to_nat len) mx no cap len j o Hc) as H.
  rewrite sl_run_fin in H |- *. lia.
Qed.

(* ================================================================== a drain's summed positive growth (A :550-803) *)
(* the held array's deficit: what its next regrowth may add beyond 8 bytes *)
Definition tp_kdef (H : list (list Z)) (ka : Z) : Z := Z.max 0 (8 * Z.of_nat (length H) - ka).
(* the stream bytes still pending, and the relay's unfinished line when it keeps it *)
Definition tp_R (s : drain_b_c.dstate) : Z := Z.of_nat (length (rm3_dstr s)).
Definition tp_U (s : drain_b_c.dstate) : Z :=
  if drain_b_c.ds_skip s then 0 else Z.of_nat (length (drain_b_c.ds_u s)).
(* the potential: a round's summed positive growth is at most its rise *)
Definition tp_psi (s : drain_b_c.dstate) : Z :=
  drain_b_c.ds_cap s + 16 * drain_b_c.ds_ecap s + drain_b_c.ds_ocap s - tp_kdef (drain_b_c.ds_H s) (drain_b_c.ds_ka s) -
  SlotReads.wcost (drain_b_c.ds_ref s) - 10 * tp_R s - 9 * tp_U s.
(* the round invariant: Cb bounds the relay's buffer, Eb the expected list's capacity, En its length and the pending
   bytes *)
Definition tp_inv (Cb Eb En : Z) (s : drain_b_c.dstate) : Prop :=
  0 <= drain_b_c.ds_cap s <= Cb /\ 0 <= drain_b_c.ds_ecap s <= Eb /\ 0 <= drain_b_c.ds_ocap s /\
  0 <= drain_b_c.ds_ka s /\ 0 <= drain_b_c.ds_en s /\ 0 <= drain_b_c.ds_off s /\
  Z.of_nat (length (drain_b_c.ds_u s)) <= 6000 /\ drain_b_c.ds_en s + tp_R s <= En.

Ltac tp_projg := cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka
  drain_b_c.ds_eintr drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap
  drain_b_c.ds_no drain_b_c.ds_ocap].

Lemma tp_grow : forall cap used j b Cb, 0 <= cap <= Cb -> 0 <= used <= 6000 -> 20192 <= Cb ->
  tr_pos (fst (drain_b_c.grow_tr cap used j b)) = fst (snd (drain_b_c.grow_tr cap used j b)) - cap /\
  0 <= fst (snd (drain_b_c.grow_tr cap used j b)) <= Cb.
Proof.
  intros cap used j b Cb Hc Hu HC. unfold drain_b_c.grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096) as [Hl|Hl]; cbv zeta; cbn [fst snd].
  - destruct (Z.eqb_spec cap 0) as [E|E]; cbv beta iota; cbn [tr_pos fold_right]; lia.
  - cbn [tr_pos fold_right]. lia.
Qed.
Lemma tp_push_tra : forall v n cap x, 0 <= cap ->
  tr_pos (ListTr.list_push_tra v n cap x) = 16 * (drain_b_c.push_cap n cap - cap) + Z.max 0 (x + 1).
Proof.
  intros v n cap x Hc. unfold ListTr.list_push_tra, drain_b_c.push_cap.
  destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; cbv beta iota; cbn [app tr_pos fold_right]; lia.
Qed.
Lemma tp_pushes : forall ls n cap j v rs tr cap' ad, 0 <= n -> 0 <= cap ->
  drain_b_c.pushes_run n cap ls j v rs = (tr, cap', ad) ->
  tr_pos tr = 16 * (cap' - cap) + Z.of_nat (length (RelayModel.with_nul ls)) /\
  cap <= cap' <= Z.max cap (Z.max 8 (2 * (n + Z.of_nat (length ls)))).
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs tr cap' ad Hn Hc E.
  - cbn [drain_b_c.pushes_run] in E. injection E as <- <- <-.
    rewrite RelayCap.with_nul_nil_len. cbn [length tr_pos fold_right]. lia.
  - cbn [drain_b_c.pushes_run] in E. cbv zeta in E.
    match type of E with context [drain_b_c.pushes_run (n + 1) ?c2 ls ?j2 ?v2 ?r2] =>
      destruct (drain_b_c.pushes_run (n + 1) c2 ls j2 v2 r2) as [[tr2 cap2] ad2] eqn:E2 end.
    cbn [fst snd] in E. injection E as <- <- <-.
    assert (Hpc : cap <= drain_b_c.push_cap n cap <= Z.max cap (Z.max 8 (2 * (n + 1))))
      by (unfold drain_b_c.push_cap; destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0)|]; lia).
    destruct (IH (n + 1) (drain_b_c.push_cap n cap) _ _ _ _ _ _ ltac:(lia) ltac:(lia) E2) as [I1 I2].
    rewrite tr_pos_app, tp_push_tra by exact Hc. rewrite I1, RelayCap.with_nul_cons_len. cbn [length]. lia.
Qed.
Lemma tp_send_line : forall live mx no cap len j o, 0 <= cap ->
  tr_pos (send_line_b_c.send_line_tr live mx no cap len j o) = send_line_b_c.send_line_cap live mx no cap len - cap /\
  cap <= send_line_b_c.send_line_cap live mx no cap len.
Proof.
  intros live mx no cap len j o Hc. unfold send_line_b_c.send_line_tr, send_line_b_c.send_line_cap.
  destruct live; cbv beta iota; [|cbn [tr_pos fold_right]; lia].
  destruct (tp_sl_run (Z.to_nat len) mx no cap len j o Hc) as [A1 A2].
  rewrite sl_run_fin in A1, A2 |- *. lia.
Qed.
(* gesture_seen: a new begin regrows the held array to 8 * |H'| (its deficit paid, 8 bytes more) and strndup's the
   key (at most the line and its NUL); an end frees its key; the array never shrinks below what the next begin needs
   more than the deficit *)
Lemma tp_seen : forall H ka l j ha ks, 0 <= ka ->
  tr_pos (fst (fst (drain_b_c.seen_tr H ka l j ha ks))) +
    tp_kdef (RelayKeys.seen_arr H l) (snd (fst (drain_b_c.seen_tr H ka l j ha ks))) <=
  8 + (Z.of_nat (length l) + 1) + tp_kdef H ka /\ 0 <= snd (fst (drain_b_c.seen_tr H ka l j ha ks)).
Proof.
  intros H ka l j ha ks Hka. unfold drain_b_c.seen_tr, RelayKeys.seen_arr, tp_kdef.
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|cbn [fst snd tr_pos fold_right]; lia].
  pose proof (dpre_gesture_len l kd x G) as Hx.
  destruct kd; destruct (RelayKeys.index_of x H) as [nn|] eqn:EI; cbn [fst snd].
  - cbn [tr_pos fold_right]. lia.
  - rewrite length_app. cbn [length].
    destruct (Z.eqb_spec ka 0) as [E|E]; cbv beta iota; cbn [tr_pos fold_right]; lia.
  - cbn [tr_pos fold_right]. rewrite (RelayCap.rc_swap_len [] nn H).
    destruct (RelayKeys.index_of_some x H nn EI) as (aa & bb & EH & _).
    assert (LH : (1 <= length H)%nat) by (rewrite EH, length_app; cbn [length]; lia).
    lia.
  - cbn [tr_pos fold_right]. lia.
Qed.
Lemma tp_lines : forall ls live mx no cap H ka j o ha ks tr oc H' ka' ad, 0 <= cap -> 0 <= ka ->
  drain_b_c.lines_run live mx no cap H ka ls j o ha ks = (tr, (oc, H', ka'), ad) ->
  tr_pos tr + tp_kdef H' ka' <= oc - cap + 9 * Z.of_nat (length (RelayModel.with_nul ls)) + tp_kdef H ka /\
  cap <= oc /\ 0 <= ka'.
Proof.
  induction ls as [|l ls IH]; intros live mx no cap H ka j o ha ks tr oc H' ka' ad Hc Hk E.
  - cbn [drain_b_c.lines_run] in E. injection E as <- <- <- <- <-.
    rewrite RelayCap.with_nul_nil_len. cbn [tr_pos fold_right]. lia.
  - cbn [drain_b_c.lines_run] in E. cbv zeta in E.
    match type of E with context [drain_b_c.lines_run live mx ?n2 ?c2 ?H2 ?k2 ls ?j2 ?o2 ?h2 ?s2] =>
      destruct (drain_b_c.lines_run live mx n2 c2 H2 k2 ls j2 o2 h2 s2) as [[tr2 [[oc2 H2'] ka2]] ad2] eqn:E2 end.
    cbn [fst snd] in E. injection E as <- <- <- <- <-.
    rewrite !tr_pos_app, RelayCap.with_nul_cons_len.
    destruct (tp_send_line live mx no cap (Z.of_nat (length l) + 1) j o Hc) as [S1 S2].
    match goal with |- context [drain_b_c.seen_tr H ka l ?jj ha ks] =>
      destruct (tp_seen H ka l jj ha ks Hk) as [T1 T2] end.
    destruct (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.le_trans _ _ _ Hc S2) T2 E2) as (I1 & I2 & I3).
    lia.
Qed.
Lemma tp_lines_len : forall d st, (length (RelayModel.lines st d) <= length d)%nat.
Proof.
  induction d as [|b d IH]; intros st; [rewrite RelayModel.lines_nil; cbn; lia|].
  rewrite RelayModel.lines_cons. specialize (IH (fst (RelayModel.step st b))).
  destruct (snd (RelayModel.step st b)); cbn [length]; lia.
Qed.

(* drain's rounds: the summed positive growth is at most the potential's rise, and the invariant is kept *)
Lemma tp_drain_run : forall f live mx s j a Cb Eb En,
  20192 <= Cb -> Z.max 8 (2 * En) <= Eb -> tp_inv Cb Eb En s ->
  tr_pos (fst (drain_b_c.drain_run f live mx s j a)) <=
    tp_psi (fst (snd (drain_b_c.drain_run f live mx s j a))) - tp_psi s /\
  tp_inv Cb Eb En (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a Cb Eb En HC HE HI.
  { cbn [drain_b_c.drain_run fst snd]. change (tr_pos (@nil (RelayRunT.rev YO0i.sptr))) with 0.
    split; [lia | exact HI]. }
  pose proof HI as (Ic & Ie & Io & Ik & Hen & Iof & Iu & Ien).
  cbn [drain_b_c.drain_run]. cbv zeta.
  pose proof (tp_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Cb Ic
                ltac:(lia) HC) as [G1 G2].
  revert G1 G2.
  generalize (drain_b_c.grow_tr (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a)).
  intros [tg [cap1 b1]] G1 G2. cbn [fst snd] in G1, G2 |- *.
  set (s1 := drain_b_c.DS cap1 (drain_b_c.ds_u s) (drain_b_c.ds_skip s) (drain_b_c.ds_H s) (drain_b_c.ds_ka s) false
               (drain_b_c.ds_pend s) (drain_b_c.ds_off s) (drain_b_c.ds_ref s) (drain_b_c.ds_en s)
               (drain_b_c.ds_ecap s) (drain_b_c.ds_no s) (drain_b_c.ds_ocap s)).
  assert (P1 : tp_psi s1 = tp_psi s + cap1 - drain_b_c.ds_cap s)
    by (unfold s1, tp_psi, tp_R, tp_U, rm3_dstr; tp_projg; lia).
  assert (J1 : tp_inv Cb Eb En s1).
  { unfold s1, tp_inv. tp_projg. unfold tp_R, rm3_dstr in Ien |- *. tp_projg. lia. }
  clearbody s1.
  assert (PS : tp_psi s = drain_b_c.ds_cap s + 16 * drain_b_c.ds_ecap s + drain_b_c.ds_ocap s -
                 tp_kdef (drain_b_c.ds_H s) (drain_b_c.ds_ka s) - SlotReads.wcost (drain_b_c.ds_ref s) - 10 * tp_R s -
                 9 * (if drain_b_c.ds_skip s then 0 else Z.of_nat (length (drain_b_c.ds_u s)))) by reflexivity.
  destruct (drain_b_c.ds_eintr s).
  - (* an EINTR round: the growth only, then the same state *)
    cbn [fst snd].
    match goal with |- context [drain_b_c.drain_run f live mx s1 ?j1 ?a1] =>
      destruct (IH s1 j1 a1 Cb Eb En HC HE J1) as [I1 I2] end.
    rewrite tr_pos_app. split; [lia | exact I2].
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP.
    + cbn [fst snd]. split; [lia | exact J1].
    + match goal with |- context [Z.min ?x ?y <=? 0] => set (n := Z.min x y) in * end.
      assert (Hnr : n <= Z.of_nat (length r0) - drain_b_c.ds_off s) by (unfold n; apply Z.le_min_l).
      destruct (Z.leb_spec n 0) as [Hn|Hn].
      * cbn [fst snd]. split; [lia | exact J1].
      * (* a data round *)
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
        assert (Ld : Z.of_nat (length d) = n) by (unfold d; rewrite length_firstn, length_skipn; lia).
        destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
        pose proof (rm3_chunk_mass _ _ _ _ _ _ EC) as CM.
        destruct (dpre_chunk _ _ _ _ _ _ EC) as (_ & _ & C3).
        pose proof (SlotReads.lines_bytes d (drain_b_c.ds_ref s)) as LB.
        pose proof (tp_lines_len d (drain_b_c.ds_ref s)) as LL.
        cbv beta iota.
        match goal with |- context [drain_b_c.pushes_run ?n0 ?c0 ?ls0 ?jj ?vv ?rr] =>
          destruct (drain_b_c.pushes_run n0 c0 ls0 jj vv rr) as [[tpu ecap'] [v' rs']] eqn:EPU end.
        destruct (tp_pushes _ _ _ _ _ _ _ _ _ Hen (proj1 Ie) EPU) as [Q1 Q2].
        match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 ?a3 ?a4 rl ?a5 ?a6 ?a7 ?a8] =>
          destruct (drain_b_c.lines_run live mx a1 a2 a3 a4 rl a5 a6 a7 a8)
            as [[tl [[oc' H'] ka']] [[o' ha'] ks']] eqn:EL end.
        destruct (tp_lines _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Io Ik EL) as (L1 & L2 & L3).
        cbn [fst snd].
        assert (R0 : tp_R s = Z.of_nat (length r0) - drain_b_c.ds_off s + Z.of_nat (length (concat rs))).
        { unfold tp_R, rm3_dstr. rewrite EP, length_app, length_skipn. lia. }
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [W|W].
        -- (* the head text is read to its end: list_drop frees it *)
           match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] =>
             set (S2 := s2); set (J4 := j4); set (A2 := a2) end.
           assert (R2 : tp_R S2 = Z.of_nat (length (concat rs))).
           { unfold S2, tp_R, rm3_dstr. tp_projg. rewrite rm3_dstr0. reflexivity. }
           assert (J2 : tp_inv Cb Eb En S2).
           { unfold tp_inv. rewrite R2. unfold S2. tp_projg. lia. }
           assert (P2 : tp_psi S2 = cap1 + 16 * ecap' + oc' - tp_kdef H' ka' -
                          SlotReads.wcost (RelayModel.feed (drain_b_c.ds_ref s) d) -
                          10 * Z.of_nat (length (concat rs)) - 9 * (if sk' then 0 else Z.of_nat (length u'))).
           { unfold tp_psi. rewrite R2. unfold tp_U, S2. tp_projg. reflexivity. }
           destruct (IH S2 J4 A2 Cb Eb En HC HE J2) as [I1 I2].
           cbv beta iota. unfold ListTr.list_drop_tra.
           rewrite !tr_pos_app, tr_pos_free. change (tr_pos (@nil (RelayRunT.rev YO0i.sptr))) with 0.
           split; [lia | exact I2].
        -- (* part of the head text read *)
           match goal with |- context [drain_b_c.drain_run f live mx ?s2 ?j4 ?a2] =>
             set (S2 := s2); set (J4 := j4); set (A2 := a2) end.
           assert (R2 : tp_R S2 = Z.of_nat (length r0) - (drain_b_c.ds_off s + n) + Z.of_nat (length (concat rs))).
           { unfold S2, tp_R, rm3_dstr. tp_projg. rewrite length_app, length_skipn. lia. }
           assert (J2 : tp_inv Cb Eb En S2).
           { unfold tp_inv. rewrite R2. unfold S2. tp_projg. lia. }
           assert (P2 : tp_psi S2 = cap1 + 16 * ecap' + oc' - tp_kdef H' ka' -
                          SlotReads.wcost (RelayModel.feed (drain_b_c.ds_ref s) d) -
                          10 * (Z.of_nat (length r0) - (drain_b_c.ds_off s + n) + Z.of_nat (length (concat rs))) -
                          9 * (if sk' then 0 else Z.of_nat (length u'))).
           { unfold tp_psi. rewrite R2. unfold tp_U, S2. tp_projg. reflexivity. }
           destruct (IH S2 J4 A2 Cb Eb En HC HE J2) as [I1 I2].
           cbv beta iota.
           rewrite !tr_pos_app. change (tr_pos (@nil (RelayRunT.rev YO0i.sptr))) with 0.
           split; [lia | exact I2].
Qed.

(* one drain from g_nout = 0: the summed positive growth is at most 44 P + 8 K + 92320 for P pending bytes and K
   held keys *)
Lemma tp_dr : forall c mx cap (e : rentry) h,
  0 <= cap -> 0 <= re_cap e -> 0 <= drain_b_c.ent_ka e -> 0 <= hl_cap (hs_expected h) -> 0 <= hs_off h ->
  hl_recs (hs_expected h) = [] -> Z.of_nat (length (re_U e)) <= APARTIAL ->
  (hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h)) ->
  tr_pos (dr_tr c mx 0 cap e h) <=
    44 * Z.of_nat (length (pending_stream h)) + 8 * Z.of_nat (length (re_keys e)) + 92320 /\
  0 <= drain_b_c.ds_cap (dr_fin c mx 0 cap e h) /\ 0 <= drain_b_c.ds_ka (dr_fin c mx 0 cap e h) /\
  0 <= drain_b_c.ds_ocap (dr_fin c mx 0 cap e h).
Proof.
  intros c mx cap e h Hcap Hrc Hka Hec Hoff Hexp HU HJ.
  set (PL := Z.of_nat (length (pending_stream h))).
  assert (HPL : 0 <= PL) by (unfold PL; lia).
  unfold APARTIAL in HU.
  assert (HI : tp_inv (Z.max (re_cap e) 20192) (Z.max (hl_cap (hs_expected h)) (Z.max 8 (2 * PL))) PL
                 (drain_b_c.drain_init 0 cap e h)).
  { unfold tp_inv, tp_R. rewrite rm3_dstr_init, RelayCap.rc_length_bzs. fold PL.
    unfold drain_b_c.drain_init. tp_projg. unfold hl_n. rewrite Hexp, RelayCap.rc_length_bzs. cbn [length]. lia. }
  assert (PS0 : tp_psi (drain_b_c.drain_init 0 cap e h) =
    re_cap e + 16 * hl_cap (hs_expected h) + cap - tp_kdef (drain_b_c.keys_texts (re_keys e)) (drain_b_c.ent_ka e) -
    SlotReads.wcost (hs_state h) - 10 * PL - 9 * (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e)))).
  { unfold tp_psi, tp_R, tp_U. rewrite rm3_dstr_init, RelayCap.rc_length_bzs. fold PL.
    unfold drain_b_c.drain_init. tp_projg. rewrite RelayCap.rc_length_bzs. reflexivity. }
  destruct (tp_drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx (drain_b_c.drain_init 0 cap e h) 0%nat
              drain_b_c.dadr0 (Z.max (re_cap e) 20192) (Z.max (hl_cap (hs_expected h)) (Z.max 8 (2 * PL))) PL
              ltac:(lia) ltac:(lia) HI) as [T1 T2].
  pose proof (RelayCap.drain_ocap_le (dr_live c h) mx 0 cap e h) as [_ OC].
  pose proof (rm3_no_fin (dr_live c h) mx cap e h Hoff) as NF.
  unfold dr_tr, dr_fin, drain_b_c.drain_tr, drain_b_c.drain_fin, drain_b_c.drain_go in *.
  revert T1 T2 OC NF.
  generalize (drain_b_c.drain_run (S (S (length (pending_stream h)))) (dr_live c h) mx
                (drain_b_c.drain_init 0 cap e h) 0%nat drain_b_c.dadr0).
  intros [tr [fin adf]] T1 T2 OC NF. cbn [fst snd] in T1, T2, OC, NF |- *.
  destruct T2 as (F1 & F2 & F3 & F4 & _).
  assert (PSF : tp_psi fin <= drain_b_c.ds_cap fin + 16 * drain_b_c.ds_ecap fin + drain_b_c.ds_ocap fin).
  { unfold tp_psi, tp_kdef, tp_R, tp_U. pose proof (SlotReads.wcost_nonneg (drain_b_c.ds_ref fin)).
    destruct (drain_b_c.ds_skip fin); lia. }
  assert (KD : tp_kdef (drain_b_c.keys_texts (re_keys e)) (drain_b_c.ent_ka e) <= 8 * Z.of_nat (length (re_keys e))).
  { unfold tp_kdef, drain_b_c.keys_texts. rewrite length_map. lia. }
  assert (WC : SlotReads.wcost (hs_state h) <= 6000).
  { unfold SlotReads.wcost, hs_state. cbn [ls_k ls_w].
    destruct HJ as [E|E]; [rewrite E; cbn; lia|].
    destruct (hs_overlong h =? 1); [lia|]. rewrite <- E, RelayCap.rc_length_bzs. lia. }
  assert (HX : 0 <= (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e))) <= 6000)
    by (destruct (re_skip e =? 1); lia).
  unfold PL in *.
  split; [lia | split; [lia | split; lia]].
Qed.

(* gestures_end's key run: its summed positive growth is g_capout's growth (a key's free adds nothing) *)
Lemma tp_ker : forall live mx (xks : list (Z * RelayRunT.addr YO0i.sptr)) no cap j o, 0 <= cap ->
  Forall (fun x => 0 <= fst x) xks ->
  tr_pos (fst (gestures_end_b_c.keys_end_run live mx no cap xks j o)) =
    fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)) - cap /\
  cap <= fst (snd (gestures_end_b_c.keys_end_run live mx no cap xks j o)).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o Hc HF.
  - cbn [gestures_end_b_c.keys_end_run fst snd tr_pos fold_right]. lia.
  - apply Forall_cons_iff in HF as [Hx HF]. cbn [fst] in Hx.
    cbn [gestures_end_b_c.keys_end_run].
    unfold gesture_end_b_c.gesture_end_tr, gesture_end_b_c.gesture_end_cap. cbv zeta. cbn [fst snd].
    rewrite !tr_pos_app, tr_pos_free.
    destruct (tp_send_line live mx no cap xl j o Hc) as [S1 S2].
    match goal with |- context [send_line_b_c.send_line_tr live mx (no + xl) ?c1 5 ?j1 ?o1] =>
      destruct (tp_send_line live mx (no + xl) c1 5 j1 o1 (Z.le_trans _ _ _ Hc S2)) as [S3 S4] end.
    match goal with |- context [gestures_end_b_c.keys_end_run live mx (no + xl + 5) ?c2 r ?j2 ?o2] =>
      destruct (IH (no + xl + 5) c2 j2 o2 ltac:(lia) HF) as [I1 I2] end.
    lia.
Qed.
Lemma tp_kw_fold : forall (a0 : RelayRunT.addr YO0i.sptr) (H : list (list Z)),
  fold_right (fun xl acc => xl + 5 + acc) 0 (map fst (map (fun x => (Z.of_nat (length x), a0)) H)) = rm3_kw H.
Proof. intros a0 H. unfold rm3_kw. induction H as [|x H IH]; cbn [map fold_right fst]; lia. Qed.

(* relay_remove's requests from g_nout = 0 (rr_tr): drain's when the entry is open, the key run's g_capout growth (at
   most 2 (g_nout + keys' bytes)), two frees *)
Lemma tp_rr : forall c mx cap FD es h (e : rentry),
  find (fun e => re_fd e =? FD) es = Some e ->
  0 <= cap -> 0 <= re_cap e -> 0 <= drain_b_c.ent_ka e -> 0 <= hl_cap (hs_expected h) -> 0 <= hs_off h ->
  hl_recs (hs_expected h) = [] -> Z.of_nat (length (re_U e)) <= APARTIAL ->
  (re_eof e = 0 -> hs_overlong h = 1 \/ bzs (re_U e) = bzs (hs_W h)) ->
  tr_pos (rr_tr c mx 0 cap FD es h) <=
    48 * Z.of_nat (length (pending_stream h)) + 8 * Z.of_nat (length (re_keys e)) +
    2 * gestures_end_b_c.keys_total (re_keys e) + 116320.
Proof.
  intros c mx cap FD es h e Hf Hcap Hrc Hka Hec Hoff Hexp HU HJ.
  pose proof (RelayCap.keys_total_nonneg (re_keys e)) as HKT.
  unfold rr_tr. cbv zeta.
  destruct (FD <? 0); [cbn [tr_pos fold_right]; lia|].
  rewrite Hf. cbv beta iota zeta.
  destruct (re_eof e =? 0) eqn:Eo; cbv beta iota.
  - apply Z.eqb_eq in Eo.
    destruct (tp_dr c mx cap e h Hcap Hrc Hka Hec Hoff Hexp HU (HJ Eo)) as (D1 & D2 & D3 & D4).
    rewrite !tr_pos_app, tr_pos_free, tr_pos_free. change (tr_pos (@nil (RelayRunT.rev YO0i.sptr))) with 0.
    match goal with |- context [gestures_end_b_c.keys_end_run ?lv ?m (drain_b_c.ds_no ?F) ?oc1 ?xks ?j1 ?o1] =>
      assert (KF : Forall (fun x => 0 <= fst x) xks)
        by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
      destruct (tp_ker lv m xks (drain_b_c.ds_no F) oc1 j1 o1 D4 KF) as [K1 _];
      pose proof (RelayCap.keys_end_run_cap_le lv m xks (drain_b_c.ds_no F) oc1 j1 o1 KF) as K2 end.
    rewrite K1. rewrite tp_kw_fold in K2.
    pose proof (rrp_fin_kw (dr_live c h) mx cap e h) as KW.
    pose proof (rm3_no_fin (dr_live c h) mx cap e h Hoff) as NF.
    change (drain_b_c.drain_fin (dr_live c h) mx 0 cap e h) with (dr_fin c mx 0 cap e h) in KW, NF.
    assert (HX : 0 <= (if re_skip e =? 1 then 0 else Z.of_nat (length (re_U e))) <= 6000)
      by (unfold APARTIAL in HU; destruct (re_skip e =? 1); lia).
    assert (N0 : 0 <= drain_b_c.ds_no (dr_fin c mx 0 cap e h)).
    { pose proof (RelayCap.drain_ocap_le (dr_live c h) mx 0 cap e h) as [N _]. exact N. }
    assert (KW0 : 0 <= rm3_kw (drain_b_c.ds_H (dr_fin c mx 0 cap e h)))
      by (unfold rm3_kw; apply bt_zsum_map_nonneg; intros; lia).
    lia.
  - rewrite app_nil_l, tr_pos_app, tr_pos_free, tr_pos_free.
    change (tr_pos (@nil (RelayRunT.rev YO0i.sptr))) with 0.
    cbn [drain_b_c.drain_init drain_b_c.ds_no drain_b_c.ds_ocap drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_cap].
    match goal with |- context [gestures_end_b_c.keys_end_run ?lv ?m 0 cap ?xks ?j1 ?o1] =>
      assert (KF : Forall (fun x => 0 <= fst x) xks)
        by (apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (x & <- & _); cbn [fst]; lia);
      destruct (tp_ker lv m xks 0 cap j1 o1 Hcap KF) as [K1 _];
      pose proof (RelayCap.keys_end_run_cap_le lv m xks 0 cap j1 o1 KF) as K2 end.
    rewrite K1. rewrite tp_kw_fold, <- rm3_kt_kw in K2. lia.
Qed.

(* ================================================================== the model blocks' sizes (A :881-896) *)
Lemma tp_pos_entry : forall e, (forall b, In b (aentry_blks e) -> 0 <= snd b) ->
  0 <= re_cap e /\ 0 <= drain_b_c.ent_ka e.
Proof.
  intros e H. unfold drain_b_c.ent_ka. split.
  - destruct (Z.eqb_spec (re_cap e) 0) as [E|E]; [lia|].
    apply (H (re_buf e, re_cap e)). unfold aentry_blks. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
  - destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; [lia|].
    apply (H (re_hp e, re_kh e)). unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
    rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
Qed.
Lemma tp_pos_out : forall cap out, (forall b, In b (aout_blks cap out) -> 0 <= snd b) -> 0 <= cap.
Proof.
  intros cap out H. destruct (Z.eqb_spec cap 0) as [E|E]; [lia|].
  apply (H (out, cap)). unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) E). left. reflexivity.
Qed.
