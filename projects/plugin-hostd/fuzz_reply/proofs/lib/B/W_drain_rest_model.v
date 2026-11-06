(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the pure model of segment GS of the ASan+UBSan walk (image B,
   fuzz_reply.asan-ubsan) of fuzz_reply's drain -- gesture_seen's held-array search and update
   (relay.c:89-121, inlined) -- with no machine state and no image address: the line [p, q) of the relay's
   buffer, the line loop's model values after one more relayed line, the held-key set (index_of and the
   four shapes of seen_tr / seen_arr), the relay entry's key list under append and swap-remove and its byte
   image key_ptrs, and upds over one more relayed line.  The three stage walks of lib/B/W_drain_gs.v
   (gs_scan_stmt, gs_add_stmt, gs_free_stmt) cite it.

   PORTED from image A's lib/A/W_drain_gs.v:59-599 on a working branch ed12337f74d (the file last
   changed in 1ef2c00b5d5), every lemma name kept.  The block names no image address and no image-A
   definition, so it is stated here over image B's own definitions: dcx, dW, drlp, dskp, drlq, dlrun, dlno,
   dloc, dlH, dlka, dbound and dline of lib/B/W_drain_cx.v (:411, :617-642; the same text as image A's), and
   the shared model of lib/A/W_drain_model.v and lib/Prog (lrun, seen_arr, seen_ka, seen_tr, index_of,
   set_nth, swap_remove, key_ptrs, keys_texts, scan, gesture, upds, with_nul).  The Require list is
   lib/B/W_drain_gs.v's, plus lib/Lib/Mem for le8. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_drain_gs_model.v; 64 of its 144 lines of code are new or changed and 415 lines of the source are left out. *)
(* Image-B (fuzz_reply.asan-ubsan) copy of lib/A/W_drain_rest_model.v (a working branch e6b5f95b285), over lib/B's
   interface; only the imports and the Section header (lib/B/W_drain_lineb.v's) changed. *)
(* The pure model facts of the REST segment of fuzz_reply's drain ASan walk
   (DLR 0x83a4c -> DI): when the relay's buffer dW s1 holds no NUL from p on, the line loop has nothing left to
   relay (drlq s1 p = []), the round's chunk is the rest [p, |dW s1|) (or the long-line reset), and the next
   round state's s->buf / s->skip are that rest and dskp s1 p (or [] and true).  Closed lemmas: no Section
   variables, no hypotheses.  Ported from W_drain_gs.v gsx_scan_nz_app / gsx_scan_pre and its helpers
   (= released lib/Prog/drain_b.v scan_nz_app / scan_pre / drl_end / drlq_0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- scan over NUL-free bytes, and the prefix [0, p) of the buffer (ported from W_drain_gs.v:67-172). ---- *)
Lemma rmx_scan_zero_fst : forall sk acc d, fst (scan sk acc (0 :: d)) = fst (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma rmx_scan_zero_snd : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma rmx_scan_nz_app : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof.
  induction u as [|b u IH]; intros sk acc d Hz.
  - rewrite app_nil_r. reflexivity.
  - pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
    rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma rmx_scan_nz0 : forall u sk d, nozero u -> scan sk [] (u ++ d) = scan sk u d.
Proof. intros u sk d Hz. rewrite (rmx_scan_nz_app u sk [] d Hz). reflexivity. Qed.

(* a NUL-free run is all accumulated: no line, the skip flag unchanged *)
Lemma rmx_scan_nz_all : forall u sk acc, nozero u -> scan sk acc u = (sk, acc ++ u, []).
Proof.
  induction u as [|b u IH]; intros sk acc Hz.
  - rewrite app_nil_r. reflexivity.
  - pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu.
    rewrite (scan_nz sk acc b u Hb), (IH sk (acc ++ [b]) Hu), <- app_assoc. reflexivity.
Qed.

Lemma rmx_firstn_nth_app : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n x Hn). reflexivity.
Qed.

Lemma rmx_nth_skipn : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l as [|a l IH]; intros n i.
  - rewrite skipn_nil, !nth_error_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|]. change (nth_error (skipn n l) i = nth_error l (n + i)). apply IH.
Qed.

Lemma rmx_scan_app_z : forall p sk acc q,
  fst (scan sk acc (p ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk acc (p ++ 0 :: q)) = snd (scan sk acc (p ++ [0])) ++ snd (scan false [] q).
Proof.
  induction p as [|b p IH]; intros sk acc q.
  - cbn [app]. rewrite rmx_scan_zero_fst, !rmx_scan_zero_snd. cbn [scan snd]. split; [reflexivity|].
    destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
  - cbn [app]. destruct (Z.eq_dec b 0) as [->|Hb].
    + rewrite rmx_scan_zero_fst, !rmx_scan_zero_snd. destruct (IH false [] q) as [I1 I2].
      split; [exact I1|]. rewrite I2. destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
    + rewrite (scan_nz sk acc b (p ++ 0 :: q) Hb), (scan_nz sk acc b (p ++ [0]) Hb). apply IH.
Qed.

Lemma rmx_scan_pre : forall s1 p r, dbound s1 p ->
  fst (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = fst (scan (dskp s1 p) [] r) /\
  snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = drlp s1 p ++ snd (scan (dskp s1 p) [] r).
Proof.
  intros s1 p r (HP & HN). destruct p as [|p]; [split; reflexivity|].
  assert (HN' : nth_error (dW s1) p = Some 0).
  { destruct HN as [H0|H0]; [discriminate|]. replace p with (S p - 1)%nat by lia. exact H0. }
  unfold drlp, dskp. cbn [Nat.eqb]. rewrite (rmx_firstn_nth_app _ _ _ HN'), <- app_assoc. cbn [app].
  exact (rmx_scan_app_z (firstn p (dW s1)) (drain_b_c.ds_skip s1) [] r).
Qed.

(* ---- REST's facts: no NUL in the buffer from p on. ---- *)
Lemma rm_nz_rest : forall s1 p, (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) ->
  nozero (skipn p (dW s1)).
Proof.
  intros s1 p H. unfold nozero. apply Forall_forall. intros x Hx.
  apply In_nth_error in Hx. destruct Hx as [i Hi].
  rewrite rmx_nth_skipn in Hi. intro E. subst x. exact (H (p + i)%nat ltac:(lia) Hi).
Qed.

Lemma rm_drlq_nil : forall s1 p, dbound s1 p -> (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) ->
  drlq s1 p = [].
Proof.
  intros s1 p _ H. unfold drlq. rewrite (rmx_scan_nz_all _ (dskp s1 p) [] (rm_nz_rest s1 p H)). reflexivity.
Qed.

Lemma rm_dchunk : forall s1 p, nozero (drain_b_c.ds_u s1) -> dbound s1 p ->
  (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) ->
  dchunk s1 = if Nat.ltb LINE_LIMIT (length (skipn p (dW s1))) then ([], true, drlp s1 p)
              else (skipn p (dW s1), dskp s1 p, drlp s1 p).
Proof.
  intros s1 p HU HB H.
  assert (HS : scan (drain_b_c.ds_skip s1) (drain_b_c.ds_u s1) (ddata s1) =
               (dskp s1 p, skipn p (dW s1), drlp s1 p)).
  { rewrite <- (rmx_scan_nz0 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (ddata s1) HU).
    change (drain_b_c.ds_u s1 ++ ddata s1) with (dW s1).
    rewrite <- (firstn_skipn p (dW s1)) at 1.
    destruct (rmx_scan_pre s1 p (skipn p (dW s1)) HB) as [E1 E2].
    rewrite (rmx_scan_nz_all _ (dskp s1 p) [] (rm_nz_rest s1 p H)) in E1, E2.
    cbn [fst snd app] in E1, E2. rewrite app_nil_r in E2.
    revert E1 E2.
    destruct (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ skipn p (dW s1))) as [[sk r] ls].
    cbn [fst snd]. intros E1 E2. rewrite E1, E2. reflexivity. }
  unfold dchunk, chunk. rewrite HS. reflexivity.
Qed.

Lemma rm_drl : forall s1 p, nozero (drain_b_c.ds_u s1) -> dbound s1 p ->
  (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) -> drl s1 = drlp s1 p.
Proof.
  intros s1 p HU HB H. unfold drl. rewrite (rm_dchunk s1 p HU HB H).
  destruct (Nat.ltb LINE_LIMIT (length (skipn p (dW s1)))); reflexivity.
Qed.

Lemma rm_dnext_short : forall lv mx s1 p, nozero (drain_b_c.ds_u s1) -> dbound s1 p ->
  (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) -> (length (skipn p (dW s1)) <= LINE_LIMIT)%nat ->
  drain_b_c.ds_u (dnext lv mx s1) = skipn p (dW s1) /\ drain_b_c.ds_skip (dnext lv mx s1) = dskp s1 p.
Proof.
  intros lv mx s1 p HU HB H HL.
  change (drain_b_c.ds_u (dnext lv mx s1)) with (fst (fst (dchunk s1))).
  change (drain_b_c.ds_skip (dnext lv mx s1)) with (snd (fst (dchunk s1))).
  rewrite (rm_dchunk s1 p HU HB H), (proj2 (Nat.ltb_ge LINE_LIMIT (length (skipn p (dW s1)))) HL).
  split; reflexivity.
Qed.

Lemma rm_dnext_long : forall lv mx s1 p, nozero (drain_b_c.ds_u s1) -> dbound s1 p ->
  (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) -> (LINE_LIMIT < length (skipn p (dW s1)))%nat ->
  drain_b_c.ds_u (dnext lv mx s1) = [] /\ drain_b_c.ds_skip (dnext lv mx s1) = true.
Proof.
  intros lv mx s1 p HU HB H HL.
  change (drain_b_c.ds_u (dnext lv mx s1)) with (fst (fst (dchunk s1))).
  change (drain_b_c.ds_skip (dnext lv mx s1)) with (snd (fst (dchunk s1))).
  rewrite (rm_dchunk s1 p HU HB H), (proj2 (Nat.ltb_lt LINE_LIMIT (length (skipn p (dW s1)))) HL).
  split; reflexivity.
Qed.
