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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
(* dcx (lib/B/W_drain_cx.v:423) carries a world over PI's segments, so the lemmas about dlrun / dloc /
   dlH / dlka take the image as an implicit argument, as W_drain_cx.v's own definitions do. *)

(* ---- The pure model of the segment (no machine state): the line loop's values after one more
   relayed line, the held-key set, and the relay entry's key list under the two updates. ---- *)
(* ---------------------------------------------------------------------------------------------------------
   (1) the line [p, q) of the relay's buffer: the prefix / rest split of the line loop's scan
   --------------------------------------------------------------------------------------------------------- *)

(* ported from lib/Prog/drain_b.v:2797-2955 (scan_zero_fst, scan_zero_snd, scan_nz_app, nth_skipn_cons,
   firstn_nth_app, firstn_split, nth_skipn, nz_firstn, scan_app_z) *)
Lemma gsx_scan_zero_fst : forall sk acc d, fst (scan sk acc (0 :: d)) = fst (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma gsx_scan_zero_snd : forall sk acc d, snd (scan sk acc (0 :: d)) =
  if (sk || Nat.ltb LINE_LIMIT (length acc))%bool then snd (scan false [] d) else acc :: snd (scan false [] d).
Proof. intros sk acc d. rewrite scan_zero. destruct (scan false [] d) as [[a b] c]. reflexivity. Qed.

Lemma gsx_scan_nz_app : forall u sk acc d, nozero u -> scan sk acc (u ++ d) = scan sk (acc ++ u) d.
Proof.
  induction u as [|b u IH]; intros sk acc d Hz.
  - rewrite app_nil_r. reflexivity.
  - pose proof (Forall_inv Hz) as Hb. pose proof (Forall_inv_tail Hz) as Hu. cbn [app].
    rewrite (scan_nz sk acc b (u ++ d) Hb), (IH sk (acc ++ [b]) d Hu), <- app_assoc. reflexivity.
Qed.

Lemma gsx_nth_skipn_cons : forall (l : list Z) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - exact (IH n x Hn).
Qed.

Lemma gsx_firstn_nth_app : forall (l : list Z) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
Proof.
  induction l as [|a l IH]; intros n x Hn; [rewrite nth_error_nil in Hn; discriminate|].
  destruct n as [|n].
  - change (Some a = Some x) in Hn. injection Hn as ->. reflexivity.
  - change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l). rewrite (IH n x Hn). reflexivity.
Qed.

Lemma gsx_firstn_split : forall P Q (l : list Z), (P <= Q)%nat -> firstn Q l = firstn P l ++ firstn (Q - P) (skipn P l).
Proof.
  induction P as [|P IH]; intros Q l HPQ.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct Q as [|Q]; [lia|]. destruct l as [|a l].
    + rewrite skipn_nil, !firstn_nil. reflexivity.
    + change (a :: firstn Q l = a :: firstn P l ++ firstn (Q - P) (skipn P l)).
      rewrite (IH Q l) by lia. reflexivity.
Qed.

Lemma gsx_nth_skipn : forall (l : list Z) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l as [|a l IH]; intros n i.
  - rewrite skipn_nil, !nth_error_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|]. change (nth_error (skipn n l) i = nth_error l (n + i)). apply IH.
Qed.

Lemma gsx_nz_firstn : forall (l : list Z) k, (forall i, (i < k)%nat -> nth_error l i <> Some 0) -> nozero (firstn k l).
Proof.
  unfold nozero. induction l as [|a l IH]; intros k H.
  - rewrite firstn_nil. constructor.
  - destruct k as [|k]; [change (Forall (fun b => b <> 0) (@nil Z)); constructor|].
    change (Forall (fun b => b <> 0) (a :: firstn k l)). constructor.
    + intro E. apply (H 0%nat); [lia|]. rewrite E. reflexivity.
    + apply IH. intros i Hi. exact (H (S i) ltac:(lia)).
Qed.

Lemma gsx_scan_app_z : forall p sk acc q,
  fst (scan sk acc (p ++ 0 :: q)) = fst (scan false [] q) /\
  snd (scan sk acc (p ++ 0 :: q)) = snd (scan sk acc (p ++ [0])) ++ snd (scan false [] q).
Proof.
  induction p as [|b p IH]; intros sk acc q.
  - cbn [app]. rewrite gsx_scan_zero_fst, !gsx_scan_zero_snd. cbn [scan snd]. split; [reflexivity|].
    destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
  - cbn [app]. destruct (Z.eq_dec b 0) as [->|Hb].
    + rewrite gsx_scan_zero_fst, !gsx_scan_zero_snd. destruct (IH false [] q) as [I1 I2].
      split; [exact I1|]. rewrite I2. destruct (sk || Nat.ltb LINE_LIMIT (length acc))%bool; reflexivity.
    + rewrite (scan_nz sk acc b (p ++ 0 :: q) Hb), (scan_nz sk acc b (p ++ [0]) Hb). apply IH.
Qed.

Lemma gs_dline_len : forall s1 p q, (p <= q < length (dW s1))%nat -> length (dline s1 p q) = (q - p)%nat.
Proof. intros s1 p q H. unfold dline. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. lia. Qed.

Lemma gs_dline_nz : forall s1 p q,
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> nozero (dline s1 p q).
Proof.
  intros s1 p q H. unfold dline. apply gsx_nz_firstn. intros i Hi. rewrite gsx_nth_skipn. apply H. lia.
Qed.

(* ported from lib/Prog/drain_b.v:2929-2989 (dW_split, dW_pre_line, scan_pre, scan_line, drl_line) *)
Lemma gsx_dW_split : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  skipn p (dW s1) = dline s1 p q ++ 0 :: skipn (S q) (dW s1).
Proof.
  intros s1 p q HPQ HQ. unfold dline. rewrite <- (gsx_nth_skipn_cons _ _ _ HQ).
  rewrite <- (firstn_skipn (q - p) (skipn p (dW s1))) at 1.
  rewrite skipn_skipn. replace (q - p + p)%nat with q by lia. reflexivity.
Qed.

Lemma gsx_dW_pre_line : forall s1 p q, (p <= q)%nat -> nth_error (dW s1) q = Some 0 ->
  firstn (S q) (dW s1) = firstn p (dW s1) ++ dline s1 p q ++ [0].
Proof.
  intros s1 p q HPQ HQ. rewrite (gsx_firstn_nth_app _ _ _ HQ), (gsx_firstn_split p q _ HPQ), <- app_assoc.
  reflexivity.
Qed.

Lemma gsx_scan_pre : forall s1 p r, dbound s1 p ->
  fst (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = fst (scan (dskp s1 p) [] r) /\
  snd (scan (drain_b_c.ds_skip s1) [] (firstn p (dW s1) ++ r)) = drlp s1 p ++ snd (scan (dskp s1 p) [] r).
Proof.
  intros s1 p r (HP & HN). destruct p as [|p]; [split; reflexivity|].
  assert (HN' : nth_error (dW s1) p = Some 0).
  { destruct HN as [H0|H0]; [discriminate|]. replace p with (S p - 1)%nat by lia. exact H0. }
  unfold drlp, dskp. cbn [Nat.eqb]. rewrite (gsx_firstn_nth_app _ _ _ HN'), <- app_assoc. cbn [app].
  exact (gsx_scan_app_z (firstn p (dW s1)) (drain_b_c.ds_skip s1) [] r).
Qed.

Lemma gsx_scan_line : forall sk ln r, nozero ln ->
  fst (scan sk [] (ln ++ 0 :: r)) = fst (scan false [] r) /\
  snd (scan sk [] (ln ++ 0 :: r)) =
    (if (sk || Nat.ltb LINE_LIMIT (length ln))%bool then [] else [ln]) ++ snd (scan false [] r).
Proof.
  intros sk ln r Hz. rewrite (gsx_scan_nz_app ln sk [] _ Hz). cbn [app].
  rewrite gsx_scan_zero_fst, gsx_scan_zero_snd.
  split; [reflexivity|]. destruct (sk || Nat.ltb LINE_LIMIT (length ln))%bool; reflexivity.
Qed.

Lemma gsx_drl_line : forall s1 p q, dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) ->
  drlp s1 (S q) = drlp s1 p ++ (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) /\
  drlq s1 p = (if (dskp s1 p || Nat.ltb LINE_LIMIT (q - p))%bool then [] else [dline s1 p q]) ++ drlq s1 (S q).
Proof.
  intros s1 p q HB HPQ HQ HNZ.
  pose proof (gs_dline_nz s1 p q HNZ) as Hz. rewrite <- (gs_dline_len s1 p q HPQ). split.
  - unfold drlp at 1. rewrite (gsx_dW_pre_line s1 p q (proj1 HPQ) HQ), (proj2 (gsx_scan_pre s1 p _ HB)).
    rewrite (proj2 (gsx_scan_line (dskp s1 p) (dline s1 p q) [] Hz)). cbn [scan snd]. rewrite app_nil_r.
    reflexivity.
  - unfold drlq at 1. rewrite (gsx_dW_split s1 p q (proj1 HPQ) HQ).
    rewrite (proj2 (gsx_scan_line (dskp s1 p) (dline s1 p q) _ Hz)). reflexivity.
Qed.

Lemma gs_drl : forall s1 p q,
dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false ->
(q - p <= LINE_LIMIT)%nat ->
drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] /\
drlq s1 p = dline s1 p q :: drlq s1 (S q) /\
dskp s1 (S q) = false.
Proof.
  intros s1 p q HB HPQ HQ HNZ HK HL.
  destruct (gsx_drl_line s1 p q HB HPQ HQ HNZ) as [E1 E2].
  rewrite HK, (proj2 (Nat.ltb_ge LINE_LIMIT (q - p)) HL) in E1, E2. cbn [orb app] in E1, E2.
  split; [exact E1|]. split; [exact E2|reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (2) the line loop's model values after one more line
   --------------------------------------------------------------------------------------------------------- *)

(* ported from lib/Prog/drain_b.v:2844-2868 (with_nul_cons, lrun_one, lrun_app) *)
Lemma gsx_with_nul_cons : forall l r, with_nul (l :: r) = (l ++ [0]) ++ with_nul r.
Proof. reflexivity. Qed.

Lemma gsx_lrun_one : forall lv mx0 no0 cp0 H0 ka0 l,
  lrun lv mx0 no0 cp0 H0 ka0 [l] =
  (send_line_b_c.send_line_cap lv mx0 no0 cp0 (Z.of_nat (length l) + 1), seen_arr H0 l, seen_ka H0 ka0 l).
Proof.
  intros lv mx0 no0 cp0 H0 ka0 l. unfold lrun. cbn [drain_b_c.lines_run fst snd]. rewrite seen_tr_m. reflexivity.
Qed.

Lemma gsx_lrun_app : forall lv mx0 l1 l2 no0 cp0 H0 ka0,
  lrun lv mx0 no0 cp0 H0 ka0 (l1 ++ l2) =
  lrun lv mx0 (no0 + Z.of_nat (length (with_nul l1))) (fst (fst (lrun lv mx0 no0 cp0 H0 ka0 l1)))
    (snd (fst (lrun lv mx0 no0 cp0 H0 ka0 l1))) (snd (lrun lv mx0 no0 cp0 H0 ka0 l1)) l2.
Proof.
  intros lv mx0 l1. induction l1 as [|l r IH]; intros l2 no0 cp0 H0 ka0.
  - rewrite app_nil_l. change (with_nul []) with (@nil Z). cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - assert (C : forall nb cb Hb kb ls, lrun lv mx0 nb cb Hb kb (l :: ls) =
                 lrun lv mx0 (nb + (Z.of_nat (length l) + 1))
                   (send_line_b_c.send_line_cap lv mx0 nb cb (Z.of_nat (length l) + 1))
                   (seen_arr Hb l) (seen_ka Hb kb l) ls).
    { intros nb cb Hb kb ls. unfold lrun at 1. cbn [drain_b_c.lines_run fst snd]. rewrite lines_run_m, seen_tr_m.
      reflexivity. }
    rewrite <- app_comm_cons, !C, IH.
    replace (no0 + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul r)))
      with (no0 + Z.of_nat (length (with_nul (l :: r))))
      by (rewrite gsx_with_nul_cons, !length_app; cbn [length]; lia).
    reflexivity.
Qed.

Lemma gs_dlno : forall s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlno s1 (S q) = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1.
Proof.
  intros s1 p q E. unfold dlno. rewrite E. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
  rewrite app_nil_r, !length_app. cbn [length]. lia.
Qed.

Lemma gs_dlrun : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlrun cx s1 (S q) =
(send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
   (Z.of_nat (length (dline s1 p q)) + 1),
 seen_arr (dlH cx s1 p) (dline s1 p q),
 seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)).
Proof.
  intros cx s1 p q E. unfold dlrun at 1. rewrite E, gsx_lrun_app, gsx_lrun_one.
  unfold dlno, dloc, dlH, dlka, dlrun. reflexivity.
Qed.

Lemma gs_dloc : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dloc cx s1 (S q) = send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
  (Z.of_nat (length (dline s1 p q)) + 1).
Proof.
  intros cx s1 p q E. change (dloc cx s1 (S q)) with (fst (fst (dlrun cx s1 (S q)))).
  rewrite (gs_dlrun cx s1 p q E). reflexivity.
Qed.

Lemma gs_dlH : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlH cx s1 (S q) = seen_arr (dlH cx s1 p) (dline s1 p q).
Proof.
  intros cx s1 p q E. change (dlH cx s1 (S q)) with (snd (fst (dlrun cx s1 (S q)))).
  rewrite (gs_dlrun cx s1 p q E). reflexivity.
Qed.

Lemma gs_dlka : forall (cx : dcx) s1 p q, drlp s1 (S q) = drlp s1 p ++ [dline s1 p q] ->
dlka cx s1 (S q) = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q).
Proof.
  intros cx s1 p q E. change (dlka cx s1 (S q)) with (snd (dlrun cx s1 (S q))).
  rewrite (gs_dlrun cx s1 p q E). reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (3) the held-key set: index_of from the search loop's invariant, and the four shapes of seen_tr / seen_arr
   --------------------------------------------------------------------------------------------------------- *)

Lemma gs_index_none : forall (x : list Z) (H : list (list Z)),
(forall i, (i < length H)%nat -> nth i H [] <> x) -> index_of x H = None.
Proof.
  intros x H. induction H as [|y H IH]; intros Hn; [reflexivity|].
  cbn [index_of]. destruct (key_eqb y x) eqn:E.
  - exfalso. apply key_eqb_spec in E. apply (Hn 0%nat); [cbn [length]; lia|exact E].
  - rewrite IH; [reflexivity|]. intros i Hi. exact (Hn (S i) ltac:(cbn [length]; lia)).
Qed.

Lemma gs_index_some : forall (x : list Z) (H : list (list Z)) n,
(n < length H)%nat -> nth n H [] = x -> (forall i, (i < n)%nat -> nth i H [] <> x) ->
index_of x H = Some n.
Proof.
  intros x H. induction H as [|y H IH]; intros n Hn Hx Hb; [cbn [length] in Hn; lia|].
  cbn [index_of]. destruct n as [|n].
  - cbn [nth] in Hx. subst y. rewrite (proj2 (key_eqb_spec x x) eq_refl). reflexivity.
  - destruct (key_eqb y x) eqn:E.
    + exfalso. apply key_eqb_spec in E. exact (Hb 0%nat ltac:(lia) E).
    + rewrite (IH n); [reflexivity|cbn [length] in Hn; lia|exact Hx|].
      intros i Hi. exact (Hb (S i) ltac:(lia)).
Qed.

Lemma gs_index_lt : forall (x : list Z) H n, index_of x H = Some n -> (n < length H)%nat /\ nth n H [] = x.
Proof.
  intros x H n E. destruct (index_of_some x H n E) as (a & b & -> & <-).
  rewrite length_app. cbn [length]. split; [lia|]. apply nth_middle.
Qed.

Lemma gs_seen_begin_new : forall H ka l x j ha ks, gesture l = Some (GBegin, x) -> index_of x H = None ->
seen_arr H l = H ++ [x] /\
drain_b_c.seen_tr H ka l j ha ks =
  ([if ka =? 0 then RelayRunT.RMalloc ((Z.of_nat (length H) + 1) * 8)
    else RelayRunT.RRealloc ka ((Z.of_nat (length H) + 1) * 8) ha;
    RelayRunT.RMalloc (Z.of_nat (length x) + 1)],
   (Z.of_nat (length H) + 1) * 8, (RelayRunT.Ret j, ks ++ [RelayRunT.Ret (S j)])) /\
seen_ka H ka l = (Z.of_nat (length H) + 1) * 8.
Proof.
  intros H ka l x j ha ks G I. unfold seen_arr, seen_ka, drain_b_c.seen_tr. rewrite G. cbv beta iota.
  rewrite I. split; [reflexivity|split; reflexivity].
Qed.

Lemma gs_seen_begin_old : forall H ka l x n j ha ks, gesture l = Some (GBegin, x) -> index_of x H = Some n ->
seen_arr H l = H /\ drain_b_c.seen_tr H ka l j ha ks = ([], ka, (ha, ks)) /\ seen_ka H ka l = ka.
Proof.
  intros H ka l x n j ha ks G I. unfold seen_arr, seen_ka, drain_b_c.seen_tr. rewrite G. cbv beta iota.
  rewrite I. split; [reflexivity|split; reflexivity].
Qed.

Lemma gs_seen_end_old : forall H ka l x n j ha ks, gesture l = Some (GEnd, x) -> index_of x H = Some n ->
seen_arr H l = swap_remove [] n H /\
drain_b_c.seen_tr H ka l j ha ks =
  ([RelayRunT.RFree (Z.of_nat (length x) + 1) (nth n ks RelayRunF.adr0)], ka, (ha, swap_remove RelayRunF.adr0 n ks)) /\
seen_ka H ka l = ka.
Proof.
  intros H ka l x n j ha ks G I. unfold seen_arr, seen_ka, drain_b_c.seen_tr. rewrite G. cbv beta iota.
  rewrite I. split; [reflexivity|split; reflexivity].
Qed.

Lemma gs_seen_end_new : forall H ka l x j ha ks, gesture l = Some (GEnd, x) -> index_of x H = None ->
seen_arr H l = H /\ drain_b_c.seen_tr H ka l j ha ks = ([], ka, (ha, ks)) /\ seen_ka H ka l = ka.
Proof.
  intros H ka l x j ha ks G I. unfold seen_arr, seen_ka, drain_b_c.seen_tr. rewrite G. cbv beta iota.
  rewrite I. split; [reflexivity|split; reflexivity].
Qed.

Lemma gs_seen_len : forall H l, (length (seen_arr H l) <= S (length H))%nat.
Proof.
  intros H l. unfold seen_arr. destruct (gesture l) as [[[|] x]|]; cbv beta iota.
  - destruct (index_of x H); [lia|]. rewrite length_app. cbn [length]. lia.
  - destruct (index_of x H) as [n|]; [|lia]. unfold swap_remove.
    pose proof (firstn_le_length (length H - 1) (set_nth n (last H []) H)). lia.
  - lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (4) the relay entry's key list under the two updates (append; swap-remove), and its byte image
   --------------------------------------------------------------------------------------------------------- *)

(* list helpers for set_nth / swap_remove / key_ptrs *)
Lemma gsx_length_set_nth : forall {A} n (y : A) l, length (set_nth n y l) = length l.
Proof.
  intros A n y l. revert n. induction l as [|h t IH]; intros [|n]; cbn [set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma gsx_nth_set_nth : forall {A} n (y : A) l i d, (n < length l)%nat ->
  nth i (set_nth n y l) d = if Nat.eqb i n then y else nth i l d.
Proof.
  intros A n y l. revert n. induction l as [|h t IH]; intros n i d Hn; [cbn [length] in Hn; lia|].
  destruct n as [|n], i as [|i]; cbn [set_nth nth Nat.eqb]; [reflexivity|reflexivity|reflexivity|].
  apply IH. cbn [length] in Hn. lia.
Qed.

Lemma gsx_nth_firstn : forall {A} (l : list A) k i d, (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  intros A l. induction l as [|h t IH]; intros k i d Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma gsx_last_nth : forall {A} (l : list A) d, last l d = nth (length l - 1) l d.
Proof.
  intros A l d. induction l as [|x l _] using rev_ind; [reflexivity|].
  rewrite last_last, length_app. cbn [length]. rewrite Nat.add_sub. symmetry. apply nth_middle.
Qed.

Lemma gsx_map_set_nth : forall {A B} (f : A -> B) n y l, map f (set_nth n y l) = set_nth n (f y) (map f l).
Proof.
  intros A B f n y l. revert n. induction l as [|h t IH]; intros [|n]; cbn [set_nth map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma gsx_last_map : forall {A B} (f : A -> B) l d e, f d = e -> last (map f l) e = f (last l d).
Proof.
  intros A B f l d e He. induction l as [|a l IH]; [symmetry; exact He|].
  destruct l as [|b l]; [reflexivity|]. exact IH.
Qed.

Lemma gsx_map_swap_remove : forall {A B} (f : A -> B) d e n l, f d = e ->
  map f (swap_remove d n l) = swap_remove e n (map f l).
Proof.
  intros A B f d e n l He. unfold swap_remove.
  rewrite length_map, <- firstn_map, gsx_map_set_nth, (gsx_last_map f l d e He). reflexivity.
Qed.

Lemma gsx_firstn_len : forall {A} (l1 l2 : list A), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros A l1 l2. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. Qed.

Lemma gsx_firstn_len_add : forall {A} (l1 l2 : list A) m, firstn (length l1 + m) (l1 ++ l2) = l1 ++ firstn m l2.
Proof.
  intros A l1 l2 m. rewrite firstn_app, firstn_all2 by lia. replace (length l1 + m - length l1)%nat with m by lia.
  reflexivity.
Qed.

Lemma gsx_skipn_len0 : forall {A} (l1 l2 : list A), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros A l1 l2. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma gsx_skipn_len : forall {A} (l1 l2 : list A) m, skipn (length l1 + m) (l1 ++ l2) = skipn m l2.
Proof.
  intros A l1 l2 m. rewrite skipn_app, skipn_all2 by lia. replace (length l1 + m - length l1)%nat with m by lia.
  reflexivity.
Qed.

Lemma gsx_skipn_le8 : forall v (l : list byte), skipn 8 (Mem.le8 v ++ l) = l.
Proof. intros v l. rewrite <- (Mem.length_le8 v). apply gsx_skipn_len0. Qed.

Lemma gsx_key_ptrs_cat : forall a b, key_ptrs (a ++ b) = key_ptrs a ++ key_ptrs b.
Proof. intros a b. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.

Lemma gsx_key_ptrs_cons : forall k b, key_ptrs (k :: b) = Mem.le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs b.
Proof. reflexivity. Qed.

Lemma gs_keys_texts_len : forall ks, length (drain_b_c.keys_texts ks) = length ks.
Proof. intros ks. unfold drain_b_c.keys_texts. apply length_map. Qed.

Lemma gs_keys_texts_nth : forall ks n, (n < length ks)%nat ->
nth n (drain_b_c.keys_texts ks) [] = bzs (key_text (nth n ks (0, [], []))).
Proof.
  intros ks n _. unfold drain_b_c.keys_texts.
  change (@nil Z) with ((fun k : Z * list byte * list byte => bzs (key_text k)) (0, [], [])). apply List.map_nth.
Qed.

Lemma gs_keys_texts_app : forall ks k,
drain_b_c.keys_texts (ks ++ [k]) = drain_b_c.keys_texts ks ++ [bzs (key_text k)].
Proof. intros ks k. unfold drain_b_c.keys_texts. rewrite map_app. reflexivity. Qed.

Lemma gs_keys_texts_swap : forall ks n, (n < length ks)%nat ->
drain_b_c.keys_texts (swap_remove (0, [], []) n ks) = swap_remove [] n (drain_b_c.keys_texts ks).
Proof. intros ks n _. unfold drain_b_c.keys_texts. apply gsx_map_swap_remove. reflexivity. Qed.

Lemma gs_swap_remove_len : forall {A} (d : A) n l, (n < length l)%nat ->
length (swap_remove d n l) = (length l - 1)%nat.
Proof.
  intros A d n l Hn. unfold swap_remove. rewrite firstn_length_le; [reflexivity|]. rewrite gsx_length_set_nth. lia.
Qed.

Lemma gs_swap_remove_nth : forall {A} (d : A) n l i, (n < length l)%nat -> (i < length l - 1)%nat ->
nth i (swap_remove d n l) d = (if Nat.eqb i n then nth (length l - 1) l d else nth i l d).
Proof.
  intros A d n l i Hn Hi. unfold swap_remove.
  rewrite gsx_nth_firstn by exact Hi. rewrite gsx_nth_set_nth by exact Hn.
  destruct (Nat.eqb i n); [apply gsx_last_nth|reflexivity].
Qed.

Lemma gs_swap_remove_perm : forall {A} (d : A) n l, (n < length l)%nat ->
Permutation l (nth n l d :: swap_remove d n l).
Proof.
  intros A d n l Hn. destruct (nth_split l d Hn) as (a & b & E & Ha).
  set (x := nth n l d) in *. clearbody x. subst l n. apply swap_remove_perm.
Qed.

Lemma gs_swap_remove_in : forall {A} (d : A) n l x, (n < length l)%nat ->
In x (swap_remove d n l) -> In x l.
Proof.
  intros A d n l x Hn Hx. apply (Permutation_in _ (Permutation_sym (gs_swap_remove_perm d n l Hn))).
  right. exact Hx.
Qed.

(* the held array's byte image: key_ptrs is the 8-byte-per-slot concatenation *)
Lemma gs_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  rewrite gsx_key_ptrs_cons, length_app, Mem.length_le8, IH. cbn [length]. lia.
Qed.

Lemma gs_key_ptrs_app : forall ks k, key_ptrs (ks ++ [k]) = key_ptrs ks ++ Mem.le8 (Z_to_bv 64 (key_addr k)).
Proof. intros ks k. unfold key_ptrs. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.

Lemma gs_key_ptrs_firstn : forall ks m, (m <= length ks)%nat ->
key_ptrs (firstn m ks) = firstn (8 * m) (key_ptrs ks).
Proof.
  intros ks m Hm. rewrite <- (firstn_skipn m ks) at 2. rewrite gsx_key_ptrs_cat.
  replace (8 * m)%nat with (length (key_ptrs (firstn m ks)))
    by (rewrite gs_key_ptrs_len, firstn_length_le; lia).
  symmetry. apply gsx_firstn_len.
Qed.

Lemma gs_key_ptrs_set : forall ks n k, (n < length ks)%nat ->
key_ptrs (set_nth n k ks) =
firstn (8 * n) (key_ptrs ks) ++ Mem.le8 (Z_to_bv 64 (key_addr k)) ++ skipn (8 * n + 8) (key_ptrs ks).
Proof.
  intros ks n k Hn. destruct (nth_split ks (0, [], []) Hn) as (a & b & E & Ha).
  set (x := nth n ks (0, [], [])) in *. clearbody x. subst ks n.
  rewrite set_nth_middle, !gsx_key_ptrs_cat, !gsx_key_ptrs_cons, <- (gs_key_ptrs_len a).
  rewrite gsx_firstn_len, gsx_skipn_len, gsx_skipn_le8. reflexivity.
Qed.

(* the array after an end: slot n takes the last slot's pointer and the array is one slot shorter.  For a slot n
   below the last one, the live 8 * (|ks| - 1) bytes; ... *)
Lemma gs_key_ptrs_swap_lt : forall ks n, (n < length ks - 1)%nat ->
key_ptrs (swap_remove (0, [], []) n ks) =
firstn (8 * n) (key_ptrs ks) ++
Mem.le8 (Z_to_bv 64 (key_addr (nth (length ks - 1) ks (0, [], [])))) ++
firstn (8 * (length ks - 1) - (8 * n + 8)) (skipn (8 * n + 8) (key_ptrs ks)).
Proof.
  intros ks n Hn. assert (Hn' : (n < length ks)%nat) by lia.
  destruct (nth_split ks (0, [], []) Hn') as (a & b & E & Ha).
  set (x := nth n ks (0, [], [])) in *. clearbody x. subst ks n.
  assert (Hb : b <> []) by (intros ->; rewrite length_app in Hn; cbn [length] in Hn; lia).
  destruct (@exists_last _ b Hb) as (b' & z & ->).
  assert (N : nth (length (a ++ x :: b' ++ [z]) - 1) (a ++ x :: b' ++ [z]) (0, [], []) = z).
  { rewrite <- gsx_last_nth.
    replace (a ++ x :: b' ++ [z]) with ((a ++ x :: b') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    apply last_last. }
  assert (L : length (a ++ x :: b' ++ [z]) = (length a + length b' + 2)%nat).
  { rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
  rewrite swap_remove_mid, N, L.
  repeat first [rewrite gsx_key_ptrs_cat | rewrite gsx_key_ptrs_cons].
  replace (8 * (length a + length b' + 2 - 1) - (8 * length a + 8))%nat with (length (key_ptrs b'))
    by (rewrite gs_key_ptrs_len; lia).
  rewrite <- (gs_key_ptrs_len a), gsx_firstn_len, gsx_skipn_len, gsx_skipn_le8, gsx_firstn_len. reflexivity.
Qed.

(* ... for any slot n, the first 8 * (|ks| - 1) bytes of the array after the store of the last slot's pointer
   into slot n. *)
Lemma gs_key_ptrs_swap_cut : forall ks n, (n < length ks)%nat ->
key_ptrs (swap_remove (0, [], []) n ks) =
firstn (8 * (length ks - 1))
  (firstn (8 * n) (key_ptrs ks) ++
   Mem.le8 (Z_to_bv 64 (key_addr (nth (length ks - 1) ks (0, [], [])))) ++
   skipn (8 * n + 8) (key_ptrs ks)).
Proof.
  intros ks n Hn. destruct (nth_split ks (0, [], []) Hn) as (a & b & E & Ha).
  set (x := nth n ks (0, [], [])) in *. clearbody x. subst ks n.
  destruct b as [|b0 b1].
  - rewrite swap_remove_last.
    replace (length (a ++ [x]) - 1)%nat with (length a) by (rewrite length_app; cbn [length]; lia).
    rewrite gsx_key_ptrs_cat, <- (gs_key_ptrs_len a), !gsx_firstn_len. reflexivity.
  - destruct (@exists_last _ (b0 :: b1) ltac:(discriminate)) as (b' & z & Eb). rewrite Eb.
    assert (N : nth (length (a ++ x :: b' ++ [z]) - 1) (a ++ x :: b' ++ [z]) (0, [], []) = z).
    { rewrite <- gsx_last_nth.
      replace (a ++ x :: b' ++ [z]) with ((a ++ x :: b') ++ [z]) by (rewrite <- app_assoc; reflexivity).
      apply last_last. }
    assert (L : length (a ++ x :: b' ++ [z]) = (length a + length b' + 2)%nat).
    { rewrite length_app. cbn [length]. rewrite length_app. cbn [length]. lia. }
    rewrite swap_remove_mid, N, L.
    repeat first [rewrite gsx_key_ptrs_cat | rewrite gsx_key_ptrs_cons].
    replace (8 * (length a + length b' + 2 - 1))%nat
      with (length (key_ptrs a) + (length (Mem.le8 (Z_to_bv 64 (key_addr z))) + (length (key_ptrs b') + 0)))%nat
      by (rewrite !gs_key_ptrs_len, Mem.length_le8; lia).
    rewrite <- (gs_key_ptrs_len a), gsx_firstn_len, gsx_skipn_len, gsx_skipn_le8, !gsx_firstn_len_add.
    cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma gs_key_ptrs_len_swap : forall ks n, (n < length ks)%nat ->
length (key_ptrs (swap_remove (0, [], []) n ks)) = (8 * (length ks - 1))%nat.
Proof. intros ks n Hn. rewrite gs_key_ptrs_len, (gs_swap_remove_len _ n ks Hn). reflexivity. Qed.

Lemma gs_keys_texts_swap_nth : forall ks n i, (n < length ks)%nat -> (i < length ks - 1)%nat ->
nth i (drain_b_c.keys_texts (swap_remove (0, [], []) n ks)) [] =
(if Nat.eqb i n then bzs (key_text (nth (length ks - 1) ks (0, [], []))) else bzs (key_text (nth i ks (0, [], [])))).
Proof.
  intros ks n i Hn Hi. rewrite (gs_keys_texts_swap ks n Hn).
  rewrite gs_swap_remove_nth by (rewrite gs_keys_texts_len; lia).
  rewrite gs_keys_texts_len. destruct (Nat.eqb i n); apply gs_keys_texts_nth; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   (5) the history clause: upds over one more relayed line
   --------------------------------------------------------------------------------------------------------- *)

Lemma gs_upds_snoc : forall G ls l, upds G (ls ++ [l]) = upd (upds G ls) l.
Proof. intros G ls l. unfold upds. rewrite fold_left_app. reflexivity. Qed.

Lemma gs_with_nul_app : forall l1 l2, with_nul (l1 ++ l2) = with_nul l1 ++ with_nul l2.
Proof. intros l1 l2. unfold with_nul. rewrite map_app, concat_app. reflexivity. Qed.

Lemma gs_with_nul_one : forall l, with_nul [l] = l ++ [0].
Proof. intros l. unfold with_nul. cbn [map concat]. apply app_nil_r. Qed.

End b.
End a.
