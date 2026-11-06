(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x837c8 .. 0x839b8, gesture_seen's held-array search and update, relay.c:100-119
   inlined), in the form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (a loop over
   concrete cut states) and lib/A/AC8h.v (call sites), and of this lane's W_send_line_entry.v.
   The statement is lib/A/W_drain_cx.v's dr_gs_stmt; the Section header below is that file's, verbatim.

   DGS (0x837c8) -> DLN (S q) (0x836f4), in three stages:
     gs_scan  0x837c8 .. 0x8389c   nheld <= 0, or the held-key search loop 0x83838 .. 0x83874
                                   (strlen 0x83850, strncmp 0x83864; its own induction, below)
     gs_add   0x8389c .. 0x839b8   a begin not held: realloc #2 0x838c0, strndup 0x838e0,
                                   s->held = res, held[nheld] = copy, nheld += 1
     gs_free  0x83940 .. 0x839b8   an end held at slot n: free #2 0x8394c, nheld -= 1,
                                   held[n] = held[nheld]
   and the three other exits of the search go straight to DLN (an end not held, a begin held). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

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

(* The segment's own program counters (fuzz_reply.asan, slot = (addr - 0x822ec) / 4; AF_fr_drain = 0xdf0).
   0x8389c - 0x830dc = 0x7c0; 0x83940 - 0x830dc = 0x864; 0x83838 - 0x830dc = 0x75c. *)
Definition A_dr_hloop : Z := AF_fr_drain + 0x75c.   (* 0x83838, the held-key search loop's head *)
Definition A_dr_add : Z := AF_fr_drain + 0x7c0.     (* 0x8389c, after the search: the two tests *)
Definition A_dr_free : Z := AF_fr_drain + 0x864.    (* 0x83940, an end whose key is held at slot n *)

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
(* the walk's globals are .data / .bss cells, never read-only image bytes (the pinned placement decides it) *)
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v) *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
(* memchr: the general text (a Theorem Labs lane's amemchr_realizesM, lib/Rt/MemchrDef.v; proved on our image by a Theorem Labs lane as
   memchr_icpt_realizesM).  Its constant window is the musl memchr's masks at 0x10350 .. 0x10370 (HCROM). *)
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
(* the allocator instance's granule-tail fact (W_drain_cx.v ALLOC_TAIL): a held key is represented over exactly
   its |text| + 1 bytes (ruling (A)); the strlen of a key reads to the end of its granule. *)
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- The relay entry in the line loop's form across a step that keeps its footprint. ----
   W_rep.v:334 aentry_ok_kept, for W_drain_cx.v:231 aentry_okx (the two differ only in the conjuncts
   about s->buf's contents, which carry no memory). *)
Lemma gs_aentry_okx_kept : forall ly S W mem ly' S' W' mem' e,
aentry_okx B ly S W mem e ->
akept W mem W' mem' (aentry_fp e) ->
(forall b, In b (aentry_blks e) -> In b (ablocks B ly' S')) ->
aentry_okx B ly' S' W' mem' e.
Proof.
intros ly S W mem ly' S' W' mem' e
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14) HK HB.
do 8 (split; [assumption|]).
split.
{ destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|].
  split; [apply HB; unfold aentry_blks; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  unfold aentry_fp. rewrite Ec. left. reflexivity. }
split; [exact H10|].
split.
{ destruct H11 as [H11 | (Hz & Hin & Hk1 & Hk2 & Hg)]; [left; exact H11|right].
  assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
  split; [exact Hz|].
  split; [apply HB; unfold aentry_blks; apply in_or_app; right; rewrite Ez; left; reflexivity|].
  split; [exact Hk1|]. split; [exact Hk2|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_hp e) (bzs (key_ptrs (re_keys e))))); [|exact Hx].
  unfold aentry_fp. apply in_or_app. right. left. reflexivity. }
split; [exact H12|]. split; [exact H13|].
rewrite Forall_forall in H14 |- *. intros k Hk. destruct (H14 k Hk) as (K1 & K2 & K3).
split; [apply HB; unfold aentry_blks; apply in_or_app; right; apply in_or_app; right;
  apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
split; [|exact K3].
apply (akept_garr8 W mem); [|exact K2].
intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
unfold aentry_fp. apply in_or_app. right. right.
apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* ---- Opening and closing the walk's journal at an allocator site. ----
   W_journal.v's allocator rules (arealloc_cf_rule, afree_cf_rule, astrndup_cf_rule) are stated over the
   donor journal `ajournal`; drain's walk carries `@ajournal_gx _ SK ... (G_DR B RG) 0 []`.  At XO = 0 the
   two differ only by the overlaid start memory memS, which the rules leave alone, so a site is: open,
   apply the rule, close with the same memS. *)
Lemma gs_gx_open : forall G STK sp0 FP ly S W0 mem md own lyc Sc (W : world SEGS) memc mdc k,
@ajournal_gx _ SK SEGS B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal SEGS B STK sp0 FP ly S W0 memS md own lyc Sc W memc mdc k.
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.

Lemma gs_gx_close : forall G STK sp0 FP ly S W0 mem md own ly2 S2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal SEGS B STK sp0 FP ly S W0 memS md own ly2 S2 W2 mem2 md2 k2 ->
@ajournal_gx _ SK SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (ajournal_gx_pack SEGS B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.

(* ---- What the segment's allocator calls cost. ----
   The requests of this round's gesture_seen are a prefix of the trace the cut predicate still owes
   (GSfut's `tl = fst (fst (seen_tr ...)) ++ tl2`), so the three meters split over an append, and the
   `mo_ok` premise of each allocator rule comes from dbud through Reusable/YC5d.v's mok_station. *)
Lemma gs_tr_cost_app : forall (t1 t2 : dtrace), tr_cost MT (t1 ++ t2) = tr_cost MT t1 + tr_cost MT t2.
Proof.
intros t1 t2. unfold tr_cost. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma gs_tr_alloc_app : forall (t1 t2 : dtrace), tr_alloc (t1 ++ t2) = tr_alloc t1 + tr_alloc t2.
Proof.
intros t1 t2. unfold tr_alloc. induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

Lemma gs_tr_max_nonneg : forall (t : dtrace), 0 <= tr_max t.
Proof.
intros t. unfold tr_max. induction t as [|ev t IH]; [cbn [fold_right]; lia|].
cbn [fold_right]. destruct ev; lia.
Qed.

Lemma gs_tr_max_app : forall (t1 t2 : dtrace), tr_max (t1 ++ t2) = Z.max (tr_max t1) (tr_max t2).
Proof.
intros t1 t2. pose proof (gs_tr_max_nonneg t2) as H2. unfold tr_max in *.
induction t1 as [|ev t1 IH]; [cbn [app fold_right]; lia|].
cbn [app fold_right]. rewrite IH. destruct ev; lia.
Qed.

(* ---- Keeping a byte across a step of the segment. ----
   Everything drain's cut predicates read lies below alloc_ceiling (the image's globals and the heap
   blocks), so one unchanged-view-and-presence pair carries the whole `akept` footprint; this is
   W_send_line_entry.v's kept_lo with presence in place of mem_grows. *)
Lemma gs_kept_lo : forall (W : world SEGS) m m' a,
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
0 <= a < alloc_ceiling -> abyte_kept W m W m' a.
Proof.
intros W m m' a HK HP Ha. split; [exact (HK a Ha)|].
unfold arm. apply (writable_kept (w_H W) m m' a (HP a)).
Qed.

Lemma gs_akept_of : forall (W : world SEGS) m m' fp,
(forall x, 0 <= x < alloc_ceiling -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
(forall r, In r fp -> forall a, fst r <= a < snd r -> 0 <= a < alloc_ceiling) ->
akept W m W m' fp.
Proof.
intros W m m' fp HK HP Hlow r Hr a Ha. exact (gs_kept_lo W m m' a HK HP (Hlow r Hr a Ha)).
Qed.

Lemma gs_mo_ok_of : forall cx S1 spent tl c,
mo_ok MT (dxS cx) (dcost MT cx) -> dbud MT MMAX cx S1 spent tl ->
0 <= c -> c <= tr_cost MT tl -> mo_ok MT S1 c.
Proof.
intros cx S1 spent tl c Hok (Hle & Hsp & Hcost & _ & _) Hc Hct.
exact (mok_station MT (dxS cx) S1 (dcost MT cx) spent c MTL Hok Hle Hc ltac:(lia)).
Qed.

(* ---- The line that gesture_seen was called on, and the line loop's core at that point. ----
   This is exactly the geometry and the LCORE that W_drain_cx.v's DGS carries; the two intermediate cut
   predicates below and the three stage lemmas quote it unchanged, so that composing them is an
   application. *)
Definition GSF (s1 : drain_b_c.dstate) (p q : nat) : Prop :=
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat.

Definition GSno (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat) : Z :=
dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1.
Definition GSoc (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat) : Z :=
send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
  (Z.of_nat (length (dline s1 p q)) + 1).

Definition GSB (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE B MT MMAX RG cx s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

Definition GSfut (cx : dcx) (s1 : drain_b_c.dstate) (p q : nat)
(a : drain_b_c.dadr) (jb : nat) (o ha : RelayRunT.addr YO0i.sptr) (ks : list (RelayRunT.addr YO0i.sptr))
(tl : dtrace) : Prop :=
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (GSno cx s1 p q) (GSoc cx s1 p q) (drlq s1 (S q)) jb o ha ks tl.

(* ---- GA (0x8389c): the search is over and the key is NOT held; a0 = a1 = s->nheld, a2 = (&s->held) >> 3,
   s3 = bg.  The two tests at 0x8389c and 0x838a0 decide: an end returns, a begin adds the key. ---- *)
Definition GA (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_add) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\ getr regs1 19 = w64 bg /\
getr regs1 10 = w64 (re_nheld e1) /\ getr regs1 11 = w64 (re_nheld e1) /\
getr regs1 12 = w64 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GSB cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* ---- GF (0x83940): an end whose key is held at slot n.  s3 = the shadow byte's address of the slot,
   s10 = &s->held[n], s4 = 8 n; s6 and s11 are back to s and &s->used. ---- *)
Definition GF (cx : dcx) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (jj n : nat),
c1 = cfg_at SEGS (BASE + A_dr_free) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 26 = w64 (re_hp e1 + 8 * Z.of_nat n) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
(n < length (re_keys e1))%nat /\
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n /\
GSF s1 p q /\
GSB cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

(* ---- The three stages. ---- *)

Definition gs_scan_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> DGS B MT MMAX RG cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GA cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GF cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition gs_add_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> GA cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

Definition gs_free_stmt : Prop :=
forall cx s1 D p q W1 c1,
DBASE B MT MMAX RG cx -> GF cx s1 D p q W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).

(* ---- The segment: the search, then whichever of the two updates the search chose. ---- *)
Theorem dr_gs_of : gs_scan_stmt -> gs_add_stmt -> gs_free_stmt -> dr_gs_stmt B MT MMAX RG.
Proof.
intros SCAN ADD FREE cx s1 D p q W1 c1 HB HGS HN.
apply (SCAN cx s1 D p q W1 c1 HB HGS HN).
- intros W2 c2 HGA. exact (ADD cx s1 D p q W2 c2 HB HGA HN).
- intros W2 c2 HGF. exact (FREE cx s1 D p q W2 c2 HB HGF HN).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): the gs stage over W_drain_cx_x.v's Section
   variables (B PST ARx MT RP MMAX RG), with the entry's ghost list Hp and budget kr after cx and a cut's own ghost
   list Hp1 after S1, as W_drain_cx_x.v threads them.  Everything above this line is unchanged, so every AR statement
   of this file keeps its text and its Section list; the twin only adds names (the AR name with _x).  The AR-free
   names of Section c above (GSF, GSno, GSoc, GSfut, A_dr_add / A_dr_free, gs_aentry_okx_kept, gs_tr_*, gs_kept_lo,
   gs_akept_of, gs_mo_ok_of and the list / model lemmas) are CITED.
   - The cut predicates GA_x / GF_x and the stage statements gs_scan_stmt_x / gs_add_stmt_x / gs_free_stmt_x are the
     AR texts with W_drain_cx_x.v's twins (DBASE_x, DGS_x, DLN_x, dPOST_x, LCORE_x); dr_gs_of_x composes them into
     W_drain_cx_x.v:700 dr_gs_stmt_x, unchanged.
   - The journal's open / close at an allocator site over W_journal_x.ajournal_gx_x (gs_gx_open_x / gs_gx_close_x).
   - The room round's bookkeeping at a call (W_drain_cx_x.v dbud_x: the room rp_RM at MT_rk's charge of the requests
     still owed plus kr, and the live counts plus their peak tr_peakP + 2) is lib/A/W_drain_room_x.v, the drain
     stages' one text (gs_rm_take, gs_cnt_call, gs_cnt_malloc, gs_cnt_realloc, gs_cnt_free); the stage files
     W_gsadd_scratch.v, W_gsaddb.v and W_gsfree_scratch.v cite it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.

(* The carriers of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, and every carrier or spec it names -> its R twin;
   every other token is the strict text's. The strict <name> is <name>R at R := wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Definition GSB_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q])
  (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (GSno cx s1 p q) (GSoc cx s1 p q)
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

Definition GA_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_add) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\ getr regs1 19 = w64 bg /\
getr regs1 10 = w64 (re_nheld e1) /\ getr regs1 11 = w64 (re_nheld e1) /\
getr regs1 12 = w64 ((dxSA cx + 40) / 8) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = None /\
GSF s1 p q /\
GSB_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition GF_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (jj n : nat),
c1 = cfg_at SEGS (BASE + A_dr_free) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 ((re_hp e1 + 8 * Z.of_nat n) / 8 + SHADOW_OFF) /\
getr regs1 26 = w64 (re_hp e1 + 8 * Z.of_nat n) /\
getr regs1 20 = w64 (8 * Z.of_nat n) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 8) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 72) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF) /\
(n < length (re_keys e1))%nat /\
gesture (dline s1 p q) = Some (GEnd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
index_of (firstn jj (dline s1 p q)) (dlH cx s1 p) = Some n /\
GSF s1 p q /\
GSB_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
GSfut cx s1 p q a jb o ha ks tl.

Definition gs_scan_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> DGS_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GA_xR cx Hp kr s1 D p q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GF_xR cx Hp kr s1 D p q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).

Definition gs_add_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GA_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).

Definition gs_free_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GF_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
End wR.

(* ---- The line loop's core at gesture_seen's entry (GSB over LCORE_x). ---- *)
Definition GSB_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
GSB_xR (@wle SEGS) cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* ---- GA (0x8389c), the cut's ghost list Hp1 an existential after S1. ---- *)
Definition GA_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
GA_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.

(* ---- GF (0x83940), the cut's ghost list Hp1 an existential after S1. ---- *)
Definition GF_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS) (c1 : config) : Prop :=
GF_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.

(* ---- The three stages, over the entry's ghost list Hp and budget kr. ---- *)
Definition gs_scan_stmt_x : Prop :=
gs_scan_stmt_xR (@wle SEGS).

Definition gs_add_stmt_x : Prop :=
gs_add_stmt_xR (@wle SEGS).

Definition gs_free_stmt_x : Prop :=
gs_free_stmt_xR (@wle SEGS).


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

(* ---- Opening and closing the walk's journal at an allocator site (gs_gx_open / gs_gx_close over ARx): the
   W_journal_x.v rules (<rule>_c_x) are stated over ajournal_x; at XO = 0 the walk's ajournal_gx_x is ajournal_x at
   the overlaid start memory memS, which the rules leave alone. ---- *)
Lemma gs_gx_open_xR : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi. exists memS. split; [exact HSTK|]. split; [exact Hag | exact HJi].
Qed.
Lemma gs_gx_close_xR : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS HSTK Hag HJ.
apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2 memS);
  [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag | intros a Ha; lia].
Qed.
(* ---- The segment over ARx: W_drain_cx_x.v:700 dr_gs_stmt_x, from the three stages. ---- *)
Theorem dr_gs_of_xR : (gs_scan_stmt_xR R) -> (gs_add_stmt_xR R) -> (gs_free_stmt_xR R) -> dr_gs_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros SCAN ADD FREE cx Hp kr s1 D p q W1 c1 HB HGS HN.
apply (SCAN cx Hp kr s1 D p q W1 c1 HB HGS HN).
- intros W2 c2 HGA. exact (ADD cx Hp kr s1 D p q W2 c2 HB HGA HN).
- intros W2 c2 HGF. exact (FREE cx Hp kr s1 D p q W2 c2 HB HGF HN).
Qed.
End wR.



(* ---- Opening and closing the walk's journal at an allocator site (gs_gx_open / gs_gx_close over ARx): the
   W_journal_x.v rules (<rule>_c_x) are stated over ajournal_x; at XO = 0 the walk's ajournal_gx_x is ajournal_x at
   the overlaid start memory memS, which the rules leave alone. ---- *)
Lemma gs_gx_open_x : forall G STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc (W : world SEGS) memc mdc k,
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
exists memS, 0 <= STK /\ gagree G (w_H W0) mem memS /\
  ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memc mdc k.
Proof. eapply (gs_gx_open_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


Lemma gs_gx_close_x : forall G STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 memS,
0 <= STK -> gagree G (w_H W0) mem memS ->
ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
@ajournal_gx_x _ SK SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k2.
Proof. eapply (gs_gx_close_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- The segment over ARx: W_drain_cx_x.v:700 dr_gs_stmt_x, from the three stages. ---- *)
Theorem dr_gs_of_x : gs_scan_stmt_x -> gs_add_stmt_x -> gs_free_stmt_x -> dr_gs_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_gs_of_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.
End cx.
End bx.
End ax.
